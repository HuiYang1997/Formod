import os

import mowl

mowl.init_jvm("10g")

from org.semanticweb.owlapi.apibinding import OWLManager
from org.semanticweb.owlapi.model import *
from org.semanticweb.owlapi.krss2.renderer import KRSS2OWLSyntaxRenderer
from org.semanticweb.owlapi.functional.renderer import OWLFunctionalSyntaxRenderer
from org.semanticweb.elk.owlapi import ElkReasonerFactory
from java.io import File, FileOutputStream, PrintWriter
from java.util import HashSet
from java.lang import StringBuilder
import pickle


class OntologyTransformer:
    def __init__(self):
        self.instance_concepts = {}
        self.concept_to_instance = {}
        self.original_axioms = {}

    def transform_ontology(self, ontology):
        manager = ontology.getOWLOntologyManager()
        data_factory = manager.getOWLDataFactory()
        axioms_to_remove = HashSet()
        axioms_to_add = HashSet()

        for axiom in ontology.getAxioms():
            if axiom.isOfType(AxiomType.CLASS_ASSERTION):
                new_axiom = self._transform_class_assertion(axiom, data_factory)
                axioms_to_remove.add(axiom)
                axioms_to_add.add(new_axiom)
                self.original_axioms[new_axiom] = axiom

            elif axiom.isOfType(AxiomType.OBJECT_PROPERTY_ASSERTION):
                new_axiom = self._transform_object_property_assertion(axiom, data_factory)
                axioms_to_remove.add(axiom)
                axioms_to_add.add(new_axiom)
                self.original_axioms[new_axiom] = axiom

            elif not self._is_el_axiom(axiom):
                axioms_to_remove.add(axiom)

        manager.removeAxioms(ontology, axioms_to_remove)
        manager.addAxioms(ontology, axioms_to_add)

        return ontology

    def _transform_class_assertion(self, axiom, data_factory):
        instance = axiom.getIndividual()
        cls = axiom.getClassExpression()

        if instance not in self.instance_concepts:
            new_concept = data_factory.getOWLClass(IRI.create(f"{instance.getIRI().toString()}_concept"))
            self.instance_concepts[instance] = new_concept
            self.concept_to_instance[new_concept] = instance

        return data_factory.getOWLSubClassOfAxiom(self.instance_concepts[instance], cls)

    def _transform_object_property_assertion(self, axiom, data_factory):
        subject = axiom.getSubject()
        object = axiom.getObject()
        property = axiom.getProperty()

        if subject not in self.instance_concepts:
            subject_concept = data_factory.getOWLClass(IRI.create(f"{subject.getIRI().toString()}_concept"))
            self.instance_concepts[subject] = subject_concept
            self.concept_to_instance[subject_concept] = subject
        if object not in self.instance_concepts:
            object_concept = data_factory.getOWLClass(IRI.create(f"{object.getIRI().toString()}_concept"))
            self.instance_concepts[object] = object_concept
            self.concept_to_instance[object_concept] = object

        exists_restriction = data_factory.getOWLObjectSomeValuesFrom(property, self.instance_concepts[object])
        return data_factory.getOWLSubClassOfAxiom(self.instance_concepts[subject], exists_restriction)

    def _is_el_axiom(self, axiom):
        return (axiom.isOfType(AxiomType.SUBCLASS_OF) or
                axiom.isOfType(AxiomType.EQUIVALENT_CLASSES) or
                axiom.isOfType(AxiomType.DISJOINT_CLASSES))

    def save_mappings(self, filename):
        with open(filename, 'wb') as f:
            pickle.dump({
                'instance_concepts': {str(k): str(v) for k, v in self.instance_concepts.items()},
                'concept_to_instance': {str(k): str(v) for k, v in self.concept_to_instance.items()},
                'original_axioms': {str(k): str(v) for k, v in self.original_axioms.items()}
            }, f)

    def load_mappings(self, filename):
        with open(filename, 'rb') as f:
            data = pickle.load(f)
        self.instance_concepts = {eval(k): eval(v) for k, v in data['instance_concepts'].items()}
        self.concept_to_instance = {eval(k): eval(v) for k, v in data['concept_to_instance'].items()}
        self.original_axioms = {eval(k): eval(v) for k, v in data['original_axioms'].items()}


def inference(ontology, manager, saving_dir_subsumptions):
    reasoner_factory = ElkReasonerFactory()
    reasoner = reasoner_factory.createReasoner(ontology)

    # Create a new ontology for direct subsumptions
    subsumption_manager = OWLManager.createOWLOntologyManager()
    subsumption_ontology = subsumption_manager.createOntology()
    data_factory = subsumption_manager.getOWLDataFactory()

    for cls in ontology.getClassesInSignature():
        direct_subclasses = set(reasoner.getSubClasses(cls, True).getFlattened())
        direct_subclasses.discard(manager.getOWLDataFactory().getOWLNothing())

        # Remove trivial subsumptions
        direct_subclasses.discard(cls)

        for subclass in direct_subclasses:
            subsumption_axiom = data_factory.getOWLSubClassOfAxiom(subclass, cls)
            subsumption_manager.addAxiom(subsumption_ontology, subsumption_axiom)

    # Store the direct subsumptions ontology in FSS format
    fss_output_file = File(f"{saving_dir_subsumptions}/subsumption_direct_terminology.owl")
    with FileOutputStream(fss_output_file) as out:
        renderer = OWLFunctionalSyntaxRenderer()
        renderer.render(subsumption_ontology, out)

    print("Processing complete. Results stored in 'processed_ontology.krss' and 'subsumption_direct_terminology.owl'")


def main(ont_path, do_transform=True):
    # 1. Load the ontology
    manager = OWLManager.createOWLOntologyManager()
    ontology = manager.loadOntologyFromOntologyDocument(File(ont_path))

    ## initialize the saving directory
    ont_name = ont_path.split("/")[-1].split(".")[0]
    if do_transform:
        ont_name += "_Abox_transformed"

    saving_dir = f"workspace/{ont_name}"
    if not os.path.exists(saving_dir):
        os.makedirs(saving_dir)
    saving_dir_subsumptions = f"{saving_dir}/data_preprocess"
    if not os.path.exists(saving_dir_subsumptions):
        os.makedirs(saving_dir_subsumptions)
    if do_transform:
        transformer = OntologyTransformer()
        ontology = transformer.transform_ontology(ontology)
        # Save the mappings
        transformer.save_mappings(f"{saving_dir}/ontology_mappings.pkl")
        print("Ontology transformed. Transformation mappings saved in 'ontology_mappings.pkl'")
    else:
        print("Skipping ontology transformation as per parameter.")

    # 2.1 Store the processed ontology in KRSS2 format
    output_file = File(f"{saving_dir}/{ont_name}.krss2.owl")
    with FileOutputStream(output_file) as out:
        renderer = KRSS2OWLSyntaxRenderer()
        renderer.render(ontology, out)
        # renderer = CustomKRSSRenderer(ontology)
        # renderer.render(out)

    ## rewrite krss2 file to krss file
    ont = []
    with open(f"{saving_dir}/{ont_name}.krss2.owl", "r") as f:
        data = f.readlines()
        for line in data:
            ont.append(line.replace("define-primitive-concept", "implies")
                       .replace("define-concept", "implies"))

    ## rewrite krss2 file to krss file
    ont = []
    with open(f"{saving_dir}/{ont_name}.krss2.owl", "r") as f:
        data = f.readlines()
        for line in data:
            ont.append(line.replace("define-primitive-concept", "implies")
                       .replace("define-concept", "implies"))
    ## save the krss file
    with open(f"{saving_dir}/{ont_name}.krss.owl", "w") as f:
        f.writelines(ont)

    # 2.2 Store the processed ontology in fss format
    output_file = File(f"{saving_dir}/{ont_name}.owl")
    with FileOutputStream(output_file) as out:
        renderer = OWLFunctionalSyntaxRenderer()
        renderer.render(ontology, out)

    # 3. Calculate direct subsumptions using ELK reasoner
    inference(ontology, manager, saving_dir_subsumptions)


if __name__ == "__main__":
    import sys

    if len(sys.argv) < 2:
        print("Usage: python ont_processing.py <ontology_path> [do_transform]\n "
              "do_transform: True/False, \n"
              "              if true, the ontology will be transformed ABox axioms\n"
              "                           'A(a)' to 'A_a\sqsubseteq A' \n"
              "                     and 'r(a,b)' to 'A_a\sqsubseteq  \exists r. A_b'\n"
              "              by transfer instances a, b to concepts A_a, A_b \n")
        sys.exit(1)

    ont_path = sys.argv[1]
    do_transform = True if len(sys.argv) < 3 else sys.argv[2].lower() == 'true'

    main(ont_path, do_transform)
