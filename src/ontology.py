import os

from src.tools import formal_form, mkdir, depth_bigger_than, axiom_without_role_concepts, cut_axiom, \
    transform_ObjectComplementOf, trans_back
import json


class Ontology:
    def __init__(self, name_ontology, path=None, normalized=False, ind_form=True):
        self.name_ontology = name_ontology
        self.path = path
        self.normalized_flag = normalized
        self.ind_form = ind_form

        self.axioms, self.axioms_RI, self.axioms_RC, = {}, {}, {}
        self.concepts, self.relations = {'owl:Nothing': 0, 'owl:Thing': 1}, {'owl:topObjectProperty': 0,
                                                                             'owl:bottomObjectProperty': 1}
        self.ind_concepts, self.ind_relations = 2, 2
        # RI for role inclusion, RC for role chain
        self.axioms_normalized, self.mapback, self.normalize_dic = {}, {}, {}

        self.num_axiom_normalized, self.new_normalize_concepts, self.current_axiom = 0, 0, 0
        self.num_axiom, self.num_no_alc_axiom = 0, 0

        self.valid_first_literals = {'E', 'S', 'T'}  # Equivalence() or Sub...() or Transverse
        self.filter_box = ['ObjectInverseOf', 'ObjectOneOf',
                           'ObjectHasValue', 'ObjectHasSelf', 'ObjectMinCardinality', 'ObjectMaxCardinality',
                           'ObjectExactCardinality', 'DataSomeValuesFrom', 'DataAllValuesFrom', 'DataHasValue',
                           'DataMinCardinality', 'DataMaxCardinality', 'DataExactCardinality',
                           'ClassAxiom', 'ObjectPropertyAxiom', 'DataPropertyAxiom', 'DatatypeDefinition', 'HasKey',
                           'Assertion',
                           'Annotation', 'Datatype', 'DataIntersectionOf', 'DataUnionOf', 'DataComplementOf',
                           'DataOneOf',
                           'DatatypeRestriction', 'DisjointUnion', 'DisjointClasses',
                           'DisjointObjectProperties',
                           'InverseObjectProperties', 'FunctionalObjectProperty',
                           'InverseFunctionalObjectProperty', 'ReflexiveObjectProperty', 'IrreflexiveObjectProperty',
                           'SymmetricObjectProperty', 'AsymmetricObjectProperty', 'SubDataPropertyOf',
                           'EquivalentDataProperties', 'DisjointDataProperties', 'DataPropertyDomain',
                           'DataPropertyRange', 'FunctionalDataProperty', 'SameIndividual', 'DifferentIndividuals',
                           'ObjectPropertyAssertion', 'NegativeObjectPropertyAssertion', 'DataPropertyAssertion',
                           'NegativeDataPropertyAssertion']
        self.load_ontology()

        if not normalized:
            self.normalize()
            print("saving normalized ontolgy...")
            self.save(path+"data_onto/")

    def load_ontology(self):
        path = self.path + self.name_ontology
        with open(path, 'r') as f:
            data = f.readlines()
            for line in data:
                self.index_concepts_and_relation(line)
        with open(path, 'r') as f:
            data = f.readlines()
            for line in data:
                line = self.delete_Annotation(line)
                self.renew(line)

    def index_concepts_and_relation(self, line):
        if '(' not in line or 'Assertion(' in line:
            return

        if line[:11] == 'Declaration':  # Declaration()
            if line[11:13] == '(C':  # Class
                # Support both formats: Declaration(Class(<...>)) and Declaration(Class(:...))
                if '<' in line:
                    # Original format with angle brackets
                    concept_name = line.split('<', 1)[1][:-4]
                elif ':' in line and 'Class(' in line:
                    # New format with colon: Declaration(Class(:ConceptName))
                    import re
                    match = re.search(r'Declaration\(Class\(:([^)]+)\)\)', line)
                    if match:
                        concept_name = f"http://www.co-ode.org/ontologies/galen#{match.group(1)}"
                    else:
                        return
                else:
                    return
                self.concepts[concept_name] = self.ind_concepts
                self.ind_concepts += 1
            elif line[11:13] == '(O':  # Object
                # Support both formats: Declaration(ObjectProperty(<...>)) and Declaration(ObjectProperty(:...))
                if '<' in line:
                    # Original format with angle brackets
                    relation_name = line.split('<', 1)[1][:-4]
                elif ':' in line and 'ObjectProperty(' in line:
                    # New format with colon: Declaration(ObjectProperty(:PropertyName))
                    import re
                    match = re.search(r'Declaration\(ObjectProperty\(:([^)]+)\)\)', line)
                    if match:
                        relation_name = f"http://www.co-ode.org/ontologies/galen#{match.group(1)}"
                    else:
                        return
                else:
                    return
                self.relations[relation_name] = self.ind_relations
                self.ind_relations += 1

    def axiom_ind_form(self, a):
        if self.normalized_flag or not self.ind_form:
            return a
        a_s = a.split('<')
        result = a_s[0]
        for a_i in a_s[1:]:
            a_i_s = a_i.split('>', 1)
            assert len(a_i_s) == 2

            if a_i_s[0][0] == '-':
                assert a_i_s[0][1:] in self.concepts
                result += '<-' + str(self.concepts[a_i_s[0][1:]]) + '>'
            elif a_i_s[0][0] != '-' and a_i_s[0] in self.concepts:
                result += '<' + str(self.concepts[a_i_s[0]]) + '>'
            else:
                result += '<r' + str(self.relations[a_i_s[0]]) + '>'

            result += a_i_s[1]
        assert "http" not in result
        return result

    def delete_Annotation(self, line):
        line_s = line.split('(', 1)
        if len(line_s) > 1 and len(line_s[1]) > 11 and line_s[1][:11] == 'Annotation(':
            new_term = line_s[1].split(')', 1)[1]
            return line_s[0] + '(' + new_term
        else:
            return line

    def renew(self, line):
        if '(' not in line or '<' not in line or 'Assertion(' in line:
            return
        for a in self.filter_box:
            if a in line:
                self.num_no_alc_axiom += 1
                return

        if line[:19] == 'ObjectPropertyRange':
            middle_part = line[20:-1].replace('ObjectSomeValuesFrom(', '(some ').replace('ObjectIntersectionOf(',
                                                                                         '(and ') \
                .replace('ObjectAllValuesFrom(', '(all ').replace('owl:Thing', '<owl:Thing>') \
                .replace('owl:Nothing', '<owl:Nothing>').replace('ObjectUnionOf(', '(union ') \
                .replace('owl:topObjectProperty', '<owl:topObjectProperty>') \
                .replace('owl:bottomObjectProperty', '<owl:bottomObjectProperty>')
            axiom_new = '(implies <owl:Thing> (all' + transform_ObjectComplementOf(middle_part) + ')'
            self.axioms[self.axiom_ind_form(axiom_new)] = self.num_axiom
            self.num_axiom += 1
            return
        if line[:20] == 'ObjectPropertyDomain':
            middle_part = line[21:-1].replace('ObjectSomeValuesFrom(', '(some ').replace('ObjectIntersectionOf(',
                                                                                         '(and ') \
                .replace('ObjectAllValuesFrom(', '(all ').replace('owl:Thing', '<owl:Thing>') \
                .replace('owl:Nothing', '<owl:Nothing>').replace('ObjectUnionOf(', '(union ') \
                .replace('owl:topObjectProperty', '<owl:topObjectProperty>') \
                .replace('owl:bottomObjectProperty', '<owl:bottomObjectProperty>')
            middle_part_s = transform_ObjectComplementOf(middle_part)[:-1].split(' ', 1)
            assert len(middle_part_s) == 2
            r, A = middle_part_s[0], middle_part_s[1]
            axiom_new = f'(implies (some {r} <owl:Thing>) {A})'
            self.axioms[self.axiom_ind_form(axiom_new)] = self.num_axiom
            self.num_axiom += 1
            return

        elif line[:11] == 'Declaration':  # Declaration()
            if line[11:13] == '(C' or line[11:13] == '(O':  # Object
                return

        elif line[:15] == 'DisjointClasses':
            c_list = [a.split('>')[0] for a in line.split('<')[1:]]
            assert len(c_list) == 2
            axiom_1 = self.axiom_ind_form(f'(implies <{c_list[0]}> <-{c_list[1]}>)')
            axiom_2 = self.axiom_ind_form(f'(implies <{c_list[1]}> <-{c_list[0]}>)')
            self.axioms[axiom_1] = self.num_axiom
            self.axioms[axiom_2] = self.num_axiom

        elif line[0] in self.valid_first_literals:
            if 'ObjectPropert' in axiom_without_role_concepts(line):  # to include two cases "Property" or "Properties"
                if 'Chain' in line:
                    assert line[0] != 'E'
                    self.axioms_RC[line[:-1]] = self.num_axiom
                else:
                    if line[:16] == 'TransitiveObject':
                        role_name = line.split('<', 1)[1].split('>', 1)[0]
                        trans_axiom = self.axiom_ind_form(
                            f'SubObjectPropertyOf(ObjectPropertyChain(<{role_name}> <{role_name}>) <{role_name}>)')
                        self.axioms_RC[trans_axiom] = self.num_axiom
                    elif line[:26] == 'EquivalentObjectProperties':
                        r_list = [a.split('>')[0] for a in line.split('<')[1:]]
                        axiom_1 = self.axiom_ind_form(f'SubObjectPropertyOf<{r_list[0]}> <{r_list[1]}>)')
                        axiom_2 = self.axiom_ind_form(f'SubObjectPropertyOf(<{r_list[1]}> <{r_list[0]}>)')
                        self.axioms_RI[axiom_1] = self.num_axiom
                        self.axioms_RI[axiom_2] = self.num_axiom
                    else:
                        line = line.replace('owl:topObjectProperty', '<owl:topObjectProperty>') \
                            .replace('owl:bottomObjectProperty', '<owl:bottomObjectProperty>')
                        self.axioms_RI[self.axiom_ind_form(line[:-1])] = self.num_axiom
            else:
                line_other_form = line.replace('SubClassOf(', '(implies ').replace('EquivalentClasses(', '(equivalent ') \
                    .replace('ObjectSomeValuesFrom(', '(some ').replace('ObjectIntersectionOf(', '(and ') \
                    .replace('ObjectAllValuesFrom(', '(all ').replace('owl:Thing', '<owl:Thing>') \
                    .replace('owl:Nothing', '<owl:Nothing>').replace('ObjectUnionOf(', '(union ') \
                    .replace('owl:topObjectProperty', '<owl:topObjectProperty>') \
                    .replace('owl:bottomObjectProperty', '<owl:bottomObjectProperty>')

                line_other_form = self.axiom_ind_form(transform_ObjectComplementOf(line_other_form))
                self.axioms[line_other_form[:-1]] = self.num_axiom
            self.num_axiom += 1

    # find all the existing definition (equivalence ... ) avoid to add this defi again when normalize the ontology.
    def preprocess(self):
        for axiom in self.axioms:
            if axiom[1] == 'e':
                # not depth_bigger_than(one_axiom, 2) means the axioms contain at most one "some" or "and"
                if len(axiom.split('(')) > 2 and not depth_bigger_than(axiom, 2):
                    # get the item **** inside (equivalent\implies <#...> (****) )
                    def_terms = formal_form(axiom.split('(')[-1].split(')')[0])
                    defined_term = axiom.split(' ')[1]
                    if def_terms not in self.normalize_dic.keys():
                        self.mapback[def_terms] = self.axioms[axiom]
                        self.normalize_dic[def_terms] = defined_term

    def normalize_one_term_begin(self, axiom):
        if depth_bigger_than(axiom, 2):
            # get the item **** inside (equi\implies <#...> (****) )
            axiom_str_rest, axiom_cutted = cut_axiom(axiom[1:-1])
            result = axiom_str_rest[0]
            assert len(axiom_cutted) <= 2
            for i, one_axiom_cutted in enumerate(axiom_cutted):
                if len(result.split('<')) >= 2:
                    k = 2
                    result += '('
                else:
                    k = 1
                while depth_bigger_than(one_axiom_cutted, k):
                    one_axiom_cutted = self.normalize_one_term_middle(one_axiom_cutted)
                result += one_axiom_cutted
                if k == 2:
                    result += ')'
                result += axiom_str_rest[i + 1]
            return '(' + result + ')'
        else:
            return axiom

    def normalize_one_term_middle(self, part_axiom):
        if depth_bigger_than(part_axiom, 2):
            axiom_str_rest, axiom_cutted = cut_axiom(part_axiom)
            result = axiom_str_rest[0]
            for i, one_axiom_cutted in enumerate(axiom_cutted):
                while depth_bigger_than(one_axiom_cutted, 1):
                    one_axiom_cutted = self.normalize_one_term_middle(one_axiom_cutted)
                result += one_axiom_cutted
                result += axiom_str_rest[i + 1]
            return result
        else:
            if part_axiom[0] == 'c':
                result = '<-' + part_axiom.split('<')[1].split('>')[0] + '>'
                return result
            one_axiom_form = formal_form(part_axiom)
            if one_axiom_form not in self.normalize_dic.keys():
                new_normalized_concept = f'<N{self.new_normalize_concepts}>'
                self.new_normalize_concepts += 1
                self.concepts[new_normalized_concept[1:-1]] = self.ind_concepts
                self.ind_concepts += 1
                self.normalize_dic[one_axiom_form] = new_normalized_concept

                self.axioms_normalized[
                    f'(equivalent {new_normalized_concept} ({part_axiom}))'] = self.num_axiom_normalized
                self.num_axiom_normalized += 1

            return self.normalize_dic[one_axiom_form]

    def normalize(self):
        # after this step, all the axioms contain only one of 'union','and', 'some' or 'all'.
        #        Also one of '(implies' or '(equivalent'
        for axiom in self.axioms:
            if not self.normalized_flag:
                self.axioms_normalized[self.normalize_one_term_begin(axiom)] = self.num_axiom_normalized
                self.mapback[self.num_axiom_normalized] = self.axioms[axiom]
            else:
                self.axioms_normalized[axiom] = self.num_axiom_normalized
            self.num_axiom_normalized += 1
        # print(f'length of ontology, normalization ontology(exclude role chain or role inclusion): {len(self.axioms)}, {self.num_axiom_normalized}')

    def len(self):
        return len(self.axioms_normalized) + len(self.axioms_RC) + len(self.axioms_RI)

    def save(self, path=None):
        mkdir(path)
        jsobj1 = json.dumps(self.axioms_RI)
        fileObject1 = open(f'{path}role_inclusion.json', 'w')
        fileObject1.write(jsobj1)
        fileObject1.close()

        jsobj1 = json.dumps(self.axioms_RC)
        fileObject1 = open(f'{path}role_chain.json', 'w')
        fileObject1.write(jsobj1)
        fileObject1.close()

        jsobj1 = json.dumps(self.axioms)
        fileObject1 = open(f'{path}axioms.json', 'w')
        fileObject1.write(jsobj1)
        fileObject1.close()

        with open(f'{path}axioms_normalized.owl', 'w') as f:
            f.write(
                'Prefix(owl:=<http://www.w3.org/2002/07/owl#>)\nPrefix(rdf:=<http://www.w3.org/1999/02/22-rdf-syntax-ns#>)\nPrefix(xml:=<http://www.w3.org/XML/1998/namespace>)\nPrefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)\nPrefix(rdfs:=<http://www.w3.org/2000/01/rdf-schema#>)\n\n')
            f.write('Ontology(\n')
            for k in self.axioms_normalized:
                f.write(trans_back(k) + '\n')
            f.write(')')
        '''
        jsobj1 = json.dumps(self.axioms_normalized)
        fileObject1 = open(f'{path}axioms_normalized.json', 'w')
        fileObject1.write(jsobj1)
        fileObject1.close()
        '''

        jsobj1 = json.dumps(self.mapback)
        fileObject1 = open(f'{path}mapback.json', 'w')
        fileObject1.write(jsobj1)
        fileObject1.close()
        return
