# generate signature and concepts for each given ontology

# !!!!!!!!! here we require the ontology is terminology, and we delete the axioms that do not satisfy the condition.
import numpy as np
from src.ontology import Ontology
from src.tools import split_two_part, unfold, mkdir, trans_back
import time
import pickle
import random
from itertools import product
import os


class initializing():
    def __init__(self, name_ontology, path):
        self.ontology = None
        self.name_ontology = name_ontology
        self.path = path

        self.A_left = set([])
        self.axioms_remain = set([])

        self.r2A2B = {}  # {r:{A:set(B, B_1,...), A_1:set(....),}, ...} corresponding to A\sqsubseteq \exists r.B
        self.r2B2A = {}  # {r:{B:set(A, A_1,...), B_1:set(....),}, ...} corresponding to A\equiv \exists r.B !!!!!(different with usual case ,i.e., not a terminology)

        self.C2Ci = {}  # {C :{(C1,...Cn),(B1,..., Bm),..},....} corresponding to C \sqsubseteq C1 \sqcap ... Cn, C \sqsubseteq C1 \sqcap ... Cn
        self.C2Ci_flat = {}  # {C :{C1,...Cn,B1,..., Bm,..},....} the value of C is the union of Ci, Bi,...

        self.atomic_concepts = set([])
        self.atomic_roles = set([])

        self.subsumptions = {}
        self.subsumptions_direct = {}  # note that here self.subsumptions_direct only contain the inferred subsumptions.

    def renew(self, r, A, B, type):
        if r:
            self.atomic_roles.add(r)

        if type == 'rB2A':
            if r not in self.r2B2A:
                self.r2B2A[r] = {B: {A}}
            elif B not in self.r2B2A[r]:
                self.r2B2A[r][B] = {A}
            else:
                self.r2B2A[r][B].add(A)
            return True
        elif type == 'A2rB':
            if A not in self.A_left:
                self.A_left.add(A)
                if r not in self.r2A2B:
                    self.r2A2B[r] = {A: {B}}
                elif A not in self.r2A2B[r]:
                    self.r2A2B[r][A] = {B}
                return True
        elif type == 'C2Ci':
            if A not in self.A_left:
                self.A_left.add(A)
                self.C2Ci[A] = {B}
                self.C2Ci_flat[A] = set(B)
                self.subsumptions_direct[A] = set(B)
                return True

        elif type == 'A2B':
            if A in self.subsumptions_direct:
                self.subsumptions_direct[A].add(B)
            else:
                self.subsumptions_direct[A] = {B}

        return False

    def initialize(self):
        for axiom in self.ontology.axioms_normalized:
            #print(axiom, self.axioms_remain)
            f = False
            axiom_s = axiom.split('(')
            if len(axiom_s) <= 2:
                A = axiom.split('<')[1].split('>')[0]
                B = axiom.split('<')[2].split('>')[0]
                if A not in self.A_left:
                    self.renew(None, A, B, 'A2B')
                    self.axioms_remain.add(axiom)
                    self.A_left.add(A)
                continue
            literal = axiom_s[2]
            type_normal, first, rest = split_two_part(axiom, type='unsort')
            if literal[0] == 's':  # (... (some...)...)
                if type_normal:  # (implies... (some ...))
                    f = self.renew(rest[0], first[0], rest[1], 'A2rB')
                    if f:
                        self.axioms_remain.add(axiom)
                else:  # (impies (some...) ...)
                    print("axioms ignored:", axiom)
                    input("enter any keys to continue...")

                if axiom[1] == 'e':
                    if type_normal:  # (equivalence ... (some...)) --> (implies (some...) ... )
                        assert len(rest) == 2
                        _ = self.renew(rest[0], first[0], rest[1], 'rB2A')
                    else:  # (equivalent (some...) ...) --> (implies ... (some...))
                        assert len(first) == 2
                        f1 = self.renew(first[0], rest[0], first[1], 'A2rB')
                        if f1:
                            self.axioms_remain.add(axiom)


            elif literal[:3] == 'and':  # (... (and...)...)
                if axiom[1] == 'e':
                    if type_normal:  # (equivalence ... (and...))
                        rest_tuple = tuple(sorted(rest))
                        f = self.renew(None, first[0], rest_tuple, "C2Ci")
                    else:  # (equivalence (and...) ...)
                        first_tuple = tuple(sorted(first))
                        f = self.renew(None, rest[0], first_tuple, "C2Ci")

                    if f:
                        self.axioms_remain.add(axiom)
                else:
                    assert axiom[1] == 'i'
                    if type_normal:# (implies ... (and...))
                        self.axioms_remain.add(axiom)


        mkdir(self.path +  'data_preprocess')
        with open(self.path + 'data_preprocess/terminology.owl', 'w') as f:
            f.write(
                'Prefix(owl:=<http://www.w3.org/2002/07/owl#>)\nPrefix(rdf:=<http://www.w3.org/1999/02/22-rdf-syntax-ns#>)\nPrefix(xml:=<http://www.w3.org/XML/1998/namespace>)\nPrefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)\nPrefix(rdfs:=<http://www.w3.org/2000/01/rdf-schema#>)\n\n')
            f.write('Ontology(\n')
            for a in self.axioms_remain:
                f.write(trans_back(a) + '\n')

            for a in self.ontology.axioms_RI:
                #print(a)
                f.write(a + '\n')

            for a in self.ontology.axioms_RC:
                f.write(a + '\n')

            f.write(')')

        os.system(f"cp {self.path}data_preprocess/terminology.owl pakages/elk-tools/{self.name_ontology}_terminology.owl")

        with open(self.path + 'data_preprocess/terminology_krss.owl', 'w') as f1:
            for a in self.axioms_remain:
                f1.write(a + '\n')

    def initial_subsumption(self):
        path = self.path + 'data_preprocess/subsumption_direct_terminology.owl'
        print("=======calculate direct subsumption of terminology====")
        #os.system(f'java -jar pakages/elk-tools/elk-standalone.jar -i pakages/elk-tools/{self.name_ontology}_terminology.owl -c -o {path}')

        with open(path, 'r') as f:
            data = f.readlines()
            for row in data:
                if row[0] == 'S':
                    row_s = row.split('<')
                    assert len(row_s) == 3
                    f_id, l_id = row_s[1].split('>')[0], row_s[2].split('>')[0]
                    if f_id in self.subsumptions_direct:
                        self.subsumptions_direct[f_id].add(l_id)
                    else:
                        self.subsumptions_direct[f_id] = {l_id}
                elif row[0] == 'D':
                    A = row.split('<')[1].split('>')[0]
                    if A[0] != 'N':
                        self.atomic_concepts.add(A)

        s_t = time.time()
        self.subsumptions = unfold(self.subsumptions_direct)
        print(time.time() - s_t)

    def save(self):
        mkdir(self.path + "data_preprocess")
        path_preprocess = self.path + 'data_preprocess/'
        with open(path_preprocess + 'queries_terminology', 'w') as f1:
            for k in self.subsumptions:
                if k[0] != 'N' and k != 'owl:Nothing':
                    for v in self.subsumptions[k]:
                        if v and v[0] != 'N' and v != 'owl:Thing':
                            f1.write(k + '\t' + v + '\n')

        with open(path_preprocess + 'subsumption_terminology.owl', 'wb') as f:
            pickle.dump(self.subsumptions, f)
        with open(path_preprocess + 'r2A2B', 'wb') as f:
            pickle.dump(self.r2A2B, f)
        with open(path_preprocess + 'r2B2A', 'wb') as f:
            pickle.dump(self.r2B2A, f)
        with open(path_preprocess + 'C2Ci', 'wb') as f:
            pickle.dump(self.C2Ci, f)

        self.C2Ci_flat = unfold(self.C2Ci_flat)
        with open(path_preprocess + 'C2Ci_flat', 'wb') as f:
            pickle.dump(self.C2Ci_flat, f)

        print('saved!')

    def load(self):
        path_preprocess = self.path + 'data_preprocess/'
        with open(path_preprocess + 'subsumption_terminology.owl', 'rb') as f:
            self.subsumptions = pickle.load(f)
        with open(path_preprocess + 'r2A2B', 'rb') as f:
            self.r2A2B = pickle.load(f)
        with open(path_preprocess + 'r2B2A', 'rb') as f:
            self.r2B2A = pickle.load(f)
        with open(path_preprocess + 'C2Ci', 'rb') as f:
            self.C2Ci = pickle.load(f)
        with open(path_preprocess + 'C2Ci_flat', 'rb') as f:
            self.C2Ci_flat = pickle.load(f)

    def main(self, gen=False):
        self.ontology = Ontology(self.name_ontology + '.owl', self.path, False, ind_form=False)
        # initialize self.r2A2B, self.r2B2A, self.C2Ci, self.C2Ci_flat, self.atomic_roles and part of self.subsumptions_direct
        #self.initialize()
        # initialize self.subsumptions_direct and unfold it to obtain self.subsumptions
        #self.initial_subsumption()
        #self.save()

        #if gen:
            #self.generate_signature()

    def generate_signature(self):
        #concept_list_test = np.arange(30, 100, 5).tolist()
        #relation_list_test = np.arange(10, 40, 5).tolist()

        concept_list_test = [100]*1000
        relation_list_test = [10]
        type = ''
        path_signature = self.path + f"sig{type}"
        path_signature_minimal_moduel = self.path + f"sig{type}_min"
        path_signature_single_minimal_moduel = self.path + f"sig{type}_single_min"
        mkdir(path_signature)
        mkdir(path_signature_minimal_moduel)
        mkdir(path_signature_single_minimal_moduel)

        i = 0
        print(len(self.atomic_roles), len(self.atomic_concepts))
        for (li, lj) in product(relation_list_test, concept_list_test):
            sig_r = random.sample(self.atomic_roles, li)
            sig_c = random.sample(self.atomic_concepts, lj)
            with open(path_signature + "/" + str(i), 'w') as fi:
                fi.write(" ".join(sig_c) + '\n')
                fi.write(" ".join(sig_r) + '\n')

            with open(path_signature_minimal_moduel + "/" + str(i), 'w') as f1:
                f1.write("concepts[\n")
                for c in sig_c:
                    f1.write("<" + c + '>\n')
                f1.write(']\nroles[\n')
                for r in sig_r:
                    f1.write("<" + r + '>\n')
                f1.write(']')

            with open(path_signature_single_minimal_moduel + "/" + str(i), 'w') as f1:
                f1.write("concepts[\n")
                for c in sig_c:
                    f1.write(c + '\n')
                f1.write(']\nroles[\n')
                for r in sig_r:
                    f1.write(r + '\n')
                f1.write(']')
            i += 1


if __name__ == "__main__":
    # name_ontology = 'terminologyWithDeclaration'
    # path = 'workspace/snomedct012016/'

    path = 'workspace/snomedct2021_Snapshot/'
    name_ontology = 'snomedct2021_normalized'
    #path = 'workspace/snomedct2021_Snapshot/'
    #path = '../workspace/test/'
    # name_ontology = 'axioms_normalized.owl'
    # path = 'workspace/snomedct2021_snapshot/'
    # name_ontology = 'galen7.owl'
    # path = 'workspace/galen7/'
    d = initializing(name_ontology, path)
    d.main()
    d.generate_signature()
