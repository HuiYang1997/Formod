import time
import copy
import json
import pickle

from pakages.trace_inference_rules.tools import unfold


def transform_class(path_ontology, name_ontology, count_c=38579, l_concepts_part_orginal=43090):
    start_time_t = time.time()
    axiom_normalized = []
    axiom_roles_inclusion = []
    with open('{}/data/id_normalize2id_original_axiom.json'.format(path_ontology), 'r') as f:
        id_normalize2id_original_axiom = json.load(f)
    with open(f'pakages/elk-tools/{name_ontology}_normalized.txt', 'r') as f:
        f_data = f.readlines()
        for row in f_data:
            axiom_normalized.append(row[:-1])
    with open('{}/data/role_inclusion.txt'.format(path_ontology), 'r') as f:
        f_data = f.readlines()
        for row in f_data:
            axiom_roles_inclusion.append(row[:-1])
    with open('{}/data/dicND2r_A.json'.format(path_ontology), 'r') as f:
        dicND2r_A = json.load(f)

    def split_id_1(axioms):
        a_s = axioms.split('<')[1:]

        def get_id(a):
            if a in dicND2r_A:
                return [str(e) for e in dicND2r_A[a]]
            else:
                return [str(a)]

        return (get_id(a_s[i].split('>')[0][2:]) for i in range(len(a_s)))

    equi_dic = {}
    equi_items = []
    with open('pakages/elk-tools/{}.class'.format(name_ontology, name_ontology), 'r') as f:
        data = f.readlines()  # have form 'Declaration(Class(<#D121>))' or 'SubClassOf(<#c25665> <#N2301>)' or 'EquivalentClasses(<#N2304> <#c15112>)' # have form: "#query_id (implies #... (some #... #...))", or "#query_id (implies #... #...)" or query_id (implies (some #... #...) ... )
        for row in data:
            if row[0] == 'E':
                equi_ids = split_id_1(row)
                all_ids = set([])
                for ids in equi_ids:
                    all_ids.update(ids)
                equi_items.append(list(all_ids))
                for id in all_ids:
                    equi_dic[id] = all_ids

    for ND in dicND2r_A:
        if int(ND) < count_c:
            assert len(dicND2r_A[ND]) == 2
            if ND not in equi_dic:
                ND_l = {str(e) for e in dicND2r_A[ND]}
                for t in ND_l:
                    equi_dic[t] = copy.deepcopy(ND_l)
                    continue
        else:
            assert len(dicND2r_A[ND]) == 1
            ND_r_A = str(dicND2r_A[ND][0])
            if ND_r_A not in equi_dic:
                equi_dic[ND_r_A] = {ND_r_A}

    for i in range(count_c):
        if str(i) not in equi_dic:
            equi_dic[str(i)] = {str(i)}

    def split_id(axioms):
        a_s = axioms.split('<')[1:]

        def get_id(a):
            if a in dicND2r_A:
                result = []
                for e in dicND2r_A[a]:
                    result += equi_dic[str(e)]
                return result
            else:
                return list(equi_dic[str(a)])

        return (get_id(a_s[i].split('>')[0][2:]) for i in range(len(a_s)))

    ini_dic = copy.deepcopy(equi_dic)  # subclass of k
    with open('pakages/elk-tools/{}.class'.format(name_ontology), 'r') as f:
        data = f.readlines()  # have form 'Declaration(Class(<#D121>))' or 'SubClassOf(<#c25665> <#N2301>)' or 'EquivalentClasses(<#N2304> <#c15112>)' # have form: "#query_id (implies #... (some #... #...))", or "#query_id (implies #... #...)" or query_id (implies (some #... #...) ... )
        for row in data:
            if row[0] == 'S':
                first_ids, last_ids = split_id(row)
                for first_id in first_ids:
                    ini_dic[first_id].update(last_ids)
                for last_id in last_ids:
                    assert set(last_ids).issubset(ini_dic[last_id])
    print('data loaded, processing.....', )

    beacon_class = unfold(ini_dic)
    with open('pakages/elk-tools/{}.class'.format(name_ontology), 'r') as f:
        data = f.readlines()  # have form 'Declaration(Class(<#D121>))' or 'SubClassOf(<#c25665> <#N2301>)' or 'EquivalentClasses(<#N2304> <#c15112>)' # have form: "#query_id (implies #... (some #... #...))", or "#query_id (implies #... #...)" or query_id (implies (some #... #...) ... )
        for row in data:
            if row[0] == 'S':
                first_ids, last_ids = split_id(row)
                for first_id in first_ids:
                    for last_id in last_ids:
                        assert beacon_class[last_id].issubset(beacon_class[first_id])
    del ini_dic

    for equi_list in equi_items:
        union = set(beacon_class[equi_list[0]])
        assert set(equi_list).issubset(union)
        for e in equi_list[1:]:
            assert set(beacon_class[e]) == union

    beacon_class_inverse = {}
    for k in beacon_class:
        assert k in beacon_class[k]
        for e in beacon_class[k]:
            if e not in beacon_class_inverse:
                beacon_class_inverse[e] = {k}
            else:
                beacon_class_inverse[e].add(k)

    for equi_list in equi_items:
        union = set(beacon_class_inverse[equi_list[0]])
        for e in equi_list[1:]:
            if set(beacon_class_inverse[e]) != union:
                print(equi_list, e)
                print(beacon_class_inverse[e] - union)
                print(union - beacon_class_inverse[e])
                assert 1 == 0

    with open('pakages/elk-tools/{}.class'.format(name_ontology), 'r') as f:
        data = f.readlines()  # have form 'Declaration(Class(<#D121>))' or 'SubClassOf(<#c25665> <#N2301>)' or 'EquivalentClasses(<#N2304> <#c15112>)' # have form: "#query_id (implies #... (some #... #...))", or "#query_id (implies #... #...)" or query_id (implies (some #... #...) ... )
        for row in data:
            if row[0] == 'S':
                first_ids, last_ids = split_id(row)
                for first_id in first_ids:
                    for last_id in last_ids:
                        assert beacon_class_inverse[first_id].issubset(beacon_class_inverse[last_id])

    with open('{}/data/M_r_A_inverse.pickle'.format(path_ontology), 'wb') as f:
        pickle.dump(beacon_class, f)

    with open('{}/data/M_r_A_appear.pickle'.format(path_ontology), 'wb') as f:
        pickle.dump(beacon_class_inverse, f)

    print("S_A saved in {}!".format(time.time() - start_time_t))

    indE2id_original_axiom, E, D_edge = {}, {}, {}
    k_E = 0

    def subgraph_concepts(li):
        '''
        calculate the subgraph for all concept nodes,
        we assume li doesn't contain axiom between relation: r\sqsubset s !!!!!!
        '''
        nonlocal id_normalize2id_original_axiom, E, D_edge, k_E
        # k_E is the index of axioms
        for i, string in enumerate(li):
            list_E = [k_E]
            if str(i) in id_normalize2id_original_axiom:
                indE2id_original_axiom[k_E] = id_normalize2id_original_axiom[str(i)]
            k_E += 1
            if string[1] == 'e':
                cl = 'equiv'
            elif string[1] == 'i':
                cl = 'sub'
            else:
                print(string)
                print('error!')
                break

            row_s = string.split('#')
            first_id = int(row_s[1].split('>')[0][1:])
            # print(string)
            string_s = string.split('(')[-1][0]
            if string_s == 's':
                r_id = int(row_s[2].split('>')[0][1:])
                list_E.append(r_id)
                last_id = r_id * count_c + int(row_s[-1].split('>')[0][1:])
                list_E.append(last_id)
                if cl == 'equiv':
                    #print(i, string, E, last_id)
                    #assert last_id not in E
                    E[last_id] = [[k_E - 1, -r_id, first_id]]
            else:
                list_E.append(0)
                list_E += [int(s.split('>')[0][1:]) for s in row_s[2:]]
                if cl == 'equiv':
                    if len(list_E) > 3:  # record definite axioms (equi #.. (and ...))
                        if first_id in D_edge:
                            D_edge[first_id].append(list_E)
                            # print(D_edge[first_id])
                        else:
                            D_edge[first_id] = [list_E]

                    else:
                        last_id = list_E[-1]
                        if last_id not in E:
                            E[last_id] = [[k_E - 1, 0, first_id]]
                        else:
                            E[last_id].append([k_E - 1, 0, first_id])

            if first_id not in E.keys():
                E[first_id] = [list_E]
            else:
                E[first_id].append(list_E)
        return

    subgraph_concepts(axiom_normalized)
    print(f'E_R built! number of edges {k_E}.')

    E_R = {}
    k_E_role = copy.deepcopy(k_E)
    def sub_graph_role(axioms_roles):
        nonlocal E_R, k_E, l_concepts_part_orginal  # E_last_part
        for i, line in enumerate(axioms_roles):
            line_s = line.split('<')[1:]
            first_role, last_role = line_s[0].split('>')[0][2:], line_s[1].split('>')[0][2:]
            indE2id_original_axiom[k_E] = l_concepts_part_orginal + i
            if first_role in E_R:
                E_R[first_role].append([k_E, 0, last_role])
            else:
                E_R[first_role] = [[k_E, 0, last_role]]
            k_E += 1
        return

    sub_graph_role(axiom_roles_inclusion)
    print(f'E_R built! number of edges {len(axiom_roles_inclusion)}.')

    jsobj1 = json.dumps(indE2id_original_axiom)
    fileObject1 = open('{}/data/indE2id_original_axiom.json'.format(path_ontology), 'w')
    fileObject1.write(jsobj1)
    fileObject1.close()

    jsobj1 = json.dumps(E)
    fileObject1 = open('{}/data/E.json'.format(path_ontology), 'w')
    fileObject1.write(jsobj1)
    fileObject1.close()

    jsobj1 = json.dumps(E_R)
    fileObject1 = open('{}/data/E_R.json'.format(path_ontology), 'w')
    fileObject1.write(jsobj1)
    fileObject1.close()

    jsobj1 = json.dumps(D_edge)
    fileObject1 = open('{}/data/D_edge.json'.format(path_ontology), 'w')
    fileObject1.write(jsobj1)
    fileObject1.close()

    print('preprocessing progress finished in {}!'.format(time.time() - start_time_t))
    return k_E_role
