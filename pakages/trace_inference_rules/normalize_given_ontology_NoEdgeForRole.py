import time
import copy
import json
import pickle
from tqdm import tqdm
from pakages.trace_inference_rules.tools import unfold, count_andAsome, trans_back, formal_form, mkdir


def normalize(path_ontology, name_ontology):
    start_time = time.time()
    axiom_ini, axiom_ini_role, axiom_rst = [], [], []
    dic_t_r, dic_t_s, dic_tr_s = {}, {}, {}
    mkdir('{}/data'.format(path_ontology))

    # we will ignore all axioms that contain term in the following list:
    split_box = ['ObjectUnionOf', 'ObjectComplementOf', 'ObjectOneOf', 'ObjectAllValuesFrom',
                 'ObjectHasValue', 'ObjectHasSelf', 'ObjectMinCardinality', 'ObjectMaxCardinality',
                 'ObjectExactCardinality', 'DataSomeValuesFrom', 'DataAllValuesFrom', 'DataHasValue',
                 'DataMinCardinality', 'DataMaxCardinality', 'DataExactCardinality', 'Declaration', 'ClassAxiom',
                 'ObjectPropertyAxiom', 'DataPropertyAxiom', 'DatatypeDefinition', 'HasKey', 'Assertion', 'Annotation',
                 'Datatype', 'DataIntersectionOf', 'DataUnionOf', 'DataComplementOf', 'DataOneOf',
                 'DatatypeRestriction',
                 'DisjointClasses', 'DisjointUnion', 'EquivalentObjectProperties', 'DisjointObjectProperties',
                 'InverseObjectProperties', 'ObjectPropertyDomain', 'ObjectPropertyRange', 'FunctionalObjectProperty',
                 'InverseFunctionalObjectProperty', 'ReflexiveObjectProperty', 'IrreflexiveObjectProperty',
                 'SymmetricObjectProperty', 'AsymmetricObjectProperty', 'TransitiveObjectProperty', 'SubDataPropertyOf',
                 'EquivalentDataProperties', 'DisjointDataProperties', 'DataPropertyDomain', 'DataPropertyRange',
                 'FunctionalDataProperty', 'SameIndividual', 'DifferentIndividuals', 'ClassAssertion',
                 'ObjectPropertyAssertion', 'NegativeObjectPropertyAssertion', 'DataPropertyAssertion',
                 'NegativeDataPropertyAssertion']

    concept2id, count_c = {}, 0
    relation2id, count_r = {}, 1

    def trans(axioms):
        nonlocal concept2id, relation2id, count_r, count_c, concepts_appeared, relation_appeared

        axioms_s = axioms.split('<')
        if 'Annotation' in axioms_s[0]:
            result = axioms_s[0].split('(')[0] + '('
            l_start = 2
        else:
            result = axioms_s[0]
            l_start = 1

        for part in axioms_s[l_start:]:
            part_s = part.split('>')
            assert len(part_s) == 2
            if part_s[0] in concepts_appeared:
                if part_s[0] not in concept2id:
                    concept2id[part_s[0]] = count_c
                    count_c += 1
                result += '<#c' + str(concept2id[part_s[0]]) + '>'
            else:
                assert part_s[0] in relation_appeared
                if part_s[0] not in relation2id:
                    relation2id[part_s[0]] = count_r
                    count_r += 1
                result += '<#r' + str(relation2id[part_s[0]]) + '>'
            result += part_s[1]

        return result.replace('SubClassOf(', '(implies ').replace('EquivalentClasses(', '(equivalent ').replace(
            'ObjectSomeValuesFrom(', '(some ').replace('ObjectIntersectionOf(', '(and ')

    def update_dic_r_s_t(a):
        nonlocal dic_t_r, dic_t_s, dic_tr_s, relation2id, count_r
        a_s = a.split('#r')[1:]
        r, s, t = int(a_s[0].split('>')[0]), int(a_s[1].split('>')[0]), int(a_s[2].split('>')[0])
        if t in dic_t_r:
            dic_t_r[t].add(r)
        else:
            dic_t_r[t] = {r}

        if t in dic_t_s:
            dic_t_s[t].add(s)
        else:
            dic_t_s[t] = {s}

        if (t, r) in dic_tr_s:
            dic_tr_s[(t, r)].add(s)
        else:
            dic_tr_s[(t, r)] = {s}

    concepts_appeared = set([])
    relation_appeared = set([])
    f1 = open(f'{path_ontology}/data/{name_ontology}_processed.owl', 'w')
    f1.write(
        'Prefix(:=<urn:absolute:galen7.owl#>)\nPrefix(owl:=<http://www.w3.org/2002/07/owl#>)\nPrefix(rdf:=<http://www.w3.org/1999/02/22-rdf-syntax-ns#>)\nPrefix(xml:=<http://www.w3.org/XML/1998/namespace>)\nPrefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)\nPrefix(rdfs:=<http://www.w3.org/2000/01/rdf-schema#>)\nPrefix(skos:=<http://www.w3.org/2004/02/skos/core#>)\n\nOntology(\n')
    with open(f'{path_ontology}/{name_ontology}.owl', 'r') as f:
        f_data = f.readlines()
        for row in f_data:
            if '<' not in row:
                continue
            if row[:2] == 'De':
                term = row.split('<')[1].split('>')[0]
                if row[12] == 'O':
                    relation_appeared.add(term)
                elif row[12] == 'C':
                    concepts_appeared.add(term)
        print(len(concepts_appeared), len(relation_appeared))

        for row in f_data:
            if '<' not in row or row[0] not in ['E', 'S']:
                continue
            else:
                f = False
                for s in split_box:
                    if s in row:
                        # print(s,row)
                        f = True
                        break
                if f:
                    continue
            row_new = trans(row)[:-1]
            if row[3] == 'O':  # 'SubObjectPropertyof(...)'
                if 'Chain' in row:
                    update_dic_r_s_t(row_new)  # r\circ s belongs to t
                    axiom_rst.append(row_new)
                else:
                    axiom_ini_role.append(row_new)  # r belongs to s
            else:
                axiom_ini.append(row_new)
            f1.write(trans_back(row_new) + '\n')
    f1.write(')\n')
    f1.close()
    elapse = time.time() - start_time
    print("data loaded in time {:5.2f}".format(elapse))
    print("input ontology:________\n#relation:", len(relation2id), "#concepts:", len(concept2id),
          "\n\t#axiom(role chain inclusion):", len(axiom_rst), "#axiom(role inclusion):", len(axiom_ini_role),
          "#axiom(others):", len(axiom_ini), )
    count_c_1 = copy.deepcopy(count_c)

    axiom_normalized = []
    normalized_term = {}
    current_axiom_id = 0
    current_normalized_axiom_id = 0
    a2a_n = {}
    id_normalize2id_original_axiom = {}

    def cut_axiom(one_axiom):
        l, i = len(one_axiom), 0
        result_str, result, type_1 = '', [], 'outside'
        while i < l:
            if type_1 == 'outside':
                if one_axiom[i] == '(':
                    type_1 = 'inside'
                    i += 1
                else:
                    result_str += one_axiom[i]
                    i += 1
            else:
                count, count_term_1, start_id = 0, 1, i
                while i < l:
                    if one_axiom[i] == '(':
                        count_term_1 += 1
                    elif one_axiom[i] == ')':
                        count_term_1 -= 1
                        if count_term_1 == 0:
                            result.append(one_axiom[start_id:i])
                            result_str += '*'
                            i += 1
                            type_1 = 'outside'
                            break
                    i += 1
        return result_str.split('*'), result

    def normalize(one_axiom, type):
        nonlocal current_axiom_id, current_normalized_axiom_id, count_c, normalized_term, original2id, a2a_n
        if count_andAsome(one_axiom, 2):
            if type == 'begin':
                # get the item **** inside (equi\implies <#...> (****) )
                axiom_str_rest, axiom_cutted = cut_axiom(one_axiom[1:-1])
                result = axiom_str_rest[0]
                assert len(axiom_cutted) <= 2
                for i, one_axiom_cutted in enumerate(axiom_cutted):
                    if len(result.split('<')) >= 2:
                        k = 2
                        result += '('
                    else:
                        k = 1
                    while count_andAsome(one_axiom_cutted, k):
                        one_axiom_cutted = normalize(one_axiom_cutted, 'middle')
                    result += one_axiom_cutted
                    if k == 2:
                        result += ')'
                    result += axiom_str_rest[i + 1]
                if type == 'begin':
                    return '(' + result + ')'
            else:
                axiom_str_rest, axiom_cutted = cut_axiom(one_axiom)
                result = axiom_str_rest[0]
                for i, one_axiom_cutted in enumerate(axiom_cutted):
                    while count_andAsome(one_axiom_cutted, 1):
                        one_axiom_cutted = normalize(one_axiom_cutted, 'middle')
                    result += one_axiom_cutted
                    result += axiom_str_rest[i + 1]
                return result

        else:
            if type == 'begin':
                return one_axiom
            else:
                one_axiom_form = formal_form(one_axiom)
                if one_axiom_form not in normalized_term.keys():
                    concept2id['#N{}'.format(count_c)] = count_c
                    axiom_normalized.append('(equivalent <#N{}> ('.format(count_c) + one_axiom + '))')
                    current_normalized_axiom_id += 1
                    normalized_term[one_axiom_form] = '<#N{}>'.format(str(count_c))
                    count_c += 1
                elif one_axiom_form in original2id:
                    id_correspond = original2id[one_axiom_form]
                    if id_correspond not in a2a_n:
                        a2a_n[id_correspond] = {current_axiom_id}
                    else:
                        a2a_n[id_correspond].add(current_axiom_id)
                return normalized_term[one_axiom_form]

    original2id = {}

    def pre_process(axioms):
        nonlocal normalized_term
        for id, one_axiom in enumerate(axioms):
            if one_axiom[1] == 'e':
                if len(one_axiom.split('(')) > 2 and not count_andAsome(one_axiom, 2):
                    l, i, = len(one_axiom), 0
                    # get the item **** inside (equi\implies <#...> (****) )
                    count_term, start_id, end_id = 0, -1, -1
                    while i < l:
                        if one_axiom[i] == '(':
                            count_term += 1
                            if count_term == 2 and start_id < 0:
                                start_id = i + 1
                        elif one_axiom[i] == ')':
                            count_term -= 1
                            if count_term == 1:
                                end_id = i
                        i += 1
                    one_axiom_form = formal_form(one_axiom[start_id: end_id])
                    first_term = one_axiom.split(' ')[1]
                    if one_axiom_form not in normalized_term.keys():
                        original2id[one_axiom_form] = id
                        normalized_term[one_axiom_form] = first_term

    i = 0
    pre_process(axiom_ini)
    print(axiom_ini)
    for axiom in tqdm(axiom_ini):
        i += 1
        axiom_normalized.append(normalize(axiom, 'begin'))
        id_normalize2id_original_axiom[current_normalized_axiom_id] = current_axiom_id
        current_normalized_axiom_id += 1
        current_axiom_id += 1
    print("after normalized on axioms(others):_________\n", '\t#axioms:', current_normalized_axiom_id, '#concepts:',
          count_c, "#relation unchange.")

    with open(f'pakages/elk-tools/{name_ontology}_normalized.txt', 'w') as f:
        for axiom in axiom_normalized:
            f.write(axiom + '\n')

    with open('{}/data/role_inclusion.txt'.format(path_ontology), 'w') as f:
        for axiom in axiom_ini_role:
            f.write(axiom + '\n')

    r_class_direct = {}
    for line in axiom_ini_role:
        line_s = line.split('<')
        first_role, last_role = int(line_s[1].split('>')[0][2:]), int(line_s[2].split('>')[0][2:])
        if last_role in r_class_direct:
            r_class_direct[last_role].update([first_role, last_role])
        else:
            r_class_direct[last_role] = {first_role, last_role}

    r_class = unfold(r_class_direct)
    r_class_inverse = {}
    for r in r_class:
        for s in r_class[r]:
            if s not in r_class_inverse:
                r_class_inverse[s] = {r}
            else:
                r_class_inverse[s].add(r)

    for i in range(1, count_r):
        if i not in r_class:
            r_class[i] = {i}
        if i not in r_class_inverse:
            r_class_inverse[i] = {i}
    with open('{}/data/M_R.pickle'.format(path_ontology), 'wb') as f:
        pickle.dump(r_class, f)
    with open('{}/data/M_R_inverse.pickle'.format(path_ontology), 'wb') as f:
        pickle.dump(r_class_inverse, f)
    with open('{}/data/a2a_n.pickle'.format(path_ontology), 'wb') as f:
        pickle.dump(a2a_n, f)

    dic_t_r_new = {}
    for t in dic_t_r:
        new_value = copy.deepcopy(dic_t_r[t])
        for r in dic_t_r[t]:
            if r in r_class:
                new_value.update(r_class[r])
        dic_t_r_new[t] = new_value

    # add  dic_t_r[t1] to  dic_t_r[t] if t1\sqsubsequent t, and dic_tr_s[(t1,r1)] to  dic_tr_s[(t,r)] if t1\sqsubsequent t,r\sqsubsequence r1
    for t in r_class:
        r_value = set([])
        for t1 in r_class[t]:
            if t1 in dic_t_r_new:
                r_value.update(dic_t_r_new[t1])
        if r_value:
            dic_t_r[t] = r_value

    dic_tr_s_new = {}
    for t, r in dic_tr_s:
        new_value = copy.deepcopy(dic_tr_s[(t, r)])
        for s in dic_tr_s[(t, r)]:
            if s in r_class:
                new_value.update(r_class[s])
        dic_tr_s_new[(t, r)] = new_value

    with open('{}/data/dic_t_r.pickle'.format(path_ontology), 'wb') as f:
        pickle.dump(dic_t_r, f)
    with open('{}/data/dic_tr_s.pickle'.format(path_ontology), 'wb') as f:
        pickle.dump(dic_tr_s_new, f)
    with open('{}/data/dic_tr_s_original.pickle'.format(path_ontology), 'wb') as f:
        pickle.dump(dic_tr_s, f)

    jsobj_n = json.dumps(id_normalize2id_original_axiom)
    fileObject_n = open('{}/data/id_normalize2id_original_axiom.json'.format(path_ontology), 'w')
    fileObject_n.write(jsobj_n)
    fileObject_n.close()

    r2A_correspond = {}

    def get_r_A(a):
        '''
        :param a:  axioms of form "(equivalent N (some r A))"
        :return: "some r A", "N"
        '''
        nonlocal count_c, r2A_correspond
        ND = a.split('<')[1].split('>')[0]
        r_id = int(a.split('#r')[1].split('>')[0])
        A_id = int(a.split('#')[-1].split('>')[0][1:])
        last_id = r_id * count_c + A_id
        if r_id in r2A_correspond:
            r2A_correspond[r_id].add(A_id)
        else:
            r2A_correspond[r_id] = {A_id}
        return last_id, int(ND[2:])

    # for all axioms "A\sqsubset (\exists_r.B)", add new definition "D\equi (\exists_r.B)" if there is no such axioms.
    # step 1: record " \exists_r.B " have been defined.
    dicND2r_A = {}
    Defined_r_A = set([])
    r_A_appear2id = {i: str(i) for i in range(count_c)}
    for a in axiom_normalized:
        a_s = a.split('(')
        l = len(a_s)
        if l == 3 and a_s[2][0] == 's':
            r_A_id, N_id = get_r_A(a)
            if a[1] == 'e':
                r_A_appear2id[r_A_id] = str(N_id)
                dicND2r_A[N_id] = [N_id, r_A_id]
                Defined_r_A.add(r_A_id)
            else:
                assert a[1] == 'i'

    # step 2: find undefined " \exists_r.B" and add definition.
    axiom_new_defined = []
    count_new_define = copy.deepcopy(count_c)
    for r_id in r2A_correspond:
        for A_id in r2A_correspond[r_id]:
            r_A_id = r_id * count_c + A_id
            if r_A_id not in Defined_r_A:
                r_A_appear2id[r_A_id] = str(r_A_id)
                dicND2r_A[count_new_define] = [r_A_id]
                Defined_r_A.add(r_A_id)
                # axiom_new_defined.append(f'(equivalent <#D{str(count_new_define)}> (some <#r{r_id}> <#c{A_id}>))')
                if A_id >= count_c_1:
                    axiom_new_defined.append(f'(equivalent <#D{str(count_new_define)}> (some <#r{r_id}> <#N{A_id}>))')
                else:
                    axiom_new_defined.append(f'(equivalent <#D{str(count_new_define)}> (some <#r{r_id}> <#c{A_id}>))')
                count_new_define += 1
    print('#axiom_new_defined (step1: exit (r,A)):', len(axiom_new_defined))
    dic_t_A = {}
    dic_t_s_new = {}
    for t in dic_t_s:
        new_value = copy.deepcopy(dic_t_s[t])
        for s in dic_t_s[t]:
            if s in r_class:
                new_value.update(r_class[s])
        dic_t_s_new[t] = new_value

    dic_t_s = unfold(dic_t_s_new)
    for t in dic_t_s:
        new_value = set([])
        for s in dic_t_s[t]:
            if s in r2A_correspond:
                new_value.update(r2A_correspond[s])
            if s in r_class:
                for s1 in r_class[s] & r2A_correspond.keys():
                    new_value.update(r2A_correspond[s1])
        dic_t_A[t] = new_value

    count_c_addtional = copy.copy(count_new_define) - 1
    print('\t#result axioms:', count_c_addtional)
    for t in dic_t_s.keys():
        for A in dic_t_A[t]:
            t_A_id = t * count_c + A
            if t_A_id not in Defined_r_A:
                r_A_appear2id[t_A_id] = str(t_A_id)
                dicND2r_A[count_new_define] = [t_A_id]
                Defined_r_A.add(t_A_id)
                if A >= count_c_1:
                    axiom_new_defined.append(f'(equivalent <#D{str(count_new_define)}> (some <#r{t}> <#N{A}>))')
                else:
                    axiom_new_defined.append(f'(equivalent <#D{str(count_new_define)}> (some <#r{t}> <#c{A}>))')
                count_new_define += 1

    print('#axiom_new_defined (step 2, added (r,A) by "r\circ s \sqsubseteq t"):',
          count_new_define - count_c_addtional)
    print('\t#result axioms:', count_new_define)

    with open(f'pakages/elk-tools/{name_ontology}_normalized_new_defined.txt', 'w') as f:
        f.write(
            'Prefix(:=<urn:absolute:galen7.owl#>)\nPrefix(owl:=<http://www.w3.org/2002/07/owl#>)\nPrefix(rdf:=<http://www.w3.org/1999/02/22-rdf-syntax-ns#>)\nPrefix(xml:=<http://www.w3.org/XML/1998/namespace>)\nPrefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)\nPrefix(rdfs:=<http://www.w3.org/2000/01/rdf-schema#>)\nPrefix(skos:=<http://www.w3.org/2004/02/skos/core#>)\n\nOntology(\n')
        for axiom in axiom_normalized:
            f.write(trans_back(axiom) + '\n')
        for axiom in axiom_new_defined:
            f.write(trans_back(axiom) + '\n')
        for axiom in axiom_ini_role:
            f.write(trans_back(axiom) + '\n')
        for axiom in axiom_rst:
            f.write(trans_back(axiom) + '\n')
        f.write(')\n')

    jsobj1 = json.dumps(id_normalize2id_original_axiom)
    fileObject1 = open('{}/data/id_normalize2id_original_axiom.json'.format(path_ontology), 'w')
    fileObject1.write(jsobj1)
    fileObject1.close()

    jsobj1 = json.dumps(concept2id)
    fileObject1 = open('{}/data/{}_concept2id.json'.format(path_ontology, name_ontology), 'w')
    fileObject1.write(jsobj1)
    fileObject1.close()

    jsobj1 = json.dumps(dicND2r_A)
    fileObject1 = open('{}/data/dicND2r_A.json'.format(path_ontology), 'w')
    fileObject1.write(jsobj1)
    fileObject1.close()

    r2A_correspond_list = {}
    for k in r2A_correspond:
        r2A_correspond_list[k] = list(r2A_correspond[k])

    jsobj1 = json.dumps(r_A_appear2id)
    fileObject1 = open('{}/data/r_A_appear2id.json'.format(path_ontology), 'w')
    fileObject1.write(jsobj1)
    fileObject1.close()
    print('ontology has been normalized and saved!')
    return count_c, len(axiom_ini)
