import os
import copy


def tensor_prod(l1, l2):
    result = []
    if not l1:
        return l2
    if not l2:
        return l1
    len1, len2 = len(l1), len(l2)
    for i in range(len1):
        for j in range(len2):
            combined_path = l1[i].union(l2[j])
            result.append(combined_path)
    return result


def filter(S_in):
    l = len(S_in)
    if l < 2:
        return S_in
    S = sorted(S_in, key=lambda i: len(i), reverse=False)
    result = []
    for s in S:
        if not s:
            continue

        flag_1 = False
        for e in result:
            if len(e) > len(s):
                continue
            if e.issubset(s):
                flag_1 = True
                break
        if flag_1:
            continue
        else:
            result.append(s)
    return result


def add_e(l1, e):
    assert l1
    result = []
    for l in l1:
        l_new = copy.deepcopy(l)
        l_new.add(e)
        result.append(l_new)
    return result


def delete_c(l, c):
    result = []
    for s in l:
        if c in s:
            continue
        else:
            result.append(s)
    return result


def unfold(dic, type=None, out=None):
    result_dic = {}
    current_key = set([])
    calculated_key = set([])
    flag_loop = False

    def unfold_A(k):
        nonlocal result_dic, current_key, flag_loop, calculated_key, dic
        if k in result_dic:
            return set(result_dic[k])
        else:
            current_key.add(k)
            calculated_key.add(k)
            if type:
                result = set([])
            else:
                result = set(dic[k])
            for n in dic[k]:
                if n == k:
                    continue
                # print(n)
                if n in current_key:
                    flag_loop = True
                    # print(current_key)
                    continue
                if n in calculated_key:
                    if n in result_dic:
                        result.update(result_dic[n])
                    continue
                elif n not in dic:
                    result.add(n)
                else:
                    result.update(unfold_A(n))
            current_key.remove(k)
            if not current_key:
                flag_loop = False
                calculated_key = set([])
            if not flag_loop:
                if out:
                    result_dic[k] = list(result)
                else:
                    result_dic[k] = result
            # return list(result)
            return result

    for k in dic:
        assert current_key == set([])
        assert calculated_key == set([])
        assert flag_loop == False
        unfold_A(k)
    return result_dic


# count how many times '(some' and '(and' appears in one axiom
def count_andAsome(one_axiom, k):
    axiom_split = one_axiom.split('(')
    i = 0
    for s in axiom_split:
        if s:
            if s[0] == 'a' or s[0] == 's':
                i += 1
            if i >= k:
                return True
    return False


def trans_back(axioms):
    return axioms.replace('(implies ', 'SubClassOf(').replace('(equivalent ', 'EquivalentClasses(').replace('(some ',
                                                                                                            'ObjectSomeValuesFrom(').replace(
        '(and ', 'ObjectIntersectionOf(')


def formal_form(a):
    '''
    :param a: "some r A" or "and A B C..."
    :return: "some r A" or "ABC..."(sorted)
    '''
    # print(a)
    if a[0] == 's':
        return a
    else:
        assert a[0] == 'a'
        a_s = ''.join(sorted(a.split(' ')[1:]))
        return a_s


def mkdir(path):
    folder = os.path.exists(path)
    if not folder:
        os.makedirs(path)


def update_equi(l, a, b):
    for s in l:
        if {a, b} & s:
            s.update({a, b})
        else:
            l.append({a, b})
    return l
