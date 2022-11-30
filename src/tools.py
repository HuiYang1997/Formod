import os
from copy import deepcopy
import signal


def set_timeout(num, callback):
    def wrap(func):
        def handle(signum, frame):  # 收到信号 SIGALRM 后的回调函数，第一个参数是信号的数字，第二个参数是the interrupted stack frame.
            raise RuntimeError

        def to_do(*args, **kwargs):
            try:
                signal.signal(signal.SIGALRM, handle)  # 设置信号和回调函数
                signal.alarm(num)  # 设置 num 秒的闹钟
                #print('start alarm signal.')
                r = func(*args, **kwargs)
                #print('close alarm signal.')
                signal.alarm(0)  # 关闭闹钟
                return r
            except RuntimeError as e:
                callback()

        return to_do
    return wrap


def after_timeout():  # 超时后的处理函数
    print("Time out!")


def trans(axioms):
    return axioms.replace('SubClassOf(', '(implies ').replace('EquivalentClasses(', '(equivalent ', ).replace(
        'ObjectSomeValuesFrom(', '(some ').replace('ObjectIntersectionOf(', '(and ').replace('SubObjectPropertyOf(', '(implies-role ')

def axiom_without_role_concepts(axioms):
    result = ''
    for a in axioms.split('<'):
        if '>' in a:
            result += a.split('>')[1]
        else:
            result += a
    return result


def transform_ObjectComplementOf(axioms):
    if 'ObjectComplementOf(' in axiom_without_role_concepts(axioms):
        axioms_s = axioms.split('(')
        result, i = '', 0
        while i < len(axioms_s):
            a = axioms_s[i]
            l = len('ObjectComplementOf')
            if len(a) > l and a[-l:] == 'ObjectComplementOf':
                result += a[:-l]
                a_next = axioms_s[i + 1].split(')', 1)
                if len(a_next) < 2:  # mean is have form 'ObjectComplementOf((some...'
                    result += '(complement '
                else:
                    assert len(a_next) == 2 and a_next[0][0] == '<'
                    result += '<-' + a_next[0][1:] + a_next[1] + '('
                    i += 1
            else:
                result += a + '('
            i += 1
        return result[:-1]
    else:
        return axioms


def cut_axiom(one_axiom):
    '''
    :param one_axiom: str ... str (...(...))(...) str(...)
    :return: [str,'',str,'','',str,'',], [...,(...(...)),(...),(...)]
    '''
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


def renew_tuple(K, B):
    if B in K:
        if isinstance(K, list):
            return tuple(sorted(K))
        else:
            assert isinstance(K, tuple)
            return K
    else:
        if isinstance(K, list):
            K_new = deepcopy(K)
        else:
            K_new = list(K)
        K_new.append(B)
        result = tuple(sorted(K_new))

        return result


def clause2axiom(clause):
    result = '(implies '
    if clause[0] == 'H2rK':
        if len(clause[1]) == 1:
            result += clause[1][0] + ' '
        else:
            result += f'(and {",".join(clause[1])})'

        result += f'(some {clause[2]} '

        if len(clause[3]) == 1:
            result += clause[3][0] + '))'
        else:
            result += f'(and {",".join(clause[1])})))'
        return result

    elif clause[0] == 'H2A':
        if len(clause[1]) == 1:
            result += clause[1][0] + ' '
        else:
            result += f'(and {",".join(clause[1])}) '

        result += clause[2] + ')'
        return result

    elif clause[0] == 'H2rK2M':
        if len(clause[1]) == 1:
            result += clause[1][0] + ' '
        else:
            result += f'(and {",".join(clause[1])}) '

        if clause[4]:
            result += '(union ' + ','.join(clause[4]) + ' '

        result += f'(some {clause[2]} '

        if len(clause[3]) == 1:
            result += clause[3][0] + ')'
        else:
            result += f'(and {",".join(clause[1])}))'

        if clause[4]:
            result += '))'
        else:
            result += ')'
        return result

    elif clause[0] == 'H2M':
        if len(clause[1]) == 1:
            result += clause[1][0] + ' '
        else:
            result += f'(and {",".join(clause[1])}) '

        if len(clause[2]) == 1:
            result += clause[2][0] + ')'
        else:
            result += f'(union {",".join(clause[1])}))'
        return result

    else:
        return False

def inverse(A):
    if A[0] == '-':
        return A[1:]
    else:
        return '-' + A

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
        l_new = deepcopy(l)
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
    return result_di
# def unfold(dic, type=None, out=None):
#     result_dic = {}
#     current_key = set([])
#     calculated_key = set([])
#     flag_loop = False
#
#     def unfold_A(k):
#         nonlocal result_dic, current_key, flag_loop, calculated_key, dic
#         if k in result_dic:
#             return set(result_dic[k])
#         else:
#             current_key.add(k)
#             calculated_key.add(k)
#             if type:
#                 result = set([])
#             else:
#                 result = set(dic[k])
#             for n in dic[k]:
#                 if n == k:
#                     continue
#                 if n in current_key:
#                     flag_loop = True
#                     continue
#                 if n in calculated_key:
#                     if n in result_dic:
#                         result.update(result_dic[n])
#                     continue
#                 elif n not in dic:
#                     result.add(n)
#                 else:
#                     result.update(unfold_A(n))
#             current_key.remove(k)
#             if not current_key:
#                 flag_loop = False
#                 calculated_key = set([])
#             if not flag_loop:
#                 if out:
#                     result_dic[k] = list(result)
#                 else:
#                     result_dic[k] = result
#             # return list(result)
#             return result
#
#     for k in dic:
#         assert current_key == set([])
#         assert calculated_key == set([])
#         assert flag_loop == False
#         unfold_A(k)
#     return result_dic


# count how many times '(some', '(and', '(union', '(complement' appears in one axiom
def depth_bigger_than(one_axiom, k):
    axiom_split = one_axiom.split('(')
    i = 0
    for s in axiom_split:
        if s:
            if s[0] in ['a', 's', 'u', 'c']:
                i += 1
            if i >= k:
                return True
    return False


def trans_back(axioms):
    return axioms.replace('(implies ', 'SubClassOf(').replace('(equivalent ', 'EquivalentClasses(').replace('(some ',
                                                                                                            'ObjectSomeValuesFrom(').replace(
        '(and ', 'ObjectIntersectionOf(').replace('(all', 'ObjectAllValuesFrom( ')


def formal_form(a):
    '''
    :param a: "some r A" , "and A B C..." , "union A B C ..." or "SubObjectPropertyOf(...r1, r2...)"
    :return: "some r A"  , "ABC..." %sorted% , "ABC..." %sorted% or (..r1,r2,...) %same order as above%
    '''
    if a[0] == 's' or a[0] == 'c':
        return a
    elif a[0] == 'a' or a[0] == 'u':
        a_s = ''.join(sorted(a.split(' ')[1:]))
        return a_s
    else:
        assert a[0] == 'S'
        result = '\t'.join([a_s.split('>')[0] for a_s in a.split('<')[1:]])
        return result


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

def unfold(dic, type=None, out=None):
    '''

    :param dic: input dictionary
    :param type: if type is true, we do not include the initial edges in the graph
    :param out: if out is true, the we the set of nodes A is connected to is collect in a list
    :return:
    '''
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

def split_two_part(axiom, type='sort'):
    axiom_s = axiom.split('(')[1:]
    if len(axiom_s) < 2:
        axiom_s_new = axiom.split('<')
        return False, (axiom_s_new[1].split('>')[0],), (axiom_s_new[2].split('>')[0],)

    if '<' in axiom_s[0]:  # (... (...))
        first_term = axiom_s[0].split('<')[1].split('>')[0]
        axiom_last_list = axiom_s[1].split('<')[1:]
        last_part = [a.split('>')[0] for a in axiom_last_list]
        if type == 'sort':
            return True, (first_term,), tuple(sorted(last_part))
        else:
            return True, (first_term,), last_part

    else:  # ((...)...)
        axiom_s = axiom.split(')')
        last_term = axiom_s[1].split('<')[1].split('>')[0]
        axiom_last_list = axiom_s[0].split('<')[1:]
        first_part = [a.split('>')[0] for a in axiom_last_list]
        if type == 'sort':
            return False, tuple(sorted(first_part)), (last_term,)
        else:
            return False, first_part, (last_term,)