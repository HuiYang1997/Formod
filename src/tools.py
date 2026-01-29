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


def replace_el_plus_role_pattern(concept_str):
    """
    Replace EL+ role patterns in a concept string (n>=1):
    1. if input string is of the form "(some <-r1-r2...-rn+t> C1)", replace it with "(some <t> C1) and (some <r1> (some <r2> (... (some <rn> X)...)))", where X is a place-holder
    2. if input string is of the form "(some <-r1-r2...-rn> C1)", replace it with "(some <r1> (some <r2> (... (some <rn> C1)...)))"
    3. if input string is of the form  "(some <+t> C1)", replace it with (some <t> C1)
    4. else, let C1 be the input string


    Note that, all the replacement above is recursively done. That is, we will do it again for C1, there are two cases:
    a. if C1 is of the form (some <xxx> C2), then repeat the process above to C1;
    b. if C1 is of the form (and C2 ... Cn), then repeat the process above for each C2, ... Cn.
    
    Attention: 
    (i) Case 1 could only happen in the first time. the following steps only meet case 3, 4 (raise error if not)
    (ii) Once the case 2 happened, the following steps should only be case 2 or 4 (raise error if not)

    Parameters
    ----------
    concept_str : str
        The concept string to process
        
    Returns
    -------
    str1: The processed concept string with EL+ patterns replaced
    str2: return the string containing place-holder X for case 1, return empty string for other cases.
    """
    
    def parse_concept(s, pos=0):
        """
        Parse a concept expression starting at position pos.
        Returns (concept_string, end_position).
        Handles: <atomic>, (some <role> C), (and C1 C2 ... Cn)
        """
        s = s.strip()
        if pos >= len(s):
            return "", pos
        
        # Skip whitespace
        while pos < len(s) and s[pos] == ' ':
            pos += 1
        
        if pos >= len(s):
            return "", pos
        
        if s[pos] == '<':
            # Atomic concept <name>
            end = s.find('>', pos)
            if end == -1:
                return s[pos:], len(s)
            return s[pos:end+1], end + 1
        elif s[pos] == '(':
            # Complex expression - find matching closing paren
            paren_count = 1
            start = pos
            pos += 1
            while pos < len(s) and paren_count > 0:
                if s[pos] == '(':
                    paren_count += 1
                elif s[pos] == ')':
                    paren_count -= 1
                pos += 1
            return s[start:pos], pos
        else:
            # Unknown format, read until space or end
            end = pos
            while end < len(s) and s[end] not in ' ()':
                end += 1
            return s[pos:end], end
    
    def parse_and_conjuncts(and_content):
        """
        Parse the content inside (and ...) to extract individual conjuncts.
        Returns list of conjunct strings.
        """
        # and_content is the part after "(and " and before final ")"
        conjuncts = []
        pos = 0
        while pos < len(and_content):
            while pos < len(and_content) and and_content[pos] == ' ':
                pos += 1
            if pos >= len(and_content):
                break
            concept, new_pos = parse_concept(and_content, pos)
            if concept:
                conjuncts.append(concept)
            pos = new_pos
        return conjuncts
    
    def process_recursive(expr, mode='initial'):
        """
        Process expression recursively.
        mode: 'initial' - first call, Case 1 allowed
              'after_case1' - after Case 1, only Case 3, 4 allowed
              'after_case2' - after Case 2, only Case 2, 4 allowed
        
        Returns: (processed_str, placeholder_str)
        """
        expr = expr.strip()
        
        # Case 4: atomic concept or non-some expression
        if not expr.startswith('(some '):
            # Check if it's (and ...)
            if expr.startswith('(and '):
                # Extract content between "(and " and final ")"
                inner = expr[5:-1]  # remove "(and " and ")"
                conjuncts = parse_and_conjuncts(inner)
                processed_conjuncts = []
                all_placeholders = []
                for conj in conjuncts:
                    proc, ph = process_recursive(conj, mode)
                    processed_conjuncts.append(proc)
                    if ph:
                        all_placeholders.append(ph)
                result = '(and ' + ' '.join(processed_conjuncts) + ')'
                placeholder = ' '.join(all_placeholders) if all_placeholders else ''
                return result, placeholder
            # Not a some or and expression - return as is
            return expr, ''
        
        # Parse (some <role> C1)
        # Find the role part
        role_start = expr.find('<')
        role_end = expr.find('>', role_start)
        if role_start == -1 or role_end == -1:
            return expr, ''
        
        role = expr[role_start+1:role_end]  # role without < >
        
        # Find C1 (the inner concept after the role)
        c1_start = role_end + 2  # skip "> "
        c1_end = len(expr) - 1   # exclude final ")"
        c1 = expr[c1_start:c1_end].strip()
        
        # Determine which case we're in based on role pattern
        has_plus = '+' in role
        has_minus = role.startswith('-')
        
        if has_minus and has_plus:
            # Case 1: (some <-r1-r2...-rn+t> C1)
            # Only allowed in initial mode
            if mode != 'initial':
                raise ValueError(f"Case 1 pattern found in non-initial mode: {expr}")
            
            # Parse: -r1-r2-...-rn+t
            # Split by '+' first to get chain part and target
            parts = role.split('+')
            chain_part = parts[0]  # -r1-r2-...-rn
            target_role = parts[1]  # t
            
            # Extract chain roles (split by '-', skip empty)
            chain_roles = [r for r in chain_part.split('-') if r]
            
            # Process C1 recursively with 'after_case1' mode
            c1_processed, c1_placeholder = process_recursive(c1, 'after_case1')
            
            # Build result: (some <t> C1_processed)
            main_result = f'(some <{target_role}> {c1_processed})'
            
            # Build placeholder: (some <r1> (some <r2> (... (some <rn> X)...)))
            placeholder = 'X'
            for r in reversed(chain_roles):
                placeholder = f'(some <{r}> {placeholder})'
            
            return main_result, placeholder
        
        elif has_minus and not has_plus:
            # Case 2: (some <-r1-r2...-rn> C1)
            if mode == 'after_case1':
                raise ValueError(f"Case 2 pattern found after Case 1: {expr}")
            
            # Extract chain roles
            chain_roles = [r for r in role.split('-') if r]
            
            # Process C1 recursively with 'after_case2' mode
            c1_processed, _ = process_recursive(c1, 'after_case2')
            
            # Build nested some: (some <r1> (some <r2> (... (some <rn> C1_processed)...)))
            result = c1_processed
            for r in reversed(chain_roles):
                result = f'(some <{r}> {result})'
            
            return result, ''
        
        elif has_plus and not has_minus:
            # Case 3: (some <+t> C1)
            if mode == 'after_case2':
                raise ValueError(f"Case 3 pattern found after Case 2: {expr}")
            
            # Remove the leading +
            actual_role = role[1:]  # remove '+'
            
            # Process C1 recursively (keep same mode)
            c1_processed, c1_placeholder = process_recursive(c1, mode)
            
            result = f'(some <{actual_role}> {c1_processed})'
            return result, c1_placeholder
        
        else:
            # Case 4: regular (some <role> C1) - no special pattern
            # Process C1 recursively (keep same mode)
            c1_processed, c1_placeholder = process_recursive(c1, mode)
            result = f'(some <{role}> {c1_processed})'
            return result, c1_placeholder
    
    result, placeholder = process_recursive(concept_str)
    
    print("-------------replacement--------------")
    print(f"old: {concept_str}")
    print(f"new: {result}")
    print(f"placeholder: {placeholder}")
    print("-----------------------------------")
    
    return result, placeholder