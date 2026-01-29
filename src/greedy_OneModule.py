class greedy_search(object):
    def __init__(self, clauses, answer_literals, root='1'):
        self.clauses = clauses
        self.answer_literals = answer_literals
        self.root = root
        self.history_result = {}

    def search(self, node, history=set([])):
        assert node in self.clauses, f"node {node} not in self.clauses"
        if node in self.history_result:
            return self.history_result[node]

        new_history = history | set([node])

        premises = self.clauses[node]
        result_candidates, l_candidate = set([]), 0
        if isinstance(premises, set):
            for n in premises:
                if n in self.answer_literals:
                    result_candidates.add(n)
                else:
                    if n not in new_history:
                        new_result = self.search(n, new_history)
                        #result_candidates.update(new_result)
                        if new_result:
                            result_candidates.update(new_result)
                        else:
                            return set([])
                    else:
                        return set([])
        else:
            premises_filtered = set([frozenset(s) for s in self.clauses[node]])
            for pre_list in premises_filtered:
                result_current = set([])
                for n in pre_list:
                    if n in self.answer_literals:
                        result_current.add(n)
                    else:
                        if n not in new_history:
                            new_result = self.search(n, new_history)
                            #result_current.update(new_result)
                            if new_result:
                                result_current.update(new_result)
                            else:
                                break
                        else:
                            break
                else:
                    if l_candidate == 0 or len(result_current) < l_candidate:
                        result_candidates, l_candidate = result_current, len(result_current)

        if result_candidates:
            self.history_result[node] = result_candidates

        return result_candidates


