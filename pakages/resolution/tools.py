def renew(S, a, b, type="add"):
    if type == "add":
        if a in S:
            S[a].add(b)
        else:
            if b:
                S[a] = {b}
            else:
                S[a] = set([])
    else:
        assert type == 'append'
        if a in S:
            S[a].append(b)
        else:
            if b:
                S[a] = [b]
            else:
                S[a] = []

def pair2dic(pairs):
    result = {}
    for p in pairs:
        renew(result, p[0], p[1], "add")

    return result
