def read_dna(dna_file):
    result = list()
    with open(dna_file, 'r') as f:
        dna = f.read().split('\n')[:-1]

    for i in dna:
        result.append(tuple(i.split(' <-> ')))

    return result


def is_rna(dna):
    dna_count, rna_count = 0, 0
    for i, j in dna:
        if not i or not j:
            continue

        if i in ['A', 'T', 'G', 'C'] and j in ['A', 'T', 'G', 'C']:
            dna_count += 1

        if i in ['A', 'U', 'G', 'C'] and j in ['A', 'U', 'G', 'C']:
            rna_count += 1

    if dna_count / len(dna) > 0.9:
        return 'DNA'
    elif rna_count / len(dna) > 0.9:
        return 'RNA'
    else:
        return 'Invalid'


def clean_dna(dna):
    t = is_rna(dna) == 'DNA'
    if type == 'Invalid':
        return None

    result = list()
    for i, j in dna:
        if not i and not j:
            continue
        elif not i or not j:
            check = True
            if not j:
                check = False
                i, j = j, i

            if j == 'G':
                i = 'C'
            elif j == 'C':
                i = 'G'
            elif j == 'A':
                i = 'T' if t else 'U'
            elif (t and j == 'T') or (not t and j == 'U'):
                i = 'A'
            else:
                continue

            result.append((i, j) if check else (j, i))
        else:
            if t and (i, j) in [('A', 'T'), ('T', 'A'), ('G', 'C'), ('C', 'G')]:
                result.append((i, j))
            elif not t and (i, j) in [('A', 'U'), ('U', 'A'), ('G', 'C'), ('C', 'G')]:
                result.append((i, j))

    return result


def mast_common_base(dna):
    count = {'A': 0, 'T': 0, 'G': 0, 'C': 0, 'U': 0}

    for i, j in dna:
        if i in ['A', 'T', 'G', 'C', 'U']:
            count[i] += 1

    return max(count, key=count.get)


def base_to_name(base):
    if base == 'A':
        return 'Adenine'
    elif base == 'T':
        return 'Thymine'
    elif base == 'G':
        return 'Guanine'
    elif base == 'C':
        return 'Cytosine'
    elif base == 'U':
        return 'Uracil'
    else:
        return 'Unknown'

