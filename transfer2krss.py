from src.tools import trans, trans_back

# path = 'workspace/nci-16/nci-16.owl.krss'
#
# f1 = open('nci-16.owl', 'w')
# with open(path, 'r') as f:
#     data = f.readlines()
#     for line in data:
#         line_owl = trans_back(line)
#         f1.write(line_owl)
#
# print('finish!')


#path = 'workspace/snomedct012016/terminologyWithDeclaration.owl'
#path = 'workspace/nci-16/terminologyWithDeclaration.owl'
#path = 'workspace/snomedct2021_Snapshot/terminologyWithDeclaration.owl'
# path = 'workspace/snomedct2021_snapshot/snomedct2021_normalized.owl'

# f1 = open('workspace/snomedct2021_snapshot/snomedct2021_normalized.krss.owl', 'w')

ont_name = "el_test1"

path = f"workspace/{ont_name}/ontology.owl"
f1 = open(f"workspace/{ont_name}/ontology.krss.owl", "w")
with open(path, 'r') as f:
    data = f.readlines()
    for line in data:
        if line[0] == 'E' or line[0] == 'S':
            line_krss = trans(line)
            line_new = line_krss.replace("<", "").replace(">", "")
            f1.write(line_new)

f1.close()

print('finish!')