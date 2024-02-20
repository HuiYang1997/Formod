# ForMod

This is a protype algorithm of the algorithm ForMod.

To use this code, put the ontology on dictionary "workspace". For example, assume the ontology is "test.owl".
We require that:

1. "test.owl" is of fss format, and there is a copy "test.krss.owl" of krss format;
2. there is a classification result of direct subsumptions of "test.owl" save in the path "workspace/test/data_preprocess";
3. all sigature are in the dictionary "workspace/test/sig", with name 0,1,2,...;
4. all the signature file consist of two lines: (i)"A B C .... D\n"; (ii)"r1 r2 ... rn\n". Here, A,B, ... are concepts, ri is role.

Then one can obtain the clauses set for each signature in "workspace/test/sig" by running:

``python ForMod.py test``

The result is saved in "workspace/test/query_sig".

Note that here the algorithm only produced the clause set $\mathcal{C}_\Sigma$. To obtain the pseduo-minimal modules, one could use the resolution algorithm which can be found in the following link:
>https://github.com/liveontologies/pinpointing-experiments

To do that, one can 
1. follow the instruction in: https://github.com/liveontologies/pinpointing-experiments/wiki;
2. change the path in line 60-64 the file "SatProofProvider.java" in the link: https://github.com/liveontologies/pinpointing-experiments/tree/master/src/main/java/org/liveontologies/proofs
