# ForMod

This is a protype algorithm of the algorithm ForMod.

## Step 1: generate the Horn clauses
To use this code, put the ontology on dictionary "workspace". For example, assume the ontology is "test.owl".
We require that:

1. "test.owl" is of fss format, and there is a copy "test.krss.owl" of krss format;
2. there is a classification result of direct subsumptions of "test.owl" save in the path "workspace/test/data_preprocess";
3. all sigature are in the dictionary "workspace/test/sig", with name 0,1,2,...;
4. all the signature file consist of two lines: (i)"A B C .... D\n"; (ii)"r1 r2 ... rn\n". Here, A,B, ... are concepts, ri is role.

Then one can obtain the clauses set for each signature in "workspace/test/sig" by running:

``python ForMod.py test``

The result is saved in "workspace/test/query_sig".


Note that here the algorithm only produced the clause set $\mathcal{C}_\Sigma$. To obtain the pseduo-minimal modules, one could use the resolution algorithm in the next step.

## Step 2: resolution over Horn clauses
We use the resolution algorithnm provided by the following link:
>https://github.com/liveontologies/pinpointing-experiments

We build a docker image, use it by following steps:
1. Download the docker image by ``docker pull yh1997/resolution``
2. Check the ID of docker image by ``docker images``
3. Run the image ``docker run -it ID_of_dokcer_image /bin/bash``
4. Go to the path "/pinpointing-experiments" by runing the command
``cd pinpointing-experiments``
5. Put all generated file of Horn clauses into a singular folder, such as "query", assume the name of all the Horn-clause-files are list in a text file, such as "queries". Then, by running the following command, you will get the statistic results of resulting pseudo-modules in the file "record.csv".
``./bin/run_justification_experiments.sh  -t 60000 record.csv queries  org.liveontologies.pinpointing.experiments.SatResolutionJustificationExperiment  -- query THRESHOLD``
