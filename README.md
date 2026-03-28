# ForMod

This is a prototype implementation of the algorithm ForMod.

## Prerequisites: ontology data

To use this code, put the ontology in the directory `workspace`. For example, assume the ontology is `test.owl`. We require that:

1. `test.owl` is of FSS format, and there is a copy `test.krss.owl` of KRSS format;
2. there is a classification result of direct subsumptions of `test.owl` saved in the path `workspace/test/data_preprocess`.

## Step 1: generate the Horn clauses

We assume all signatures have been provided as follows:

1. all signatures are in the directory `workspace/<name>/sig/`, with names `0, 1, 2, ...`;
2. each signature file consists of two lines: (i) `"A B C ... D\n"` (concept names); (ii) `"r1 r2 ... rn\n"` (role names).

Then obtain the clause set for each signature by running:

``python ForMod.py <name> [--init] [--el-plus]``

where `<name>` is the subdirectory under `workspace/` (also used as the ontology base name).

> **Note:** `--init` is **required on the first run**. It builds the hypergraph representation from the ontology. On subsequent runs it can be omitted to reuse the cached hypergraph.

**Optional flags:**
- `--init`: build (or rebuild) the hypergraph from scratch.
- `--el-plus`: enable EL⁺ mode (supports role chains and other EL⁺ constructs).

**Examples:**

```bash
# First run — --init is required
python ForMod.py test --init

# Subsequent runs
python ForMod.py test

# EL+ ontology, first run
python ForMod.py test --init --el-plus
```

The result is saved in `workspace/<name>/query_sig/`.

Note: the algorithm produces the clause set $\mathcal{C}_\Sigma$. To obtain pseudo-minimal modules, use the resolution algorithm in the next step.

## Step 2: resolution over Horn clauses

We use the resolution algorithm provided at:
> https://github.com/liveontologies/pinpointing-experiments

For convenience, a Docker image of the resolution algorithm is also available:

1. Download the image: ``docker pull yh1997/resolution``
2. Check the image ID: ``docker images``
3. Run the container: ``docker run -it <image_id> /bin/bash``
4. Navigate to the working directory: ``cd pinpointing-experiments``
5. Place all generated Horn-clause files in a single folder (e.g. `query`), list their names in a text file (e.g. `queries`), then run:

``./bin/run_justification_experiments.sh -t 60000 record.csv queries org.liveontologies.pinpointing.experiments.SatResolutionJustificationExperiment -- query THRESHOLD``

The statistical results of the resulting pseudo-modules are saved in `record.csv`.
