# ForMod

This is a prototype implementation of the algorithm ForMod.

## Step 0: preprocessing

To use this code, place the ontology in the `workspace` directory. For example, assume the ontology is stored at `workspace/<workspace_name>/<ontology_name>.owl`. We require that:

1. `<ontology_name>.owl` is in FSS format, and a copy `<ontology_name>.krss.owl` in KRSS format also exists in the same folder;
2. the classification result of direct subsumptions is saved under `workspace/<workspace_name>/data_preprocess/`.

This preprocessing can be done as follows. First, install the mOWL package:

``pip install mowl-borg``

Then run:

``python ont_processing.py <ontology_path> [do_transform]``

where `do_transform = True/False`. If `do_transform == True`, all ABox axioms are translated to TBox axioms as follows (the translation is saved in `ontology_mappings.pkl`):
- `A(a)` to `A_a ⊑ A`
- `r(a,b)` to `A_a ⊑ ∃r. A_b`


## Step 1: generate the Horn clauses

We assume all signatures have been provided as follows:

1. all signatures are in the directory `workspace/<workspace_name>/sig/`, with names `0, 1, 2, ...`;
2. each signature file consists of two lines: (i) `"A B C ... D\n"` (concept names); (ii) `"r1 r2 ... rn\n"` (role names).

Then obtain the clause set for each signature by running:

``python ForMod.py <workspace_name> [ontology_name]``

- `<workspace_name>`: the subdirectory under `workspace/` containing the ontology and signatures (e.g. `test`).
- `[ontology_name]` *(optional)*: the base name of the ontology file without extension (e.g. `ontology`). Defaults to `<workspace_name>` if omitted.

**Examples:**

```bash
# ontology at workspace/test/test.owl, signatures at workspace/test/sig/
python ForMod.py test

# ontology at workspace/myexp/ontology.owl, signatures at workspace/myexp/sig/
python ForMod.py myexp ontology

# with optional flags
python ForMod.py myexp ontology --init --el-plus --quiet
```

**Optional flags:**
- `--init`: re-run initialisation (build the hypergraph from scratch).
- `--el-plus`: enable EL⁺ mode (supports role chains and other EL⁺ constructs).
- `--quiet`: suppress verbose output.

The result is saved in `workspace/<workspace_name>/query_sig/`.

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
