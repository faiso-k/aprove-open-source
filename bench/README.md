# Setup

## Docker mode

Load an existing image with `docker load -i image.tar`, or build from scratch:
```
docker build -t aprove_solver:some_ID .
```

## Local mode

Requires the same external tools used by the handlers (z3, minisat, loat, etc.) to be on `PATH`.

# Run benchmarks

1. Build AProVE: `ant -f build-aprove.xml dist`
2. Run `python3 benchmark.py -c config.toml`. CLI arguments override config values. Run `python3 benchmark.py -h` for full usage.
3. The script will run AProVE on the provided problem set in parallel and write to OUTDIR in the following format.
```
out/
- summary.csv
- results/
   - AProVE_FoSSaCS24/
        - coinflips01.ari.out
        - coinflips02.ari.out
   - AProVE_Special/
      - paper2.ari.out
```
Where `summary.csv` contains the first line (result) of the respective problem.
The serialization logic is abstracted into `serialize_result.py`.

After the run completes (or is interrupted), a result table is printed to stdout:
```
Result        Count
----------   ------
YES             123
NO               45
MAYBE            12
KILLED            3
ERROR             0
```

### Resume & rerun

**Resume** - continue an interrupted run, skipping files that already have a result in `summary.csv`:
```
python3 benchmark.py -c config.toml --resume
```

**Rerun** - re-run only files that previously got a specific result (comma-separated):
```
python3 benchmark.py -c config.toml --rerun MAYBE,KILLED,ERROR
```

Both modes preserve the existing `summary.csv` and update results in place. They are mutually exclusive. If no `summary.csv` exists yet, `--rerun` exits with a warning while `--resume` simply runs everything.

### Flat CSV mode

Pass `-F`/`--flat-csv <path>` to additionally append results to a single flat CSV that accumulates runs across multiple benchmarks:

```
python3 benchmark.py -c config.toml -F /path/to/big_table.csv
```

Columns: `Timestamp;Problem;Result;Timeout;Category;CommitID;Conflict`

The commit ID is read automatically from the `VERSION` file embedded in `aprove.jar`. If a host jar is provided via `-J`/`APROVE_JAR`, it is read locally; otherwise it is extracted from the jar inside the Docker image. Both output modes (`--outdir` and `--flat-csv`) can be used simultaneously.

#### Conflict detection

When the same `(Problem, Category)` pair is run multiple times, the `Conflict` column tracks disagreements between runs:

| Conflict | Meaning | Example |
|---|---|---|
| `NONE` | No conflict, most recent result kept | YES → YES, KILLED → MAYBE |
| `BROKEN` | Any result regressed to ERROR | YES → ERROR, MAYBE → ERROR |
| `BAD` | Definitive results disagree | YES → NO, NO → MAYBE |
| `GOOD` | Inconclusive result later resolved | MAYBE → YES, KILLED → NO, ERROR → YES |

On a conflict both rows are kept and tagged with the conflict type. On no conflict the old row is replaced by the most recent result.

After each run using `--flat-csv`, a conflict summary is printed alongside the result table. `BROKEN` and `BAD` conflicts are listed individually by problem since they indicate regressions that need attention - `BROKEN` meaning a previously conclusive result now errors, `BAD` meaning two definitive results disagree.

Example `config.toml` (Docker mode)
```toml
FOLDER="/path/to/TPDB-ARI"
SUBDIR="PTRS_Standard"
CATEGORY="PTRS_AST"
TIMEOUT="3"
IMAGE="aprove_solver:java25"
OUTDIR="result"
APROVE_JAR="../dist/lib/aprove.jar"
EXTENSION="ari"
FLAT_CSV="/path/to/big_table.csv"
```

Example `config.toml` (local mode)
```toml
FOLDER="/path/to/TPDB-ARI"
SUBDIR="PTRS_Standard"
CATEGORY="PTRS_AST"
TIMEOUT="3"
LOCAL=true
APROVE_JAR="../dist/lib/aprove.jar"
OUTDIR="result"
EXTENSION="ari"
```

Rebuilding the Docker image: `docker build -t aprove_solver:local_test_ID .`

Known Bugs:
