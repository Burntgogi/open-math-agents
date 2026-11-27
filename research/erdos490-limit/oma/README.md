# Checking the Erdős 490 limit proof with Open Math Agents

These seven files prove that the maximum of `|A| |B| log N / N²` converges, where multiplication is injective on `A × B` and both sets lie in `[1,N]`. The proof establishes existence of the limit. Its value remains unknown. The [modular proof and replay instructions](https://github.com/Burntgogi/open-math-agents/blob/8d2e7fbb460e25c1e9b626f0cdd99478fbe82d2b/research/erdos490-limit/REVIEW.md) provide a second way to check the theorem.

| Dependency | Files | Result |
|---|---|---|
| Original site declaration | `R1` | Trimming, transfer and boundedness imply convergence. |
| Registered `R1` | `R1.H1`, `R1.H3`, `R1.H2.R2` | Two proofs and a reduction of transfer to three analytic statements. |
| Registered `R1.H2.R2` | Its `H1`, `H2` and `H3` | Effective prime counting, shift stability and recovery of a common sample. |

The upstream submissions follow the repository's one-file convention. Each leaf uses the name `OMA.solution`, so the checker isolates the leaf modules and type-checks each against its parent's actual proposition. It then checks that the two reductions compose at the exact type of the original question. The file checksums are in `files.json`. The source credits and licenses are in the affected files.

Use Lean 4.33.1, formal-conjectures revision `9097e2f90e66d2f6244209cb1c07f7120d17ec53`, its pinned Mathlib, and the Open Math Agents linter at revision `9b0666fab640c28cc1a97dc3439ea547f4f7a972`. With dependencies already downloaded, build the original target in the formal-conjectures checkout.

```sh
lake build FormalConjectures/ErdosProblems/490.lean:olean
```

From this directory run the following command with the paths to the two checkouts.

```sh
python audit.py /path/to/formal-conjectures /path/to/open-math-agents
```

The script checks the source hashes, runs the repository linter, compiles each submission with warnings as errors, checks its axiom report and runs `leanchecker`. The recorded verification results are in `receipts/`. The registration status of the parent is available on [upstream PR 11241](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/11241).
