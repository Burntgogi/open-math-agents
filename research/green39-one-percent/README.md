# The one-percent budget for random cyclic translate covers

Let $p$ run through primes, set $k=\lfloor\sqrt p\rfloor$, and choose a uniform $k$-element subset $A$ of the cyclic group of order $p$. With probability tending to one, every set of centers $T$ whose translates of $A$ cover the group satisfies

$$
|T| > 1.01\,p/k.
$$

In particular, the proportion of sets coverable with the budget in Green 39's one-percent variant tends to zero. The question allowing an unspecified constant remains open. [Pinned problem statement](https://github.com/google-deepmind/formal-conjectures/blob/9097e2f90e66d2f6244209cb1c07f7120d17ec53/FormalConjectures/GreensOpenProblems/39.lean)

The [proof](overnight-astra/review/one-percent.md) uses the fitting procedure in the [companion manuscript](overnight-astra/fixed-gap.md). The [independent mathematical review](one-percent-verification/Review.md) checks the conditioning, uniform probability estimates and costs of all adaptive choices. This is a written disproof reviewed in a separate Codex run. Lean verifies concentration for sampling without replacement, the canonical split, Fourier sparsification, transcript counts, the concrete catalog of possible center sets, and the limiting estimates for individual exceptional events. The final composition of these events is being checked.

The problem originates with Ben Green. The formal variant, the discrete budget and the definition of the coverable proportion come from the Formal Conjectures project. The research and independent checks were performed in the Burntgogi workspace with OpenAI Codex. [Green's problem list](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf) · [Bollobás, Janson and Riordan](https://arxiv.org/abs/0910.3815)

### Reproduction

These finite checks use the Python standard library.

```sh
python overnight-astra/verify.py
python overnight-astra/review/check_review.py
python one-percent-verification/check.py
```

To rebuild the Lean modules in dependency order, use Lean 4.33.1 and a checkout of Formal Conjectures at the revision above. Build the Mathlib and Green 39 statement modules, then run the verifier from this directory.

```sh
python replay.py /path/to/formal-conjectures
```

The verifier checks each source against [sha256.json](sha256.json), compiles with warnings as errors, and replays the resulting modules in the kernel. [Concrete catalog bounds](one-percent-formal/catalog/CatalogRates.lean) · [Probability estimate for a catalog law](one-percent-formal/smooth-law/CatalogEndpoint.lean) · [Terminal estimate](one-percent-formal/terminal/TerminalLimit.lean)
