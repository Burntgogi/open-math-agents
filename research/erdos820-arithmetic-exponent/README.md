# The arithmetic exponent in Erdős problem 820

For $n\ge1$, let $H(n)$ be the least $b$ for which there is an integer $2\le a<b$ with
$\gcd(a^n-1,b^n-1)=1$. Write $W(n)=\#\{p\text{ prime}:p-1\mid n\}$,
$\tau(n)$ for the divisor count, and $F(n)=\log n/\log\log n$ for $n\ge3$.

[`Erdos820ArithmeticIdentity.lean`](Erdos820ArithmeticIdentity.lean) proves
four results in the namespace `Erdos820Identity`.

- `pointwise_bound` gives
  $\log H(n)\le1280(1+\max_{1\le j\le\tau(n)}W(jn))(1+\log n)^2$
  for every $n\ge3$.
- `arithmetic_identity` proves
  $\limsup_{n\to\infty}\log\log H(n)/F(n)
  =\limsup_{n\to\infty}\log W(n)/F(n)$.
- `common_exponent_iff` identifies the unique real $c$ giving, for every
  $\varepsilon>0$, a frequent lower bound at
  $\exp(n^{(c-\varepsilon)/\log\log n})$ and an eventual upper bound at
  $\exp(n^{(c+\varepsilon)/\log\log n})$.
- `site_iff_positive` proves that the exact Formal Conjectures statement
  `Erdos820.erdos_820.variants.log_log_exponent` is equivalent to strict
  positivity of the shifted-prime limsup.

All four results are unconditional. Positivity itself follows from the
shifted-prime estimates of Steve Fan and Paul Pollack and remains a separate
formalization step. [Fan–Pollack, Theorem 1.1](https://arxiv.org/abs/2510.14167)

## Sources and credits

- Paul Erdős stated the common-exponent question and gave the shifted-prime
  product obstruction. [*Remarks on some problems in number theory* (1974), p. 200](https://users.renyi.hu/~p_erdos/1974-27.pdf#page=4)
- Wouter van Doorn applied the product obstruction on the sharper scale
  using Adleman, Pomerance, and Rumely. [October 2025 discussion](https://www.erdosproblems.com/forum/thread/820#post-1099) · [Adleman–Pomerance–Rumely, Proposition 10](https://math.dartmouth.edu/~carlp/PDF/paper37.pdf#page=29)
- Liam Price contributed the fixed-base sieve. The Lean source independently
  implements that sieve and extends the argument by averaging the smaller
  base for $H$. [*Coprime Power Differences*](https://www.overleaf.com/read/kvjrzdkwkgkx#010e4a) · [Price's proof claim and Lean attachment](https://www.erdosproblems.com/forum/thread/proof-claim:2e58a1390acd4e6b89490b881ad2c77a#post-7756)
  Price's post credits GPT 5.6 Sol Pro for the earlier proof and Claude Fable 5
  for its Lean formalization. [Price's attribution](https://www.erdosproblems.com/forum/thread/proof-claim:2e58a1390acd4e6b89490b881ad2c77a)
- The Formal Conjectures authors supplied the definitions of $H,K$ and the
  official Lean statement. [Pinned statement](https://github.com/google-deepmind/formal-conjectures/blob/9097e2f90e66d2f6244209cb1c07f7120d17ec53/FormalConjectures/ErdosProblems/820.lean)

## Verification

Use Lean `v4.33.1` and a Formal Conjectures checkout at
`9097e2f90e66d2f6244209cb1c07f7120d17ec53`. Its Lake manifest pins Mathlib to
`0df444a360eaa60ab8c11dca51a86af692955474`. From that checkout, prepare the
imports with these commands.

```sh
lake exe cache get
lake --wfail build '@mathlib/+Mathlib:olean' '+FormalConjectures.ErdosProblems.«820»:olean'
```

Then run the verifier with Python 3 and Lake on your path.

```sh
python verify.py /path/to/formal-conjectures
```

The verifier compiles with warnings treated as errors, saves build artifacts
in a temporary directory, and checks that each of the four results uses
exactly `propext`, `Classical.choice`, and `Quot.sound`. It then replays
the module with `leanchecker`.
