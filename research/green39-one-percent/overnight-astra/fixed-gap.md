# A fixed gap above the volume bound for random cyclic translate covers

Let $p$ run through the primes, let $k=\lfloor\sqrt p\rfloor$, and choose $A$ uniformly from the $k$-subsets of $G=\mathbb Z/p\mathbb Z$. Write $\tau(A)$ for the minimum number of translates covering $G$. Then
$$
 \Pr\!\left(\tau(A)>(1+10^{-26})\,p/k\right)\ \longrightarrow\ 1. \tag{1}
$$
This establishes the fixed-gap subsidiary question. The assertion that *some* constant $C>1$ suffices at this exponent remains open here. The argument does not reach $C=1.01$. The probability and the floors in the [upstream statement](https://github.com/google-deepmind/formal-conjectures/blob/9097e2f90e66d2f6244209cb1c07f7120d17ec53/FormalConjectures/GreensOpenProblems/39.lean) are compatible with (1), since $\sqrt p\le p/k$.

All logarithms are natural. We use counting measure for norms and convolution, and $\widehat f(\xi)=\sum_x f(x)e^{2\pi i\xi x/p}$. A probability measure below has total mass one. Write $\check\mu(x)=\mu(-x)$. For a uniform ordering of $A$, let $A_1,A_2$ be its first $\lfloor k/2\rfloor$ elements and the rest, with sizes $k_1,k_2$. Marginally each is a uniform subset. Given $A_1$, the second is a uniform sample without replacement from its complement.

## 1. Private labels and the two different center samples

Set
$$
 c=10^{-26},\qquad b=10^{-24},\qquad \alpha=10^{-5},\qquad r=\lfloor\alpha k\rfloor.
$$
Suppose $A+T=G$ and $|T|k\le(1+c)p$. Call a center good if at most $bk$ of its labels $a\in A$ give a point $a+t$ also covered by another center. A point with multiplicity $m\ge2$ contributes $m\le2(m-1)$ nonprivate incidences. Thus there are at most $2cp/(bk)$ centers that are not good. For all sufficiently large $p$ we have at least $0.97k$ good centers and at most $2k$ centers altogether. This uses no multiplicity cap.

For **any** $r$ good centers $R$ put $U=A_1+R$. For any $s$ good centers $S$, write $Y(z)=|(z+S)\cap U|$. Then
$$
 |U|\ge(k_1-bk)r,\qquad \sum_{z\in A_2} Y(z)\le bks. \tag{2}
$$
The private labels give distinct points in the first inequality. In the second, an incidence counted at $(z,t)\in A_2\times S$ has another representation from $A_1\times R$, necessarily with a different center. The two center samples may overlap. The ability to keep $r$ fixed while $s$ is much smaller is important.

## 2. A family of smooth probability measures

Let $K=10^{24}$. The following estimates hold simultaneously with probability $1-o(1)$ for any **deterministic** family of at most $\exp(k^{1/5})$ probability measures $\mu$ with $\|\mu\|_\infty\le2/(Kk)$. Put $\varepsilon=10^{-8}$ and $g=\mathbf1_{A_1}*\check\mu$. The estimates we use are
$$
 \|\mathbf1_{A_2}*\mu-k_2/p\|_1\le\varepsilon k,\qquad
 \sum_{z\in A_2}\big(g(z-v)-2/k\big)_+\le 0.01\quad(v\in G). \tag{3}
$$
Here and below a constant subtracted from a function denotes the constant function on $G$.

For either half and either orientation of the kernel, a single convolution coordinate has variance at most $(k_j/p)\sum_x\mu(x)^2$ by sampling without replacement (equivalently by nonpositive covariance between inclusion indicators and nonnegative weights). Cauchy–Schwarz gives expected $\ell^1$ deviation at most $\sqrt{p k_j\sum_x\mu(x)^2}\le(2/\sqrt K)k$ for large $p$. A sample exchange changes the norm by at most 2. The exposure martingale, coupling the two conditional completions by transposing the differing choices, gives failure probability $\exp[-\Omega(\varepsilon^2 k)]$ for the claimed $\ell^1$ bound. Use this for both $\mathbf1_{A_2}*\mu$ and $g$.

Also, with probability $1-o(1)$, simultaneously $\sup_z g(z)\le k^{-2/3}$. For a list $0\le w_i\le m$ of length $N$, the moment generating function for a uniform $n$-subset satisfies
$$
 \mathbb E\exp\!\left(\sum_{\rm sample}w_i/m\right)
 \le\left(N^{-1}\sum_i e^{w_i/m}\right)^n
 \le\exp\!\left((e-1)n\,\sum_i w_i/(Nm)\right). \tag{4}
$$
The first inequality is the elementary symmetric mean inequality, and the second follows from convexity on $[0,1]$. With $m=2/(Kk)$, a fixed coordinate exceeds $k^{-2/3}$ with probability at most $\exp[O(K)-(K/2)k^{1/3}]$, sufficient for all measures and coordinates.

Condition on $A_1$ satisfying its bounds. Since $k_1/p\le2/k$, the positive excess of $g$ above $2/k$ has total mass at most $\varepsilon k$. In a sample $A_2$ its expected sum, after any translation, is at most $2\varepsilon$. Use (4) with $m=k^{-2/3}$ on the remaining population. The probability that the sampled excess exceeds $0.01$ is at most $\exp[-(0.01-2(e-1)\varepsilon)k^{2/3}]$. The union over measures and shifts proves (3). The first estimate of (3), which uses $A_2$, is an unconditional typical event. We do not condition the later probability estimates on it.

## 3. How the deterministic families are constructed

Use levels $x_0=\log(p/k)$ and $x_{i+1}=x_i/2$ until the first $x_i\le5000$. At an active level $x=x_i>5000$ set
$$
 \eta=e^{-1000-x/20},\qquad \xi=x^{-2}.
$$
For any set $V$ of at most $2k$ points we can do one of the following:

* Find $F\subset V$ with $|F|\ge\xi k$ and a measure $\mu$ of the kind in Section 2 with $\max_\omega|\widehat{\mathbf1_F}(\omega)/|F|-\widehat\mu(\omega)|\le5\eta$.
* Put all but fewer than $\xi k$ elements of $V$ into a set $P'$ of size at most $k e^{x/2}$.

Here both the measures and the containers come from deterministic, enumerable families, independent of $A$. The cardinality bounds below are essential. The assertion when $|V|<\xi k$ holds with an empty container.

Start with the remaining target $F=V$. While $|F|\ge\xi k$, use target law $\nu=\mathbf1_F/|F|$ and start a fit with the **uniform law on all of $G$**. For the current law $m$ form $H=\{u:m(u)>1/(Kk)\}$. If $m(H)>\eta$ and $\nu(H)\ge\eta/2$, record $H$, remove it from $F$, and restart with the uniform law. If $m(H)>\eta$ and $\nu(H)<\eta/2$, choose the test $f=-\mathbf1_H$. Otherwise if a signed real or imaginary part of a character has $\mathbb E_\nu f-\mathbb E_m f>\eta/2$, choose such a test. When neither a removal nor a test applies, $m(H)\le\eta$ and both real and imaginary differences have absolute value at most $\eta/2$ at every frequency. Delete the mass on $H$ and normalize what remains to obtain $\mu$. This changes the law by at most $2\eta$ in $\ell^1$, giving the stated Fourier error and the cap $2/(Kk)$.

For a test update $m$ by multiplying by $\exp((\eta/4)f)$ and normalizing. Every chosen test has expectation gap at least $\eta/2$. Since $|f|\le1$, Hoeffding's elementary exponential moment bound shows that the relative entropy of $\nu$ with respect to $m$ decreases by at least $(\eta/4)(\eta/2)-(\eta/4)^2/2>\eta^2/16$. Its initial value is at most $\log p$ and it stays nonnegative. Hence there are at most $1+16\eta^{-2}\log p$ updates in one fit. A removal discards at least an $\eta/2$ fraction of the current target. At most $2+\lceil 2\eta^{-1}\log(2/\xi)\rceil$ removals suffice. Their union has size at most that number times $Kk$; this is below $ke^{x/2}$ for $x>5000$. For example its logarithmic ratio to $k$ is at most $\log K+1000+x/20+\log(5+2\log(2x^2))<x/2$.

At each update there are at most $4p+1$ instructions: a signed real/imaginary character or the negative indicator of the heavy set computed from the preceding law. A stop can be specified by its depth. Thus the logarithm of the number of possible fitted measures or individual recorded sets is $O(\eta^{-2}\log^2 p)$. The logarithm of the number of their possible unions is $O((1+\eta^{-1}\log(2/\xi))\eta^{-2}\log^2 p)$. Across all levels $\eta^{-1}\le e^{1000}(p/k)^{1/20}$, so even the union families have log cardinality $k^{3/20+o(1)}<k^{1/5}$. One fit never needs the previous container for its starting law. This is why descriptions from earlier levels do not inflate the family of fitted laws. These finite lists are for counting only.

## 4. Excluding the fitted piece of a family of good centers

With probability $1-o(1)$ the following holds at all active levels. If $V$ consists of good centers in a container $P$ of size at most $ke^x$ from the preceding level (initially $P=G$), and $|V|\ge0.9k$, the first outcome of Section 3 is impossible.

Suppose a fitted piece $F$ exists. Choose any $r$ points $R$ of $V$ and put $s=\min(r,|F|)$. There is an $s$-subset $S$ of $F$ with
$$
 \max_\omega|\widehat{\mathbf1_S}(\omega)-s\widehat\mu(\omega)|\le 7\eta s. \tag{5}
$$
For $s=|F|$ this is immediate. Otherwise sample without replacement. Fourier real and imaginary parts have bounded exchange differences, and $s\eta^2\gg\log p$ uniformly here ($s=r$ in the sampling case). Hoeffding and a union bound give a sample with normalized Fourier error from $\nu$ at most $2\eta$. This is an existence claim inside each $F$.

For fixed $P,R,S,\mu$, expose $A_1$ and set $U=A_1+R$. Define
$$
 Y_0(z)=s\sum_{u\in U}\mu(u-z),\qquad Y(z)=|(z+S)\cap U|.
$$
On (3), if (2) holds then, for all sufficiently large $p$,
$$
 \sum_{z\in A_2}Y_0(z)\ge s(k_2|U|/p-\varepsilon k)\ge0.22rs.
$$
For every $E\subset A_2$ we also have
$$
 \sum_{z\in E}Y_0(z)
 \le s\sum_{v\in R}\sum_{z\in E}g(z-v)
 \le 2rs|E|/k+0.01rs. \tag{6}
$$
This is an upper bound by all representations from $A_1\times R$. Set $E=\{z\in A_2:|Y(z)-Y_0(z)|>rs/(100k)\}$. Off $E$ the total error is at most $0.01rs$, and $\sum_{A_2}Y\le bks\le0.01rs$. Applying (6) on $E$ shows $|E|\ge k/20$. In particular, localized baselines with large pointwise peaks are allowed.

For the probability bound, conditional **only on $A_1$**, Parseval and (5) give $\mathbb E_{z\in G}|Y(z)-Y_0(z)|^2\le(7\eta s)^2|U|/p$. The fraction of all positions above the error threshold is at most $(1400\eta/\alpha)^2$, using $r\ge\alpha k/2$. At each draw of $A_2$ the conditional probability of hitting those positions is at most $2(1400\eta/\alpha)^2$. A union over sample indices bounds the probability of at least $k/20$ hits by
$$
 2^k [\,2(1400\eta/\alpha)^2\,]^{k/20}.
$$
Intersecting with the typical event (3) costs no factor. The number of $R,S$ within $P$ is at most $(r+1)(e|P|/r)^{2r}$ when $|P|\ge2r$, as here. The log cost of choices of $P$ and $\mu$ together is $o(k)$. After division by $k$, the total log bound is at most
$$
 o(1)+2\alpha\log(2e\,e^x/\alpha)+\log2+
 \tfrac1{20}\log(2(1400/\alpha)^2)-100-\tfrac{x}{200}.
$$
This is less than $-1$ for all active $x$, since $2\alpha<1/200$. The $O(\log\log p)$ levels also cost $o(k)$ in the logarithm. This proves the exclusion.

## 5. The terminal container

Apply Sections 3–4 to the good centers. At each active level retain those in the new container. The total discarded fraction of $k$ is at most $\sum_{x_i>5000}x_i^{-2}<4/(3\cdot5000^2)$, by the geometric progression. Inductively there are always at least $0.9k$ centers left. At termination they lie in one of $\exp(o(k))$ deterministic candidate containers of size at most $k e^{5000}$. The statement about the discarded fraction refers to all levels combined, including the last active one.

We detail the last test because the centers inside a terminal container can still be freely chosen. Take $\sigma=10^{-13}$, $s=\lfloor\sigma k\rfloor$, $h=10^{-7}$, $d=h/128$. A uniform $s$-subset $S$ of the retained centers satisfies, with probability $1-o(1)$,
$$
 \max_{v\ne0}r_S(v)\le2s^2/k,\qquad r_S(v)=|S\cap(S+v)|.
$$
Indeed its expectation for each $v\ne0$ is at most $s(s-1)/(|V|-1)\le1.2s^2/k$ for large $p$. Exchange differences are at most 2, so the tail exponent is $\Omega(s^3/k^2)\gg\log p$. Fix such an $S$. Its loss $D(A,S)=ks-|A+S|$ is at most $bks<ds^2$ for large $p$, because every center has at most $bk$ nonprivate labels in the original cover.

For clarity, the uniform bound needed for this test is proved in [Sections 2–3 of the companion proof](report.ko.md). On an event of probability $1-o(1)$ depending **only on $A_1$**, every $S$ with the displayed difference bound satisfies
$$
 \sum_z |(z+S)\cap(A_1+S)|^2\le10^5s^4.
$$
The proof there uses only $s\to\infty$, $s^2\ge k$, and the displayed difference bound. It first controls the average of $r_{A_1}(u-v)$ on all sufficiently large sets of offsets, then applies that bound to the weights $r_S$ after splitting off $v=0$. Here $s$ meets both size requirements. If $D(A,S)\le ds^2$, then $|A_1+S|\ge k_1s-ds^2\ge ks/3$. For fixed $S$ and exposed $A_1$ with this size and second moment, at least an $h$-fraction of positions $z$ have overlap at least $s^2/(8k)$, by Cauchy–Schwarz and the mean $s|A_1+S|/p$. During exposure of $A_2$ their conditional probability is at least $h/2$. Except with probability $\exp(-hk/32)$, at least $hk/8$ are sampled, forcing $D(A,S)\ge hs^2/64>ds^2$. If $|A_1+S|$ was smaller than $k_1s-ds^2$, the claimed small loss was already impossible.

In a terminal container the log cost of all such samples is at most
$$
 s\log(e\,ke^{5000}/s)
 \le(\sigma(5001+\log(1/\sigma))+o(1))k<hk/32.
$$
The family of containers adds $o(k)$ to the log cost. Therefore, with probability $1-o(1)$, none allows the required small-loss sample. This contradicts the proposed cover and proves (1).

## Appendix. The uniform second moment used at termination

Here is a proof of the companion estimate in the notation of this paper. Write $\ell=\lceil\log^2 p\rceil$, $b_0=\lceil100\ell^4\rceil$. With probability $1-o(1)$,
$$
 \sum_{\{u,v\}\subset B} r_{A_1}(u-v)\le1000|B|^2
 \qquad\text{for every } B\subset G,\ |B|\ge b_0. \tag{7}
$$
For fixed $\ell$-set $L$ form the graph on $G$ with nonzero edge differences in $L-L$. Its degree is at most $\ell^2$. Independently keep vertices at rate $q=2k/p$. A matching of size $m=20\ell^2$ in the retained graph has probability at most $(ep\ell^2 q^2/(2m))^m\le(e/10)^m$ of existing. If at least $20\ell$ retained vertices lie in components of order at least three, one can select disjoint connected sets, each of size at least three, with total order $v\in[20\ell,20\ell+2]$. Take components up to the cutoff and truncate the last by a connected ordering, using at least three vertices from it. A composition of $v$, a root for each set, and a tree traversal with at most $2v$ steps encode these sets. Thus the probability for fixed $v$ is at most $2^v p^{v/3}\ell^{4v} q^v=p^{(-1/6+o(1))v}$. The factor $q^v$ applies to encodings of disjoint sets with $v$ distinct vertices. Union over at most $p^\ell$ choices of $L$ costs $o(1)$ in failure probability for both estimates. The larger components then contribute at most $200\ell^2$ edges and the two-vertex components are a matching. The resulting bound of $220\ell^2$ edges transfers to $A_1$ by monotone coupling: the independent sample has at least $k_1$ elements with probability $1-o(1)$.

Sample an $\ell$-subset $L$ uniformly from $B$. Even conditional on including a particular pair of $B$, its unordered-pair differences are distinct up to sign with probability at least $1/2$. Indeed an equality between different pair differences, after cancelling, either contradicts distinctness or gives a nontrivial linear relation on three or four slots with coefficients in $\{\pm1,\pm2\}$. Given the two fixed slots, one of the remaining variables is forced. The union bound is at most $2\ell^4/(|B|-\ell)$. On the distinct-difference event the induced edge count equals the sum on the left of (7) restricted to $L$. Averaging only on that event proves (7), because every pair contributes with probability at least $\binom{\ell}{2}/(2\binom{|B|}{2})$.

For a terminal seed with $r_S(v)\le2s^2/k$ off zero, write $r_S=s\mathbf1_{\{0\}}+w$, where $W=\sum w=s(s-1)$. For $n=\lfloor k/4\rfloor$, the distribution $w/W$ has all coordinates at most $1/n$. Hence it is a mixture of uniform $n$-set distributions: the extreme points of this capped simplex have no two strictly interior coordinates and the sum condition rules out exactly one. For two such $n$-sets, apply (7) to their union to bound the off-diagonal ordered cross sum by $8000n^2$. Consequently the off-diagonal part of $\|\mathbf1_{A_1}*w\|_2^2$ is at most $8000 W^2$; its diagonal is at most $k W\max w\le2s^4$. The zero-difference term has squared norm $s^2k_1\le s^4$. Since $|(z+S)\cap(A_1+S)|\le(\mathbf1_{A_1}*r_S)(z)$, the elementary square-sum inequality gives the asserted $10^5s^4$ bound. This proves the terminal estimate without any assumption on the Fourier coefficients of the center set.

## Scope and verification

The proof treats all adaptive choices of centers, including those forming large hubs. It uses the small total number of nonprivate incidences of a near-volume cover. For a general fixed $C$ this count can be of order $p$ with a large constant, and the good-center conclusion in Section 1 is unavailable. Thus (1) does not decide the full Green variant.

The [finite checks](verify.py) reproduce the upstream proportions $3/5,1/3,1/6$. They check 54,450 pairs for the weighted difference identities, 66,150 asymmetric configurations for the incidence, clipped baseline and residual Fourier estimates, and a finite fitting loop with 13,415 updates, 630 removals and 330 fitted outcomes. The code also checks the Singer control and the numerical margins. The combinatorial and probabilistic limit argument above is a written proof. It has not been verified in Lean or independently refereed.

The problem is due to Ben Green, with the normalization of the exponent variant due to the Formal Conjectures authors. Prior local work identified the rare-interval first-moment obstruction and the Singer and stratified controls. The fitting step uses the standard multiplicative-weights relative-entropy argument, and (4) is Maclaurin's symmetric mean inequality. The split between fitted and localized centers and its use with (2) are derived here. No literature priority is asserted. Earlier independent review · [Green, Problem 39](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.39) · [Bollobás–Janson–Riordan](https://arxiv.org/abs/0910.3815)
