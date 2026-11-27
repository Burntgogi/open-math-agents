# A one-percent gap for random cyclic translate covers

Let \(p\) tend to infinity through the primes, \(G=\mathbb Z/p\mathbb Z\), \(k=\lfloor\sqrt p\rfloor\), and \(A\) be a uniformly random \(k\)-subset of \(G\). The following is a proposed strengthening of the fixed-gap manuscript, with a proof.

**Theorem.** With probability tending to one, every \(T\subset G\) with \(A+T=G\) satisfies
\[
 |T|>1.01p/k.
\]
In particular the coverable proportion with at most \(\lfloor1.01 k\rfloor\) translates tends to zero. This answers the 1.01 variant in the negative if the proof stands. The cases of 100 and of an unspecified larger constant remain open in this review.

## 1. How many translates are needed outside a small prescribed set?

**Lemma.** Fix \(M<\infty\). For each \(p\), let \(\mathcal P\) be a deterministic list of subsets of \(G\), each of size at most \(Mk\), with \(\log(1+|\mathcal P|)=O_M((\log p)^D)\) for a fixed \(D\). For every fixed \(\zeta>0\), with probability tending to one, simultaneously for every \(P\in\mathcal P\) and every cover \(A+T=G\),
\[
 |T\setminus P|\ \ge (1-\zeta)p/k. \tag{1}
\]
The constant \(M\) can be arbitrarily large and must be fixed before the limit.

**Proof.** Fix \(P\). Put \(m=|P|\), \(H=G\setminus(A+P)\), and
\[
 \rho=\binom{p-m}{k}/\binom pk.
\]
Then \(\mathbb E|H|=p\rho\). Uniformly in the permitted \(m\), \(\rho\) is bounded below by a positive constant depending on \(M\). For example, use the \(k\) factors \(1-m/(p-j)\), \(0\le j<k\), and \(\log(1-u)\ge-2u\) for \(u\le1/2\). One exchange in \(A\) changes the cardinality of \(H\) by at most \(m\) in either direction. For any fixed \(0<\delta<1\), the exchange bounded-differences inequality therefore gives
\[
 |H|\ge(1-\delta)p\rho
\]
except with probability \(\exp(-\Omega_{M,\delta}(k))\) (the case \(m=0\) is deterministic). Here and below that inequality follows by exposing a random ordered sample and coupling two completions by a transposition. For an exchange-Lipschitz function with constant \(L'\), the tail at deviation \(u\) is at most \(2\exp[-u^2/(2kL'^2)]\).

Write \(X_t(A)=|(A+t)\cap H|\). For \(t\in P\) this is zero. For \(t\notin P\), a proposed element \(a\in A\) can contribute only if \(A\) avoids the \(m\) distinct points \(a+t-P\), all different from \(a\). Thus
\[
 \mathbb E X_t
 = k\frac{\binom{p-1-m}{k-1}}{\binom{p-1}{k-1}}
 = k\rho\,\frac{p}{p-m}. \tag{2}
\]
We need concentration of this random variable even though \(H\) uses the same sample.

Set \(L=\lceil k^{1/10}\rceil\) and call a sample \(B\) regular if \(\max_v |B\cap(v+P)|\le L\). For a fixed translate the probability of at least \(L\) hits is at most \(\binom mL (k/p)^L\), by specifying \(L\) points. Thus the failure probability for regularity is at most \(p(eMk^2/(pL))^L\), at most \(\exp[-\Omega(k^{1/10}\log k)]\) eventually for fixed \(M\). The orientation is \(+P\).

For **any two** regular samples \(B,B'\), put \(d=|B\setminus B'|\). Of the contributions to \(X_t(B)\) that disappear in \(X_t(B')\), at most \(d\) correspond to removed elements of \(B\). Each remaining lost point is in \(B+t\) and in \(v+P\) for some \(v\in B'\setminus B\). There are at most \(L\) such points per \(v\), by regularity of \(B\) at \(v-t+P\). Reverse \(B,B'\) to obtain
\[
 |X_t(B)-X_t(B')|\le(1+L)d .
\]
On the whole slice use the extension \(\min_{B\ {\rm regular}}[X_t(B)+(1+L)|A\setminus B|]\), clipped to \([0,k]\). The regular domain is nonempty for large \(p\). The triangle inequality gives the global Lipschitz bound and equality on the regular domain. Its expectation differs from (2) by at most \(k\Pr(A\ {\rm irregular})\). Since \(m/p=o(1)\) uniformly and \(\rho\) has a positive uniform lower bound, exchange concentration at deviation \(\delta k\rho/2\) shows that
\[
 X_t(A)\le(1+\delta)k\rho\qquad(t\in G)
\]
outside a failure event of size at most \(\Pr(A\ {\rm irregular})+2p\exp[-\Omega_{M,\delta}(k^{4/5})]\). We pay for irregularity once for this \(P\). The union over the stated list of \(P\)'s preserves probability \(1-o(1)\).

Every point of \(H\) must be covered by a translate centered outside \(P\). Consequently \(|H|\le\sum_{t\in T\setminus P}X_t\), so \(|T\setminus P|\ge[(1-\delta)/(1+\delta)]p/k\). Choose \(\delta\) small enough for (1). This last implication is deterministic and simultaneous for all \(T\). \(\square\)

## 2. A canonical cover and a balanced exposure of its private labels

On the event that a cover of size at most \(1.01p/k\) exists, select the lexicographically first one using \(A\) alone. Then order \(A\) uniformly, and split into \(A_1,A_2\) of sizes \(k_1=\lfloor k/2\rfloor,\ k_2=k-k_1\). Call \(a\in A\) nonprivate at \(t\in T\) if \(a+t\) is covered by another center. The total number of nonprivate incidences is at most \(2(k|T|-p)\le0.02p\). Take \(b=0.0225\). At least
\[
 |T|-\frac{0.02p}{bk}\ \ge\ \frac{p}{9k}\ \ge\ k/9
\]
centers have at most \(bk\) nonprivate labels. Call these centers good. Conditional on \(A\), each good center has at most \(0.0114k\) nonprivate labels in **each half**, except with probability \(\exp(-\Omega(k))\) for that center. Indeed the hypergeometric means are at most \(0.01125k+O(1)\) and the deviation is linear. Union over at most \(p\) centers. This conditional statement concerns only the selected cover. Its failure jointly with cover existence has unconditional probability \(o(1)\).

Write \(B=0.0114\), \(r=\lfloor0.1k\rfloor\), \(s_*=\lfloor0.001k\rfloor\). For any \(r\) good centers \(R\) and any \(s\) good centers \(S\), on the balanced exposure event we have, for \(U=A_1+R,\ Y(z)=|(z+S)\cap U|\),
\[
 |U|\ge(k_1-Bk)r,\qquad \sum_{z\in A_2}Y(z)\le Bks. \tag{3}
\]
This uses distinct private points for the first bound. In the second bound the other label lies in \(A_1\) and therefore the other center differs. In particular \(R,S\) may overlap.

## 3. Fitting and the cost of its descriptions

Set \(K=10^{24}\) and \(\varepsilon=10^{-8}\). Use levels \(x_0=\log(p/k),\ x_{i+1}=x_i/2\), active for \(x_i>5000\). At an active level put
\[
 \eta=e^{-1000-0.22x},\qquad \xi=x^{-2}.
\]
For a target \(V\) of at most \(2k\) centers the following deterministic alternatives are supplied by the fitting procedure in §3 of the fixed-gap manuscript:

1. Some \(F\subset V,\ |F|\ge\xi k\), has normalized Fourier transform within \(5\eta\) in sup norm of the transform of a probability \(\mu\) capped by \(2/(Kk)\).
2. All but fewer than \(\xi k\) target points lie in one candidate \(P'\) of size \(\le ke^{x/2}\).

Here are the construction and the dependence on the changed exponent. With remaining target law \(\nu\) uniform on its points, initialize \(m\) uniform on \(G\). Put \(J=\{m>1/(Kk)\}\). If \(m(J)>\eta\) and \(\nu(J)\ge\eta/2\), record \(J\), delete its points from the target and restart. If \(m(J)>\eta\) and \(\nu(J)<\eta/2\), use \(f=-1_J\). Otherwise test signed real and imaginary characters. A discrepancy \(>\eta/2\) supplies \(f\); absent one, delete \(J\) from \(m\) and renormalize. In the latter case the cap is satisfied and the Fourier error is at most \(2\eta+\sqrt2\eta/2<5\eta\). Each update \(m\propto m_{\rm old}\exp((\eta/4) f)\) decreases relative entropy \(D(\nu\Vert m)\) by \(>\eta^2/16\), by the bounded exponential moment for \(f\in[-1,1]\). A run uses \(O(\eta^{-2}\log p)\) instructions, each one of \(4p+1\) choices. At most \(2+\lceil 2\eta^{-1}\log(2/\xi)\rceil\) removals can occur. Their union has size at most this number times \(Kk\). The required shrinkage follows from
\[
 \log K+1000+0.22x+\log(5+2\log(2x^2))<x/2 \qquad(x\ge5000).
\]
For instance the slack exceeds 300 at 5000 and increases thereon, by differentiation.

Consequently the combined lists of measures have log size \(O(\max_x\eta^{-2}\log^2 p+\log\log p)=k^{0.44+o(1)}\) as an upper bound. The lists of candidate containers have log size at most \(k^{0.66+o(1)}\), by encoding the ordered sequence of recorded sets. Empty unions are allowed. **For the last active level**, \(5000<x\le10000\), both \(\eta^{-1}\) and the number of removals are bounded by absolute constants. Its output container list therefore has log size \(O((\log p)^2)\). Crucially, each fit starts uniform on \(G\); its record can be decoded without knowing the input target or the input container. The last output is the union from that level alone. Earlier containers need not be enumerated in the test (1).

## 4. Simultaneous estimates for the smooth measures

For all fitted measures on the lists and all \(v\), with probability \(1-o(1)\),
\[
 \|1_{A_2}*\mu-k_2/p\|_1\le\varepsilon k,\qquad
 \sum_{z\in A_2}\big(g(z-v)-0.51/k\big)_+\le0.001,\quad
 g=1_{A_1}*\check\mu . \tag{4}
\]
Norms use counting measure. For either half, sampling without replacement gives coordinate variance at most \((k_j/p)\sum\mu^2\) by nonpositive pair covariance. The expected \(\ell^1\) deviation is at most \(\sqrt{pk_j\sum\mu^2}\le2k/\sqrt K\). Exchanges cost at most two in this norm. The probability of deviation above \(\varepsilon k\) is \(\exp(-\Omega(\varepsilon^2 k))\) for each law. Apply to \(g\) and to \(1_{A_2}*\mu\).

For nonnegative population weights \(\le m_0\), a sample sum \(Z\) on the uniform slice satisfies \(\mathbb E e^{Z/m_0}\le \exp[(e-1)\mathbb E Z/m_0]\). This is the elementary symmetric mean inequality followed by the chord bound on \(e^u,\ 0\le u\le1\). For a fixed coordinate of \(g\), use \(m_0=2/(Kk)\) and \(\mathbb Eg=k_1/p\). The probability that it exceeds \(k^{-1/2}\) is at most \(\exp[O(K)-(K/2)k^{1/2}]\). This pays for all \(p\) positions and the \(k^{0.44+o(1)}\) log size of the measure list.

Now condition on \(A_1\) satisfying its two bounds. The excess above \(0.51/k\ge k_1/p\) has total mass at most \(\varepsilon k\). The expectation of its translated sum on \(A_2\) is at most \(k_2\varepsilon k/(p-k_1)\le2\varepsilon\). The same moment inequality with \(m_0=k^{-1/2}\) gives failure at threshold \(0.001\) at most \(\exp[-(0.001-2(e-1)\varepsilon)k^{1/2}]\). Again this pays for all shifts and measures. The first bound in (4) is marginal in \(A_2\); we use the intersection of the resulting typical events and do not condition the next estimate on any information about \(A_2\).

## 5. Excluding a fitted piece

Initially \(P=G\). At an active level use the previous output \(P\), with \(|P|\le ke^x\). Suppose it contains a set \(V\) of at least \(0.11k\) good centers from our selected cover and that the first alternative in §3 holds for \(V\). Choose any \(R\subset V\) of size \(r\); set \(s=\min(s_*,|F|)\). Some \(s\)-subset \(S\subset F\) satisfies
\[
 \|\widehat{1_S}-s\widehat\mu\|_\infty\le7\eta s. \tag{5}
\]
If \(s=|F|\), take \(F\); otherwise the normalized mean of a uniform \(s_*\)-sample approximates each real and imaginary character mean by \(\eta\) simultaneously with positive probability. The bounded exchange tail and \(s_*\eta^2\ge k^{0.56-o(1)}\gg\log p\) suffice. This is deterministic existence for each qualifying \(F\).

Fix \(P,R,S,\mu\) satisfying (5). Put \(Y_0(z)=s\sum_{u\in U}\mu(u-z)\). By (3), (4) and \(p/k^2\to1\), for all sufficiently large \(p\),
\[
 \sum_{z\in A_2}Y_0(z)\ge s(k_2|U|/p-\varepsilon k)\ge0.244rs,\qquad
 \sum_{z\in A_2}Y(z)\le0.115rs .
\]
Indeed the limiting lower coefficient is at least \((0.5-0.0114)/2-\varepsilon/0.1=0.2442999\), and the upper coefficient tends to \(0.114\). For any \(E\subset A_2\), counting all representations in \(A_1+R\) in place of just one yields
\[
 \sum_{z\in E}Y_0(z)\le s\sum_{v\in R}\sum_{z\in E}g(z-v)
 \le rs(0.51|E|/k+0.001).
\]
Take \(E=\{z\in A_2:|Y-Y_0|>0.001rs/k\}\). Off \(E\) the total discrepancy is at most \(0.001rs\). Thus \(|E|/k\ge(0.244-0.115-0.001-0.001)/0.51>0.24\).

For fixed choices and conditional only on \(A_1\), positions in \(G\) where the discrepancy exceeds that threshold are now fixed. Parseval gives
\[
 p^{-1}\sum_z|Y-Y_0|^2\le(7\eta s)^2 |U|/p .
\]
Using \(|U|\le p,\ r/k\ge0.099\), the bad fraction is at most \((71000\eta)^2\). Each draw of \(A_2\) hits this set with conditional probability at most \(2(71000\eta)^2\), since the denominator remains at least \(p-k\). The probability of the necessary number of hits is bounded by \(2^k[2(71000\eta)^2]^{0.24k}\). This estimate requires no conditional randomness of \(R,S,\mu\): these were fixed for the bound and will all be enumerated.

The cost for \(R\) and all \(S\) of size at most \(s_*\), divided by \(k\), is at most
\[
 0.101x+0.1\log(10e)+0.001\log(1000e)+o(1).
\]
This follows from \(\binom Nn\le(eN/n)^n\), using monotonicity of \(u\log(eke^x/u)\) up to the respective caps. Include the \(s_*+1\) possible sizes. The previous-container and law lists have log size \(o(k)\); the number of levels is \(O(\log\log p)\). The total log probability divided by \(k\) is bounded above by
\[
 o(1)+(0.101-2\cdot0.24\cdot0.22)x+
 0.1\log(10e)+0.001\log(1000e)+\log2+
 0.24\log(2\cdot71000^2)-480 .
\]
The slope is \(-0.0046\), and the intercept is below \(-470\). Thus the required configuration anywhere has probability \(o(1)\) on the joint balanced and typical events. In this argument those events were used only for the deterministic implication from a witness to a large hit count.

## 6. End of the proof

Start with the good centers and repeatedly retain all those in the new container from §3. The aggregate loss is less than \(4k/(3\cdot5000^2)\), by the geometric progression of active levels. Starting from \(k/9\), the retained number always exceeds \(0.11k\). By §5 a fitted outcome is excluded at every step with probability tending to one, jointly with the requisite events. The terminal container \(P\) then has size \(\le e^{5000}k\) and contains at least \(0.11k\) members of \(T\).

Apply (1) with \(M=e^{5000}\), the terminal list from §3, and \(\zeta=0.02\). We have \(|T|\ge0.98p/k+0.11k>1.01p/k\) for large \(p\), a contradiction. The terminal event is an unconditional event on \(A\); intersections with events on the ordered split cost only the sum of their failure probabilities. The canonical balanced-split argument then gives the assertion for \(A\) alone. \(\square\)
