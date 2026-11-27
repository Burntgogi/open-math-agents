# Green 74 partial results

Partial result for the large-dimension variant. Write f(d,N) for the maximum in the pinned statement. We obtain f(d,N) >= N^max(d-100,0) for every d <= 200 and N >= 1. In d = 201 we obtain the target for 1 <= N <= (9*10^9)^2. For all sufficiently large N we obtain the different bound f(201,N) >= c*N^100.5*(log N)^3, with c > 0 independent of N. The d = 201 target N^101 remains open.

Here is an elementary starting point for reproducing the result. Each forbidden five-set spans a line or a plane, and at least six of its triples span the same affine space. A coordinate projection injects that space's grid points into [N]^2. Thus the number E of forbidden sets satisfies 6E <= binom(N^d,3)*binom(N^2,2). Select points with probability 2*N^(-d/2-1) and delete one from each surviving forbidden set. This gives f(d,N) >= (14/9)*N^(d/2-1) for d,N >= 2, including the required coefficient at d = 198.

For the logarithmic gain, count coplanar five-sets on the integer spheres about a common central lattice point. Summing over squared radii gives O_d(N^(3d-8)) for d >= 16. The five planar shape points determine a conic, giving quadratic constraints on the direction vectors and linear constraints on the translation. The degenerate Gram matrices must be counted separately. Averaging selects one sphere with many points relative to its forbidden-set count. Sample and remove pairs of surviving forbidden sets sharing two or more vertices; the linear five-uniform hypergraph independence bound gives a factor (log N)^(1/4) in a block of dimension at least 16. The resulting set also has no three collinear points, so Cartesian products preserve the required five-point property. Use eleven 16-dimensional blocks and one 25-dimensional block for d = 201. The radius average does not give an upper bound on the independent sets of each individual sphere.

The result through dimension 100 was checked in Lean. The higher-dimensional counting and independence arguments are pen-and-paper results. The remaining gap in d = 201 is a factor of order sqrt(N)/(log N)^3.

[Catalogue problem](https://lefttosolve.com/p/Green74.green_74.variants.large)
