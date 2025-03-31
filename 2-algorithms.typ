#import "environments.typ": *

#import "symbols.typ": *

= Low-Degree Algorithms <section_algorithm>

An _algorithm_ is a function which takes as input an instance $g in RR^N$ and outputs some $x in Sigma_N$.
This definition can be extended to functions giving outputs on $RR^N$ and rounding to a vertex on the hypercube $Sigma_N$, which we consider in @section_rounding.
Alternatively, we could consider _randomized algorithms_ via taking as additional input some randomness $omega$ independent of the problem instance.
However, as this extension requires only minor changes, which we describe when relevant, most of our analysis will focus on the deterministic case.

The category of algorithms we consider are specifically _low degree algorithms_.
We treat two closely related notions of degree: first is _polynomial degree_, in which we assume our algorithms are given coordinate-wise by polynomials of some bounded degree.
The second, more general notion is _coordinate degree_, which roughly counts how many coordinates can interact nonlinearly; this can be applied to arbitrary algorithms given by $L^2$ functions.
While polynomial algorithms are widely known and studied, low coordinate degree algorithms were first introduced in Hopkins' thesis @hopkinsStatisticalInferenceSum2018, and were later used by Brennan et al. @brennanStatisticalQueryAlgorithms2021 and Mossel et al. @koehlerReconstructionTreesLowDegree2022 @huangOptimalLowDegree2025 (although in the latter case, they were shown to be equivalent to polynomial algorithms).
Compared to analytically-defined classes of algorithms (e.g. Lipschitz), these low degree algorithms have an algebraic structure that we can exploit to precisely control their stability properties.

As mentioned in the introduction, our goal is to show _strong low degree hardness_, meaning that low degree algorithms (either meaning low polynomial degree or low coordinate degree) fail to find solutions to the NPP with high probability.
However, our proofs only use the low degree assumption to apply stability bounds: roughly, a stable algorithm cannot "overcome" the gaps between solutions for two closely-related instances of the NPP.
Why, then, do we restrict to low degree algorithms specifically?
The main reason is the _low degree heuristic_:
#align(
  center,
  [
    _For nice random optimization problems, there exists a successful degree $D$ algorithm \ if and only if there exists a successful algorithm running in time $e^(tilde(O)(D))$._
  ],
)
This heuristic was first proposed in Hopkins' thesis @hopkinsStatisticalInferenceSum2018, and later expanded upon by Kunisky, Wein, and Bandeira @kuniskyNotesComputationalHardness2019, although this was primarily in the context of low degree polynomials for hypothesis testing.
Kunisky later expanded these results when applying low coordinate degree methods towards hypothesis testing @kuniskyLowCoordinateDegree2024a @kuniskyLowCoordinateDegree2024.
Huang and Sellke thus observed that strong low degree hardness up to $o(N)$ can be thought of as evidence of requiring exponential $e^(tilde(Omega)(N))$ time to find globally optimal solutions @huangStrongLowDegree2025.
They prove strong low degree hardness for a variety of random optimization problems: optimization of pure $k$-spin glasses, symmetric binary perceptrons, and random $k$-SAT, to name a few, most of which are optimal under the low degree heuristic.
However, Huang and Mossel's work on broadcasting on trees, this heuristic breaks down: degree $D <= O(log N)$ algorithms fail despite there existing a linear-time algorithm known as Belief Propagation @huangOptimalLowDegree2025.
To this end, the authors suggest this discrepancy arises from the requirement of "depth" in the Belief Propagation algorithm -- roughly, despite running in linear time, this algorithm still struggles in practice in the "hard" regime.
As a takeaway, we can surmise that the low degree heuristic is reasonable for describing random search problems involving optimization of a "flat" structure, in which algorithmic complexity cannot hide behind $N$-independent factors.
Thus, having an explicit handle on algorithm degree enables us to both control stability and extend our results to rule out general polynomial-time algorithms.

meow @liEasyOptimizationProblems2024

/*
$omega mapsto f(omega) := EE[ norm(alg(g,omega))^2 | omega]$

WTS $f(omega) <= C'(omega) N$

$
  EE[f(omega) | f(omega) <= C N] PP(f(omega) <= C N) + EE[f(omega) | f(omega) >= C N] PP(f(omega) >= C N) = EE[f(omega)] <= C N
$

$
  PP_omega (EE[norm(alg(g,omega))^2 | omega] >= C' N) <= (EE norm(alg(g,omega))^2) / (C' N) <= C / C'
$

$
  PP(alg(g,omega) in Soln(g)) &= EE[ PP(alg(g,omega) in Soln(g) | omega) ] \
  &<= EE[ ]
$
*/

== Coordinate Degree and $L^2$ Stability <section_algorithm_es>

First, we consider a general class of putative algorithms, and construct the "coordinate decomposition" underlying the notion of coordinate degree.
Given this notion, deriving stability bounds becomes a straightforward piece of functional analysis.
To start, recall the notion of $L^2$ functions:

// Def. L2 space of functions of N iid variables
#definition[
  Let $pi$ be a probability distribution on $RR$. The $L^2$ space $L2iid$ is the space of functions $f:RR^N to RR$ with finite $L^2$ norm.
  $
    EE[f^2] := integral_(RR^N) f(x)^2 dif pi^(times.circle N)(x) < infinity.
  $
  Alternatively, this is the space of $L^2$ functions of $N$ i.i.d. random variables $x_i$, distributed as $pi$.
] <def_L2_iid>

This is an extremely broad class of functions; for instance, all bounded functions are $L^2$.
Given any function $f in L2iid$, we can then consider how it depends on various subsets of the $N$ input coordinates.
In principle, everything about $f$ should be reflected in how it acts on all possible such subsets.
To formalize this intuition, define the following coordinate projection:

// Def. Projection of function.
#definition[
  Let $f in L2iid$ and $J subeq [N]$, with $overline(J)=[N] without J$.
  The _projection of $f$ onto $J$_ is the function $f^(subeq J): RR^N to RR$ given by
  $ f^(subeq J)(x) := EE[f(x_1,dots,x_n) | x_i, i in J] = EE[f(x) | x_J] $
] <def_subset_proj>

Intuitively $f^(subeq J)$ is $f$ with the $overline(J)$ coordinates re-randomized, so $f^(subeq J)$ only depends on the coordinates in $J$.
However, depending on how $f$ accounts for higher-order interactions, it might be the case that $f^(subeq J)$ is fully described by some $f^(subeq J')$, for $J' subset.neq J$.
What we really want is to decompose $f$ as
$ f = sum_(S subeq [N]) f^(= S) $ <eq_efron_stein_decomp>
where each $f^(=S)$ only depends on the coordinates in $S$, but not any smaller subset.
That is, if $T subset.eq.not S$ and $g$ depends only on the coordinates in $T$, then $inn(f^(=S), g)=0$.

This decomposition, often called the _Efron-Stein_, _orthogonal_, or _Hoeffding_ decomposition, does indeed exist.
Its applications in statistics come from the fact that it provides a way of decomposing the total variance of a function into the components coming from specific sets of coordinates, a step which underlies the ANOVA methodology.
These low coordinate degree decompositions have also been used in computational chemistry: see the reviews by Li et al. @liHighDimensionalModel2001 or Rabitz and Aliş @rabitzGeneralFoundationsHighdimensional1999 for more details.
The Efron-Stein decomposition exhibits the following combinatorial construction;
our presentation largely follows @odonnellAnalysisBooleanFunctions2021[#sym.section 8.3], as well as the paper @kuniskyLowCoordinateDegree2024a.

The motivating fact is that for any $J subeq [N]$, we should have
$ f^(subeq J) = sum_(S subeq J) f^(=S). $ <eq_efron_stein_motiv>
Intuitively, $f^(subeq J)$ captures everything about $f$ depending on the coordinates in $J$, and each $f^(subeq S)$ captures precisely the interactions within each subset $S$ of $J$.
The construction of $f^(= S)$ proceeds by inverting this formula.

First, we consider the case $J=emptyset$. It is clear that $f^(=emptyset) = f^(subeq emptyset)$, which, by @def_subset_proj is the constant function $EE[f]$.
Next, if $J={j}$ is a singleton, @eq_efron_stein_motiv gives
$ f^(subeq {j}) = f^(=emptyset) + f^(= {j}), $
and as $f^(subeq {j})(x) = EE[f | x_j]$, we get
$ f^(={j}) = EE[f | x_j] - EE[f]. $
This function only depends on $x_j$; all other coordinates are averaged over, thus measuring how the expectation of $f$ changes given $x_j$.

Continuing on to sets of two coordinates, some brief manipulation gives, for $J={i,j}$,
$
  f^(subeq {i,j}) &= f^(=emptyset) + f^(={i}) + f^(={j}) + f^(={i,j}) \
  &= f^(subeq emptyset) + (f^(subeq {i}) - f^(subeq emptyset)) + (f^(subeq {j}) - f^(subeq emptyset)) + f^(={i,j}) \
  therefore f^(={i,j}) &= f^(subeq {i,j}) - f^(subeq {i}) - f^(subeq {j}) + f^(subeq emptyset).
$
We can imagine that this accounts for the two-way interaction of $i$ and $j$, namely $f^(subeq {i,j}) = EE[f | x_i,x_j]$, while "correcting" for the one-way effects of $x_i$ and $x_j$ individually.
Inductively, we can continue on and define all the $f^(=J)$ via inclusion-exclusion, as
$
  f^(= J) := sum_(S subeq J) (-1)^(abs(J)-abs(S))f^(subeq S) = sum_(S subeq J) (-1)^(abs(J)-abs(S)) EE[f | x_S].
$

This construction, along with some direct calculations, leads to the following:

#theorem[@odonnellAnalysisBooleanFunctions2021[Thm 8.35]][
  Let $f in L2iid$. Then $f$ has a unique decomposition as
  $ f = sum_(S subeq [N]) f^(=S), $
  known as the _Efron-Stein decomposition_, where the functions $f^(=S) in L2iid$ satisfy
  #enum(
    numbering: "(1)",
    [$f^(=S)$ depends only on the coordinates in $S$;],
    [if $T subset.neq S$ and $g in L2iid$ only depends on coordinates in $T$, then $inn(f^(=S),g)=0$.],
  )
  In addition, this decomposition has the following properties:
  #enum(
    numbering: "(1)",
    start: 3,
    [Condition (2) holds whenever $S subset.eq.not T$.],
    [The decomposition is orthogonal: $inn(f^(=S),f^(=T))=0$ for $S eq.not T$.],
    [$sum_(S subeq T) f^(=S) = f^(subeq T)$.],
    [For each $S subeq [N]$, $f mapsto f^(=S)$ is a linear operator.],
  )
] <thrm_efron_stein>

In summary, this decomposition of any $L2iid$ function into it's different interaction levels not only uniquely exists, but is an orthogonal decomposition, enabling us to apply tools from elementary Fourier analysis.

@thrm_efron_stein further implies that we can define subspaces of $L2iid$ (see also @kuniskyLowCoordinateDegree2024a[#sym.section 1.3])
$
  V_J &:= { f in L2iid : f = f^(subeq J) }, \
  V_(<= D) &:= sum_(J subeq [N] \ abs(J) <= D) V_T.
$ <eq_es_subspaces>
These capture functions which only depend on some subset of coordinates, or some bounded number of coordinates. Note that $V_[N] = V_(<= N) = L2iid$.

With this, we can define the notion of "coordinate degree":

#definition[
  The _coordinate degree_ of a function $f in L2iid$ is
  $
    cdeg(f) := max { abs(S) : S subeq [N]\, f^(=S)!=0 } = min {D : f in V_(<= D) }
  $
  If $f=(f_1,dots,f_M): RR^N to RR^M$ is a multivariate function, then
  $ cdeg(f) := max_(i in [M]) cdeg(f_i). $
]

Intuitively, the coordinate degree is the maximum size of (nonlinear) multivariate interaction that $f$ accounts for.
Of course, this degree is also bounded by $N$, very much unlike polynomial degree.
Note as a special case that any multivariate polynomial of degree $D$ has coordinate degree at most $D$.
As an example, the function $x_1 + x_2$ has both polynomial degree and coordinate degree 1, while $x_1+x_2^2$ has polynomial degree 2 and coordinate degree 1.
We are especially interested in algorithms coming from functions in $V_(<= D)$, which we term _low coordinate degree algorithms_.

As we are interested in how these function behaves under small changes in its input, we are led to consider the following "noise operator," which lets us measures the effect of small changes in the input on the coordinate decomposition.
First, we need the following notion of distance between problem instances:

#definition[
  For $p in [0,1]$, and $x in RR^N$, we say $y in RR^N$ is _$p$-resampled from $x$_, denoted $y~pi^(times.circle N)_p (x)$, if $y$ is chosen as follows: for each $i in [N]$, independently,
  $
    y_i = cases(x_i &"with probability" p, "drawn from" pi #h(2em)&"with probability" 1-p).
  $
  We say $(x,y)$ are a _$p$-resampled pair_.
] <def_p_resampled>

Note that being $p$-resampled and being $p$-correlated are rather different - for one, there is a nonzero probability that, for $pi$ a continuous probability distribution, $x=y$ when they are $p$-resampled, even though this a.s. never occurs if they were $p$-correlated.

// #show sym.EE: math.limits

#definition[
  For $p in [0,1]$, the _noise operator_ $T_p$ is the linear operator on $L2iid$ defined by
  $ T_p f(x) = EE_(y ~ pi^(times.circle N)_p (x))[f(y)] $
  In particular, $inn(f,T_p f) = EE_((x,y)" " p"-resampled") [f(x) dot f(y)]$.
]

// #show sym.EE: math.scripts

This noise operator changes the Efron-Stein decomposition, and hence the behavior of low coordinate degree functions, in a controlled way:

#lemma[
  Let $p in [0,1]$ and $f in L2iid$ have Efron-Stein decomposition $f=sum_(S subeq [N]) f^(=S)$. Then
  $ T_p f(x) = sum_(S subeq [N]) p^(abs(S))f^(=S). $
] <lem_es_noise_op>
#proof[
  Let $J$ denote a $p$-random subset of $[N]$, i.e. with $J$ formed by including each $i in [N]$ independently with probability $p$.
  By definition, $T_p f(x) = EE_J [f^(subeq J)(x)]$ (i.e. pick a random subset of coordinates to fix, and re-randomize the rest).
  We know by @thrm_efron_stein that $f^(subeq J) = sum_(S subeq J) f^(=S)$, so
  $
    T_p f(x) = EE_J [ sum_(S subeq J) f^(=S) ] = sum_(S subeq [N]) EE_J [I(S subeq J)] dot f^(=S) = sum_(S subeq [N]) p^abs(S) f^(=S),
  $
  since for a fixed $S subeq [N]$, the probability that $S subeq J$ is $p^abs(S)$.
]

Thus, we can derive the following stability bound on low coordinate degree functions.

#theorem[
  Let $p in [0,1]$ and let $f=(f_1,dots,f_M):RR^N arrow RR^M$ be a multivariate function with coordinate degree $D$ and each $f_i in L2iid$.
  Suppose that $(x,y)$ are a $p$-resampled pair under $pi^(times.circle N)$, and $EE norm(f(x))^2 = 1$. Then
  $ EE norm(f(x)-f(y))^2 <= 2(1-p^D) <= 2(1-p)D. $ <eq_es_stability>
] <thrm_es_stability>
#proof[
  Observe that
  $
    EE norm(f(x)-f(y))^2 &= EE norm(f(x))^2 + EE norm(f(y))^2 - 2 EE inn(f(x),f(y)) \ &= 2 - 2(sum_i EE[f_i (x) f_i (y)])
    \ &= 2 - 2(sum_i inn(f_i,T_p f_i)).
  $ <eq_thrm_es_stability_1>
  Here, we have for each $i in [M]$ that
  $
    inn(f_i,T_p f_i) = inn(sum_(S subeq [N]) f_i^(=S), sum_(S subeq [N]) p^abs(S) f_i^(=S))= sum_(S subeq [N]) p^abs(S) norm(f_i^(=S) )^2,
  $
  by @lem_es_noise_op and orthogonality.
  Now, as each $f_i$ has coordinate degree at most $D$, the sum above can be taken only over $S subeq [N]$ with $0 <= abs(S) <= D$, giving the bound
  $
    p^D EE [f_i (x)^2] <= inn(f_i,T_p f_i)=EE[f_i (x) dot T_p f_i (x)] <= EE[f_i (x)^2].
  $
  Summing up over $i$, and using that $EE norm(f(x))^2 = 1$, gives
  $ p^D <= sum_i inn(f_i,T_p f_i) = EE inn(f(x),f(y)) <= 1. $
  Finally, we can substitute into @eq_thrm_es_stability_1 to get
  #footnote[The last inequality follows from $(1-p^D) = (1-p)(1+p+p^2+ dots p^(D-1))$; the bound is tight for $p approx 1$.]
  $
    EE norm(f(x) - f(y))^2 <= 2 - 2 p^D = 2(1-p^D) <= 2(1-p)D. #qedhere
  $
]

== Hermite Polynomials

Alternatively, we can consider the much more restrictive (but more concrete) class of honest polynomials. When considered as functions of independent Normal variables, such functions admit a simple description in terms of _Hermite polynomials_, which enables us to prove similar bounds as @thrm_es_stability.
This theory is much more classical, so we encourage the interested reader to see @odonnellAnalysisBooleanFunctions2021[#sym.section 11] for details.

#definition[
  Let $gamma_N$ be the $N$-dimensional standard Normal measure on $RR^N$. The _$N$-dimensional Gaussian space_ is the space $L2normN$ of $L^2$ functions of $N$ i.i.d. standard Normal r.v.s.
]

Note that under the usual $L^2$ inner product, $inn(f,g) = EE[f dot g]$, this is a separable Hilbert space.

It is a well-known fact that the monomials $1,z,z^2,dots$ form a complete basis for $L2norm$ @odonnellAnalysisBooleanFunctions2021[Thm 11.22].
However, these are far from an orthonormal "Fourier" basis; for instance, we know $EE[z^2]=1$ for $z ~ Normal(0,1)$.
By the Gram-Schmidt process, these monomials can be converted into the _(normalized) Hermite polynomials_ $h_j$ for $j>=0$, given as
$
  h_0(z)=1,
  #h(2em)
  h_1(z)=z,
  #h(2em)
  h_2(z)=(z^2-1)/sqrt(2),
  #h(2em)
  h_3(z)=(z^3-3z)/sqrt(6),
  #h(2em)
  ...
$ <eq_hermite_polys>
Note here that each $h_j$ is a degree $j$ polynomial. With these, we have:

#theorem([@odonnellAnalysisBooleanFunctions2021[Prop 11.30]])[
  The Hermite polynomials $(h_j)_(j >= 0)$ form a complete orthonormal basis for $L2norm$.
]

To extend this to $L2normN$, we can take products. For a multi-index $alpha in NN^N$, we define the multivariate Hermite polynomial $h_alpha: RR^N to RR$ as
$ h_alpha (z) := product_(j=1)^N h_(alpha_j)(z_j). $
The degree of $h_alpha$ is clearly $abs(alpha)=sum_j alpha_j$.

#theorem[
  The Hermite polynomials $(h_alpha)_(alpha in NN^N)$ form a complete orthonormal basis for $L2normN$. In particular, every $f in L2normN$ has a unique expansion in $L^2$ norm as
  $ f(z) = sum_(alpha in NN^N) hat(f)(alpha) h_alpha (z). $
] <thrm_hermite>

As a consequence of the uniqueness of the expansion in <thrm_hermite>, we see that polynomials are their own Hermite expansion.
Namely, let $H^(<= k) subeq L2normN$ be the subset of multivariate polynomials of degree at most $k$. Then, any $f in H^(<= k)$ can be Hermite expanded as
$
  f(z) = sum_(alpha in NN^N) hat(f)(alpha) h_alpha (z) = sum_(abs(alpha) <= k) hat(f)(alpha) h_alpha (z).
$
Thus, $H^(<= k)$ is the closed linear span of the set ${ h_alpha : abs(alpha) <= k}$.

When working with honest polynomials, the traditional notion of correlation is a much more natural measure of "distance" between inputs:

#definition[
  Let $(x,y)$ be $N$-dimensional standard Normal vectors. We say $(x,y)$ are _$p$-correlated_ if $(x_i,y_i)$ are $p$-correlated for each $i in [N]$, and these pairs are mutually independent.
]

In a similar way to the Efron-Stein case, we can consider the resulting "noise operator," as a way of measuring the effect on a function of a small change in the input.

#show sym.EE: math.limits

#definition[
  For $p in [0,1]$, the _Gaussian noise operator_ $T_p$ is the linear operator on $L2normN$, given by
  $
    T_p f(x) = EE_(y " " p"-correlated to" x)[f(y)] = EE_(y ~ stdnorm )[ f(p x + sqrt(1-p^2) y)]
  $
]
#show sym.EE: math.scripts

This operator admits a more classical description in terms of the Ornstein-Uhlenbeck semigroup, but we will not need that connection here.
As it happens, a straightforward computation with the Normal moment generating function gives the following:

#lemma[@odonnellAnalysisBooleanFunctions2021[Prop 11.37]][
  Let $p in [0,1]$ and $f in L2normN$. Then $T_p f$ has Hermite expansion
  $ T_p f = sum_(alpha in NN^N) p^abs(alpha) hat(f)(alpha) h_alpha $
  and in particular,
  $ inn(f, T_p f) = sum_(alpha in NN^N) p^abs(alpha) hat(f)(alpha)^2. $
] <lem_hermite_noise_op>

With this in hand, we can prove a similar stability bound to @thrm_es_stability.

#theorem[
  Let $p in [0,1]$ and let $f=(f_1,dots,f_M):RR^N arrow RR^M$ be a multivariate polynomial with degree $D$.
  Suppose that $(x,y)$ are a $p$-correlated pair of standard Normal vectors, and $EE norm(f(x))^2 = 1$.
  Then
  $ EE norm(f(x)-f(y))^2 <= 2(1-p^D) <= 2(1-p)D. $ <eq_poly_stability>
] <thrm_poly_stability>
#proof[
  The proof is almost identical to that of @thrm_es_stability (see also @gamarnikHardnessRandomOptimization2022a[Lem. 3.4]).
  The main modification is to realize that for each $f_i$, having degree at most $D$ implies that $hat(f_i)(alpha) = 0$ for $abs(alpha)>D$. Thus, as $p^D <= p^s <= 1$ for all $s <= D$, we can apply @lem_hermite_noise_op to get
  $
    p^D EE[f_i (x)^2] <= inn(f_i, T_p f_i) = sum_(alpha in NN^N : abs(alpha) <= D) p^abs(alpha) hat(f_i)(alpha)^2 <= EE[f_i (x)^2].
  $
  From there, the proof proceeds as before.
]

As a comparison to the case for functions with coordinate degree $D$, notice that @thrm_poly_stability gives, generically, a much looser bound.
In exchange, being able to use $p$-correlation as a "metric" on the input domain will turn out to offer significant benefits in the arguments which follow, justifying equal consideration of both classes of functions.

== Stability of Low-Degree Algorithms <section_algorithm_stability>

With these notions of low degree functions/polynomials in hand, we can consider algorithms based on such functions.

#definition[
  A _(randomized) algorithm_ is a measurable function $alg :(g,omega) mapsto x in Sigma_N$, where $omega in Omega_N$ is an independent random variable. Such an $alg$ is _deterministic_ if it does not depend on $omega$.
] <def_algorithm>

As discussed in the introduction to this section, we will usually focus on deterministic algorithms, discussing the minor modifications necessary for handling randomized algorithms as necessary.
In addition, many practical algorithms are $RR^N$-valued, which must be rounded to give outputs on $Sigma_N$.
For simplicity, we assume for now that our algorithms are $Sigma_N$-valued, and discuss the extensions to handle this rounding in @section_rounding.

#definition[
  A _polynomial algorithm_ is an algorithm $alg(g,omega)$ where each coordinate of $alg(g,omega)$ is given by a polynomial in the $N$ entries of $g$. If $alg$ is a polynomial algorithm, we say it has degree $D$ if each coordinate has degree at most $D$ (with at least one equality).
]

We can broaden the notion of polynomial algorithms (with their obvious notion of degree) to algorithms with a well-defined notion of coordinate degree:

#definition[
  Suppose an algorithm $alg(g,omega)$ is such that each coordinate of $alg(-,omega)$ is in $L2iid$. Then, the _coordinate degree_ of $alg$ is the maximum coordinate degree of each of its coordinate functions.
]

As we've seen, these algorithms admit clear stability bounds:

// Thrm. Stability of randomized algorithms (part 1 of Prop 1.9)

#proposition[Low-Degree Stability -- @huangStrongLowDegree2025[Prop. 1.9]][
  Suppose we have a deterministic algorithm $alg$ with degree (resp. coordinate degree) $<= D$ and norm $EE norm(alg(g))^2 <= C N$.
  Then, for inputs $g,g'$ which are $(1-epsilon)$-correlated (resp. $(1-epsilon)$-resampled),
  $ EE norm(alg(g) - alg(g'))^2 <= 2C D epsilon N, $ <eq_alg_expected_stability>
  and thus
  $
    PP( norm(alg(g) - alg(g'))>= 2sqrt(eta N)) <= (C D epsilon) / (2 eta) asymp (D epsilon) / eta
  $ <eq_alg_stability>
] <prop_alg_stability>
#proof[
  Let $C' := EE norm(alg(g))^2$, and define the rescaling $alg' := alg slash sqrt(C')$. Then, by @thrm_poly_stability (or @thrm_es_stability, in the low coordinate degree case), we have
  $
    EE norm(alg'(g) - alg'(g'))^2 = 1 / (C') EE norm(alg(g) - alg(g'))^2 <= 2 D epsilon.
  $
  Multiplying by $C'$ gives @eq_alg_expected_stability (as $C' <= C N$).
  Finally, @eq_alg_stability follows from Markov's inequality.
]

#remark[
  Note that @prop_alg_stability also holds for randomized algorithms meow
]


/*
#example[
  Let $bold(U)=(U_1,dots,U_N)$ be i.i.d. $Unif([-1,1])$. Then, we define the random coordinate-wise function
  $ "round"_bold(U)(bold(x))=("round"_(U_1)(x_1),dots,"round"_(U_N)(x_N)), $
  where we define
  $ "round"_U (x) = cases(1" " &x >= U, -1"  " &x < U). $
] <randomized_rounding>

#example[
  Given a real-valued algorithm $cal(A)^degree$, we can convert it into a $Sigma_N$-valued algorithm $cal(A)$ via
  $ cal(A)(g,omega,bold(U)) := round_bold(U)(cal(A)^degree (g,omega)). $
] <rounded_algorithm>

By the will of God (i.e. writeup pending), we have the following:

As a consequence, a degree $D$ algorithm $alg$ has $p_"unstable" = o_N(1)$ for $eta ^4 >> epsilon D$.
*/
