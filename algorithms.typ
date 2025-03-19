#import "environments.typ": *

#import "symbols.typ": *

= Low-Degree Algorithms

For our purposes, an #emph[algorithm] is a function which takes as input a problem instance $g ~ stdnorm$ and outputs some $x in Sigma_N$.
This definition can be extended to functions giving outputs on $RR^N$ (and rounding to a vertex on the hypercube $Sigma_N$), or to taking as additional input some randomness $omega$, allowing for randomized algorithms.
However, most of our analysis will focus on the deterministic case.

To further restrict the category of algorithms considered, we specifically restrict to #emph[low-degree algorithms].
Compared to analytically-defined classes of algorithms (e.g. Lipschitz), these algorithms have a regular algebraic structure that we can exploit to precisely control their stability properties.
In particular, our goal is to show #emph[strong low-degree hardness], in the sense of @huangStrongLowDegree2025[Def. 3].

#definition[Strong Low-Degree Hardness][
  A random search problem, namely a $N$-indexed sequence of input vectors $y_N in RR^(d_N)$ and random subsets $S_N = S_N(y_N) subeq Sigma_N$, exhibits #emph[strong low-degree hardness up to degree $D <= o(D_N)$] if, for all sequences of degree $o(D_N)$ algorithms $(alg_N)$ with $EE norm(alg(y_N))^2 <= O(N)$, we have
  $ PP(alg(y_N) in S_N) <= o(1). $
]

// Why study low-degree algorithms (poly time heuristic + simple)

In addition, degree $D$ polynomials are a heuristic proxy for the class of $e^(tilde(O)(D))$-time algorithms @hopkinsStatisticalInferenceSum2018 @kothariSumSquaresLower2017.
Thus, strong low-degree hardness up to $o(N)$ can be thought of as evidence of requiring exponential (i.e. $e^Omega(N)$) time to find globally optimal solutions.

For the case of NPP, we consider two distinct notions of degree.
One is traditional polynomial degree, which has an intuitive interpretation, but the other, which we term Efron-Stein degree, is a more flexible notion which can be applied to a much broader class of algorithms.
As we will see in @section_proof, these classes of algorithms exhibit quantitatively different behavior, in line with existing heuristics for the "brittleness" of NPP.

== Efron-Stein Degree and $L^2$ Stability

First, we consider a very general class of putative algorithms, where the notion of "degree" corresponds to how complex the interactions between the input variables can get.
Given this notion, deriving stability bounds becomes a straightforward piece of functional analysis.
To start, recall the notion of $L^2$ functions:

// Def. L2 space of functions of N iid variables
#definition[
  Let $pi$ be a probability distribution on $RR$. The $L^2$ space $L2iid$ is the space of functions $f:RR^N to RR$ with finite $L^2$ norm.
  $
    EE[f^2] := integral_(x=(x_1,dots,x_n) in RR^N) f(x)^2 dif pi^(times.circle N)(x) < infinity.
  $
  Alternatively, this is the space of $L^2$ functions of $N$ i.i.d. random variables $x_i$, distributed as $pi$.
] <def_L2_iid>

Given any function $f in L2iid$, we can consider how it depends on various subsets of the $N$ input coordinates.
In principle, everything we want to know about $f$ should be reflected in how it acts on all possible such subsets.
To formalize this intuition, we define the following coordinate projection:

// Def. Projection of function.
#definition[
  Let $f in L2iid$ and $J subeq [N]$, with $overline(J)=[N] without J$. The #emph[projection of $f$ onto $J$] is the function
  $f^(subeq J): RR^N to RR$ given by
  $ f^(subeq J)(x) = EE[f(x_1,dots,x_n) | x_i, i in J]. $
  This is $f$ with the $overline(J)$ coordinates re-randomized, so $f^(subeq J)$ only depends on $x_J$.
] <def_es_proj>

Intuitively $f^(subeq J)$ is the part of $f$ which only depends on the coordinates in $J$.
However, depending on how $f$ accounts for higher-order interactions, it might be the case that $f^(subeq J)$ is fully described by some $f^(subeq J')$, for $J' subset.neq J$.
What we really want is to decompose $f$ as
$ f = sum_(S subeq [N]) f^(= S) $ <eq_efron_stein_decomp>
where each $f^(=S)$ only depends on the coordinates in $S$, but not any smaller subset.
That is, if $T subset.eq.not S$ and $g$ depends only on the coordinates in $T$, then $inn(f^(=S), g)=0$.

This decomposition, often called the #emph[Efron-Stein decomposition], does indeed exist, and exhibits the following combinatorial construction.
Our presentation largely follows @odonnellAnalysisBooleanFunctions2021[#sym.section 8.3] (who refers to this as the #emph[orthogonal decomposition]).

The motivating fact is that we should expect that for any $J subeq [N]$, we should have
$ f^(subeq J) = sum_(S subeq J) f^(=S). $ <eq_efron_stein_motiv>
Intuitively, $f^(subeq J)$ captures everything about $f$ depending on the coordinates in $J$, and each $f^(subeq S)$ captures precisely the interactions within each subset $S$ of $J$.
The construction of $f^(= S)$ proceeds by inverting this formula.

First, we consider the case $J=emptyset$. It is clear that $f^(=emptyset) = f^(subeq emptyset)$, which, by @def_es_proj is the constant function $EE[f]$.
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

This construction, along with some direct calculations, leads to the following theorem on Efron-Stein decompositions:

/*
To see that these functions are indeed orthogonal, we need the following computation:

#lemma[
  Let $f,g in L2iid$ and $I,J subeq [n]$ be subsets of coordinates.
  Assume that $f$ only depends on coordinates in $I$ and likewise for $g$ and $J$.
  Then $inn(f,g) = inn(f^(subeq I inter J), g^(subeq I inter J))$.
]
#proof[
  Assume without loss of generality that $I union J = [n]$.
  Then, given $x in RR^N$, we can split it into $(x_(I inter J), x_(I without J), x_(J without I))$. Abusing notation slightly to only include the coordinates a function actually depends on, we have
  $
    inn(f,g) &= EE_(x_(I inter J), x_(I without J), x_(J without I))[f(x_(I inter J), x_(I without J)) dot g(x_(I inter J), x_(J without I))] \
    &= EE_(x_(I inter J))[ EE_(x_(I without J))[f(x_(I inter J), x_(I without J))] dot
      EE_(x_(J without I))[g(x_(I inter J), x_(J without I))] ] \
    &= EE_(x_(I inter J))[ f^(subset I inter J)(x_(I inter J)) dot
      g^(subset I inter J)(x_(I inter J)) ] \
    &= inn(f^(subeq I inter J), g^(subeq I inter J)).
  $
  The first line follows from Adam's law and independence of $x_(I without J)$ and $x_(J without I)$, while the second follows from definition of $f^(subset I inter J)$ and $g^(subset I inter J)$.
]
*/

#theorem[@odonnellAnalysisBooleanFunctions2021[Thm 8.35]][
  Let $f in L2iid$. Then $f$ has a unique decomposition as
  $ f = sum_(S subeq [N]) f^(=S) $
  where the functions $f^(=S) in L2iid$ satisfy
  + $f^(=S)$ depends only on the coordinates in $S$;
  + if $T subset.neq S$ and $g in L2iid$ only depends on coordinates in $T$, then $inn(f^(=S),g)=0$.
  In addition, this decomposition has the following properties:
  3. Condition 2. holds whenever $S subset.eq.not T$.
  + The decomposition is orthogonal: $inn(f^(=S),f^(=T))=0$ for $S eq.not T$.
  + $sum_(S subeq T) f^(=S) = f^(subeq T)$.
  + For each $S subeq [N]$, $f mapsto f^(=S)$ is a linear operator.
] <thrm_efron_stein>

In summary, this desired decomposition of any $L2iid$ function into it's different interaction levels not only uniquely exists, but is an orthogonal decomposition, enabling us to apply tools from elementary Fourier analysis.

We can finally define the Efron-Stein notion of "degree":

#definition[
  The #emph[Efron-Stein degree] of a function $f in L2iid$ is
  $ deg_"ES" (f) = max_(S subeq [N] "s.t." f^(=S)!= 0) |S|. $
  If $f=(f_1,dots,f_M): RR^N to RR^M$ is a multivariate function, then the Efron-Stein degree of $f$ is the maximum degree of the $f_i$.
]

Intuitively, the Efron-Stein degree is the maximum size of multivariate interaction that $f$ accounts for. Of course, this degree is also bounded by $N$, very much unlike polynomial degree. Note as a special case that any multivariate polynomial of degree $D$ has Efron-Stein degree at most $D$.

As we are interested in how these function behaves under small changes in its input, we are led to consider the following "noise operator," which lets us measures the effect of small changes in the input on the Efron-Stein decomposition.
First, we need the following notion of distance between problem instances:

#definition[
  For $p in [0,1]$, and $x in RR^N$, we say $y in RR^N$ is #emph[$p$-resampled from $x$] if $y$ is chosen as follows: for each $i in [N]$, independently,
  $
    y_i = cases(x_i &"with probability" p, "drawn from" pi #h(2em)&"with probability" 1-p).
  $
  We say $(x,y)$ is a #emph[$p$-resampled pair].
] <def_p_resampled>

Note that being $p$-resampled and being $p$-correlated are rather different - for one, there is a nonzero probability that, for $pi$ a continuous probability distribution, $x=y$ when they are $p$-resampled, even though this a.s. never occurs.

// #show sym.EE: math.limits

#definition[
  For $p in [0,1]$, the #emph[noise operator] is the linear operator $T_p$ on $L2iid$, defined by, for $y$ $p$-resampled from $x$
  $ T_p f(x) = EE_(y " " p"-resampled from" x)[f(y)] $
  In particular, $inn(f,T_p f) = EE_((x,y)" " p"-resampled") [f(x) dot f(y)]$.
]

// #show sym.EE: math.scripts

As claimed, we can compute how this operator changes the Efron-Stein decomposition:

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

Putting these facts together, we can derive the following stability bound on functions of bounded Efron-Stein degree.

#theorem[
  Let $p in [0,1]$ and let $f=(f_1,dots,f_M):RR^N arrow RR^M$ be a multivariate function with Efron-Stein degree $D$ and each $f_i in L2iid$.
  Suppose that $(x,y)$ are a $p$-resampled pair under $pi^(times.circle N)$, and $EE norm(f(x))^2 = 1$. Then
  $ EE norm(f(x)-f(y))^2 <= 2(1-p^D) <= 2(1-p)D. $ <eq_es_stability>
] <thrm_es_stability>
#proof[
  Observe that
  $
    EE norm(f(x)-f(y))^2 &= EE norm(f(x))^2 + EE norm(f(y))^2 - 2 EE inn(f(x),f(y)) \ &= 2 - 2(sum_i EE[f_i (x) f_i (y)])
    \ &= 2 - 2(sum_i inn(f_i,T_p f_i)).
  $ <eq_thrm_es_stability_1>
  Here, we have for each $i in [N]$ that
  $
    inn(f_i,T_p f_i) = inn(sum_(S subeq [N]) f_i^(=S), sum_(S subeq [N]) p^abs(S) f_i^(=S))= sum_(S subeq [N]) p^abs(S) norm(f_i^(=S) )^2,
  $
  by @lem_es_noise_op and orthogonality.
  Now, as each $f_i$ has Efron-Stein degree at most $D$, the sum above can be taken only over $S subeq [N]$ with $0 <= abs(S) <= D$, giving the bound
  $
    p^D EE [f_i (x)^2] <= inn(f_i,T_p f_i)=EE[f_i (x) dot T_p f_i (x)] <= EE[f_i (x)^2].
  $
  Summing up over $i$, and using that $EE norm(f(x))^2 = 1$, gives
  $ p^D <= sum_i inn(f_i,T_p f_i) = EE inn(f(x),f(y)) <= 1. $
  Finally, we can substitute into @eq_thrm_es_stability_1 to get
  $
    EE norm(f(x) - f(y))^2 <= 2 - 2 p^D = 2(1-p^D) <=
  #footnote[This follows from the identity $(1-p^D) = (1-p)(1+p+p^2+ dots p^(D-1))$; the bound is tight for $p approx 1$.]
  #h(0.4em)
  2(1-p)D,
  $
  as desired.
]

== Hermite Polynomials

Alternatively, we can consider the much more restrictive (but more concrete) class of honest polynomials. When considered as functions of independent Normal variables, such functions admit a simple description in terms of #emph[Hermite polynomials], which enables us to prove similar bounds as @thrm_es_stability.
This theory is much more classical, so we encourage the interested reader to see @odonnellAnalysisBooleanFunctions2021[#sym.section 11] for details.

To start, we consider the following space of $L^2$ functions:

#definition[
  Let $gamma_N$ be the $N$-dimensional standard Normal measure on $RR^N$. Then the #emph[$N$-dimensional Gaussian space] is the space $L2normN$ of $L^2$ functions of $N$ i.i.d. standard Normal random variables.
]

Note that under the usual $L^2$ inner product, $inn(f,g) = EE[f dot g]$, this is a separable Hilbert space.

It is a well-known fact that the monomials $1,z,z^2,dots$ form a complete basis for $L2norm$ @odonnellAnalysisBooleanFunctions2021[Thm 11.22].
However, these are far from an orthonormal "Fourier" basis; for instance, we know $EE[z^2]=1$ for $z ~ Normal(0,1)$.
By the Gram-Schmidt process, these monomials can be converted into the #emph[(normalized) Hermite polynomials] $h_j$ for $j>=0$, given as
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
Note here that each $h_j$ is a degree $j$ polynomial.

It is then straightforward to show the following:

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
  Let $(x,y)$ be $N$-dimensional standard Normal vectors. We say $(x,y)$ are #emph[$p$-correlated] if $(x_i,y_i)$ are $p$-correlated for each $i in [N]$, and these pairs are mutually independent.
]

In a similar way to the Efron-Stein case, we can consider the resulting "noise operator," as a way of measuring a the effect on a function of a small change in the input.

#show sym.EE: math.limits

#definition[
  For $p in [0,1]$, the #emph[Gaussian noise operator] $T_p$ is the linear operator on $L2normN$, given by
  $
    T_p f(x) = EE_(y " " p"-correlated to" x)[f(y)] = EE_(y ~ stdnorm )[ f(p x + sqrt(1-p^2) y)]
  $
]
#show sym.EE: math.scripts

This operator admits a more classical description in terms of the Ornstein-Uhlenbeck semigroup, but we will not need those connections for what follows.
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

As a comparision to the case for functions with Efron-Stein degree $D$, notice that @thrm_poly_stability gives a much looser bound.
For instance, the function $f(x)=x_1^2 x_2^4$ has Efron-Stein degree 2, but polynomial degree 6.
In exchange, being able to use $p$-correlation as a "metric" on the input domain will turn out to offer significant benefits in the arguments which follow, justifying equal consideration of both classes of functions.

== Algorithms

Def. Randomized algorithm

Def. degree of algorithm is degree as multivariate function.

Discussion of how low-degree algs are approximate for class of Lipschitz algorithms?

Need for rounding function to land on $Sigma_N$

Construction of randomized rounding function.

Constr. rounded algorithm.

Lemma. stability of rounding

Thrm. Stability of randomized algorithms (part 1 of Prop 1.9)

Show that Markov gives a useful bound on


#lemma[
  Let $f:RR^N arrow RR^N$, $p in [0,1]$, and $X,Y$ marginally $N$-dimensional standard Normal vectors.
  Suppose that $EE norm(f(X))_2^2 = 1$ and either of the following cases hold:
  #[
    #set enum(numbering: "I.")
    + $(X,Y)$ are a $p$-resampled pair, and $f$ is a degree-$D$ function.
    + $(X,Y)$ are $p$-correlated, and $f$ is a degree-$D$ polynomial.
  ]
  Then
  $ EE norm(f(X)- f(Y))_2^2 <= 2(1-p^D). $
]

#definition[
  A #emph[randomized algorithm] is a measurable function $cal(A)^degree :(g,omega) mapsto bold(x) in RR^N $, where $omega in Omega_N$ is an independent random variable in some Polish space. Such an $cal(A)^degree$ is #emph[deterministic] if it does not depend on $omega$.
] <algorithm>

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


#definition[
  Algorithm $alg$ is $(epsilon,eta,p_"unstable")$-stable if, for $g,g'$ $(1-epsilon)$-correlated/resampled, we have
  $ PP(norm(alg(g) - alg(g'))<= eta sqrt(N)) >= 1-p_"unstable". $
] <stability_def>

By the will of God (i.e. writeup pending), we have the following:

#lemma[Algorithm $alg$ with degree $<= D$ and norm $EE norm(alg(g))^2 <= C N$ has
  $ EE norm(alg(g) - alg(g'))^2 <= 2C N epsilon D, $
  and (because of randomized rounding)
  $ EE norm(alg(g)- alg(g'))^4 <= 16 C N^2 epsilon D. $
  Thus,
  $
    PP(norm(alg(g) - alg(g'))>= eta sqrt(N)) <= (16 C N^2 epsilon D) / (eta^4 N^2) asymp (epsilon D) / eta^4.
  $
] <stability>

As a consequence, a degree $D$ algorithm $alg$ has $p_"unstable" = o_N(1)$ for $eta ^4 >> epsilon D$.

