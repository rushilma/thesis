#import "environments.typ": *

#import "symbols.typ": *

= Low-Degree Algorithms

What are algorithms of interest

For our purposes, an #emph[algorithm] is a function which takes as input

Why study low-degree algorithms (poly time heuristic + simple)

Different notions of degree.

Overview of section
- Efron-Stein notion
- Hermite notion
- Algorithms and Stability Bounds

== Efron-Stein Polynomials (TODO)


// Def. L2 space of functions of n iid variables
#definition[
  Let $pi$ be a probability distribution on $RR$. The $L^2$ space $L2iid$ is the space of functions $f:RR^N to RR$ with finite $L^2$ norm.
  $
    EE[f^2] := integral_(x=(x_1,dots,x_n) in RR^N) f(x)^2 dif pi^(times.circle N)(x) < infinity.
  $
  Alternatively, this is the space of $L^2$ functions of $N$ i.i.d. random variables $x_i$ distributed as $pi$.
] <def_L2_iid>

Motivation for studying decompositions of functions by projecting onto coordinates.


Want to decompose
$ f = sum_(S subeq [n]) f^(= S) $ <eq_efron_stein_decomp>

Want $f^(=S)$ to only depend on the coordinates in $S$.

If $T subset.eq.not S$ and $g$ depends only on the coordinates in $T$, then $inn(f^(=S), g)=0$.

// Def. Projection of function.
#definition[
  Let $f in L2iid$ and $J subset.eq [n]$, with $overline(J)=[n] without J$. The #emph[projection of $f$ onto $J$] is the function
  $f^(subset.eq J): RR^N to RR$ given by
  $ f^(subset.eq J)(x) = EE[f(x_1,dots,x_n) | x_i, i in J]. $
  This is $f$ with the $overline(J)$ coordinates re-randomized, so $f^(subset.eq J)$ only depends on $x_J$.
]

// Follow O'Donnell

In particular, we should have that
$ f^(subeq J) = sum_(S subeq J) f^(=S) $ <eq_efron_stein_motiv>

First, we consider the case $J=emptyset$. It is clear that $f^(=emptyset) = f^(subeq emptyset)$, which is the constant function $EE[f]$.

Next, if $J={j}$ is a singleton, @eq_efron_stein_motiv gives
$ f^(subeq {j}) = f^(=emptyset) + f^(= {j}), $
and as $f^(subeq {j})(x) = EE[f | x_j]$, we get
$ f^(={j}) = EE[f | x_j] - EE[f]. $

This function only depends on $x_j$; all other coordinates are averaged over. It measures what difference in expectation of $f$ is given $x_j$.

Continuing on to sets of two coordinates, some brief manipulation gives, for $J={i,j}$,
$
  f^(subeq {i,j}) &= f^(=emptyset) + f^(={i}) + f^(={j}) + f^(={i,j}) \
  &= f^(subeq emptyset) + (f^(subeq {i}) - f^(subeq emptyset)) + (f^(subeq {j}) - f^(subeq emptyset)) + f^(={i,j}) \
  therefore f^(={i,j}) &= f^(subeq {i,j}) - f^(subeq {i}) - f^(subeq {j}) + f^(subeq emptyset).
$
Inductively, all the $f^(=J)$ can be defined via the principle of inclusion-exclusion.

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

// Lem. Orthogonality of fns of different subsets

// Thrm. Unique existence of Efron-Stein basis

#theorem[O'Donnell, Theorem 8.35][
  Let $f in L2iid$. Then $f$ has a unique decomposition as
  $ f = sum_(S subeq [n]) f^(=S) $
  where the functions $f^(=S) in L2iid$ satisfy
  + $f^(=S)$ depends only on the coordinates in $S$;
  + if $T subset.neq S$ and $g in L2iid$ only depends on coordinates in $T$, then $inn(f^(=S),g)=0$.
  In addition, this decomposition has the following properties:
  3. Condition 2. holds whenever $S subset.eq.not T$.
  + The decomposition is orthogonal: $inn(f^(=S),f^(=T))=0$ for $S eq.not T$.
  + $sum_(S subeq T) f^(=S) = f^(subeq T)$.
  + For each $S subeq [n]$, $f mapsto f^(=S)$ is a linear operator.
] <thrm_efron_stein>

// Def. Function degree under ES basis (and for multivariate functions).

#definition[
  The #emph[Efron-Stein degree] of a function $f in L2iid$ is
  $ deg_"ES" (f) = max_(S subeq [n] "s.t." f^(=S)!= 0) |S|. $
  If $f=(f_1,dots,f_M): RR^N to RR^M$ is a multivariate function, then the Efron-Stein degree of $f$ is the maximum degree of the $f_i$.
]

Intuitively, the Efron-Stein degree is the maximum size of multiway interactions that $f$ accounts for.

Motivation for "noise operator" - see how function behaves for small change in input parameters.

#definition[
  For $p in [0,1]$, and $x in RR^N$, we say $y in RR^N$ is #emph[$p$-resampled from $x$] if $y$ is chosen as follows: for each $i in [n]$, independently,
  $
    y_i = cases(x_i &"with probability" p, "drawn from" pi #h(2em)&"with probability" 1-p).
  $
  We say $(x,y)$ is a #emph[$p$-resampled pair].
] <def_p_resampled>

Def. noise operator.

#show sym.EE: math.limits

#definition[
  For $p in [0,1]$, the #emph[noise operator] is the linear operator $T_p$ on $L2iid$, defined by, for $y$ $p$-resampled from $x$
  $ T_p f(x) = EE_(y " " p"-resampled from" x)[f(y)] $
  In particular, $inn(f,T_p f) = EE_((x,y)" " p"-resampled") [f(x) dot f(y)]$.
]

#show sym.EE: math.scripts

#lemma[
  Let $p in [0,1]$ and $f in L2iid$ have Efron-Stein decomposition $f=sum_(S subeq [n]) f^(=S)$. Then
  $ T_p f(x) = sum_(S subeq [n]) p^(abs(S))f^(=S). $
] <lem_es_noise_op>
#proof[
  Let $J$ denote a $p$-random subset of $[n]$, i.e. with $J$ formed by including each $i in [n]$ independently with probability $p$.
  By definition, $T_p f(x) = EE_J [f^(subeq J)(x)]$ (i.e. pick a random subset of coordinates to fix, and re-randomize the rest).
  We know by @thrm_efron_stein that $f^(subeq J) = sum_(S subeq J) f^(=S)$, so
  $
    T_p f(x) = EE_J [ sum_(S subeq J) f^(=S) ] = sum_(S subeq [n]) EE_J [I(S subeq J)] dot f^(=S) = sum_(S subeq [n]) p^abs(S) f^(=S),
  $
  since for a fixed $S subeq [n]$, the probability that $S subeq J$ is $p^abs(S)$.
]

Lem. Noise operator formula in E-S decomposition. (Ex. 8.18)

Thrm. Function stability for degree D functions

#theorem[
  Let $p in [0,1]$ and let $f=(f_1,dots,f_M):RR^N arrow RR^M$ be a multivariate function with Efron-Stein degree $D$ and each $f_i in L2iid$.
  Suppose that $(x,y)$ are a $p$-resampled pair under $pi^(times.circle N)$, and $EE norm(f(x))^2 = 1$. Then
  $ EE norm(f(x)-f(y))^2 <= 2(1-p^D) <= 2(1-p)D $ <eq_es_stability>
  /*
  $p in [0,1]$, and $X,Y$ marginally $N$-dimensional standard Normal vectors.
  Suppose that $EE norm(f(X))_2^2 = 1$ and either of the following cases hold:
  #[ #set enum(numbering: "I.")
  + $(X,Y)$ are a $p$-resampled pair, and $f$ is a degree-$D$ function.
  + $(X,Y)$ are $p$-correlated, and $f$ is a degree-$D$ polynomial.
  ]
  Then
  $ EE norm(f(X)- f(Y))_2^2 <= 2(1-p^D). $
  */
] <thrm_es_stability>
#proof[
  Observe that
  $
    EE norm(f(x)-f(y))^2 &= EE norm(f(x))^2 + EE norm(f(y))^2 - 2 EE inn(f(x),f(y)) \ &= 2 - 2(sum_i EE[f_i (x) f_i (y)])
    \ &= 2 - 2(sum_i inn(f_i,T_p f_i)).
  $ <eq_thrm_es_stability_1>
  Here, we have for each $i in [n]$ that
  $
    inn(f_i,T_p f_i) = inn(sum_(S subeq [n]) f_i^(=S), sum_(S subeq [n]) p^abs(S) f_i^(=S))= sum_(S subeq [n]) p^abs(S) norm(f_i^(=S) )^2,
  $
  by @lem_es_noise_op and orthogonality.
  Now, as each $f_i$ has Efron-Stein degree at most $D$, the sum above can be taken only over $S subeq [n]$ with $0 <= abs(S) <= D$, giving the bound
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

== Hermite Polynomials (TODO)

Disclaimer of "this theory is much more classical, see (ref) for details."

Def. Gaussian space

#definition[
  Let $gamma_N$ be the $N$-dimensional standard Normal measure on $RR^N$. Then the #emph[$N$-dimensional Gaussian space] is the space $L2normN$ of $L^2$ functions of $N$ i.i.d. standard Normal random variables.
]

Note that under the usual $L^2$ inner product, $inn(f,g) = EE[f dot g]$, Gaussian space is a separable Hilbert space.

To us, the interesting functions in this space are those given by degree $D$ multivariate polynomials (here "degree" is used in the traditional sense.)

Thrm. monomials form basis of 1D Gaussian space (cite)

It is a well-known fact that the monomials $1,z,z^2,dots$ form a complete basis for $L2norm$ (O'Donnell 11.22).
However, these are far from an orthonormal "Fourier" basis; for instance, we know $EE[z^2]=1$ for $z ~ cal(N)(0,1)$.
By the Gram-Schmidt process, these monomials can be converted into the polynomials $h_j$ for $j>=0$, given as
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


nd thus the collection of $(h_j)_(0 <= j <= k)$

These formulas require knowledge of the moments of a standard Normal random variable, so a more convenient way to derive them is by analyzing the standard Normal moment generating function.
Recall that for $z ~ cal(N)(0,1)$, we have
$
  EE[exp(t z)] = 1 / sqrt(2pi) integral_RR e^(t z - 1 / 2 z^2) dif z = e^(1 / 2 t^2) 1 / sqrt(2pi) integral_RR e^(-1 / 2 (z-t)^2) dif z = exp(1/2 t^2).
$

// skip this stuff

#theorem([O'Donnell, meow])[
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



Def. noise operator/Ornstein-Uhlenbeck operator

Compute effect of noise operator on Hermite polys

Thrm. Hermite polys form basis for 1D Gaussian space

Thrm. Products of Hermite polys form basis for N-dim Gaussian space

Noise operator on arbitrary function with given Hermite expansion

#definition[
  Let $(g,g')$ be $N$-dimensional standard Normal vectors. We say $(g,g')$ are #emph[$p$-correlated] if $(g_i,g'_i)$ are $p$-correlated for each $i in [n]$, and these pairs are mutually independent.
]

In a similar way to the Efron-Stein case, we can consider the resulting "noise operator," as a way of measuring a the effect on a function of a small change in the input.

#show sym.EE: math.limits

#definition[
  For $p in [0,1]$, the #emph[Gaussian noise operator] $T_p$ is the linear operator on $L2normN$, given by
  $
    T_p f(x) = EE_(y " " p"-correlated to" x)[f(y)] = EE_(y tilde stdnorm )[ f(p x + sqrt(1-p^2) y)]
  $
]

#show sym.EE: math.scripts

In particular, a straightforward computation with the Normal moment generating function gives

Remark that degree D function can be expressed in terms of degree D and lower Hermite polynomials - gives a Hilbert basis which reflects the natural algebraic grading.

Thrm. Function stability for degree D polynomials.

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





// TODO
// #definition[Degree.]

// $pi$ any distribution with


// == Efron-Stein Decomposition

// O'Donnell 8.28




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


== Algorithms

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

