#import "environments.typ": *

#import "symbols.typ": *

= Introduction

Let $g_1,dots,g_N$ be $N$ real numbers.
The #emph[number partitioning problem (NPP)] asks: what is the subset $A$ of $[N]:={1,2,dots,N}$ such that the sum of the $g_i$ for $i in A$ and the sum of the remaining $g_i$ are as close as possible?
More formally, the $A$ we want to find is the one minimizing the discrepancy
$ abs(sum_(i in A) g_i - sum_(i in.not A) g_i). $

When rephrased as a decision problem (i.e., whether there in an $A$ such that the discrepancy is below a certain threshold, or even zero), the NPP is one of the six basic NP-complete problems of Garey and Johnson, and of those, the only one to deal with numbers @gareyComputersIntractabilityGuide1979[#sym.section 3.1].

(talk about modifications and variants?)

The number partitioning problem can be rephrased in the following way.
Let our instance $g_1,dots,g_N$ be identified with a point $g in RR^N$.
Then, a choice of $A subset.eq [N]$ is equivalent to choosing a point $x$ in the $N$-dimensional binary hypercube $Sigma_N := {plus.minus 1}^N$, and the discrepancy of $x$ is now $abs(inn(g,x))$.
The goal is now to find the $x$ minimizing this discrepancy:
$ min_(x in Sigma_N) abs(inn(g,x)). $

#definition[
  Let $x in Sigma_N$. The #emph[energy] of $x$ (with respect to the instance $g$) is
  $
    E(x;g) := - log_2 abs(inn(g,x)).
  $
  The #emph[solution set $S(E;g)$] is the set of all $x in Sigma_N$ that have energy at least $E$, i.e. that satisfy
  $
    abs(inn(g,x)) <= 2^(-E).
  $ <eq_npp>
] <def_npp_statement>

- This terminology is motivated by the statistical physics literature, wherein random optimiztation problems are often reframed as energy maximization over a random landscape @mertensPhysicistsApproachNumber2001.
- Observe that minimizing the discrepancy $abs(inn(g,x))$ corresponds to maximizing the energy $E$.

Overview of number partitioning problem.

Application: randomized control trials.

Other applications.
- Circuit design, etc.

Two questions of interest:
+ What is optimal solution.
+ How to find optimal solution.



== Physical Interpretations

== Statistical-to-Computational Gap


Low degree heuristic: degree $D$ algorithms are a proxy for the class of $e^(tilde(O)(D))$-time algorithms.


== Existing Results

+ $X_i,1<=i<=n$ i.i.d. uniform from ${1,2,...,M:=2^m}$, with $kappa := m/n$, then phase transition going from $kappa<1$ to $kappa>1$.
+ Average case, $X_i$ i.i.d. standard Normal.
+ Karmarkar [KKLO86] - NPP value is $Theta(sqrt(N)2^(-N))$ whp as $N to infinity$ (doesn't need Normality).
+ Best polynomial-time algorithm: Karmarkar-Karp [KK82] - Discrepancy $O(N^(-alpha log N))=2^(-Theta (log^2 N))$ whp as $N to infinity$
+ PDM (paired differencing) heuristic - fails for i.i.d. uniform inputs with objective $Theta(n^(-1))$ (Lueker).
+ LDM (largest differencing) heuristic - works for i.i.d. Uniforms, with $n^(-Theta(log n))$ (Yakir, with constant $alpha=1/(2ln 2)$ calculated non-rigorously by Boettcher and Mertens).
+ Krieger - $O(n^(-2))$ for balanced partition.
+ Hoberg [HHRY17] - computational hardness for worst-case discrepancy, as poly-time oracle that can get discrepancy to within $O(2^sqrt(n))$ would be oracle for Minkowski problem.
+ Gamarnik-Kizildag: Information-theoretic guarantee $E_n=n$, best computational guarantee $E_n = Theta(log^2 n)$.
+ Existence of $m$-OGP for $m=O(1)$ and $E_n=Theta(n)$.
+ Absence for $omega(1) <= E_n=o(n)$
+ Existence for $omega(sqrt(n log_2 n)) <= E_n <= o(n)$ for $m=omega_n(1)$ (with changing $eta,beta$)
  + While OGP not ruled out for $E_n <= omega(sqrt(n log_2 n))$, argued that it is tight.
+ For $epsilon in (0,1/5)$, no stable algorithm can solve $omega(n log^(-1/5 + epsilon) n) <= E_n <= o(n)$
+ Possible to strengthen to $E_n=Theta(n)$ (as $2^(-Theta(n)) <= 2^(-o(n))$)

== Our Results <subsection_intro_results>

== Notation and Conventions

Conventions:
+ On $RR^N$ we write $norm(dot)_2 = norm(dot)$ for the Euclidean norm, and $norm(dot)_1$ for the $ell^1$ norm.
// + $log$ means $log$ in base 2, $exp$ is $exp$ base 2 - natural log/exponent is $ln$/$e^x$.
+ If $x in RR^N$ and $S subeq [N]$, then $x_S$ is vector with
  $ (x_S)_i = cases(x_i #h(2em) &i in S\,, 0 &"else.") $
  In particular, for $x,y in RR^N$,
  $ inn(x_S, y) = inn(x,y_S) = inn(x_S,y_S). $
+ $B(x,r) = { y in RR^N : norm(y-x) < r}$ is $ell^2$ unit ball.

Throughout we will make key use of the following lemma:

#lemma[Normal Small-Probability Estimate][
  Let $E,sigma^2 > 0$, and $mu,Z$ be random variables with $Z | mu ~ Normal(mu,sigma^2)$.
  for $sigma^2$ a constant. Then
  $
    PP(abs(Z) <= 2^(-E) | mu) <= exp_2(-E - 1 / 2 log_2(sigma^2) + O(1)).
  $ <eq_normal_smallprob>
] <lem_normal_smallprob>
#proof[
  Observe that conditional on $mu$, the distribution of $Z$ is bounded as
  $
    phi_(Z|mu) (z) <= 1 / sqrt(2 pi sigma^2) e^(-(z-mu)^2 / (2 sigma^2)) <= (2 pi sigma^2)^(-1 slash 2).
  $
  Integrating over $abs(z)<= 2^(-E)$ then gives @eq_normal_smallprob, via
  $
    PP(abs(Z) <= 2^(-E)) = integral_(abs(z) <= 2^(-E)) (2 pi sigma^2)^(-1 slash 2) dif z <= 2^(-E - 1 / 2 log_2(2 pi sigma^2) + 1). #qedhere
  $
]

#lemma[
  Suppose that $K <= N slash 2$, and let $h(x)=-x log(x) - (1-x) log(x)$ be the binary entropy function. Then, for $p := K slash N$,
  $ sum_(k <= K) binom(N,k) <= exp(N h(p)) <= exp(2 N p log(1/p)). $
  // https://mathoverflow.net/questions/473730/bounding-a-binomial-coefficient-using-the-binary-entropy-function#mjx-eqn-20
] <lem_chernoff_hoeffding>
#proof[
  Consider a $Bin(N,p)$ random variable $S$. Summing its PMF from $0$ to $K$, we have
  $
    1 >= PP(S <= K) = sum_(k <= K) binom(N,k) p^k (1-p)^(N-k) >= sum_(k<= K) binom(N,k) p^K (1-p)^(N-K).
  $
  Here, the last inequality follows from the fact that $p <= (1-p)$, and we multiply each term by $(p/(1-p))^(K-k)<1$.
  Now rearrange to get
  $
    sum_(k <= K) binom(N,k) &<= p^(-K) (1-p)^(-(N-K)) \ &= exp(-K log(p) - (N-K) log(1-p)) \
    &= exp(N dot (-K/N log(p) - ((N-K)/N) log(1-p))) \
    &= exp(N dot (-p log(p) - (1-p) log (1-p)) ) = exp(N h(p)).
  $
  The final equality then follows from the bound $h(p) <= 2 p log(1 slash p)$ for $p <= 1 slash 2$.
]


Note that this is decreasing function of $sigma^2$, e.g. it's bounded by $exp_2(-E - 1/2 log_2( min sigma^2))$ (this bound is trivial unless $sigma^2 => gamma > 0$).

=== Glossary:
+ "instance"/"disorder" - $g$, instance of the NPP problem
+ "discrepancy" - for a given $g$, value of $min _(x in Sigma_N) abs(inn(g,x))$
+ "energy" - negative exponent of discrepancy, i.e. if discrepancy is $2^(-E)$, then energy is $E$. Lower energy indicates "worse" discrepancy.
+ "near-ground state"/"approximate solution"

