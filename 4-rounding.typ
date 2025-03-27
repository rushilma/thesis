#import "environments.typ": *

#import "symbols.typ": *

= Extending to Rounded Algorithms <section_rounding>

== Solutions repel

Claim: no two adjacent points on $Sigma_N$ (or pairs within $k=O(1)$ distance) which are both good solutions to the same problem.
The reason is that this would require a subset of $k$ signed coordinates $± g_{i_1},...,± g_{i_k}$ to have small sum, and there are only $2^k binom{N}{k}\leq O(N^k)$ possibilities, each of which is centered Gaussian with variance at least $1$, so the smallest is typically of order $Omega(N^{-k})$.

#proposition[
  Fix distinct points $x,x' in Sigma_N$ and let $g ~ stdnorm$ be any instance.
  // with $norm(x - x')<= 2sqrt(k)$ (i.e. $x,x'$ differ by $k$ sign flips), and let $g$ be any instance.
  Then,
  $
    PP(x, x' in Soln(g)) <= exp(-E + O(1)).
  $
] <prop_fixed_close_solns_lowprob>
#proof[
  For $x != x'$, let $J subeq [N]$ denote the subset of coordinates in which $x,x'$ differ, i.e. $x_J != x'_J$.
  // by assumption, $abs(J) <= k$.
  In particular, we can write
  $ x = x_([N] without J) + x_J, #h(5em) x' = x_([N] without J) - x_J. $
  Thus, for a fixed pair $(x,x')$, if $-2^(-E) <= inn(g,x), inn(g,x') <= 2^(-E)$,
  we can expand this into
  $
    -2^(-E) <= &inn(g,x_([N] without J)) + inn(g,x_J) <= 2^(-E), \
    -2^(-E) <= &inn(g,x_([N] without J)) - inn(g,x_J) <= 2^(-E).
  $
  Multiplying the lower equation by $-1$ and adding the resulting inequalities gives $abs(inn(g,x_J)) <= 2^(-E)$.
  Note that $inn(g,x_J)~Normal(0,abs(J))$ (and is nondegenerate, as $abs(J)>0$). By @lem_normal_smallprob and the following remark, it follows that
  $
    PP(x,x' in Soln(g)) <= PP(abs(inn(g,x_J)) <= 2^(-E)) <= exp(-E + O(1)). #qedhere
  $
]

#theorem[Solutions Can't Be Close][
  Consider any distances $k = Omega(1)$ and energy levels $E >> k log_2  N$.
  Then for any instance $g$, there are no pairs of distinct solutions $x,x' in Soln(g)$ with $norm(x-x') <= 2 sqrt(k)$ (i.e. within $k$ coordinate flips of each other) with high probability.
] <thrm_solutions_repel>
#proof[
  Observe that by @prop_fixed_close_solns_lowprob, finding a pair of distinct solutions within distance $2 sqrt(k)$ implies finding some subset of at most $k$ coordinates $J subset[N]$ of $g$ and $abs(J)$ signs $x_J$ such that $abs(inn(g_J,x_J))$ is small.
  For any $g$, there are at most $2^k$ choices of signs and, by @vershyninHighDimensionalProbabilityIntroduction2018[Exer. 0.0.5], there are
  $
    sum_(1 <= k' <= k)binom(N,k') <= ((e N) / k)^k <= (e N)^k = 2^(O(k log_2 N))
  $
  choices of such subsets.
  Union bounding @prop_fixed_close_solns_lowprob over these $exp_2 O(k log_2 N)$ choices, we get
  $
    PP multiprob(
      exists x\,x' "s.t.",
      (upright(a))  &norm(x-x') <= 2sqrt(k)\,,
      (upright(b)) #h(0.3em) &x\,x' in Soln(g)
    ) <= PP multiprob(
      exists J subset [N]\, x_J in {plus.minus 1}^abs(J) "s.t.",
      (upright(a)) &abs(J) <= k\,,
      (upright(b)) &abs(inn(g_J,x_J)) <= exp(-E))
    <= exp(-E + O(k log_2  N)) = o(1).
  $ <eq_solutions_repel>
  Note that the last equality holds as $E >> k log_2 N$.
]

== Proof of Hardness for Close Algorithms

Fix some $k=O(1)$. Let the event that the $RR^N$-valued $alg$ succeeds on a random instance $g$ be
$
  S_"close" = multiset(
    exists hat(x) in S(E;g) "s.t.",
    alg(g) in B_(L^1)(hat(x), k)
  )
$
That is, we ask that $alg$ output a point which is $O(1)$-close to a solution in $L^1$. For $k$ fixed in advance, this implies we can convert $alg$ into a $Sigma_N$-valued algorithm by computing the energy of the $O(1)$ corners near the output of $alg(g)$ and minimizing over this set, which only takes $O(N)$ additional operations.

=== Solve case - rounding might help us

For this section, let $alg$ be an $RR^N$-valued algorithm with coordinate degree $D$. For a constant $k$ fixed in advance, we can consider the partially-defined algorithm $hat(alg)_k$ given by
$
  hat(alg)_k (g) := limits("argmin")_(x' in Sigma_N \ norm(x'-alg(g)) <= 2sqrt(k)) abs(inn(g,x'))
$ <eq_hat_alg>
Observe that $S_"close"$, as defined above, implies that $hat(alg)_k$ finds a solution for $g$.

Let $g,g'$ be $(1-epsilon)$-resampled standard Normal vectors. Define the following events:
$
  S_"diff" &= { g != g'} \
  S_"solve" &= { hat(alg)_k (g) in Soln(g), hat(alg)_k (g') in Soln(g')} \
  S_"stable" &= { norm(alg(g) - alg(g')) <= 2 sqrt(eta N) } \
  S_"cond" (x) &= multiset(
    exists.not x' in Soln(g') "such that",
    norm(x-x') <= 2sqrt(eta N),
  )
$ <eq_es_events>

We can consider the partially defined algorithm $hat(alg)$ which, given an instance $g$ such that $S_"close"$ holds, sets $hat(alg)(g) := hat(x) in S(E;g)$ to be the (unique) nearby good solution.
This function is
is unique as our process for choosing $hat(x)$ implies taking the one which maximizes energy, and two solutions have the same energy with low probability.

Stability analysis:
for $g,g'$ being $(1-epsilon)$-resampled/correlated, it still holds that, conditional on $hat(alg)(g)$ and $hat(alg)(g')$ being defined, then
$
  EE norm(hat(alg(g)) - hat(alg(g')))^2 <= EE 2norm(hat(alg(g)) - alg(g))^2 + EE norm(alg(g) - alg(g'))^2 <= 2 O(1)^2 + 2 C epsilon D N + O(1)
$

Thus,
$
  p_"unstable" = PP(norm(hat(alg)(g) - hat(alg)(g')) >= 2 sqrt(eta N)) <= (C epsilon D) / 4 + O(1) / (eta N)
$


== No solve case -- rounding is truly random.

$inn(g,x) ~ Normal(0,N)$
$
  PP(abs(inn(g,x)) <= 2^(-E)) <= 2^(-E+1) / sqrt(2 pi N) = exp(-E - 1/2 log_2 (N) + O(1))
$
Follows by @lem_normal_smallprob.
i.e., for $E >> log_2  N$, any fixed $x$ is not solution to random instance whp.
By conditioning, this implies that if $x$ is random and independent from $g$, then it's a solution with $o(1)$ probability.
Thus, if you truly had a random point, then it's almost certainly not a solution; that is, if your randomized rounding destroys your algorithms output, then whp you fail to find a solution.

Note: we should assume $log_2 ^2 N << E <= N$.
Also, getting algorithms for polynomial discrepancy ($n^-1$, etc.) is basically trivial.

Let $x := alg(g)$.
We write $x^*$ for the coordinate-wise signs of $x$, i.e.
$ x^*_i := cases(+1 #h(1em) &x_i > 0\,, -1 &x_i <= 0.) $

Let $round(x,omega):RR^N times Omega to Sigma_N$ denote any randomized rounding function, with randomness $omega$ independent of the input.
We will often suppress the $omega$ in the notation, and treat $round(x)$ as a $Sigma_N$-valued random variable.

#remark[
  Meow $alg^*$ fails and is still degree $D$ lcdf, even if it stops being a polynomial. Bounds on $D$ worsen, but only to what you'd expect.
]

Given such a randomized rounding function, we can describe it in the following way.
Let $p_1,dots,p_N$ be the probabilities of $round(x)_i != (x^*)_i$.
We assume without loss of generality that each $p_i <= 1/2$.

#lemma[
  Draw $N$ coin flips $I_i ~ Bern(2p_i)$ and N$N$_N_ signs $S_i ~ "Unif"{plus.minus 1}$, all mutually independent, and define the random variable $tilde(x) in Sigma_N$ by
  $ tilde(x)_i := S_i I_i + (1-I_i) x^*_i. $
  Then $tilde(x) ~ round(x)$.
] <lem_random_rounding_altdef>
#proof[
  Conditioning on $I_i$, we can check that
  $
    PP(tilde(x)_i != x_i) &= 2 p_i dot PP(tilde(x)_i = x_i | I_i = 1) + (1-2p_i ) dot PP(tilde(x)_i != x_i | I_i = 0) \
    &= 2 p_i dot 1 / 2 + 0 = p_i.
  $
  Thus, $tilde(x)$ has the same probability of equalling $x^*$ in each coordinate as $round(x)$ does, as claimed.
]

By @lem_random_rounding_altdef, we can redefine $round(x)$ to be $tilde(x)$ as constructed without loss of generality.

// What is tilde(x)?

By @lem_random_rounding_altdef, it makes sense to define $tilde(alg)(g) := round(alg(g))$, which is now (a) $Sigma_N$-valued and (b) randomized only in the transition from $RR^N$ to $Sigma_N$ (i.e., the rounding doesn't depend directly on $g$, only the output $x = alg(g)$).


TODO: explain why we want to consider $tilde(alg)(g) = round(alg(g))$
#definition[
  Given $alg$, we can define two $Sigma_N$-valued algorithms. Let $x := alg(g)$. Then
  $
    alg^*(g)_i := 2 I(x_i > 0) - 1 #h(2em)"and"#h(2em) tilde(alg)(g) =: sans("round")(alg(g)).
  $
]

Note that if $alg$ has coordinate degree $D$, then $alg^*$ also has coordinate degree $D$. As a deterministic $Sigma_N$-valued algorithm, strong low degree hardness as proved in the previous section applies.

However, we still want to show that $tilde(x) := tilde(alg)(g)$ fails to solve $g$ with high probability.
Intuitively, the landscape of solutions is so fractured that any rounding procedure which produces results different from $x^*$ will effectively be selecting a random point, and because any fixed point has such a low probability of being a solution, hardness still follows.

#lemma[
  Suppose $p_1,dots,p_N$ are the probabilities of $tilde(x)$ and $x^*$ differing in each coordinate.
  // Assume $p_i <= 1 slash 2$
  Assume $sum_i p_i = omega(1)$.
  Then $tilde(x) != x^*$ with high probability.
] <lem_rounding_changes_soln>
#proof[
  Observe that as each coordinate is rounded independently, we can compute
  $
    PP(tilde(x) = x^*) = product_i (1-p_i) = exp(sum_i log_2 (1-p_i)) <= exp(- sum_i p_i).
  $
  For $sum_i p_i = omega(1)$, we get $PP(tilde(x)=x^*) <= e^(-omega(1)) = o(1)$, as claimed.
]



- Flip coin with prob $2p_i$
- If heads, randomize $tilde(x)$ with probability $1/2$; if tails keep coord.
- Then,
  $ PP(tilde(x)_i = x^*_i) = 2p_i * 1 / 2 + (1-2p_i) * 0 = p_i. $

Let $K$ be a large constant, and let $S subeq [N]$ denote the coordinates of the first $K$ coordinates to be randomized.
Then, we can condition on $x_([N] without S)$, given which $tilde(x)$ is a uniformly random point within a $K$-dimensional subcube of $Sigma_N$.
By @thrm_solutions_repel, at most one of these points is in $S(E;g)$, so the probability of $tilde(x)$ being a solution is at most $2^(-K)$.


$
  PP(abs(inn(g,tilde(x))) <= 2^(-E) | g, x_([N] without S)) <= exp_2 (-E - 1 / 2 log_2 abs(S) + O(1)).
$

First, assume $attach(S_"solve", tl: not)$. In that case, $x:=alg(g)$ is far from any solution, and randomized rounding fails with high probability.
That is, $PP(tilde(x) in S(E;g)) = o(1)$

To see this, let $x^*$ be the point on $Sigma_N$ closest to $x$ (in principle, this is the vector which is coordinatewise $plus.minus 1$ depending on whether each coordinate of $x$ is positive or negative).

Let $p_1,dots,p_N$ be the probability of $tilde(x)$ disagreeing with $x_*$ on each coordinate.
- Require that no $p_i = 0$ (i.e. all coordinates have a chance to disagree)
- Then, for $x in [0,1)$, exists universal constant $C$ such that $-log (1-x) <= C x$.
- Probability that $tilde(x)=x_*$ is
  $ product (1-p_i) = exp( sum log(1-p_i) ) <= exp(- C sum p_i). $
- If we assume that randomized rounding changes solution, then that requires this probability to go to zero, i.e. $sum p_i = omega(1)$.

In this case, consider following construction. For each $1 <= i <= N$, flip an independent coin $H_i$ which lands heads with probability $2 p_i$, and keep all the heads.
- By Second Borel-Cantelli lemma, $E_i = { H_i "heads"}$, the $E_i$ are independent, and $ sum_( i>= 0 ) PP(E_i) = sum 2 p_i = infinity, $ so $PP(limsup E_i) = 1$, i.e., get heads infinitely often.
- That is, number of heads is $omega(1)$.
- For every coin with a head, round $x^*$ by changing coord with probability $1/2$; if tails keep coord.
- That is, randomized rounding done by choosing random set of $omega(1)$ coordinates and resampling them as iid Uniform in ${-1,1}$.

Because number of coordinates being changed is $omega(1)$, can pick large constant $K$ such that whp there are at least $K$ coordinates being changed.
- Only randomize first $K$ heads, condition on the others. Thus, $tilde(x)$ has $K$ i.i.d., random coordinates.
- $tilde(x)$ is random point in $K$-dimensional subcube, but by @prop_fixed_close_solns_lowprob, only one out of the $2^K$ such points is a good solution.

Thus, probability for rounding to give a good solution is
$$


- Randomized rounding in artificially difficult way. (I.e. this multistage procedure accomplishes the same thing as randomized rounding.)
- Now, randomized rounding is done by choosing a random set of $omega(1)$ coordinates, and making those iid Uniform in ${-1,1}$.
- Pick a large constant (e.g. 100), and only randomize the first 100 heads, and condition on the others (i.e. choose the others arbitrarily). Note that since $100 >= omega(1)$, there are at least 100 heads whp.
- Now rounded point is random point in 100 dimensional subcube, but at most one of them is a good solution by the claim at the top of the page.
- Combining, the probability for rounding to give a good solution is at most $o(1) + 2^{-100}$. Since $100$ is arbitrary, this is $o(1)$ by sending parameters to $0$ and/or infinity in the right order.

Let $tilde(x)$ be the point on $Sigma_N$ after randomized rounding.

Moreover, let $tilde(x)$ be the point

consider the case where

What could go wrong? It could be that all deterministic $Sigma_N$ algorithms fail, but an algorithm which is allowed to output a continuous point and then round it (potentially in a randomized way) could succeed.
Such an algorithm would have to do more than just deterministically round, because

Let $p_"solve"$ be probability that $alg$ outputs a point $x$ which is $k$ close in $L^1$ to a vertex and a good solution $x^*$ exists in nbhd of that corner.
Because solutions repel, such $x^*$ is unique, so only hope is that $x$ gets rounded to $x^*$ with reasonable probability.


(Weaker than traditional solution case).

Then, either $tilde(alg)$ finds this good solution with reasonable probability, or

Argument:
- Algorithm $alg$ which is deterministic $RR^N -> RR^N$. Suppose $tilde(A): RR^N -> Sigma^N$ is $alg$ passed through any nontrivial rounding procedure.
- Say $alg(g) = x$. Let $x^* in Sigma_N$ be closest point to $x$, and $tilde(x)=tilde(A)(g)$ be the rounding of $x$.
- If $x^* = tilde(x)$, we're done.
- Else, we know that only one of $x^*$ and $tilde(g)$ are a good solution, by @thrm_solutions_repel. It's $x^*$ with probability $p_"solve"$.
  - Here, we're assuming randomized rounding changes at most some $O(1)$ amount of coordinates.
-

Thus, rounding would destroy the solution.


