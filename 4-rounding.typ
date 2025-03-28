#import "environments.typ": *

#import "symbols.typ": *

#pagebreak()

#show math.equation: set text(font: "New Computer Modern Math")

= Extensions to Real-Valued Algorithms <section_rounding>

#show math.equation: set text(font: "STIX Two Math")

With @section_hardness, we have established strong low degree hardness for both low degree polynomial algorithms and low coordinate degree algorithms.
However, our stability analysis assumed that the algorithms in question were $Sigma_N$-valued.
In this section, we show that this assumption is not in fact as restrictive as it might appear.

Throughout, let $alg$ denote an $RR^N$-valued algorithm.
We want to show that
#enum(
  numbering: "I.",
  indent: 1.2em,
  [No low degree $alg$ can reliably output points _close_ -- within constant distance -- to a solution,],
  [No $Sigma_N$-valued algorithm $tilde(alg)$ coming from randomly rounding the output of $alg$, which changes an $omega(1)$ number of coordinates, can find a solution with nonvanishing probability.],
)
In principle, the first possibility fails via the same analysis as in @section_hardness, while the second fails because because the landscape of solutions to any given NPP instance is sparse.

Why are these the only two possibilities? For $alg$ to provide a way to actually solve the NPP, we must be able to turn its outputs on $RR^N$ into points on $Sigma_N$. If $alg$ could output points within an constant distance (independent of the instance) of a solution, then we could convert $alg$ into a $Sigma_N$-valued algorithm by manually computing the energy of all points close to its output and returning the energy-maximizing point.

However, the more common way to convert a $RR^N$-valued algorithm into a $Sigma_N$-valued one is by rounding the outputs, as in @huangStrongLowDegree2025.
Doing this directly can lead to difficulties in performing the stability analysis.
In our case, though, if we know no $alg$ can reliably output points within constant distance of a solution, then any rounding scheme which only flips $O(1)$ many coordinates will assuredly fail.
Thus, the only rounding schemes worth considering are those which flip $omega(1)$ many coordinates.

We first describe a landscape obstruction to finding multiple solutions at the same energy level for a random NPP instance. Then, we show hardness in both of the aforementioned cases. meow.

== Solutions repel meow

Introduce section meow.

No two adjacent points on $Sigma_N$ (or pairs within $k=O(1)$ distance) which are both good solutions to the same problem.
// The reason is that this would require a subset of $k$ signed coordinates $± g_{i_1},...,± g_{i_k}$ to have small sum, and there are only $2^k binom{N}{k}\leq O(N^k)$ possibilities, each of which is centered Gaussian with variance at least $1$, so the smallest is typically of order $Omega(N^{-k})$.

#proposition[
  Fix distinct points $x,x' in Sigma_N$ and let $g ~ stdnorm$ be a random instance.
  // with $norm(x - x')<= 2sqrt(k)$ (i.e. $x,x'$ differ by $k$ sign flips), and let $g$ be any instance.
  Then,
  $
    PP(x, x' in Soln(g)) <= exp_2 (-E + O(1)) = exp2(-E + O(1)).
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
    PP(x,x' in Soln(g)) <= PP(abs(inn(g,x_J)) <= 2^(-E)) <= exp_2 (-E + O(1)). #qedhere
  $
]

Remarks on theorem below meow.

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
      (upright(b)) &abs(inn(g_J,x_J)) <= exp_2 (-E))
    <= exp_2 (-E + O(k log_2 N)) = o(1).
  $ <eq_solutions_repel>
  Note that the last equality holds as $E >> k log_2 N$.
]

== Proof of Hardness for Close Algorithms



Throughout this section, fix some distance $r=O(1)$.
Consider the event that the $RR^N$-valued $alg$ outputs a point close to a solution for an instance $g$:
$
  S_"close" (r) = multiset(
    exists hat(x) in S(E;g) "s.t.",
    alg(g) in B(hat(x), r)
  ) = {B(alg(g), r) inter S(E;g) != emptyset }
$

Note that as $r$ is fixed (potentially depending on $alg$, but independent of $N$ or $g$), we can convert $alg$ into a $Sigma_N$-valued algorithm by considering the corners of $Sigma_N$ within constant distance of $alg(g)$.

// definition of hat alg

#definition[
  Let $r>0$ and $alg$ be an $RR^N$-valued algorithm. Define $hat(alg)_r$ to be the $Sigma_N$-valued algorithm defined by
  $
    hat(alg)_r (g) := limits("argmin")_(x' in B(alg(g),r) inter Sigma_N) abs(inn(g,x')).
  $ <eq_hat_alg>
  If $B(alg(g),r) inter Sigma_N = emptyset$, then set $hat(alg)_r (g) := (1 slash g_1,0,dots)$, which always has energy 0.
] <def_hat_alg>

Observe that $S_"close"(r)$ occuring is the same as $hat(alg)_r$ finding a solution for $g$.
In addition, note that practically speaking, computing $hat(alg)_r$ requires additionally computing the energy of $O(1)$-many points on $Sigma_N$.
This requires an additional $O(N)$ operations.

Recall from @section_algorithm_stability that if $alg$ is low degree (or low coordinate degree) then we can derive useful stability bounds for its outputs. Luckily, this modification $hat(alg)_r$ of $alg$ also are stable, with slightly modified bounds.

// hat alg is still stable

#lemma[
  Suppose that $EE norm(alg(g))^2 <= C N$ and that $alg$ has degree $<= D$ (resp. coordinate degree $<= D$), and let $(g,g')$ be $(1-epsilon)$-correlated (resp. $(1-epsilon)$-resampled).
  Then $hat(alg)_r$ as defined above has
  $
    EE norm(hat(alg)_r (g) - hat(alg)_r (g'))^2 <= 6C D epsilon N + 6 r^2.
  $
  In particular, we have
  $
    PP (norm(hat(alg)_r (g) - hat(alg)_r (g')) >= 2 sqrt(eta N)) <= (3 C D epsilon) / (2 eta) + (3 r^2) / (2 eta N).
  $
  <eq_hat_alg_stability>
] <lem_hat_alg_stability>
#proof[
  Observe by the triangle inequality, as per @eq_squared_triangle_ineq, that
  $
    norm(hat(alg)_r (g) - hat(alg)_r (g'))^2 <=
    3( norm(hat(alg)_r (g) - alg(g))^2 +
      norm(alg(g) - alg(g'))^2 +
      norm(alg(g') - hat(alg)_r (g'))^2 ).
  $
  By @prop_alg_stability, we know $EE norm(alg(g)-alg(g'))^2 <= 6 C D epsilon N$.
  Moreover, we know that $norm(hat(alg)_r (g) - alg(g)) <= r$ by definition, so the remaining terms can be bounded by $3r^2$ each deterministically. Finally, @eq_hat_alg follows from Markov's inequality.
]

Of course, computing $hat(alg)_r$ is certainly never polynomial, and does not preserve any low coordinate degree assumptions in a controllable way.
Thus, we cannot directly hope for @thrm_sldh_poly_linear, @thrm_sldh_poly_sublinear, @thrm_sldh_lcd_linear, or @thrm_sldh_lcd_sublinear to hold.
Meow

// lcd hat alg is still hard

We show for $alg$ being a $RR^N$-valued, low coordinate degree algorithm and any $r=O(1)$, low degree hardness still holds for $hat(alg)_r$.
Note that by a similar argument, we can show hardness in the case that $alg$ is a low degree polynomial algorithm, but we omit the proof meow.

We recall the setup from @section_hardness_lcd.
Let $g,g'$ be $(1-epsilon)$-resampled standard Normal vectors.
Define the following events:
$
  S_"diff" &= { g != g'} \
  S_"solve" &= { hat(alg)_r (g) in Soln(g), hat(alg)_r (g') in Soln(g')} \
  S_"stable" &= { norm(hat(alg)_r (g) - hat(alg)_r (g')) <= 2 sqrt(eta N) } \
  S_"cond" (x) &= multiset(
    exists.not x' in Soln(g') "such that",
    norm(x-x') <= 2sqrt(eta N),
  )
$ <eq_lcd_hat_events>

These are the same events as in @eq_lcd_events, just adapted to $hat(alg)_r$. In particular, @lem_lcd_solve_disjoint holds unchanged.

Moreover, we can define
$
  p_"solve" = PP(hat(alg)_r (g) in Soln(g)) = PP(S_"close" (r)),
$ <eq_def_lcd_hat_psolve>
as well as
$
  p_"unstable" = 1 - PP(S_"stable" | S_"diff"), #h(5em)  p_"cond" (x) = 1 - PP(S_"cond" (x) | S_"diff"),
$
along with $p_"cond" := max_(x in Sigma_N) p_"cond" (x)$, echoing @eq_def_lcd_punstablecond.

Observe that as $p_"cond"$ makes no reference to any algorithm, the bound in @prop_resampled_fundamental holds without change. Moreover, @lem_hat_alg_stability lets us control $p_"unstable"$. The final piece needed is an appropriate analog of @lem_resampled_solve_prob.

#lemma[
  For $g,g'$ being $(1-epsilon)$-resampled, we have
  $
    PP(S_"solve") = PP(hat(alg)_r (g) in Soln(g), hat(alg)_r (g') in Soln(g')) >= p_"solve"^2
  $
] <lem_hat_resampled_solve_prob>
#proof[
  Observe that, letting $+$ denote Minkowski sum, we have that
  $ { hat(alg)_r (g) in Soln(g) } = { alg(g) in Soln(g) + B(0,r) }. $
  Expanding $Soln(g)$, the proof concludes as in @lem_resampled_solve_prob.
]

#set math.cases(gap: 0% + 0.4em)

#theorem[
  Let $omega((log_2 N)^2) <= E <= Theta(N)$, and let $g,g'$ be $(1-epsilon)$-resampled standard Normal r.v.s.
  Consider any $r=O(1)$ and $RR^N$-valued $alg$ with $EE norm(alg(g))^2 <= C N$, and assume in addition that
  #enum(
    numbering: "(a)",
    indent: 1.2em,
    [if $E = delta N = Theta(N)$ for $delta > 0$, then $alg$ has coordinate degree $D <= o(N)$;],
    [if $(log_2 N)^2 << E << N$, then $alg$ has coordinate degree $D <= o(E slash (log_2 N)^2)$.],
  )
  Let $hat(alg)_r$ be defined as in @def_hat_alg. Then there exist $epsilon, eta > 0$ such that
  $ p_"solve" = PP(hat(alg)_r (g) in Soln(g)) = o(1). $
] <thrm_sldh_hat_lcd>
#proof[
  First, by @lem_lcd_solve_disjoint, the appropriate adjustment of @eq_lcd_fundamental holds, namely that
  $
    p_"solve"^2 <= PP(S_"diff") dot (p_"unstable" + p_"cond").
  $ <eq_hat_lcd_fundamental>
  To ensure $PP(S_"diff") approx 1$, we begin by following @eq_def_lcd_epsilon and choosing $epsilon = log_2 (N slash D) slash N$. Moreover, following the proof of @thrm_sldh_lcd_linear and @thrm_sldh_lcd_sublinear, we know that choosing
  $
    eta = cases(
      O(1) "s.t." 2 eta log_2(1 slash eta) < delta slash 4 #h(1em) &E = delta N\,,
      E / (16 N log_2  (N slash E)) #h(1em) &E = o(N),
    )
  $
  in conjunction with @prop_resampled_fundamental, guarantees that
  $
    p_"cond" <= exp_2 (- (3 E) / 4 + O(1)) = o(1).
  $
  Finally, note that in the linear case, when $eta = O(1)$, $r^2/(eta N) = o(1)$ trivially. In the sublinear case, for $eta= E slash (16 N log_2 (N slash E))$, we instead get
  $ eta N = E / (16 log_2 (N slash E)) >= E / (16 log_2 N) = omega(1), $
  as $E >> (log_2 N)^2$.
  Thus, applying the properly modified @lem_hat_alg_stability with these choices of $epsilon,eta$, we see that $p_"unstable" = o(1)$.
  By @eq_hat_lcd_fundamental, we conclude that $p_"solve" = o(1)$, as desired.
]

Talk about implications meow.

== No solve case -- rounding is truly random.

$inn(g,x) ~ Normal(0,N)$
$
  PP(abs(inn(g,x)) <= 2^(-E)) <= 2^(-E+1) / sqrt(2 pi N) = exp_2 (-E - 1 / 2 log_2 (N) + O(1))
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
    PP(tilde(x) = x^*) = product_i (1-p_i) = exp_2 (sum_i log_2 (1-p_i)) <= exp_2 (- sum_i p_i).
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
  $ product (1-p_i) = exp_2 ( sum log(1-p_i) ) <= exp_2 (- C sum p_i). $
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


