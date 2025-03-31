#import "environments.typ": *

#import "symbols.typ": *

// #show math.equation: set text(font: "New Computer Modern Math")

= Extensions to Real-Valued Algorithms <section_rounding>

// #show math.equation: set text(font: "STIX Two Math")

With @section_hardness, we have established strong low degree hardness for both low degree polynomial algorithms and low coordinate degree algorithms.
However, our stability analysis assumed that the algorithms in question were $Sigma_N$-valued.
In this section, we show that this assumption is not in fact as restrictive as it might appear.

Throughout, let $alg$ denote a $RR^N$-valued algorithm.
We want to show that
#enum(
  // numbering: "I.",
  [No low degree $alg$ can reliably output points _close_ -- within constant distance -- to a solution,],
  [No $Sigma_N$-valued algorithm $tilde(alg)$ coming from randomly rounding the output of $alg$, which changes an $omega(1)$ number of coordinates, can find a solution with nonvanishing probability.],
)
In principle, the first possibility fails via the same analysis as in @section_hardness, while the second fails because the landscape of solutions to any given NPP instance is sparse.

Why are these the only two possibilities? For $alg$ to provide a way to actually solve the NPP, we must be able to turn its outputs on $RR^N$ into points on $Sigma_N$. If $alg$ could output points within an constant distance (independent of the instance) of a solution, then we could convert $alg$ into a $Sigma_N$-valued algorithm by manually computing the energy of all points close to its output and returning the energy-maximizing point.

However, another common way to convert a $RR^N$-valued algorithm into a $Sigma_N$-valued one is by rounding the outputs, as in @alaouiSamplingSherringtonKirkpatrickGibbs2024a @huangStrongLowDegree2025.
Doing this directly can lead to difficulties in performing the stability analysis.
In our case, though, if we know no $alg$ can reliably output points within constant distance of a solution, then any rounding scheme which only flips $O(1)$ many coordinates will assuredly fail.
Thus, the only rounding schemes worth considering are those which flip $omega(1)$ many coordinates.

We first show that no low degree $alg$ can find points within constant distance of a solution, effectively by reproducing the argument of @section_hardness_lcd.
We then turn to describing a landscape obstruction to randomized rounding, relying on what we term the _solution repulsion property_ -- namely that solutions to any NPP instance are far away from each other, with this distance tradeoff controlled by the energy level of the solution set in consideration.
This can then be leveraged to show that any sufficiently randomized rounding scheme will always fail to find solutions at energies higher than the computational threshold.

== Proof of Hardness for Close Algorithms

Throughout this section, fix some distance $r=O(1)$.
Consider the event that the $RR^N$-valued $alg$ outputs a point close to a solution for an instance $g$:
$
  S_"close" (r) = multiset(
    exists hat(x) in S(E;g) "s.t.",
    alg(g) in B(hat(x), r)
  ) = {B(alg(g), r) inter S(E;g) != emptyset }
$

Note that as $r$ is of constant order, we can convert $alg$ into a $Sigma_N$-valued algorithm by first rounding the $alg(g)$ into the unit cube and then picking the best corner of $Sigma_N$ within constant distance of this output.
Let $cube colon RR^N to [-1,1]^N$ be the function which rounds $x in RR^N$ into the cube $[-1,1]^N$:
$
  cube(x)_i = cases(-1 #h(1em) &x_i <= -1\,, x_i &-1 < x_i < 1\,, 1 &x_i >= 1.)
$
Note that $cube$ is $1$-Lipschitz with respect to the Euclidean norm.

// definition of hat alg

#definition[
  Let $r>0$ and $alg$ be a $RR^N$-valued algorithm. Define $hat(alg)_r$ to be the $[-1,1]^N$-valued algorithm defined by
  $
    hat(alg)_r (g) := limits("argmin")_(x' in B(cube(alg(g)),r) inter Sigma_N) abs(inn(g,x')).
  $ <eq_hat_alg>
  If $B(cube(alg(g)),r) inter Sigma_N = emptyset$, then set $hat(alg)_r (g) := cube(alg(g))$, which is necessarily not in $Sigma_N$.
] <def_hat_alg>

Observe that $S_"close" (r)$ occuring implies $hat(alg)_r$ finds a solution for $g$.
In addition, computing $hat(alg)_r$ in practice requires additionally calculating the energy of $O(1)$-many points on $Sigma_N$.
This requires only an additional $O(N)$ operations.

Recall from @section_algorithm_stability that if $alg$ has low polynomial/coordinate degree, then we can derive useful stability bounds for its outputs.
Adjusting the bounds, this modification $hat(alg)_r$ of $alg$ is also stable.

#lemma[
  Suppose that $EE norm(alg(g))^2 <= C N$ and that $alg$ has degree $<= D$ (resp. coordinate degree $<= D$), and let $(g,g')$ be $(1-epsilon)$-correlated (resp. $(1-epsilon)$-resampled).
  Then $hat(alg)_r$ as defined above has
  $
    EE norm(hat(alg)_r (g) - hat(alg)_r (g'))^2 <= 4C D epsilon N + 8 r^2.
  $ <eq_hat_alg_expectation>
  In particular, we have
  $
    PP (norm(hat(alg)_r (g) - hat(alg)_r (g')) >= 2 sqrt(eta N)) <= (C D epsilon) / (eta) + (2 r^2) / (eta N).
  $
  <eq_hat_alg_stability>
] <lem_hat_alg_stability>
#proof[
  Observe that by the triangle inequality, $ norm(hat(alg)_r (g) &- hat(alg)_r (g'))$ is bounded by
  $
    norm(hat(alg)_r (g) - cube(alg(g))) +
    norm(cube(alg(g)) - cube(alg(g'))) +
    norm(cube(alg(g')) - hat(alg)_r (g')) \
    <= 2r + norm(alg(g) - alg(g')).
  $
  This follows as $cube$ is $1$-Lipschitz and the corner-picking step in @eq_hat_alg only moves $hat(alg)_r (g)$ from $cube(alg(r))$ by at most $r$.
  By Jensen's inequality, squaring this gives
  $
    norm(hat(alg)_r (g) - hat(alg)_r (g'))^2 <=
    2( 4r^2 + norm(alg(g) - alg(g'))^2).
  $
  Combining this with @prop_alg_stability gives @eq_hat_alg_expectation, and @eq_hat_alg_stability follows from Markov's inequality.
]

Of course, our construction of $hat(alg)_r$ is certainly never polynomial, and does not preserve any low coordinate degree assumptions in a controllable way.
Thus, we cannot directly hope for @thrm_sldh_poly_linear, @thrm_sldh_poly_sublinear, @thrm_sldh_lcd_linear, or @thrm_sldh_lcd_sublinear to hold.
However, because this rounding does not drastically alter the stability analysis, we are still able to show for $alg$ being a $RR^N$-valued low coordinate degree algorithm and any $r=O(1)$, low degree hardness still holds for $hat(alg)_r$.
The same argument shows hardness when $alg$ is a low degree polynomial algorithm; this is omitted for brevity.

We recall the setup from @section_hardness_lcd.
Let $g,g'$ be $(1-epsilon)$-resampled standard Normal vectors.
Define the following events:
$
  S_"diff" &:= { g != g'} \
  S_"solve" &:= { hat(alg)_r (g) in Soln(g), hat(alg)_r (g') in Soln(g')}, \
  S_"stable" &:= { norm(hat(alg)_r (g) - hat(alg)_r (g')) <= 2 sqrt(eta N) }, \
  S_"cond" (x) &:= multiset(
    exists.not x' in Soln(g') "such that",
    norm(x-x') <= 2sqrt(eta N),
  ).
$ <eq_lcd_hat_events>

These are the same events as in @eq_lcd_events, just adapted to $hat(alg)_r$. In particular, @lem_lcd_solve_disjoint holds unchanged.

Moreover, we define
$
  hat(p)^cor_"solve" := PP(hat(alg)_r (g) in Soln(g)) >= PP(S_"close" (r)),
$ <eq_def_lcd_hat_psolve>
$
  hat(p)^cor _"unstable" := 1 - PP(S_"stable" | S_"diff"), #h(5em)  hat(p)^cor _"cond" (x) := 1 - PP(S_"cond" (x) | S_"diff"),
$
along with $hat(p)^cor _"cond" := max_(x in Sigma_N) hat(p)^cor _"cond" (x)$, echoing @eq_def_lcd_punstablecond.
Observe that as $hat(p)^cor _"cond"$ makes no reference to any algorithm, the bound in @prop_resampled_fundamental holds without change. Moreover, @lem_hat_alg_stability lets us control $hat(p)^cor _"unstable"$. The final piece needed is an appropriate analog of @lem_resampled_solve_prob.

#lemma[
  For $g,g'$ being $(1-epsilon)$-resampled, we have
  $
    PP(S_"solve") = PP(hat(alg)_r (g) in Soln(g), hat(alg)_r (g') in Soln(g')) >= (hat(p)^cor_"solve")^2
  $
] <lem_hat_resampled_solve_prob>
#proof[
  Observe that, letting $+$ denote Minkowski sum, we have that
  $ { hat(alg)_r (g) in Soln(g) } = { alg(g) in Soln(g) + B(0,r) }. $
  Expanding $Soln(g)$, the proof concludes as in @lem_resampled_solve_prob.
]

#set math.cases(gap: 0% + 0.4em)

#theorem[
  Let $omega(log^2 N) <= E <= Theta(N)$, and let $g,g'$ be $(1-epsilon)$-resampled standard Normal r.v.s.
  Consider any $r=O(1)$ and $RR^N$-valued $alg$ with $EE norm(alg(g))^2 <= C N$, and assume in addition that
  #enum(
    [if $E = delta N = Theta(N)$ for $delta > 0$, then $alg$ has coordinate degree $D <= o(N)$;],
    [if $log^2 N << E << N$, then $alg$ has coordinate degree $D <= o(E slash log^2 N)$.],
  )
  Let $hat(alg)_r$ be defined as in @def_hat_alg. Then there exist $epsilon, eta > 0$ such that
  $ hat(p)^cor_"solve" = PP(hat(alg)_r (g) in Soln(g)) = o(1). $
] <thrm_sldh_hat_lcd>
#proof[
  First, by @lem_lcd_solve_disjoint, the appropriate adjustment of @eq_lcd_fundamental holds, namely that
  $
    (hat(p)^cor_"solve")^2 <= hat(p)^cor_"unstable" + hat(p)^cor_"cond" + (1 - PP(S_"diff"))
  $ <eq_hat_lcd_fundamental>
  To ensure $PP(S_"diff") approx 1$, we begin by following @eq_def_lcd_epsilon and choosing $epsilon = log_2 (N slash D) slash N$. Moreover, following the proof of @thrm_sldh_lcd_linear and @thrm_sldh_lcd_sublinear, we know that choosing
  $
    eta = cases(
      O(1) "s.t." 2 eta log_2(1 slash eta) < delta slash 4 #h(1em) &E = delta N\,,
      E / (16 N log_2  (N slash E)) #h(1em) &E <= o(N).,
    )
  $
  in conjunction with @prop_resampled_fundamental, guarantees that
  $
    hat(p)^cor_"cond" <= exp_2 (- (3 E) / 4 + O(1)) = o(1).
  $
  Finally, note that in the linear case, when $eta = O(1)$, $r^2/(eta N) = o(1)$ trivially. In the sublinear case, for $eta= E slash (16 N log_2 (N slash E))$, we instead get
  $ eta N = E / (16 log_2 (N slash E)) >= E / (16 log_2 N) = omega(1), $
  as $E >> log^2 N$.
  Thus, applying the properly modified @lem_hat_alg_stability with these choices of $epsilon,eta$, we see that $hat(p)^cor _"unstable" = o(1)$.
  By @eq_hat_lcd_fundamental, we conclude that $hat(p)^cor _"solve" = o(1)$, as desired.
]


Talk about implications meow.

== Truly Random Rounding

At this point, one might wonder whether, while deterministic algorithms fail, perhaps a randomized rounding scheme could save us, maybe by assigning small values to coordinates which it was less confident in.
However, this approach is blunted by the same brittleness of the NPP landscape that established the conditional obstruction of @prop_correlated_fundamental and @prop_resampled_fundamental.
In particular, by @thrm_solutions_repel, if you have a subcube of $Sigma_N$ with dimension growing slowly with $N$, then with high probability at most one of those points will be a solution.

For this section, again let $alg$ be a deterministic $RR^N$-valued algorithm.
Moreover, assume we are searching for solutions with energy between $(log_2 N)^2 << E <= N$; note that for lower values of $E$, algorithms like @karmarkarDifferencingMethodSet1983 already achieve discrepancies of $N^(O(log_2 N))$ energy in polynomial time.

To start, for any $x in RR^N$, we write $x^*$ for the coordinate-wise signs of $x$, i.e.
$ x^*_i := cases(+1 #h(1em) &x_i > 0\,, -1 &x_i <= 0.) $
We can define the modified alg $alg^*(g) := alg(g)^*$.

#remark[
  meow $alg^*$ fails and is still degree $D$ lcdf, even if it stops being a polynomial. Bounds on $D$ worsen, but only to what you'd expect.
  Note that if $alg$ has coordinate degree $D$, then $alg^*$ also has coordinate degree $D$. As a deterministic $Sigma_N$-valued algorithm, strong low degree hardness as proved in the previous section applies.
]

In contrast to taking signs of the outputs of $alg$ (which corresponds to deterministically rounding the outputs of $alg$ to $Sigma_N$), we can consider passing the output of $alg$ through a randomized rounding scheme. Let $round(x,omega) colon RR^N times Omega to Sigma_N$ denote any randomized rounding function, with randomness $omega$ independent of the input. We will often suppress the $omega$ in the notation, and treat $round(x)$ as a $Sigma_N$-valued random variable.
Given such a randomized rounding function, we can describe it in the following way.
Let $p_1 (x),dots,p_N (x)$ be defined by
$ p_i (x) := max(PP(round(x)_i != x^*_i), 1/2). $ <eq_rounding_changed_coord>

We need to guarantee that each $p_i (x) <= 1 slash 2$ for the following alternative description of $round(x)$:

#lemma[
  Fix $x in RR^N$, and draw $N$ coin flips $I_(x,i) ~ Bern(2p_i (x))$ and $N$ signs $S_i ~ "Unif"{plus.minus 1}$, all mutually independent, and define the random variable $tilde(x) in Sigma_N$ by
  $ tilde(x)_i := S_i I_(x,i) + (1-I_(x,i)) x^*_i. $
  Then $tilde(x) ~ round(x)$.
] <lem_random_rounding_altdef>
#proof[
  Conditioning on $I_(x,i)$, we can check that
  $
    PP(tilde(x)_i != x_i) &= 2 p_i (x) dot PP(tilde(x)_i = x_i | I_(x,i) = 1) + (1-2p_i (x) ) dot PP(tilde(x)_i != x_i | I_(x,i) = 0)
    // = 2 p_i (x) dot 1 / 2
    = p_i (x).
  $
  Thus, $PP(tilde(x)_i = x^*_i) = PP(round(x)_i = x^*_i)$, as claimed.
  // $tilde(x)$ has the same probability of equalling $x^*$ in each coordinate as $round(x)$ does, as claimed.
]

By @lem_random_rounding_altdef, we can redefine $round(x)$ to be $tilde(x)$ as constructed without loss of generality.

// What is tilde(x)?

It thus makes sense to define $tilde(alg)(g) := round(alg(g))$, which is now (a) $Sigma_N$-valued and (b) randomized only in the transition from $RR^N$ to $Sigma_N$ (i.e., the rounding does not depend directly on $g$, only the output $x = alg(g)$).
We should expect that if $tilde(alg)=alg^*$ (e.g., if $alg$ outputs values far outside the cube $[-1,1]^N$) with high probability, then low degree hardness will still apply, as $alg^*$ is deterministic.
However, in general, any $tilde(alg)$ which differs from $alg^*$ will fail to solve $g$ with high probability.
This is independent of any assumptions on $alg$: any rounding scheme will introduce so much randomness that $tilde(x)$ will be effectively a random point, which has a vanishing probability of being a solution because of how sparse and disconnected the NPP landscape is.

To see this, we first show that any randomized rounding scheme as in @lem_random_rounding_altdef which a.s.~differs from picking the closest point deterministically will resample a diverging number of coordinates.

#lemma[
  Fix $x in RR^N$, and let $p_1 (x),dots,p_N (x)$ be defined as in @eq_rounding_changed_coord.
  Then $tilde(x) != x^*$ with high probability iff $sum_i p_i (x) = omega(1)$.
  Moreover, assuming that $sum_i p_i (x)= omega(1)$, the number of coordinates in which $tilde(x)$ is resampled diverges almost surely.
] <lem_rounding_changes_soln>
#proof[
  Recall that for $x in [0,1 slash 2]$, $log_2 (1-x) = Theta(x)$.
  Thus, as each coordinate of $x$ is rounded independently, we can compute
  $
    PP(tilde(x) = x^*) = product_i (1-p_i (x)) = exp_2 (sum_i log_2 (1-p_i (x))) <= exp_2 (- Theta(sum_i p_i (x))).
  $
  Thus, $PP(tilde(x)=x^*) = o(1)$ iff $sum_i p_i (x) = omega(1)$, as claimed.

  Next, following the construction of $tilde(x)$ in @lem_random_rounding_altdef, let $E_i = {I_(x,i) = 1}$ be the event that $tilde(x)_i$ is resampled from $ "Unif"{plus.minus 1}$, independently of $x^*_i$.
  The $E_i$ are independent, so by Borel-Cantelli, $sum_i PP(E_i) = 2 sum_i p_i (x) = omega(1)$ implies $tilde(x)_i$ is resampled infinitely often with probability 1, thus completing the proof.
]

Introduce section meow.

No two adjacent points on $Sigma_N$ (or pairs within $k=O(1)$ distance) which are both good solutions to the same problem.

Remarks on theorem below meow.

#theorem[Solutions Repel][
  Consider any distances $k = Omega(1)$ and energy levels $E >> k log N$.
  With high probability, there are no pairs of distinct solutions $x,x' in Soln(g)$ to an instance $g$ with $norm(x-x') <= 2 sqrt(k)$ (i.e. within $k$ sign flips of each other).
] <thrm_solutions_repel>
#proof[
  Consider any $x != x'$, and let $J subeq [N]$ denote the coordinates in which $x,x'$ differ. Then
  $ x = x_(overline(J)) + x_J, #h(5em) x' = x_(overline(J)) - x_J. $
  Assuming both $x,x' in Soln(g)$, we can expand the inequalities
  $-2^(-E) <= inn(g,x), inn(g,x') <= 2^(-E)$
  into
  $
    -2^(-E) <= &inn(g,x_(overline(J))) + inn(g,x_J) <= 2^(-E), \
    -2^(-E) <= &inn(g,x_(overline(J))) - inn(g,x_J) <= 2^(-E).
  $
  Multiplying the lower equation by $-1$ and adding the resulting inequalities gives $abs(inn(g,x_J)) <= 2^(-E)$.

  Thus, finding pairs of distinct solutions within distance $2 sqrt(k)$ implies finding a subset $J subeq [N]$ of at most $k$ coordinates and $abs(J)$ signs $x_J$ such that $abs(inn(g_J,x_J)) <= 2^(-E)$.
  By @vershyninHighDimensionalProbabilityIntroduction2018[Exer. 0.0.5], there are
  $
    sum_(1 <= k' <= k)binom(N,k') <= ((e N) / k)^k <= (e N)^k = 2^(O(k log N))
  $
  choices of such subsets, and at most $2^k$ choices of signs.
  Now, $inn(g_J,x_J) ~ Normal(0,abs(J))$, and as $abs(J)>=1$, @lem_normal_smallprob and the following remark implies $PP(abs(inn(g_J,x_J)) <= 2^(-E)) <= exp_2(-E + O(1))$, so union bounding this over the $2^O(k log N))$ possibilities gives
  $
    PP multiprob(
      exists (x,x') in Soln(g) "s.t.",
      norm(x-x') <= 2sqrt(k).
    )
    /* <= PP multiprob( exists J subset [N]\, x_J in {plus.minus 1}^abs(J) "s.t.", (upright(a)) &abs(J) <= k\,, (upright(b)) &abs(inn(g_J,x_J)) <= exp_2 (-E)) */
    <= exp_2 (-E + O(k log N)) = o(1). #qedhere
  $ <eq_solutions_repel>

  /*
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
  */
]

Here, our technique of converting pairs of solutions into subvectors of $g$ which must have small sum enables us to reduce the size of the set we union bound over from $2^(O(N))$ to $2^(O(k log N))$.
Moreover, observe that this proof can be adapted to show that for a fixed $x in Soln(g)$, there are no other solutions within $k$ sign flips with high probability.

meow
With this, we can apply @thrm_solutions_repel, which shows that solutions resist clustering at a rate related to their energy level (i.e. higher energy solutions are push each other further apart), to conclude that any $tilde(alg)$ which is not equal to $alg^*$ with high probability fails to find solutions.

#theorem[
  Let $x= alg(g)$, and define $x^*, tilde(x)$, etc., as previously.
  Moreover, assume that for any $x$ in the possible outputs of $alg$, we have $sum_i p_i (x) = omega(1)$.
  Then, for any $E >= omega((log_2 N)^2)$, we have
  $ PP(tilde(alg)(g) in S(E;g)) = PP(tilde(x) in S(E;g)) <= o(1). $
]
#proof[
  Following the characterization of $tilde(x)$ in @lem_random_rounding_altdef, let $K := max(log_2 N, sum_i I_(x,i))$.
  By assumption on $sum_i p_i (x)$ and @lem_rounding_changes_soln, we know $K$, which is at least the number of coordinates which are resampled, is bounded as $1 << K <= log_2 N$, for any possible $x = alg(g)$.
  Now, let $S subeq [N]$ denote the set of the first $K$ coordinates to be resampled, so that $K = abs(S)$.
  Consider now
  $ PP(tilde(x) in S(E;g) | tilde(x)_([N] without S)), $
  where we fix the coordinates outside of $S$ and let $tilde(x)$ be uniformly sampled from a $K$-dimensional subcube of $Sigma_N$.
  All such $tilde(x)$ are within distance $2sqrt(K)$ of each other, so by @thrm_solutions_repel, the probability there is more than one such $tilde(x) in S(E;g)$ is bounded by
  $ exp_2 (-E + O(K log_2 N)) <= exp_2(-E + O((log_2 N)^2)) = o(1), $
  by assumption on $E$. Thus, the probability that any of the $tilde(x)$ is in $S(E;g)$ is bounded by $2^(-K)$, whence
  $
    PP(tilde(x) in S(E;g)) =
    EE[ PP(tilde(x) in S(E;g) | tilde(x)_([N] without S)) ] <= 2^(-K) <= o(1). #qedhere
  $
  // This should work as the rounding bounds are independent of the bounds pertaining to g, by assumption that sum_i p_i (x) = omega(1) for all x; can't have alg throw a bunch of x's where K = O(1).
]

meow discuss possible extensions of randomization schemes and whether you expect those to work instead.

