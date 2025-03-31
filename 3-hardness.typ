#import "environments.typ": *

#import "symbols.typ": *

= Proof of Strong Low Degree Hardness <section_hardness>

In this section, we prove @thrm_sldh_poly_informal and @thrm_sldh_lcd_informal -- that is, we show strong low degree hardness for both low polynomial degree and low coordinate degree algorithms.

Our argument utilizes what can be thought of as a "conditional" version of the overlap gap property.
Traditionally, proofs of algorithmic hardness use the overlap gap property is a global obstruction: one shows that with high probability, one cannot find a tuple of good solutions to a family of correlated instances which are all roughly the same distance apart.
Here, however, we show a local obstruction -- we condition on being able to solve a single instance, and show that after a small change to the instance, we cannot guarantee any solutions will exist close to the first one.
This is an instance of the "brittleness," so to speak, that makes NPP so frustrating to solve; even small changes in the instance break the landscape geometry, so that even if solutions exist, there's no way to know where they will end up.

This conditional landscape obstruction approach is partially inspired by Huang and Sellke's recent work on strong low degree hardness for finding optima in spin glasses @huangStrongLowDegree2025.
However, a main reason for not appealing to an OGP-style result is Gamarnik and Kızıldağ's disproof of the $m$-OGP for sublinear energy levels @gamarnikAlgorithmicObstructionsRandom2021b[Thm. 2.5].

Our conditional obstruction (@prop_correlated_fundamental in the low degree polynomial case, and @prop_resampled_fundamental in the low coordinate degree case) is established by a first moment computation.
That is, we show that given "correlated" instances $g,g'$ and a point $x in Sigma_N$ such that $g',x$ are conditionally independent given $g$, then any fixed point $x' in Sigma_N$ has low probability of solving $g'$; then the same must hold for all $x'$ in a suitably small neighborhood of $x$.
This is similar to the proof of the OGP in the linear energy regime in @gamarnikAlgorithmicObstructionsRandom2021b, but our method allows us to work with sublinear energy levels.
Heuristically, this is because the cardinality of neighborhoods of $x$ grows exponentially in $N$, which means that the number of $m$-tuples of such points grows much faster than any sublinearly small probability.
In contrast, the disproof of the OGP in the sublinear energy regime of Gamarnik and Kızıldağ follows from a second moment computation:
they show that the majority of pairs of $m$-tuples of solutions are nearly "uncorrelated," which again implies that globally, looking at large ensembles of solutions fails to capture the brittleness of the NPP for cardinality reasons.

The proof of @thrm_sldh_poly_informal, stated formally as @thrm_sldh_poly_linear and @thrm_sldh_poly_sublinear, is as follows.
#footnote[The proof of @thrm_sldh_lcd_informal requires only minor modifications.]
Let $E$ be an energy level and $D$ be a maximum algorithm degree, both depending on $N$.
We assume that $D$ is bounded by a level depending on $E$ and $N$, corresponding to the low degree regime in which we want to show hardness.
We then choose parameters $eta$ and $epsilon$, depending on $E$, $D$, and $N$.
As described in @section_algorithm, assume $alg$ is a deterministic, $Sigma_N$-valued algorithm with polynomial degree at most $D$.
Our goal is to show that for our choices of $eta$ and $epsilon$,
$ PP(alg(g) in Soln(g)) -> 0 $
as $N to infinity$.
This is done in the following steps:

#enum(
  [
    Consider a $(1-epsilon)$-correlated pair $g,g'$ of NPP instances.
    These are $N$-dimensional standard Normal vectors which are $p$-correlated, for $p=1-epsilon$ (when considering coordinate degree, we instead require them to be $p$-resampled).
  ],
  [
    For $epsilon$ small, $g$ and $g'$ have correlation close to 1.
    By @prop_alg_stability, this implies the outputs of a low degree polynomial algorithm $alg$ will be within distance $2sqrt(eta N)$ of each other with high probability.
  ],
  [
    For $eta$ small and a fixed $alg(g)$, @prop_correlated_fundamental shows that conditional on $g$, $g'$ has no solutions within distance $2 sqrt(eta N)$ of $alg(g)$. This is the conditional landscape obstruction we described above.
  ],
  [
    Put together, these points imply it is unlikely for $alg$ to find solutions to _both_ $g$ and $g'$ such that the stability guarantee of @prop_alg_stability holds.
    By the positive correlation statement in @lem_correlated_solve_prob, we conclude that $alg(g) in.not Soln(g)$ with high probability.
  ],
)

We can summarize the parameters in our argument in the following table.

#figure(
  pad(
    x: 1.2em,
    table(
      columns: 4,
      fill: (_, y) => if calc.odd(y) { purple.transparentize(80%) },
      // rgb("EAF2F5") },
      stroke: none,
      table.hline(),
      [*Parameter*], [*Meaning*], [*Desired Direction*], [*Intuition*],
      table.hline(),
      [$N$], [Dimension],
      [-], [Showing strong hardness _asymptotically_, want uniformly large.],

      [$E$], [Energy; \ want $x$ such that \ $abs(inn(g,x)) <= 2^(-E)$],
      [Small], [Smaller $E$ rules out weaker solutions; know $Omega(log^2 N) <= E <= Theta(N)$ by @karmarkarDifferencingMethodSet1983 @karmarkarProbabilisticAnalysisOptimum1986],

      [$D$], [Algorithm degree],
      [Large], [Higher degree means more complex/longer time algorithms fail.],

      [$epsilon$], [Distance between $(g,g')$],
      [Small], [Want to show that small changes in instance lead to "breaking" of landscape.],

      [$eta$], [Instability; \ $norm(alg(g) - alg(g')) <= 2 sqrt(eta N)$, for $(g,g')$ close],
      [Large \ (but bounded \ by $E,N$)], [Large $eta$ indicates a more unstable algorithm; want to show that even weakly stable algorithms fail. ],

      table.hline(),
    ),
  ),
  caption: [Explanation of Parameters],
) <parameter_table>

For the remainder of this section, we first show strong low degree hardness for polynomial algorithms, and then for low coordinate degree algorithms.
Throughout, we aim to keep constants as explicit as possible, to clarify the nature in which $epsilon$ and $eta$ behave in the limit as $N to infinity$.
We end by interpreting our results through the lens of the low degree heuristic, as well as discuss the extensions needed to consider randomized $Sigma_N$-valued algorithms.

== Hardness for Low Degree Polynomial Algorithms <section_hardness_poly>

// Degree $D$ polynomials

First, we consider the case of $alg$ being a polynomial algorithm with degree $D$.
Let $g,g'$ be $(1-epsilon)$-correlated standard Normal r.v.s, and let $x in Sigma_N$ depend only on $g$.
Furthermore, let $eta>0$ be a parameter which will be chosen in a manner specified later.
We define the events
$
  S_"solve" &:= {alg(g) in Soln(g), alg(g') in Soln(g')}, \
  S_"stable" &:= {norm(alg(g) - alg(g')) <= 2 sqrt(eta N) }, \
  S_"cond" (x) &:= multiset(
    exists.not x' in Soln(g') "such that",
    norm(x-x') <= 2sqrt(eta N),
  ).
$ <eq_poly_events>

Intuitively, the first two events ask that the algorithm solves both instances and is stable, respectively.
The last event, which depends on $x$, corresponds to the conditional landscape obstruction: for an $x$ depending only on $g$, there is no solution to $g'$ which is close to $x$.

#lemma[
  We have, for $x := alg(g)$, $S_"solve" inter S_"stable" inter S_"cond" (x) = emptyset$.
] <lem_solve_disjoint>
#proof[
  Suppose that $S_"solve"$ and $S_"stable"$ both occur.
  Letting $x:=alg(g)$ (which only depends on $g$) and $x':=alg(g')$, we have that $x' in Soln(g')$ while also being within distance $2 sqrt(eta N)$ of $x$.
  This contradicts $S_"cond" (x)$, as desired.
]

First, define $p^cor _"solve"$ as the probability that the algorithm solves a single random instance:
$ p^cor_"solve" = PP(alg(g) in Soln(g)). $ <eq_def_psolve>
Then, we have the following correlation bound, which allows us to avoid union bounding over instances.

#lemma[
  For $g,g'$ being $(1-epsilon)$-correlated, we have
  $
    PP(S_"solve") = PP(alg(g) in Soln(g), alg(g') in Soln(g')) >= (p^cor_"solve")^2
  $
] <lem_correlated_solve_prob>
#proof[
  Let $tilde(g), g^((0)), g^((1))$ be three i.i.d. copies of $g$, and observe that $g,g'$ are jointly representable as
  $
    g = sqrt(1-epsilon) tilde(g) + sqrt(epsilon) g^((0)), #h(5em)
    g' = sqrt(1-epsilon) tilde(g) + sqrt(epsilon) g^((1)).
  $
  Thus, since $g,g'$ are conditionally independent given $tilde(g)$, we have
  $
    PP(alg(g) in Soln(g), alg(g') in Soln(g'))
    &= EE[ PP(alg(g) in Soln(g), alg(g') in Soln(g') | tilde(g)) ] \
    &= EE[ PP(alg(g) in Soln(g) | tilde(g))^2 ] \
    &>= EE[ PP(alg(g) in Soln(g) | tilde(g))]^2 = (p^cor_"solve")^2,
  $
  where the last line follows by Jensen's inequality.
]

#remark[
  We note here that @lem_correlated_solve_prob also holds in the case where $alg(g,omega)$ is randomized, in the sense of @def_algorithm.
  Namely, write
  $
    p &= PP(alg(g, omega) in Soln(g)), &P& = PP(alg(g,omega) in Soln(g), alg(g',omega) in Soln(g')), \
    p(omega) &= PP(alg(g,omega) in Soln(g) | omega), #h(2em) &P(omega)& = PP(alg(g,omega) in Soln(g), alg(g',omega) in Soln(g') | omega).
  $
  @lem_correlated_solve_prob shows that for any $omega in Omega_N$, $P(omega) >= p(omega)^2$. Then, by Jensen's inequality,
  $ P = EE[P(omega)] >= EE[p(omega)^2] >= EE[p(omega)]^2 = p^2. $
  Thus, in combination with @rmk_randomized_L2_stable, the remainder of the proof also applies when $alg$ depends on an independent random seed $omega$.
] <rmk_randomized_multiple_solve>

Moreover, define $p^cor _"unstable"$, $p^cor _"cond" (x)$, and $p^cor_"cond"$ by
$
  p^cor _"unstable" := 1 - PP(S_"stable"),
  #h(2em)
  p^cor _"cond" (x) := 1 - PP(S_"cond" (x)),
  #h(2em)
  p^cor_"cond" := max_(x in Sigma_N) p^cor_"cond" (x).
$ <eq_def_pcond>
By @lem_solve_disjoint, we know that for $x := alg(g)$
$ PP(S_"solve") + PP(S_"stable") + PP(S_"cond" (x)) <= 2, $
and rearranging, we get that
$ (p^cor_"solve")^2 <= p^cor_"unstable" + p^cor_"cond". $ <eq_poly_fundamental>
Our proof follows by showing that, for appropriate choices of $epsilon$ and $eta$, depending on $D$, $E$, and $N$, we have $p^cor _"unstable",p^cor _"cond" = o(1)$.
The former is controlled by @prop_alg_stability, so all that remains is to show the latter.
To this end, we start by bounding the size of neighborhoods on $Sigma_N$.

#proposition[Hypercube Neighborhood Size][
  Fix $x in Sigma_N$, and let $eta <= 1 slash 2$. Then the number of $x'$ within distance $2 sqrt(eta N)$ of $x$ is
  $
    abs({x' in Sigma_N : norm(x-x') <= 2eta sqrt(N)})
    <= exp_2 (2 eta log_2 (1 slash eta)N ).
  $
] <lem_hypercube_counting>
#proof[
  Let $k$ be the number of coordinates which differ between $x$ and $x'$ (i.e. the Hamming distance).
  We have $norm(x-x')^2=4k$, so $norm(x-x') <= 2 sqrt(eta N)$ iff $k <= N eta$.
  Moreover, for $eta <= 1 slash 2$, we know $k <= N slash 2$.
  Thus, by @lem_chernoff_hoeffding,
  $
    sum_(k <= N eta) binom(N,k) <= exp_2 (2 eta log_2 (1 slash eta)N ). #qedhere
  $
]

This shows that within a small neighborhood of any $x in Sigma_N$, the number of nearby points is exponential in $N$, with a more nontrivial dependence on $eta$. The question is then how many of these are solutions to the correlated instance $g'$. This forms the heart of our conditional landscape obstruction, which we show as follows.

#proposition[Fundamental Estimate -- Correlated Case][
  Assume that $(g,g')$ are $(1-epsilon)$-correlated standard Normal vectors.
  Then, for any $x$ such that $(g',x)$ are conditionally independent given $g$,
  $
    p^cor_"cond" (x) &:= PP multiprob(
      exists x' in Soln(g') "such that",
      norm(x-x') <= 2sqrt(eta N),
    ) \
    &<= exp_2(-E -1 / 2 log_2(epsilon) + 2 eta log_2(1 / eta) N + O(log N)).
  $ <eq_correlated_lowprob_disp>
] <prop_correlated_fundamental>
#proof[
  For each $x'$ within distance $2 sqrt(eta N)$ of $x$, let
  $ I_(x') := I(x' in Soln(g')) = I(abs(inn(g',x')) <= 2^(-E)), $
  so that
  $
    p^cor_"cond" (x) =
    EE[ sum_(norm(x - x') <= 2sqrt(eta N)) EE[I_(x') | g] ]
    = EE[ sum_(norm(x-x') <= 2sqrt(eta N)) PP(abs(inn(g',x')) <= 2^(-E) | g) ]
  $ <eq_correlated_firstmoment>
  Note in particular that the range of this sum is independent of the inner probability, as $g'$ and $x$ are conditionally independent.

  To bound the inner probability, let $tilde(g)$ be a Normal vector independent to $g$ and set $p = 1-epsilon$.
  Observe that $g'$ can be represented as $g' = p g + sqrt(1-p^2)tilde(g)$,
  so, $inn(g',x') = p inn(g,x') + sqrt(1-p^2)inn(tilde(g),x')$.
  We know $inn(tilde(g),x')~ Normal(0,N)$, so conditional on $g$, we have $inn(g',x') | g ~ Normal(p inn(g,x'), (1-p^2)N)$.
  Note that $inn(g',x')$ is nondegenerate for $(1-p^2) N >= epsilon N > 0$; thus by @lem_normal_smallprob, we get
  $
    PP(abs(inn(g',x')) <= 2^(-E) | g) <= exp_2 (-E - 1 / 2 log_2 (epsilon) + O(log N)).
  $ <eq_correlated_lowprob>

  Finally, by @lem_hypercube_counting, the number of terms in the sum @eq_correlated_firstmoment is bounded by $exp_2 (2 eta log_2 (1 slash eta)N)$, so given that @eq_correlated_lowprob is independent of $g$, we deduce @eq_correlated_lowprob_disp.
]

With this obstruction in hand, we can turn to showing strong low degree hardness for polynomial algorithms.
We start with hardness for linear energy levels, $E=Theta(N)$; this corresponds to the statistically optimal regime, as per @karmarkarProbabilisticAnalysisOptimum1986.
Our hardness result in this regime roughly corresponds to that of Gamarnik and Kızıldağ's Theorem 3.2, although their result applies to stable algorithms and does not show a low degree hardness-type result
@gamarnikAlgorithmicObstructionsRandom2021b[Thm. 3.2].
A key feature of considering polynomial algorithms is that in @prop_correlated_fundamental, we can let $epsilon$ be exponentially small in $E$, which in the linear regime allows for it to be exponentially small in $N$; as we will see, this has rather extreme implications for the failure of polynomial algorithms under the low degree heuristic.

// linear poly low degree hardness
#theorem[
  Let $delta > 0$ and $E = delta N$, and let $g,g'$ be $(1-epsilon)$-correlated standard Normal r.v.s.
  Then, for any polynomial algorithm $alg$ with $EE norm(alg(g))^2 <= C N$ and degree $D <= o(exp_2 (delta N slash 2))$, there exist $epsilon, eta > 0$ such that $p^cor _"solve" = o(1)$.
] <thrm_sldh_poly_linear>
#proof[
  Recall from @eq_poly_fundamental that it suffices to show that both $p^cor _"cond"$ and $p^cor _"unstable"$ go to zero.
  Further, by @eq_def_pcond and @prop_correlated_fundamental, we have
  $
    p^cor_"cond" <= exp_2 (-E - 1 / 2 log_2 (epsilon) + 2 eta log_2 (1 / eta) N + O(log N))
  $
  Thus, first choose $eta$ sufficiently small, such that $2 eta log_2 (1 slash eta) < delta slash 4$ -- this results in $eta$ being independent of $N$.
  Next, choose $epsilon = exp_2 (- delta N slash 2)$. This gives
  $
    p^cor_"cond" <= exp_2 (- delta N - 1 / 2 (-(delta N) / 2) + (delta N) / 4 + O(log N)) = exp_2 (- (delta N) / 2 + O(log N)) = o(1).
  $
  Moreover, for $D <= o(exp_2 (delta N slash 2))$, we get by @prop_alg_stability that
  $
    p^cor_"unstable" <= (C D epsilon) / (2 eta) asymp (D epsilon) / eta asymp D dot exp_2 (- (delta N) / 2) -> 0.
  $
  By @eq_poly_fundamental, we conclude that $(p^cor _"solve")^2 <= p^cor _"unstable" + p^cor _"cond" = o(1)$.
]

Next, we let $omega(log  N ) <= E <= o(N)$. This bridges the gap from the statistically optimal energy threshold down to the computational threshold. In particular, our method allows us to rule out degree $o(N^O(N))$ polynomial algorithms even for achieving the same energy threshold as the Karmarkar-Karp algorithm; this is expected however, as neither the original KK algorithm nor the simplified LDM algorithm are polynomial.

// sublinear poly low degree hardness
#theorem[
  Let $omega(log N) <= E <= o(N)$, and let $g,g'$ be $(1-epsilon)$-correlated standard Normal r.v.s.
  Then, for any polynomial algorithm $alg$ with $EE norm(alg(g))^2 <= C N$ and degree $D <= o(exp_2 (E slash 4))$, there exist $epsilon, eta > 0$ such that $p^cor _"solve" = o(1)$.
] <thrm_sldh_poly_sublinear>
#proof[
  As in @thrm_sldh_poly_linear, it suffices to show that both $p^cor _"cond"$ and $p^cor _"unstable"$ go to zero.
  To do this, we choose
  $
    epsilon = exp_2 (-E/2), #h(5em) eta = E / (16 N log_2  (N slash E)).
  $ <eq_def_sublinear_epseta>
  With this choice of $eta$, some simple analysis shows that for $E / N << 1$, we have that
  $ E / (4 N) > 2 eta log_2 (1 slash eta). $
  Thus, by @prop_correlated_fundamental, we get
  $
    p^cor_"cond" &<= exp_2 (-E - 1 / 2 log_2 (epsilon) + 2 eta log_2 (1 / eta) N + O(log N)) \
    &<= exp_2 (-E + E / 4 + E / 4 + O(log N)) = exp_2 (-E / 2 + O(log N)) = o(1).
  $
  where the last equality follows as $E >> log  N$.
  Then, by @prop_alg_stability, the choice of $D = o(exp_2 (E slash 4))$ gives
  $
    p^cor_"unstable" &<= (C D epsilon) / (2 eta)
    asymp (D epsilon N log_2 (N slash E)) / E \
    &= (D exp_2 (-E slash 2) N log_2 (N slash E)) / E
    <= (D exp_2 (-E slash 2) N log_2 (N)) / E \
    &<= D exp_2 (-E / 2 + log_2 (N) + log_2 log_2 (N) - log_2 (E)) \
    &<= exp_2 (-E / 4 + log_2 (N) + log_2 log_2 (N) - log_2 (E)) = o(1),
  $
  again, as $E >> log  N$.
  Ergo, by @eq_poly_fundamental, $(p^cor _"solve")^2 <= p^cor _"unstable" + p^cor _"cond" = o(1)$.
]

#remark[Extending to Randomized Algorithms][
  meow
]

== Hardness for Low Coordinate Degree Algorithms <section_hardness_lcd>

// Degree $D$ functions

Next, let $alg$ have coordinate degree $D$.
We now want $g,g'$ to be $(1-epsilon)$-resampled standard Normal random variables. We define
$
  S_"diff" &:= { g != g'}, \
  S_"solve" &:= {alg(g) in Soln(g), alg(g') in Soln(g')}, \
  S_"stable" &:= {norm(alg(g) - alg(g')) <= 2 sqrt(eta N) }, \
  S_"cond" (x) &:= multiset(
    exists.not x' in Soln(g') "such that",
    norm(x-x') <= 2sqrt(eta N),
  ).
$ <eq_lcd_events>
Note that these are the same events as @eq_poly_events, along with an event to ensure that $g'$ is nontrivially resampled from $g$.

#lemma[
  For $g,g'$ being $(1-epsilon)$-resampled,
  $PP(S_"diff") = 1 - (1-epsilon)^N <= epsilon N$.
] <lem_sdiff_prob>
#proof[
  Follows from calculation:
  $ PP(g=g') = product_(i=1)^N PP(g_i = g_i') = (1-epsilon)^N #qedhere $
]

#lemma[
  We have, for $x=alg(g)$, $S_"diff" inter S_"solve" inter S_"stable" inter S_"cond" (x) = emptyset$.
] <lem_lcd_solve_disjoint>
#proof[
  This follows from @lem_solve_disjoint, noting that the proof did not use that $g != g'$ almost surely.
]

We can interpret this as saying $S_"solve", S_"stable", S_"cond"$ are all mutually exclusive, conditional on $g != g'$.
The previous definition of $p^cor _"solve"$ in @eq_def_psolve, which we now term $p^res _"solve"$, remains valid.

#lemma[
  For $g,g'$ being $(1-epsilon)$-resampled, we have
  $
    PP(S_"solve") = PP(alg(g) in Soln(g), alg(g') in Soln(g')) >= (p^res_"solve")^2
  $
] <lem_resampled_solve_prob>
#proof[
  // First, the statement is trivial if $g=g'$, as $p^res _"solve" <= 1$, so assume that $g != g'$.
  Let $tilde(g), g^((0)), g^((1))$ be three i.i.d. copies of $g$, and let $J$ be a random subset of $[N]$ where each coordinate is included with probability $1-epsilon$.
  Then, $g,g'$ are jointly representable as
  $
    g = tilde(g)_J + g^((0))_([N] without J), #h(5em)
    g' = tilde(g)_J + g^((1))_([N] without J)
  $
  where $tilde(g)_J$ denotes the vector with coordinates $tilde(g)_i$ if $i in J$ and 0 else.
  Thus $g$ and $g'$ are conditionally independent, given $(tilde(g),J)$, and the proof concludes as in @lem_correlated_solve_prob.
]

// define p^res _"unstable" and p^res _"cond"
Let us slightly redefine $p^res _"unstable"$ and $p^res _"cond" (x)$ by
$
  p^res _"unstable" = 1 - PP(S_"stable" | S_"diff"), #h(5em)  p^res _"cond" (x) = 1 - PP(S_"cond" (x) | S_"diff").
$ <eq_def_lcd_punstablecond>
This is necessary as when $g=g'$, $S_"stable"$ always holds and $S_"cond" (x)$ always fails.
Note however that if we knew that $PP(S_"diff") = 1$, which is always the case for $g,g'$ being $(1-epsilon)$-correlated, these definitions agree with what we had in @eq_poly_fundamental.
Again, we can define $p^res _"cond"$ via @eq_def_pcond, i.e. as the maximum of $p^res _"cond" (x)$ over $Sigma_N$.

// fundamental equation
Now, by @lem_lcd_solve_disjoint, we know that for $x = alg(g)$, $PP(S_"solve",S_"stable",S_"cond" (x) |S_"diff") = 0$, so
$
  PP(S_"solve"|S_"diff") + PP(S_"stable"|S_"diff") + PP(S_"cond" (x)|S_"diff") <= 2.
$
Thus, rearranging and multiplying by $PP(S_"diff")$ gives
$
  PP(S_"solve",S_"diff") <= PP(S_"diff") dot (p^res_"unstable" + p^res_"cond") <= p^res_"unstable" + p^res_"cond".
$
Adding $PP(S_"solve",attach(tl: not, S_"diff")) <= 1-P(S_"diff")$
(so as to apply @lem_resampled_solve_prob) now lets us conclude
$
  (p^res_"solve")^2 <= PP(S_"solve") <= p^res_"unstable" + p^res_"cond" + (1 - PP(S_"diff"))
$ <eq_lcd_fundamental>

As before, our proof follows by showing that, for appropriate choices of $epsilon$ and $eta$, depending on $D$, $E$, and $N$, that $p^res _"unstable",p^res _"cond" = o(1)$. However, this also requires us to choose $epsilon >> 1/N$, so as to ensure that $g != g'$, as otherwise (a) $p^res _"cond"$ would be too large and (b) the $1-PP(S_"diff")$ term would fail to vanish.
This restriction on $epsilon$ limits us from showing hardness for algorithms with degree larger than $o(N)$, as we will see shortly.

As before, we can establish a conditional landscape obstruction for resampled instances via a first moment computation. Here, we need to condition on the resampled instance being different, as otherwise the probability in question can be made to be 1 if $x$ was chosen to solve $g$.

#proposition[Fundamental Estimate -- Resampled Case][
  Assume that $(g,g')$ are $(1-epsilon)$-resampled standard Normal vectors.
  Then, for any $x$ such that $(g',x)$ are conditionally independent given $g$,
  $
    p^res_"cond" (x) &= PP
    multiprobcond(
        g != g',
        exists x' in Soln(g') "such that",
        norm(x-x') <= 2sqrt(eta N),
    ) \
    &<= exp_2 (-E + 2 eta log_2 (1 / eta) N + O(1)).
  $ <eq_resampled_lowprob_disp>
] <prop_resampled_fundamental>
#proof[
  We follow the setup of proof of @prop_correlated_fundamental.
  For each $x'$ within distance $2 sqrt(eta N)$ of $x$, let
  $ I_(x') := I(x' in Soln(g')) = I(abs(inn(g',x')) <= 2^(-E)), $
  so that
  $
    p^res_"cond" (x) &=
    EE[ sum_(norm(x - x') <= 2sqrt(eta N)) EE[I_(x') | g, g != g'] ] \
    &= EE[ sum_(norm(x-x') <= 2sqrt(eta N)) PP(abs(inn(g',x')) <= 2^(-E) | g, g!= g') mid(|) g != g' ]
  $ <eq_resampled_firstmoment>

  Again, to bound the inner probability, let $tilde(g)$ be a Normal vector independent to $g$. Let $J subeq [N]$ be a random subset where each $i in J$ with probability $1-epsilon$, independently, so $g'$ can be represented as
  $g' = g_J + tilde(g)_([N] without J)$.
  For a fixed $x'$ and conditional on $(g,J)$, we know that $inn(tilde(g)_([N] without J),x')$ is $Normal(0,N-abs(J))$ and $inn(g_J,x')$ is deterministic. That is,
  $
    inn(g',x') | (g,J) ~ Normal(inn(g_J,x'), N - abs(J)).
  $
  Conditioning on $g!= g'$ is equivalent to conditioning on $abs(J)<N$, so $N-abs(J) >= 1$. Thus, applying @lem_normal_smallprob and integrating over all valid choices of $J$ gives
  $
    PP(abs(inn(g',x')) <= 2^(-E) | g, g!= g') <= exp_2 (-E + O(1)).
  $ <eq_resampled_lowprob>

  By @lem_hypercube_counting, the number of terms in the sum @eq_resampled_firstmoment is bounded by $exp_2 (2 eta log_2 (1 slash eta)N)$, so summing @eq_resampled_lowprob allows us to conclude @eq_resampled_lowprob_disp.
]

Note that in contrast to @prop_correlated_fundamental, this bound does not involve $epsilon$ at all, but the condition $g!= g'$ requires $epsilon = omega(1 slash N)$ to hold almost surely, by @lem_sdiff_prob.

// Linear case
With this, we can show strong low degree hardness for low coordinate degree algorithms at energy levels $E=Theta(N)$.As before, this corresponds to hardness at the statistically optimal energy regime, but now applies to an extremely broad category of algorithms.

// linear lcdf low degree hardness
#theorem[
  Let $E = delta N$ for $delta > 0$, and let $g,g'$ be $(1-epsilon)$-resampled standard Normal r.v.s.
  Then, for any algorithm $alg$ with $EE norm(alg(g))^2 <= C N$ and coordinate degree $D <= o(N)$, there exist $epsilon, eta > 0$ such that $p^res _"solve" = o(1)$.
] <thrm_sldh_lcd_linear>
#proof[
  Recall from @eq_lcd_fundamental that it suffices to show that both $p^res _"cond"$ and $p^res _"unstable"$ go to zero, while $PP(S_"diff") -> 1$.
  By @lem_sdiff_prob, the latter condition is satisfied for $epsilon = omega(1 slash N)$.
  Thus, pick
  $ epsilon = (log_2 (N slash D)) / N. $ <eq_def_lcd_epsilon>
  Note that this satisfies $N epsilon = log_2 (N slash D) >> 1$, for $D = o(N)$.
  Next, choose $eta$ such that $2 eta log_2 (1 slash eta) < delta slash 4$ -- again, this results in $eta$ being independent of $N$.
  As the bound in @prop_resampled_fundamental is independent of $x$, we get
  $
    p^res_"cond" <= exp_2 (- delta N + (delta N) / 4 + O(1) ) = o(1).
  $
  Moreover, for $D <= o(N)$, @prop_alg_stability now gives
  $
    p^res_"unstable" <= (C D epsilon) / (2 eta) asymp D dot (log_2 (N slash D)) / N -> 0.
  $
  //as $x log_2 (1 slash x) -> 0$ for $x << 1$.
  By @eq_lcd_fundamental, we conclude that $(p^res _"solve")^2 <= p^res _"unstable" + p^res _"cond" + (1 - P(S_"diff")) = o(1)$.
]

Finally, combining the ideas behind @thrm_sldh_poly_sublinear and our conditional landscape obstruction for $(1-epsilon)$-resampled Normal random variables, we can show hardness for algorithms with bounded coordinate degree at sublinear energy levels, ranging from $log^2 N << E << N$.
Here we have to increase our lower bound to $log^2 N$ as opposed to $log N$ from @thrm_sldh_poly_sublinear, to address the requirement that $epsilon=omega(1 slash N)$, but this still enables us to "close" the statistical-to-computational gap by proving hardness in this range.
Note also that our method also allows us to derive a clear tradeoff between solution energy and algorithm degree.

// sublinear lcdf low degree hardness
#theorem[
  Let $omega(log^2 N) <= E <= o(N)$, and let $g,g'$ be $(1-epsilon)$-resampled standard Normal r.v.s.
  Then, for any algorithm $alg$ with $EE norm(alg(g))^2 <= C N$ and coordinate degree $D <= o(E slash log^2 N)$, there exist $epsilon, eta > 0$ such that $p^res _"solve" = o(1)$.
] <thrm_sldh_lcd_sublinear>
#proof[
  The strategy is the same as in @thrm_sldh_lcd_linear.
  Start by choosing $epsilon$ as in @eq_def_lcd_epsilon, so that $epsilon=omega(1 slash N)$ and $PP(S_"diff") approx 1$.
  To account for $E <= o(N)$, we need to adjust $eta$ as $N -> infinity$;
  thus, choose $eta$ as in @eq_def_sublinear_epseta: this ensures $2 eta log_2(1 slash eta) < E slash 4 N$ for $E << N$.
  By @prop_resampled_fundamental, this guarantees that
  $
    p^res_"cond" <= exp_2 (- E + 2 eta log_2 (1 / eta) N + O(1) ) <= exp_2 (-(3 E) / 4 + O(1)) = o(1).
  $
  The low coordinate degree requirement $D <= o(E slash log^2 N)$ plus @prop_alg_stability now gives
  $
    p^res_"unstable" &<= (C D epsilon) / (2 eta)
    asymp (D epsilon N log_2 (N slash E)) / E \
    &= (D log_2 (N slash D) log_2 (N slash E)) / E
    <= (D (log_2 N)^2) / E = o(1).
  $
  We are now done by @eq_lcd_fundamental.
]

#remark[Tightness of Coordinate Degree Bounds][
  For any $E <= Theta(N)$, there is an easy method to achieve a discrepancy of $2^(-E)$ in $e^(O(E))$ time.
  #enum(
    [
      Pick a subset $J subeq[N]$ of $E$ coordinates.
    ],
    [
      Run LDM on the restricted NPP $g_overline(J)$ to find a partition $x_overline(J)$ with $inn(g_overline(J), x_overline(J)) <= 1$.
    ],
    [
      If we fix the values of $x_overline(J)$, the NPP given by $g$ turns into finding $x_J$ minimizing $abs(inn(g,x)) = abs(inn(g_J,x_J) + inn(g_overline(J), x_overline(J)))$. Note here that $inn(g,x)|(g_overline(J),x_overline(J)) ~ Normal(mu, E)$, for $mu=inn(g_overline(J), x_overline(J))$.
    ],
    [
      Given the statistical energy threshold is $Theta(N)$, we know $g$ has a solution with energy $E$ with high probability.
      Moreover, by the proof of @lem_normal_smallprob, the probability of any $x_J$ solving $g_J$ is independent of $O(1)$ constant shifts to the instance, so we can conclude that this restricted NPP also has an energy $E$ solution.
    ],
    [
      Thus, at this stage, we can brute force search over the remaining $J$ coordinates, which gives a solution with energy $E$ with high probability, in $e^(O(E))$ time.
    ],
  )
  In particular, this suggests that our results @thrm_sldh_lcd_linear and @thrm_sldh_lcd_sublinear are optimal under the low degree heuristic.
  Namely, low degree hardness of finding solutions with energy $E$ holds up to degree $tilde(o)(E)$, which implies finding such solutions requires at least time $e^(tilde(Omega)(E))$.
  This restricted brute force strategy shows that it is indeed possible to find these solutions in time $e^(tilde(O)(E))$, implying that our method gives the optimal energy/runtime tradeoff.
]

As a final remark, consider that an algorithm with coordinate degree $Omega(N)$ (which of course implies $cdeg alg = Theta(N)$) is one which considers nonlinear interactions between some constant fraction of all the coordinates as $N$ gets large.
Intuitively, this is an algorithm which is forced to look at how a large number of instance elements balance against each other, giving further evidence to the claim that any sufficiently local algorithm for the NPP will be no better than random search.
The good algorithms must be global, which reflects recent developments in heuristics for computing solutions to the NPP @kraticaTwoMetaheuristicApproaches2014 @corusArtificialImmuneSystems2019 @santucciImprovedMemeticAlgebraic2021.
