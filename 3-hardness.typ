#import "environments.typ": *

#import "symbols.typ": *

= Proof of Strong Low-Degree Hardness <section_hardness>

In this section, we prove strong low degree hardness for both low degree polynomial algorithms and algorithms with low Efron-Stein degree.

For now, we consider $Sigma_N$-valued deterministic algorithms.
We discuss the extension to $RR^N$-valued algorithms in @section_rounding.
As outlined in @subsection_intro_results, we show that TODO.

// TODO - talk about what's going on here
The key argument is as follows.
Fix some energy levels $E$, depending on $N$.
Suppose we have a $Sigma_N$-valued, deterministic algorithm $alg$ given by a degree $D$ polynomial (resp. an Efron-Stein degree $D$ function), and we have two instances $g,g'~stdnorm$ which are $(1-epsilon)$-correlated (resp. $(1-epsilon)$-resampled), for $epsilon>0$.
Say $alg(g)=x in Sigma_N$ is a solution with energy at least $E$, i.e. it "solves" this NPP instance.
For $epsilon$ close to 0, $alg(g')=x'$ will be close to $x$, by low degree stability.
However, by adjusting parameters carefully, we can make it so that with high probability (exponential in $E$), there are no solutions to $g'$ close to $x$.
By application of a correlation bound on the probability of solving any fixed instance, we can conclude that with high probability, $alg$ can't find solutions to NPP with energy $E$.

Our argument utilizes what can be thought of as a "conditional" version of the overlap gap property.
Traditionally, the overlap gap property is a global obstruction: one shows that with high probability, one cannot find a tuple of good solutions to a family of correlated instances which are all roughly the same distance apart.
Here, however, we show a local obstruction - we condition on being able to solve a single instance, and show that after a small change to the instance, we cannot guarantee any solutions will exist close to the first one.
This is an instance of the "brittleness," so to speak, that makes NPP so frustrating to solve; even small changes in the instance break the landscape geometry, so that even if solutions exist, there's no way to know where they'll end up.

First moment details meow.
// TODO - discuss that this is first moment computation, as opposed to a second moment one in which we consider pairs of solutions

We start with some setup which will apply, with minor modifications depending on the nature of the algorithm in consideration, to all of the energy regimes in discussion.
After proving some preliminary estimates, we establish the existence of our conditional landscape obstruction, which is of independent interest.
Finally, we conclude by establishing low degree hardness in both the linear and sublinear energy regimes.


Explain more meow.


== Hardness for Low Degree Polynomial Algorithms

// Degree $D$ polynomials

First, consider the case of $alg$ being a polynomial algorithm with degree $D$.

Let $g,g'$ be $(1-epsilon)$-correlated standard Normal r.v.s, and let $x in Sigma_N$ depend only on $g$.
Furthermore, let $eta>0$ be a parameter which will be chosen in a manner specified later.
We define the following events:
$
  S_"solve" &= {alg(g) in Soln(g), alg(g') in Soln(g')} \
  S_"stable" &= {norm(alg(g) - alg(g')) <= 2 sqrt(eta N) } \
  S_"cond" (x) &= multiset(
    exists.not x' in Soln(g') "such that",
    norm(x-x') <= 2sqrt(eta N),
  )
$ <eq_poly_events>

Intuitively, the first two events ask that the algorithm solves both instances and is stable, respectively.
The last event, which depends on $x$, corresponds to the conditional landscape obstruction: for an $x$ depending only on $g$, there is no solution to $g'$ which is close to $x$.

#lemma[
  We have, for $x := alg(g)$, $S_"solve" inter S_"stable" inter S_"cond" (x) = emptyset$.
] <lem_solve_disjoint>
#proof[
  Suppose that $S_"solve"$ and $S_"stable"$ both occur.
  Letting $x:=alg(g)$ (which only depends on $g$) and $x':=alg(g')$, we have that $x' in Soln(g')$ while also being within distance $2 sqrt(eta N)$ of $x$.
  This contradicts $S_"cond" (x)$, thus completing the proof.
]

First, define $p^cor _"solve"$ as the probability that the algorithm solves a single random instance:
$ p^cor_"solve" = PP(alg(g) in Soln(g)). $ <eq_def_psolve>
Then, we have the following correlation bound, which allows us to avoid union bounding over instances:

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

// TODO: should we rearrange this?

Moreover, let us define $p^cor _"unstable"$ and $p^cor _"cond" (x)$ by
$
  p^cor _"unstable" = 1 - PP(S_"stable"), #h(5em)  p^cor _"cond" (x) = 1 - PP(S_"cond" (x)).
$
In addition, define
$ p^cor_"cond" := max_(x in Sigma_N) p^cor_"cond" (x). $ <eq_def_pcond>
By @lem_solve_disjoint, we know that for $x := alg(g)$
$ PP(S_"solve") + PP(S_"stable") + PP(S_"cond" (x)) <= 2, $
and rearranging, we get that
$ (p^cor_"solve")^2 <= p^cor_"unstable" + p^cor_"cond" $ <eq_poly_fundamental>
Our proof follows by showing that, for appropriate choices of $epsilon$ and $eta$, depending on $D$, $E$, and $N$, we have $p^cor _"unstable",p^cor _"cond" = o(1)$.

To this end, we start by bounding the size of neighborhoods on $Sigma_N$.

#proposition[Hypercube Neighborhood Size][
  Fix $x in Sigma_N$, and let $eta <= 1 slash 2$. Then the number of $x'$ within distance $2 sqrt(eta N)$ of $x$ is
  $
    abs({x' in Sigma_N : norm(x-x') <= 2eta sqrt(N)})
    <= exp_2 (2 eta log_2 (1 slash eta)N )
  $
] <lem_hypercube_counting>
#proof[
  Let $k$ be the number of coordinates which differ between $x$ and $x'$ (i.e. the Hamming distance).
  We have $norm(x-x')^2=4k$, so $norm(x-x') <= 2 sqrt(eta N)$ iff $k <= N eta$.
  Moreover, for $eta <= 1/2$, $k <= N/2$.
  Thus, by @lem_chernoff_hoeffding, we get
  $
    sum_(k <= N eta) binom(N,k) <= exp_2 (N h(eta))
    <= exp_2 (2 eta log_2 (1 slash eta)N ). #qedhere
  $
]

This shows that within a small neighborhood of any $x in Sigma_N$, the number of nearby points is exponential in $N$, with a more nontrivial dependence on $eta$. The question is how many of these are solutions to a correlated/resampled instance.

First, we consider the conditional probability of any fixed $x in Sigma_N$ solving a $(1-epsilon)$-correlated problem instance $g'$, given $g$:

Putting together these bounds, we conclude the following fundamental estimates of $p^cor _"cond"$, i.e. of the failure of our conditional landscape obstruction.

#proposition[Fundamental Estimate -- Correlated Case][
  Assume that $(g,g')$ are $(1-epsilon)$-correlated standard Normal vectors. Then, for any $x$ only depending on $g$,
  $
    p^cor_"cond" (x) := PP multiprob(
      exists x' in Soln(g') "such that",
      norm(x-x') <= 2sqrt(eta N),
    ) <= exp_2(-E -1 / 2 log_2(epsilon) + 2 eta log_2(1 / eta) N + O(log_2 N)).
  $
] <prop_correlated_fundamental>
#proof[
  For each $x'$ within distance $2 sqrt(eta N)$ of $x$, let
  $ I_(x') := I(x in Soln(g')) = I(abs(inn(g',x')) <= 2^(-E)), $
  so that
  $
    p^cor_"cond" (x) =
    EE[ sum_(norm(x - x') <= 2sqrt(eta N)) EE[I_(x') | g] ]
    = EE[ sum_(norm(x-x') <= 2sqrt(eta N)) PP(abs(inn(g',x')) <= 2^(-E) | g) ]
  $ <eq_correlated_firstmoment>

  To bound the inner probability, let $tilde(g)$ be a Normal vector independent to $g$ and set $p = 1-epsilon$.
  Observe that $g'$ can be represented as $g' = p g + sqrt(1-p^2)tilde(g)$,
  so, $inn(g',x') = p inn(g,x') + sqrt(1-p^2)inn(tilde(g),x')$.
  We know $inn(tilde(g),x')~ Normal(0,N)$, so conditional on $g$, we have $inn(g',x') | g ~ Normal(p inn(g,x'), (1-p^2)N)$.
  Note that $inn(g',x')$ is nondegenerate for $(1-p^2) N >= epsilon N > 0$; thus by @lem_normal_smallprob, we get
  $
    PP(abs(inn(g',x')) <= 2^(-E) | g) <= exp_2 (-E - 1 / 2 log_2 (epsilon) + O(log_2 N)).
  $ <eq_correlated_lowprob>

  Finally, by @lem_hypercube_counting, the number of terms in the sum @eq_correlated_firstmoment is bounded by $exp_2 (2 eta log_2 (1 slash eta)N)$, so given that @eq_correlated_lowprob is independent of $g$, we conclude that
  $
    p^cor _"cond" (x) <= exp_2 (-E + -1/2 log_2 (epsilon) + 2 eta log_2 (1 / eta) N + O(log_2 N)). #qedhere
  $
]

Note for instance that $epsilon$ can be exponentially small in $E$ (e.g. $epsilon = exp_2 (-E slash 10)$), which for the case $E = Theta(N)$ implies $epsilon$ can be exponentially small in $N$.

Transition para meow.

Throughout this section, we let $E= delta N$ for some $delta > 0$, and aim to rule out the existence of low degree algorithms achieving these energy levels.
This corresponds to the statistically optimal regime, as per @karmarkarProbabilisticAnalysisOptimum1986.
These results roughly correspond to those in @gamarnikAlgorithmicObstructionsRandom2021b[Thm. 3.2], although their result applies to stable algorithms more generally, and does not show a low degree hardness-type result.

// linear poly low degree hardness
#theorem[
  Let $delta > 0$ and $E = delta N$, and let $g,g'$ be $(1-epsilon)$-correlated standard Normal r.v.s.
  Then, for any degree $D <= o(exp_2 (delta N slash 2))$ polynomial algorithm $alg$ (with $EE norm(alg(g))^2 <= C N$), there exist $epsilon, eta > 0$ such that $p^cor _"solve" = o(1)$.
] <thrm_sldh_poly_linear>
#proof[
  Recall from @eq_poly_fundamental that it suffices to show that both $p^cor _"cond"$ and $p^cor _"unstable"$ go to zero.
  Further, by @eq_def_pcond and @prop_correlated_fundamental, we have
  $
    p^cor_"cond" <= exp_2 (-E - 1 / 2 log_2 (epsilon) + 2 eta log_2 (1 / eta) N + O(log_2 N))
  $
  Thus, first choose $eta$ sufficiently small, such that $2 eta log_2 (1 slash eta) < delta slash 4$ -- this results in $eta$ being independent of $N$.
  Next, choose $epsilon = exp_2 (- delta N slash 2)$. This gives
  $
    p^cor_"cond" <= exp_2 (- delta N - 1 / 2 (-(delta N) / 2) + (delta N) / 4 + O(log_2 N)) = exp_2 (- (delta N) / 2 + O(log_2 N)) = o(1).
  $
  Moreover, for $D <= o(exp_2 (delta N slash 2))$, we get by @prop_alg_stability that
  $
    p^cor_"unstable" <= (C D epsilon) / (2 eta) asymp (D epsilon) / eta asymp D dot exp_2 (- (delta N) / 2) -> 0.
  $
  By @eq_poly_fundamental, we conclude that $(p^cor _"solve")^2 <= p^cor _"unstable" + p^cor _"cond" = o(1)$, thus completing the proof.
]

Remark that this implies poly algs are really bad, requiring ~double exponential time. meow.

Next, we let $omega(log_2  N ) <= E <= o(N)$.

// sublinear poly low degree hardness
#theorem[
  Let $omega(log_2 ^2 N) <= E <= o(N)$, and let $g,g'$ be $(1-epsilon)$-correlated standard Normal r.v.s.
  Then, for any polynomial algorithm $alg$ with degree $D <= o(exp_2 (E slash 4))$ (and with $EE norm(alg(g))^2 <= C N$), there exist $epsilon, eta > 0$ such that $p^cor _"solve" = o(1)$.
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
    p^cor_"cond" &<= exp_2 (-E - 1 / 2 log_2 (epsilon) + 2 eta log_2 (1 / eta) N + O(log_2 N)) \
    &<= exp_2 (-E + E / 4 + E / 4 + O(log_2 N)) = exp_2 (-E / 2 + O(log_2 N)) = o(1).
  $
  where the last equality follows as $E >> log_2  N$.
  Then, by @prop_alg_stability, the choice of $D = o(exp_2 (E slash 4))$ gives
  $
    p^cor_"unstable" &<= (C D epsilon) / (2 eta)
    asymp (D epsilon N log_2 (N slash E)) / E \
    &= (D exp_2 (-E slash 2) N log_2 (N slash E)) / E
    <= (D exp_2 (-E slash 2) N log_2 (N)) / E \
    &<= D exp_2 (-E / 2 + log_2 (N) + log_2 log_2 (N) - log_2 (E)) \
    &<= exp_2 (-E / 4 + log_2 (N) + log_2 log_2 (N) - log_2 (E)) = o(1),
  $
  again, as $E >> log_2  N$.
  Ergo, by @eq_poly_fundamental, $(p^cor _"solve")^2 <= p^cor _"unstable" + p^cor _"cond" = o(1)$, as desired.
]

== Proof for Low Coordinate-Degree Algorithms <section_hardness_lcd>

// Degree $D$ functions

Next, let $alg$ have coordinate degree $D$.
We now want $g,g'$ to be $(1-epsilon)$-resampled standard Normals. We define the following events.
$
  S_"diff" &= { g != g'} \
  S_"solve" &= {alg(g) in Soln(g), alg(g') in Soln(g')} \
  S_"stable" &= {norm(alg(g) - alg(g')) <= 2 sqrt(eta N) } \
  S_"cond" (x) &= multiset(
    exists.not x' in Soln(g') "such that",
    norm(x-x') <= 2sqrt(eta N),
  )
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

We should interpret this as saying $S_"solve", S_"stable", S_"cond"$ are all mutually exclusive, conditional on $g != g'$.

The previous definition of $p^cor _"solve"$ in @eq_def_psolve, which we now term $p^res _"solve"$, remains valid. In particular, we have

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
Thus, rearranging and multiplying by $PP(S_"diff")$ (so as to apply @lem_resampled_solve_prob) gives
$
  (p^res_"solve")^2 <= PP(S_"diff") dot (p^res_"unstable" + p^res_"cond")
$ <eq_lcd_fundamental>

As before, our proof follows by showing that, for appropriate choices of $epsilon$ and $eta$, depending on $D$, $E$, and $N$, that $p^res _"unstable",p^res _"cond" = o(1)$. However, this also requires us to choose $epsilon >> 1/N$, so as to ensure that $g != g'$, as otherwise $p^res _"unstable",p^res _"cond"$ would be too large. This restriction on $epsilon$ effectively limits us from showing hardness for algorithms with degree larger than $o(N)$, as we will see shortly.

First, we bound the same probability of a fixed $x$ solving a resampled instance. Here, we need to condition on the resampled instance being different, as otherwise the probability in question can be made to be 1 if $x$ was chosen to solve $g$.

#proposition[Fundamental Estimate -- Resampled Case][
  Assume that $(g,g')$ are $(1-epsilon)$-resampled standard Normal vectors. Then, for any $x$ only depending on $g$,
  $
    p^res_"cond" (x) = PP
    multiprobcond(
        g != g',
        exists x' in Soln(g') "such that",
        norm(x-x') <= 2sqrt(eta N),
    ) <= exp_2 (-E + 2 eta log_2 (1 / eta) N + O(1)).
  $
] <prop_resampled_fundamental>
#proof[
  We follow the setup of proof of @prop_correlated_fundamental.
  For each $x'$ within distance $2 sqrt(eta N)$ of $x$, let
  $ I_(x') := I(x in Soln(g')) = I(abs(inn(g',x')) <= 2^(-E)), $
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

  By @lem_hypercube_counting, the number of terms in the sum @eq_resampled_firstmoment is bounded by $exp_2 (2 eta log_2 (1 slash eta)N)$, so summing @eq_resampled_lowprob allows us to conclude that
  $
    p^res _"cond" (x) <= exp_2 (-E + 2 eta log_2 (1 / eta) N + O( 1 )). #qedhere
  $
]

Note that in contrast to @prop_correlated_fundamental, this bound doesn't involve $epsilon$ at all, but the condition $g!= g'$ requires $epsilon = omega(1 slash N)$ to hold almost surely, by @lem_sdiff_prob.

// Linear case
With this, we can show strong low degree hardness for low coordinate degree algorithms at energy levels $E=Theta(N)$.

// linear lcdf low degree hardness
#theorem[
  Let $delta > 0$ and $E = delta N$, and let $g,g'$ be $(1-epsilon)$-resampled standard Normal r.v.s.
  Then, for any algorithm $alg$ with coordinate degree $D <= o(N)$ and $EE norm(alg(g))^2 <= C N$, there exist $epsilon, eta > 0$ such that $p^res _"solve" = o(1)$.
] <thrm_sldh_lcd_linear>
#proof[
  Recall from @eq_lcd_fundamental that it suffices to show that both $p^res _"cond"$ and $p^res _"unstable"$ go to zero, while $PP(S_"diff") approx 1$.
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
    p^res_"unstable" <= (C D epsilon) / (2 eta) asymp D dot (log_2 (N slash D)) / N -> 0,
  $
  as $x log_2 (1 slash x) -> 0$ for $x << 1$.
  By @eq_lcd_fundamental, we conclude that $(p^res _"solve")^2 <= PP(S_"diff")dot (p^res _"unstable" + p^res _"cond") = o(1)$, thus completing the proof.
]

Sublinear case. We now consider sublinear energy levels, ranging from $(log_2 N)^2 << E << N$. Note here that we have to increase our lower bound to $(log_2 N)^2$ as opposed to $log_2 N$ from @thrm_sldh_poly_sublinear, to address the requirement that $epsilon=omega(1 slash N)$.

// sublinear lcdf low degree hardness
#theorem[
  Let $omega((log_2 N)^2) <= E <= o(N)$, and let $g,g'$ be $(1-epsilon)$-resampled standard Normal r.v.s.
  Then, for any algorithm $alg$ with coordinate degree $D <= o(E slash (log_2 N)^2)$ and $EE norm(alg(g))^2 <= C N$,
  there exist $epsilon, eta > 0$ such that $p^res _"solve" = o(1)$.
] <thrm_sldh_lcd_sublinear>
#proof[
  As in @thrm_sldh_lcd_linear, choose $epsilon$ as in @eq_def_lcd_epsilon, so that $epsilon=omega(1 slash N)$ and $PP(S_"diff") approx 1$.
  However, to account for $E <= o(N)$, we need to adjust $eta$ as $N -> infinity$.
  Thus, choose $eta$ as in @eq_def_sublinear_epseta: this ensures that $epsilon = omega(1 slash N)$ and that $2 eta log_2(1 slash eta) < E slash 4 N$ for $E << N$.
  By @prop_resampled_fundamental, this guarantees that
  $
    p^res_"cond" <= exp_2 (- E + 2 eta log_2 (1 / eta) N + O(1) ) <= exp_2 (-(3 E) / 4 + O(1)) = o(1).
  $
  The low coordinate degree requirement $D <= o(E slash (log_2 N)^2)$ plus @prop_alg_stability now gives
  $
    p^res_"unstable" &<= (C D epsilon) / (2 eta)
    asymp (D epsilon N log_2 (N slash E)) / E \
    &= (D log_2 (N slash D) log_2 (N slash E)) / E
    <= (D (log_2 N)^2) / E = o(1).
  $
  By @eq_lcd_fundamental, $(p^res _"solve")^2 <= PP(S_"diff")dot (p^res _"unstable" + p^res _"cond") = o(1)$, thus completing the proof.
]

== Summary of Parameters

#figure(
  table(
    columns: 4,
    fill: (_, y) => if calc.odd(y) { rgb("EAF2F5") },
    stroke: none,
    table.hline(),
    [*Parameter*], [*Meaning*], [*Desired Direction*], [*Intuition*],
    table.hline(),
    [$N$], [Dimension],
    [Large], [Showing hardness _asymptotically_, want "bad behavior" to pop up in low dimensions.],

    [$E$], [Solution energy; want to find $x$ such that $abs(inn(g,x)) <= 2^(-E)$],
    [Small], [Smaller $E$ implies weaker solutions, and can consider full range of $1 << E << N$. Know that $E>(log^2 N)$ by @karmarkerDifferencingMethodSet1983],

    [$D$], [Algorithm degree (in either Efron-Stein sense or usual polynomial sense.)],
    [Large], [Higher degree means more complexity. Want to show even complex algorithms fail.],

    [$epsilon$], [Complement of correlation/resample probability; (g,g') are $(1-epsilon)$-correlated.],
    [Small], [$epsilon$ is "distance" between $g,g'$. Want to show that small changes in disorder lead to "breaking" of landscape.],

    [$eta$], [Algorithm instability; $alg$ is stable if $norm(alg(g) - alg(g')) <= 2 sqrt(eta N)$, for $(g,g')$ close.],
    [Large], [Large $eta$ indicates a more unstable algorithm; want to show that even weakly stable algorithms fail. ],

    table.hline(),
  ),
  caption: [Explanation of Parameters],
) <parameter_table>

