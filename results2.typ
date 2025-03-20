#import "environments.typ": *

#import "symbols.typ": *

// TODO:
// - Write theorems explaining the actual results
// - Finish algorithms section

= Proof of Strong Low-Degree Hardness

In this section, we prove strong low-degree hardness for both low-degree polynomial algorithms and algorithms with low Efron-Stein degree.

For now, we consider $Sigma_N$-valued deterministic algorithms.
We discuss the extension to random, $RR^N$-valued algorithms later on in (section ???).
As outlined in @subsection_intro_results,

The key argument is as follows.
Fix some energy levels $E$, depending on $N$.
Suppose we have a $Sigma_N$-valued, deterministic algorithm $alg$ given by a degree $D$ polynomial (resp. an Efron-Stein degree $D$ function), and we have two instances $g,g'~stdnorm$ which are $(1-epsilon)$-correlated (resp. $(1-epsilon)$-resampled), for $epsilon>0$.
Say $alg(g)=x in Sigma_N$ is a solution with energy at least $E$, i.e. it "solves" this NPP instance.
For $epsilon$ close to 0, $alg(g')=x'$ will be close to $x$, by low-degree stability.
However, by adjusting parameters carefully, we can make it so that with high probability (exponential in $E$), there are no solutions to $g'$ close to $x$.
By application of a correlation bound on the probability of solving any fixed instance, we can conclude that with high probability, $alg$ can't find solutions to NPP with energy $E$.

Our argument utilizes what can be thought of as a "conditional" version of the overlap gap property.
Traditionally, the overlap gap property is a global obstruction: one shows that with high probability, one cannot find a tuple of good solutions to a family of correlated instances which are all roughly the same distance apart.
Here, however, we show a local obstruction - we condition on being able to solve a single instance, and show that after a small change to the instance, we cannot guarantee any solutions will exist close to the first one.
This is an instance of the "brittleness," so to speak, that makes NPP so frustrating to solve; even small changes in the instance break the landscape geometry, so that even if solutions exist, there's no way to know where they'll end up.

We start with some setup which will apply, with minor modifications depending on the nature of the algorithm in consideration, to all of the energy regimes in discussion.
After proving some preliminary estimates, we establish the existence of our conditional landscape obstruction, which is of independent interest.
Finally, we conclude by establishing low-degree hardness in both the linear and sublinear energy regimes.

== Proof Outline and Preliminary Estimates

// Degree $D$ polynomials

First, consider the case of $alg$ being a polynomial algorithm with degree $D$.

Let $g,g'$ be $(1-epsilon)$-correlated standard Normal r.v.s, and let $x in Sigma_N$ depend only on $g$. Furthermore, let $eta>0$ be a parameter which will be chosen in a manner specified later.
We define the following events:
$
  S_"solve" &= {alg(g) in Soln(g), alg(g') in Soln(g')} \
  S_"stable" &= {norm(alg(g) - alg(g')) <= 2 sqrt(eta N) } \
  S_"cond" &= multiset(
    exists.not x' in Soln(g') "such that",
    norm(x-x') <= 2sqrt(eta N),
  )
$ <eq_poly_events>

Intuitively, the first two events ask that the algorithm solves both instances and is stable, respectively.
The last event corresponds to the conditional landscape obstruction: for an $x$ depending only on $g$, there is no solution to $g'$ which is close to $x$.

#lemma[
  We have $S_"solve" inter S_"stable" inter S_"cond" = emptyset$.
] <lem_solve_disjoint>
#proof[
  Suppose that $S_"solve"$ and $S_"stable"$ both occur.
  Letting $x:=alg(g)$ (which only depends on $g$) and $x':=alg(g')$, we have that $x' in Soln(g')$ while also being within distance $2 sqrt(eta N)$ of $x$.
  This contradicts $S_"cond"$, thus completing the proof.
]

Define $p_"solve"$ as the probability that the algorithm solves a single instance:
$ p_"solve" = PP(alg(g) in Soln(g)). $
Then, we have the following correlation bound, which allows us to avoid union bounding over instances:

#lemma[
  For $g,g'$ being $(1-epsilon)$-correlated, we have
  $ PP(S_"solve") = PP(alg(g) in Soln(g), alg(g') in Soln(g')) >= p_"solve"^2 $
] <lem_solve_prob>
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
    &>= EE[ PP(alg(g) in Soln(g) | tilde(g))]^2 = p_"solve"^2,
  $
  where the last line follows by Jensen's inequality.
]

Moreover, let us define $p_"unstable"$ and $p_"cond"$ by
$ PP(S_"stable") = 1- p_"unstable" $
and
$ PP(S_"cond") = 1 - p_"cond". $
By @lem_solve_disjoint, we know that
$ PP(S_"solve") + PP(S_"stable") + PP(S_"cond") <= 2, $
and rearranging, we get that
$ p_"solve"^2 <= p_"unstable" + p_"cond" $ <eq_poly_fundamental>
Our proof follows by showing that, for appropriate choices of $epsilon$ and $eta$, depending on $D$, $E$, and $N$, we have $p_"unstable",p_"cond" = o(1)$.

// Degree $D$ functions

Next, let $alg$ be given by a function with Efron-Stein degree $D$.
We now want $g,g'$ to be $(1-epsilon)$-resampled standard Normals. We define the following events.
$
  S_"diff" &= { g != g'} \
  S_"solve" &= {alg(g) in Soln(g), alg(g') in Soln(g')} \
  S_"stable" &= {norm(alg(g) - alg(g')) <= 2 sqrt(eta N) } \
  S_"cond" &= multiset(
    exists.not x' in Soln(g') "such that",
    norm(x-x') <= 2sqrt(eta N),
  )
$ <eq_es_events>
Note that these are the same events as @eq_poly_events, along with an event to ensure that $g'$ is nontrivially resampled from $g$.

#lemma[
  We have $S_"diff" inter S_"solve" inter S_"stable" inter S_"cond" = emptyset$.
] <lem_es_solve_disjoint>
#proof[
  This follows from @lem_solve_disjoint, noting that the proof did not use that $g != g'$ almost surely.
]

In this case, we should interpret this as saying $S_"solve", S_"stable", S_"cond"$ are all mutually exclusive, conditional on $g != g'$.

#lemma[
  For $g,g'$ being $(1-epsilon)$-resampled,
  $PP(S_"diff") = 1 - (1-epsilon)^N <= epsilon N$.
]
#proof[
  Follows from calculation:
  $ PP(g=g') = product_(i=1)^N PP(g_i = g_i') = (1-epsilon)^N #qedhere $

]

The previous definition of $p_"solve"$ remains valid. In particular, we have

#lemma[
  For $g,g'$ being $(1-epsilon)$-resampled, we have
  $ PP(S_"solve") = PP(alg(g) in Soln(g), alg(g') in Soln(g')) >= p_"solve"^2 $
] <lem_es_solve_prob>
#proof[
  First, the statement is trivial if $g=g'$, as $p_"solve" <= 1$, so assume that $g != g'$.
  Let $tilde(g), g^((0)), g^((1))$ be three i.i.d. copies of $g$, and let $J$ be a random subset of $[N]$ where each coordinate is included with probability $1-epsilon$.
  Then, $g,g'$ are jointly representable as
  $
    g = tilde(g)_J + g^((0))_([N] without J), #h(5em)
    g' = tilde(g)_J + g^((1))_([N] without J)
  $
  where $tilde(g)_J$ denotes the vector with coordinates $tilde(g)_i$ if $i in J$ and 0 else.
  Thus $g$ and $g'$ are conditionally independent, given $(tilde(g),J)$, and the proof concludes as in @lem_solve_prob.
]

Let us slightly redefine $p_"unstable"$ and $p_"cond"$ by
$ PP(S_"stable" | S_"diff") = 1- p_"unstable" $
and
$ PP(S_"cond"|S_"diff") = 1 - p_"cond". $
This is necessary as $p_"unstable",p_"cond" = 1$ given $g=g'$. Note however that for $PP(S_"diff") = 1$, as is the case for $g,g'$ being $(1-epsilon)$-correlated, these definitions agree with what we had in @eq_poly_fundamental.

Now, by @lem_es_solve_disjoint, we know that $PP(S_"solve",S_"stable",S_"cond"|S_"diff") = 0$, so
$
  PP(S_"solve"|S_"diff") + PP(S_"stable"|S_"diff") + PP(S_"cond"|S_"diff") <= 2.
$
Thus, rearranging and multiplying by $PP(S_"diff")$ (so as to apply @lem_es_solve_prob) gives
$ p_"solve"^2 <= P(S_"diff") dot (p_"unstable" + p_"cond") $ <eq_es_fundamental>

As before, our proof follows by showing that, for appropriate choices of $epsilon$ and $eta$, depending on $D$, $E$, and $N$, that $p_"unstable",p_"cond" = o(1)$. However, this also requires us to choose $epsilon >> 1/N$, so as to ensure that $g != g'$, as otherwise $p_"unstable",p_"cond"$ would be too large. This restriction on $epsilon$ effectively limits us from showing hardness for algorithms with degree larger than $o(N)$, as we will see shortly.

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


== Conditional Landscape Obstruction <section_proof>

Our goal is to show that in both cases, whether we consider $g'$ correlated to or resampled from $g$,
$
  p_"cond" = PP(
  multiset(
    exists x' in Soln(g') "such that",
    norm(x-x') <= 2sqrt(eta N),
  ) mid(|) g != g'
) = o(1).
$
(Of course, the condition $g != g'$ is vacuously true for $(g,g')$ $(1-epsilon)$-correlated.

To this end, we start by bounding the size of neighborhoods on $Sigma_N$.

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

#proposition[Hypercube Neighborhood Size][
  Fix $x in Sigma_N$, and let $eta <= 1/2$. Then the number of $x'$ within distance $2 sqrt(eta N)$ of $x$ is
  $
    abs({x' in Sigma_N | norm(x-x') <= 2eta sqrt(N)})
    <= exp(2 eta log (1 slash eta)N )
  $
] <lem_hypercube_counting>
#proof[
  Let $k$ be the number of coordinates which differ between $x$ and $x'$ (i.e. the Hamming distance).
  We have $norm(x-x')^2=4k$, so $norm(x-x') <= 2 sqrt(eta N)$ iff $k <= N eta$.
  Moreover, for $eta <= 1/2$, $k <= N/2$.
  Thus, by @lem_chernoff_hoeffding, we get
  $
    sum_(k <= N eta) binom(N,k) <= exp(N h(eta))
    <= exp(2 eta log(1 slash eta)N ). #qedhere
  $
]

This shows that within a small neighborhood of any $x in Sigma_N$, the number of nearby points is exponential in $N$, with a more nontrivial dependence on $eta$. The question is how many of these are solutions to a correlated/resampled instance.

First, we consider the conditional probability of any fixed $x in Sigma_N$ solving a $(1-epsilon)$-correlated problem instance $g'$, given $g$:


#lemma[Suppose $(g,g')$ are $(1-epsilon)$-correlated standard Normal vectors, and let $x in Sigma_N$. Then
  $ PP(abs(inn(g',x)) <= 2^(-E) | g) <= exp(-E - 1/2 log(epsilon) + O(log N)). $
] <lem_correlated_solution_lowprob>
#proof[
  Let $tilde(g)$ be an independent Normal vector to $g$, and observe that $g'$ can be represented as
  $g' = p g + sqrt(1-p^2)tilde(g)$,
  for $p=1-epsilon$.
  Thus, $inn(g',x) = p inn(g,x) + sqrt(1-p^2)inn(tilde(g),x)$.
  Observe $inn(g,x)$ is constant given $g$, and $inn(tilde(g),x)$ is a Normal r.v. with mean 0 and variance $N$, so $inn(g',x) ~ Normal(p inn(g,x), (1-p^2)N)$.
  This random variable is nondegenerate for $(1-p^2)N > 0$, with density bounded above as
  $
    phi_(g)(z) &= 1 / (sqrt(2pi (1-p^2)N)) e^(- (z-p inn(g,x))^2 / (2(1-p^2)N)) <= 1 / sqrt(2 pi (1-p^2) N) \
    &<= 1 / sqrt(2 pi epsilon N) = exp (-1 / 2 log (epsilon) + O(log N))
  $
  Integrating this bound over the interval $abs(z) <= 2^(-E)$, we conclude that
  $
    PP(abs(inn(g',x)) <= 2^(-E) | g) = integral_(abs(z)<=-2^(-E)) phi_(g,abs(S))(z) dif z <= exp(-E - 1/2 log(epsilon) + O(log N)). #qedhere
  $
]

Note for instance that $epsilon$ can be exponentially small in $E$ (e.g. $epsilon = exp(-E slash 10)$), which for the case $E = Theta(N)$ implies $epsilon$ can be exponentially small in $N$.

Next, we bound the same probability of a fixed $x$ solving a resampled instance. Here, we need to condition on the resampled instance being different, as otherwise the probability in question can be made to be 1 if $x$ was chosen to solve $g$.

#lemma[Suppose $(g,g')$ are $(1-epsilon)$-resampled standard Normal vectors, and let $x in Sigma_N$. Then,
  $ PP(abs(inn(g',x)) <= 2^(-E) | g, g != g') <= exp(-E + O(1)). $
] <lem_resampled_solution_lowprob>
#proof[
  Let $S={ i in [N] : g_i != g'_i}$ be the set of indices where $g$ and $g'$ differ. We can express
  $
    inn(g',x) = sum_(i in [N]) g'_i x_i = sum_(i in.not S)g_i x_i + sum_(i in S) g_i' x_i ~ Normal(sum_(i in.not S)g_i x_i, abs(S)).
  $
  The conditional distribution of interest can now be expressed as
  $PP(abs(inn(g',x)) <= 2^(-E) | g, abs(S)>= 1)$.
  Given $abs(S) >= 1$, the quantity $inn(g',x')$ is a nondegenerate random variable, with density bounded above as
  $
    phi_(g,abs(S))(z) = 1 / (sqrt(2pi abs(S)) )e^(- (z - sum_(i in.not S)g_i x_i )^2 / (2abs(S))) <= 1 / sqrt(2 pi abs(S)) <= 1 / sqrt(2 pi).
  $
  Hence, the quantity of interest can be bounded as
  $
    PP(abs(inn(g',x)) <= 2^(-E) | g, g != g') <= integral_(abs(z)<=-2^(-E)) phi_(g,abs(S))(z) dif z <= sqrt(2/pi) exp(-E) = exp(-E + O(1)). #qedhere
  $
]

Note that in contrast to @lem_resampled_solution_lowprob, this bound doesn't involve $epsilon$ at all, but the condition $g!= g'$ requires $epsilon = omega(1 slash N)$ to hold w.p. 1.

Putting together these bounds, we conclude the following fundamental estimates of $p_"cond"$, i.e. of the failure of our conditional landscape obstruction.

#proposition[Fundamental Estimate -- Correlated Case][
  Assume that $(g,g')$ are $(1-epsilon)$-correlated standard Normal vectors. Then, for any $x$ only depending on $g$,
  $
    p_"cond" = PP(
      multiset(
        exists x' in Soln(g') "such that",
        norm(x-x') <= 2sqrt(eta N),
      )
    ) <= exp(-E + -1/2 log(epsilon) + 2 eta log(1 / eta) N + O(log N)).
  $
] <prop_correlated_fundamental>
#proof[
  Observe that
  $
    p_"cond" = EE[ PP( // attach(S_"cond", tl: not)
      multiset(
        exists x' "s.t.",
        (upright(I)) #h(0.45em) abs(inn(g',x')) <= exp(-E),
        (upright(I I)) #h(0.1em) norm(x-x') <= 2sqrt(eta N),
      )
      mid(|) g )].
  $
  Then, for fixed $x$, we know there are $exp(2 eta log(1 slash eta)N)$-many $x'$ satisfying condition (II), with each having an exponentially small probability of satisfying condition (I).
  Thus, we conclude by union bounding @lem_correlated_solution_lowprob (which is independent of $g$) over @lem_hypercube_counting.
]

By the same proof, using @lem_resampled_solution_lowprob instead of @lem_correlated_solution_lowprob, we show:

#proposition[Fundamental Estimate -- Resampled Case][
  Assume that $(g,g')$ are $(1-epsilon)$-resampled standard Normal vectors. Then, for any $x$ only depending on $g$,
  $
    p_"cond" = PP(
      multiset(
        exists x' in Soln(g') "such that",
        norm(x-x') <= 2sqrt(eta N),
      ) mid(|) g != g'
    ) <= exp(-E + 2 eta log(1 / eta) N + O(1)).
  $
] <prop_resampled_fundamental>

== Hardness in the Linear Energy Regime


== Hardness in the Sublinear Regime
