#import "environments.typ": *

#import "symbols.typ": *

= Conditional Landscape Obstruction

Explain what the obstruction is.

We start with a bound on the geometry of the binary hypercube.

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


#lemma([Hypercube Neighborhood Size])[
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


Next, we can consider what this probability is in the case of correlated Normals.

#lemma[Suppose $(g,g')$ are $(1-epsilon)$-correlated Normal vectors, and let $x in Sigma_N$. Then
  $ PP(abs(inn(g',x)) <= 2^(-E) | g) <= exp(-E - 1/2 log(epsilon) + O(log N)). $
] <correlated_solution_lowprob>
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

Note for instance that here $epsilon$ can be exponentially small in $E$ (e.g. $epsilon = exp(-E slash 10)$), which for the case $E=Theta(N)$ implies $epsilon$ can be exponentially small in $N$.

// Efron-Stein case

First, we consider the probability of a solution being optimal for a resampled instance.


#lemma[Suppose $(g,g')$ are $(1-epsilon)$-resampled Normal vectors, and let $x in Sigma_N$. Then,
  $ PP(abs(inn(g',x)) <= 2^(-E) | g, g != g') <= 2^(-E + O(1)). $
] <resampled_solution_lowprob>
#proof[
  Let $S={ i in [N] : g_i != g'_i}$ be the set of indices where $g$ and $g'$ differ. We can express
  $
    inn(g',x') = sum_(i in [N]) g'_i x_i = sum_(i in.not S)g_i x_i + sum_(i in S) g_i' x_i ~ Normal(sum_(i in.not S)g_i x_i, abs(S)).
  $
  Let $mu := sum_(i in.not S) g_i x_i$.
  The conditional distribution of interest can now be expressed as
  $PP(abs(inn(g',x')) <= 2^(-E) | g, abs(S)>= 1)$.
  Given $abs(S) >= 1$, the quantity $inn(g',x')$ is a nondegenerate random variable, with density bounded above as
  $
    phi_(g,abs(S))(z) = 1 / (sqrt(2pi abs(S)) )e^(- (z - mu)^2 / (2abs(S))) <= 1 / sqrt(2 pi abs(S)) <= 1 / sqrt(2 pi).
  $
  Hence, the quantity of interest can be bounded as
  $
    PP(abs(inn(g',x)) <= 2^(-E) | g, g != g') <= integral_(abs(z)<=-2^(-E)) phi_(g,abs(S))(z) dif z <= sqrt(2/pi) 2^(-E) = 2^(-E + O(1)). #qedhere
  $
]

Note that in the resampled case, we can compute the probability that $g=g'$ as
$ PP(g=g') = product_(i=1)^N PP(g_i = g_i') = (1-epsilon)^N, $
which for $epsilon << 1$ is approximately $1-N epsilon$. Thus, for $epsilon >> omega(1/N)$, we have
$ PP(abs(inn(g',x)) <= 2^(-E) | g) <= 2^(-E + O(1)) $



= Proof of Strong Low-Degree Hardness <section_proof>

Broad setup




Throughout this section, we let $E=delta N$ for some $delta > 0$, and aim to rule out the existence of low-degree algorithms achieving these energy levels.
This corresponds to the statistically optimal regime, as per @karmarkarProbabilisticAnalysisOptimum1986.

For now, let $alg$ denote a $Sigma_N$-valued deterministic algorithm.
We discuss the extension to random, $RR^N$-valued algorithms later on in (section ???).

// Assume for sake of contradiction that $p_"solve" >= Omega(1)$.

Setup
Let $g,g'$ be $(1-epsilon)$-correlated instances. We define the following events:
$
  S_"diff" &= { g != g'} \
  S_"solve" &= {alg(g) in Soln(g), alg(g') in Soln(g')} \
  S_"stable" &= {norm(alg(g) - alg(g')) <= 2 sqrt(eta N) } \
  // S_"ogp" &= {"for" x "depending only on" g, exists x' in Soln(g') "such that" norm(x-x') <= eta sqrt(N) } \
  S_"cond" &= multiset(
    exists.not x' in Soln(g') "such that",
    norm(x-x') <= 2sqrt(eta N),
  )
$



In this case, set $epsilon = 2^(-delta N)=o(1)$

#lemma[
  There exists an $eta > 0$ of constant order such that
  $ PP(S_"cond") >= 1 - e^(-c N) $
  for an arbitrary constant $c$.
]

$D=o(2^N)$.

$D epsilon = D / 2^N * 2^((1-delta)N)$


#lemma[
  For any $omega(log^2 N) <= E <= Theta(N)$, there exist choices of $epsilon,eta$ (depending on $N, E$) such that
  $PP(S_"ogp")=o(1)$.
]
// Efron-Stein case first
#proof[
  Observe that
  $ PP(S_"ogp") = EE[PP(S_"ogp" | g)]. $ <meow>
  Conditional on $g$, we can compute $PP(S_"ogp" | g) = PP(exists x' in S(E;g'), norm(x-x') <= 2eta sqrt(N))$ by setting $x=alg(g)$ (so $x$ only depends on $g$), and union bounding @resampled_solution_lowprob over the $x'$ within $2eta sqrt(N)$ of $x$, as per @lem_hypercube_counting:
  $ PP(S_"ogp" | g) <= exp_2(-E + N eta^2 log_2(1 slash eta^2) + O(1)). $
  We want to choose $eta$ such that
  $ -E + N eta^2 log_2(1 slash eta^2) = -Omega(N) $ // or omega(1)
  $ E / N > eta^2 log(1 slash eta^2) $
  Using the fact that $sqrt(2x) >= -x log_2 x$, it suffices to pick $eta^2$ with
  $ E / N > 2 eta, $
  so $eta^2 := E^2/(2 N^2)$ is a valid choice.


  By the choice of $eta^2 << (h^(-1))(delta) asymp 1$, this bound gives $PP(S_"ogp"|g) <= exp_2(-O(N))=o(1)$.
  Integrating over $g$ gives the overall bound.
]

When $C D epsilon N^2 = omega_N(1)$ (i.e. goes to infinity),

$
  PP(S_"stable") &<= (16C D epsilon N^2) / (16 eta^4 N^2) \
  &= (C D epsilon) / (eta^4) = (4 C D epsilon N^4) / (E^4)
$

$D epsilon to 0$ same as $D = o(1/epsilon)=o(N)$.




#lemma[
  $PP(S_"solve",S_"stable") <= PP(S_"ogp")=o(1)$.
]
#proof[
  The first inequality follows from definition, with $x=alg(g)$ and $x'=alg(g')$. For the second, observe that
  $ PP(S_"ogp") = EE[PP(S_"ogp" | g)]. $
  Now, let $M=delta N$, we can compute $PP(S_"ogp" | g) = PP(exists x' in S(delta;g'), norm(x-x') <= eta sqrt(N))$ by setting $x=alg(g)$ (so $x$ only depends on $g$), and union bounding @resampled_solution_lowprob over the $x'$ within $eta sqrt(N)$ of $x$, as per @lem_hypercube_counting:
  $ PP(S_"ogp" | g) <= exp_2(-delta N + N h(eta^2 / 4) + O(log_2 N)). $
  By the choice of $eta^2 << (h^(-1))(delta) asymp 1$, this bound gives $PP(S_"ogp"|g) <= exp_2(-O(N))=o(1)$.
  Integrating over $g$ gives the overall bound.
]

However, by the choice of parameters above, we also have
$
  PP(S_"solve", S_"stable") &>= PP(S_"solve") + PP(S_"stable") - 1 \
  &>= p_"solve"^4 + p_"unstable" >= Omega(1) - o(1) = Omega(1),
$ <eq_contra>
which is a contradiction.


