#import "@preview/ctheorems:1.1.3": *
#show: thmrules.with(qed-symbol: $square$)

#import "environments.typ": *

#import "@preview/equate:0.3.1": equate

// #show: equate.with(breakable: true, sub-numbering: true)
// #set math.equation(numbering: "(1.1)", supplement: "Eq.") // , supplement: (x) => [(#x.label)])
#set math.equation(
  supplement: none,
  numbering: (..nums) => numbering("(1.1)", ..nums),
)
#show math.equation: it => {
  if it.block and not it.has("label") [
    #counter(math.equation).update(v => v - 1)
    #math.equation(it.body, block: true, numbering: none)#label("")
  ] else {
    it
  }
}

// page layout
#set text(font: "Crimson Pro", size: 12pt)
#set page(
  paper: "us-letter",
  header: [
    Rushil Mallarapu
    #h(1fr) #datetime.today().display()
    // #line(length: 100%, stroke: 0.5pt)
  ],
  numbering: "1",
  number-align: bottom + right,
  margin: (x: 1in, y: 1in),
)

// 2 level math numbering
#set heading(numbering: "1.1.")
#show heading.where(level: 1): it => {
  counter(math.equation).update(0)
  it
}

#set math.equation(
  numbering: it => {
    let count = counter(heading.where(level: 1)).at(here()).first()
    if count > 0 {
      numbering("(1.1)", count, it)
    } else {
      numbering("(1)", it)
    }
  },
)

/// Math environments

#import "symbols.typ": *

= Number Packing Problem

Let $N$ be the dimensionality, and $Sigma_N := { plus.minus 1}$ be the binary cube.
Suppose we're given $g ~ #stdnorm$.
We want to find $x in Sigma_N$ such that we minimize $abs(inn(x, g))$.

#definition[
  Let $delta > 0$.
  The #emph[solution set] $S(delta;g)$ is the set of all $x in Sigma_N$ that are #emph[$delta$-optimal], satisfying
  $ 1 / sqrt(N) abs(inn(g,x)) <= 2^(-delta N). $ <eq_npp>
] <number_packing>

@eq_npp Hi


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


= Glossary and conventions

Conventions:
+ $log$ means $log$ in base 2, $exp$ is $exp$ base 2 - natural log/exponent is $ln$/$e^x$.
+

Glossary:
+ "instance"/"disorder" - $g$, instance of the NPP problem
+ "discrepancy" - for a given $g$, value of $min _(x in Sigma_N) abs(inn(g,x))$
+ "energy" - negative exponent of discrepancy, i.e. if discrepancy is $2^(-E)$, then energy is $E$. Lower energy indicates "worse" discrepancy.
+ "near-ground state"/"approximate solution"

#include "algorithms.typ"

= Summary of Parameters

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

    [$delta$], [Solution tightness; want to find $x$ such that $abs(inn(g,x)) <= 2^(-delta N)$],
    [Small], [Smaller $delta$ implies weaker solutions, e.g. $delta=0$ is just finding solutions $<= 1$. Want to show even weak solutions are hard to find.],

    [$E$], [Solution tightness; "energy level"; want to find $x$ such that $abs(inn(g,x)) <= 2^(-E)$],
    [Small], [Smaller $E$ implies weaker solutions, and can consider full range of $1 << E << N$. Know that $E>(log^2 N)$ by Karmarkar-Karp],

    [$D$], [Algorithm degree (in either Efron-Stein sense or usual polynomial sense.)],
    [Large], [Higher degree means more complexity. Want to show even complex algorithms fail.],

    [$epsilon$], [Complement of correlation/resample probability; (g,g') are $(1-epsilon)$-correlated.],
    [Small], [$epsilon$ is "distance" between $g,g'$. Want to show that small changes in disorder lead to "breaking" of landscape.],

    [$eta$], [Algorithm instability; $alg$ is stable if $norm(alg(g) - alg(g')) <= eta sqrt(N)$, for $(g,g')$ $(1-epsilon)$-correlated.],
    [Large], [Large $eta$ indicates a more unstable algorithm; want to show that even weakly stable algorithms fail. ],

    table.hline(),
  ),
  caption: [Explanation of Parameters],
) <parameter_table>

= Conditional Landscape Obstruction

We start with a bound on the geometry of the binary hypercube.

#lemma[
  Fix $x in Sigma_N$. Then, the number of $x'$ within distance $eta sqrt(N)$ of $x$ is
  $
    abs({x' in Sigma_N | norm(x-x') <= eta sqrt(N)})=exp_2(N h(eta^2 / 4) + O(log_2 N)),
  $
  where $h(x)=x log_2(1/x) + (1-x) log_2(1/(1-x))$ is the binary entropy function.
] <hypercube_count_bound>
#proof[
  Let $k$ be the number of coordinates which differ between $x$ and $x'$ (i.e. the Hamming distance). Then we have $norm(x-x')^2 = 4k$, so for $norm(x-x') <= eta sqrt(N)$ requires that $k <= N eta^2/4$. Given $k$, there are $binom(N,k)$ choices for the coordinates of $x$ to flip, giving a count of
  $
    sum_(k <= (N eta^2) / 4) binom(N,k) = sum_(k <= (N eta^2) / 4) exp_2(N h(k / N) + O(log_2 N)) <= exp_2(N h(eta^2 / 4) + O(log_2 N)).
  $
  Here, the first equality follows from the Stirling approximation for $binom(N,k)$, and the second follows because the sum is over $O(N)$ terms. Moreover, for $k <= N/2 $, $k/N <= eta^2/4$ over the range of this sum.
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
    &= exp(N (-p log(p) - (1-p) log(p))) = exp(N h(p)).
  $
  The final equality then follows from the bound $h(p) <= 2 p log(1 slash p)$ for $p <= 1/2$.
]


#lemma[
  Fix $x in Sigma_N$, and let $eta <= 1/sqrt(2)$. Then the number of $x'$ within distance $2 eta sqrt(N)$ of $x$ is
  $
    abs({x' in Sigma_N | norm(x-x') <= 2eta sqrt(N)})
    <= exp_2(2eta^2log_2(1 slash eta^2)N )
  $
]
#proof[
  Let $k$ be the number of coordinates which differ between $x$ and $x'$ (i.e. the Hamming distance).
  We have $norm(x-x')^2=4k$, so $norm(x-x') <= 2 eta sqrt(N)$ iff $k <= N eta^2$.
  Moreover, for $eta <= 1/sqrt(2)$, $k <= N/2$.
  Thus, by @lem_chernoff_hoeffding,
  we get
  $
    sum_(k <= N eta^2) binom(N,k) <= exp_2(N h(eta^2))
    <= exp_2(2eta^2log_2(1 / eta^2)N )
  $
]


Next, we can consider what this probability is in the case of correlated Normals.

#lemma[Suppose $(g,g')$ are $(1-epsilon)$-correlated Normal vectors, and let $x in Sigma_N$. Then
  $ PP(abs(inn(g',x)) <= 2^(-E) | g) <= 2^(-E + O(log_2 epsilon N)). $
] <correlated_solution_lowprob>
#proof[
  Let $tilde(g)$ be an independent Normal vector to $g$, and observe that $g'$ can be represented as
  $g' = p g + sqrt(1-p^2)tilde(g)$,
  for $p=1-epsilon$.
  Thus, $inn(g',x) = p inn(g,x) + sqrt(1-p^2)inn(tilde(g),x)$.
  Observe $inn(g,x)$ is constant given $g$, and $inn(tilde(g),x)$ is a Normal r.v. with mean 0 and variance $N$, so $inn(g',x) tilde cal(N)(p inn(g,x), (1-p^2)N)$.
  This random variable is nondegenerate for $(1-p^2)N > 0$, with density bounded above as
  $
    phi_(g)(z) = 1 / (sqrt(2pi (1-p^2)N)) e^(- (z-p inn(g,z))^2 / (2(1-p^2)N)) <= 1 / sqrt(2 pi (1-p^2) N).
  $
  Following the remainder of the proof of @resampled_solution_lowprob, we conclude that
  $
    PP(abs(inn(g',x)) <= 2^(-E) | g)
    <= sqrt(2/(pi (1-p^2)N)) 2^(-E)
    = 2^(-E + O(log_2 (1-p^2)N))
    = 2^(-E + O(log_2 epsilon N)).
  $
  The last line follows as $(1-p^2)N <= 2(1-p)N = 2 epsilon N$.
]

Note for instance that here $epsilon$ can be exponentially small in $E$ (i.e. $epsilon = exp_2(-E slash 10)$), which for the case $E=Theta(N)$ implies $epsilon$ can be exponentially small in $N$.

// Efron-Stein case

First, we consider the probability of a solution being optimal for a resampled instance.


#lemma[Suppose $(g,g')$ are $(1-epsilon)$-resampled Normal vectors, and let $x in Sigma_N$. Then,
  $ PP(abs(inn(g',x)) <= 2^(-E) | g, g != g') <= 2^(-M + O(1)). $
] <resampled_solution_lowprob>
#proof[
  Let $S={ i in [N] : g_i != g'_i}$ be the set of indices where $g$ and $g'$ differ. We can express
  $
    inn(g',x') = sum_(i in [N]) g'_i x_i = sum_(i in.not S)g_i x_i + sum_(i in S) g_i' x_i ~ cal(N)(sum_(i in.not S)g_i x_i, abs(S)).
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
    PP(abs(inn(g',x)) <= 2^(-E) | g, g != g') <= integral_(abs(z)<=-2^(-E)) phi_(g,abs(S))(z) dif z <= sqrt(2/pi) 2^(-E) = 2^(-E + O(1)).
  $
]

In this case, we can compute the probability that $g=g'$ as
$ PP(g=g') = product_(i=1)^N PP(g_i = g_i') = (1-epsilon)^N, $
which for $epsilon << 1$ is approximately $1-N epsilon$. Thus, for $epsilon >> omega(1/N)$, we have
$ PP(abs(inn(g',x)) <= 2^(-E) | g) <= 2^(-E + O(1)) $



== Proof of Low-Degree Hardness.


Let $delta > 0$.
Let $E$ be a sequence of energy levels.
Assume for sake of contradiction that $p_"solve" >= Omega(1)$. Let $g,g'$ be $(1-epsilon)$-resampled/$(1-epsilon)$-correlated problem instances. We define the following events:
$
  S_"solve" &= {alg(g) in S(delta;g), alg(g') in S(delta;g')} \
  S_"stable" &= {norm(alg(g) - alg(g')) <= 2eta sqrt(N) } \
  S_"ogp" &= {"for" x "depending only on" g, exists x' in S(delta;g') "such that" norm(x-x') <= eta sqrt(N) } \
  // S_"ogp" (g,x) &= {"for "g'" "p"-resampled from "g, exists x' in Sigma_N " s.t. " norm(x-x') <= eta sqrt(N)" and "x' in S(delta;g')}
$

To set the remaining parameters, choose $epsilon = omega(1/N)$ such that $epsilon D = o(1)$.
Then, choose $eta$ such that $(h^(-1)(delta))^2 >> eta^4 >> epsilon D$.
With this, the previous landscape obstructions give the following.


#lemma[
  For any $omega(log^2 N) <= E <= Theta(N)$, there exist choices of $epsilon,eta$ (depending on $N, E$) such that
  $PP(S_"ogp")=o(1)$.
]
// Efron-Stein case first
#proof[
  Observe that
  $ PP(S_"ogp") = EE[PP(S_"ogp" | g)]. $ <meow>
  Conditional on $g$, we can compute $PP(S_"ogp" | g) = PP(exists x' in S(E;g'), norm(x-x') <= 2eta sqrt(N))$ by setting $x=alg(g)$ (so $x$ only depends on $g$), and union bounding @resampled_solution_lowprob over the $x'$ within $2eta sqrt(N)$ of $x$, as per @hypercube_count_bound:
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
  Now, let $M=delta N$, we can compute $PP(S_"ogp" | g) = PP(exists x' in S(delta;g'), norm(x-x') <= eta sqrt(N))$ by setting $x=alg(g)$ (so $x$ only depends on $g$), and union bounding @resampled_solution_lowprob over the $x'$ within $eta sqrt(N)$ of $x$, as per @hypercube_count_bound:
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

= Randomized Rounding Things

Claim: no two adjacent points on $Sigma_N$ (or pairs within $k=O(1)$ distance) which are both good solutions to the same problem.
The reason is that this would require a subset of $k$ signed coordinates $± g_{i_1},...,± g_{i_k}$ to have small sum, and there are only $2^k binom{N}{k}\leq O(N^k)$ possibilities, each of which is centered Gaussian with variance at least $1$, so the smallest is typically of order $Omega(N^{-k})$.


Thus, rounding would destroy the solution.


- Say we're in the case where rounding changes the solution. (i.e. rounding moves $x$ to point that is not the closest point $x_*$, whp.)
- Let $p_1,dots,p_N$ be the probabilities of disagreeing with $x_*$ on each coordinate.
  - We know that $sum p_i$ diverges (this is equivalent to the statement that rounding will changes the solution whp).
  - Reason: for each coord, chance of staying at that coordinate is $e^(-Theta(p_i))$.
- For each $i$, flip coin with heads prob $2p_i$, and keep all the heads.
  - By Borel-Cantelli type argument, typical number of heads will be $omega(1)$.
- For every coin with a head, change coord with prob 50%, if tails, keep coord.
  - Randomized rounding in artificially difficult way. (I.e. this multistage procedure accomplishes the same thing as randomized rounding.)
- Now, randomized rounding is done by choosing a random set of $omega(1)$ coordinates, and making those iid Uniform in ${-1,1}$.
- Pick a large constant (e.g. 100), and only randomize the first 100 heads, and condition on the others (i.e. choose the others arbitrarily). Note that since $100\leq omega(1)$, there are at least 100 heads whp.
- Now rounded point is random point in 100 dimensional subcube, but at most one of them is a good solution by the claim at the top of the page.
- Combining, the probability for rounding to give a good solution is at most $o(1) + 2^{-100}$. Since $100$ is arbitrary, this is $o(1)$ by sending parameters to $0$ and/or infinity in the right order.




// $ PP(A,B) = 1-PP(not A "or" not B) >= 1 - PP(not A) - PP(not B) = PP(A) + PP(B) - 1 $




#bibliography("references.bib", full: true)
