#import "@preview/ctheorems:1.1.3": *
#show: thmrules.with(qed-symbol: $square$)

#import "environments.typ": *

#import "@preview/equate:0.3.1": equate

// page layout
#set text(font: "Crimson Pro", size: 12pt)
#set page(
  paper: "us-letter",
  header: [
    Rushil Mallarapu
    #h(1fr) #datetime.today().display()
    #v(-0.8em)
    #line(length: 100%, stroke: 0.5pt)
  ],
  numbering: "1",
  number-align: bottom + right,
  margin: (x: 1in, y: 1in),
)
#set par(
  justify: true,
  spacing: 1em,
  first-line-indent: (amount: 1.2em, all: false),
)

#show math.equation: set text(font: "STIX Two Math")

// 2 level math numbering

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

#set cite(style: "alphanumeric.csl")

#let crimson = rgb(68%, 12%, 20%)
#show ref: it => text(fill: crimson)[#it]

/// Math environments

#import "symbols.typ": *

/// Introduction

#include "introduction.typ"

/// Algorithms

#include "algorithms.typ"

/// Results

#include "results.typ"

= Randomized Rounding Things

Claim: no two adjacent points on $Sigma_N$ (or pairs within $k=O(1)$ distance) which are both good solutions to the same problem.
The reason is that this would require a subset of $k$ signed coordinates $± g_{i_1},...,± g_{i_k}$ to have small sum, and there are only $2^k binom{N}{k}\leq O(N^k)$ possibilities, each of which is centered Gaussian with variance at least $1$, so the smallest is typically of order $Omega(N^{-k})$.

#proposition[
  Fix distinct points $x,x' in Sigma_N$ with $norm(x - x')<= 2sqrt(k)$ (i.e. $x,x'$ differ by $k$ sign flips), for $k=O(1)$, and let $g$ be any instance.
  Then,
  $
    PP(x in Soln(g) "and" x' in Soln(g)) <= exp(-E + O(1)).
  $
] <prop_fixed_close_solns_lowprob>
#proof[
  For $x != x'$, let $J subeq [N]$ denote the subset of coordinates in which $x,x'$ differ, i.e. $x_J != x'_J$; by assumption, $abs(J) <= k$.
  In particular, we can write
  $ x = x_([N] without J) + x_J, #h(5em) x' = x_([N] without J) - x_J. $
  Thus, for a fixed $x,x'$, if
  $ -2^(-E) <= inn(g,x), inn(g,x') <= 2^(-E), $
  we can expand this into
  $
    -2^(-E) <= &inn(g,x_([N] without J)) + inn(g,x_J) <= 2^(-E), \
    -2^(-E) <= &inn(g,x_([N] without J)) - inn(g,x_J) <= 2^(-E).
  $
  Multiplying the lower equation by $-1$ and adding the resulting inequalities gives
  $ abs(inn(g,x_J)) <= 2^(-E), $
  where $inn(g,x_J)$ is a $Normal(0,k)$ r.v. (note that $k>0$ so it is nondegenerate). Moreover, as $k=O(1)$, we get by the logic in @lem_correlated_solution_lowprob that
  $
    PP(x in Soln(g) "and" x' in Soln(g)) <= PP(abs(inn(g,x_J)) <= 2^(-E)) <= exp(-E + O(1)). #qedhere
  $
]

#theorem[Solutions Can't Be Close][
  Let $k=O(1)$ and $E >> log N$.
  Then for any instance $g$, with high probability there are no pairs of distinct solutions $x,x' in Soln(g)$ with $norm(x-x') <= 2 sqrt(k)$.
] <thrm_solutions_repel>
#proof[
  Observe that by @prop_fixed_close_solns_lowprob, finding a pair of distinct solutions within distance $2 sqrt(k)$ implies finding some subset of at most $k$ coordinates $J subset[N]$ of $g$ and $abs(J)$ signs $x_J$ such that $abs(inn(g_J,x_J))$ is small.
  For any $g$, there are at most $2^k=O(1)$ choices of signs and, by @vershyninHighDimensionalProbabilityIntroduction2018[Exer. 0.0.5],
  $ sum_(1 <= k' <= k)binom(N,k') <= ((e N) / k)^k = O(N^k) $
  choices of such subsets.
  Union bounding @prop_fixed_close_solns_lowprob over these $O(N^k)$ choices, we get that
  $
    PP multiprob(exists x\,x' "s.t.", (upright(I)) #h(0.5em) norm(x-x') <= 2sqrt(k)\,, (upright(I I)) #h(0.3em) &x\,x' in Soln(g))
  <= PP multiprob(exists J subset [N]\, x_J in {plus.minus 1}^k "s.t.",
     (upright(I)) #h(0.65em) abs(J) <= k\,,
     (upright(I I)) #h(0.3em) abs(inn(g_J,x_J)) <= exp(-E))
  <= exp(-E + O(log N)) = o(1). #qedhere
  $
]

Argument:
- Algorithm $alg$ which is deterministic $RR^N -> RR^N$. Suppose $tilde(A): RR^N -> Sigma^N$ is $alg$ passed through any nontrivial rounding procedure.
- Say $alg(g) = x$. Let $x^* in Sigma_N$ be closest point to $x$, and $tilde(x)=tilde(A)(g)$ be the rounding of $x$.
- If $x^* = tilde(x)$, we're done.
- Else, we know that only one of $x^*$ and $tilde(g)$ are a good solution, by @thrm_solutions_repel. It's $x^*$ with probability $p_"solve"$.
  - Here, we're assuming randomized rounding changes at most some $O(1)$ amount of coordinates.
-


Meow meow
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


#bibliography("references.bib", full: true)
