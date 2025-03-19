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
    #v(-0.8em)
    #line(length: 100%, stroke: 0.5pt)
  ],
  numbering: "1",
  number-align: bottom + right,
  margin: (x: 1in, y: 1in),
)
#set par(
  justify: true,
  first-line-indent: (amount: 1.2em, all: false),
)

#show math.equation: set text(font: "STIX Two Math")

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


#set cite(style: "alphanumeric.csl")

/// Math environments

#import "symbols.typ": *

/// Introduction

#include "introduction.typ"

/// Algorithms

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

/// Results

#include "results.typ"

#include "results2.typ"

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



@odonnellAnalysisBooleanFunctions2021


#bibliography("references.bib", full: true)
