#import "@preview/ctheorems:1.1.3": *
#show: thmrules.with(qed-symbol: $square$)

#import "environments.typ": *

#import "@preview/equate:0.3.1": equate

#let purple = rgb(128, 0, 76)

#import "thesisize.typ": *

#let abstract = [
  Finding good solutions to the _number partitioning problem (NPP)_ -- that is, finding a partition of a set of $N$ numbers to minimize the discrepancy between the sums of the two subsets -- is a well-studied optimization problem, with applications to statistics, physics, and computer science.
  Along with having numerous practical applications in the design of randomized control trials and processor scheduling,
  the NPP is famous posessing a _statistical-to-computational gap_:
  assuming the $N$ numbers to be partitioned are i.i.d. standard Normal random variables, the optimal discrepancy is $2^(-Theta(N))$ with high probability, but the best polynomial-time algorithms only find solutions with a discrepancy of $2^(- Theta(log^2 N))$.
  This gap is a common feature in optimization problems over random combinatorial structures, and indicates the need for a theory of computational complexity beyond worst-case analysis.

  In this thesis, we prove a strong form of algorithmic hardness for the number partitioning problem, aiming to establish that this statistical-to-computational gap is intrinsic to this problem.

  To do this, we first establish a "brittleness" property on the geometry of the solution set, which ensures any stable algorithms are unable to efficiently traverse this random landscape.

  We then study _low degree algorithms_, which


  + The success of overparameterization in modern machine learning has caused a paradigm shift in statistics.
  + In particular, the phenomenon of double descent, wherein model performance improves with model size far past the interpolation threshold, has upended the classical understanding of the bias-variance tradeoff.
  + Seeking tractable models in which to study this, statisticians have returned to the canonical problem of linear regression, though now under a high dimensional lens.
  + There, examining the effects of overparameterization in these simple models, they recover some hallmarks of double descent.
  + Throughout this literature, the assumption that the rows of the design are independent and identically distributed is ubiquitous – little is known about what may occur in settings of heavy dependence, which arise in, for example, neuroscience and finance.
  + Here, we instead model the design as right-rotationally invariant, a distribution permitting significant row dependence that has received recent attention.
  + Under this model, we derive the out-of-sample risks for minimum norm linear interpolation and ridge regression; furthermore, we prove that Generalized Cross Validation is no longer consistent, and offer a consistent alternative.
  + Lastly, we present partial findings on the random features model with Gaussian inputs and right-rotationally invariant weights, demonstrating numerical support for conjectures underlying our results.

]

#show: thesisize.with(
  title: [Strong Low Degree Hardness for \ the Number Partitioning Problem],
  // subtitle: [Strong Low Degree Hardness for the Number Partitioning Problem],
  abstract: abstract,
  linkcolor: purple,
)

/// Math environments

#import "symbols.typ": *

/// Introduction

#include "1-introduction.typ"

/// Algorithms

#include "2-algorithms.typ"

/// Hardness

#include "3-hardness.typ"

/// Rounding

#include "4-rounding.typ"

/// Litreview

// #include "5-litref.typ"

/// Conclusion

// #include "5-conclusion.typ"


#bibliography(
  "references.bib",
  style: "ieee.csl", // "chicago-author-date", // "alphanumeric.csl",
  title: "References",
  full: false,
)
