#import "@preview/ctheorems:1.1.3": *
#show: thmrules.with(qed-symbol: $square$)

#import "environments.typ": *

#import "@preview/equate:0.3.1": equate

#import "thesisize.typ": *

#show: thesisize.with(
  title: [SLDH For NPP],
  subtitle: [Strong Low Degree Hardness for the Number Partitioning Problem],
  abstract: [Meow #lorem(200)],
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

#include "5-conclusion.typ"


#bibliography(
  "references.bib",
  style: "springer-lecture-notes-in-computer-science", // "chicago-author-date", // "alphanumeric.csl",
  full: true,
)
