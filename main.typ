#import "@preview/ctheorems:1.1.3": *
#show: thmrules.with(qed-symbol: $square$)

#import "environments.typ": *

#import "@preview/equate:0.3.1": equate

// page layout
#set text(
  font: (
    /*
    (
      name: "STIX Two Math",
      covers: regex("[0-9]"),
    ),
    */
    "Crimson Pro",
  ),
  size: 12pt,
  weight: "regular",
  alternates: true,
)
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

#show math.equation: set text(font: "STIX Two Math", size: 11pt)

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

#include "1-introduction.typ"

/// Algorithms

#include "2-algorithms.typ"

/// Hardness

#include "3-hardness.typ"

/// Rounding

#include "4-rounding.typ"

/// Litreview

#include "5-litref.typ"


#bibliography("references.bib", full: true)
