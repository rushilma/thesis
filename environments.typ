/// Module for thesis environments

#import "@preview/ctheorems:1.1.3": *
// #show: thmrules.with(qed-symbol: $square$)

#let theorem = thmbox(
  "theorem",
  "Theorem",
  breakable: true,
  fill: rgb("#eeffee"),
)
#let corollary = thmplain(
  "theorem",
  "Corollary",
  base: "theorem",
  titlefmt: strong,
)

#let lemma = thmplain(
  "theorem",
  "Lemma",
  // base: "theorem",
  titlefmt: strong,
)
#let definition = thmbox("theorem", "Definition", inset: (x: 1.2em, top: 1em))

#let example = thmplain("example", "Example") // .with(numbering: none)
#let proof = thmproof("proof", "Proof")



