#let titlepage(title, subtitle, abstract) = {
  pad(
    left: -0.01in,
    top: 0.7in,
    text(
      weight: "medium",
      size: 30pt,
      title,
    ),
  )
  pad(top: 0.05in, text(size: 17pt, style: "italic", subtitle))
  pad(
    top: 5em,
    text[Rushil Mallarapu #footnote[Written under the joint supervision of Professor Mark Sellke and Professor Subhabrata Sen.]],
  )
  pad(top: -0.05in, text[Harvard University, Cambridge, MA 02138])
  pad(top: 0.7in, text(size: 11pt)[*Abstract.* #abstract])
}

#let thesisize(doc, title: none, subtitle: none, abstract: none) = [
  #set text(
    font: "Crimson Pro",
    size: 12pt,
    weight: "regular",
    alternates: true,
  )
  #set page(
    paper: "us-letter",
    numbering: none,
    number-align: bottom + center,
    margin: (x: 1in, y: 1in),
  )
  #set par(
    justify: true,
    spacing: 1em,
    first-line-indent: (amount: 1.2em, all: false),
  )

  // math equation stuff
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
  #show math.equation: set text(size: 11pt)
  #set math.accent(size: 150%)
  #show math.equation: set block(breakable: true)

  // references
  #let crimson = rgb(68%, 12%, 20%)
  #show ref: it => text(fill: crimson)[#it]

  // title page
  #titlepage(title, subtitle, abstract)
  #set page(numbering: "1")

  // for Jarell: how to add spacing after top level headers
  #show heading.where(level: 1): it => {
    pagebreak()
    pad(it, bottom: 5em)
  }

  // acknowledgments
  #include "acknowledgements.typ"

  // outline
  #show outline.entry.where(level: 1): set outline.entry(fill: " ")
  #show outline.entry.where(level: 1): set block(above: 1.2em)

  #outline()

  // math numbering
  #set heading(numbering: "1.1")
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

  #doc
]
