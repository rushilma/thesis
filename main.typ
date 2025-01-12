#set text(font: "Crimson Pro", size: 12pt)
#set page(paper: "us-letter", margin: (x: 1.75in))

// #show link.where

#let crimson = rgb(68%, 12%, 20%)
// I modified the code a bit to make it works along with cite and refs other than heading. note that equations don't have a numbering by default, so need to #set math.equation(numbering: "(1)") if anyone wants to reference an equation with a such colored box manner.

#let separate-supplement-style(supp, num) = {
  text(supp, fill: crimson)
  [ ]
  box(num, stroke: 1pt + green, outset: (bottom: 1.5pt, x: .5pt, y: .5pt))
}
/*
#show ref: it => {
  let (element, target, supplement: supp) = it.fields()
  // cite doesn't have element
  if element == none {
    return it
  }

  let non_cite_ref = element.fields()
  let supp = if supp == auto { non_cite_ref.supplement } else { supp }
  let num = context {
    // apply the heading's numbering style
    let head-count = counter(heading).at(target)
    numbering(non_cite_ref.numbering, ..head-count)
  }
  link(target, separate-supplement-style(supp, num))
}
*/

#set heading(numbering: "1.")

#show smallcaps: set text(font: "Latin Modern Roman Caps")




#let titlepage(
  title,
  subtitle,
  author,
  date,
) = {
  set align(center)
  set par(leading: 0.5em)


  page([
    #v(150pt)
    #text(
      fill: crimson,
      style: "italic",
      size: 40pt,
      title,
    )
    #v(1fr)
    #text(
      fill: crimson,
      style: "italic",
      size: 30pt,
      subtitle,
    )
    #v(5fr)
    #smallcaps[
      A thesis presented \
      by \
      #author \
      to \
      The Department of Statistics
    ]
    #v(1fr)
    #smallcaps[
      in partial fulfillment of the requirements \
      for the degree of \
      Bachelor of Arts (Honors) \
      in the subject of \
      Statistics
    ]
    #v(1fr)
    #smallcaps[
      Harvard University \
      Cambridge, Massachusetts \
      #date
    ]
    #v(3fr)
  ])
}

#let author = "Rushil Mallarapu"
#let degreemonth = "April"
#let degreeyear = "2025"

#titlepage(
  "Meow",
  "meow meow",
  author,
  [#degreemonth #degreeyear],
)

#set math.equation(numbering: "(1)")

#let copyrightpage(author, year) = {
  set align(left)
  page([
    #v(1fr)
    #sym.copyright
    #text(style: "italic")[#year -- #author]
    \
    #smallcaps[All rights reserved.]
    #v(1fr)
  ])
}

#copyrightpage([#author], [#degreeyear])

#set page(numbering: "i")

#let abstractpage(author, advisor, title, content) = {
  set page(
    header: [
      Thesis advisor: #advisor
      #h(1fr)
      #author
    ],
  )

  page([
    #set align(center)
    #text(
      fill: crimson,
      style: "italic",
      size: 35pt,
      title,
    )
    \ #v(0.7em)
    #smallcaps[Abstract]
    #v(1em)

    #set align(left)
    #par(first-line-indent: 1em, leading: 1.3em)[#content]
  ])
}

#abstractpage(author, "Subhabrata Sen", "Meow")[
  #lorem(100)

  #lorem(100)

  #lorem(100)

  #lorem(100)

  #lorem(100)
  #lorem(100)
]

#show outline: it => {
  v(150pt)
  align(right)[#text(size: 30pt)[#it.title]]
  v(100pt)
  let chapters = query(it.target)
  for chapter in chapters {
    let loc = chapter.location()
    let nr = numbering(loc.page-numbering(), ..counter(page).at(loc))
    // [#chapter.numbering]
    let n = 1
    if chapter.level == 1 {
      if chapter.numbering != none {
        let n = numbering(chapter.numbering, ..counter(heading).at(loc))
        smallcaps[#n #h(1em) #chapter.body]
      } else {
        smallcaps[#chapter.body]
      }
      h(1fr)
      nr // page number
      linebreak()
      v(1em)
    } else if chapter.level == 2 {
      let n = numbering(chapter.numbering, ..counter(heading).at(loc))
      smallcaps[#n #h(1em) #chapter.body]
      // #smallcaps[#chapter.body] #box(width: 1fr, repeat(".")) #nr \
      //smallcaps[#chapter.body]
      box(
        width: 1fr,
        repeat("."),
      )
      nr // page number
      linebreak()
    }
    // [#chapter.fields()]
  }
}


#outline(title: align(right)[Content])



#set heading(numbering: "1.1")

#show heading.where(level: 1): it => {
  set align(right)
  pagebreak()
  v(150pt)
  text(
    // number
    fill: crimson,
    size: 100pt,
    counter(heading).display(),
  )
  linebreak()
  text(
    // body
    size: 24pt,
    it.body,
  )
  v(50pt)

  // #it.fields()
}

#set page(numbering: "1")
#counter(page).update(1)

= Introduction <intro>

#lorem(100)

== Hello
#lorem(100)

In @intro

= Beginnings <beginning>
In @beginning we prove @pythagoras.
$ a^2 + b^2 = c^2 $ <pythagoras>

Hello @bubeckEntropicCLTPhase2018.

== Meow

#lorem(100)

// Appendix

#set heading(numbering: "A.1")
#counter(heading).update(0)

= Hello
= Meow meow


#show heading: it => [
  #set align(right)
  #text(size: 20pt, it.body)
]
#show bibliography: set heading(numbering: none)

#bibliography(full: true, "references.bib")

// sw=2 ts=2 sts=2




















