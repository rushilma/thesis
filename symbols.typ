/// Module for symbols in thesis

// #import "environments.typ": *

#let alg = $cal(A)$
#let to = math.arrow

#let cor = $upright("cor")$
#let res = $upright("res")$

#let abs(x) = $lr(bar.v #x bar.v)$
#let inn(x, y) = $lr(angle.l #x, #y angle.r)$
#let corr(x, y) = $"corr"(#x, #y)$
#let exp2(x) = $exp_2 lr(paren.l #x paren.r)$
#let log2(x) = $log_2 lr(paren.l #x paren.r)$

#let cdeg(x) = $"cdeg"lr(paren.l #x paren.r)$

#let PP = $upright(bold(P))$
#let EE = $upright(bold(E))$
#let RR = $upright(bold(R))$

#let Unif(x) = $"Unif"lr(paren.l #x paren.r)$
#let Bern(x) = $"Bern"lr(paren.l #x paren.r)$
#let Bin(x, y) = $"Bin"lr(paren.l #x, #y paren.r)$
#let Normal(x, y) = $cal(N)lr(paren.l #x, #y paren.r)$
#let stdnorm = $Normal(0,I_N)$

#let L2iid = $L^2(RR^N,pi^(times.circle N))$
#let subeq = $subset.eq$
#let round = $sans("round")$
#let cube = $sans("cube")$

#let L2norm = $L^2(RR,gamma)$
#let L2normN = $L^2(RR^N,gamma^N)$

#let Soln(x) = $S(E;#x)$

#let colon = $class("punctuation", :) space.thin$

#let multiset(..x) = (
  math.lr(
    size: 100% + 1em,
    $brace.l
      #stack(
        spacing: 0.7em,
        ..x.pos().map(it => align(left, it)),
      )
      brace.r$,
  )
)

#let multiprob(..x) = (
  math.lr(
    size: 100% + 1em,
    $paren.l
      #stack(
        spacing: 0.7em,
        ..x.pos().map(it => align(left, it)),
      )
      paren.r$,
  )
)

#let multiprobcond(y, ..x) = (
  math.lr(
    size: 100% + 1em,
    $paren.l
      #stack(
        spacing: 0.7em,
        ..x.pos().map(it => align(left, it)),
      )
      mid(|) #y
      paren.r$,
  )
)

/*
// #let theoremrefs(..thms) = {
#let theoremrefs(it, it2) = {
  //let thms = its.pos().map(x => x.element)
  // its.at(0).fields()
  context {
    let elem = query(it).first()
    if elem.func() == theorem {
      panic("meow")
    }
    link(it, elem.body)

    // query(it2).at(0)
  }

  [meow]
}
*/
