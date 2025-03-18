/// Module for symbols in thesis

#let alg = $cal(A)$
#let to = math.arrow

#let abs(x) = $lr(bar.v #x bar.v)$
#let inn(x, y) = $lr(angle.l #x, #y angle.r)$
#let vol(x) = $"vol"lr(paren.l #x paren.r)$

#let PP = $upright(bold(P))$
#let EE = $upright(bold(E))$
#let RR = $upright(bold(R))$

#let Unif(x) = $"Unif"lr(paren.l #x paren.r)$
#let Bin(x, y) = $"Bin"lr(paren.l #x, #y paren.r)$
#let Normal(x, y) = $cal(N)lr(paren.l #x, #y paren.r)$
#let stdnorm = $Normal(0,I_N)$

#let L2iid = $L^2(RR^N,pi^(times.circle N))$
#let subeq = $subset.eq$

#let L2norm = $L^2(RR,gamma)$
#let L2normN = $L^2(RR^N,gamma^N)$

