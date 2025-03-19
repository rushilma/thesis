#import "environments.typ": *

#import "symbols.typ": *



= Proof of Strong Low-Degree Hardness <section_proof>

Broad setup




Throughout this section, we let $E=delta N$ for some $delta > 0$, and aim to rule out the existence of low-degree algorithms achieving these energy levels.
This corresponds to the statistically optimal regime, as per @karmarkarProbabilisticAnalysisOptimum1986.


// Assume for sake of contradiction that $p_"solve" >= Omega(1)$.



In this case, set $epsilon = 2^(-delta N)=o(1)$

#lemma[
  There exists an $eta > 0$ of constant order such that
  $ PP(S_"cond") >= 1 - e^(-c N) $
  for an arbitrary constant $c$.
]

$D=o(2^N)$.

$D epsilon = D / 2^N * 2^((1-delta)N)$


#lemma[
  For any $omega(log^2 N) <= E <= Theta(N)$, there exist choices of $epsilon,eta$ (depending on $N, E$) such that
  $PP(S_"ogp")=o(1)$.
]
// Efron-Stein case first
#proof[

  $ PP(S_"ogp" | g) <= exp_2(-E + N eta^2 log_2(1 slash eta^2) + O(1)). $

  We want to choose $eta$ such that

  $ -E + N eta^2 log_2(1 slash eta^2) = -Omega(N) $ // or omega(1)

  $ E / N > eta^2 log(1 slash eta^2) $

  Using the fact that $sqrt(2x) >= -x log_2 x$, it suffices to pick $eta^2$ with

  $ E / N > 2 eta, $

  so $eta^2 := E^2/(2 N^2)$ is a valid choice.


  By the choice of $eta^2 << (h^(-1))(delta) asymp 1$, this bound gives $PP(S_"ogp"|g) <= exp_2(-O(N))=o(1)$.
  Integrating over $g$ gives the overall bound.
]

When $C D epsilon N^2 = omega_N(1)$ (i.e. goes to infinity),

$
  PP(S_"stable") &<= (16C D epsilon N^2) / (16 eta^4 N^2) \
  &= (C D epsilon) / (eta^4) = (4 C D epsilon N^4) / (E^4)
$

$D epsilon to 0$ same as $D = o(1/epsilon)=o(N)$.




#lemma[
  $PP(S_"solve",S_"stable") <= PP(S_"ogp")=o(1)$.
]
#proof[
  For the second, observe that
  $ PP(S_"ogp") = EE[PP(S_"ogp" | g)]. $
  Now, let $M=delta N$, we can compute $PP(S_"ogp" | g) = PP(exists x' in S(delta;g'), norm(x-x') <= eta sqrt(N))$ by setting $x=alg(g)$ (so $x$ only depends on $g$), and union bounding @resampled_solution_lowprob over the $x'$ within $eta sqrt(N)$ of $x$, as per @lem_hypercube_counting:
  $ PP(S_"ogp" | g) <= exp_2(-delta N + N h(eta^2 / 4) + O(log_2 N)). $
  By the choice of $eta^2 << (h^(-1))(delta) asymp 1$, this bound gives $PP(S_"ogp"|g) <= exp_2(-O(N))=o(1)$.
  Integrating over $g$ gives the overall bound.
]


