


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

