#import "environments.typ": *

#import "symbols.typ": *

// TODO:
// - Write theorems explaining the actual results
// - Finish algorithms section

= Proof of Strong Low-Degree Hardness

In this section, we prove strong low-degree hardness for both low-degree polynomial algorithms and algorithms with low Efron-Stein degree.

For now, we consider $Sigma_N$-valued deterministic algorithms.
We discuss the extension to random, $RR^N$-valued algorithms later on in (section ???).
As outlined in @subsection_intro_results,

The key argument is as follows.
Fix some energy levels $E$, depending on $N$.
Suppose we have a $Sigma_N$-valued, deterministic algorithm $alg$ given by a degree $D$ polynomial (resp. an Efron-Stein degree $D$ function), and we have two instances $g,g'~stdnorm$ which are $(1-epsilon)$-correlated (resp. $(1-epsilon)$-resampled), for $epsilon>0$.
Say $alg(g)=x in Sigma_N$ is a solution with energy at least $E$, i.e. it "solves" this NPP instance.
For $epsilon$ close to 0, $alg(g')=x'$ will be close to $x$, by low-degree stability.
However, by adjusting parameters carefully, we can make it so that with high probability (exponential in $E$), there are no solutions to $g'$ close to $x$.
By application of a correlation bound on the probability of solving any fixed instance, we can conclude that with high probability, $alg$ can't find solutions to NPP with energy $E$.

Intuitively, our argument can be thought of as a "conditional" version of the overlap gap property.
Traditionally, the overlap gap property is a global obstruction: one shows that with high probability, one cannot find a tuple of good solutions to a family of correlated instances which are all roughly the same distance apart.
Here, however, we show a local obstruction - we condition on being able to solve a single instance, and show that after a small change to the instance, we cannot guarantee any solutions will exist close to the first one.
This is an instance of the "brittleness," so to speak, that makes NPP so frustrating to solve; even small changes in the instance break the landscape geometry, so that even if solutions exist, there's no way to know where they'll end up.

We start with some setup which will apply, with minor modifications depending on the nature of the algorithm in consideration, to all of the energy regimes in discussion.
After proving some preliminary estimates, we establish the existence of our conditional landscape obstruction, which is of independent interest.
Finally, we conclude by establishing low-degree hardness in both the linear and sublinear energy regimes.

== Proof Outline and Preliminary Estimates

First, consider the case of $alg$ being a polynomial algorithm with degree $D$, where $D$ will depend on $N$.
Let $g,g'$ be $(1-epsilon)$-correlated. We define the following events:
$
  S_"solve" &= {alg(g) in Soln(g), alg(g') in Soln(g')} \
  S_"stable" &= {norm(alg(g) - alg(g')) <= 2 sqrt(eta N) } \
  S_"cond" &= multiset(
    exists.not x' in Soln(g') "such that",
    norm(x-x') <= 2sqrt(eta N),
  )
$ <eq_poly_events>



Next, let $alg$ be given by a function with Efron-Stein degree $D$.
We now want $g,g'$ to be $(1-epsilon)$-resampled. We define the following events.
$
  S_"diff" &= { g != g'} \
  S_"solve" &= {alg(g) in Soln(g), alg(g') in Soln(g')} \
  S_"stable" &= {norm(alg(g) - alg(g')) <= 2 sqrt(eta N) } \
  S_"cond" &= multiset(
    exists.not x' in Soln(g') "such that",
    norm(x-x') <= 2sqrt(eta N),
  )
$ <eq_es_events>
Note that these are the same events as @eq_poly_events, along with an

== Conditional Landscape Obstruction

Our goal is to show that
$
  p_"cond" = PP(
  multiset(
    exists x' in Soln(g') "such that",
    norm(x-x') <= 2sqrt(eta N),
  )
) <= o(1).
$


