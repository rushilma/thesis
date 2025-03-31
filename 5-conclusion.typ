#import "environments.typ": *

#import "symbols.typ": *

= Conclusion


For any $D <= o(N)$, there is an easy method to achieve a discrepancy of $2^(-D)$ in $e^(O(D))$ time.

#enum(
  [First, pick a subset $J subeq[N]$ of $D$ coordinates.],
  [meow],
  [meow],
)

First, fix a set of all but $D$ coordinates of $x$ via an LDM pass over $g$ (so that the sum of these "extraneous" coordinates $g_i x_i$ is at most 1).

Given the statistical energy threshold is $Theta(N)$, we know the original problem has a $2^(-D)$ solution with high probability.
Thus,



then brute force search the remaining $D$ coordinates.

By fixing all but D coordinates (eg in a greedy way so their sum is at most 1) and then brute force searching for the remaining coordinates.
(You can argue directly that because the original problem has a 2^{-D} solution whp so does this one because the shift is small and independent of the remaining coordinates.
Basically you can absorb the small shift into any remaining coordinate and say high-probability properties of standard gaussians also hold for Gaussians shifted by an independent O(1) constant.)
So qualitatively our result and the low degree ansatz suggest this simple method gives a roughly optimal quality/time tradeoff.


Meow

== Future Work
