#import "environments.typ": *

#import "symbols.typ": *

= Introduction

Suppose we have $N$ items, each with associated weights.
How should we divide these items into two groups such that the sum of their weights is as close as possible?
Alternatively, is it possible to divide these items into two groups such that the absolute difference of the sum of their weights is below a certain threshold?
This question is known in statistics, physics, and computer science as the _number partitioning problem (NPP)_,
and has been the subject of intense study from the 1970s to the present day.

// todo fix this para
Let $g_1,dots,g_N$ be $N$ real numbers.
The _number partitioning problem (NPP)_ asks: what is the subset $A$ of $[N]:={1,2,dots,N}$
such that the sum of the $g_i$ for $i in A$ and the sum of the remaining $g_i$ are as close as possible?
More formally, the $A$ we want to find is the one minimizing the discrepancy
$ abs(sum_(i in A) g_i - sum_(i in.not A) g_i). $

When rephrased as a decision problem (i.e., whether there exists an $A$ such that the discrepancy is zero, or sufficiently small), the NPP is NP-complete; this can be shown by reduction from the subset sum problem.
The NPP is also one of the six basic NP-complete problems of Garey and Johnson, and of those, the only one to deal with numbers @gareyComputersIntractabilityGuide1979[#sym.section 3.1].

(talk about modifications and variants?)

The number partitioning problem can be rephrased in the following way.
Let our instance $g_1,dots,g_N$ be identified with a point $g in RR^N$.
Then, a choice of $A subset.eq [N]$ is equivalent to choosing a point $x$ in the $N$-dimensional binary hypercube $Sigma_N := {plus.minus 1}^N$, and the discrepancy of $x$ is now $abs(inn(g,x))$.
The goal is now to find the $x$ minimizing this discrepancy:
$ min_(x in Sigma_N) abs(inn(g,x)). $



// practical applications

The number partitioning problem and algorithms designed to solve it have myriad practical applications.

Early work by Coffman, Garey, and Johnson, as well as by Tsai, looked at utilizing such algorithms for multiprocessor scheduling: dividing a group of tasks of approximately known runtimes across a pool of processors @coffmanjr.ApplicationBinPackingMultiprocessor1978.
Coffman and Lueker also describe how the NPP can be applied as a framework for allocating material stocks, such as steel coils in factories, paintings in museums, or advertisements in newspapers @coffmanProbabilisticAnalysisPacking1991.

// applications: cryptography

On the other hand, in 1976, Merkle and Hellman devised one of the earliest public key cryptography schemes, deriving its hardness from their belief that a variant of the NPP was computationally difficult to solve -- at the time, it was not yet known whether the NPP was NP-complete or not @merkleHidingInformationSignatures1978.
Their proposal was for the reciever, say Alice, to generate as a public key $N$ natural numbers $(a_1,dots,a_N)$, with $N$ typically around 100 and each $a_i$ around 200 bits long.
Then, to encrypt a $N$-bit message, $x = (x_1,dots,x_N)$, with $x_i in {0,1}$, the sender, say Bob, could compute
$ b := sum_(i in N) a_i x_i, $
and send the ciphertext $b$ to Alice.
Any eavesdropper would know $a_1,dots,a_N$, as well as $b$, and decrypting the message involved finding a subset of the $a_i$ adding up to $b$: this is the _knapsack problem_, which is NP-complete.
However, such NP-completeness is only a worst-case hardness guarantee; Merkle and Hellman's scheme involved Alice choosing $a_1,dots,a_N$ by cryptographically scrambling a sequence $(a'_1,dots,a'_N)$ for which solving the NPP was easy, enabling the reciever to practically decrypt the message $x$ from the ciphertext $b$.
In 1984, Shamir -- one of the developers of the RSA cryptosystem still in use today -- showed that one could exploit this public key generation process to reduce the "hard" knapsack problem to one which was solvable in polynomial time, rendering the Merkle-Hellman scheme insecure @shamirPolynomialTimeAlgorithm1982.
While today, Merkle-Hellman is but a footnote in the history of cryptography, it demonstrates the importance of looking beyond worst-case hardness and expanding complexity theory to describe the difficulty of the average problem instance.

// application: randomized control trials

One particularly important application of the NPP in statistics comes from the design of _randomized controlled trials_.
Consider $N$ individuals, each with a set of covariate information $bold(g)_i in RR^d$.
Then the problem is to divide them into a treatment group (denoted $A_+$) and a control group (denoted $A_-$), subject each to different conditions, and evaluate the responses.
In order for such a trial to be accurate, it is necessary to ensure that the covariates across both groups are roughly the same;
in our notation, this equates to finding an $A_+$ (with $A_- := [N] without A_+$) to minimize
$
  min_(A_+ subeq [N]) norm( sum_(i in A_+) bold(g)_i - sum_(i in A_-) bold(g)_i )_infinity.
$
This multidimensional extension of the NPP is often termed the _vector balancing problem (VBP)_, and many algorithms for solving the NPP/VBP come from designing such randomized controlled trials @kriegerNearlyRandomDesigns2019 @harshawBalancingCovariatesRandomized2023.

An orthogonal extension to the NPP is the _multiway number partitioning problem (MWNPP)_: here we want to partition $g_1,dots,g_N$ into $M$ subsets such that the within-subset sums are mutually close. While what "mutually close" might mean is ()

Other applications.
- Circuit design, etc.

Two questions of interest:
+ What is optimal solution.
+ How to find optimal solution.

== History


== Statistical-to-Computational Gap


Non-planted models:
- Random constraint satisfaction: @mezardClusteringSolutionsRandom2005 @achlioptasAlgorithmicBarriersPhase2008 @kothariSumSquaresLower2017.
- Maximum independent sets in sparse random graphs @gamarnikLimitsLocalAlgorithms2013 @coja-oghlanIndependentSetsRandom2015.
- Largest submatrix @gamarnikFindingLargeSubmatrix2016
- $p$-spin model: @gamarnikOverlapGapProperty2019 @montanariOptimizationSherringtonKirkpatrickHamiltonian2019
- diluted $p$-spin model: @chenSuboptimalityLocalAlgorithms2019

Planted models:
- matrix principal component analysis @berthetComputationalLowerBounds2013 @lesieurMMSEProbabilisticLowrank2015 @lesieurPhaseTransitionsSparse2015
- tensor PCA @hopkinsTensorPrincipalComponent2015 @hopkinsPowerSumofsquaresDetecting2017 @arousAlgorithmicThresholdsTensor2020
- high dimensional linear regression @gamarnikSparseHighDimensionalLinear2019 @gamarnikHighDimensionalRegressionBinary2019
- planted clique problem @jerrumLargeCliquesElude1992 @deshpandeImprovedSumofSquaresLower2015 @mekaSumofsquaresLowerBounds2015 @barakNearlyTightSumofSquares2016 @gamarnikLandscapePlantedClique2019


Evidence of hardness:

Failure of MCMC: @huangStrongLowDegree2025 @jerrumLargeCliquesElude1992
Failure of AMP: @zdeborovaStatisticalPhysicsInference2016 @bandeiraNotesComputationaltostatisticalGaps2018
Reductions from planted clique - @berthetComputationalLowerBounds2013 @brennanOptimalAverageCaseReductions2019 @brennanReducibilityComputationalLower2019
Lower bounds agains Sum of Squares hierarchy: @hopkinsTensorPrincipalComponent2015 @hopkinsPowerSumofsquaresDetecting2017 @raghavendraHighdimensionalEstimationSumofsquares2019 @barakNearlyTightSumofSquares2016
Lower bounds in statistical query model: @kearnsEfficientNoisetolerantLearning1998 @diakonikolasStatisticalQueryLower2017 @feldmanStatisticalAlgorithmsLower2016
Low degree methods, and low degree likelihood ratio: @hopkinsStatisticalInferenceSum2018 @kuniskyNotesComputationalHardness2019



== Overlap Gap Property



== Our Results



Low degree heuristic: degree $D$ algorithms are a proxy for the class of $e^(tilde(O)(D))$-time algorithms.


== Existing Results

+ $X_i,1<=i<=n$ i.i.d. uniform from ${1,2,...,M:=2^m}$, with $kappa := m/n$, then phase transition going from $kappa<1$ to $kappa>1$.
+ Average case, $X_i$ i.i.d. standard Normal.
+ Karmarkar [KKLO86] - NPP value is $Theta(sqrt(N)2^(-N))$ whp as $N to infinity$ (doesn't need Normality).
+ Best polynomial-time algorithm: Karmarkar-Karp [KK82] - Discrepancy $O(N^(-alpha log N))=2^(-Theta (log^2 N))$ whp as $N to infinity$
+ PDM (paired differencing) heuristic - fails for i.i.d. uniform inputs with objective $Theta(n^(-1))$ (Lueker).
+ LDM (largest differencing) heuristic - works for i.i.d. Uniforms, with $n^(-Theta(log n))$ (Yakir, with constant $alpha=1/(2ln 2)$ calculated non-rigorously by Boettcher and Mertens).
+ Krieger - $O(n^(-2))$ for balanced partition.
+ Hoberg [HHRY17] - computational hardness for worst-case discrepancy, as poly-time oracle that can get discrepancy to within $O(2^sqrt(n))$ would be oracle for Minkowski problem.
+ Gamarnik-Kizildag: Information-theoretic guarantee $E_n=n$, best computational guarantee $E_n = Theta(log^2 n)$.
+ Existence of $m$-OGP for $m=O(1)$ and $E_n=Theta(n)$.
+ Absence for $omega(1) <= E_n=o(n)$
+ Existence for $omega(sqrt(n log_2 n)) <= E_n <= o(n)$ for $m=omega_n(1)$ (with changing $eta,beta$)
  + While OGP not ruled out for $E_n <= omega(sqrt(n log_2 n))$, argued that it is tight.
+ For $epsilon in (0,1/5)$, no stable algorithm can solve $omega(n log^(-1/5 + epsilon) n) <= E_n <= o(n)$
+ Possible to strengthen to $E_n=Theta(n)$ (as $2^(-Theta(n)) <= 2^(-o(n))$)

== Our Results <subsection_intro_results>

== Notation and Conventions


#definition[
  Let $x in Sigma_N$. The _energy_ of $x$ (with respect to the instance $g$) is
  $
    E(x;g) := - log_2 abs(inn(g,x)).
  $
  The _solution set $S(E;g)$_ is the set of all $x in Sigma_N$ that have energy at least $E$, i.e. that satisfy
  $
    abs(inn(g,x)) <= 2^(-E).
  $ <eq_npp>
] <def_npp_statement>

- This terminology is motivated by the statistical physics literature, wherein random optimiztation problems are often reframed as energy maximization over a random landscape @mertensPhysicistsApproachNumber2001.
- Observe that minimizing the discrepancy $abs(inn(g,x))$ corresponds to maximizing the energy $E$.

Conventions:
+ On $RR^N$ we write $norm(dot)_2 = norm(dot)$ for the Euclidean norm, and $norm(dot)_1$ for the $ell^1$ norm.
// + $log$ means $log$ in base 2, $exp$ is $exp$ base 2 - natural log/exponent is $ln$/$e^x$.
+ If $x in RR^N$ and $S subeq [N]$, then $x_S$ is vector with
  $ (x_S)_i = cases(x_i #h(2em) &i in S\,, 0 &"else.") $
  In particular, for $x,y in RR^N$,
  $ inn(x_S, y) = inn(x,y_S) = inn(x_S,y_S). $
+ meow
+ $B(x,r) = { y in RR^N : norm(y-x) < r}$ is $ell^2$ unit ball.
+ Recall by Jensen's inequality that for any real numbers $d_1,dots,d_n$, we have
  $ (sum_(i = 1)^n d_i)^2 <= n sum_(i=1)^n d_i^2. $
  We will use this in the following way: suppose $x^((1)), dots, x^((n)), x^((n+1))$ are $n$ vectors in $RR^N$. Then
  $
    norm(x^((1)) - x^((n+1)))^2 <= ( sum_(i=1)^n norm(x^((i)) - x^((i+1))) )^2 <= n sum_(i=1)^n norm(x^((i)) - x^((i+1)))^2
  $ <eq_squared_triangle_ineq>


Throughout we will make key use of the following lemma:

#lemma[Normal Small-Probability Estimate][
  Let $E,sigma^2 > 0$, and $mu,Z$ be random variables with $Z | mu ~ Normal(mu,sigma^2)$.
  for $sigma^2$ a constant. Then
  $
    PP(abs(Z) <= 2^(-E) | mu) <= exp_2 (-E - 1 / 2 log_2 (sigma^2) + O(1)).
  $ <eq_normal_smallprob>
] <lem_normal_smallprob>
#proof[
  Observe that conditional on $mu$, the distribution of $Z$ is bounded as
  $
    phi_(Z|mu) (z) <= 1 / sqrt(2 pi sigma^2) e^(-(z-mu)^2 / (2 sigma^2)) <= (2 pi sigma^2)^(-1 slash 2).
  $
  Integrating over $abs(z)<= 2^(-E)$ then gives @eq_normal_smallprob, via
  $
    PP(abs(Z) <= 2^(-E)) = integral_(abs(z) <= 2^(-E)) (2 pi sigma^2)^(-1 slash 2) dif z <= 2^(-E - 1 / 2 log_2 (2 pi sigma^2) + 1). #qedhere
  $
]

Note that this is decreasing function of $sigma^2$, e.g. it's bounded by $exp_2(-E - 1/2 log_2( min sigma^2))$ (this bound is trivial unless $sigma^2 => gamma > 0$).

#lemma[
  Suppose that $K <= N slash 2$, and let $h(x)=-x log_2 (x) - (1-x) log_2 (x)$ be the binary entropy function. Then, for $p := K slash N$,
  $ sum_(k <= K) binom(N,k) <= exp_2 (N h(p)) <= exp_2 (2 N p log_2 (1 / p)). $
  // https://mathoverflow.net/questions/473730/bounding-a-binomial-coefficient-using-the-binary-entropy-function#mjx-eqn-20
] <lem_chernoff_hoeffding>
#proof[
  Consider a $Bin(N,p)$ random variable $S$. Summing its PMF from $0$ to $K$, we have
  $
    1 >= PP(S <= K) = sum_(k <= K) binom(N,k) p^k (1-p)^(N-k) >= sum_(k<= K) binom(N,k) p^K (1-p)^(N-K).
  $
  Here, the last inequality follows from the fact that $p <= (1-p)$, and we multiply each term by $(p/(1-p))^(K-k)<=1$.
  Now rearrange to get
  $
    sum_(k <= K) binom(N,k) &<= p^(-K) (1-p)^(-(N-K)) \ &= exp_2 (-K log_2 (p) - (N-K) log_2 (1-p)) \
    &= exp_2 (N dot (-K / N log_2 (p) - ((N-K) / N) log_2 (1-p))) \
    &= exp_2 (N dot (-p log_2 (p) - (1-p) log_2 (1-p)) ) = exp_2 (N h(p)).
  $
  The final equality then follows from the bound $h(p) <= 2 p log_2 (1 slash p)$ for $p <= 1 slash 2$.
]



=== Glossary:
+ "instance"/"disorder" - $g$, instance of the NPP problem
+ "discrepancy" - for a given $g$, value of $min _(x in Sigma_N) abs(inn(g,x))$
+ "energy" - negative exponent of discrepancy, i.e. if discrepancy is $2^(-E)$, then energy is $E$. Lower energy indicates "worse" discrepancy.
+ "near-ground state"/"approximate solution"

