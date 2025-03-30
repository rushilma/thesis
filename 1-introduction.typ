#import "environments.typ": *

#import "symbols.typ": *

= Introduction

Suppose we have $N$ items, each with associated weights.
How should we divide these items into two groups such that the sum of their weights is as close as possible?
Alternatively, is it possible to divide these items into two groups such that the absolute difference of the sum of their weights is below a certain threshold?
This question is known in statistics, physics, and computer science as the _number partitioning problem (NPP)_,
and has been the subject of intense study since its proposal in 1969 @grahamBoundsMultiprocessingTiming1969.

// todo fix this para
Let $g_1,dots,g_N$ be $N$ real numbers.
The _number partitioning problem (NPP)_ asks: what is the subset $A$ of $[N]:={1,2,dots,N}$
such that the sum of the $g_i$ for $i in A$ and the sum of the remaining $g_i$ are as close as possible?
More formally, the $A$ we want to find is the one minimizing the discrepancy
$ abs(sum_(i in A) g_i - sum_(i in.not A) g_i). $

When rephrased as a decision problem (i.e., whether there exists an $A$ such that the discrepancy is zero, or sufficiently small), the NPP is NP-complete; this can be shown by reduction from the subset sum problem.
In fact, the NPP is one of the six basic NP-complete problems of Garey and Johnson, and of those, the only one involving numbers @gareyComputersIntractabilityGuide1979[#sym.section 3.1].

The number partitioning problem can be rephrased in the following way.
Let our instance $g_1,dots,g_N$ be identified with a point $g in RR^N$.
Then, a choice of $A subset.eq [N]$ is equivalent to choosing a point $x$ in the $N$-dimensional binary hypercube $Sigma_N := {plus.minus 1}^N$, where $x_i = +1$ is the same as including $i in A$.
The discrepancy of $x$ is now $abs(inn(g,x))$, and solving the NPP means finding the $x$ minimizing this discrepancy:
$ min_(x in Sigma_N) abs(inn(g,x)). $ <eq_npp_first>

()


// practical applications

A common extension to the NPP is the _multiway number partitioning problem (MWNPP)_, in which we want to partition $g_1,dots,g_N$ into $M$ subsets such that the within-subset sums are mutually close.
While what "mutually close" precisely means varies across the literature, this problem has myriad practical applications which motivate the study of the NPP.

For instance, the NPP was first formulated by Graham, who considered it in the context of multiprocessor scheduling: dividing a group of tasks with known runtimes across a pool of processors so as to minimize one core being overworked while others stall @grahamBoundsMultiprocessingTiming1969.
Later work by Coffman, Garey, and Johnson, as well as by Tsai, looked at utilizing algorithms designed for the NPP for designing multiprocessor schedulers or large integrated circuits @coffmanjr.ApplicationBinPackingMultiprocessor1978 @tsaiAsymptoticAnalysisAlgorithm1992.
Coffman and Lueker also write on how the NPP can be applied as a framework for allocating material stocks, such as steel coils in factories, paintings in museums, or advertisements in newspapers @coffmanProbabilisticAnalysisPacking1991.


// applications: cryptography

On the other hand, in 1976, Merkle and Hellman devised one of the earliest public key cryptography schemes, deriving its hardness from their belief that a variant of the NPP was computationally difficult to solve -- at the time, it was not yet known whether the NPP was NP-complete or not @merkleHidingInformationSignatures1978.
Their proposal was for the reciever, say Alice, to generate as a public key $N$ natural numbers $(a_1,dots,a_N)$, with $N$ typically around 100 and each $a_i$ around 200 bits long.
Then, to encrypt a $N$-bit message, $x = (x_1,dots,x_N)$, with $x_i in {0,1}$, the sender, say Bob, could compute
$ b := sum_(i in N) a_i x_i, $
and send the ciphertext $b$ to Alice.
Any eavesdropper would know $a_1,dots,a_N$, as well as $b$, and decrypting the message involved finding a subset of the $a_i$ adding up to $b$.
This is known as the _knapsack problem_, which is NP-complete, as can be shown by restriction to the NPP @gareyComputersIntractabilityGuide1979[3.2.1(6)].
However, such NP-completeness is only a worst-case hardness guarantee; Merkle and Hellman's scheme involved Alice choosing $a_1,dots,a_N$ by cryptographically scrambling a sequence $(a'_1,dots,a'_N)$ for which solving the NPP was easy, enabling the reciever to practically decrypt the message $x$ from the ciphertext $b$.
In 1984, Shamir -- one of the developers of the RSA cryptosystem still in use today -- showed that one could exploit this public key generation process to reduce the "hard" knapsack problem to one which was solvable in polynomial time, rendering the Merkle-Hellman scheme insecure @shamirPolynomialTimeAlgorithm1982.
While today, Merkle-Hellman is but a footnote in the history of cryptography, it demonstrates the importance of looking beyond worst-case hardness and expanding complexity theory to describe the difficulty of the average problem instance.

// application: randomized control trials

One particularly important application of the NPP in statistics comes from the design of _randomized controlled trials_.
Consider $N$ individuals, each with a set of covariate information $bold(g)_i in RR^d$.
Then the problem is to divide them into a treatment group (denoted $A_+$) and a control group (denoted $A_-$), subject each to different conditions, and evaluate the responses.
In order for such a trial to be accurate, it is necessary to ensure that the covariates across both groups are roughly the same.
in our notation, this equates to finding an $A_+$ (with $A_- := [N] without A_+$) to minimize
$
  min_(A_+ subeq [N]) norm( sum_(i in A_+) bold(g)_i - sum_(i in A_-) bold(g)_i )_infinity.
$ <eq_def_vbp>
This multidimensional extension of the NPP is often termed the _vector balancing problem (VBP)_, and many algorithms for solving the NPP/VBP come from designing such randomized controlled trials @kriegerNearlyRandomDesigns2019 @harshawBalancingCovariatesRandomized2023.

// physics and phase transition

Another major source of interest in the NPP comes from statistical physics.
In the 1980s, Derrida introduced the eponymous _random energy model (REM)_, a simplified example of a spin glass in which, unlike the Sherrington-Kirkpatrick or other $p$-spin glass models, the possible energy levels are indepedent of each other @derridaRandomEnergyModelLimit1980 @derridaRandomenergyModelExactly1981 @baukeNumberPartitioningRandom2004.
Despite this simplicity, this model made possible heuristic analyses of the Parisi theory for mean field spin glasses, and it was suspected that arbitrary random discrete systems would locally behave like the REM @baukeUniversalityLevelStatistics2004 @kistlerDerridasRandomEnergy2014.
The NPP was the first system for which this local REM conjecture was shown @borgsProofLocalREM2009 @borgsProofLocalREM2009a.
In addition, in the case when the $g_i$ are independently chosen uniformly over ${1,2,...,2^M}$, Gent and Walsh conjectured that the hardness of finding perfect partitions (i.e., with discrepancy zero if $sum_i g_i$ is even, and one else) was controlled by the parameter $kappa := m/n$ @gentAnalysisHeuristicsNumber1998 @gentPhaseTransitionsAnnealed2000.
Mertens soon gave a nonrigorous statistical mechanics argument suggesting the existence of a phase transition from $kappa < 1$ to $kappa > 1$: that is, while solutions exist in the low $kappa$ regime, they stop existing in the high $kappa$ regime @mertensPhysicistsApproachNumber2001.
It was also observed that this phase transition coincided with the empirical onset of computational hardness for typical algorithms, and Borgs, Chayes, and Pittel proved the existence of this phase transition soon after @hayesEasiestHardProblem2002 @borgsPhaseTransitionFinitesize2001.
(concluding sentence meow)

// algorithmic gap

Of more interest to us is the the typical optical discrepancy in the average-case, i.e., here we assume the instance inputs $g_i$ are i.i.d. random variables.

The landmark result here is by Karmarkar et al., who showed that when the distribution of the $g_i$'s is sufficiently nice,
#footnote[Specifically, having bounded density, variance $sigma^2$, and finite 4th moment.] <foot_nice>
then the minimum discrepancy of @eq_npp_first is $Theta(sqrt(N) 2^(-N))$ as $N to infinity$ with high probability as $N to infinity$ @karmarkarProbabilisticAnalysisOptimum1986.
Their result also extends to _even partitions_, where the sizes of each subset is equal (i.e., for $N$ even), worsening only to $Theta( N 2^(-N))$.

On the algorithmic side, ()

A first approach, often termed the _greedy heuristic_, would be to sort the $N$ inputs, place the largest in one subset, and place the subsequent largest numbers in the subset with the smaller total running sum.
This takes $O(N log N)$ time (due to the sorting step), but achieves a discrepancy of $O(N^(-1))$, extremely far off from the statistical optimum @mertensEasiestHardProblem2003.
More recently Krieger et al. developed an algorithm achieving a discrepancy of $O(N^(-2))$, but in exchange for this poor performance, their algorithm solves for a balanced partition, which makes it useful for randomized control trials applications @kriegerNearlyRandomDesigns2019.

The true breakthrough towards the statistical optimum came from Karmarkar and Karp, whose algorithm produced a discrepancy of $O(N^(-alpha log N))=2^(-O(log^2 N))$ with high probability.
Their algorithm is rather complicated, involving randomization and a resampling step to make their analysis tractable, but their main contribution is the _differencing heuristic_ @karmarkarDifferencingMethodSet1983.
The idea is as follows: if $S$ is a list of items, then putting $g,g' in S$ in opposite partitions is the same as removing $g$ and $g'$ and adding $abs(g-g')$ back to $S$.
Karmarkar and Karp propose two simpler algorithms based on this heuristic, the partial differencing method (PDM) and largest differencing method (LDM), which they conjectured could also achieve discrepancies of $O(N^(-alpha log N))$.
In both, the items are first sorted, and the differencing is performed on the pairs of the largest and second largest items.
However, in PDM, the remainders are ignored until all original numbers have been differenced, and then are resorted and repartitioned, while LDM reinserts the remainder in sorted order at each step; in any case, both algorithms are thus polynomial in $N$.
Lueker soon disproved that PDM could achieve the KK discrepancy, showing that when $g_i$ were i.i.d. Uniform on $[0,1]$, then the expected discrepancy was $Theta(N^(-1))$, no better than the greedy algorithm @luekerNoteAveragecaseBehavior1987.
However, for $g_i$ i.i.d. Uniform or even Exponential, Yakir confirmed that LDM could achieve the performance of the original differencing algorithm, proving that its expected discrepancy was $N^(-Theta(log N))$ @yakirDifferencingAlgorithmLDM1996.
The constant $alpha$ was later estimated for LDM to be $alpha=1/(2 ln 2)$, via non-rigorous calculations @boettcherAnalysisKarmarkarKarpDifferencing2008.

Of course, at its most basic, the NPP is a search problem over $2^N$ possible partitions, so given more and more time, an appropriate algorithm could keep improving its partition until it acheived the global optimum.
To this degree, Korf developed alternatives known as the _complete greedy_ and _complete Karmarkar-Karp_ algorithms which, if run for exponentially long time, can find the globally optimal partition @korfApproximateOptimalSolutions1995 @korfCompleteAnytimeAlgorithm1998.
This algorithm was later extended to multiway number partitioning @korfMultiwayNumberPartitioning2009.
See also Michiels et al. for extensions to balaced multiway partitioning @michielsPerformanceRatiosDifferencing2003.
()


+ Hoberg [HHRY17] - computational hardness for worst-case discrepancy, as poly-time oracle that can get discrepancy to within $O(2^sqrt(n))$ would be oracle for Minkowski problem.
+ Gamarnik-Kizildag: Information-theoretic guarantee $E_n=n$, best computational guarantee $E_n = Theta(log^2 n)$.
+ Existence of $m$-OGP for $m=O(1)$ and $E_n=Theta(n)$.
+ Absence for $omega(1) <= E_n=o(n)$
+ Existence for $omega(sqrt(n log_2 n)) <= E_n <= o(n)$ for $m=omega_n(1)$ (with changing $eta,beta$)
  + While OGP not ruled out for $E_n <= omega(sqrt(n log_2 n))$, argued that it is tight.
+ For $epsilon in (0,1/5)$, no stable algorithm can solve $omega(n log^(-1/5 + epsilon) n) <= E_n <= o(n)$
+ Possible to strengthen to $E_n=Theta(n)$ (as $2^(-Theta(n)) <= 2^(-o(n))$)

+ @gamarnikAlgorithmicObstructionsRandom2021b
+ @hobergNumberBalancingHard2016
+ @vafaSymmetricPerceptronsNumber2025 - hardness by relation to shortest vector problem

For the multidimensional VBP case, Spencer showed in 1985 that the worse-case discrepancy of the VBP was at most $6sqrt(N)$ for $d=N$ and $norm(bold(g)_i)_infinity <= 1$ for all $i$ @spencerSixStandardDeviations1985.
However, his argument is an application of the probabilistic method, and does not construct such a solution.
In the average case, Turner et al. proved that, under similar regularity assumptions on the $bold(g)_i$,@foot_nice the minimum discrepancy is $Theta(sqrt(N) 2^(-N slash d))$ for all $d <= o(N)$, with high probability @turnerBalancingGaussianVectors2020.
For the regime $delta=Theta(N)$, Aubin et al. conjecture there exists an explicit function $c(delta)$ such that for $delta > 0$, then the discrepancy in the $d=delta N$ regime is $c(delta) sqrt(N)$ with high probability @aubinStorageCapacitySymmetric2019.
To this end, Turner et al. also showed that for $d <= delta N$, one can achieve $O(sqrt(N) 2^(-1 slash delta))$ with probability at least 99% @turnerBalancingGaussianVectors2020.
On the algorithmic side, they generalized the Karmarkar-Karp algorithm to VBP, which, for $2 <= d = O(sqrt( log N))$ finds partitions with discrepancy $2^(-Theta(log^2 N slash d))$, reproducing the gap of classical Karmarkar-Karp.

On the other hand, in the superlinear regime $d >= 2 N$, this average-case discrepancy worsens to $tilde(O)(sqrt(N log(2d slash N)))$ @chandrasekaranIntegerFeasibilityRandom2013.
Yet, many proposed algorithms can achieve similar discrepancies, which is believed to be optimal for $d >= N$ @spencerSixStandardDeviations1985 @bansalConstructiveAlgorithmsDiscrepancy2010 @lovettConstructiveDiscrepancyMinimization2012 @rothvossConstructiveDiscrepancyMinimization2016.
(concluding sentence)

== Hardness and Statistical-to-Computational Gaps

Non-planted models:
- Random constraint satisfaction: @mezardClusteringSolutionsRandom2005 @achlioptasAlgorithmicBarriersPhase2008 @kothariSumSquaresLower2017.
- Maximum independent sets in sparse random graphs @gamarnikLimitsLocalAlgorithms2014 @coja-oghlanIndependentSetsRandom2015.
- Largest submatrix @gamarnikFindingLargeSubmatrix2016 @gamarnikOverlapGapProperty2021a
- $p$-spin model: @gamarnikOverlapGapProperty2019 @montanariOptimizationSherringtonKirkpatrickHamiltonian2019
- diluted $p$-spin model: @chenSuboptimalityLocalAlgorithms2019

Planted models:
- matrix principal component analysis @berthetComputationalLowerBounds2013 @lesieurMMSEProbabilisticLowrank2015 @lesieurPhaseTransitionsSparse2015
- tensor PCA @hopkinsTensorPrincipalComponent2015 @hopkinsPowerSumofsquaresDetecting2017 @arousAlgorithmicThresholdsTensor2020
- high dimensional linear regression @gamarnikSparseHighDimensionalLinear2019 @gamarnikHighDimensionalRegressionBinary2019
- planted clique problem @jerrumLargeCliquesElude1992 @deshpandeImprovedSumofSquaresLower2015 @mekaSumofsquaresLowerBounds2015 @barakNearlyTightSumofSquares2016 @gamarnikLandscapePlantedClique2019


Evidence of hardness:

- Failure of MCMC: @huangStrongLowDegree2025 @jerrumLargeCliquesElude1992
- Failure of AMP: @zdeborovaStatisticalPhysicsInference2016 @bandeiraNotesComputationaltostatisticalGaps2018
- Reductions from planted clique - @berthetComputationalLowerBounds2013 @brennanOptimalAverageCaseReductions2019 @brennanReducibilityComputationalLower2019
- Lower bounds agains Sum of Squares hierarchy: @hopkinsTensorPrincipalComponent2015 @hopkinsPowerSumofsquaresDetecting2017 @raghavendraHighdimensionalEstimationSumofsquares2019 @barakNearlyTightSumofSquares2016
- Lower bounds in statistical query model: @kearnsEfficientNoisetolerantLearning1998 @diakonikolasStatisticalQueryLower2017 @feldmanStatisticalAlgorithmsLower2016
- Low degree methods, and low degree likelihood ratio: @hopkinsStatisticalInferenceSum2018 @kuniskyNotesComputationalHardness2019



== Overlap Gap Property

@gamarnikOverlapGapProperty2021

The _overlap gap property (OGP)_ states that if $g,g'$ are ()

- OGP originally emerged in spin glass theory.
- Link between OGP and $k$-SAT first came in @achlioptasSolutionSpaceGeometryRandom2006 @achlioptasAlgorithmicBarriersPhase2008 @mezardClusteringSolutionsRandom2005
- Clustering: large portions of solutions cluster in sets disconnected wrt the topology of the solution space.
  - Onset of clustering = regine where polynomial time algorithms fail

First formal implication: @gamarnikLimitsLocalAlgorithms2014.

@hatamiLimitsLocallyGlobally2014

@gamarnikLowDegreeHardnessRandom2020


@rahmanLocalAlgorithmsIndependent2017

@weinOptimalLowDegreeHardness2020

- Multioverlap OGP

@weinOptimalLowDegreeHardness2020

@coja-oghlanIndependentSetsRandom2015


Landscape obstructions suggesting sources of hardness

@arguelloRandomizedMethodsNumber1996

@storerProblemSpaceLocal1996

@johnsonOptimizationSimulatedAnnealing1989b

@johnsonOptimizationSimulatedAnnealing1991

@alidaeeNewModelingSolution2005

@kraticaTwoMetaheuristicApproaches2014

@corusArtificialImmuneSystems2019

@santucciImprovedMemeticAlgebraic2021

@mertensPhysicistsApproachNumber2001
- Physics notation as applied to NPP
- "Any heuristic that exploits a fraction of the domain, generating and evaluating a series of feasible configurations, cannot be significantly better than random search." section 4.3

Quantum algorithms

@asproniAccuracyMinorEmbedding2020

@wenOpticalExperimentalSolution2023



== Our Results <subsection_intro_results>

Low degree heuristic: degree $D$ algorithms are a proxy for the class of $e^(tilde(O)(D))$-time algorithms.

== Notation and Conventions


// Glossary

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

+ "instance"/"disorder" - $g$, instance of the NPP problem
+ "discrepancy" - for a given $g$, value of $min _(x in Sigma_N) abs(inn(g,x))$
+ "energy" - negative exponent of discrepancy, i.e. if discrepancy is $2^(-E)$, then energy is $E$. Lower energy indicates "worse" discrepancy.
+ "near-ground state"/"approximate solution"

// Conventions

Conventions:
+ On $RR^N$ we write $norm(dot)_2 = norm(dot)$ for the Euclidean norm, and $norm(dot)_1$ for the $ell^1$ norm.
// + $log$ means $log$ in base 2, $exp$ is $exp$ base 2 - natural log/exponent is $ln$/$e^x$.
+ If $x in RR^N$ and $S subeq [N]$, then $x_S$ is vector with
  $ (x_S)_i = cases(x_i #h(2em) &i in S\,, 0 &"else.") $
  In particular, for $x,y in RR^N$,
  $ inn(x_S, y) = inn(x,y_S) = inn(x_S,y_S). $
+ meow
+ If $S subeq [N]$, then $overline(S) := [N] without S$ is the complementary set of indices.
+ $B(x,r) = { y in RR^N : norm(y-x) < r}$ is $ell^2$ unit ball.
+ Recall by Jensen's inequality that for any real numbers $d_1,dots,d_n$, we have
  $ (sum_(i = 1)^n d_i)^2 <= n sum_(i=1)^n d_i^2. $
  We will use this in the following way: suppose $x^((1)), dots, x^((n)), x^((n+1))$ are $n$ vectors in $RR^N$. Then
  $
    norm(x^((1)) - x^((n+1)))^2 <= ( sum_(i=1)^n norm(x^((i)) - x^((i+1))) )^2 <= n sum_(i=1)^n norm(x^((i)) - x^((i+1)))^2
  $ <eq_squared_triangle_ineq>

// Normal probability lemma

Throughout we will make key use of the following lemma:

#lemma[Normal Small-Probability Estimate][
  Let $E,sigma^2 > 0$, and suppose $Z | mu ~ Normal(mu,sigma^2)$. Then
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

Note that this is decreasing function of $sigma^2$. Thus, for instance if there exists $gamma$ with $sigma^2 >= gamma > 0$, then @eq_normal_smallprob is bounded by $exp_2(-E - log_2(gamma) slash 2 + O(1))$.

// Chernoff-Hoeffding bound

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
  The last inequality follows by multiplying each term by $(p slash (1-p))^(K-k)<=1$. Rearranging gives
  $
    sum_(k <= K) binom(N,k) &<= p^(-K) (1-p)^(-(N-K)) \ &= exp_2 (-K log_2 (p) - (N-K) log_2 (1-p)) \
    &= exp_2 (N dot (-K / N log_2 (p) - ((N-K) / N) log_2 (1-p))) \
    &= exp_2 (N dot (-p log_2 (p) - (1-p) log_2 (1-p)) ) = exp_2 (N h(p)).
  $
  The final equality then follows from the bound $h(p) <= 2 p log_2 (1 slash p)$ for $p <= 1 slash 2$.
]

