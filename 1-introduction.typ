#import "environments.typ": *

#import "symbols.typ": *

= Introduction

Suppose we have $N$ items, each with associated weights.
How should we divide these items into two groups such that the sum of their weights is as close as possible?
Alternatively, is it possible to divide these items into two groups such that the absolute difference of the sum of their weights is below a certain threshold?
This question is known in statistics, physics, and computer science as the _number partitioning problem (NPP)_,
and has been the subject of intense study since its proposal in 1969 @grahamBoundsMultiprocessingTiming1969.

// todo fix this para
Formally, let $g_1,dots,g_N$ be $N$ real numbers.
The NPP is the problem of finding the subset $A$ of $[N]:={1,2,dots,N}$ which minimizes the discrepancy
$ abs(sum_(i in A) g_i - sum_(i in.not A) g_i). $
Alternatively, identify the instance $g_1,dots,g_N$ with a point $g in RR^N$.
Then, a choice of $A subset.eq [N]$ is equivalent to choosing a point $x$ in the $N$-dimensional binary hypercube $Sigma_N := {plus.minus 1}^N$, where $x_i = +1$ is the same as including $i in A$.
The discrepancy of $x$ is now $abs(inn(g,x))$, and solving the NPP means finding the $x$ minimizing this discrepancy:
$ min_(x in Sigma_N) abs(inn(g,x)). $ <eq_npp_first>

When rephrased as a decision problem -- does there exists an $A subeq [N]$ (or an $x in Sigma_N$) such that the discrepancy is zero, or sufficiently small -- the NPP is NP-complete; this can be shown by reduction from the subset sum problem.
In fact, the NPP is one of the six basic NP-complete problems of Garey and Johnson, and of those, the only one involving numbers @gareyComputersIntractabilityGuide1979[#sym.section 3.1].

// practical applications

Finding "good" solutions to this problem has a number of practical applications.
For instance, the NPP and MWNPP
#footnote[That is, the _multiway number partitioning problem (MWNPP)_, in which we want to partition $g_1,dots,g_N$ into $M$ subsets such that the within-subset sums are mutually close; what "mutually close" means precisely varies across the literature.]
were first formulated by Graham, who considered it in the context of multiprocessor scheduling: dividing a group of tasks with known runtimes across a pool of processors so as to minimize one core being overworked while others stall @grahamBoundsMultiprocessingTiming1969.
Later work by Coffman, Garey, and Johnson, as well as by Tsai, looked at utilizing algorithms designed for the NPP for designing multiprocessor schedulers or large integrated circuits @coffmanjr.ApplicationBinPackingMultiprocessor1978 @tsaiAsymptoticAnalysisAlgorithm1992.
Coffman and Lueker also write on how the NPP can be applied as a framework for allocating material stocks, such as steel coils in factories, paintings in museums, or advertisements in newspapers @coffmanProbabilisticAnalysisPacking1991.

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

// physics and phase transition

Another major source of interest in the NPP, as well as potential explanations for when it is hard, come from statistical physics.
In the 1980s, Derrida introduced the eponymous _random energy model (REM)_, a simplified example of a spin glass in which, unlike the Sherrington-Kirkpatrick or other $p$-spin glass models, the possible energy levels are indepedent of each other @derridaRandomEnergyModelLimit1980 @derridaRandomenergyModelExactly1981 @baukeNumberPartitioningRandom2004.
Despite this simplicity, this model made possible heuristic analyses of the Parisi theory for mean field spin glasses, and it was suspected that arbitrary random discrete systems would locally behave like the REM @baukeUniversalityLevelStatistics2004 @kistlerDerridasRandomEnergy2014.
The NPP was the first system for which this local REM conjecture was shown @borgsProofLocalREM2009 @borgsProofLocalREM2009a.
In addition, in the case when the $g_i$ are independently chosen uniformly over ${1,2,...,2^M}$, Gent and Walsh conjectured that the hardness of finding perfect partitions (i.e., with discrepancy zero if $sum_i g_i$ is even, and one else) was controlled by the parameter $kappa := m/n$ @gentAnalysisHeuristicsNumber1998 @gentPhaseTransitionsAnnealed2000.
Mertens soon gave a nonrigorous statistical mechanics argument suggesting the existence of a phase transition from $kappa < 1$ to $kappa > 1$: that is, while solutions exist in the low $kappa$ regime, they stop existing in the high $kappa$ regime @mertensPhysicistsApproachNumber2001.
It was also observed that this phase transition coincided with the empirical onset of computational hardness for typical algorithms, and Borgs, Chayes, and Pittel proved the existence of this phase transition soon after @hayesEasiestHardProblem2002 @borgsPhaseTransitionFinitesize2001.
(concluding sentence meow)

// algorithmic gap

== The Statistical-to-Computational Gap

Many problems involving searches over random combinatorial structures (i.e., throughout high-dimensional statistics) are known to exhibit a statistical-to-computational gap: the optimal values which are known to exist via non-constructive, probabilistic methods are far better than those achievable by known algorithms.
In the pure optimization setting, such gaps are exhibited in random constraint satisfaction @mezardClusteringSolutionsRandom2005 @achlioptasAlgorithmicBarriersPhase2008 @kothariSumSquaresLower2017, finding maximal independent sets in sparse random graphs @gamarnikLimitsLocalAlgorithms2014 @coja-oghlanIndependentSetsRandom2015, the largest submatrix problem @gamarnikFindingLargeSubmatrix2016 @gamarnikOverlapGapProperty2021a, and the $p$-spin and diluted $p$-spin models @gamarnikOverlapGapProperty2019 @montanariOptimizationSherringtonKirkpatrickHamiltonian2019 @chenSuboptimalityLocalAlgorithms2019.
These gaps also arise in various "planted" models, such as matrix or tensor PCA @berthetComputationalLowerBounds2013 @lesieurMMSEProbabilisticLowrank2015 @lesieurPhaseTransitionsSparse2015 @hopkinsTensorPrincipalComponent2015 @hopkinsPowerSumofsquaresDetecting2017 @arousAlgorithmicThresholdsTensor2020,
high-dimensional linear regression @gamarnikSparseHighDimensionalLinear2019 @gamarnikHighDimensionalRegressionBinary2019,
or the infamously hard planted clique problem @jerrumLargeCliquesElude1992 @deshpandeImprovedSumofSquaresLower2015 @mekaSumofsquaresLowerBounds2015 @barakNearlyTightSumofSquares2016 @gamarnikLandscapePlantedClique2019.
(meow why does this indicate hardness beyond NP?)


The NPP is no exception: despite its apparent simplicity, its continual focus in the random optimization literature comes from the shocking width of its associated statistical-to-computational gap.
On the statistical side, the landmark result here is by Karmarkar et al., who showed that when the $g_i$ are i.i.d.random variables, with distribution sufficiently nice,
#footnote[Specifically, having bounded density, variance $sigma^2$, and finite 4th moment.] <foot_nice>
then the minimum discrepancy of @eq_npp_first is $Theta(sqrt(N) 2^(-N))$ as $N to infinity$ with high probability as $N to infinity$ @karmarkarProbabilisticAnalysisOptimum1986.
Their result also extends to _even partitions_, where the sizes of each subset is equal (i.e., for $N$ even), worsening only to $Theta( N 2^(-N))$.
Yet the best known algorithms cannot achieve discrepancies close to this in polynomial time.

A first approach to the NPP, often termed the _greedy heuristic_, would be to sort the $N$ inputs, place the largest in one subset, and place the subsequent largest numbers in the subset with the smaller total running sum.
This takes $O(N log N)$ time (due to the sorting step), but achieves a discrepancy of $O(N^(-1))$, extremely far off from the statistical optimum @mertensEasiestHardProblem2003.
More recently, Krieger et al. developed an algorithm achieving a discrepancy of $O(N^(-2))$, but in exchange for this poor performance, their algorithm solves for a balanced partition, which makes it useful for randomized control trials applications @kriegerNearlyRandomDesigns2019.

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

For the multidimensional VBP case, Spencer showed in 1985 that the worse-case discrepancy of the VBP was at most $6sqrt(N)$ for $d=N$ and $norm(bold(g)_i)_infinity <= 1$ for all $1 <= i <= N$ @spencerSixStandardDeviations1985.
However, his argument is an application of the probabilistic method, and does not construct such a solution.
In the average case, Turner et al. proved that, under similar regularity assumptions on the $bold(g)_i$,@foot_nice the minimum discrepancy is $Theta(sqrt(N) 2^(-N slash d))$ for all $d <= o(N)$, with high probability @turnerBalancingGaussianVectors2020.
For the regime $delta=Theta(N)$, Aubin et al. conjecture there exists an explicit function $c(delta)$ such that for $delta > 0$, then the discrepancy in the $d=delta N$ regime is $c(delta) sqrt(N)$ with high probability @aubinStorageCapacitySymmetric2019.
To this end, Turner et al. also showed that for $d <= delta N$, one can achieve $O(sqrt(N) 2^(-1 slash delta))$ with probability at least 99% @turnerBalancingGaussianVectors2020.
On the algorithmic side, they generalized the Karmarkar-Karp algorithm to VBP, which, for $2 <= d = O(sqrt( log N))$ finds partitions with discrepancy $2^(-Theta(log^2 N slash d))$, reproducing the gap of classical Karmarkar-Karp.
On the other hand, in the superlinear regime $d >= 2 N$, this average-case discrepancy worsens to $tilde(O)(sqrt(N log(2d slash N)))$ @chandrasekaranIntegerFeasibilityRandom2013.
Yet, many proposed algorithms can achieve similar discrepancies, which is believed to be optimal for $d >= N$ @spencerSixStandardDeviations1985 @bansalConstructiveAlgorithmsDiscrepancy2010 @lovettConstructiveDiscrepancyMinimization2012 @rothvossConstructiveDiscrepancyMinimization2016.
(concluding sentence)

== Algorithmic Hardness and Landscape Obstructions

Classical algorithmic complexity theory -- involving classes such as P, NP, etc. -- is poorly suited to describing the hardness of random optimization problems, as these classes are based on the worst-case performance of available algorithms.
In many cases, the statistically possible performance of solutions to random instances of these NP-complete problems will be far better than the worst-case analysis would suggest.
How then, can we extend complexity theory to describe problems which, like the NPP, are hard on average?
The past two decades of research have shown that many methods can provide evidence of this average-case hardness, such as the failure of Markov chain algorithms
@jerrumLargeCliquesElude1992 @gamarnikAlgorithmicObstructionsRandom2021b @huangStrongLowDegree2025,
the failure of approximate message passing (AMP) algorithms
@zdeborovaStatisticalPhysicsInference2016 @bandeiraNotesComputationaltostatisticalGaps2018,
or lower bounding performance against the Sum-of-Squares heirarchy or the statistical query model
@hopkinsTensorPrincipalComponent2015 @hopkinsPowerSumofsquaresDetecting2017 @raghavendraHighdimensionalEstimationSumofsquares2019 @barakNearlyTightSumofSquares2016 @kearnsEfficientNoisetolerantLearning1998 @diakonikolasStatisticalQueryLower2017 @feldmanStatisticalAlgorithmsLower2016.

One particularly interesting approach is to prove random-case to worst-case reductions: if one shows that a polynomial-time algorithm for solving random instances could be used to design a polynomial-time algorithm for arbitrary instances, then assuming the problem was known to be in NP, it can be concldued that no such polynomial-time algorithm for the average case can exist @gamarnikOverlapGapProperty2021.
This method has been used to show hardness for sparse PCA, detecting planted independent subgraphs, and more by reducing to the random planted clique problem @berthetComputationalLowerBounds2013 @brennanOptimalAverageCaseReductions2019 @brennanReducibilityComputationalLower2019.
To this extent, Hoberg et al. provided such evidence of hardness for the NPP by showing that a polynomial-time approximation oracle that achieved discrepancies around $O(2^sqrt(N))$ could give polynomial-time approximations for Minkowski's problem, the latter of which is known to be hard @hobergNumberBalancingHard2016.
More recently, Vafa and Vaikuntanathan showed that the Karmarkar-Karp algorithm's performance was nearly tight, assuming the worst-case hardness of the shortest vector problem on lattices @vafaSymmetricPerceptronsNumber2025.
Other conjectures suggested that the onset of algorithmic hardness was related to phase transitions in the solution landscapes, something which shown for random K-SAT, but this fails to describe hardness for optimization problems.

A more recent and widely successful approach is based on analyzing the geometry of the solution landscapes.
Many of the "hard" random optimization problems have a certain disconnectivity property, known as the _overlap gap property (OGP)_ @gamarnikOverlapGapProperty2021.
Roughly, this means there exist $0 <= nu_1 < nu_2$ such that, for every two near-optimal states $x,x'$ for a particular instance $g$ of the problem either have $d(x,x')<nu_1$ or $d(x,x') > nu_2$.
That is, every pair of solutions are either close to each other, or much further away - the condition that $nu_1 < nu_2$ ensures that the "diameter" of solution clusters is much smaller than the separation between these clusters.
#footnote[This is called the "overlap" gap property because, in the literature, this is often described in terms of the inner product of the solutions, as opposed to the distance between them.]
Beyond ruling out the existence of pairs of near solutions with $d(x,x') in [nu_1,nu_2]$, a common extension is the _multioverlap OGP (m-OGP)_: given an ensemble of $m$ strongly correlated instances, there do not exist $m$-tuples of near solutions all equidistant from each other.
This extension is often useful to lower the "threshold" at which the OGP starts to appear.
Once established, the OGP and m-OGP, which is intrinsic to the problem itself, can then be leveraged to rule out the success of a wide class of stable algorithms @achlioptasSolutionSpaceGeometryRandom2006 @achlioptasAlgorithmicBarriersPhase2008 @mezardClusteringSolutionsRandom2005 @gamarnikLimitsLocalAlgorithms2014 @gamarnikLowDegreeHardnessRandom2020 @rahmanLocalAlgorithmsIndependent2017 @weinOptimalLowDegreeHardness2020.

For the NPP, it was expected for decades that the "brittleness" of the solution landscape would be a central barrier in finding successful algorithms to close the statistical-to-computational gap. Mertens wrote in 2001 that any local heuristics, which only looked at fractions of the domain, would fail to outperform random search @mertensPhysicistsApproachNumber2001[#sym.section 4.3].
This was backed up by the failure of many algorithms based on locally refining KK-optimal solutions, such as simulated annealing
@arguelloRandomizedMethodsNumber1996 @storerProblemSpaceLocal1996 @johnsonOptimizationSimulatedAnnealing1989b @johnsonOptimizationSimulatedAnnealing1991 @alidaeeNewModelingSolution2005.
To that end, more recent approaches for algorithmic development are rooted in more global heuristics
@kraticaTwoMetaheuristicApproaches2014 @corusArtificialImmuneSystems2019 @santucciImprovedMemeticAlgebraic2021,
and some of the most interesting directions in algorithmic development for the NPP comes from quantum computing: as this is outside our scope, we encourage the interested reader to consult @asproniAccuracyMinorEmbedding2020 @wenOpticalExperimentalSolution2023.
The main result to this effect comes from Gamarnik and Kızıldağ, who proved that for $m$ of constant order, the m-OGP for NPP held for discrepancies of $2^(-Theta(N))$ (i.e. the statistical optimum), but was absent for smaller discrepancies of $2^(-E_N)$ with $omega(1) <= E_N <= o(N)$ @gamarnikAlgorithmicObstructionsRandom2021b.
They do show, however, that the m-OGP in for $E_N >= omega(sqrt(N log N))$ could be recovered for $m$ superconstant.
This allowed them to prove that for $epsilon in (0,1 slash 5)$, no stable algorithm (suitably defined) could find solutions with discrepancy $2^(-E_N)$ for $omega(n log^(-1/5 + epsilon) N) <= E_N$ @gamarnikAlgorithmicObstructionsRandom2021b[Thm. 3.2].
These results point to the efficacy of using landscape obstructions to show algorithmic hardness for the NPP, which we'll take advantage of in @section_hardness.
// However, their proof of the OGP, which relies on a first-moment computation, is inherently global, and we'll see that it is possible to improve this result in @section_hardness.

== Our Results <section_intro_results>

Low degree heuristic: degree $D$ algorithms are a proxy for the class of $e^(tilde(O)(D))$-time algorithms.

#definition[Strong Low-Degree Hardness @huangStrongLowDegree2025[Def. 3]][
  A sequence of random search problems -- a $N$-indexed sequence of input vectors $g_N in RR^(d_N)$ and random subsets $S_N = S_N (g_N) subeq Sigma_N$, exhibits _strong low degree hardness (SLDH) up to degree $D <= o(D_N)$_ if, for all sequences of degree $o(D_N)$ algorithms $alg_N: (g,omega) mapsto x$ with $EE norm(alg(y_N))^2 <= O(N)$, we have
  $ PP(alg(g_N,omega) in S_N) <= o(1). $
] <def_sldh>

There are two related notions of degree which we want to consider in @def_sldh.
The first is traditional polynomial degree, applicable for algorithms given in each coordinate by low degree polynomial functions of the inputs.
The second uses the more general notion of _coordinate degree_: a function $f: RR^N to RR$ has coordinate degree $D$ if it can be expressed as a linear combination of functions depending on combinations of no more than $D$ coordinates.
()

Our reasons for condisdering low degree algorithms are twofold.


#theorem[Results of @section_hardness_poly][
  The NPP exhibits SLDH for degree $D$ polynomial algorithms, when
  #enum(
    numbering: "(a)",
    indent: 0.5em,
    [$D <= o(exp_2(delta N slash 2))$ when $E = delta N$ for $delta > 0$;],
    [$D <= o(exp_2(E slash 4))$ when $omega(log N) <= E <= o(N)$.],
  )
]

#theorem[Results of @section_hardness_lcd][
  The NPP exhibits SLDH for coordinate degree $D$ algorithms, when
  #enum(
    numbering: "(a)",
    indent: 0.5em,
    [$D <= o(N)$ when $E = delta N$ for $delta > 0$;],
    [$D <= o(E slash log^2 N)$ when $omega(log^2 N) <= E <= o(N)$.],
  )
]

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

