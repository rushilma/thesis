#import "environments.typ": *

#import "symbols.typ": *

= Introduction

Overview of number partitioning problem.

Application: randomized control trials.

Other applications.
- Circuit design, etc.

Importance as a basic NP-complete problem.
- One of the six basic NP-complete problems of Garey and Johnson @gareyComputersIntractabilityGuide1979, and the only one to deal with numbers.

Two questions of interest:
+ What is optimal solution.
+ How to find optimal solution.



== Physical Interpretations

== Statistical-to-Computational Gap


Low degree heuristic: degree $D$ algorithms are a proxy for the class of $e^(tilde(O)(D))$-time algorithms.


== Number Packing Problem

Let $N$ be the dimensionality, and $Sigma_N := { plus.minus 1}$ be the binary cube.
Suppose we're given $g ~ #stdnorm$.
We want to find $x in Sigma_N$ such that we minimize $abs(inn(x, g))$.


#definition[
  Let $x in Sigma_N$. The #emph[energy of $x$ (with respect to the instance $g$)] is
  $
    E(x;g) := - log abs(inn(g,x)).
  $
  The #emph[solution set $S(E;g)$] is the set of all $x in Sigma_N$ that have energy at least $E$, i.e. that satisfy
  $
    abs(inn(g,x)) <= 2^(-E).
  $ <eq_npp>
] <def_npp_statement>

- This terminology is motivated by the statistical physics literature, wherein random optimiztation problems are often reframed as energy maximization over a random landscape @mertensPhysicistsApproachNumber2001.
- Observe that minimizing the discrepancy $abs(inn(g,x))$ corresponds to maximizing the energy $E$.


@eq_npp Hi


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

== Glossary and conventions

Conventions:
+ $log$ means $log$ in base 2, $exp$ is $exp$ base 2 - natural log/exponent is $ln$/$e^x$.
+ If $x in RR^N$ and $S subeq [N]$, then $x_S$ is vector with
  $ (x_S)_i = cases(x_i #h(2em) &i in S\,, 0 &"else.") $
  In particular, for $x,y in RR^N$,
  $ inn(x_S, y) = inn(x,y_S) = inn(x_S,y_S). $

Glossary:
+ "instance"/"disorder" - $g$, instance of the NPP problem
+ "discrepancy" - for a given $g$, value of $min _(x in Sigma_N) abs(inn(g,x))$
+ "energy" - negative exponent of discrepancy, i.e. if discrepancy is $2^(-E)$, then energy is $E$. Lower energy indicates "worse" discrepancy.
+ "near-ground state"/"approximate solution"


== Literature Review

@achlioptasAlgorithmicBarriersPhase2008
- Phase transitions for random constraint satisfaction
- S2C gap for random constraint satisfaction

@achlioptasSolutionSpaceGeometryRandom2006
- Random constraint satisfaction

@addario-berryLocalOptimaSherringtonKirkpatrick2017
- Local algorithms for SK.

@alidaeeNewModelingSolution2005
- NPP as unconstrained quadratic binary problem, and efficient metaheuristic algorithm.

@arguelloRandomizedMethodsNumber1996
- Randomized differencing heuristic for NPP; computational simulations.

@asproniAccuracyMinorEmbedding2020
- Quantum hardware for solving NPP.

@aubinStorageCapacitySymmetric2019
- OGP for SBPs.

@bandeiraNotesComputationaltostatisticalGaps2018
- Computational gaps in terms of signal-to-noise and S2C for Bayesian inference.

@bansalConstructiveAlgorithmsDiscrepancy2010
- Generalized version of NPP with multiple sets

@barakNearlyTightSumofSquares2016
- Sum of squares bound

@baukeNumberPartitioningRandom2004
- REM approach to NPP (Derrida model)

@bayatiCombinatorialApproachInterpolation2013
- S2C for random graphs

@berthetComputationalLowerBounds2013
- S2C for sparce PCA

@bismuthPartitioningProblemsSplittings2024
- Generalization of NPP allowing some numbers to be split up

@boettcherAnalysisKarmarkarKarpDifferencing2008
- Fix constant $alpha$ in KK algorithm discrepancy

@borgsPhaseTransitionFinitesize2001
- Phase transitions for integral NPP

@brennanOptimalAverageCaseReductions2019
- Strong hardness for sparse PCA

@brennanReducibilityComputationalLower2019
- S2C in sparce problems via planted clique
- Spiritually similar to conditional landscape obstructions, in that you fix one instance and study how it changes??

@chandrasekaranIntegerFeasibilityRandom2013
- Random polytopes

@chenSuboptimalityLocalAlgorithms2019
- Local algorithms fail for max-cut

@coffmanjr.ApplicationBinPackingMultiprocessor1978
- Motivation for bin packing application to multiprocessor scheduling

@coffmanProbabilisticAnalysisPacking1991
- Book summarizing results of Karmarkar-Karp

@coja-oghlanIndependentSetsRandom2015
- Independent sets in random graphs

@corusArtificialImmuneSystems2019
- Evolutionary algorithms for NP hard NPP

@deshpandeImprovedSumofSquaresLower2015
- Sum of squares bounds

@diakonikolasStatisticalQueryLower2017
- Estimation of Gaussian mixtures

@feldmanStatisticalAlgorithmsLower2016
- Planted clique detection

@ferreiraProbabilisticAnalysisNumber1998
- Physics perspective for uniform instances

@gamarnikAlgorithmicObstructionsRandom2021b
- prove OGP and stable hardness for NPP

@gamarnikAlgorithmsBarriersSymmetric2022
- Barriers in Symmetric Binary Perceptron

@gamarnikComputingPartitionFunction2021
- Average hardness of computing SK partition function

@gamarnikHardnessRandomOptimization2022a
- GJW22, low degree poly algorithms for Boolean circuits
- Lemma 3.4!

@gamarnikHighDimensionalRegressionBinary2019
- Phase transition in high-dim regression with binary coeffs

@gamarnikLandscapePlantedClique2019
- Planted clique: OGP for dense subgraphs

@gamarnikLimitsLocalAlgorithms2013
- Original OGP paper with Gamarnik-Sudan

@gamarnikOverlapGapProperty2019
- OGP and AMP

@gamarnikOverlapGapProperty2021
- Overview/summary of OGP

@gamarnikOverlapGapProperty2021a
- Principal submatrix recovery

@gamarnikPerformanceSequentialLocal2017
- Local algorithms for NAE-k-SAT

@gamarnikSparseHighDimensionalLinear2019
- Local search for sparse high-dim regression

@gareyComputersIntractabilityGuide1979
- Garey-Johnson book on NP hardness

@gentAnalysisHeuristicsNumber1998
- Phase transitions for NPP: performance of algorithms depends on their constrainedness.
- i.e. number of their solutions, e.g. if on state space of $2^N$ states, this parameter is > 1, you're screwed
  $ kappa := 1 - log("# of solns") / N $

@gentPhaseTransitionsAnnealed2000
- Phase transitions in simulated annealing

@harshawBalancingCovariatesRandomized2023
- Application of NPP to radomized control testing

@hastieElementsStatisticalLearning2009
- Textbook

@hatamiLimitsLocallyGlobally2014
- Local-global study of sparse graphs

@hobergNumberBalancingHard2016
- Hardness of number balancing (diff from NPP) by reduction to Minkowski/shortest vector.

@hopkinsPowerSumofsquaresDetecting2017
- Signal recovery using sum-of-squares semidefinite programming
- Early suggestion of low-degree heuristic

@hopkinsStatisticalInferenceSum2018
- Hopkins thesis - intoduced low-degree hypothesis

@hopkinsTensorPrincipalComponent2015
- Tensor PCA via sum of squares

@huangStrongLowDegree2025
- SLDH paper

@jerrumLargeCliquesElude1992
- MCMC can't find cliques; algorithm failure

@johnsonOptimizationSimulatedAnnealing1989b
- Overview of simulated annealing

@johnsonOptimizationSimulatedAnnealing1991
- Failure of sim annealing for NPP

@karmarkarProbabilisticAnalysisOptimum1986
- original analysis of hardness

@karmarkerDifferencingMethodSet1983
- KK algorithm - time $O(N log N)$

@kearnsEfficientNoisetolerantLearning1998
- Classification and learning in presence of noise

@kizildagPlantedRandomNumber2023
- Planted version of NPP, with explicit analysis + hardness results

@kojicIntegerLinearProgramming2010
- Using linear programing solver for NPP.

@korfApproximateOptimalSolutions1995
- Initial work on CKK

@korfCompleteAnytimeAlgorithm1998
- Extend KK to complete algorithm; will get better

@korfMultiwayNumberPartitioning2009
- CKK for larger sets

@kothariSumSquaresLower2017
- Sum of squares for constraint satisfaction.

@kraticaTwoMetaheuristicApproaches2014
- Heuristics for multidimensional NPP

@kriegerNearlyRandomDesigns2019
- NPP for randomized contorl testing

@kuniskyNotesComputationalHardness2019
- Kunisky, Wein, Banderia - discussion on low-degree heuristic for hypothesis testing.

@lauerLargeIndependentSets2007
- Independent sets in regular graphs of girth

@levyDeterministicDiscrepancyMinimization2017
- Discrepancy coloring - poly time algorithm

@lovettConstructiveDiscrepancyMinimization2012
- Constructive proof of discrepancy minimizing coloring

@luekerNoteAveragecaseBehavior1987
- PDM heuristic fails

@mekaSumofsquaresLowerBounds2015
- Sum of squares in planted case

@merkleHidingInformationSignatures1978
- Using NPP for cryptography

@mertensEasiestHardProblem2003
- Phase transition and overview of NPP

@mertensPhysicistsApproachNumber2001
- Physics notation as applied to NPP
- "Any heuristic that exploits a fraction of the domain, generating and evaluating a series of feasible configurations, cannot be significantly better than random search." section 4.3

@mezardClusteringSolutionsRandom2005
- Random k-SAT/CSP clustering

@michielsPerformanceRatiosDifferencing2003
- Worst case performance of KK algorithm when attempting balanced Number Partitioning

@odonnellAnalysisBooleanFunctions2021
- Textbook on Boolean functions

@raghavendraHighdimensionalEstimationSumofsquares2019
- Hidh dimensional estimation for SoS - more SoS stuff

@rahmanLocalAlgorithmsIndependent2017
- Failure of local algorithm for independent sets in graphs

@rothvossConstructiveDiscrepancyMinimization2016
- Partial coloring of sets (discrepancy min)

@santucciImprovedMemeticAlgebraic2021
- Memetic algebraic diffeq for NPP
- Evolutionary algorithm
- Experimental calculation

@storerProblemSpaceLocal1996
- Several order of magnitude improvement over annealing, but with greater commputation time, by modifying differencing heuristic.

@tsaiAsymptoticAnalysisAlgorithm1992
- Application of NPP to process scheduling

@turnerBalancingGaussianVectors2020
- Multidimensional NPP - poly time algorithm achieving $e^(-Omega(log^2 N/m))$, for $m = O(sqrt(log n))$.

@vafaSymmetricPerceptronsNumber2025
- Assuming hardness of shortest vector on lattice, derived polynomial-time hardness for NPP;
- Prove KK is tight; no poly time algorithm achieves energy of $Omega(log^3 N)$

@vershyninHighDimensionalProbabilityIntroduction2018
- Textbook on high dim probability

@wainwrightHighDimensionalStatisticsNonAsymptotic2019
- Textbook on high dim statistics

@weinOptimalLowDegreeHardness2020
- Low degree polynomial hardness for max independent set.

@wenOpticalExperimentalSolution2023
- Experimental solution using quantum computing.

@yakirDifferencingAlgorithmLDM1996
- Showed LDM achieves $n^log(n)$ performance despite being a simple heuristic, for uniform instance.

@zdeborovaStatisticalPhysicsInference2016
- Inference using algorithms - overview of pedagogy using statistical physics framework.

== Our Results <subsection_intro_results>
