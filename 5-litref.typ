#pagebreak()

= Literature Review

== Applications of NPP

@tsaiAsymptoticAnalysisAlgorithm1992
- Application of NPP to process scheduling


@kriegerNearlyRandomDesigns2019
- NPP for randomized contorl testing

== Algorithms for solving real-world cases

@johnsonOptimizationSimulatedAnnealing1989b
- Overview of simulated annealing

@johnsonOptimizationSimulatedAnnealing1991
- Failure of sim annealing for NPP

@storerProblemSpaceLocal1996
- Several order of magnitude improvement over annealing, but with greater commputation time, by modifying differencing heuristic.

@kojicIntegerLinearProgramming2010
- Using linear programing solver for NPP.

@santucciImprovedMemeticAlgebraic2021
- Memetic algebraic diffeq for NPP
- Evolutionary algorithm
- Experimental calculation

=== Quantum algorithms

@asproniAccuracyMinorEmbedding2020
- Quantum hardware for solving NPP.

@wenOpticalExperimentalSolution2023
- Experimental solution using quantum computing.

== Algorithms for average time case

@korfApproximateOptimalSolutions1995
- Initial work on CKK

@korfCompleteAnytimeAlgorithm1998
- Extend KK to complete algorithm; will get better

@luekerNoteAveragecaseBehavior1987
- PDM heuristic fails

@yakirDifferencingAlgorithmLDM1996
- Showed LDM achieves $n^log(n)$ performance despite being a simple heuristic, for uniform instance.

== Statistical to Computational Gaps

== OGP Examples

=== Hardness Examples

@jerrumLargeCliquesElude1992
- MCMC can't find cliques; algorithm failure

@zdeborovaStatisticalPhysicsInference2016
- Inference using algorithms - overview of pedagogy using statistical physics framework.

== Low-Degree Heuristic

@kuniskyNotesComputationalHardness2019
- Kunisky, Wein, Banderia - discussion on low degree heuristic for hypothesis testing.

----------------

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

@hatamiLimitsLocallyGlobally2014
- Local-global study of sparse graphs

@hobergNumberBalancingHard2016
- Hardness of number balancing (diff from NPP) by reduction to Minkowski/shortest vector.

@hopkinsPowerSumofsquaresDetecting2017
- Signal recovery using sum-of-squares semidefinite programming
- Early suggestion of low degree heuristic

@hopkinsStatisticalInferenceSum2018
- Hopkins thesis - intoduced low degree hypothesis

@hopkinsTensorPrincipalComponent2015
- Tensor PCA via sum of squares

@huangStrongLowDegree2025
- SLDH paper



@karmarkarProbabilisticAnalysisOptimum1986
- original analysis of hardness

@karmarkerDifferencingMethodSet1983
- KK algorithm - time $O(N log N)$

@kearnsEfficientNoisetolerantLearning1998
- Classification and learning in presence of noise

@kizildagPlantedRandomNumber2023
- Planted version of NPP, with explicit analysis + hardness results



@korfMultiwayNumberPartitioning2009
- CKK for larger sets

@kothariSumSquaresLower2017
- Sum of squares for constraint satisfaction.

@kraticaTwoMetaheuristicApproaches2014
- Heuristics for multidimensional NPP



@lauerLargeIndependentSets2007
- Independent sets in regular graphs of girth

@levyDeterministicDiscrepancyMinimization2017
- Discrepancy coloring - poly time algorithm

@lovettConstructiveDiscrepancyMinimization2012
- Constructive proof of discrepancy minimizing coloring


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



@turnerBalancingGaussianVectors2020
- Multidimensional NPP - poly time algorithm achieving $e^(-Omega(log^2 N/m))$, for $m = O(sqrt(log n))$.

@vafaSymmetricPerceptronsNumber2025
- Assuming hardness of shortest vector on lattice, derived polynomial-time hardness for NPP;
- Prove KK is tight; no poly time algorithm achieves energy of $Omega(log^3 N)$

@weinOptimalLowDegreeHardness2020
- Low degree polynomial hardness for max independent set.
