#import "environments.typ": *

#import "symbols.typ": *

= Introduction

Overview of number partitioning problem.

Application: randomized control trials.

Other applications.
- Circuit design, etc.

Importance as a basic NP-complete problem.

Two questions of interest:
+ What is optimal solution.
+ How to find optimal solution.



== Physical Interpretations

== Statistical-to-Computational Gap



== Number Packing Problem

Let $N$ be the dimensionality, and $Sigma_N := { plus.minus 1}$ be the binary cube.
Suppose we're given $g ~ #stdnorm$.
We want to find $x in Sigma_N$ such that we minimize $abs(inn(x, g))$.

#definition[
  Let $delta > 0$.
  The #emph[solution set] $S(delta;g)$ is the set of all $x in Sigma_N$ that are #emph[$delta$-optimal], satisfying
  $ 1 / sqrt(N) abs(inn(g,x)) <= 2^(-delta N). $ <eq_npp>
] <number_packing>

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
+

Glossary:
+ "instance"/"disorder" - $g$, instance of the NPP problem
+ "discrepancy" - for a given $g$, value of $min _(x in Sigma_N) abs(inn(g,x))$
+ "energy" - negative exponent of discrepancy, i.e. if discrepancy is $2^(-E)$, then energy is $E$. Lower energy indicates "worse" discrepancy.
+ "near-ground state"/"approximate solution"


== Literature Review

@achlioptasAlgorithmicBarriersPhase2008
- S2C gap for random constraint satisfaction

@achlioptasSolutionSpaceGeometryRandom2006
-

@addario-berryLocalOptimaSherringtonKirkpatrick2017
-

@alidaeeNewModelingSolution2005
-

@arguelloRandomizedMethodsNumber1996
-

@asproniAccuracyMinorEmbedding2020
-

@aubinStorageCapacitySymmetric2019
-

@bandeiraNotesComputationaltostatisticalGaps2018
-

@bansalConstructiveAlgorithmsDiscrepancy2010
-

@barakNearlyTightSumofSquares2016
-

@baukeNumberPartitioningRandom2004
-

@bayatiCombinatorialApproachInterpolation2013
-

@berthetComputationalLowerBounds2013
-

@boettcherAnalysisKarmarkarKarpDifferencing2008
-

@borgsPhaseTransitionFinitesize2001
-

@brennanOptimalAverageCaseReductions2019
-

@brennanReducibilityComputationalLower2019
-

@chandrasekaranIntegerFeasibilityRandom2013
-

@chenSuboptimalityLocalAlgorithms2019
-

@coffmanjr.ApplicationBinPackingMultiprocessor1978
-

@coffmanProbabilisticAnalysisPacking1991
-

@coja-oghlanIndependentSetsRandom2015
-

@corusArtificialImmuneSystems2019
-

@deshpandeImprovedSumofSquaresLower2015
-

@diakonikolasStatisticalQueryLower2017
-

@feldmanStatisticalAlgorithmsLower2016
-

@ferreiraProbabilisticAnalysisNumber1998
-

@gamarnikAlgorithmicObstructionsRandom2021b
-

@gamarnikAlgorithmsBarriersSymmetric2022
-

@gamarnikComputingPartitionFunction2021
-

@gamarnikHardnessRandomOptimization2022a
-

@gamarnikHighDimensionalRegressionBinary2019
-

@gamarnikLandscapePlantedClique2019
-

@gamarnikLimitsLocalAlgorithms2013
-

@gamarnikOverlapGapProperty2019
-

@gamarnikOverlapGapProperty2021
-

@gamarnikOverlapGapProperty2021a
-

@gamarnikPerformanceSequentialLocal2017
-

@gamarnikSparseHighDimensionalLinear2019
-

@gareyComputersIntractabilityGuide1979
-

@gentAnalysisHeuristicsNumber1998
-

@gentPhaseTransitionsAnnealed2000
-

@harshawBalancingCovariatesRandomized2023
-

@hastieElementsStatisticalLearning2009
-

@hatamiLimitsLocallyGlobally2014
-

@hobergNumberBalancingHard2016
-

@hopkinsPowerSumofsquaresDetecting2017
-

@hopkinsStatisticalInferenceSum2018
-

@hopkinsTensorPrincipalComponent2015
-

@huangStrongLowDegree2025
-

@jerrumLargeCliquesElude1992
-

@johnsonOptimizationSimulatedAnnealing1989b
-

@johnsonOptimizationSimulatedAnnealing1991
-

@karmarkarProbabilisticAnalysisOptimum1986
-

@karmarkerDifferencingMethodSet1983
-

@kearnsEfficientNoisetolerantLearning1998
-

@kizildagPlantedRandomNumber2023
-

@kojicIntegerLinearProgramming2010
-

@korfApproximateOptimalSolutions1995
-

@korfCompleteAnytimeAlgorithm1998
-

@korfMultiwayNumberPartitioning2009
-

@kothariSumSquaresLower2017
-

@kraticaTwoMetaheuristicApproaches2014
-

@kriegerNearlyRandomDesigns2019
-

@kuniskyNotesComputationalHardness2019
-

@lauerLargeIndependentSets2007
-

@levyDeterministicDiscrepancyMinimization2017
-

@lovettConstructiveDiscrepancyMinimization2012
-

@luekerNoteAveragecaseBehavior1987
-

@mekaSumofsquaresLowerBounds2015
-

@merkleHidingInformationSignatures1978
-

@mertensEasiestHardProblem2003
-

@mertensPhysicistsApproachNumber2001
-

@mezardClusteringSolutionsRandom2005
-

@michielsPerformanceRatiosDifferencing2003
-

@odonnellAnalysisBooleanFunctions2021
-

@raghavendraHighdimensionalEstimationSumofsquares2019
-

@rahmanLocalAlgorithmsIndependent2017
-

@rothvossConstructiveDiscrepancyMinimization2016
-

@santucciImprovedMemeticAlgebraic2021
-

@storerProblemSpaceLocal1996
-

@tsaiAsymptoticAnalysisAlgorithm1992
-

@turnerBalancingGaussianVectors2020
-

@wainwrightHighDimensionalStatisticsNonAsymptotic2019
-

@weinOptimalLowDegreeHardness2020
-

@wenOpticalExperimentalSolution2023
-

@yakirDifferencingAlgorithmLDM1996
- Showed LDM achieves $n^log(n)$ performance despite being a simple heuristic, for uniform instance.

@zdeborovaStatisticalPhysicsInference2016
-

== Our Results <subsection_intro_results>
