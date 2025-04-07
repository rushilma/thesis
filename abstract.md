# Thesis Details

+ Title of Project: Strong Low Degree Hardness for the Number Partitioning Problem
+ Number of Pages: 43(?)
+ Nominator's Name: Mark Sellke
+ Nominator's Email Address: msellke@fas.harvard.edu

# Thesis (369)

Finding good solutions to the _number partitioning problem (NPP)_ -- that is, finding a partition of a set of $N$ numbers to minimize the discrepancy between the sums of the two subsets -- is a well-studied optimization problem, with applications to statistics, physics, and computer science.
Along with having numerous practical applications in the design of randomized control trials and processor scheduling,
the NPP is famous for possessing a _statistical-to-computational gap_:
assuming the $N$ numbers to be partitioned are i.i.d. standard Normal random variables, the optimal discrepancy is $2^{ -\Theta(N) }$ with high probability, but the best polynomial-time algorithms only find solutions with a discrepancy of $2^{ - \Theta(\log^2 N) }$.
This gap is a common feature in optimization problems over random combinatorial structures, and indicates the need for a theory of computational complexity beyond worst-case analysis.

In this thesis, we prove a strong form of algorithmic hardness for the number partitioning problem, aiming to establish that this statistical-to-computational gap is an intrinsic feature of the NPP.
We study _low degree algorithms_, as they provide both tunable stability behavior and are tractable models for a broad class of algorithms, under the widely successful _low degree heuristic_.
Then, we establish a _brittleness property_ on the geometry of the solution set, which ensures that stable algorithms are unable to efficiently traverse this random landscape.
By combining these notions, we are able to show _strong low degree hardness_, in that low degree algorithms will fail to find good solutions with high probability.
In addition, while we show that low degree polynomial algorithms are structurally ill-suited to the NPP, our results for the more general class of _low coordinate degree algorithms_ demonstrate a sharp tradeoff between algorithmic runtime (vis-à-vis algorithmic complexity) and solution discrepancy, which our analysis suggests is optimal.

Finally, we establish a _repulsion property_, giving a precise tradeoff between the discrepancy of a solution to a fixed instance and its distance to other solutions.
We then leverage this to show that any algorithm fed through a truly randomized rounding scheme will fail to find solutions with high probability.
This work demonstrates the effectiveness of using landscape properties to address questions about algorithmic hardness, and suggests interesting directions for future study.

# FOCS (214)

In the _number partitioning problem (NPP)_ one aims to partition a given set of $N$ real numbers into two subsets with approximately equal sum.
The NPP is a well-studied optimization problem and is famous for possessing a _statistical-to-computational gap_:
when the $N$ numbers to be partitioned are i.i.d. standard Gaussian, the optimal discrepancy is $2^{ -\Theta(N) }$ with high probability, but the best known polynomial-time algorithms only find solutions with a discrepancy of $2^{ - \Theta(\log^2 N) }$.
This gap is a common feature in optimization problems over random combinatorial structures, and indicates the need for a study that goes beyond worst-case analysis.

In this paper, we provide evidence of a nearly tight algorithmic barrier for the number partitioning problem.
Namely we consider the family of low coordinate degree algorithms (with randomized rounding into the Boolean cube), and show that degree $D$ algorithms fail to solve the NPP to accuracy below $2^{ -\tilde{ O }(D) }$.
According to the low degree heuristic, this suggests that simple brute-force search algorithms are nearly unimprovable, give any runtime between polynomial and exponential.
Our proof leverages the isolation of all solutions in the landscape as well as a _conditional OGP_: any given good solution to an NPP instance is, with high probability, destroyed by slightly noising the input.

# Hoopes

150-200 words
non-specialist reader
+ goals of project
+ context within discipline
+ highlight its importance
    - Precise energy-time tradeoff
    - Heuristically optimal result
    - Demonstrates the effectiveness of using landscape properties to address questions about algorithmic hardness, and suggests interesting directions for future study.


## Abstract

Given N numbers, the number partitioning problem (NPP) asks for a partition of this set into two subsets minimizing the "discrepancy," that is, the difference of their sums. Finding solutions, i.e. low-discrepancy partitions, to the NPP has applications for designing randomized trials, scheduling tasks on multicore computers, or implementing public-key encryption. Yet despite its utility, the NPP is infamous for its statistical-to-computational gap: when the inputs are random, the discrepancies of the partitions found by the best-known polynomial-time algorithms are exponentially worse (in N) than the discrepancies probabilistic analysis guarantees are achievable. Such gaps are common in many random combinatorial problems encountered in statistical physics and computer science; such problems are not just NP-hard, but hard on average, preventing the development of efficient practical algorithms.

We prove that for a certain representative class of "low degree" algorithms, there is a precise tradeoff between algorithm complexity and achievable discrepancy. Heuristically, such low degree hardness implies it is impossible to design polynomial-time algorithms which can find better partitions than the current state-of-the-art. That is, the statistical-to-computational gap is impossible to close. Our proof relies on analyzing the random landscape of solutions, an emerging strategy which is effective for studying high-dimensional random optimization.

## Scratch

and are evidence of problems which are not only NP-hard, but also hard on average imply the existence of complexity classes which, unlike P or NP, go beyond worst-case performance.

This work demonstrates the effectiveness of using landscape properties to address questions about algorithmic hardness, and suggests interesting directions for future study.

Heuristically, our results imply a precise tradeoff between the runtime of an algorithm and the discrepancy of solutions it can find.

That is, not only are the current best algorithms the best which can ever exist, there is likely no way to find the statistically optimal partitions without taking exponential time in N.
By a well-evidenced

evidence of an algorithmic barrier -- i.e., the impossibility 

for the number partitioning problem.




Our proof leverages the isolation of all solutions in the landscape as well as a _conditional OGP_: any given good solution to an NPP instance is, with high probability, destroyed by slightly noising the input.
Finally, we establish a _repulsion property_, giving a precise tradeoff between the discrepancy of a solution to a fixed instance and its distance to other solutions.
We then leverage this to show that any algorithm fed through a truly randomized rounding scheme will fail to find solutions with high probability.

Using intuitions from statistical physics, in which partitions with lower discrepancies are deemed to have higher "energy," we reframe solving the NPP as an energy maximization problem.
Then, we use the "brittleness" of the random energy landscape 

- What is number partitioning problem
    - applications
    - statistical to computational gap

- our results
    - algorithmic hardness
    - tunable tight runtime bound

- importance
    - overlap gap property, use of landscape properties in showing hardness

# Jarell Hoopes Abstract

Mixed Hodge structures, introduced by Pierre Deligne, are fundamental objects in Hodge theory which precisely relate the geometry of algebraic varieties to the linear algebra of their cohomology spaces.
Mixed Hodge structures, introduced by Pierre Deligne, are fundamental objects in Hodge theory which precisely relate the geometry of algebraic varieties to the linear algebra of their cohomology spaces.

In this thesis, we draw from classical textbooks, cutting-edge research, and historical accounts to deliver a unifying contemporary exposition on the profound theory and applications of these objects.
In this thesis, we unify historical accounts, classical textbooks, and cutting-edge research to deliver a contemporary exposition on the profound theory and applications of these objects.

First, we trace the historical progression of Hodge theory, beginning with Niels Henrik Abel's pioneering work on elliptic integrals through to advancements in the present day, to illuminate the confluence of ideas which eventually led to the study of mixed Hodge structures.
First, we trace the historical progression of Hodge theory, going from Abel's pioneering work on elliptic integrals to Hodge's analysis of the cohomology of smooth varieties, culminating with Deligne's extension of Hodge theory to general varieties.

Then, we develop this theory of mixed Hodge structures, carefully interleaving general constructions with detailed examples and computations in geometrically significant scenarios to make this notoriously abstract theory more accessible.
Then, we develop the theory of mixed Hodge structures, interleaving abstract constructions with specific examples of geometrically significant computations to make this notoriously opaque subject more accessible 

Finally, we reveal the subtle yet important applications of mixed Hodge theory, from Maxim Kontsevich's theorem on the birational invariance of Calabi-Yau Hodge diamonds, which has far-reaching implications in string theory, to Philippe Du Bois' extension of differentials to singular varieties, which unlocks some of the most powerful techniques for understanding singularities in modern algebraic geometry.

Finally, we explore the important applications of mixed Hodge theory, from Kontsevich's theorem on the birational invariance of Calabi-Yau Hodge diamonds, which has far-reaching implications in string theory,
to Du Bois' extension of differentials to singular varieties, which forms the basis for our most powerful techniques for understanding singularities in modern algebraic geometry.

Altogether, we narrate the rich mathematical story of Hodge theory from Deligne to Du Bois.

(Why study these varieties?)
Varieties show up in the most important question in AG, the classification of varieties, but lack differential geometric methods

In algebraic geometry, singular varieties are the cornerstone of Mori's Minimal Model Program in algebraic geometry and Mori's minimal model program,
but are impenetrable by differential geometric methods.

Mixed Hodge structures are fundamental objects in Hodge theory which precisely relate the geometry of algebraic varieties to the linear algebra of their cohomology spaces.
In this thesis, we unify historical accounts, classical textbooks, and cutting-edge research to deliver a contemporary exposition on the profound theory and applications of these objects.

First, we trace the historical progression of , going from Abel's pioneering work on elliptic integrals to Hodge's analysis of the cohomology of smooth varieties, culminating with Deligne's extension of Hodge theory to general varieties.
Then, we develop the theory of mixed Hodge structures, interleaving abstract constructions with specific examples of geometrically significant computations to make this notoriously opaque subject more accessible 
Finally, we explore the important applications of mixed Hodge theory, from Kontsevich's theorem on the birational invariance of Calabi-Yau Hodge diamonds, which has far-reaching implications in string theory, to Du Bois' extension of differentials to singular varieties, which forms the basis for our most powerful techniques for understanding singularities in modern algebraic geometry.
Altogether, we narrate the rich mathematical story of Hodge theory from Deligne to Du Bois.

186 words, so 15-30 words extra
