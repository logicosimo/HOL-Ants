# HOL-Ants: Pathfinding ants formalised in the HOL Light theorem prover

This repository contains a detailed, principled model in HOL Light simulating foraging ants in an idealized environment. 

The model is designed to explore long-term dynamics based on pheromone release and tracking. 

We formally verify in HOL Light the convergence of the ant colony on the shortest path to a food source during foraging activities.

To enhance the performance of simulations, we introduce an interface between HOL Light terms and expressions of SMT-LIB2 to bridge proof contraints with SMT problems.

Some examples of translations from HOL Light goals to resolution statements about colony dynamics are collected in the folder `smt2`.

## Associated papers

- Maggesi, M., Perini Brogi, C. (2025). Rigorous Analysis of Idealised Pathfinding Ants in Higher-Order Logic. In: Margaria, T., Steffen, B. (eds) Leveraging Applications of Formal Methods, Verification and Validation. Rigorous Engineering of Collective Adaptive Systems. ISoLA 2024. Lecture Notes in Computer Science, vol 15220. Springer, Cham.  [https://doi.org/10.1007/978-3-031-75107-3_18](https://doi.org/10.1007/978-3-031-75107-3_18)
- Perini Brogi, C., Maggesi, M. (2025). Analysing Collective Adaptive Systems by Proving Theorems. In: Margaria, T., Steffen, B. (eds) Leveraging Applications of Formal Methods, Verification and Validation. REoCAS Colloquium in Honor of Rocco De Nicola. ISoLA 2024. Lecture Notes in Computer Science, vol 15219. Springer, Cham. [https://doi.org/10.1007/978-3-031-73709-1_14](https://doi.org/10.1007/978-3-031-73709-1_14)

## How to run the code

1. Start HOL Light.
2. Add this directory to the `load_path` (replace "/path/to/HOL-Ants" with the actual path):
   ```
   load_path := "/path/to/HOL-Ants" :: !load_path;;
   ```
3. Load make.ml:
   ```
   loadt "make.ml";;
   ```

(c) Marco Maggesi and Cosimo Perini Brogi, 2023-2025
