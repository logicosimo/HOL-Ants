# HOL-Ants: Pathfinding ants formalised in the HOL Light theorem prover

This repository contains a detailed, principled model in HOL Light simulating foraging ants in an idealized environment. 

The model is designed to explore long-term dynamics based on pheromone release and tracking. 

We formally verify in HOL Light the convergence of the ant colony on the shortest path to a food source during foraging activities. 

## Associated papers

- Maggesi, M. and Perini Brogi, C., 2024. Rigorous Analysis of Idealised Pathfinding Ants in Higher-Order Logic. To appear in AISoLA 2024, Springer Lecture Notes in Computer Science ([HAL Preprint online](https://hal.science/hal-04620418/))
- Perini Brogi, C. and Maggesi, M., 2024. Analysing Collective Adaptive Systems by Proving Theorems. To appear in REoCAS Colloquium 2024, Springer Lecture Notes in Computer Science

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

(c) Marco Maggesi and Cosimo Perini Brogi, 2023-2024
