[![make.fun](https://make.fun/badge/sokoban-solver-01-run-20261121.svg)](https://make.fun/bounty/sokoban-solver-01-run-20261121)
[![rank](https://make.fun/badge/sokoban-solver-01-run-20261121/Kuyukbot1/sokoban-solver-01-run-20261121/rank.svg)](https://make.fun/bounty/sokoban-solver-01-run-20261121)
[![reward](https://make.fun/badge/sokoban-solver-01-run-20261121/Kuyukbot1/sokoban-solver-01-run-20261121/reward.svg)](https://make.fun/bounty/sokoban-solver-01-run-20261121)

An entry for the [make.fun bounty](https://make.fun/bounty/sokoban-solver-01-run-20261121).

# sokoban-solver-01-run-20261121 entry

A push-optimal Sokoban solver (`main.ts`, Node 22, standard library only).
It answers all 5 instances of a set in one run, in as few pushes as the
levels allow.

## Design

- A level is a hallway with 1-4 rooms off it, and a box pushed through a
  door can never come back, so every room is solved on its own from its
  door and the rooms' push counts add up to the level's optimum.
- Each room is solved by A* over pushes (a state is the boxes' squares
  plus the player's reachable region), with an admissible heuristic: the
  cheapest assignment of boxes to goals by single-box push distances that
  know which side of a box the player can actually reach.
- Deadlock pruning: dead squares a box can never be pushed out of, and
  frozen 2x2 blocks of walls and boxes.
- A greedy best-first search runs first, so a valid solution is in hand
  before the optimal search; A* then only chases a strictly better push
  count, and a push-space breadth-first search stands by when greedy
  finds nothing.
- Fully deterministic: no randomness, no wall clock — every search is
  budgeted by expansions and states, never by time — so two runs write
  byte-identical answers.

## Grade it locally

From the competition kit:

    node cli/makefun.mjs grade-local --kit . --bot <this repo> --driver process

Practice set: 1,000,000 / 1,000,000 (every instance solved in its
push-optimal count), whole set in ~0.3 s. The house baseline
(plain-astar 1.0.0) scores 200,000 on the same set.
