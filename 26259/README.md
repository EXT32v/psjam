# 26259
https://www.acmicpc.net/problem/26259

## Idea
- Implement memoization monad (using Map)
- Prove that memoization moand preserve property about input and output of target function.
- Implement PMap, which ensures that proposition `P key value` holds for every `(key, value)` pair in the map.

I think PMap and Memoization can be used generally, not only for this problem.