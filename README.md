# treesiv

> Tree-based sieves for natural numbers in Lean4.

This library contains a data structure that models the natural numbers as a tree of arithmetic sequences.

---

An **arithmetic sequence** is the result of applying a binomial with integer coefficients to the natural numbers (including 0).

For example, the natural numbers themselves are described by the arithmetic sequence `0+1n`, the evens by `0+2n` and the odds by `1+2n`.

A **sieve** ("siv"), in the mathematical sense, is an algorithm that filters out members of a set.

This library presents a tree data structure where each node contains the coeficients of an arithmetic sequence, and a flag indicating whether or not that sequence has been "filtered out".

Child nodes are generally partitions of the node above it.

For example, the root node might be all natural numbers, and its children might be the evens and odds.

A famous example of a sieve is the the Sieve of Eratosthenes for finding prime numbers, where multiples of each newly found prime are filtered out.

In this library, to filter out the mulitples of 2, you could partition the naturals into evens and odds, and then flag the even numbers or trim the tree to make the odd numbers your new root node.
