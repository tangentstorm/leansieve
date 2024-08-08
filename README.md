# leansieve

> Natural number sieves for Lean 4.

This library contains some data structures that model the natural numbers as collections of arithmetic sequences.

---

An **arithmetic sequence** is the result of applying a binomial with integer coefficients to the natural numbers.

For example, the natural numbers themselves are described by the arithmetic sequence `0+1n`, the evens by `0+2n` and the odds by `1+2n`.

A **sieve** ("siv"), in the mathematical sense, is an algorithm that filters out (sifts) members of a set.

For example, the [Sieve of Eratosthenes](https://en.wikipedia.org/wiki/Sieve_of_Eratosthenes) is a famous
mathematical sieve for identifying prime numbers.

In this library:

- `ASeq` models a single arithmetic sequence (`k + d * n`)
- `Rake` represents a collection of arithmetic sequences that share the same delta (`d`).
- `RakeMap` provides a mapping between a Rake and subsets of the natural numbers.
- `PrimeGen` specifies what a prime-generating algorithm
- `PrimeSieve` provides a formal proof of the generic logic of prime sieves like that of Eratosthenes.
- `RakeSieve` provides a (laughably inefficient) prime sieve based on `RakeMap`.

The `RakeSieve` works by repeatedly replacing the initial rake `ge2 := { d:=1, ks=[2] }` (that is, the rake consisting of the single arithmetic sequence `2 + 1 * n`) by partitioning the current list of sequences based
on the lowest constant term.

For example:

```
# initial state. Lowest constant 2 is prime.
2 + 1n

# partition on 2 by composing the current sequence
# with sequences (0..C)+2n. After this step, each sequence
# either produces no multiples of 2, or only multiples of 2.
2 + 1(0+2n) =  3 + 2n   # <- no multiples of 2. keep.
2 + 1(1+2n) =  4 + 2n   # <- all multipels of 2. trim.

# new state. Lowest constant 3 is next prime.
3 + 2n

# partition on 3
3 + 2(0 + 3n) = 3 + 6n  # ← 3(1+3n), so always multiple of 3. discard.
3 + 2(1 + 3n) = 5 + 6n
3 + 2(2 + 3n) = 7 + 6n

# partition on new prime 5.
5 + 6(0 + 5n) = 5  + 30n  # discard
7 + 6(0 + 5n) = 7  + 30n
5 + 6(1 + 5n) = 11 + 30n
7 + 6(1 + 5n) = 13 + 30n
5 + 6(2 + 5n) = 17 + 30n
7 + 6(2 + 5n) = 19 + 30n
5 + 6(3 + 5n) = 23 + 30n
7 + 6(3 + 5n) = 25 + 30n # = 5(5+6n), so discard
5 + 6(4 + 5n) = 29 + 30n
7 + 6(4 + 5n) = 31 + 30n
```

In general, for each new prime `P`, the number of sequences is multiplied by (`P-1`),
which leads to worse-than-exponential growth at each step:

```
step: 0 1 2  3   4    5     6       7        8          9
size: 1 2 8 48 480 5760 92160 1658880 36495360 1021870080
```

Many of the constant terms generated at each step are prime (especially towards the beginning of the list). A variation of the `RakeSieve` algorithm could be constructed that performs its `partition` step lazily and produces all primes up to N with sub-linear time
and space requirements.

At the moment, no such work is planned. If you want an actual prime-generating sieve in lean 4, see [esiv](https://github.com/ykonstant1/esiv). If you want a more theoretical sieve that counts the number of primes in set, see [selbergSieve](https://reservoir.lean-lang.org/@FLDutchmann/selbergSieve)
