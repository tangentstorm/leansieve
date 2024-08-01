-- The twin prime conjecture
import Mathlib

theorem tpc :  (∀n:Nat, ∃p q:Nat, Nat.Prime p ∧ Nat.Prime q ∧ q-p = 2) := by
  sorry


/-

under what conditions would this be true for C in a rake sieve?

- a rake r contains a large number of tines (arithmetic sequences with same delta)
- hd : the rake's delta is a primorial (product of first n primes)
- hkd : the k term of each tine is coprime to the delta
- let K := map λt=>t.k tines
- let C := min K
- hC: Nat.Prime C  -- (this is the "fundamental theorem" of a prime sieve)
- let H := C²      -- the "horizon"
- let Q := [ k ∈ K | k < H ]  ( the "queue" of already identified but as-yet-unreported primes )
- hQ: ∀ q ∈ Q, Nat.prime q := (because of hCo, the next composite number is C²)
- def hasTwin r : Prop := ∃p q ∈ r.Q, q-p = 2

Do I have any reason to believe this is true?

Here are the first few iterations of the sieve.
|q| is the number of primes it has found less than h
|x| is the number of sequences whose k ≥ h.

r₀ | d:1         c:2 h:4     |q|:1   |x|:0        |q+x|:1
r₁ | d:2         c:3 h:9     |q|:1   |x|:0        |q+x|:1
r₂ | d:6         c:5 h:25    |q|:2   |x|:0        |q+x|:2
r₃ | d:30        c:7 h:49    |q|:8   |x|:0        |q+x|:8
r₄ | d:210       c:11 h:121  |q|:26  |x|:22       |q+x|:48
r₅ | d:2310      c:13 h:169  |q|:34  |x|:446      |q+x|:480
r₆ | d:30030     c:17 h:289  |q|:55  |x|:5705     |q+x|:5760
r₇ | d:510510    c:19 h:361  |q|:65  |x|:92095    |q+x|:92160
r₈ | d:9699690   c:23 h:529  |q|:91  |x|:1658789  |q+x|:1658880
r₉ | d:223092870 c:29 h:841  |q|:137 |x|:36495223 |q+x|:36495360

It *appears* that |q| grows slowly at each step, but the sieve is so slow
that it's hard to generate more terms.

Here are the differences in the size of q at each step: 0,1,6,18,8,21,10,26,46
The OEIS doesn't suggest much of interest here.

So far, this tells me nothing about the number of twin values in Q or K, but we
do know some exist.

The basic problem is that we observe a bunch of twin sequences.
At each step, we partition those sequences into c copies and remove 1.

Let's break this into two parts. In the partitioning step, the number
of sequences and the number of twin sequences both multiply by c.

In the removal step, 1/c of the newly-generated twins become singletons.
Why? Well, we have k₀ and k₀+2 and we add the ranges 0..(c-1) to each.
Exactly two of these get struck out, but the one that gets struck out
is different for k₀ vs k₀+2. So I would say we have (c-2)*t twins now,
and 2 new singletons.

How many of these are less than c²? If we could show that a twin prime always exists betwen p and p^2 that would be something.


# twin primes up to 500
-- jlang:
-- |: tp500 =: {{> ({~ [:I. 2=-~/every) 2<\ p:i. _1 p: y }} 500
3 5 11 17 29 41 59 71 101 107 137 149 179 191 197 227 239 269 281 311 347 419 431 461
5 7 13 19 31 43 61 73 103 109 139 151 181 193 199 229 241 271 283 313 349 421 433 463

Interesting that (269 271 -: 264 + 5 7) appears. 264 is the current provable minimal prime gap.


Anyway, I guess what I'm trying to see is whether these pairs are less than the square
of a prime.

   (1{|:tp500) < table *:p:i.10
┌───┬─────────────────────────────────┐
│<  │4 9 25 49 121 169 289 361 529 841│
├───┼─────────────────────────────────┤
│  5│0 1  1  1   1   1   1   1   1   1│
│  7│0 1  1  1   1   1   1   1   1   1│
│ 13│0 0  1  1   1   1   1   1   1   1│
│ 19│0 0  1  1   1   1   1   1   1   1│
│ 31│0 0  0  1   1   1   1   1   1   1│
│ 43│0 0  0  1   1   1   1   1   1   1│
│ 61│0 0  0  0   1   1   1   1   1   1│
│ 73│0 0  0  0   1   1   1   1   1   1│
│103│0 0  0  0   1   1   1   1   1   1│
│109│0 0  0  0   1   1   1   1   1   1│
│139│0 0  0  0   0   1   1   1   1   1│
│151│0 0  0  0   0   1   1   1   1   1│
│181│0 0  0  0   0   0   1   1   1   1│
│193│0 0  0  0   0   0   1   1   1   1│
│199│0 0  0  0   0   0   1   1   1   1│
│229│0 0  0  0   0   0   1   1   1   1│
│241│0 0  0  0   0   0   1   1   1   1│
│271│0 0  0  0   0   0   1   1   1   1│
│283│0 0  0  0   0   0   1   1   1   1│
│313│0 0  0  0   0   0   0   1   1   1│
│349│0 0  0  0   0   0   0   1   1   1│
│421│0 0  0  0   0   0   0   0   1   1│
│433│0 0  0  0   0   0   0   0   1   1│
│463│0 0  0  0   0   0   0   0   1   1│
└───┴─────────────────────────────────┘

that's the table of whether the upper value of the pair is less than
the square of one of the first 10 primes. (2 3 5 7 11 13 17 19 23 29)

Does this matter? The idea I was reaching for is that the square of the primes grows very quickly,
and if it grows fast enough, then more twins will be admitted into the queue than can be discarded.

bertrand's postulate / (Chebyshev's theorem):
  n≥3 → ∃p, Prime p ∧ p>n ∧ p<2*n-2
https://en.wikipedia.org/wiki/Bertrand%27s_postulate
In lean: alas bertrand := Nat.exists_prime_lt_and_le_two_mul

This gives us an upper bound on the gap between a prime and the next prime. I'm not sure why I think it's useful.

How many primes do we admit into the queue at each step?

Well, we don't know how many there are, but it's all the primes between c² and c'².
All the primes < c² are already in the queue, and then at the next step, we add up to c'².

The new primes we're going to add are already in K... We literally just take everything from
k that is < c'² and move it over to q.

Will c² never split a pair of twin primes? Well, c² is odd, so it can't be k+1,
but it could be either k or k+2. So yes, this is how twin sequences become singletons.

The j table above suggests that there may always be a twin prime between p and p^2,
and the pattern does seem to continue:

load 'viewmat'
tp =: {{> ({~ [:I. 2=-~/every) 2<\ p:i. _1 p: y }}
viewmat (*:p:i.200) >/~ 1{|:tp 10000

But that's just evidence.

Is there an argument that some number of primes exist between p and p^2?

Yes: from bertrand's postulate, we can conclude that at least floor(log2(n))
primes exist between n and n^2.  (because n=2^log2(n)), so log2(n) is the number
of times we can double before we cross n^2.

I don't think it makes sense spending energy trying to prove that anything
ever happens here unless there's some way to explain under what conditions
it'll happen.

So for example, a new twin pair is admitted into Q whenever:
- there is a pair in K that is strictly less than C².

We always add SOMETHING to Q at each step, because:
-  Q is < C² and Q' is < C'².
-  ... ???

Well, who's to say there are any primes between C² and C'²?
In practice, there's always something to scratch off, but who's to say
it's in this range?

-/
example {y n : Int} (hy: y = (n+2)^2 - n^2) := by
  calc
    y = (n+2)^2 - n^2 := hy
    _ = 4*n + 4 := by ring

/-
Okay, so since the smallest possible change from c to c' is 2,
c'² is at least (4c²+4) greater than c².

Here's the general formula that uses the actual change:
-/

example {y n k : Int} (hy: y = (n+k)^2 - n^2) := by
  calc
    y = (n+k)^2 - n^2 := hy
    _ = n^2 + 2*k*n + k^2 - n^2 := by ring
    _ = 2*k*n + k^2 := by ring

/-
What to conclude from this? Well, if the gap between c² and (c+2)²
that means... What? There's actually nothing here yet that even
proves there's a prime between those two numbers.

Legendre conjectured that a prime exists between any n and (n+1)²
but this is unproven. https://mathworld.wolfram.com/LegendresConjecture.html


It could be the case that all the numbers between c² and (c+2)² are
already in Q, but in practice it appears that doesn't happen. (But of
course no matter how long I look, I'm only seeing a tiny sample of
numbers near 0).

DoT pointed out that wheels are symmetrical, if you vizualize
the interferece patterns for sin(x*π/pᵢ) for the first n primes.
These waves are 0 at the multiples of their respective primes.
At the spots where none of the waves are 0, you find all the
coprime numbers. ( https://www.geogebra.org/calculator/bfvsf9sf )

It's a neat visualization, and it suggests something about the
numbers you're "marking out" - namely, whenever you mark
out a number, you can also mark out the number equidistant
from half the primorial you're dealing with.

Anyway, I don't see much point to any of this yet. I should probably
stick to simple statements I can prove.


-/
