import PrimeGen

/--
A PrimeSieve is a PrimeGen that uses a sieve to generate primes.
In practice this means that it somehow models the set of natural
numbers greater than 1 that are coprime to a list of primes, and
then repeatedly:
  - obtains the minimum of this set as the next prime
  - eliminates multiples of the new prime. -/
class PrimeSieve {α : Type} [PrimeGen α] where
  todo : sorry
