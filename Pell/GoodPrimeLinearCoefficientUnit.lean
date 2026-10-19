import Pell.GoodPrimeAnnulus
import Mathlib.Data.ZMod.Units
import Mathlib.RingTheory.Int.Basic

/-!
# Linear coefficients are units at good prime products

If an integer coefficient divides the bad-prime certificate, then every prime
in the associated good annulus is coprime to that coefficient.  For two such
primes this gives a unit modulo their product, exactly as required by the
linear Jacobi rectangle estimate.
-/

namespace PellPaper

/-- A divisor of the certificate is a unit modulo the product of any two
primes from the corresponding good annulus.  Distinctness is unnecessary for
this elementary unit statement. -/
theorem isUnit_intCast_zmod_mul_of_dvd_goodPrimeAnnulus
    (N : ℕ) (Delta a : ℤ) (p q : ℕ)
    (hp : p ∈ goodPrimeAnnulus N Delta)
    (hq : q ∈ goodPrimeAnnulus N Delta) (ha : a ∣ Delta) :
    IsUnit (a : ZMod (p * q)) := by
  have hpprime : p.Prime :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
  have hqprime : q.Prime :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2
  have hpnDelta : ¬(p : ℤ) ∣ Delta := (Finset.mem_filter.mp hp).2
  have hqnDelta : ¬(q : ℤ) ∣ Delta := (Finset.mem_filter.mp hq).2
  have hpna : ¬(p : ℤ) ∣ a := fun hpa => hpnDelta (hpa.trans ha)
  have hqna : ¬(q : ℤ) ∣ a := fun hqa => hqnDelta (hqa.trans ha)
  have hpInt : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hpprime
  have hqInt : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hqprime
  have hpCoprime : IsCoprime (p : ℤ) a :=
    hpInt.irreducible.coprime_iff_not_dvd.mpr hpna
  have hqCoprime : IsCoprime (q : ℤ) a :=
    hqInt.irreducible.coprime_iff_not_dvd.mpr hqna
  rw [ZMod.coe_int_isUnit_iff_isCoprime]
  simpa only [Int.natCast_mul] using
    (IsCoprime.mul_left_iff.mpr ⟨hpCoprime, hqCoprime⟩)

/-- If a nonzero binary linear form has each nonzero coefficient dividing the
certificate, one coefficient is a unit modulo every good-prime product. -/
theorem linearCoefficient_isUnit_or_isUnit_of_goodPrimeAnnulus
    (N : ℕ) (Delta a b : ℤ) (p q : ℕ)
    (hp : p ∈ goodPrimeAnnulus N Delta)
    (hq : q ∈ goodPrimeAnnulus N Delta)
    (hab : a ≠ 0 ∨ b ≠ 0)
    (ha : a ≠ 0 → a ∣ Delta) (hb : b ≠ 0 → b ∣ Delta) :
    IsUnit (a : ZMod (p * q)) ∨ IsUnit (b : ZMod (p * q)) := by
  rcases hab with ha0 | hb0
  · exact Or.inl
      (isUnit_intCast_zmod_mul_of_dvd_goodPrimeAnnulus N Delta a p q hp hq (ha ha0))
  · exact Or.inr
      (isUnit_intCast_zmod_mul_of_dvd_goodPrimeAnnulus N Delta b p q hp hq (hb hb0))

end PellPaper
