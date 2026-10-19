import Pell.QuadraticIdealNormRamifiedDiscriminant
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-!
# A concrete unique-prime bridge at a ramified discriminant prime

For the rational quadratic algebra attached to a positive fundamental
discriminant `D`, this module turns an explicit divisibility `p ∣ D` into the
two local ideal-theoretic inputs used by
`QuadraticIdealNormLocalUniquePrime`:

* a prime ideal over `(p)` of absolute norm `p`;
* uniqueness of every maximal ideal over `(p)`.

The proof combines the concrete discriminant-to-ramification bridge with
Mathlib's equality between the sum of ramification-index times inertia-degree
and the degree of the extension.  Since this quadratic algebra has degree two,
one ramified prime forces a single prime with ramification index two and
inertia degree one.

This does not prove that a chosen Dirichlet character vanishes at `p`, and it
does not state a local Euler factor or a global Euler-product identity.
-/

namespace PellPaper

noncomputable section

local instance rationalQuadraticAlgebra_ramifiedUniquePrime_numberField_instance (d : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot d)] :
    NumberField (rationalQuadraticAlgebra d) :=
  rationalQuadraticAlgebra_numberField d

private theorem ramification_sum_eq_two_for_rationalQuadraticAlgebra
    (D p : ℕ) (hD : PositiveFundamentalDiscriminant D) (hp : Nat.Prime p) :
    let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
      ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
    let _ : Fact (Nat.Prime p) := ⟨hp⟩
    ∑ Q : (Ideal.span ({(p : ℤ)} : Set ℤ)).primesOver
        (NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))),
      Q.1.ramificationIdx ℤ * Q.1.inertiaDeg ℤ = 2 := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  let _ : Fact (Nat.Prime p) := ⟨hp⟩
  dsimp only
  rw [Ideal.sum_ramification_inertia_eq_finrank]
  rw [NumberField.RingOfIntegers.rank]
  exact rationalQuadraticAlgebra_finrank_eq_two (D : ℤ)

/-- A prime divisor of a positive fundamental discriminant supplies a prime
ideal of absolute norm `p`, and that ideal is the unique maximal ideal above
`(p)` in the ring of integers of the corresponding rational quadratic
algebra.  This establishes only the unique-prime/norm local input; the
separate character-vanishing input remains open. -/
theorem rationalQuadraticAlgebra_exists_uniquePrimeOver_of_prime_dvd_positiveFundamentalDiscriminant
    (D p : ℕ) (hD : PositiveFundamentalDiscriminant D)
    (hp : Nat.Prime p) (hpD : p ∣ D) :
    let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
      ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
    let _ : Fact (Nat.Prime p) := ⟨hp⟩
    ∃ P : Ideal (NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))),
      Ideal.absNorm P = p ∧
        ∀ Q : Ideal (NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))),
          Q.IsMaximal →
          Q.under ℤ = Ideal.span ({(p : ℤ)} : Set ℤ) → Q = P := by
  classical
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  let _ : Fact (Nat.Prime p) := ⟨hp⟩
  dsimp only
  have hpz : Prime (p : ℤ) := by
    rw [Int.prime_iff_natAbs_prime]
    simpa using hp
  have hram : ¬ Algebra.IsUnramifiedIn
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ)))
      (Ideal.span ({(p : ℤ)} : Set ℤ)) := by
    simpa only using
      (rationalQuadraticAlgebra_not_isUnramifiedIn_of_prime_dvd_positiveFundamentalDiscriminant
        D p hD hp hpD)
  have hnotall : ¬ ∀
      (P : Ideal (NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))))
      (_ : P.IsMaximal),
      P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) → Algebra.IsUnramifiedAt ℤ P := by
    intro hall
    apply hram
    exact (NumberField.not_dvd_discr_iff_isUnramifiedIn
      (rationalQuadraticAlgebra (D : ℤ))
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))) hpz).mp
      ((NumberField.not_dvd_discr_iff_forall_liesOver
        (rationalQuadraticAlgebra (D : ℤ))
        (NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))) hpz).mpr hall)
  push Not at hnotall
  obtain ⟨P, hPmax, hPover, hPnotunram⟩ := hnotall
  let _ : P.IsPrime := hPmax.isPrime
  let _ : P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) := hPover
  let PP : (Ideal.span ({(p : ℤ)} : Set ℤ)).primesOver
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))) :=
    Ideal.primesOver.mk (Ideal.span ({(p : ℤ)} : Set ℤ)) P
  let f : (Ideal.span ({(p : ℤ)} : Set ℤ)).primesOver
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))) → ℕ :=
    fun Q => Q.1.ramificationIdx ℤ * Q.1.inertiaDeg ℤ
  have hram_ne_one : P.ramificationIdx ℤ ≠ 1 := by
    intro h
    exact hPnotunram (Ideal.ramificationIdx_eq_one_iff.mp h)
  have hram_pos : 0 < P.ramificationIdx ℤ := Ideal.ramificationIdx_pos P ℤ
  have hinertia_pos : 0 < P.inertiaDeg ℤ := Ideal.inertiaDeg_pos P ℤ
  have hram_ge_two : 2 ≤ P.ramificationIdx ℤ := by omega
  have hPP_ge_two : 2 ≤ f PP := by
    change 2 ≤ P.ramificationIdx ℤ * P.inertiaDeg ℤ
    calc
      2 = 2 * 1 := by omega
      _ ≤ P.ramificationIdx ℤ * P.inertiaDeg ℤ :=
        Nat.mul_le_mul hram_ge_two (by omega)
  have hsum : ∑ Q, f Q = 2 := by
    simpa only [f] using
      (ramification_sum_eq_two_for_rationalQuadraticAlgebra D p hD hp)
  have hPP_le_sum : f PP ≤ ∑ Q, f Q :=
    Finset.single_le_sum (fun Q _ => Nat.zero_le (f Q)) (Finset.mem_univ PP)
  have hPP_eq_two : f PP = 2 := by omega
  have hprime_unique : ∀ Q : (Ideal.span ({(p : ℤ)} : Set ℤ)).primesOver
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))), Q = PP := by
    intro Q
    by_contra hQPP
    have hQmem : Q ∈ Finset.univ.erase PP :=
      Finset.mem_erase.mpr ⟨hQPP, Finset.mem_univ _⟩
    have hQpos : 1 ≤ f Q := by
      change 1 ≤ Q.1.ramificationIdx ℤ * Q.1.inertiaDeg ℤ
      exact Nat.succ_le_iff.mpr (Nat.mul_pos
        (Ideal.ramificationIdx_pos Q.1 ℤ) (Ideal.inertiaDeg_pos Q.1 ℤ))
    have hQ_le_erase : f Q ≤ ∑ R ∈ Finset.univ.erase PP, f R :=
      Finset.single_le_sum (fun R _ => Nat.zero_le (f R)) hQmem
    have herase_pos : 1 ≤ ∑ R ∈ Finset.univ.erase PP, f R :=
      hQpos.trans hQ_le_erase
    have hsplit := Finset.sum_erase_add Finset.univ f (Finset.mem_univ PP)
    omega
  have hproduct : P.ramificationIdx ℤ * P.inertiaDeg ℤ = 2 := by
    simpa only [f, PP] using hPP_eq_two
  have hram_dvd_two : P.ramificationIdx ℤ ∣ 2 := by
    rw [← hproduct]
    exact ⟨P.inertiaDeg ℤ, rfl⟩
  have hram_le_two : P.ramificationIdx ℤ ≤ 2 :=
    Nat.le_of_dvd (by omega) hram_dvd_two
  have hram_eq_two : P.ramificationIdx ℤ = 2 := by omega
  have hinertia_eq_one : P.inertiaDeg ℤ = 1 := by
    apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2)
    calc
      2 * P.inertiaDeg ℤ = P.ramificationIdx ℤ * P.inertiaDeg ℤ := by
        rw [hram_eq_two]
      _ = 2 := hproduct
      _ = 2 * 1 := by omega
  have hPnorm : Ideal.absNorm P = p := by
    calc
      Ideal.absNorm P = p ^ P.inertiaDeg ℤ := (Ideal.pow_inertiaDeg p P).symm
      _ = p := by simp [hinertia_eq_one]
  refine ⟨P, hPnorm, ?_⟩
  intro Q hQmax hQunder
  let _ : Q.IsPrime := hQmax.isPrime
  let _ : Q.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) := ⟨hQunder.symm⟩
  have hQeq : Ideal.primesOver.mk (Ideal.span ({(p : ℤ)} : Set ℤ)) Q = PP :=
    hprime_unique (Ideal.primesOver.mk (Ideal.span ({(p : ℤ)} : Set ℤ)) Q)
  exact congrArg Subtype.val hQeq

end

end PellPaper
