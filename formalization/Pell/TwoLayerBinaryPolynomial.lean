import Pell.IntegralAuxiliaryRelation
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic

/-!
# Literal binary components of an integral two-layer auxiliary form

The existing coefficient index records the exponent of the second target
coordinate. Each source-coordinate slice is therefore an actual homogeneous
binary polynomial with monomials X₀^(b-k) X₁^k. The coefficient and evaluation
identities below preserve that indexing, including at degree zero.
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

/-- The homogeneous target polynomial belonging to one source coordinate
of the existing two-layer coefficient vector. -/
def twoLayerBinaryPolynomial (b : ℕ) (f : twoLayerFormIndex b → ℤ) (a : Fin 2) :
    MvPolynomial (Fin 2) ℤ :=
  ∑ k : Fin (b + 1), MvPolynomial.C (f (a, k)) *
    MvPolynomial.X 0 ^ (b - k.val) * MvPolynomial.X 1 ^ k.val

/-- Both source slices have the original target degree, even when a slice
is zero or when the target degree is zero. -/
theorem twoLayerBinaryPolynomial_isHomogeneous (b : ℕ)
    (f : twoLayerFormIndex b → ℤ) (a : Fin 2) :
    (twoLayerBinaryPolynomial b f a).IsHomogeneous b := by
  apply MvPolynomial.IsHomogeneous.sum
  intro k _
  have hk : k.val ≤ b := Nat.le_of_lt_succ k.isLt
  have h := ((MvPolynomial.isHomogeneous_X_pow (R := ℤ) (0 : Fin 2)
    (b - k.val)).C_mul (f (a, k))).mul
      (MvPolynomial.isHomogeneous_X_pow (R := ℤ) (1 : Fin 2) k.val)
  simpa only [Nat.sub_add_cancel hk] using h

private theorem binary_term_eq_monomial (c : ℤ) (m n : ℕ) :
    (MvPolynomial.C c * MvPolynomial.X (0 : Fin 2) ^ m *
      MvPolynomial.X 1 ^ n : MvPolynomial (Fin 2) ℤ) =
    MvPolynomial.monomial (Finsupp.single 0 m + Finsupp.single 1 n) c := by
  rw [MvPolynomial.C_mul_X_pow_eq_monomial, ← MvPolynomial.monomial_add_single]

private theorem coeff_twoLayerBinaryPolynomial_sum (b : ℕ)
    (f : twoLayerFormIndex b → ℤ) (a : Fin 2) (e : Fin 2 →₀ ℕ) :
    (twoLayerBinaryPolynomial b f a).coeff e =
      ∑ k : Fin (b + 1),
        if Finsupp.single 0 (b - k.val) + Finsupp.single 1 k.val = e then f (a, k)
        else 0 := by
  unfold twoLayerBinaryPolynomial
  rw [MvPolynomial.coeff_sum]
  simp_rw [binary_term_eq_monomial, MvPolynomial.coeff_monomial]

/-- The coefficient at the original exponent pair is exactly the original
coefficient, without summation collisions or an extra height factor. -/
theorem coeff_twoLayerBinaryPolynomial (b : ℕ) (f : twoLayerFormIndex b → ℤ)
    (a : Fin 2) (k : Fin (b + 1)) :
    (twoLayerBinaryPolynomial b f a).coeff
      (Finsupp.single 0 (b - k.val) + Finsupp.single 1 k.val) = f (a, k) := by
  rw [coeff_twoLayerBinaryPolynomial_sum]
  rw [Finset.sum_eq_single k]
  · simp
  · intro l _ hl
    apply if_neg
    intro heq
    apply hl
    apply Fin.ext
    have h := congrArg (fun e : Fin 2 →₀ ℕ => e 1) heq
    simpa using h
  · simp

/-- A uniform integer coefficient bound for the vector is inherited by
each literal binary component with no loss. -/
theorem abs_coeff_twoLayerBinaryPolynomial_le (b : ℕ)
    (f : twoLayerFormIndex b → ℤ) (a : Fin 2) (H : ℤ) (hH : 0 ≤ H)
    (hf : ∀ ab, |f ab| ≤ H) (e : Fin 2 →₀ ℕ) :
    |(twoLayerBinaryPolynomial b f a).coeff e| ≤ H := by
  classical
  by_cases he : ∃ k : Fin (b + 1),
      Finsupp.single 0 (b - k.val) + Finsupp.single 1 k.val = e
  · obtain ⟨k, rfl⟩ := he
    rw [coeff_twoLayerBinaryPolynomial]
    exact hf (a, k)
  · rw [coeff_twoLayerBinaryPolynomial_sum]
    have hz : ∀ k : Fin (b + 1),
        ¬ Finsupp.single 0 (b - k.val) + Finsupp.single 1 k.val = e := by
      simpa only [not_exists] using he
    simpa only [if_neg (hz _), Finset.sum_const_zero, abs_zero] using hH

/-- Literal polynomial evaluation is the original target-monomial sum. -/
theorem eval_twoLayerBinaryPolynomial (b : ℕ) (f : twoLayerFormIndex b → ℤ)
    (a : Fin 2) (y : ℤ × ℤ) :
    MvPolynomial.eval ![y.1, y.2] (twoLayerBinaryPolynomial b f a) =
      ∑ k : Fin (b + 1), f (a, k) * twoLayerFormTarget b y k := by
  simp [twoLayerBinaryPolynomial, twoLayerFormTarget, mul_assoc]

/-- Exact compatibility with the existing source-target auxiliary-form
evaluation, with the two source coordinates in their original order. -/
theorem twoLayerFormEval_eq_binaryPolynomial (b : ℕ)
    (f : twoLayerFormIndex b → ℤ) (lambda y : ℤ × ℤ) :
    twoLayerFormEval b f (lambda, y) =
      lambda.1 * MvPolynomial.eval ![y.1, y.2] (twoLayerBinaryPolynomial b f 0) +
      lambda.2 * MvPolynomial.eval ![y.1, y.2] (twoLayerBinaryPolynomial b f 1) := by
  rw [twoLayerFormEval, Fintype.sum_prod_type, Fin.sum_univ_two,
    eval_twoLayerBinaryPolynomial, eval_twoLayerBinaryPolynomial,
    Finset.mul_sum, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro k _ <;>
    simp [twoLayerFormMonomial, twoLayerFormSource, mul_left_comm]

/-- A nonzero coefficient vector has a genuinely nonzero binary component.
This does not assert nonvanishing of any later substituted eliminant. -/
theorem twoLayerBinaryPolynomial_zero_ne_or_one_ne (b : ℕ)
    (f : twoLayerFormIndex b → ℤ) (hf : f ≠ 0) :
    twoLayerBinaryPolynomial b f 0 ≠ 0 ∨ twoLayerBinaryPolynomial b f 1 ≠ 0 := by
  by_contra h
  simp only [not_or, not_not] at h
  apply hf
  funext ab
  rcases ab with ⟨a, k⟩
  have hz : twoLayerBinaryPolynomial b f a = 0 := by
    fin_cases a
    · exact h.1
    · exact h.2
  have hc := coeff_twoLayerBinaryPolynomial b f a k
  rw [hz, MvPolynomial.coeff_zero] at hc
  exact hc.symm

end
end PellPaper
