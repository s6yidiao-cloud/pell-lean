import Pell.BinaryCommonFactorHeight
import Pell.HomogeneousTwoLayerPacking
import Pell.PaddedCoprimeHomogenizeEvaluation
import Pell.PointwiseEliminantProjection

/-!
# Bounded common-factor selection for the actual two-layer coefficient vector

The original integral auxiliary form splits exactly into a homogeneous target
factor and another integral two-layer form. Residual component nonvanishing
at primitive targets is proved, not assumed. All source-independent zeros
remain visible in the exact evaluation factorization.
-/

namespace PellPaper
noncomputable section

/-- The literal binary components inherit any nonnegative real coefficient
budget for the original two-layer vector without rounding or height loss. -/
theorem abs_real_coeff_twoLayerBinaryPolynomial_le (n : ℕ)
    (f : twoLayerFormIndex n → ℤ) (a : Fin 2) (H : ℝ) (hH : 0 ≤ H)
    (hf : ∀ ab, |((f ab : ℤ) : ℝ)| ≤ H) (e : Fin 2 →₀ ℕ) :
    |(((twoLayerBinaryPolynomial n f a).coeff e : ℤ) : ℝ)| ≤ H := by
  by_cases he : e.degree = n
  · have hsum : e 0 + e 1 = n := by
      simpa only [Finsupp.degree_eq_sum, Fin.sum_univ_two] using he
    let k : Fin (n + 1) := ⟨e 1, by omega⟩
    have hexp : Finsupp.single 0 (n - k.val) + Finsupp.single 1 k.val = e := by
      ext i
      fin_cases i <;> simp [k]
      omega
    rw [← hexp, coeff_twoLayerBinaryPolynomial]
    exact hf (a, k)
  · rw [(twoLayerBinaryPolynomial_isHomogeneous n f a).coeff_eq_zero he]
    simpa only [Int.cast_zero, abs_zero] using hH

/-- A nonzero original coefficient vector has actual bounded integral
common-target and residual factors, of complementary degrees. The residual
vector is nonzero and its components do not both vanish at primitive targets.
The evaluation identity holds at all integral source and target vectors,
without primitivity restrictions on that identity. -/
theorem exists_bounded_twoLayer_common_factor
    (n : ℕ) (f : twoLayerFormIndex n → ℤ) (hf₀ : f ≠ 0)
    (H : ℝ) (hH : 0 ≤ H) (hf : ∀ ab, |((f ab : ℤ) : ℝ)| ≤ H) :
    ∃ (d b : ℕ) (D : MvPolynomial (Fin 2) ℤ) (f' : twoLayerFormIndex b → ℤ),
      d + b = n ∧ D ≠ 0 ∧ D.IsHomogeneous d ∧ f' ≠ 0 ∧
      (∀ a : Fin 2, twoLayerBinaryPolynomial n f a =
        D * twoLayerBinaryPolynomial b f' a) ∧
      (∀ e, |((D.coeff e : ℤ) : ℝ)| ≤ (2 : ℝ) ^ n * ((n : ℝ) + 1) * H) ∧
      (∀ ab, |((f' ab : ℤ) : ℝ)| ≤ (2 : ℝ) ^ n * ((n : ℝ) + 1) * H) ∧
      (∀ y : Fin 2 → ℤ, IsCoprime (y 0) (y 1) →
        MvPolynomial.eval y (twoLayerBinaryPolynomial b f' 0) ≠ 0 ∨
          MvPolynomial.eval y (twoLayerBinaryPolynomial b f' 1) ≠ 0) ∧
      (∀ lambda y : ℤ × ℤ, twoLayerFormEval n f (lambda, y) =
        MvPolynomial.eval ![y.1, y.2] D * twoLayerFormEval b f' (lambda, y)) := by
  obtain ⟨D, A, B, d, b, hD₀, hAB₀, hD, hA, hB, hdb, hFA, hFB,
    hrel, hmax, hHD, hHA, hHB⟩ := exists_bounded_homogeneous_binary_common_factor
      (twoLayerBinaryPolynomial n f 0) (twoLayerBinaryPolynomial n f 1) n H
      (twoLayerBinaryPolynomial_isHomogeneous n f 0)
      (twoLayerBinaryPolynomial_isHomogeneous n f 1)
      (twoLayerBinaryPolynomial_zero_ne_or_one_ne n f hf₀) hH
      (abs_real_coeff_twoLayerBinaryPolynomial_le n f 0 H hH hf)
      (abs_real_coeff_twoLayerBinaryPolynomial_le n f 1 H hH hf)
  let f' := homogeneousTwoLayerCoefficients b A B
  have hpack := twoLayerBinaryPolynomial_homogeneousTwoLayerCoefficients b A B hA hB
  have hAr : (binaryDehomogenizeAtOne A).homogenize b = A := by
    apply Polynomial.homogenize_eq_of_isHomogeneous hA
    rfl
  have hBr : (binaryDehomogenizeAtOne B).homogenize b = B := by
    apply Polynomial.homogenize_eq_of_isHomogeneous hB
    rfl
  refine ⟨d, b, D, f', hdb, hD₀, hD,
    (homogeneousTwoLayerCoefficients_ne_zero_iff b A B hA hB).mpr hAB₀, ?_, hHD,
    abs_real_homogeneousTwoLayerCoefficients_le b A B _ hHA hHB, ?_, ?_⟩
  · intro a
    fin_cases a
    · change twoLayerBinaryPolynomial n f 0 =
        D * twoLayerBinaryPolynomial b (homogeneousTwoLayerCoefficients b A B) 0
      rw [hpack.1]
      exact hFA
    · change twoLayerBinaryPolynomial n f 1 =
        D * twoLayerBinaryPolynomial b (homogeneousTwoLayerCoefficients b A B) 1
      rw [hpack.2]
      exact hFB
  · intro y hy
    have h := eval_max_homogenize_ne_zero_or_ne_zero_of_int_isRelPrime
      (binaryDehomogenizeAtOne A) (binaryDehomogenizeAtOne B) hrel y hy
    rw [← hmax, hAr, hBr] at h
    simpa only [f', hpack.1, hpack.2] using h
  · intro lambda y
    rw [twoLayerFormEval_eq_binaryPolynomial, hFA, hFB,
      twoLayerFormEval_homogeneousTwoLayerCoefficients b A B hA hB, map_mul, map_mul]
    ring

/-- The exact original-coefficient family is bounded by its retained
common-target zero branch and twice the residual eliminant-square targets.
The factor and component hypotheses are the outputs of the selection theorem
above; no irreducibility, nonzero-eliminant or analytic counting premise is used. -/
theorem card_twoLayer_solutions_le_target_factor_zeros_add_twice_squares
    (n b : ℕ) (f : twoLayerFormIndex n → ℤ) (f' : twoLayerFormIndex b → ℤ)
    (D : MvPolynomial (Fin 2) ℤ)
    (hfactor : ∀ a : Fin 2, twoLayerBinaryPolynomial n f a =
      D * twoLayerBinaryPolynomial b f' a)
    (hcomponents : ∀ y : Fin 2 → ℤ, IsCoprime (y 0) (y 1) →
      MvPolynomial.eval y (twoLayerBinaryPolynomial b f' 0) ≠ 0 ∨
        MvPolynomial.eval y (twoLayerBinaryPolynomial b f' 1) ≠ 0)
    (g : Fin 3 → Fin 2 → ℤ) (c : ℤ) (hc : c ≠ 0)
    (S : Finset ((Fin 2 → ℤ) × (Fin 2 → ℤ))) (T : Finset (Fin 2 → ℤ))
    (hS : ∀ p ∈ S, IsCoprime (p.1 0) (p.1 1) ∧ IsCoprime (p.2 0) (p.2 1) ∧
      twoLayerFormEval n f ((p.1 0, p.1 1), (p.2 0, p.2 1)) = 0 ∧
      quadraticLinearFormEval g p.1 p.2 = c)
    (hT : ∀ p ∈ S, p.2 ∈ T) :
    S.card ≤ (S.filter fun p => MvPolynomial.eval p.2 D = 0).card +
      2 * (T.filter fun y => IsSquare (MvPolynomial.eval y (twoLayerEliminant b f' g c)) ∧
        MvPolynomial.eval y (twoLayerEliminant b f' g c) ≠ 0).card := by
  apply card_surface_solutions_le_common_factor_zeros_add_twice_squares g c
    (twoLayerBinaryPolynomial n f 0) (twoLayerBinaryPolynomial n f 1) D
    (twoLayerBinaryPolynomial b f' 0) (twoLayerBinaryPolynomial b f' 1)
    (hfactor 0) (hfactor 1) hc S T ?_ ?_ hT
  · intro p hp
    refine ⟨(hS p hp).1, (hS p hp).2.1, ?_, (hS p hp).2.2.2⟩
    have h := (hS p hp).2.2.1
    rw [twoLayerFormEval_eq_binaryPolynomial] at h
    have hy : ![p.2 0, p.2 1] = p.2 := by funext i; fin_cases i <;> rfl
    simpa only [hy] using h
  · intro p hp _
    exact hcomponents p.2 (hS p hp).2.1

end
end PellPaper
