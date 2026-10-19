import Pell.TwoLayerBinaryPolynomial

/-!
# Exact packing of homogeneous binary components into the two-layer model

The coefficient index records the exponent of the second target variable.
Packing the degree-b coefficients of two integral homogeneous binary forms
therefore reconstructs both forms, with their signs and heights unchanged.
This is the representation handoff for the source-linear factor in
the manuscript; it does not select or normalize that factor.
-/

namespace PellPaper

noncomputable section

/-- Pack the degree-b coefficients in the original source-coordinate order.
For arbitrary inputs this samples their degree-b part; exact reconstruction
below uses the explicit homogeneity hypotheses. -/
def homogeneousTwoLayerCoefficients (b : ℕ) (A B : MvPolynomial (Fin 2) ℤ) :
    twoLayerFormIndex b → ℤ := fun ab =>
  if ab.1 = 0 then
    A.coeff (Finsupp.single 0 (b - ab.2.val) + Finsupp.single 1 ab.2.val)
  else B.coeff (Finsupp.single 0 (b - ab.2.val) + Finsupp.single 1 ab.2.val)

/-- Both source slices retain their literal integral coefficients. -/
theorem homogeneousTwoLayerCoefficients_apply (b : ℕ)
    (A B : MvPolynomial (Fin 2) ℤ) (k : Fin (b + 1)) :
    homogeneousTwoLayerCoefficients b A B (0, k) =
      A.coeff (Finsupp.single 0 (b - k.val) + Finsupp.single 1 k.val) ∧
    homogeneousTwoLayerCoefficients b A B (1, k) =
      B.coeff (Finsupp.single 0 (b - k.val) + Finsupp.single 1 k.val) := by
  simp [homogeneousTwoLayerCoefficients]

private theorem binary_slice_eq_of_coefficients (b : ℕ)
    (f : twoLayerFormIndex b → ℤ) (a : Fin 2) (P : MvPolynomial (Fin 2) ℤ)
    (hP : P.IsHomogeneous b)
    (hf : ∀ k : Fin (b + 1), f (a, k) =
      P.coeff (Finsupp.single 0 (b - k.val) + Finsupp.single 1 k.val)) :
    twoLayerBinaryPolynomial b f a = P := by
  ext e
  by_cases he : e.degree = b
  · have hsum : e 0 + e 1 = b := by
      simpa only [Finsupp.degree_eq_sum, Fin.sum_univ_two] using he
    let k : Fin (b + 1) := ⟨e 1, by omega⟩
    have hexp : Finsupp.single 0 (b - k.val) + Finsupp.single 1 k.val = e := by
      ext i
      fin_cases i <;> simp [k]
      omega
    rw [← hexp, coeff_twoLayerBinaryPolynomial]
    exact hf k
  · rw [(twoLayerBinaryPolynomial_isHomogeneous b f a).coeff_eq_zero he,
      hP.coeff_eq_zero he]

/-- Exact reconstruction of both homogeneous components, including degree
zero and either or both zero components. -/
theorem twoLayerBinaryPolynomial_homogeneousTwoLayerCoefficients
    (b : ℕ) (A B : MvPolynomial (Fin 2) ℤ)
    (hA : A.IsHomogeneous b) (hB : B.IsHomogeneous b) :
    twoLayerBinaryPolynomial b (homogeneousTwoLayerCoefficients b A B) 0 = A ∧
      twoLayerBinaryPolynomial b (homogeneousTwoLayerCoefficients b A B) 1 = B := by
  constructor
  · exact binary_slice_eq_of_coefficients b _ 0 A hA
      (fun k => (homogeneousTwoLayerCoefficients_apply b A B k).1)
  · exact binary_slice_eq_of_coefficients b _ 1 B hB
      (fun k => (homogeneousTwoLayerCoefficients_apply b A B k).2)

/-- Evaluation is the original source-linear combination with no scalar,
coordinate permutation, or primitive-point restriction. -/
theorem twoLayerFormEval_homogeneousTwoLayerCoefficients
    (b : ℕ) (A B : MvPolynomial (Fin 2) ℤ)
    (hA : A.IsHomogeneous b) (hB : B.IsHomogeneous b) (lambda y : ℤ × ℤ) :
    twoLayerFormEval b (homogeneousTwoLayerCoefficients b A B) (lambda, y) =
      lambda.1 * MvPolynomial.eval ![y.1, y.2] A +
        lambda.2 * MvPolynomial.eval ![y.1, y.2] B := by
  obtain ⟨ha, hb⟩ := twoLayerBinaryPolynomial_homogeneousTwoLayerCoefficients b A B hA hB
  rw [twoLayerFormEval_eq_binaryPolynomial, ha, hb]

/-- The packed vector is nonzero precisely when at least one original
homogeneous component is nonzero. No eliminant nonvanishing is asserted. -/
theorem homogeneousTwoLayerCoefficients_ne_zero_iff
    (b : ℕ) (A B : MvPolynomial (Fin 2) ℤ)
    (hA : A.IsHomogeneous b) (hB : B.IsHomogeneous b) :
    homogeneousTwoLayerCoefficients b A B ≠ 0 ↔ A ≠ 0 ∨ B ≠ 0 := by
  obtain ⟨ha, hb⟩ := twoLayerBinaryPolynomial_homogeneousTwoLayerCoefficients b A B hA hB
  constructor
  · intro hf
    simpa only [ha, hb] using
      twoLayerBinaryPolynomial_zero_ne_or_one_ne b (homogeneousTwoLayerCoefficients b A B) hf
  · rintro (hA0 | hB0) hf
    · apply hA0
      rw [← ha, hf]
      simp [twoLayerBinaryPolynomial]
    · apply hB0
      rw [← hb, hf]
      simp [twoLayerBinaryPolynomial]

/-- Sampling the actual coefficients preserves an integral height bound
without loss, even without a homogeneity hypothesis. -/
theorem abs_homogeneousTwoLayerCoefficients_le
    (b : ℕ) (A B : MvPolynomial (Fin 2) ℤ) (H : ℤ)
    (hA : ∀ e, |A.coeff e| ≤ H) (hB : ∀ e, |B.coeff e| ≤ H)
    (ab : twoLayerFormIndex b) :
    |homogeneousTwoLayerCoefficients b A B ab| ≤ H := by
  unfold homogeneousTwoLayerCoefficients
  split_ifs
  · exact hA _
  · exact hB _

/-- The same lossless coefficient bound with a real height budget, matching
the existing Hadamard and binary-factor height interfaces. -/
theorem abs_real_homogeneousTwoLayerCoefficients_le
    (b : ℕ) (A B : MvPolynomial (Fin 2) ℤ) (H : ℝ)
    (hA : ∀ e, |((A.coeff e : ℤ) : ℝ)| ≤ H)
    (hB : ∀ e, |((B.coeff e : ℤ) : ℝ)| ≤ H) (ab : twoLayerFormIndex b) :
    |((homogeneousTwoLayerCoefficients b A B ab : ℤ) : ℝ)| ≤ H := by
  unfold homogeneousTwoLayerCoefficients
  split_ifs
  · exact hA _
  · exact hB _

/-- Packing the components of an existing coefficient vector recovers that
same vector exactly, not merely an associated or normalized vector. -/
theorem homogeneousTwoLayerCoefficients_twoLayerBinaryPolynomial
    (b : ℕ) (f : twoLayerFormIndex b → ℤ) :
    homogeneousTwoLayerCoefficients b
      (twoLayerBinaryPolynomial b f 0) (twoLayerBinaryPolynomial b f 1) = f := by
  funext ab
  obtain ⟨a, k⟩ := ab
  fin_cases a
  · exact (homogeneousTwoLayerCoefficients_apply b _ _ k).1.trans
      (coeff_twoLayerBinaryPolynomial b f 0 k)
  · exact (homogeneousTwoLayerCoefficients_apply b _ _ k).2.trans
      (coeff_twoLayerBinaryPolynomial b f 1 k)

end
end PellPaper
