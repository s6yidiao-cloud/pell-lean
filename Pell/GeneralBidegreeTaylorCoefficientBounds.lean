import Pell.GeneralBidegreeFiniteTaylorSelection
import Pell.RowWeightedDeterminantBound

/-!
# Entrywise bounds for sheared Taylor coefficients

The determinant argument in `L:sheared` assigns the Taylor term
`alpha^i beta^j / (i! j!)` the logarithmic weight coming from powers of the
two small local parameters.  This module records the elementary finite
coefficient bound: factorial denominators can only improve the bound supplied
by absolute bounds for `alpha` and `beta`.  It also packages the corresponding
ordered Cauchy--Binet upper bound for a finite Taylor truncation; the
unproved part of the manuscript's determinant argument is thereby isolated to
estimating the coefficient-evaluation minors and the resulting weighted
injection sum.
-/

namespace PellPaper

/-- A literal Taylor coefficient is bounded by the corresponding powers of
any nonnegative absolute bounds for its two local parameters. -/
theorem abs_generalBidegreeTaylorCoefficient_le_of_abs_le
    (A B : ℕ) (α β : generalBidegreeGrid A B → ℝ)
    (m : generalBidegreeCoefficientMonomialIndex)
    (r : generalBidegreeGrid A B) (a b : ℝ)
    (ha : 0 ≤ a)
    (hα : |α r| ≤ a) (hβ : |β r| ≤ b) :
    |generalBidegreeTaylorCoefficient A B α β m r| ≤
      a ^ (m 0) * b ^ (m 1) := by
  have hfac0 : 1 ≤ (Nat.factorial (m 0) : ℝ) := by
    exact_mod_cast Nat.one_le_of_lt (Nat.factorial_pos (m 0))
  have hfac1 : 1 ≤ (Nat.factorial (m 1) : ℝ) := by
    exact_mod_cast Nat.one_le_of_lt (Nat.factorial_pos (m 1))
  have hfac0pos : 0 < (Nat.factorial (m 0) : ℝ) := by positivity
  have hfac1pos : 0 < (Nat.factorial (m 1) : ℝ) := by positivity
  have hpowα : |α r| ^ (m 0) ≤ a ^ (m 0) :=
    pow_le_pow_left₀ (abs_nonneg _) hα _
  have hpowβ : |β r| ^ (m 1) ≤ b ^ (m 1) :=
    pow_le_pow_left₀ (abs_nonneg _) hβ _
  rw [generalBidegreeTaylorCoefficient, abs_div, abs_div, abs_mul,
    abs_pow, abs_pow, abs_of_pos hfac0pos, abs_of_pos hfac1pos]
  calc
    (|α r| ^ (m 0) * |β r| ^ (m 1) / (Nat.factorial (m 0) : ℝ)) /
        (Nat.factorial (m 1) : ℝ) ≤
      |α r| ^ (m 0) * |β r| ^ (m 1) := by
        have hprod : 0 ≤ |α r| ^ (m 0) * |β r| ^ (m 1) :=
          mul_nonneg (pow_nonneg (abs_nonneg _) _) (pow_nonneg (abs_nonneg _) _)
        rw [div_div]
        apply (div_le_iff₀ (mul_pos hfac0pos hfac1pos)).mpr
        nlinarith [mul_le_mul_of_nonneg_left hfac0 hprod,
          mul_le_mul_of_nonneg_left hfac1 hprod]
    _ ≤ a ^ (m 0) * b ^ (m 1) := by
      exact mul_le_mul hpowα hpowβ
        (pow_nonneg (abs_nonneg _) _) (pow_nonneg ha _)

/-- The local-scale form used in the sheared determinant argument: bounds
`|alpha| ≤ M⁻¹` and `|beta| ≤ x⁻¹` give the expected inverse-power Taylor
coefficient bound. -/
theorem abs_generalBidegreeTaylorCoefficient_le_inv_pows
    (A B : ℕ) (α β : generalBidegreeGrid A B → ℝ)
    (m : generalBidegreeCoefficientMonomialIndex)
    (r : generalBidegreeGrid A B) (M x : ℝ)
    (hM : 0 < M)
    (hα : |α r| ≤ M⁻¹) (hβ : |β r| ≤ x⁻¹) :
    |generalBidegreeTaylorCoefficient A B α β m r| ≤
      (M⁻¹) ^ (m 0) * (x⁻¹) ^ (m 1) := by
  apply abs_generalBidegreeTaylorCoefficient_le_of_abs_le
    A B α β m r M⁻¹ x⁻¹ (inv_nonneg.mpr hM.le) hα hβ

/-- A finite square Taylor coefficient determinant retains the product of
the individual inverse-power scales of its selected exponent rows.  The
factorial in front is the finite Leibniz constant, independent of the local
parameters. -/
theorem abs_det_generalBidegreeFiniteTaylorCoefficientMatrix_le_factorial_mul_prod_invPows
    (A B : ℕ) (α β : generalBidegreeGrid A B → ℝ)
    (s : generalBidegreeGrid A B → generalBidegreeCoefficientMonomialIndex)
    (M x : ℝ) (hM : 0 < M)
    (hα : ∀ r, |α r| ≤ M⁻¹) (hβ : ∀ r, |β r| ≤ x⁻¹) :
    |(generalBidegreeFiniteTaylorCoefficientMatrix A B α β s).det| ≤
      (Nat.factorial (Fintype.card (generalBidegreeGrid A B)) : ℝ) *
        ∏ q, (M⁻¹) ^ (s q 0) * (x⁻¹) ^ (s q 1) := by
  apply abs_det_le_factorial_mul_prod_rowBounds
    (generalBidegreeFiniteTaylorCoefficientMatrix A B α β s)
    (fun q => (M⁻¹) ^ (s q 0) * (x⁻¹) ^ (s q 1))
  intro q r
  exact abs_generalBidegreeTaylorCoefficient_le_inv_pows
    A B α β (s q) r M x hM (hα r) (hβ r)

/-- The product of the rowwise exponential Taylor scales is exactly the
exponential of the negative total logarithmic weight of the selected
exponent pairs. -/
theorem prod_exp_neg_pows_eq_exp_neg_sum_generalBidegreeRealWeight
    {ι : Type*} [Fintype ι]
    (s : ι → generalBidegreeCoefficientMonomialIndex)
    (ellM ellX : ℝ) :
    (∏ q, (Real.exp (-ellM)) ^ (s q 0) *
      (Real.exp (-ellX)) ^ (s q 1)) =
      Real.exp (- ∑ q, generalBidegreeRealWeight ellM ellX (s q)) := by
  calc
    (∏ q, (Real.exp (-ellM)) ^ (s q 0) *
      (Real.exp (-ellX)) ^ (s q 1)) =
        ∏ q, Real.exp (-generalBidegreeRealWeight ellM ellX (s q)) := by
      apply Finset.prod_congr rfl
      intro q _
      rw [← Real.exp_nat_mul (-ellM) (s q 0),
        ← Real.exp_nat_mul (-ellX) (s q 1), ← Real.exp_add]
      congr 1
      simp only [generalBidegreeRealWeight]
      ring
    _ = Real.exp (∑ q, -generalBidegreeRealWeight ellM ellX (s q)) := by
      rw [Real.exp_sum]
    _ = Real.exp (- ∑ q, generalBidegreeRealWeight ellM ellX (s q)) := by
      rw [Finset.sum_neg_distrib]

/-- With local scales `exp (-ellM)` and `exp (-ellX)`, the finite Taylor
coefficient determinant is bounded by its finite Leibniz constant times the
exponential of the negative selected total logarithmic weight. -/
theorem abs_det_generalBidegreeFiniteTaylorCoefficientMatrix_le_factorial_mul_exp_neg_totalWeight
    (A B : ℕ) (α β : generalBidegreeGrid A B → ℝ)
    (s : generalBidegreeGrid A B → generalBidegreeCoefficientMonomialIndex)
    (ellM ellX : ℝ)
    (hα : ∀ r, |α r| ≤ Real.exp (-ellM))
    (hβ : ∀ r, |β r| ≤ Real.exp (-ellX)) :
    |(generalBidegreeFiniteTaylorCoefficientMatrix A B α β s).det| ≤
      (Nat.factorial (Fintype.card (generalBidegreeGrid A B)) : ℝ) *
        Real.exp (- ∑ q, generalBidegreeRealWeight ellM ellX (s q)) := by
  calc
    |(generalBidegreeFiniteTaylorCoefficientMatrix A B α β s).det| ≤
        (Nat.factorial (Fintype.card (generalBidegreeGrid A B)) : ℝ) *
          ∏ q, ((Real.exp ellM)⁻¹) ^ (s q 0) *
            ((Real.exp ellX)⁻¹) ^ (s q 1) := by
      apply abs_det_generalBidegreeFiniteTaylorCoefficientMatrix_le_factorial_mul_prod_invPows
        A B α β s (Real.exp ellM) (Real.exp ellX) (Real.exp_pos _)
      · intro r
        simpa only [Real.exp_neg] using hα r
      · intro r
        simpa only [Real.exp_neg] using hβ r
    _ = (Nat.factorial (Fintype.card (generalBidegreeGrid A B)) : ℝ) *
        Real.exp (- ∑ q, generalBidegreeRealWeight ellM ellX (s q)) := by
      rw [← Real.exp_neg ellM, ← Real.exp_neg ellX,
        prod_exp_neg_pows_eq_exp_neg_sum_generalBidegreeRealWeight]

/-- A single Taylor coefficient has the exponential decay prescribed by its
two-coordinate logarithmic weight. -/
theorem abs_generalBidegreeTaylorCoefficient_le_exp_neg_realWeight
    (A B : ℕ) (α β : generalBidegreeGrid A B → ℝ)
    (m : generalBidegreeCoefficientMonomialIndex)
    (r : generalBidegreeGrid A B) (ellM ellX : ℝ)
    (hα : |α r| ≤ Real.exp (-ellM))
    (hβ : |β r| ≤ Real.exp (-ellX)) :
    |generalBidegreeTaylorCoefficient A B α β m r| ≤
      Real.exp (-generalBidegreeRealWeight ellM ellX m) := by
  calc
    |generalBidegreeTaylorCoefficient A B α β m r| ≤
        (Real.exp (-ellM)) ^ (m 0) * (Real.exp (-ellX)) ^ (m 1) :=
      abs_generalBidegreeTaylorCoefficient_le_of_abs_le A B α β m r
        (Real.exp (-ellM)) (Real.exp (-ellX)) (Real.exp_pos _).le hα hβ
    _ = Real.exp (-generalBidegreeRealWeight ellM ellX m) := by
      rw [← Real.exp_nat_mul (-ellM) (m 0),
        ← Real.exp_nat_mul (-ellX) (m 1), ← Real.exp_add]
      congr 1
      simp only [generalBidegreeRealWeight]
      ring

/-- A finite product of exponential row scales is the exponential of the
negative total weight. -/
theorem prod_exp_neg_eq_exp_neg_sum
    {ι : Type*} [Fintype ι] (weight : ι → ℝ) :
    (∏ i, Real.exp (-weight i)) = Real.exp (- ∑ i, weight i) := by
  rw [← Real.exp_sum, Finset.sum_neg_distrib]

/-- Ordered Cauchy--Binet determinant bound with rowwise exponential decay.
The coefficient-evaluation minor may have an arbitrary nonnegative majorant
`H`; the Taylor factor contributes precisely the negative total selected
weight. -/
theorem abs_det_mul_le_sum_exp_neg_selectedWeight
    {n m : Type*} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m]
    (U : Matrix n m ℝ) (V : Matrix m n ℝ)
    (H : {p : n → m // Function.Injective p} → ℝ) (weight : m → ℝ)
    (hU : ∀ p, |(U.submatrix id p.1).det| ≤ H p)
    (hV : ∀ q i, |V q i| ≤ Real.exp (-weight q)) :
    |(U * V).det| ≤
      ∑ p : {p : n → m // Function.Injective p},
        H p * Real.exp (- ∑ i, weight (p.1 i)) := by
  rw [det_mul_rectangular_eq_sum_injective]
  calc
    |∑ p : {p : n → m // Function.Injective p},
        (U.submatrix id p.1).det * ∏ i, V (p.1 i) i| ≤
        ∑ p : {p : n → m // Function.Injective p},
          |(U.submatrix id p.1).det * ∏ i, V (p.1 i) i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ p : {p : n → m // Function.Injective p},
        |(U.submatrix id p.1).det| * ∏ i, |V (p.1 i) i| := by
      apply Finset.sum_congr rfl
      intro p _
      rw [abs_mul, Finset.abs_prod]
    _ ≤ ∑ p : {p : n → m // Function.Injective p},
        H p * ∏ i, Real.exp (-weight (p.1 i)) := by
      apply Finset.sum_le_sum
      intro p _
      have hH_nonneg : 0 ≤ H p := (abs_nonneg _).trans (hU p)
      have hprod_nonneg : 0 ≤ ∏ i, |V (p.1 i) i| :=
        Finset.prod_nonneg fun i _ => abs_nonneg _
      have hprod : (∏ i, |V (p.1 i) i|) ≤
          ∏ i, Real.exp (-weight (p.1 i)) := by
        apply Finset.prod_le_prod
        · intro i _
          exact abs_nonneg _
        intro i _
        exact hV (p.1 i) i
      exact mul_le_mul (hU p) hprod hprod_nonneg hH_nonneg
    _ = ∑ p : {p : n → m // Function.Injective p},
        H p * Real.exp (- ∑ i, weight (p.1 i)) := by
      apply Finset.sum_congr rfl
      intro p _
      rw [prod_exp_neg_eq_exp_neg_sum]

/-- Finite Taylor truncation bound in the exact sheared bidegree variables.
This turns local exponential control of the two Taylor parameters into an
ordered weighted Cauchy--Binet sum. -/
theorem abs_det_generalBidegreeFiniteTaylorEvaluationMatrix_le_sum_exp_neg_selectedWeight
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A B : ℕ) (α β : generalBidegreeGrid A B → ℝ)
    (s : κ → generalBidegreeCoefficientMonomialIndex)
    (H : {p : generalBidegreeGrid A B → κ // Function.Injective p} → ℝ)
    (ellM ellX : ℝ)
    (hH : ∀ p,
      |((generalBidegreeRectangularCoefficientMatrixReal A B s).submatrix id p.1).det|
        ≤ H p)
    (hα : ∀ r, |α r| ≤ Real.exp (-ellM))
    (hβ : ∀ r, |β r| ≤ Real.exp (-ellX)) :
    |(generalBidegreeFiniteTaylorEvaluationMatrix A B α β s).det| ≤
      ∑ p : {p : generalBidegreeGrid A B → κ // Function.Injective p},
        H p * Real.exp (- ∑ i,
          generalBidegreeRealWeight ellM ellX (s (p.1 i))) := by
  rw [generalBidegreeFiniteTaylorEvaluationMatrix_eq_transpose_mul,
    Matrix.det_transpose]
  apply abs_det_mul_le_sum_exp_neg_selectedWeight
    (generalBidegreeRectangularCoefficientMatrixReal A B s)
    (generalBidegreeFiniteTaylorCoefficientMatrix A B α β s)
    H (fun q => generalBidegreeRealWeight ellM ellX (s q)) hH
  intro q r
  exact abs_generalBidegreeTaylorCoefficient_le_exp_neg_realWeight
    A B α β (s q) r ellM ellX (hα r) (hβ r)

end PellPaper
