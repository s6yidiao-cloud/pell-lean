import Pell.DyadicResidualFullCellBudget

/-!
# Actual logarithmic majorants for the full-cell square sieve

This frozen candidate isolates the elementary logarithmic bridge used by the
full-cell odd-degree square sieve.  A positive integral coefficient height
whose logarithm is bounded by `Klog` controls both the value-height expression
and every odd-degree squarefree-certificate expression.

No polynomial, target set, lattice geometry, or character-sum estimate occurs
in this statement.
-/

namespace PellPaper

noncomputable section

/-- A positive coefficient height with logarithm at most `Klog` controls the
literal value-height and all odd-degree certificate-height expressions used by
`eventually_fullCell_oddHomogeneousPolynomial_filter_le`.

The oddness hypothesis is retained in the conclusion because it is part of
the square-sieve interface, although this numerical majorization only uses
`0 < j` and `j ≤ d`. -/
theorem fullCell_actual_logs_le_of_log_coefficientHeight_le
    (d HK : ℕ) (C Klog : ℝ)
    (hd : 0 < d) (hHKpos : 0 < HK) (hC : 0 < C)
    (hlogHK : Real.log (HK : ℝ) ≤ Klog) :
    let HJ : ℕ := 2 ^ d * (d + 1) * HK
    let Wval : ℝ := ((d : ℝ) + 1) * (HK : ℝ) * C ^ d
    Real.log Wval ≤
        Real.log ((d : ℝ) + 1) + Klog + (d : ℝ) * Real.log C ∧
      ∀ j : ℕ, Odd j → 0 < j → j ≤ d →
        fullCellCertificateLogMajorant d HK j + 2 * Real.log (HJ : ℝ) ≤
          fullCellCertificateUniformLogMajorant d Klog := by
  dsimp only
  let HJ : ℕ := 2 ^ d * (d + 1) * HK
  let Wval : ℝ := ((d : ℝ) + 1) * (HK : ℝ) * C ^ d
  have hHKreal : (0 : ℝ) < HK := by exact_mod_cast hHKpos
  have hdreal : (0 : ℝ) < d := by exact_mod_cast hd
  have hdplus : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have hlogHKnonneg : 0 ≤ Real.log (HK : ℝ) :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hHKpos.ne')
  have hvalueEq :
      Real.log Wval = Real.log ((d : ℝ) + 1) + Real.log (HK : ℝ) +
        (d : ℝ) * Real.log C := by
    dsimp [Wval]
    rw [Real.log_mul (mul_ne_zero hdplus.ne' hHKreal.ne')
        (pow_ne_zero _ hC.ne'),
      Real.log_mul hdplus.ne' hHKreal.ne', Real.log_pow]
  have hvalue :
      Real.log Wval ≤ Real.log ((d : ℝ) + 1) + Klog +
        (d : ℝ) * Real.log C := by
    rw [hvalueEq]
    linarith
  refine ⟨hvalue, ?_⟩
  intro j _hjOdd hjpos hjle
  have hjreal : (0 : ℝ) < j := by exact_mod_cast hjpos
  have hjdreal : (j : ℝ) ≤ d := by exact_mod_cast hjle
  have hlogj : Real.log (j : ℝ) ≤ Real.log (d : ℝ) :=
    Real.log_le_log hjreal hjdreal
  have hfactorialNat : (2 * (j - 1)).factorial ≤ (2 * d).factorial := by
    apply Nat.factorial_le
    omega
  have hfactorial :
      Real.log ((2 * (j - 1)).factorial : ℝ) ≤
        Real.log ((2 * d).factorial : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hfactorialNat
  let innerJ : ℝ :=
    2 * Real.log (j : ℝ) + (d : ℝ) * Real.log 2 +
      Real.log ((d : ℝ) + 1) + Real.log (HK : ℝ)
  let innerD : ℝ :=
    2 * Real.log (d : ℝ) + (d : ℝ) * Real.log 2 +
      Real.log ((d : ℝ) + 1) + Klog
  have hinnerJ : 0 ≤ innerJ := by
    dsimp [innerJ]
    have hjone : (1 : ℝ) ≤ j := by exact_mod_cast hjpos
    have hdplusone : (1 : ℝ) ≤ (d : ℝ) + 1 := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le d)
    have hlogjnonneg : 0 ≤ Real.log (j : ℝ) := Real.log_nonneg hjone
    have hlog2nonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hlogdplusnonneg : 0 ≤ Real.log ((d : ℝ) + 1) :=
      Real.log_nonneg hdplusone
    positivity
  have hinner : innerJ ≤ innerD := by
    dsimp [innerJ, innerD]
    linarith
  have hcoeff : ((2 * (j - 1) : ℕ) : ℝ) ≤ (2 * d : ℕ) := by
    exact_mod_cast (show 2 * (j - 1) ≤ 2 * d by omega)
  have hproduct :
      ((2 * (j - 1) : ℕ) : ℝ) * innerJ ≤
        ((2 * d : ℕ) : ℝ) * innerD := by
    calc
      ((2 * (j - 1) : ℕ) : ℝ) * innerJ ≤
          ((2 * d : ℕ) : ℝ) * innerJ :=
        mul_le_mul_of_nonneg_right hcoeff hinnerJ
      _ ≤ ((2 * d : ℕ) : ℝ) * innerD :=
        mul_le_mul_of_nonneg_left hinner (by positivity)
  have hlogHJ :
      Real.log (HJ : ℝ) =
        (d : ℝ) * Real.log 2 + Real.log ((d : ℝ) + 1) +
          Real.log (HK : ℝ) := by
    dsimp [HJ]
    push_cast
    rw [Real.log_mul (mul_ne_zero (pow_ne_zero _ (by norm_num)) hdplus.ne')
        hHKreal.ne',
      Real.log_mul (pow_ne_zero _ (by norm_num)) hdplus.ne', Real.log_pow]
  rw [fullCellCertificateLogMajorant,
    fullCellCertificateUniformLogMajorant, hlogHJ]
  change Real.log 2 + Real.log (HK : ℝ) +
      Real.log ((2 * (j - 1)).factorial : ℝ) +
        ((2 * (j - 1) : ℕ) : ℝ) * innerJ +
          2 * ((d : ℝ) * Real.log 2 + Real.log ((d : ℝ) + 1) +
            Real.log (HK : ℝ)) ≤
    Real.log 2 + Klog + Real.log ((2 * d).factorial : ℝ) +
        ((2 * d : ℕ) : ℝ) * innerD +
          2 * ((d : ℝ) * Real.log 2 + Real.log ((d : ℝ) + 1) + Klog)
  linarith

end

end PellPaper
