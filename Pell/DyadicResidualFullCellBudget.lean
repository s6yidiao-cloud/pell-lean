import Pell.DyadicResidualFullCellSquareSieve

/-!
# Explicit uniform thresholds for the full-cell residual sieve budgets

The full-cell counting theorem asks for two logarithmic inequalities for every
possible residual degree.  This file replaces that family by one explicit real
threshold.  The threshold uses the proved ceiling-aware substitution-height
majorant and a finite supremum over the possible factor degrees, so it incurs
no extra factor in the sieve scale.
-/

namespace PellPaper

noncomputable section

/-- The ceiling-aware logarithmic coefficient-height majorant after a binary
linear substitution. -/
def fullCellSubstitutionHeightLogMajorant (d : ℕ) (H L : ℝ) : ℝ :=
  Real.log ((d : ℝ) + 1) + Real.log (H + 1) +
    (d : ℝ) * (Real.log 2 + Real.log (L + 1))

/-- A degree-uniform majorant for the squarefree certificate and the extra
degree-one coefficient-height cost.  It dominates every returned odd degree
`j ≤ d`. -/
def fullCellCertificateUniformLogMajorant (d : ℕ) (Klog : ℝ) : ℝ :=
  Real.log 2 + Klog + Real.log ((2 * d).factorial : ℝ) +
    (2 * d : ℕ) *
      (2 * Real.log (d : ℝ) + (d : ℝ) * Real.log 2 +
        Real.log ((d : ℝ) + 1) + Klog) +
    2 * ((d : ℝ) * Real.log 2 + Real.log ((d : ℝ) + 1) + Klog)

/-- A single real sieve-scale threshold for one possible residual degree.
Its two terms respectively enforce the value-height budget and the uniform
certificate budget. -/
def fullCellResidualSieveBudgetThreshold
    (i : ℕ × ℕ × ℕ × ℕ) (M b HF : ℕ) : ℝ :=
  let U : ℝ := ((2 ^ i.2.2.1 : ℕ) : ℝ)
  let V : ℝ := ((2 ^ i.2.2.2 : ℕ) : ℝ)
  let d : ℕ := 2 * b + 1
  let Hraw : ℝ := (12 * (b + 1) * HF ^ 2 : ℕ)
  let L : ℝ := 6 * (M : ℝ) * (U + V)
  let Klog := fullCellSubstitutionHeightLogMajorant d Hraw L
  let valueLog :=
    Real.log ((d : ℝ) + 1) + Klog +
      (d : ℝ) * Real.log (4 * (U + V))
  let certificateLog := fullCellCertificateUniformLogMajorant d Klog
  max
    (valueLog / (Real.log 2 / 16))
    (certificateLog / (Real.log 2 / 8))

/-- The endpoint threshold for all residual degrees `b ≤ n`.  Its validity
for the whole range follows from the monotonicity theorem below. -/
def fullCellResidualSieveUniformBudgetThreshold
    (i : ℕ × ℕ × ℕ × ℕ) (M n HF : ℕ) : ℝ :=
  fullCellResidualSieveBudgetThreshold i M n HF

private theorem fullCellSubstitutionHeightLogMajorant_mono
    {d D : ℕ} {H H' L : ℝ}
    (hdD : d ≤ D) (hHH' : H ≤ H') (hH : 0 ≤ H) (hL : 0 ≤ L) :
    fullCellSubstitutionHeightLogMajorant d H L ≤
      fullCellSubstitutionHeightLogMajorant D H' L := by
  have hdCast : (d : ℝ) ≤ D := by exact_mod_cast hdD
  have hdOne : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have hDOne : (d : ℝ) + 1 ≤ (D : ℝ) + 1 := by linarith
  have hlogd : Real.log ((d : ℝ) + 1) ≤ Real.log ((D : ℝ) + 1) :=
    Real.log_le_log hdOne hDOne
  have hHOne : 0 < H + 1 := by linarith
  have hHOneLe : H + 1 ≤ H' + 1 := by linarith
  have hlogH : Real.log (H + 1) ≤ Real.log (H' + 1) :=
    Real.log_le_log hHOne hHOneLe
  have hlogBase : 0 ≤ Real.log 2 + Real.log (L + 1) := by
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hlogL : 0 ≤ Real.log (L + 1) := Real.log_nonneg (by linarith)
    linarith
  have hdegreeTerm :
      (d : ℝ) * (Real.log 2 + Real.log (L + 1)) ≤
        (D : ℝ) * (Real.log 2 + Real.log (L + 1)) :=
    mul_le_mul_of_nonneg_right hdCast hlogBase
  rw [fullCellSubstitutionHeightLogMajorant,
    fullCellSubstitutionHeightLogMajorant]
  linarith

private theorem fullCellCertificateUniformLogMajorant_mono
    {d D : ℕ} {Klog Klog' : ℝ}
    (hd : 0 < d) (hdD : d ≤ D) (hKlog : 0 ≤ Klog)
    (hKK' : Klog ≤ Klog') :
    fullCellCertificateUniformLogMajorant d Klog ≤
      fullCellCertificateUniformLogMajorant D Klog' := by
  have hD : 0 < D := hd.trans_le hdD
  have hdreal : (0 : ℝ) < d := by exact_mod_cast hd
  have hdDreal : (d : ℝ) ≤ D := by exact_mod_cast hdD
  have hlogd : Real.log (d : ℝ) ≤ Real.log (D : ℝ) :=
    Real.log_le_log hdreal hdDreal
  have hfactorialNat : (2 * d).factorial ≤ (2 * D).factorial := by
    exact Nat.factorial_le (Nat.mul_le_mul_left 2 hdD)
  have hfactorial : Real.log ((2 * d).factorial : ℝ) ≤
      Real.log ((2 * D).factorial : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hfactorialNat
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlogdNonneg : 0 ≤ Real.log (d : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hd)
  have hlogdOneNonneg : 0 ≤ Real.log ((d : ℝ) + 1) :=
    Real.log_nonneg (by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le d))
  have hlogdOne : Real.log ((d : ℝ) + 1) ≤
      Real.log ((D : ℝ) + 1) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast Nat.succ_le_succ hdD
  let inner : ℝ :=
    2 * Real.log (d : ℝ) + (d : ℝ) * Real.log 2 +
      Real.log ((d : ℝ) + 1) + Klog
  let inner' : ℝ :=
    2 * Real.log (D : ℝ) + (D : ℝ) * Real.log 2 +
      Real.log ((D : ℝ) + 1) + Klog'
  have hinnerNonneg : 0 ≤ inner := by
    dsimp [inner]
    positivity
  have hdegreeLog : (d : ℝ) * Real.log 2 ≤ (D : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_right hdDreal hlog2
  have hinner : inner ≤ inner' := by
    dsimp [inner, inner']
    linarith
  have hcoeff : ((2 * d : ℕ) : ℝ) ≤ (2 * D : ℕ) := by
    exact_mod_cast Nat.mul_le_mul_left 2 hdD
  have hproduct : ((2 * d : ℕ) : ℝ) * inner ≤
      ((2 * D : ℕ) : ℝ) * inner' := by
    calc
      ((2 * d : ℕ) : ℝ) * inner ≤
          ((2 * D : ℕ) : ℝ) * inner :=
        mul_le_mul_of_nonneg_right hcoeff hinnerNonneg
      _ ≤ ((2 * D : ℕ) : ℝ) * inner' :=
        mul_le_mul_of_nonneg_left hinner (by positivity)
  have htail :
      (d : ℝ) * Real.log 2 + Real.log ((d : ℝ) + 1) + Klog ≤
        (D : ℝ) * Real.log 2 + Real.log ((D : ℝ) + 1) + Klog' := by
    linarith
  rw [fullCellCertificateUniformLogMajorant,
    fullCellCertificateUniformLogMajorant]
  change Real.log 2 + Klog + Real.log ((2 * d).factorial : ℝ) +
      ((2 * d : ℕ) : ℝ) * inner +
        2 * ((d : ℝ) * Real.log 2 + Real.log ((d : ℝ) + 1) + Klog) ≤
    Real.log 2 + Klog' + Real.log ((2 * D).factorial : ℝ) +
      ((2 * D : ℕ) : ℝ) * inner' +
        2 * ((D : ℝ) * Real.log 2 + Real.log ((D : ℝ) + 1) + Klog')
  linarith

/-- The explicit one-degree threshold is monotone in the possible residual
degree.  Thus the endpoint `b = n` controls every factor degree `b ≤ n`. -/
theorem fullCellResidualSieveBudgetThreshold_mono
    (i : ℕ × ℕ × ℕ × ℕ) (M HF : ℕ) {b n : ℕ}
    (hbn : b ≤ n) :
    fullCellResidualSieveBudgetThreshold i M b HF ≤
      fullCellResidualSieveBudgetThreshold i M n HF := by
  let U : ℝ := ((2 ^ i.2.2.1 : ℕ) : ℝ)
  let V : ℝ := ((2 ^ i.2.2.2 : ℕ) : ℝ)
  let d : ℕ := 2 * b + 1
  let D : ℕ := 2 * n + 1
  let HrawNat : ℕ := 12 * (b + 1) * HF ^ 2
  let HrawNat' : ℕ := 12 * (n + 1) * HF ^ 2
  let Hraw : ℝ := (HrawNat : ℝ)
  let Hraw' : ℝ := (HrawNat' : ℝ)
  let L : ℝ := 6 * (M : ℝ) * (U + V)
  let Klog := fullCellSubstitutionHeightLogMajorant d Hraw L
  let Klog' := fullCellSubstitutionHeightLogMajorant D Hraw' L
  let C : ℝ := 4 * (U + V)
  let valueLog := Real.log ((d : ℝ) + 1) + Klog +
    (d : ℝ) * Real.log C
  let valueLog' := Real.log ((D : ℝ) + 1) + Klog' +
    (D : ℝ) * Real.log C
  let certificateLog := fullCellCertificateUniformLogMajorant d Klog
  let certificateLog' := fullCellCertificateUniformLogMajorant D Klog'
  have hdD : d ≤ D := by dsimp [d, D]; omega
  have hd : 0 < d := by dsimp [d]; omega
  have hHrawNat : HrawNat ≤ HrawNat' := by
    dsimp [HrawNat, HrawNat']
    exact Nat.mul_le_mul_right (HF ^ 2)
      (Nat.mul_le_mul_left 12 (Nat.add_le_add_right hbn 1))
  have hHraw : Hraw ≤ Hraw' := by
    dsimp [Hraw, Hraw']
    exact_mod_cast hHrawNat
  have hHrawNonneg : 0 ≤ Hraw := by positivity
  have hLNonneg : 0 ≤ L := by positivity
  have hKlogLe : Klog ≤ Klog' := by
    exact fullCellSubstitutionHeightLogMajorant_mono hdD hHraw
      hHrawNonneg hLNonneg
  have hKlogNonneg : 0 ≤ Klog := by
    have hdOne : (1 : ℝ) ≤ (d : ℝ) + 1 := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le d)
    have hHOne : (1 : ℝ) ≤ Hraw + 1 := by linarith
    have hLOne : (1 : ℝ) ≤ L + 1 := by linarith
    dsimp [Klog, fullCellSubstitutionHeightLogMajorant]
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hlogd : 0 ≤ Real.log ((d : ℝ) + 1) := Real.log_nonneg hdOne
    have hlogH : 0 ≤ Real.log (Hraw + 1) := Real.log_nonneg hHOne
    have hlogL : 0 ≤ Real.log (L + 1) := Real.log_nonneg hLOne
    positivity
  have hCOne : (1 : ℝ) ≤ C := by
    have hU : (1 : ℝ) ≤ U := by
      dsimp [U]
      exact_mod_cast (one_le_pow₀ (by norm_num : 1 ≤ (2 : ℕ)))
    have hV : (1 : ℝ) ≤ V := by
      dsimp [V]
      exact_mod_cast (one_le_pow₀ (by norm_num : 1 ≤ (2 : ℕ)))
    dsimp [C]
    linarith
  have hlogC : 0 ≤ Real.log C := Real.log_nonneg hCOne
  have hdDreal : (d : ℝ) ≤ D := by exact_mod_cast hdD
  have hdegreeValue : (d : ℝ) * Real.log C ≤ (D : ℝ) * Real.log C :=
    mul_le_mul_of_nonneg_right hdDreal hlogC
  have hlogDegreeOne : Real.log ((d : ℝ) + 1) ≤
      Real.log ((D : ℝ) + 1) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast Nat.succ_le_succ hdD
  have hvalue : valueLog ≤ valueLog' := by
    dsimp [valueLog, valueLog']
    linarith
  have hcertificate : certificateLog ≤ certificateLog' := by
    exact fullCellCertificateUniformLogMajorant_mono hd hdD hKlogNonneg hKlogLe
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmax :
      max (valueLog / (Real.log 2 / 16))
          (certificateLog / (Real.log 2 / 8)) ≤
        max (valueLog' / (Real.log 2 / 16))
          (certificateLog' / (Real.log 2 / 8)) := by
    apply max_le_max
    · exact (div_le_div_iff_of_pos_right (by positivity)).mpr hvalue
    · exact (div_le_div_iff_of_pos_right (by positivity)).mpr hcertificate
  simpa only [fullCellResidualSieveBudgetThreshold, U, V, d, D,
    HrawNat, HrawNat', Hraw, Hraw', L, Klog, Klog', C,
    valueLog, valueLog', certificateLog, certificateLog'] using hmax

private theorem fullCell_actual_logs_le_majorants
    (d HK : ℕ) (H L C : ℝ)
    (hd : 0 < d) (hH : 0 ≤ H) (hL : 0 ≤ L) (hC : 1 ≤ C)
    (hHK : HK = binaryLinearSubstitutionNatHeight d H L) :
    let Klog := fullCellSubstitutionHeightLogMajorant d H L
    let HJ : ℕ := 2 ^ d * (d + 1) * HK
    let Wval : ℝ := ((d : ℝ) + 1) * (HK : ℝ) * C ^ d
    Real.log Wval ≤
        Real.log ((d : ℝ) + 1) + Klog + (d : ℝ) * Real.log C ∧
      ∀ j : ℕ, Odd j → 0 < j → j ≤ d →
        fullCellCertificateLogMajorant d HK j + 2 * Real.log (HJ : ℝ) ≤
          fullCellCertificateUniformLogMajorant d Klog := by
  dsimp only
  let Klog := fullCellSubstitutionHeightLogMajorant d H L
  let HJ : ℕ := 2 ^ d * (d + 1) * HK
  let Wval : ℝ := ((d : ℝ) + 1) * (HK : ℝ) * C ^ d
  have hHKpos : 0 < HK := by
    rw [hHK]
    exact binaryLinearSubstitutionNatHeight_pos d H L
  have hHKreal : (0 : ℝ) < HK := by exact_mod_cast hHKpos
  have hdreal : (0 : ℝ) < d := by exact_mod_cast hd
  have hdplus : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hlogHK : Real.log (HK : ℝ) ≤ Klog := by
    rw [hHK]
    exact log_binaryLinearSubstitutionNatHeight_le d hH hL
  have hlogHKnonneg : 0 ≤ Real.log (HK : ℝ) :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hHKpos.ne')
  have hvalueEq :
      Real.log Wval = Real.log ((d : ℝ) + 1) + Real.log (HK : ℝ) +
        (d : ℝ) * Real.log C := by
    dsimp [Wval]
    rw [Real.log_mul (mul_ne_zero hdplus.ne' hHKreal.ne')
        (pow_ne_zero _ hCpos.ne'),
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

/-- One explicit threshold inequality discharges both full-cell residual
sieve budgets, including the universal squarefree degree. -/
theorem fullCellResidualSieveBudgets_of_budgetThreshold_le
    (N : ℕ) (i : ℕ × ℕ × ℕ × ℕ) (M b HF : ℕ)
    (hthreshold : fullCellResidualSieveBudgetThreshold i M b HF ≤ (N : ℝ)) :
    fullCellResidualSieveBudgets N i M b HF := by
  let U : ℝ := ((2 ^ i.2.2.1 : ℕ) : ℝ)
  let V : ℝ := ((2 ^ i.2.2.2 : ℕ) : ℝ)
  let d : ℕ := 2 * b + 1
  let HrawNat : ℕ := 12 * (b + 1) * HF ^ 2
  let Hraw : ℝ := (HrawNat : ℝ)
  let L : ℝ := 6 * (M : ℝ) * (U + V)
  let HK : ℕ := binaryLinearSubstitutionNatHeight d Hraw L
  let Klog := fullCellSubstitutionHeightLogMajorant d Hraw L
  let HJ : ℕ := 2 ^ d * (d + 1) * HK
  let C : ℝ := 4 * (U + V)
  let Wval : ℝ := ((d : ℝ) + 1) * (HK : ℝ) * C ^ d
  let valueLog := Real.log ((d : ℝ) + 1) + Klog +
    (d : ℝ) * Real.log C
  let certificateLog := fullCellCertificateUniformLogMajorant d Klog
  have hd : 0 < d := by dsimp [d]; omega
  have hHraw : 0 ≤ Hraw := by positivity
  have hL : 0 ≤ L := by positivity
  have hC : 1 ≤ C := by
    have hU : (1 : ℝ) ≤ U := by
      dsimp [U]
      exact_mod_cast (one_le_pow₀ (by norm_num : 1 ≤ (2 : ℕ)))
    have hV : (1 : ℝ) ≤ V := by
      dsimp [V]
      exact_mod_cast (one_le_pow₀ (by norm_num : 1 ≤ (2 : ℕ)))
    dsimp [C]
    linarith
  have hactual := fullCell_actual_logs_le_majorants d HK Hraw L C
    hd hHraw hL hC rfl
  have hthreshold' :
      max (valueLog / (Real.log 2 / 16))
          (certificateLog / (Real.log 2 / 8)) ≤ (N : ℝ) := by
    simpa only [fullCellResidualSieveBudgetThreshold, U, V, d, HrawNat,
      Hraw, L, Klog, C, valueLog, certificateLog] using hthreshold
  have hvalueDiv : valueLog / (Real.log 2 / 16) ≤ (N : ℝ) :=
    (le_max_left _ _).trans hthreshold'
  have hcertificateDiv : certificateLog / (Real.log 2 / 8) ≤ (N : ℝ) :=
    (le_max_right _ _).trans hthreshold'
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hvalueBudget : valueLog ≤ (Real.log 2 / 16) * (N : ℝ) := by
    have h := (div_le_iff₀ (by positivity : 0 < Real.log 2 / 16)).mp hvalueDiv
    simpa only [mul_comm] using h
  have hcertificateBudget :
      certificateLog ≤ (Real.log 2 / 8) * (N : ℝ) := by
    have h := (div_le_iff₀ (by positivity : 0 < Real.log 2 / 8)).mp hcertificateDiv
    simpa only [mul_comm] using h
  rw [fullCellResidualSieveBudgets]
  have hactual' :
      Real.log Wval ≤ valueLog ∧
        ∀ j : ℕ, Odd j → 0 < j → j ≤ d →
          fullCellCertificateLogMajorant d HK j + 2 * Real.log (HJ : ℝ) ≤
            certificateLog := by
    simpa only [Klog, HJ, Wval, valueLog, certificateLog] using hactual
  refine ⟨?hvalue, ?hcertificate⟩
  · simpa only [U, V, d, HrawNat, Hraw, L, HK, C, Wval] using
      hactual'.1.trans hvalueBudget
  · intro j hj hjpos hjle
    simpa only [U, V, d, HrawNat, Hraw, L, HK, HJ] using
      (hactual'.2 j hj hjpos hjle).trans hcertificateBudget

/-- A single maximum-threshold inequality supplies the whole family of
budgets required by the source-tuple insertion theorem. -/
theorem fullCellResidualSieveBudgets_of_uniformBudgetThreshold_le
    (N : ℕ) (i : ℕ × ℕ × ℕ × ℕ) (M n HF : ℕ)
    (hthreshold : fullCellResidualSieveUniformBudgetThreshold i M n HF ≤
      (N : ℝ)) :
    ∀ b ≤ n, fullCellResidualSieveBudgets N i M b HF := by
  intro b hb
  have hsingle : fullCellResidualSieveBudgetThreshold i M b HF ≤
      fullCellResidualSieveUniformBudgetThreshold i M n HF := by
    exact fullCellResidualSieveBudgetThreshold_mono i M HF hb
  exact fullCellResidualSieveBudgets_of_budgetThreshold_le N i M b HF
    (hsingle.trans hthreshold)

end

end PellPaper
