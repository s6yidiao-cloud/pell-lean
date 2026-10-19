import Pell.Main3LargeAnalyticIntrinsicEliminantSieveBudget

/-!
# Uniform logarithmic budget for the intrinsic main3 sieve threshold

The literal intrinsic eliminant threshold is cubic in `B + 1` once the
target-basis entry height and the rectangle value height have logarithmic
size `O(log Y)`.  This module performs only that elementary expansion.  It
does not invoke the sieve, a character sum, or the external Weil interface.
-/

namespace PellPaper

noncomputable section

private theorem log_two_mul_intrinsicDegree_factorial_le
    (B b : ℕ) (hb : b ≤ B) :
    Real.log ((2 * (2 * b + 1)).factorial : ℝ) ≤
      16 * ((B : ℝ) + 1) ^ 2 := by
  let n : ℕ := 2 * (2 * b + 1)
  let p : ℝ := (B : ℝ) + 1
  have hnpos : 0 < n := by
    dsimp [n]
    omega
  have hp : 1 ≤ p := by
    dsimp [p]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le B)
  have hbReal : (b : ℝ) ≤ B := by exact_mod_cast hb
  have hn : (n : ℝ) ≤ 4 * p := by
    dsimp [n, p]
    push_cast
    linarith
  have hfacNat : n.factorial ≤ n ^ n := Nat.factorial_le_pow n
  have hfacReal : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by
    exact_mod_cast hfacNat
  have hlogFacPow : Real.log (n.factorial : ℝ) ≤
      Real.log ((n : ℝ) ^ n) :=
    Real.log_le_log (by positivity) hfacReal
  have hlogn : Real.log (n : ℝ) ≤ (n : ℝ) :=
    Real.log_le_self (by positivity)
  have hlogFac : Real.log (n.factorial : ℝ) ≤ (n : ℝ) ^ 2 := by
    rw [Real.log_pow] at hlogFacPow
    have hn0 : (0 : ℝ) ≤ n := by positivity
    nlinarith
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hp0 : 0 ≤ p := zero_le_one.trans hp
  have hsquare : (n : ℝ) ^ 2 ≤ (4 * p) ^ 2 := by
    nlinarith
  change Real.log (n.factorial : ℝ) ≤ 16 * p ^ 2
  exact hlogFac.trans (hsquare.trans_eq (by ring))

/-- If the target-basis entries and the value rectangle have the displayed
logarithmic budgets, then the exact intrinsic eliminant sieve threshold is
uniformly cubic in `B + 1`.  The statement bounds the threshold itself; it
does not turn an eventual sieve estimate into a pointwise assertion. -/
theorem main3LargeAnalyticIntrinsicEliminantSieveBudgetThreshold_le_uniformLogBudget
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N B : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (data : Main3LargeAnalyticFixedKeyCellAuxiliaryFactorData
      htheta hY hi key cell B)
    (L U V : ℝ)
    (hlogL : Real.log (L + 1) ≤ 64 * Real.log (Y : ℝ))
    (hlogUV : Real.log (4 * (U + V)) ≤ 12 * Real.log (Y : ℝ)) :
    main3LargeAnalyticIntrinsicEliminantSieveBudgetThreshold data L U V ≤
      16000 * ((B : ℝ) + 1) ^ 3 * theta * Real.log (Y : ℝ) := by
  let p : ℝ := (B : ℝ) + 1
  let ell : ℝ := Real.log (Y : ℝ)
  let Q : ℝ := theta * ell
  let b : ℕ := data.residualDegree
  let d : ℕ := main3LargeAnalyticIntrinsicEliminantDegree data
  let factorLog : ℝ :=
    main3LargeAnalyticFixedKeyFactorLogMajorant theta Y B
  let rawLog : ℝ :=
    main3LargeAnalyticIntrinsicEliminantRawLogMajorant theta Y B
  let Klog : ℝ :=
    main3LargeAnalyticIntrinsicEliminantSubstitutionLogMajorant data L
  let valueLog : ℝ :=
    main3LargeAnalyticIntrinsicEliminantValueLogMajorant data L U V
  let certificateLog : ℝ :=
    main3LargeAnalyticIntrinsicEliminantCertificateLogMajorant data L
  have hp : 1 ≤ p := by
    dsimp [p]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le B)
  have hp0 : 0 ≤ p := zero_le_one.trans hp
  have hpPos : 0 < p := zero_lt_one.trans_le hp
  have hthetaOne : (1 : ℝ) ≤ theta := by linarith
  have htheta0 : 0 ≤ theta := zero_le_one.trans hthetaOne
  have hbase := one_add_log_two_le_log_of_65536_le hY
  have hlogTwo0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hellOne : 1 ≤ ell := by
    dsimp [ell]
    linarith
  have hell0 : 0 ≤ ell := zero_le_one.trans hellOne
  have hlogTwo : Real.log 2 ≤ ell := by
    dsimp [ell]
    linarith
  have hlogSix : Real.log 6 ≤ ell := by
    dsimp [ell]
    exact Real.log_le_log (by norm_num)
      (by exact_mod_cast (show 6 ≤ Y by omega))
  have hQone : 1 ≤ Q := by
    dsimp [Q]
    exact one_le_mul_of_one_le_of_one_le hthetaOne hellOne
  have hQthree : 3 ≤ Q := by
    dsimp [Q]
    calc
      (3 : ℝ) ≤ theta := htheta
      _ = theta * 1 := by ring
      _ ≤ theta * ell := mul_le_mul_of_nonneg_left hellOne htheta0
  have hQ0 : 0 ≤ Q := zero_le_one.trans hQone
  have hellQ : ell ≤ Q := by
    dsimp [Q]
    calc
      ell = 1 * ell := by ring
      _ ≤ theta * ell := mul_le_mul_of_nonneg_right hthetaOne hell0
  have hlogTwoQ : Real.log 2 ≤ Q := hlogTwo.trans hellQ
  have hlogSixQ : Real.log 6 ≤ Q := hlogSix.trans hellQ
  have hlogp : Real.log p ≤ p - 1 :=
    Real.log_le_sub_one_of_pos hpPos
  have hpSub0 : 0 ≤ p - 1 := sub_nonneg.mpr hp
  have hpSubQ : p - 1 ≤ (p - 1) * Q := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hQone hpSub0
  have hpQ : p ≤ p * Q := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hQone hp0
  have hpQ_le_sqQ : p * Q ≤ p ^ 2 * Q := by
    have := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hp hp0) hQ0
    simpa only [mul_one, pow_two, mul_assoc] using this
  have hpSqQ_le_cubeQ : p ^ 2 * Q ≤ p ^ 3 * Q := by
    have hpSq0 : 0 ≤ p ^ 2 := sq_nonneg p
    have hpSqCube : p ^ 2 ≤ p ^ 3 := by
      nlinarith [mul_nonneg hpSq0 hpSub0]
    exact mul_le_mul_of_nonneg_right hpSqCube hQ0
  have hlogTwoP : Real.log (2 * p) / 2 ≤ p := by
    have hlog := Real.log_le_self (show (0 : ℝ) ≤ 2 * p by positivity)
    nlinarith
  have hfactorLog : factorLog ≤ 14 * p ^ 2 * Q := by
    have hBnonneg : (0 : ℝ) ≤ B := by positivity
    have hBLog : (B : ℝ) * Real.log 2 ≤ (p - 1) * Q := by
      have hBEq : (B : ℝ) = p - 1 := by
        dsimp [p]
        ring
      rw [hBEq]
      exact mul_le_mul_of_nonneg_left hlogTwoQ hpSub0
    have hlogpQ : Real.log p ≤ (p - 1) * Q := hlogp.trans hpSubQ
    have hinside :
        Real.log (2 * p) / 2 + (6 + 2 * (B : ℝ)) * Q ≤
          (3 * p + 4) * Q := by
      have hlogPart : Real.log (2 * p) / 2 ≤ p * Q :=
        hlogTwoP.trans hpQ
      dsimp [p] at hlogPart ⊢
      nlinarith
    have hmul :
        2 * p * (Real.log (2 * p) / 2 +
            (6 + 2 * (B : ℝ)) * Q) ≤
          2 * p * ((3 * p + 4) * Q) :=
      mul_le_mul_of_nonneg_left hinside (by positivity)
    have hcoef :
        2 * (p - 1) + 2 * p * (3 * p + 4) ≤ 14 * p ^ 2 := by
      have hprod : 0 ≤ (p - 1) * (4 * p - 1) :=
        mul_nonneg hpSub0 (by linarith)
      nlinarith only [hprod]
    have hcombined :
        (B : ℝ) * Real.log 2 + Real.log p +
            2 * p * (Real.log (2 * p) / 2 +
              (6 + 2 * (B : ℝ)) * Q) ≤
          (2 * (p - 1) + 2 * p * (3 * p + 4)) * Q := by
      linarith
    have hfinal := hcombined.trans
      (mul_le_mul_of_nonneg_right hcoef hQ0)
    dsimp [factorLog]
    rw [main3LargeAnalyticFixedKeyFactorLogMajorant]
    push_cast
    simpa only [p, Q, ell, mul_assoc] using hfinal
  have hrawLog : rawLog ≤ 38 * p ^ 2 * Q := by
    have hlogpQ : Real.log p ≤ (p - 1) * Q := hlogp.trans hpSubQ
    have hpre :
        3 * Real.log 2 + Real.log 6 + Real.log p +
            2 * factorLog + 6 * ell ≤
          (28 * p ^ 2 + p + 9) * Q := by
      linarith
    have hcoef : 28 * p ^ 2 + p + 9 ≤ 38 * p ^ 2 := by
      have hprod : 0 ≤ (p - 1) * (10 * p + 9) :=
        mul_nonneg hpSub0 (by positivity)
      nlinarith only [hprod]
    have hfinal := hpre.trans (mul_le_mul_of_nonneg_right hcoef hQ0)
    dsimp [rawLog]
    rw [main3LargeAnalyticIntrinsicEliminantRawLogMajorant]
    simpa only [p, ell, Q, factorLog] using hfinal
  have hb : b ≤ B := by
    dsimp [b]
    have hsplit := data.degree_split
    omega
  have hdFormula : d = 2 * b + 1 := by
    rfl
  have hdPosNat : 0 < d := by
    rw [hdFormula]
    omega
  have hdBoundNat : d ≤ 2 * B + 1 := by
    rw [hdFormula]
    omega
  have hdBound : (d : ℝ) ≤ 2 * p - 1 := by
    have hdCast : (d : ℝ) ≤ (2 * B + 1 : ℕ) := by exact_mod_cast hdBoundNat
    dsimp [p]
    push_cast at hdCast ⊢
    linarith
  have htwoDBound : ((2 * d : ℕ) : ℝ) ≤ 4 * p := by
    push_cast
    nlinarith
  have hdReal0 : (0 : ℝ) ≤ d := by positivity
  have hdRealPos : (0 : ℝ) < d := by exact_mod_cast hdPosNat
  have hdOneBound : (d : ℝ) + 1 ≤ 2 * p := by linarith
  have hlogd : Real.log (d : ℝ) ≤ p * Q := by
    have hlog := Real.log_le_self hdReal0
    exact hlog.trans (hdBound.trans (by nlinarith [hpQ]))
  have hlogdOne : Real.log ((d : ℝ) + 1) ≤ p * Q := by
    have hlog := Real.log_le_self (show (0 : ℝ) ≤ (d : ℝ) + 1 by positivity)
    exact hlog.trans (hdOneBound.trans (by nlinarith [hpQ]))
  have hlogLQ : Real.log (L + 1) ≤ 64 * Q := by
    calc
      Real.log (L + 1) ≤ 64 * ell := by simpa only [ell] using hlogL
      _ ≤ 64 * Q := mul_le_mul_of_nonneg_left hellQ (by norm_num)
  have hdegreeSubstitution :
      (d : ℝ) * (Real.log 2 + Real.log (L + 1)) ≤
        (2 * p - 1) * (65 * Q) := by
    have hsum : Real.log 2 + Real.log (L + 1) ≤ 65 * Q := by
      linarith
    calc
      (d : ℝ) * (Real.log 2 + Real.log (L + 1)) ≤
          (d : ℝ) * (65 * Q) :=
        mul_le_mul_of_nonneg_left hsum hdReal0
      _ ≤ (2 * p - 1) * (65 * Q) :=
        mul_le_mul_of_nonneg_right hdBound (by positivity)
  have hKlog : Klog ≤ 104 * p ^ 2 * Q := by
    have hpre :
        Real.log ((d : ℝ) + 1) + rawLog +
            (d : ℝ) * (Real.log 2 + Real.log (L + 1)) ≤
          (38 * p ^ 2 + 131 * p - 65) * Q := by
      calc
        _ ≤ p * Q + 38 * p ^ 2 * Q + (2 * p - 1) * (65 * Q) :=
          add_le_add (add_le_add hlogdOne hrawLog) hdegreeSubstitution
        _ = (38 * p ^ 2 + 131 * p - 65) * Q := by ring
    have hcoef : 38 * p ^ 2 + 131 * p - 65 ≤ 104 * p ^ 2 := by
      have hprod : 0 ≤ (p - 1) * (66 * p - 65) :=
        mul_nonneg hpSub0 (by linarith)
      nlinarith only [hprod]
    have hfinal := hpre.trans (mul_le_mul_of_nonneg_right hcoef hQ0)
    dsimp [Klog]
    rw [main3LargeAnalyticIntrinsicEliminantSubstitutionLogMajorant]
    simpa only [d, rawLog] using hfinal
  have hdegreeValue :
      (d : ℝ) * Real.log (4 * (U + V)) ≤
        (2 * p - 1) * (12 * Q) := by
    have hUVQ : Real.log (4 * (U + V)) ≤ 12 * Q := by
      calc
        Real.log (4 * (U + V)) ≤ 12 * ell := by
          simpa only [ell] using hlogUV
        _ ≤ 12 * Q := mul_le_mul_of_nonneg_left hellQ (by norm_num)
    calc
      (d : ℝ) * Real.log (4 * (U + V)) ≤ (d : ℝ) * (12 * Q) :=
        mul_le_mul_of_nonneg_left hUVQ hdReal0
      _ ≤ (2 * p - 1) * (12 * Q) :=
        mul_le_mul_of_nonneg_right hdBound (by positivity)
  have hvalueLog : valueLog ≤ 117 * p ^ 2 * Q := by
    have hpre :
        Real.log ((d : ℝ) + 1) + Klog +
            (d : ℝ) * Real.log (4 * (U + V)) ≤
          (104 * p ^ 2 + 25 * p - 12) * Q := by
      calc
        _ ≤ p * Q + 104 * p ^ 2 * Q + (2 * p - 1) * (12 * Q) :=
          add_le_add (add_le_add hlogdOne hKlog) hdegreeValue
        _ = (104 * p ^ 2 + 25 * p - 12) * Q := by ring
    have hcoef : 104 * p ^ 2 + 25 * p - 12 ≤ 117 * p ^ 2 := by
      have hprod : 0 ≤ (p - 1) * (13 * p - 12) :=
        mul_nonneg hpSub0 (by linarith)
      nlinarith only [hprod]
    have hfinal := hpre.trans (mul_le_mul_of_nonneg_right hcoef hQ0)
    dsimp [valueLog]
    rw [main3LargeAnalyticIntrinsicEliminantValueLogMajorant]
    simpa only [d, Klog] using hfinal
  have hfactorial :
      Real.log ((2 * d).factorial : ℝ) ≤ 16 * p ^ 2 := by
    have hfac := log_two_mul_intrinsicDegree_factorial_le B b hb
    simpa only [hdFormula, p] using hfac
  let inner : ℝ :=
    2 * Real.log (d : ℝ) + (d : ℝ) * Real.log 2 +
      Real.log ((d : ℝ) + 1) + Klog
  have hdLogTwo : (d : ℝ) * Real.log 2 ≤ (2 * p - 1) * Q := by
    calc
      (d : ℝ) * Real.log 2 ≤ (d : ℝ) * Q :=
        mul_le_mul_of_nonneg_left hlogTwoQ hdReal0
      _ ≤ (2 * p - 1) * Q :=
        mul_le_mul_of_nonneg_right hdBound hQ0
  have hinner : inner ≤ 108 * p ^ 2 * Q := by
    have hpre : inner ≤ (104 * p ^ 2 + 5 * p - 1) * Q := by
      dsimp [inner]
      calc
        _ ≤ 2 * (p * Q) + (2 * p - 1) * Q + p * Q +
            104 * p ^ 2 * Q := by linarith
        _ = (104 * p ^ 2 + 5 * p - 1) * Q := by ring
    have hcoef : 104 * p ^ 2 + 5 * p - 1 ≤ 108 * p ^ 2 := by
      have hprod : 0 ≤ (p - 1) * (4 * p - 1) :=
        mul_nonneg hpSub0 (by linarith)
      nlinarith only [hprod]
    exact hpre.trans (mul_le_mul_of_nonneg_right hcoef hQ0)
  have hproduct : ((2 * d : ℕ) : ℝ) * inner ≤ 432 * p ^ 3 * Q := by
    by_cases hinner0 : 0 ≤ inner
    · calc
        ((2 * d : ℕ) : ℝ) * inner ≤ (4 * p) * inner :=
          mul_le_mul_of_nonneg_right htwoDBound hinner0
        _ ≤ (4 * p) * (108 * p ^ 2 * Q) :=
          mul_le_mul_of_nonneg_left hinner (by positivity)
        _ = 432 * p ^ 3 * Q := by ring
    · have hnonpos : inner ≤ 0 := le_of_not_ge hinner0
      have hleft : ((2 * d : ℕ) : ℝ) * inner ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) hnonpos
      exact hleft.trans (by positivity)
  have htailInner :
      (d : ℝ) * Real.log 2 + Real.log ((d : ℝ) + 1) + Klog ≤
        106 * p ^ 2 * Q := by
    have hpre :
        (d : ℝ) * Real.log 2 + Real.log ((d : ℝ) + 1) + Klog ≤
          (104 * p ^ 2 + 3 * p - 1) * Q := by
      calc
        _ ≤ (2 * p - 1) * Q + p * Q + 104 * p ^ 2 * Q := by
          linarith
        _ = (104 * p ^ 2 + 3 * p - 1) * Q := by ring
    have hcoef : 104 * p ^ 2 + 3 * p - 1 ≤ 106 * p ^ 2 := by
      have hprod : 0 ≤ (p - 1) * (2 * p - 1) :=
        mul_nonneg hpSub0 (by linarith)
      nlinarith only [hprod]
    exact hpre.trans (mul_le_mul_of_nonneg_right hcoef hQ0)
  have hfactorialQ : 16 * p ^ 2 ≤ 16 * p ^ 3 * Q := by
    have hone : p ^ 2 ≤ p ^ 3 * Q := by
      calc
        p ^ 2 ≤ p ^ 2 * Q := by
          simpa only [mul_one] using
            mul_le_mul_of_nonneg_left hQone (sq_nonneg p)
        _ ≤ p ^ 3 * Q := hpSqQ_le_cubeQ
    have hscaled := mul_le_mul_of_nonneg_left hone
      (by norm_num : (0 : ℝ) ≤ 16)
    simpa only [mul_assoc] using hscaled
  have hcertificateLog : certificateLog ≤ 765 * p ^ 3 * Q := by
    have hlogTwoCube : Real.log 2 ≤ p ^ 3 * Q := by
      exact hlogTwoQ.trans (by
        calc
          Q = 1 * Q := by ring
          _ ≤ p ^ 3 * Q :=
            mul_le_mul_of_nonneg_right (one_le_pow₀ hp) hQ0)
    have hKscale : 104 * (p ^ 2 * Q) ≤ 104 * (p ^ 3 * Q) :=
      mul_le_mul_of_nonneg_left hpSqQ_le_cubeQ (by norm_num)
    have hKcube : Klog ≤ 104 * p ^ 3 * Q := by
      have hKlog' : Klog ≤ 104 * (p ^ 2 * Q) := by
        simpa only [mul_assoc] using hKlog
      exact hKlog'.trans (by simpa only [mul_assoc] using hKscale)
    have hfacCube : Real.log ((2 * d).factorial : ℝ) ≤
        16 * p ^ 3 * Q := hfactorial.trans hfactorialQ
    have htail :
        2 * ((d : ℝ) * Real.log 2 + Real.log ((d : ℝ) + 1) + Klog) ≤
          212 * p ^ 3 * Q := by
      calc
        _ ≤ 212 * p ^ 2 * Q := by linarith
        _ ≤ 212 * p ^ 3 * Q := by
          have hscaled := mul_le_mul_of_nonneg_left hpSqQ_le_cubeQ
            (by norm_num : (0 : ℝ) ≤ 212)
          simpa only [mul_assoc] using hscaled
    have hsum :
        Real.log 2 + Klog + Real.log ((2 * d).factorial : ℝ) +
            ((2 * d : ℕ) : ℝ) * inner +
              2 * ((d : ℝ) * Real.log 2 +
                Real.log ((d : ℝ) + 1) + Klog) ≤
          765 * p ^ 3 * Q := by
      linarith
    dsimp [certificateLog]
    rw [main3LargeAnalyticIntrinsicEliminantCertificateLogMajorant,
      fullCellCertificateUniformLogMajorant]
    simpa only [d, Klog, inner] using hsum
  have hlogTwoLower : (1 : ℝ) / 2 ≤ Real.log 2 := by
    exact (by norm_num : (1 : ℝ) / 2 ≤ 0.6931471803).trans
      Real.log_two_gt_d9.le
  have hden16 : 0 < Real.log 2 / 16 := by positivity
  have hden8 : 0 < Real.log 2 / 8 := by positivity
  let P : ℝ := p ^ 3 * Q
  have hP0 : 0 ≤ P := by dsimp [P]; positivity
  have hvalueP : valueLog ≤ 117 * P := by
    have hscale := mul_le_mul_of_nonneg_left hpSqQ_le_cubeQ
      (by norm_num : (0 : ℝ) ≤ 117)
    have hvalueLog' : valueLog ≤ 117 * (p ^ 2 * Q) := by
      simpa only [mul_assoc] using hvalueLog
    have hresult := hvalueLog'.trans hscale
    simpa only [P] using hresult
  have hcertificateP : certificateLog ≤ 765 * P := by
    simpa only [P, mul_assoc] using hcertificateLog
  have hvalueDiv : valueLog / (Real.log 2 / 16) ≤ 16000 * P := by
    apply (div_le_iff₀ hden16).2
    have hfactor : 117 ≤ 16000 * (Real.log 2 / 16) := by
      nlinarith only [hlogTwoLower]
    have hscaled := mul_le_mul_of_nonneg_right hfactor hP0
    exact hvalueP.trans (by
      simpa only [mul_assoc, mul_left_comm, mul_comm] using hscaled)
  have hcertificateDiv :
      certificateLog / (Real.log 2 / 8) ≤ 16000 * P := by
    apply (div_le_iff₀ hden8).2
    have hfactor : 765 ≤ 16000 * (Real.log 2 / 8) := by
      nlinarith only [hlogTwoLower]
    have hscaled := mul_le_mul_of_nonneg_right hfactor hP0
    exact hcertificateP.trans (by
      simpa only [mul_assoc, mul_left_comm, mul_comm] using hscaled)
  rw [main3LargeAnalyticIntrinsicEliminantSieveBudgetThreshold]
  have hmax : max (valueLog / (Real.log 2 / 16))
      (certificateLog / (Real.log 2 / 8)) ≤ 16000 * P :=
    max_le hvalueDiv hcertificateDiv
  simpa only [valueLog, certificateLog, P, p, Q, mul_assoc] using hmax

/-- At the paper's balanced choice `B = ceil(theta^2)`, the preceding cubic
budget is at most `128000 * theta^7 * log Y`. -/
theorem main3LargeAnalyticIntrinsicEliminantSieveBudgetThreshold_balancedDegree_le
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (data : Main3LargeAnalyticFixedKeyCellAuxiliaryFactorData
      htheta hY hi key cell (main3BalancedDegree theta))
    (L U V : ℝ)
    (hlogL : Real.log (L + 1) ≤ 64 * Real.log (Y : ℝ))
    (hlogUV : Real.log (4 * (U + V)) ≤ 12 * Real.log (Y : ℝ)) :
    main3LargeAnalyticIntrinsicEliminantSieveBudgetThreshold data L U V ≤
      128000 * theta ^ 7 * Real.log (Y : ℝ) := by
  have hgeneric :=
    main3LargeAnalyticIntrinsicEliminantSieveBudgetThreshold_le_uniformLogBudget
      htheta hY hi key cell data L U V hlogL hlogUV
  let p : ℝ := (main3BalancedDegree theta : ℝ) + 1
  have htheta0 : 0 ≤ theta := by linarith
  have hthetaSq : 2 ≤ theta ^ 2 := by
    nlinarith [sq_nonneg (theta - 3)]
  have hp0 : 0 ≤ p := by dsimp [p]; positivity
  have hp : p ≤ 2 * theta ^ 2 := by
    have hdegree := (main3BalancedDegree_nearSquare theta).2
    dsimp [p]
    linarith
  have hpCube : p ^ 3 ≤ 8 * theta ^ 6 := by
    calc
      p ^ 3 ≤ (2 * theta ^ 2) ^ 3 :=
        pow_le_pow_left₀ hp0 hp 3
      _ = 8 * theta ^ 6 := by ring
  have hlogY0 : 0 ≤ Real.log (Y : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ Y by omega))
  have hfinal :
      16000 * p ^ 3 * theta * Real.log (Y : ℝ) ≤
        128000 * theta ^ 7 * Real.log (Y : ℝ) := by
    calc
      16000 * p ^ 3 * theta * Real.log (Y : ℝ) ≤
          16000 * (8 * theta ^ 6) * theta * Real.log (Y : ℝ) := by
        gcongr
      _ = 128000 * theta ^ 7 * Real.log (Y : ℝ) := by ring
  exact hgeneric.trans (by simpa only [p] using hfinal)

end

end PellPaper
