import Pell.Main3LargeAnalyticSieveEnvelopePower
import Mathlib.Tactic

/-!
# Workspace: a coarse algebraic Main3 key envelope

The analytic geometry is kept outside this lemma.  Once the five aggregate
inputs have the displayed common bounds, the expanded power-form sieve
envelope is bounded by one deliberately generous absolute constant.
-/

namespace PellPaper

noncomputable section

/-- A deliberately generous constant for the deterministic envelope
expansion.  Its size is irrelevant to the eventual power saving. -/
def main3LargeAnalyticCoarseKeyEnvelopeConstant : ℝ :=
  1000000000000000000000

/-- Replacing a possibly signed reciprocal budget by its nonnegative part can
only enlarge the variable aggregate.  This avoids duplicating the geometric
lower-bound argument that originally established positivity of the budget. -/
theorem fullCellOddDegreeSieveVariableAggregateEnvelope_le_max_reciprocal_workspace
    (N D : ℕ) (cellCount area reciprocalSum : ℝ) (hN : 4 ≤ N) :
    fullCellOddDegreeSieveVariableAggregateEnvelope
        N D cellCount area reciprocalSum ≤
      fullCellOddDegreeSieveVariableAggregateEnvelope
        N D cellCount area (max 0 reciprocalSum) := by
  let Llog : ℝ := 1 + Real.log (16 * (N : ℝ) ^ 2)
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have harg : (1 : ℝ) ≤ 16 * (N : ℝ) ^ 2 := by
    have hNfour : (4 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith [sq_nonneg (N : ℝ)]
  have hLlog : 0 ≤ Llog := by
    dsimp only [Llog]
    linarith [Real.log_nonneg harg]
  have hcoefficient :
      0 ≤ 768 * (N : ℝ) * Llog +
        96 * ((D : ℝ) + 1) ^ 2 * Llog := by positivity
  unfold fullCellOddDegreeSieveVariableAggregateEnvelope
  dsimp only
  have hmul :=
    mul_le_mul_of_nonneg_left (le_max_right 0 reciprocalSum) hcoefficient
  exact add_le_add (le_refl _) (by simpa only [Llog] using hmul)

/-- The complex reciprocal budget is below the common outer majorant once
the two logarithms and the two square-root scales have been bounded. -/
theorem complexReciprocalBudget_mul_le_common_workspace
    (X sqrtE sqrtEMD logH logL S T : ℝ)
    (hX : 0 ≤ X) (hsqrtE : 0 ≤ sqrtE) (_hsqrtEMD : 0 ≤ sqrtEMD)
    (hS : 1 ≤ S) (hT : 0 ≤ T)
    (hlogL0 : 0 ≤ logL) (hlogH : logH ≤ 16 * S)
    (hlogL : logL ≤ 16 * S)
    (hXsqrtE : X * sqrtE ≤ 33 * T)
    (hXsqrtEMD : X * sqrtEMD ≤ 94 * T) :
    X * (9216 * sqrtE * logH * logL + 663552 * sqrtEMD) ≤
      3000000000000000 * S ^ 3 * T := by
  have hS0 : 0 ≤ S := zero_le_one.trans hS
  have hSsqCube : S ^ 2 ≤ S ^ 3 :=
    pow_le_pow_right₀ hS (by omega)
  have hTle : T ≤ S ^ 3 * T := by
    have hS3one : 1 ≤ S ^ 3 := one_le_pow₀ hS
    nlinarith [mul_le_mul_of_nonneg_right hS3one hT]
  have hS2T : S ^ 2 * T ≤ S ^ 3 * T := by gcongr
  have hfirstLift : 77856768 * S ^ 2 * T ≤
      77856768 * (S ^ 3 * T) := by
    have := mul_le_mul_of_nonneg_left hS2T
      (by norm_num : (0 : ℝ) ≤ 77856768)
    nlinarith
  have hsecondLift : 62373888 * T ≤
      62373888 * (S ^ 3 * T) := by gcongr
  have hsecond : X * (663552 * sqrtEMD) ≤ 62373888 * T := by
    calc
      X * (663552 * sqrtEMD) = 663552 * (X * sqrtEMD) := by ring
      _ ≤ 663552 * (94 * T) := by gcongr
      _ = 62373888 * T := by ring
  by_cases hlogH0 : 0 ≤ logH
  · have hfirst : X * (9216 * sqrtE * logH * logL) ≤
        77856768 * S ^ 2 * T := by
      calc
        X * (9216 * sqrtE * logH * logL) =
            9216 * (X * sqrtE) * logH * logL := by ring
        _ ≤ 9216 * (33 * T) * (16 * S) * (16 * S) := by gcongr
        _ = 77856768 * S ^ 2 * T := by ring
    calc
      X * (9216 * sqrtE * logH * logL + 663552 * sqrtEMD) =
          X * (9216 * sqrtE * logH * logL) +
            X * (663552 * sqrtEMD) := by ring
      _ ≤ 77856768 * S ^ 2 * T + 62373888 * T :=
        add_le_add hfirst hsecond
      _ ≤ 77856768 * (S ^ 3 * T) +
          62373888 * (S ^ 3 * T) := add_le_add hfirstLift hsecondLift
      _ ≤ 3000000000000000 * S ^ 3 * T := by nlinarith
  · have hfirstNonpos :
        X * (9216 * sqrtE * logH * logL) ≤ 0 := by
      have : logH ≤ 0 := le_of_not_ge hlogH0
      have hnonneg : 0 ≤ X * 9216 * sqrtE * logL := by positivity
      nlinarith
    calc
      X * (9216 * sqrtE * logH * logL + 663552 * sqrtEMD) =
          X * (9216 * sqrtE * logH * logL) +
            X * (663552 * sqrtEMD) := by ring
      _ ≤ 0 + 62373888 * T := add_le_add hfirstNonpos hsecond
      _ ≤ 62373888 * (S ^ 3 * T) := by simpa using hsecondLift
      _ ≤ 3000000000000000 * S ^ 3 * T := by nlinarith

/-- Real-branch version, including the annular-scale factor. -/
theorem realReciprocalBudget_mul_le_common_workspace
    (X Lscale sqrtE sqrtEMD logH logL S T : ℝ)
    (hX : 0 ≤ X) (hLscale0 : 0 ≤ Lscale) (hsqrtE : 0 ≤ sqrtE)
    (hsqrtEMD : 0 ≤ sqrtEMD)
    (hS : 1 ≤ S) (hT : 0 ≤ T)
    (hLscale : Lscale ≤ 100 * S)
    (hlogL0 : 0 ≤ logL) (hlogH : logH ≤ 16 * S)
    (hlogL : logL ≤ 16 * S)
    (hXsqrtE : X * sqrtE ≤ 33 * T)
    (hXsqrtEMD : X * sqrtEMD ≤ 94 * T) :
    X * (38880000 * Lscale * sqrtE * logH * logL +
        201553920000 * Lscale * sqrtEMD) ≤
      3000000000000000 * S ^ 3 * T := by
  have hS0 : 0 ≤ S := zero_le_one.trans hS
  have hSsqCube : S ^ 2 ≤ S ^ 3 :=
    pow_le_pow_right₀ hS (by omega)
  have hTle : T ≤ S ^ 3 * T := by
    have hS3one : 1 ≤ S ^ 3 := one_le_pow₀ hS
    nlinarith [mul_le_mul_of_nonneg_right hS3one hT]
  have hsecond : X * (201553920000 * Lscale * sqrtEMD) ≤
      1894606848000000 * S * T := by
    calc
      X * (201553920000 * Lscale * sqrtEMD) =
          201553920000 * Lscale * (X * sqrtEMD) := by ring
      _ ≤ 201553920000 * (100 * S) * (94 * T) := by gcongr
      _ = 1894606848000000 * S * T := by ring
  have hST : S * T ≤ S ^ 3 * T := by
    have hS1S3raw : S ^ (1 : ℕ) ≤ S ^ (3 : ℕ) :=
      pow_le_pow_right₀ hS (by norm_num)
    have hS1S3 : S ≤ S ^ 3 := by simpa using hS1S3raw
    gcongr
  have hsecondLift : 1894606848000000 * S * T ≤
      1894606848000000 * (S ^ 3 * T) := by
    have := mul_le_mul_of_nonneg_left hST
      (by norm_num : (0 : ℝ) ≤ 1894606848000000)
    nlinarith
  by_cases hlogH0 : 0 ≤ logH
  · have hfirst :
        X * (38880000 * Lscale * sqrtE * logH * logL) ≤
          32845824000000 * S ^ 3 * T := by
      calc
        X * (38880000 * Lscale * sqrtE * logH * logL) =
            38880000 * Lscale * (X * sqrtE) * logH * logL := by ring
        _ ≤ 38880000 * (100 * S) * (33 * T) *
            (16 * S) * (16 * S) := by gcongr
        _ = 32845824000000 * S ^ 3 * T := by ring
    calc
      X * (38880000 * Lscale * sqrtE * logH * logL +
          201553920000 * Lscale * sqrtEMD) =
          X * (38880000 * Lscale * sqrtE * logH * logL) +
            X * (201553920000 * Lscale * sqrtEMD) := by ring
      _ ≤ 32845824000000 * S ^ 3 * T +
          1894606848000000 * S * T := add_le_add hfirst hsecond
      _ ≤ 32845824000000 * S ^ 3 * T +
          1894606848000000 * (S ^ 3 * T) := by
        exact add_le_add (le_refl _) hsecondLift
      _ ≤ 3000000000000000 * S ^ 3 * T := by nlinarith
  · have hfirstNonpos :
        X * (38880000 * Lscale * sqrtE * logH * logL) ≤ 0 := by
      have : logH ≤ 0 := le_of_not_ge hlogH0
      have hnonneg : 0 ≤ X * 38880000 * Lscale * sqrtE * logL := by
        positivity
      nlinarith
    calc
      X * (38880000 * Lscale * sqrtE * logH * logL +
          201553920000 * Lscale * sqrtEMD) =
          X * (38880000 * Lscale * sqrtE * logH * logL) +
            X * (201553920000 * Lscale * sqrtEMD) := by ring
      _ ≤ 0 + 1894606848000000 * S * T :=
        add_le_add hfirstNonpos hsecond
      _ ≤ 1894606848000000 * (S ^ 3 * T) := by
        simpa using hsecondLift
      _ ≤ 3000000000000000 * S ^ 3 * T := by nlinarith

/-- Pure nonnegative algebra for the coarse per-key sieve envelope. -/
theorem fullCellOddDegreeSievePowerAggregateEnvelope_le_coarseKeyEnvelope_workspace
    (theta S T cellCount area Z L reciprocalSum : ℝ) (D : ℕ)
    (htheta : 1 ≤ theta) (hS : 1 ≤ S) (hT : 0 ≤ T)
    (hcellCount : 0 ≤ cellCount) (_harea : 0 ≤ area)
    (hZ : 0 < Z) (hL0 : 0 ≤ L) (hreciprocal : 0 ≤ reciprocalSum)
    (hL : L ≤ 7 * S)
    (hdegree : (D : ℝ) + 1 ≤ 2 * theta ^ 3)
    (hcellArea : cellCount * area / Z ≤ 31363200 * S * T)
    (hcellZ : cellCount * Z ^ 2 ≤ 7200 * S * T)
    (hZreciprocal : Z * reciprocalSum ≤
      3000000000000000 * S ^ 3 * T)
    (hreciprocalUpper : reciprocalSum ≤
      3000000000000000 * S ^ 3 * T) :
    2 * fullCellOddDegreeSievePowerAggregateEnvelope
          Z L D cellCount area reciprocalSum ≤
      main3LargeAnalyticCoarseKeyEnvelopeConstant *
        theta ^ 6 * S ^ 4 * T := by
  have htheta0 : 0 ≤ theta := zero_le_one.trans htheta
  have hS0 : 0 ≤ S := zero_le_one.trans hS
  have hthetaSixOne : 1 ≤ theta ^ 6 := one_le_pow₀ htheta
  have hSSq : S ^ 2 ≤ S ^ 4 := by
    exact pow_le_pow_right₀ hS (by omega)
  have hSCube : S ^ 3 ≤ S ^ 4 := by
    exact pow_le_pow_right₀ hS (by omega)
  have hdegree0 : 0 ≤ (D : ℝ) + 1 := by positivity
  have hdegreeSq : ((D : ℝ) + 1) ^ 2 ≤ 4 * theta ^ 6 := by
    calc
      ((D : ℝ) + 1) ^ 2 ≤ (2 * theta ^ 3) ^ 2 :=
        pow_le_pow_left₀ hdegree0 hdegree 2
      _ = 4 * theta ^ 6 := by ring
  have hLsq : L ^ 2 ≤ 49 * S ^ 2 := by
    calc
      L ^ 2 ≤ (7 * S) ^ 2 := pow_le_pow_left₀ hL0 hL 2
      _ = 49 * S ^ 2 := by ring
  have hST_to_target : S ^ 2 * T ≤ theta ^ 6 * S ^ 4 * T := by
    calc
      S ^ 2 * T ≤ S ^ 4 * T := by gcongr
      _ ≤ theta ^ 6 * S ^ 4 * T := by
        have := mul_le_mul_of_nonneg_right hthetaSixOne
          (show 0 ≤ S ^ 4 * T by positivity)
        nlinarith
  have hS3T_to_target : S ^ 3 * T ≤ theta ^ 6 * S ^ 4 * T := by
    calc
      S ^ 3 * T ≤ S ^ 4 * T := by gcongr
      _ ≤ theta ^ 6 * S ^ 4 * T := by
        have := mul_le_mul_of_nonneg_right hthetaSixOne
          (show 0 ≤ S ^ 4 * T by positivity)
        nlinarith
  have hareaTerm :
      cellCount * (9216 * area * L / Z) ≤
        2023302758400 * (theta ^ 6 * S ^ 4 * T) := by
    calc
      cellCount * (9216 * area * L / Z) =
          9216 * (cellCount * area / Z) * L := by ring
      _ ≤ 9216 * (31363200 * S * T) * (7 * S) := by gcongr
      _ = 2023302758400 * (S ^ 2 * T) := by ring
      _ ≤ 2023302758400 * (theta ^ 6 * S ^ 4 * T) := by gcongr
  have hdegreeTerm :
      cellCount * (256 * ((D : ℝ) + 1) ^ 2 * Z ^ 2 * L ^ 2) ≤
        361267200 * (theta ^ 6 * S ^ 4 * T) := by
    calc
      cellCount * (256 * ((D : ℝ) + 1) ^ 2 * Z ^ 2 * L ^ 2) =
          256 * ((D : ℝ) + 1) ^ 2 * (cellCount * Z ^ 2) * L ^ 2 := by ring
      _ ≤ 256 * (4 * theta ^ 6) * (7200 * S * T) * (49 * S ^ 2) := by
        gcongr
      _ = 361267200 * theta ^ 6 * S ^ 3 * T := by ring
      _ ≤ 361267200 * (theta ^ 6 * S ^ 4 * T) := by
        have := mul_le_mul_of_nonneg_left hSCube
          (show 0 ≤ 361267200 * theta ^ 6 by positivity)
        nlinarith
  have hlinearReciprocalTerm :
      (1536 * Z * L) * reciprocalSum ≤
        32256000000000000000 * (theta ^ 6 * S ^ 4 * T) := by
    calc
      (1536 * Z * L) * reciprocalSum =
          1536 * L * (Z * reciprocalSum) := by ring
      _ ≤ 1536 * (7 * S) *
          (3000000000000000 * S ^ 3 * T) := by gcongr
      _ = 32256000000000000000 * (S ^ 4 * T) := by ring
      _ ≤ 32256000000000000000 *
          (theta ^ 6 * S ^ 4 * T) := by
        have := mul_le_mul_of_nonneg_right hthetaSixOne
          (show 0 ≤ S ^ 4 * T by positivity)
        nlinarith
  have hdegreeReciprocalTerm :
      (96 * ((D : ℝ) + 1) ^ 2 * L) * reciprocalSum ≤
        8064000000000000000 * (theta ^ 6 * S ^ 4 * T) := by
    calc
      (96 * ((D : ℝ) + 1) ^ 2 * L) * reciprocalSum ≤
          96 * (4 * theta ^ 6) * (7 * S) *
            (3000000000000000 * S ^ 3 * T) := by gcongr
      _ = 8064000000000000000 * (theta ^ 6 * S ^ 4 * T) := by ring
  unfold fullCellOddDegreeSievePowerAggregateEnvelope
  unfold main3LargeAnalyticCoarseKeyEnvelopeConstant
  have htarget : 0 ≤ theta ^ 6 * S ^ 4 * T := by positivity
  nlinarith

end

end PellPaper

#print axioms PellPaper.fullCellOddDegreeSievePowerAggregateEnvelope_le_coarseKeyEnvelope_workspace
