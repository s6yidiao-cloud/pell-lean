import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Stability of the sheared determinant surplus

The rectangular-determinant argument in `main.tex` compares a weight gain
against the centre and denominator cost.  This module records exactly that
real-valued surplus and proves the local continuity consequence of its strict
positivity.  It supplies no determinant estimate or auxiliary-form result.
-/

namespace PellPaper

/-- The leading cubic-logarithmic surplus in `L:sheared`:
the weight-gain coefficient minus the centre and denominator cost. -/
noncomputable def shearedSurplus (alphaM alphaX alphaDE alphaUV rho : ℝ) : ℝ :=
  rho * alphaM / 2 + alphaX * rho ^ 2 / 2 -
    alphaX ^ 2 * rho ^ 3 / (24 * alphaM) -
      (alphaDE * rho ^ 2 + alphaUV * rho) / 2

/-- The five real quantities varied in the local continuity argument, ordered
as `(alphaM, alphaX, alphaDE, alphaUV, rho)`. -/
abbrev ShearedSurplusParameters := ℝ × ℝ × ℝ × ℝ × ℝ

/-- The surplus as a function on the full parameter product. -/
noncomputable def shearedSurplusAt (p : ShearedSurplusParameters) : ℝ :=
  shearedSurplus p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2

/-- With the manuscript's normalized `UV` exponent equal to one, strict
positivity of the surplus is exactly the strict inequality in
`e:shear-condition`. -/
theorem shearedSurplus_pos_iff_source_shearCondition
    (alphaM alphaX alphaDE rho : ℝ) :
    0 < shearedSurplus alphaM alphaX alphaDE 1 rho ↔
      (alphaDE * rho ^ 2 + rho) / 2 <
        rho * alphaM / 2 + alphaX * rho ^ 2 / 2 -
          alphaX ^ 2 * rho ^ 3 / (24 * alphaM) := by
  unfold shearedSurplus
  constructor <;> intro h <;> linarith

/-- Away from the singular hyperplane `alphaM = 0`, the full surplus is
continuous in all five parameters. -/
theorem continuousAt_shearedSurplusAt
    {p : ShearedSurplusParameters} (hp : p.1 ≠ 0) :
    ContinuousAt shearedSurplusAt p := by
  unfold shearedSurplusAt shearedSurplus
  have hden : (24 : ℝ) * p.1 ≠ 0 :=
    mul_ne_zero (by norm_num) hp
  fun_prop

/-- Continuity on the nonsingular parameter region. -/
theorem continuousOn_shearedSurplusAt_alphaM_ne_zero :
    ContinuousOn shearedSurplusAt {p : ShearedSurplusParameters | p.1 ≠ 0} := by
  intro p hp
  exact (continuousAt_shearedSurplusAt hp).continuousWithinAt

/-- In particular, continuity on the positive `alphaM` region used by
`L:sheared`. -/
theorem continuousOn_shearedSurplusAt_alphaM_pos :
    ContinuousOn shearedSurplusAt {p : ShearedSurplusParameters | 0 < p.1} := by
  intro p hp
  exact (continuousAt_shearedSurplusAt (ne_of_gt hp)).continuousWithinAt

/-- A strict positive surplus persists on a metric neighborhood of the full
parameter vector, with the explicit lower bound half of its base value. -/
theorem exists_shearedSurplus_positive_neighborhood
    (p : ShearedSurplusParameters) (hpM : 0 < p.1)
    (hpos : 0 < shearedSurplusAt p) :
    ∃ eps c0 : ℝ, 0 < eps ∧ 0 < c0 ∧
      ∀ q : ShearedSurplusParameters, dist q p < eps →
        c0 ≤ shearedSurplusAt q := by
  have hcont : ContinuousAt shearedSurplusAt p :=
    continuousAt_shearedSurplusAt (ne_of_gt hpM)
  obtain ⟨eps, heps, hclose⟩ :=
    Metric.continuousAt_iff.mp hcont (shearedSurplusAt p / 2) (by linarith)
  refine ⟨eps, shearedSurplusAt p / 2, heps, by linarith, ?_⟩
  intro q hq
  have hdist := hclose hq
  have habs : |shearedSurplusAt q - shearedSurplusAt p| <
      shearedSurplusAt p / 2 := by
    simpa [Real.dist_eq] using hdist
  have hleft : shearedSurplusAt p - shearedSurplusAt q <
      shearedSurplusAt p / 2 :=
    (abs_sub_lt_iff.mp habs).2
  linarith

/-- The same stability statement in coordinatewise form.  This is directly
compatible with the separate logarithmic-exponent ranges in `L:sheared`. -/
theorem exists_shearedSurplus_positive_coordinateBox
    (p : ShearedSurplusParameters) (hpM : 0 < p.1)
    (hpos : 0 < shearedSurplusAt p) :
    ∃ eta c0 : ℝ, 0 < eta ∧ 0 < c0 ∧
      ∀ q : ShearedSurplusParameters,
        |q.1 - p.1| < eta →
        |q.2.1 - p.2.1| < eta →
        |q.2.2.1 - p.2.2.1| < eta →
        |q.2.2.2.1 - p.2.2.2.1| < eta →
        |q.2.2.2.2 - p.2.2.2.2| < eta →
          c0 ≤ shearedSurplusAt q := by
  obtain ⟨eta, c0, heta, hc0, hball⟩ :=
    exists_shearedSurplus_positive_neighborhood p hpM hpos
  refine ⟨eta, c0, heta, hc0, ?_⟩
  intro q hM hX hDE hUV hrho
  apply hball q
  simpa [Prod.dist_eq, Real.dist_eq, max_lt_iff] using
    ⟨hM, hX, hDE, hUV, hrho⟩

/-- A closed coordinate box also preserves the positive lower bound, after
halving the radius supplied by continuity.  This matches the non-strict
parameter ranges in `L:sheared`. -/
theorem exists_shearedSurplus_positive_closedCoordinateBox
    (p : ShearedSurplusParameters) (hpM : 0 < p.1)
    (hpos : 0 < shearedSurplusAt p) :
    ∃ eta c0 : ℝ, 0 < eta ∧ 0 < c0 ∧
      ∀ q : ShearedSurplusParameters,
        |q.1 - p.1| ≤ eta →
        |q.2.1 - p.2.1| ≤ eta →
        |q.2.2.1 - p.2.2.1| ≤ eta →
        |q.2.2.2.1 - p.2.2.2.1| ≤ eta →
        |q.2.2.2.2 - p.2.2.2.2| ≤ eta →
          c0 ≤ shearedSurplusAt q := by
  obtain ⟨eps, c0, heps, hc0, hopen⟩ :=
    exists_shearedSurplus_positive_coordinateBox p hpM hpos
  refine ⟨eps / 2, c0, half_pos heps, hc0, ?_⟩
  intro q hM hX hDE hUV hrho
  apply hopen q <;> linarith

/-- A continuous positive real-valued function stays positive on a closed
coordinate box after halving a metric continuity radius. -/
theorem exists_positive_closedCoordinateBox_of_continuousAt
    (f : ShearedSurplusParameters → ℝ) (p : ShearedSurplusParameters)
    (hcont : ContinuousAt f p) (hpos : 0 < f p) :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ q : ShearedSurplusParameters,
        |q.1 - p.1| ≤ eta →
        |q.2.1 - p.2.1| ≤ eta →
        |q.2.2.1 - p.2.2.1| ≤ eta →
        |q.2.2.2.1 - p.2.2.2.1| ≤ eta →
        |q.2.2.2.2 - p.2.2.2.2| ≤ eta →
          0 < f q := by
  obtain ⟨eps, heps, hclose⟩ :=
    Metric.continuousAt_iff.mp hcont (f p / 2) (by linarith)
  refine ⟨eps / 2, half_pos heps, ?_⟩
  intro q hM hX hDE hUV hrho
  have hdist : dist (f q) (f p) < f p / 2 := by
    apply hclose
    simpa [Prod.dist_eq, Real.dist_eq, max_lt_iff] using
      ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩
  have habs : |f q - f p| < f p / 2 := by
    simpa [Real.dist_eq] using hdist
  have hleft : f p - f q < f p / 2 := (abs_sub_lt_iff.mp habs).2
  linarith

/-- The three strict admissibility gaps from `L:sheared`, packaged into one
continuous real function. -/
def shearedAdmissibilityMargin (p : ShearedSurplusParameters) : ℝ :=
  min p.1 (min (p.2.1 - p.1) (2 * p.1 - p.2.1 * p.2.2.2.2))

/-- The admissibility margin is continuous in all five parameters. -/
theorem continuousAt_shearedAdmissibilityMargin
    (p : ShearedSurplusParameters) :
    ContinuousAt shearedAdmissibilityMargin p := by
  unfold shearedAdmissibilityMargin
  fun_prop

/-- Under the three strict base admissibility assumptions and strict surplus,
one closed coordinate box preserves positive `alphaM`, the order
`alphaM < alphaX`, the aspect inequality `alphaX * rho < 2 * alphaM`, and a
uniform positive surplus lower bound. -/
theorem exists_shearedAdmissible_surplus_closedCoordinateBox
    (p : ShearedSurplusParameters)
    (hpM : 0 < p.1)
    (hpMX : p.1 < p.2.1)
    (hAspect : p.2.1 * p.2.2.2.2 < 2 * p.1)
    (hpos : 0 < shearedSurplusAt p) :
    ∃ eta c0 : ℝ, 0 < eta ∧ 0 < c0 ∧
      ∀ q : ShearedSurplusParameters,
        |q.1 - p.1| ≤ eta →
        |q.2.1 - p.2.1| ≤ eta →
        |q.2.2.1 - p.2.2.1| ≤ eta →
        |q.2.2.2.1 - p.2.2.2.1| ≤ eta →
        |q.2.2.2.2 - p.2.2.2.2| ≤ eta →
          0 < q.1 ∧ q.1 < q.2.1 ∧
            q.2.1 * q.2.2.2.2 < 2 * q.1 ∧ c0 ≤ shearedSurplusAt q := by
  have hmargin : 0 < shearedAdmissibilityMargin p := by
    unfold shearedAdmissibilityMargin
    exact lt_min hpM (lt_min (sub_pos.mpr hpMX) (sub_pos.mpr hAspect))
  obtain ⟨etaS, c0, hetaS, hc0, hsurplus⟩ :=
    exists_shearedSurplus_positive_closedCoordinateBox p hpM hpos
  obtain ⟨etaA, hetaA, hadmissible⟩ :=
    exists_positive_closedCoordinateBox_of_continuousAt
      shearedAdmissibilityMargin p
      (continuousAt_shearedAdmissibilityMargin p) hmargin
  refine ⟨min etaS etaA, c0, lt_min hetaS hetaA, hc0, ?_⟩
  intro q hM hX hDE hUV hrho
  have hsurplusq : c0 ≤ shearedSurplusAt q :=
    hsurplus q
      (le_trans hM (min_le_left _ _))
      (le_trans hX (min_le_left _ _))
      (le_trans hDE (min_le_left _ _))
      (le_trans hUV (min_le_left _ _))
      (le_trans hrho (min_le_left _ _))
  have hmarginq : 0 < shearedAdmissibilityMargin q :=
    hadmissible q
      (le_trans hM (min_le_right _ _))
      (le_trans hX (min_le_right _ _))
      (le_trans hDE (min_le_right _ _))
      (le_trans hUV (min_le_right _ _))
      (le_trans hrho (min_le_right _ _))
  have hqM : 0 < q.1 :=
    lt_of_lt_of_le hmarginq (min_le_left _ _)
  have hqRest : 0 < min (q.2.1 - q.1)
      (2 * q.1 - q.2.1 * q.2.2.2.2) :=
    lt_of_lt_of_le hmarginq (min_le_right _ _)
  have hqOrderGap : 0 < q.2.1 - q.1 :=
    lt_of_lt_of_le hqRest (min_le_left _ _)
  have hqAspectGap : 0 < 2 * q.1 - q.2.1 * q.2.2.2.2 :=
    lt_of_lt_of_le hqRest (min_le_right _ _)
  exact ⟨hqM, sub_pos.mp hqOrderGap, sub_pos.mp hqAspectGap, hsurplusq⟩

/-- The full collection of strict positivity and shape gaps used by the
`L:sheared` parameter box: positivity of `alphaM`, `alphaDE`, `alphaUV`, and
`rho`, followed by the two strict shape inequalities. -/
def shearedFullAdmissibilityMargin (p : ShearedSurplusParameters) : ℝ :=
  min p.1 (min p.2.2.1 (min p.2.2.2.1
    (min p.2.2.2.2 (min (p.2.1 - p.1) (2 * p.1 - p.2.1 * p.2.2.2.2)))))

/-- The full positivity-and-shape margin is continuous in all five
parameters. -/
theorem continuousAt_shearedFullAdmissibilityMargin
    (p : ShearedSurplusParameters) :
    ContinuousAt shearedFullAdmissibilityMargin p := by
  unfold shearedFullAdmissibilityMargin
  fun_prop

/-- Under all strict positivity and shape assumptions used for the sheared
parameter range, one closed coordinate box preserves those assumptions and a
uniform positive lower bound for the surplus.  This is only a local
real-parameter stability statement; it supplies no determinant estimate. -/
theorem exists_shearedFullyAdmissible_surplus_closedCoordinateBox
    (p : ShearedSurplusParameters)
    (hpM : 0 < p.1)
    (hpMX : p.1 < p.2.1)
    (hDE : 0 < p.2.2.1)
    (hUV : 0 < p.2.2.2.1)
    (hrho : 0 < p.2.2.2.2)
    (hAspect : p.2.1 * p.2.2.2.2 < 2 * p.1)
    (hpos : 0 < shearedSurplusAt p) :
    ∃ eta c0 : ℝ, 0 < eta ∧ 0 < c0 ∧
      ∀ q : ShearedSurplusParameters,
        |q.1 - p.1| ≤ eta →
        |q.2.1 - p.2.1| ≤ eta →
        |q.2.2.1 - p.2.2.1| ≤ eta →
        |q.2.2.2.1 - p.2.2.2.1| ≤ eta →
        |q.2.2.2.2 - p.2.2.2.2| ≤ eta →
          0 < q.1 ∧ q.1 < q.2.1 ∧ 0 < q.2.2.1 ∧ 0 < q.2.2.2.1 ∧
            0 < q.2.2.2.2 ∧ q.2.1 * q.2.2.2.2 < 2 * q.1 ∧
              c0 ≤ shearedSurplusAt q := by
  have hmargin : 0 < shearedFullAdmissibilityMargin p := by
    unfold shearedFullAdmissibilityMargin
    exact lt_min hpM (lt_min hDE (lt_min hUV (lt_min hrho
      (lt_min (sub_pos.mpr hpMX) (sub_pos.mpr hAspect)))))
  obtain ⟨etaS, c0, hetaS, hc0, hsurplus⟩ :=
    exists_shearedSurplus_positive_closedCoordinateBox p hpM hpos
  obtain ⟨etaA, hetaA, hadmissible⟩ :=
    exists_positive_closedCoordinateBox_of_continuousAt
      shearedFullAdmissibilityMargin p
      (continuousAt_shearedFullAdmissibilityMargin p) hmargin
  refine ⟨min etaS etaA, c0, lt_min hetaS hetaA, hc0, ?_⟩
  intro q hM hX hDEq hUVq hrhoq
  have hsurplusq : c0 ≤ shearedSurplusAt q :=
    hsurplus q
      (le_trans hM (min_le_left _ _))
      (le_trans hX (min_le_left _ _))
      (le_trans hDEq (min_le_left _ _))
      (le_trans hUVq (min_le_left _ _))
      (le_trans hrhoq (min_le_left _ _))
  have hmarginq : 0 < shearedFullAdmissibilityMargin q :=
    hadmissible q
      (le_trans hM (min_le_right _ _))
      (le_trans hX (min_le_right _ _))
      (le_trans hDEq (min_le_right _ _))
      (le_trans hUVq (min_le_right _ _))
      (le_trans hrhoq (min_le_right _ _))
  have hqM : 0 < q.1 :=
    lt_of_lt_of_le hmarginq (min_le_left _ _)
  have hqRest0 : 0 < min q.2.2.1 (min q.2.2.2.1
      (min q.2.2.2.2 (min (q.2.1 - q.1)
        (2 * q.1 - q.2.1 * q.2.2.2.2)))) :=
    lt_of_lt_of_le hmarginq (min_le_right _ _)
  have hqDE : 0 < q.2.2.1 :=
    lt_of_lt_of_le hqRest0 (min_le_left _ _)
  have hqRest1 : 0 < min q.2.2.2.1
      (min q.2.2.2.2 (min (q.2.1 - q.1)
        (2 * q.1 - q.2.1 * q.2.2.2.2))) :=
    lt_of_lt_of_le hqRest0 (min_le_right _ _)
  have hqUV : 0 < q.2.2.2.1 :=
    lt_of_lt_of_le hqRest1 (min_le_left _ _)
  have hqRest2 : 0 < min q.2.2.2.2
      (min (q.2.1 - q.1) (2 * q.1 - q.2.1 * q.2.2.2.2)) :=
    lt_of_lt_of_le hqRest1 (min_le_right _ _)
  have hqrho : 0 < q.2.2.2.2 :=
    lt_of_lt_of_le hqRest2 (min_le_left _ _)
  have hqRest3 : 0 < min (q.2.1 - q.1)
      (2 * q.1 - q.2.1 * q.2.2.2.2) :=
    lt_of_lt_of_le hqRest2 (min_le_right _ _)
  have hqOrderGap : 0 < q.2.1 - q.1 :=
    lt_of_lt_of_le hqRest3 (min_le_left _ _)
  have hqAspectGap : 0 < 2 * q.1 - q.2.1 * q.2.2.2.2 :=
    lt_of_lt_of_le hqRest3 (min_le_right _ _)
  exact ⟨hqM, sub_pos.mp hqOrderGap, hqDE, hqUV, hqrho,
    sub_pos.mp hqAspectGap, hsurplusq⟩

end PellPaper
