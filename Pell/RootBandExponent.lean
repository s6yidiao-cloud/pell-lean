import Pell.PowerSaving

/-!
# Scalar exponent ledger for fixed root bands

The finite root-band bound has a factor counting roots in a band and a
scaled-cutoff factor at its lower endpoint.  If the lower and upper endpoints
are heuristically of sizes `Y^a` and `Y^b`, respectively, its real-power
exponent is
`b + (1 - 2 * a) * (1 - d)`.  This module isolates the exact scalar algebra
behind that expression.

It deliberately does not select finitely many bands, turn natural endpoint
inequalities into real-power estimates, or assert a Pell power saving.  Those
remain separate quantitative obligations.
-/

namespace PellPaper

/-- The saving contributed by a fixed-height squarefree estimate of exponent
`d` at a lower root exponent `a`, before paying for the width of the band. -/
noncomputable def fixedHeightLayerSaving (a d : ℝ) : ℝ :=
  a + (1 - 2 * a) * d

/-- The real-power exponent suggested by a root band with lower exponent `a`,
upper exponent `b`, and fixed-height saving `d`. -/
noncomputable def rootBandExponent (a b d : ℝ) : ℝ :=
  b + (1 - 2 * a) * (1 - d)

/-- The corresponding saving, written so that
`rootBandExponent = 1 - rootBandSaving`. -/
noncomputable def rootBandSaving (a b d : ℝ) : ℝ :=
  2 * a - b + (1 - 2 * a) * d

/-- A root band's exponent is one minus its scalar saving. -/
theorem rootBandExponent_eq_one_sub_rootBandSaving (a b d : ℝ) :
    rootBandExponent a b d = 1 - rootBandSaving a b d := by
  unfold rootBandExponent rootBandSaving
  ring

/-- At a positive base, the product of the endpoint and scaled-cutoff powers
is exactly the power with the root-band exponent. -/
theorem rpow_rootBandExponent (Y a b d : ℝ) (hY : 0 < Y) :
    Y ^ rootBandExponent a b d =
      Y ^ b * (Y ^ (1 - 2 * a)) ^ (1 - d) := by
  unfold rootBandExponent
  rw [Real.rpow_add hY, Real.rpow_mul hY.le]

/-- The scalar exponent criterion converts to the corresponding real-power
bound for every base at least one. -/
theorem rpow_rootBandExponent_le_one_sub
    {Y a b d delta : ℝ} (hY : 1 ≤ Y)
    (hexponent : rootBandExponent a b d ≤ 1 - delta) :
    Y ^ rootBandExponent a b d ≤ Y ^ (1 - delta) := by
  exact Real.rpow_le_rpow_of_exponent_le hY hexponent

/-- The width `b - a` is exactly the loss from the lower-layer saving. -/
theorem rootBandSaving_eq_fixedHeightLayerSaving_sub_width (a b d : ℝ) :
    rootBandSaving a b d = fixedHeightLayerSaving a d - (b - a) := by
  unfold rootBandSaving fixedHeightLayerSaving
  ring

/-- Equivalently, the root-band exponent is the complementary lower-layer
exponent plus exactly the width of the band. -/
theorem rootBandExponent_eq_one_sub_fixedHeightLayerSaving_add_width
    (a b d : ℝ) :
    rootBandExponent a b d =
      1 - fixedHeightLayerSaving a d + (b - a) := by
  unfold rootBandExponent fixedHeightLayerSaving
  ring

/-- Exact scalar criterion for a non-strict target saving on one root band. -/
theorem rootBandExponent_le_one_sub_iff (a b d delta : ℝ) :
    rootBandExponent a b d ≤ 1 - delta ↔ delta ≤ rootBandSaving a b d := by
  rw [rootBandExponent_eq_one_sub_rootBandSaving]
  constructor <;> intro h <;> linarith

/-- Exact scalar criterion for a strict target saving on one root band. -/
theorem rootBandExponent_lt_one_sub_iff (a b d delta : ℝ) :
    rootBandExponent a b d < 1 - delta ↔ delta < rootBandSaving a b d := by
  rw [rootBandExponent_eq_one_sub_rootBandSaving]
  constructor <;> intro h <;> linarith

/-- A lower-layer margin that absorbs the band width gives the desired
non-strict power-exponent bound. -/
theorem rootBandExponent_le_one_sub_of_layer_margin
    {a b d delta : ℝ}
    (hmargin : delta + (b - a) ≤ fixedHeightLayerSaving a d) :
    rootBandExponent a b d ≤ 1 - delta := by
  rw [rootBandExponent_eq_one_sub_fixedHeightLayerSaving_add_width]
  linarith

/-- A strict lower-layer margin that absorbs the band width gives a strict
power-exponent bound. -/
theorem rootBandExponent_lt_one_sub_of_layer_margin
    {a b d delta : ℝ}
    (hmargin : delta + (b - a) < fixedHeightLayerSaving a d) :
    rootBandExponent a b d < 1 - delta := by
  rw [rootBandExponent_eq_one_sub_fixedHeightLayerSaving_add_width]
  linarith

/-- The actual finite-band height budget is controlled at the upper endpoint.
When the fixed height is the rescaled height there, the full scalar ledger
has the corrections `2 * (b - a) * (1 - d)` and
`(1 - 2 * b) * (Delta phi - d)`.  They are losses in the usual small-root
parameter range, as checked separately below, but are signed quantities in
this unconstrained identity.  The theorem neither proves the endpoint budget
nor selects a finite family of bands. -/
theorem rootBandExponent_eq_one_sub_squarePartLayerSaving_add_upper_endpoint_losses
    {theta a b phi d : ℝ}
    (hsigma : 1 - 2 * b ≠ 0)
    (hphi : phi = theta / (1 - 2 * b)) :
    rootBandExponent a b d =
      1 - squarePartLayerSaving theta b +
        2 * (b - a) * (1 - d) +
        (1 - 2 * b) * (Delta phi - d) := by
  rw [hphi, squarePartLayerSaving_eq_add_scaled_Delta hsigma]
  unfold rootBandExponent
  ring

/-- In the usual small-root parameter range, both displayed upper-endpoint
losses are nonnegative.  The theorem is only sign bookkeeping and does not
establish the natural endpoint inequalities required by the finite-band
counting bound. -/
theorem rootBand_upper_endpoint_losses_nonneg
    {a b phi d : ℝ}
    (hab : a ≤ b) (hbhalf : b ≤ (1 : ℝ) / 2)
    (hdone : d ≤ 1) (hd : d ≤ Delta phi) :
    0 ≤ 2 * (b - a) * (1 - d) ∧
      0 ≤ (1 - 2 * b) * (Delta phi - d) := by
  constructor
  · exact mul_nonneg
      (mul_nonneg (by norm_num) (sub_nonneg.mpr hab))
      (sub_nonneg.mpr hdone)
  · exact mul_nonneg (by linarith) (sub_nonneg.mpr hd)

/-- An explicit scalar condition that guarantees the finite-band exponent is
at most the target exponent.  The condition retains exactly the two losses
in the upper-endpoint ledger; constructing finite bands satisfying it is the
remaining parameter-selection problem. -/
theorem rootBandExponent_le_one_sub_of_upper_squarePartLayer_margin
    {theta a b phi d delta : ℝ}
    (hsigma : 1 - 2 * b ≠ 0)
    (hphi : phi = theta / (1 - 2 * b))
    (hmargin : delta + 2 * (b - a) * (1 - d) +
      (1 - 2 * b) * (Delta phi - d) ≤ squarePartLayerSaving theta b) :
    rootBandExponent a b d ≤ 1 - delta := by
  rw [rootBandExponent_eq_one_sub_squarePartLayerSaving_add_upper_endpoint_losses
    hsigma hphi]
  linarith

/-- At a zero-width band and the limiting fixed-height saving, the exponent
is exactly complementary to the manuscript's square-part layer saving.
This is an identity only: applications of `FixedHeightSquarefree` still need
a strict choice `d < Delta phi`. -/
theorem rootBandExponent_at_single_layer
    {theta a : ℝ} (hsigma : 1 - 2 * a ≠ 0) :
    rootBandExponent a a (Delta (theta / (1 - 2 * a))) =
      1 - squarePartLayerSaving theta a := by
  simpa using
    (rootBandExponent_eq_one_sub_squarePartLayerSaving_add_upper_endpoint_losses
      (theta := theta) (a := a) (b := a)
      (phi := theta / (1 - 2 * a))
      (d := Delta (theta / (1 - 2 * a))) hsigma rfl)

/-- The limiting zero-width layer has at least the original target saving
whenever the base height is at least three and the square-part exponent is
nonnegative.  This still does not furnish a strict fixed-height saving or a
positive-width band. -/
theorem rootBandExponent_at_single_layer_le_one_sub_Delta
    {theta a : ℝ} (htheta : 3 ≤ theta) (ha : 0 ≤ a)
    (hsigma : 1 - 2 * a ≠ 0) :
    rootBandExponent a a (Delta (theta / (1 - 2 * a))) ≤
      1 - Delta theta := by
  rw [rootBandExponent_at_single_layer hsigma]
  linarith [Delta_le_squarePartLayerSaving theta a htheta ha]

end PellPaper
