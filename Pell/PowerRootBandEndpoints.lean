import Pell.FiniteRootBandAggregation
import Pell.RootBandExponent
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Rounded real-power endpoints for finite root bands

The small square-part range is naturally cut at a ceiling of a real power of
the dyadic scale.  This file makes the resulting natural intervals explicit.
It separates two issues which are easy to conflate:

* adjacent ceiling endpoints give an exact finite cover of the natural root
  range; and
* a ceiling endpoint is controlled by a *strictly larger* real-power
  exponent, once a stated slack factor absorbs the rounding error.

The second point is deliberately quantified by hypotheses such as
`2 <= Y ^ eta`.  No asymptotic parameter selection, fixed-height estimate,
or Pell power saving is asserted here.
-/

namespace PellPaper

open Filter

/-- The natural endpoint obtained by rounding a root-scale power upward. -/
noncomputable def powerRootCeilEndpoint (Y : ℕ) (a : ℝ) : ℕ :=
  ⌈(Y : ℝ) ^ a⌉₊

/-- The natural endpoint obtained by rounding a root-scale power downward. -/
noncomputable def powerRootFloorEndpoint (Y : ℕ) (a : ℝ) : ℕ :=
  ⌊(Y : ℝ) ^ a⌋₊

/-- The closed natural band between two adjacent ceiling endpoints. -/
noncomputable def powerRootCeilBand (Y : ℕ) (a : ℕ → ℝ) (i : ℕ) : Finset ℕ :=
  Finset.Icc (powerRootCeilEndpoint Y (a i))
    (powerRootCeilEndpoint Y (a (i + 1)))

/-- A real power is below its rounded-up natural endpoint. -/
theorem rpow_le_powerRootCeilEndpoint (Y : ℕ) (a : ℝ) :
    (Y : ℝ) ^ a ≤ (powerRootCeilEndpoint Y a : ℝ) := by
  simpa [powerRootCeilEndpoint] using Nat.le_ceil ((Y : ℝ) ^ a)

/-- A rounded-up endpoint is less than one above its underlying real power. -/
theorem powerRootCeilEndpoint_lt_rpow_add_one (Y : ℕ) (a : ℝ) :
    (powerRootCeilEndpoint Y a : ℝ) < (Y : ℝ) ^ a + 1 := by
  simpa [powerRootCeilEndpoint] using
    Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg Y) a)

/-- A rounded-down endpoint is below its underlying real power. -/
theorem powerRootFloorEndpoint_le_rpow (Y : ℕ) (a : ℝ) :
    (powerRootFloorEndpoint Y a : ℝ) ≤ (Y : ℝ) ^ a := by
  simpa [powerRootFloorEndpoint] using
    Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg Y) a)

/-- The real power is less than one above its rounded-down endpoint. -/
theorem rpow_lt_powerRootFloorEndpoint_add_one (Y : ℕ) (a : ℝ) :
    (Y : ℝ) ^ a < (powerRootFloorEndpoint Y a : ℝ) + 1 := by
  simpa [powerRootFloorEndpoint] using Nat.lt_floor_add_one ((Y : ℝ) ^ a)

/-- At a positive dyadic scale, every ceiling endpoint is positive. -/
theorem one_le_powerRootCeilEndpoint {Y : ℕ} (hY : 1 ≤ Y) (a : ℝ) :
    1 ≤ powerRootCeilEndpoint Y a := by
  rw [powerRootCeilEndpoint, Nat.one_le_ceil_iff]
  exact Real.rpow_pos_of_pos (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hY)) a

/-- The zero exponent gives the exact natural endpoint one. -/
theorem powerRootCeilEndpoint_zero (Y : ℕ) :
    powerRootCeilEndpoint Y 0 = 1 := by
  simp [powerRootCeilEndpoint]

/-- At a scale at least one, upward-rounded power endpoints are monotone in
their real exponent. -/
theorem powerRootCeilEndpoint_mono {Y : ℕ} (hY : 1 ≤ Y) :
    Monotone (powerRootCeilEndpoint Y) := by
  intro a b hab
  apply Nat.ceil_le_ceil
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hY) hab

/-- For a nonnegative root exponent, the ceiling endpoint costs at most a
factor of two.  This is the raw rounding estimate before that factor is
absorbed into an exponent slack. -/
theorem powerRootCeilEndpoint_le_two_rpow
    {Y : ℕ} (hY : 1 ≤ Y) {b : ℝ} (hb : 0 ≤ b) :
    (powerRootCeilEndpoint Y b : ℝ) ≤ 2 * (Y : ℝ) ^ b := by
  have hpowone : 1 ≤ (Y : ℝ) ^ b :=
    Real.one_le_rpow (by exact_mod_cast hY) hb
  calc
    (powerRootCeilEndpoint Y b : ℝ) ≤ (Y : ℝ) ^ b + 1 :=
      (powerRootCeilEndpoint_lt_rpow_add_one Y b).le
    _ ≤ 2 * (Y : ℝ) ^ b := by linarith

/-- A factor two in front of an arbitrary real power is absorbed by a stated
positive-power factor.  The explicit hypothesis is the finite-scale form of
the eventual inequality supplied by a positive exponent slack. -/
theorem two_mul_rpow_le_rpow_add_slack
    {Y : ℕ} (hY : 1 ≤ Y) (x eta : ℝ)
    (hslack : 2 ≤ (Y : ℝ) ^ eta) :
    2 * (Y : ℝ) ^ x ≤ (Y : ℝ) ^ (x + eta) := by
  have hYpos : 0 < (Y : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hY)
  calc
    2 * (Y : ℝ) ^ x = (Y : ℝ) ^ x * 2 := by ring
    _ ≤ (Y : ℝ) ^ x * (Y : ℝ) ^ eta :=
      mul_le_mul_of_nonneg_left hslack (Real.rpow_nonneg (Nat.cast_nonneg Y) x)
    _ = (Y : ℝ) ^ (x + eta) := (Real.rpow_add hYpos x eta).symm

/-- A strictly positive exponent slack eventually supplies the explicit
factor-two inequality used by the rounded endpoint estimates. -/
theorem eventually_two_le_rpow_of_pos {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ Y : ℕ in atTop, 2 ≤ (Y : ℝ) ^ eta := by
  have htend : Tendsto (fun Y : ℕ => (Y : ℝ) ^ eta) atTop atTop :=
    (tendsto_rpow_atTop heta).comp tendsto_natCast_atTop_atTop
  exact htend.eventually (eventually_ge_atTop 2)

/-- A ceiling endpoint is bounded by the same real power with a slack
exponent, once that slack absorbs the rounding factor two. -/
theorem powerRootCeilEndpoint_le_rpow_add_slack
    {Y : ℕ} (hY : 1 ≤ Y) {b eta : ℝ} (hb : 0 ≤ b)
    (hslack : 2 ≤ (Y : ℝ) ^ eta) :
    (powerRootCeilEndpoint Y b : ℝ) ≤ (Y : ℝ) ^ (b + eta) := by
  exact (powerRootCeilEndpoint_le_two_rpow hY hb).trans
    (two_mul_rpow_le_rpow_add_slack hY b eta hslack)

/-- The exact height-budget interface for a ceiling upper endpoint.  The
buffered exponent `b + eta` must fit in the height budget; no claim is made
that this happens without parameter slack. -/
theorem powerRootCeilEndpoint_height_budget_of_slack
    {Y : ℕ} (hY : 1 ≤ Y) {b eta phi theta : ℝ}
    (hb : 0 ≤ b) (hphi : 0 ≤ phi)
    (hslack : 2 ≤ (Y : ℝ) ^ eta)
    (hbudget : 2 * phi * (b + eta) ≤ phi - theta) :
    (powerRootCeilEndpoint Y b : ℝ) ^ (2 * phi) ≤
      (Y : ℝ) ^ (phi - theta) := by
  have hYnonneg : 0 ≤ (Y : ℝ) := Nat.cast_nonneg Y
  have hroot : (powerRootCeilEndpoint Y b : ℝ) ≤ (Y : ℝ) ^ (b + eta) :=
    powerRootCeilEndpoint_le_rpow_add_slack hY hb hslack
  have hpow : 0 ≤ 2 * phi := mul_nonneg (by norm_num) hphi
  have hexponent : (b + eta) * (2 * phi) ≤ phi - theta := by
    calc
      (b + eta) * (2 * phi) = 2 * phi * (b + eta) := by ring
      _ ≤ phi - theta := hbudget
  calc
    (powerRootCeilEndpoint Y b : ℝ) ^ (2 * phi) ≤
        ((Y : ℝ) ^ (b + eta)) ^ (2 * phi) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hroot hpow
    _ = (Y : ℝ) ^ ((b + eta) * (2 * phi)) := by
      rw [← Real.rpow_mul hYnonneg]
    _ ≤ (Y : ℝ) ^ (phi - theta) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hY) hexponent

/-- The exact cardinality factor in a closed root band is at most its upper
ceiling endpoint whenever the lower endpoint is a positive root-scale
endpoint. -/
theorem powerRootCeilBand_width_le_upper
    {Y : ℕ} (hY : 1 ≤ Y) (a b : ℝ) :
    ((powerRootCeilEndpoint Y b - powerRootCeilEndpoint Y a + 1 : ℕ) : ℝ) ≤
      (powerRootCeilEndpoint Y b : ℝ) := by
  have hlower : 1 ≤ powerRootCeilEndpoint Y a :=
    one_le_powerRootCeilEndpoint hY a
  have hupper : 1 ≤ powerRootCeilEndpoint Y b :=
    one_le_powerRootCeilEndpoint hY b
  have hwidth : powerRootCeilEndpoint Y b - powerRootCeilEndpoint Y a + 1 ≤
      powerRootCeilEndpoint Y b := by
    calc
      powerRootCeilEndpoint Y b - powerRootCeilEndpoint Y a + 1 ≤
          powerRootCeilEndpoint Y b - 1 + 1 :=
        Nat.add_le_add_right (Nat.sub_le_sub_left hlower _) _
      _ = powerRootCeilEndpoint Y b := Nat.sub_add_cancel hupper
  exact_mod_cast hwidth

/-- The closed-band cardinality factor is controlled by the buffered upper
exponent.  This is directly compatible with the root-count factor in
`FiniteRootBandBound`. -/
theorem powerRootCeilBand_width_le_rpow_add_slack
    {Y : ℕ} (hY : 1 ≤ Y) (a : ℝ) {b eta : ℝ} (hb : 0 ≤ b)
    (hslack : 2 ≤ (Y : ℝ) ^ eta) :
    ((powerRootCeilEndpoint Y b - powerRootCeilEndpoint Y a + 1 : ℕ) : ℝ) ≤
      (Y : ℝ) ^ (b + eta) := by
  exact (powerRootCeilBand_width_le_upper hY a b).trans
    (powerRootCeilEndpoint_le_rpow_add_slack hY hb hslack)

/-- The scaled natural cutoff at a ceiling lower endpoint has the expected
real-power size, with only the explicit factor two from the dyadic upper
edge. -/
theorem scaledCutoff_at_powerRootCeilEndpoint_le_two_rpow
    {Y : ℕ} (hY : 1 ≤ Y) (a : ℝ) :
    (((2 * Y - 1) / (powerRootCeilEndpoint Y a) ^ 2 : ℕ) : ℝ) ≤
      2 * (Y : ℝ) ^ (1 - 2 * a) := by
  let L : ℕ := powerRootCeilEndpoint Y a
  have hYpos : 0 < (Y : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hY)
  have hLpos : 0 < (L : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one
      (one_le_powerRootCeilEndpoint hY a))
  have hnum : ((2 * Y - 1 : ℕ) : ℝ) ≤ 2 * (Y : ℝ) := by
    exact_mod_cast Nat.sub_le (2 * Y) 1
  have hroot : (Y : ℝ) ^ a ≤ (L : ℝ) := by
    simpa [L] using rpow_le_powerRootCeilEndpoint Y a
  have hsquare : (Y : ℝ) ^ (2 * a) ≤ (L : ℝ) ^ 2 := by
    have hmul := mul_self_le_mul_self
      (Real.rpow_nonneg (Nat.cast_nonneg Y) a) hroot
    calc
      (Y : ℝ) ^ (2 * a) = (Y : ℝ) ^ a * (Y : ℝ) ^ a := by
        rw [show 2 * a = a + a by ring, Real.rpow_add hYpos]
      _ ≤ (L : ℝ) * (L : ℝ) := hmul
      _ = (L : ℝ) ^ 2 := by ring
  calc
    (((2 * Y - 1) / (powerRootCeilEndpoint Y a) ^ 2 : ℕ) : ℝ) ≤
        ((2 * Y - 1 : ℕ) : ℝ) /
          (((powerRootCeilEndpoint Y a) ^ 2 : ℕ) : ℝ) :=
      Nat.cast_div_le
    _ = ((2 * Y - 1 : ℕ) : ℝ) / (L : ℝ) ^ 2 := by
      simp [L, Nat.cast_pow]
    _ ≤ (2 * (Y : ℝ)) / (L : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hnum (sq_nonneg (L : ℝ))
    _ ≤ (2 * (Y : ℝ)) / (Y : ℝ) ^ (2 * a) :=
      div_le_div_of_nonneg_left (by positivity)
        (Real.rpow_pos_of_pos hYpos _) hsquare
    _ = 2 * (Y : ℝ) ^ (1 - 2 * a) := by
      rw [Real.rpow_sub hYpos, Real.rpow_one]
      ring

/-- The scaled cutoff is controlled by a buffered exponent once the same
factor-two slack is available.  This is the endpoint inequality normally
combined with the `1 - d` power in `FiniteRootBandBound`. -/
theorem scaledCutoff_at_powerRootCeilEndpoint_le_rpow_add_slack
    {Y : ℕ} (hY : 1 ≤ Y) (a eta : ℝ)
    (hslack : 2 ≤ (Y : ℝ) ^ eta) :
    (((2 * Y - 1) / (powerRootCeilEndpoint Y a) ^ 2 : ℕ) : ℝ) ≤
      (Y : ℝ) ^ (1 - 2 * a + eta) := by
  exact (scaledCutoff_at_powerRootCeilEndpoint_le_two_rpow hY a).trans
    (two_mul_rpow_le_rpow_add_slack hY (1 - 2 * a) eta hslack)

/-- Raising the rounded scaled cutoff to the nonnegative fixed-height power
preserves the buffered real-power bound. -/
theorem scaledCutoff_at_powerRootCeilEndpoint_rpow_le_rpow_add_slack
    {Y : ℕ} (hY : 1 ≤ Y) (a eta d : ℝ) (hd : d ≤ 1)
    (hslack : 2 ≤ (Y : ℝ) ^ eta) :
    ((((2 * Y - 1) / (powerRootCeilEndpoint Y a) ^ 2 : ℕ) : ℝ) ^ (1 - d)) ≤
      (Y : ℝ) ^ ((1 - 2 * a + eta) * (1 - d)) := by
  have hcutoff :=
    scaledCutoff_at_powerRootCeilEndpoint_le_rpow_add_slack hY a eta hslack
  have hpower : 0 ≤ 1 - d := sub_nonneg.mpr hd
  calc
    ((((2 * Y - 1) / (powerRootCeilEndpoint Y a) ^ 2 : ℕ) : ℝ) ^ (1 - d)) ≤
        ((Y : ℝ) ^ (1 - 2 * a + eta)) ^ (1 - d) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hcutoff hpower
    _ = (Y : ℝ) ^ ((1 - 2 * a + eta) * (1 - d)) := by
      rw [← Real.rpow_mul (Nat.cast_nonneg Y)]

/-- The exponent paid by a rounded physical root band: one upper-endpoint
slack and one cutoff slack are recorded separately. -/
noncomputable def roundedRootBandExponent
    (a b d etaUpper etaCutoff : ℝ) : ℝ :=
  (b + etaUpper) + (1 - 2 * a + etaCutoff) * (1 - d)

/-- The rounded exponent is the ideal scalar band exponent plus exactly the
two rounding slacks. -/
theorem roundedRootBandExponent_eq_rootBandExponent_add_slacks
    (a b d etaUpper etaCutoff : ℝ) :
    roundedRootBandExponent a b d etaUpper etaCutoff =
      rootBandExponent a b d + etaUpper + etaCutoff * (1 - d) := by
  unfold roundedRootBandExponent rootBandExponent
  ring

/-- If the same nonnegative slack is used at both endpoints, its total
contribution is at most `2 * rho` whenever the fixed-height saving exponent
is nonnegative. -/
theorem roundedRootBandExponent_same_slack_le_rootBandExponent_add_two_mul
    (a b d rho : ℝ) (hrho : 0 ≤ rho) (hd : 0 ≤ d) :
    roundedRootBandExponent a b d rho rho ≤
      rootBandExponent a b d + 2 * rho := by
  rw [roundedRootBandExponent_eq_rootBandExponent_add_slacks]
  have hfactor : 1 - d ≤ 1 := by linarith
  have hproduct : rho * (1 - d) ≤ rho * 1 :=
    mul_le_mul_of_nonneg_left hfactor hrho
  linarith

/-- Combining the two endpoint bounds gives a direct upper bound for the
root-count/cutoff cost appearing in `FiniteRootBandBound`.  The coefficient
is kept outside the exponent, so this theorem does not select parameters or
claim a power saving. -/
theorem roundedPowerRootBandCost_le
    {Y : ℕ} (hY : 1 ≤ Y) (a : ℝ)
    {b etaUpper etaCutoff d C : ℝ} (hb : 0 ≤ b) (hd : d ≤ 1) (hC : 0 ≤ C)
    (hupperSlack : 2 ≤ (Y : ℝ) ^ etaUpper)
    (hcutoffSlack : 2 ≤ (Y : ℝ) ^ etaCutoff) :
    ((powerRootCeilEndpoint Y b - powerRootCeilEndpoint Y a + 1 : ℕ) : ℝ) * C *
        ((((2 * Y - 1) / (powerRootCeilEndpoint Y a) ^ 2 : ℕ) : ℝ) ^ (1 - d)) ≤
      C * (Y : ℝ) ^ roundedRootBandExponent a b d etaUpper etaCutoff := by
  have hwidth :=
    powerRootCeilBand_width_le_rpow_add_slack hY a hb hupperSlack
  have hcutoff :=
    scaledCutoff_at_powerRootCeilEndpoint_rpow_le_rpow_add_slack
      hY a etaCutoff d hd hcutoffSlack
  have hproduct :
      ((powerRootCeilEndpoint Y b - powerRootCeilEndpoint Y a + 1 : ℕ) : ℝ) *
          ((((2 * Y - 1) / (powerRootCeilEndpoint Y a) ^ 2 : ℕ) : ℝ) ^ (1 - d)) ≤
        (Y : ℝ) ^ (b + etaUpper) *
          (Y : ℝ) ^ ((1 - 2 * a + etaCutoff) * (1 - d)) :=
    mul_le_mul hwidth hcutoff
      (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hYpos : 0 < (Y : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hY)
  calc
    ((powerRootCeilEndpoint Y b - powerRootCeilEndpoint Y a + 1 : ℕ) : ℝ) * C *
        ((((2 * Y - 1) / (powerRootCeilEndpoint Y a) ^ 2 : ℕ) : ℝ) ^ (1 - d)) =
      C * (((powerRootCeilEndpoint Y b - powerRootCeilEndpoint Y a + 1 : ℕ) : ℝ) *
        ((((2 * Y - 1) / (powerRootCeilEndpoint Y a) ^ 2 : ℕ) : ℝ) ^ (1 - d))) := by
          ring
    _ ≤ C * ((Y : ℝ) ^ (b + etaUpper) *
        (Y : ℝ) ^ ((1 - 2 * a + etaCutoff) * (1 - d))) :=
      mul_le_mul_of_nonneg_left hproduct hC
    _ = C * (Y : ℝ) ^ ((b + etaUpper) +
        (1 - 2 * a + etaCutoff) * (1 - d)) := by
      have hrpow :
          (Y : ℝ) ^ ((b + etaUpper) +
            (1 - 2 * a + etaCutoff) * (1 - d)) =
            (Y : ℝ) ^ (b + etaUpper) *
              (Y : ℝ) ^ ((1 - 2 * a + etaCutoff) * (1 - d)) :=
        Real.rpow_add hYpos _ _
      rw [hrpow]
    _ = C * (Y : ℝ) ^ roundedRootBandExponent a b d etaUpper etaCutoff := by
      rfl

/-- A generic finite chain of adjacent closed natural intervals covers its
entire endpoint interval.  The first endpoint is included in the first band,
so there is one band even when `n = 0`. -/
theorem Icc_subset_biUnion_adjacentIntervals
    (q : ℕ → ℕ) (hzero : q 0 = 1) (n : ℕ) :
    Finset.Icc 1 (q (n + 1)) ⊆
      (Finset.range (n + 1)).biUnion fun i => Finset.Icc (q i) (q (i + 1)) := by
  induction n with
  | zero =>
      intro s hs
      refine Finset.mem_biUnion.mpr ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
      simpa [hzero] using hs
  | succ n ih =>
      intro s hs
      by_cases hsle : s ≤ q (n + 1)
      · obtain ⟨i, hi, hband⟩ := Finset.mem_biUnion.mp
          (ih (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hs).1, hsle⟩))
        refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr ?_, hband⟩
        exact (Finset.mem_range.mp hi).trans (by omega)
      · refine Finset.mem_biUnion.mpr ⟨n + 1, Finset.mem_range.mpr (by omega), ?_⟩
        exact Finset.mem_Icc.mpr
          ⟨Nat.le_of_lt (lt_of_not_ge hsle), (Finset.mem_Icc.mp hs).2⟩

/-- Adjacent ceiling endpoints of a monotone real-exponent sequence cover
the full natural range through the last endpoint. -/
theorem Icc_subset_biUnion_powerRootCeilBand
    {Y : ℕ} (a : ℕ → ℝ) (hzero : a 0 = 0) (n : ℕ) :
    Finset.Icc 1 (powerRootCeilEndpoint Y (a (n + 1))) ⊆
      (Finset.range (n + 1)).biUnion (powerRootCeilBand Y a) := by
  let q : ℕ → ℕ := fun i => powerRootCeilEndpoint Y (a i)
  have hqzero : q 0 = 1 := by
    simp [q, hzero, powerRootCeilEndpoint_zero]
  change Finset.Icc 1 (q (n + 1)) ⊆
    (Finset.range (n + 1)).biUnion fun i => Finset.Icc (q i) (q (i + 1))
  exact Icc_subset_biUnion_adjacentIntervals q hqzero n

/-- For an increasing exponent sequence, every adjacent ceiling band has its
lower endpoint below its upper endpoint.  This is the interval hypothesis
required by `FiniteRootBandBound`. -/
theorem powerRootCeilBand_lower_le_upper
    {Y : ℕ} (hY : 1 ≤ Y) (a : ℕ → ℝ) (hmono : Monotone a) (i : ℕ) :
    powerRootCeilEndpoint Y (a i) ≤ powerRootCeilEndpoint Y (a (i + 1)) := by
  exact powerRootCeilEndpoint_mono hY (hmono (Nat.le_succ i))

/-- The finite adjacent ceiling bands are packaged as a `FiniteRootBandCover`.
The exponent sequence is infinite only for convenience of indexing; this
definition uses exactly its first `n + 2` values. -/
noncomputable def powerRootCeilBandCover
    (Y : ℕ) (a : ℕ → ℝ) (n : ℕ)
    (hzero : a 0 = 0) :
    FiniteRootBandCover (powerRootCeilEndpoint Y (a (n + 1)) + 1) where
  bandCount := n + 1
  lower := fun i => powerRootCeilEndpoint Y (a i)
  upper := fun i => powerRootCeilEndpoint Y (a (i + 1))
  covers := by
    intro s hs
    change s ∈ Finset.Ico 1 (powerRootCeilEndpoint Y (a (n + 1)) + 1) at hs
    have hs' : s ∈ Finset.Icc 1 (powerRootCeilEndpoint Y (a (n + 1))) :=
      Finset.mem_Icc.mpr ⟨(Finset.mem_Ico.mp hs).1, by
        exact Nat.le_of_lt_succ (Finset.mem_Ico.mp hs).2⟩
    obtain ⟨i, hi, hband⟩ :=
      Finset.mem_biUnion.mp
        (Icc_subset_biUnion_powerRootCeilBand a hzero n hs')
    refine Finset.mem_biUnion.mpr
      ⟨⟨i, Finset.mem_range.mp hi⟩, Finset.mem_univ _, ?_⟩
    change s ∈ Finset.Icc (powerRootCeilEndpoint Y (a i))
      (powerRootCeilEndpoint Y (a (i + 1))) at hband
    exact hband

end PellPaper
