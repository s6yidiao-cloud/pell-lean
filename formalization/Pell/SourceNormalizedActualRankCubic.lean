import Pell.SourceNormalizedShearedRankCaps
import Pell.SourceNormalizedShearedErrorSums
import Pell.ShearedMeshCubicScaledRank
import Pell.ShearedMeshCubicFlexibleEndpoint
import Pell.GeneralBidegreeActualRankWeightedFiltration
import Pell.GeneralBidegreeActualRankTaylorDecay
import Pell.GeneralBidegreeCoefficientRankAmbient

/-!
# The source-normalized cubic bound for literal coefficient ranks

This module composes the source-normalized triangular and shifted-shell caps
with the finite two-regime mesh calculation.  It uses the literal
coefficient-evaluation rank at every radius; no continuous rank envelope is
left as an input.

The mesh is `x / B` and its low block has `A` cells.  The source-ready
endpoint takes the high-cell count to be the natural floor of the terminal
shell length divided by this mesh, avoiding an irrational alignment
assumption; an exact-alignment comparison is retained as a reusable general
lemma.  All lattice-boundary errors remain finite sums of the explicit
normalized cap errors.
-/

namespace PellPaper

open scoped BigOperators Interval

noncomputable section

/-- The literal coefficient-rank deficit at a source-normalized radius
`lambda`, so that the underlying weighted-ball radius is `lambda * B * L`. -/
def sourceNormalizedActualPositiveBallRankDeficit
    (A B : ℕ) (m x L lambda : ℝ)
    (hm : 0 < m) (hmx : m ≤ x) (hL : 0 < L) : ℕ :=
  generalBidegreePositiveRealWeightedRankDeficit A B
    (Fintype.card (generalBidegreeGrid A B)) (m * L) (x * L)
    (lambda * (B : ℝ) * L) (mul_pos hm hL)
    (mul_le_mul_of_nonneg_right hmx hL.le)

/-- The mesh-scaled contiguous literal rank-deficit sum in the source's
normalized radius variable. -/
def sourceNormalizedScaledActualPositiveBallRankDeficits
    (A B : ℕ) (m x L mesh : ℝ)
    (hm : 0 < m) (hmx : m ≤ x) (hL : 0 < L) (Q : ℕ) : ℝ :=
  (∑ n ∈ Finset.range Q,
    (sourceNormalizedActualPositiveBallRankDeficit A B m x L
      (((n + 1 : ℕ) : ℝ) * mesh) hm hmx hL : ℝ)) * mesh

/-- The normalized scale `B^2` times `rho = A / B` fits in the full
coefficient grid. -/
theorem sourceNormalized_squareScale_mul_rho_le_gridCard
    (A B : ℕ) (hB : 0 < B) :
    (B : ℝ) ^ 2 * ((A : ℝ) / (B : ℝ)) ≤
      (Fintype.card (generalBidegreeGrid A B) : ℝ) := by
  have hB_real : 0 < (B : ℝ) := by exact_mod_cast hB
  have hmain : (B : ℝ) ^ 2 * ((A : ℝ) / (B : ℝ)) =
      (A : ℝ) * (B : ℝ) := by
    field_simp [ne_of_gt hB_real]
  rw [hmain]
  calc
    (A : ℝ) * (B : ℝ) ≤ ((A : ℝ) + 1) * ((B : ℝ) + 1) := by
      nlinarith [mul_nonneg (show 0 ≤ (A : ℝ) by positivity)
        (show 0 ≤ (B : ℝ) by positivity)]
    _ = (Fintype.card (generalBidegreeGrid A B) : ℝ) := by
      norm_num [Fintype.card_coe, card_generalBidegreeGrid, Nat.cast_mul,
        Nat.cast_add, Nat.cast_one]

/-- Exact finite reindexing of the source-normalized low and translated high
rank-deficit sums into one contiguous mesh sum. -/
theorem sum_sourceNormalizedActualPositiveBallRankDeficits_low_high_eq_contiguous
    (A B : ℕ) (m x L mesh rho : ℝ)
    (hm : 0 < m) (hmx : m ≤ x) (hL : 0 < L)
    (Nlow Nhigh : ℕ)
    (hlow_align : (Nlow : ℝ) * mesh = x * rho) :
    (∑ n ∈ Finset.range Nlow,
      (sourceNormalizedActualPositiveBallRankDeficit A B m x L
        (((n + 1 : ℕ) : ℝ) * mesh) hm hmx hL : ℝ)) +
      ∑ n ∈ Finset.range Nhigh,
        (sourceNormalizedActualPositiveBallRankDeficit A B m x L
          (x * rho + ((n + 1 : ℕ) : ℝ) * mesh) hm hmx hL : ℝ) =
      ∑ n ∈ Finset.range (Nlow + Nhigh),
        (sourceNormalizedActualPositiveBallRankDeficit A B m x L
          (((n + 1 : ℕ) : ℝ) * mesh) hm hmx hL : ℝ) := by
  let f : ℕ → ℝ := fun n =>
    (sourceNormalizedActualPositiveBallRankDeficit A B m x L
      (((n + 1 : ℕ) : ℝ) * mesh) hm hmx hL : ℝ)
  have hhigh :
      (∑ n ∈ Finset.range Nhigh,
        (sourceNormalizedActualPositiveBallRankDeficit A B m x L
          (x * rho + ((n + 1 : ℕ) : ℝ) * mesh) hm hmx hL : ℝ)) =
        ∑ n ∈ Finset.range Nhigh, f (Nlow + n) := by
    apply Finset.sum_congr rfl
    intro n _
    dsimp [f]
    rw [← hlow_align]
    push_cast
    ring_nf
  change (∑ n ∈ Finset.range Nlow, f n) +
      ∑ n ∈ Finset.range Nhigh,
        (sourceNormalizedActualPositiveBallRankDeficit A B m x L
          (x * rho + ((n + 1 : ℕ) : ℝ) * mesh) hm hmx hL : ℝ) =
      ∑ n ∈ Finset.range (Nlow + Nhigh), f n
  rw [hhigh]
  have hsplit := Finset.sum_range_add_sum_Ico f (Nat.le_add_right Nlow Nhigh)
  rw [Finset.sum_Ico_eq_sum_range] at hsplit
  simpa [Nat.add_sub_cancel_left] using hsplit

/-- At every source mesh point on the translated high branch, the shifted
radius is exactly `n * x * L`.  In particular, the sharp shifted cap is
available at every high point without an additional asymptotic hypothesis. -/
theorem sourceNormalized_highMesh_shift_radius_eq
    (A B n : ℕ) (x L : ℝ) (hB : 0 < B) :
    (x * ((A : ℝ) / (B : ℝ)) +
      ((n + 1 : ℕ) : ℝ) * (x / (B : ℝ))) * (B : ℝ) * L -
        ((A + 1 : ℕ) : ℝ) * (x * L) = (n : ℝ) * x * L := by
  have hB_real : 0 < (B : ℝ) := by exact_mod_cast hB
  norm_num [Nat.cast_add, Nat.cast_one]
  field_simp [ne_of_gt hB_real]
  ring

/-- The exact shifted-radius condition at all translated high mesh points. -/
theorem sourceNormalized_highMesh_shift_nonneg
    (A B n : ℕ) {x L : ℝ}
    (hB : 0 < B) (hx : 0 ≤ x) (hL : 0 ≤ L) :
    0 ≤ (x * ((A : ℝ) / (B : ℝ)) +
      ((n + 1 : ℕ) : ℝ) * (x / (B : ℝ))) * (B : ℝ) * L -
        ((A + 1 : ℕ) : ℝ) * (x * L) := by
  rw [sourceNormalized_highMesh_shift_radius_eq A B n x L hB]
  positivity

/-- Rescaling the source-normalized mesh by `B * L` gives exactly the
literal weighted-radius mesh `x * L` used by the determinant estimates. -/
theorem sourceNormalizedScaledActualPositiveBallRankDeficits_rescale_eq
    (A B : ℕ) (m x L : ℝ)
    (hB : 0 < B) (hm : 0 < m) (hmx : m ≤ x) (hL : 0 < L)
    (Q : ℕ) :
    (B : ℝ) * L *
        sourceNormalizedScaledActualPositiveBallRankDeficits A B m x L
          (x / (B : ℝ)) hm hmx hL Q =
      generalBidegreeScaledActualPositiveBallRankDeficits A B (m * L) (x * L)
        (x * L) (mul_pos hm hL) (mul_le_mul_of_nonneg_right hmx hL.le) Q := by
  have hB_real : 0 < (B : ℝ) := by exact_mod_cast hB
  have hradius (n : ℕ) :
      (((n + 1 : ℕ) : ℝ) * (x / (B : ℝ))) * (B : ℝ) * L =
        ((n + 1 : ℕ) : ℝ) * (x * L) := by
    field_simp [ne_of_gt hB_real]
  unfold sourceNormalizedScaledActualPositiveBallRankDeficits
    sourceNormalizedActualPositiveBallRankDeficit
    generalBidegreePositiveRealWeightedRankDeficit
    generalBidegreeScaledActualPositiveBallRankDeficits
  have hsum :
      (∑ n ∈ Finset.range Q,
        ((Fintype.card (generalBidegreeGrid A B) -
          generalBidegreeCoefficientEvaluationRank A B
            (generalBidegreePositiveRealWeightedBall (m * L) (x * L)
              ((((n + 1 : ℕ) : ℝ) * (x / (B : ℝ))) * (B : ℝ) * L)
              (mul_pos hm hL) (mul_le_mul_of_nonneg_right hmx hL.le)) : ℕ) : ℝ)) =
        ∑ n ∈ Finset.range Q,
          ((Fintype.card (generalBidegreeGrid A B) -
            generalBidegreeCoefficientEvaluationRank A B
              (generalBidegreePositiveRealWeightedBall (m * L) (x * L)
                (((n + 1 : ℕ) : ℝ) * (x * L))
                (mul_pos hm hL) (mul_le_mul_of_nonneg_right hmx hL.le)) : ℕ) : ℝ) := by
    apply Finset.sum_congr rfl
    intro n _
    rw [hradius n]
  rw [hsum]
  simp only [generalBidegreePositiveRealWeightedRankDeficit]
  field_simp [ne_of_gt hB_real]

/-- **Source-normalized actual-rank cubic bound.**  At mesh `x / B`, the
literal rank deficits over the first `A + Nhigh` cells dominate the cubic
gain supplied by the two sheared caps, minus the displayed finite sums of
lattice-boundary errors.  The high shifted-radius hypothesis is kept
pointwise, exactly as required by the shifted sharp cap. -/
theorem sourceNormalized_actualRankDeficits_ge_cubic_sub_errors
    (A B Nhigh : ℕ) (m x L : ℝ)
    (hB : 0 < B) (hm : 0 < m) (hmx : m ≤ x) (hL : 0 < L)
    (hshear : x * ((A : ℝ) / (B : ℝ)) ≤ 2 * m)
    (hhigh_align : (Nhigh : ℝ) * (x / (B : ℝ)) =
      m - x * ((A : ℝ) / (B : ℝ)) / 2)
    (hhigh_shift : ∀ n ∈ Finset.range Nhigh,
      0 ≤ (x * ((A : ℝ) / (B : ℝ)) +
        ((n + 1 : ℕ) : ℝ) * (x / (B : ℝ))) * (B : ℝ) * L -
          ((A + 1 : ℕ) : ℝ) * (x * L)) :
    (B : ℝ) ^ 2 *
        (((A : ℝ) / (B : ℝ)) * m / 2 +
          x * ((A : ℝ) / (B : ℝ)) ^ 2 / 2 -
          x ^ 2 * ((A : ℝ) / (B : ℝ)) ^ 3 / (24 * m) -
          2 * ((A : ℝ) / (B : ℝ)) * (x / (B : ℝ))) -
        (x / (B : ℝ)) *
          ((∑ n ∈ Finset.range A,
              sourceNormalizedTriangularCapError B m x
                (((n + 1 : ℕ) : ℝ) * (x / (B : ℝ)))) +
            ∑ n ∈ Finset.range Nhigh,
              sourceNormalizedShellCapError B m x
                (x * ((A : ℝ) / (B : ℝ)) +
                  ((n + 1 : ℕ) : ℝ) * (x / (B : ℝ)))) ≤
      sourceNormalizedScaledActualPositiveBallRankDeficits A B m x L
        (x / (B : ℝ)) hm hmx hL (A + Nhigh) := by
  let rho : ℝ := (A : ℝ) / (B : ℝ)
  let mesh : ℝ := x / (B : ℝ)
  let q : ℝ := (B : ℝ) ^ 2
  let rank : ℝ → ℕ := fun lambda =>
    generalBidegreeCoefficientEvaluationRank A B
      (generalBidegreePositiveRealWeightedBall (m * L) (x * L)
        (lambda * (B : ℝ) * L) (mul_pos hm hL)
        (mul_le_mul_of_nonneg_right hmx hL.le))
  let errLow : ℕ → ℝ := fun n =>
    sourceNormalizedTriangularCapError B m x
      (((n + 1 : ℕ) : ℝ) * mesh)
  let errHigh : ℕ → ℝ := fun n =>
    sourceNormalizedShellCapError B m x
      (x * rho + ((n + 1 : ℕ) : ℝ) * mesh)
  have hB_real : 0 < (B : ℝ) := by exact_mod_cast hB
  have hx : 0 < x := hm.trans_le hmx
  have hrho : 0 ≤ rho := by
    dsimp [rho]
    positivity
  have hmesh : 0 < mesh := by
    dsimp [mesh]
    exact div_pos hx hB_real
  have hq : 0 ≤ q := by
    dsimp [q]
    positivity
  have hambient : q * rho ≤
      (Fintype.card (generalBidegreeGrid A B) : ℝ) := by
    dsimp [q, rho]
    exact sourceNormalized_squareScale_mul_rho_le_gridCard A B hB
  have hlow_align : (A : ℝ) * mesh = x * rho := by
    dsimp [mesh, rho]
    exact sourceNormalized_lowMesh_alignment A B x hB
  have herr_low : ∀ n ∈ Finset.range A, 0 ≤ errLow n := by
    intro n _
    dsimp [errLow]
    apply sourceNormalizedTriangularCapError_nonneg B hB hm hx
    exact mul_nonneg (by positivity) hmesh.le
  have herr_high : ∀ n ∈ Finset.range Nhigh, 0 ≤ errHigh n := by
    intro n hn
    dsimp [errHigh, rho, mesh]
    exact sourceNormalizedShellCapError_nonneg_of_shift A B hB hm hx hL
      (hhigh_shift n hn)
  have hlow_cap : ∀ n ∈ Finset.range A,
      (rank (((n + 1 : ℕ) : ℝ) * mesh) : ℝ) ≤
        q * shearedTriangularCap m x (((n + 1 : ℕ) : ℝ) * mesh) + errLow n := by
    intro n _
    dsimp [rank, q, errLow]
    apply generalBidegreeCoefficientEvaluationRank_sourceNormalized_le_triangularCap
      A B m x (((n + 1 : ℕ) : ℝ) * mesh) L hB hm hmx hL
    exact mul_nonneg (by positivity) hmesh.le
  have hhigh_cap : ∀ n ∈ Finset.range Nhigh,
      (rank (x * rho + ((n + 1 : ℕ) : ℝ) * mesh) : ℝ) ≤
        q * shearedShellCap rho m x
          (x * rho + ((n + 1 : ℕ) : ℝ) * mesh) + errHigh n := by
    intro n hn
    dsimp [rank, q, errHigh]
    apply generalBidegreeCoefficientEvaluationRank_sourceNormalized_le_shellCap
      A B m x (x * rho + ((n + 1 : ℕ) : ℝ) * mesh) L hB hm hmx hL
    dsimp [rho, mesh]
    exact hhigh_shift n hn
  have hrank_dim : ∀ R, rank R ≤ Fintype.card (generalBidegreeGrid A B) := by
    intro R
    dsimp [rank]
    exact generalBidegreeCoefficientEvaluationRank_le_grid_card A B _
  have hscaled := sheared_twoRegime_mesh_scaledRankDeficits_ge_scaledCubic_sub_errors
    rho m x mesh q A Nhigh (Fintype.card (generalBidegreeGrid A B)) rank
      errLow errHigh hrho hm hx (by simpa [rho] using hshear) hmesh hq hambient
      hlow_align (by simpa [mesh, rho] using hhigh_align) hrank_dim herr_low herr_high
      hlow_cap hhigh_cap
  let lowSum : ℝ := ∑ n ∈ Finset.range A,
    (sourceNormalizedActualPositiveBallRankDeficit A B m x L
      (((n + 1 : ℕ) : ℝ) * mesh) hm hmx hL : ℝ)
  let highSum : ℝ := ∑ n ∈ Finset.range Nhigh,
    (sourceNormalizedActualPositiveBallRankDeficit A B m x L
      (x * rho + ((n + 1 : ℕ) : ℝ) * mesh) hm hmx hL : ℝ)
  let contiguousSum : ℝ := ∑ n ∈ Finset.range (A + Nhigh),
    (sourceNormalizedActualPositiveBallRankDeficit A B m x L
      (((n + 1 : ℕ) : ℝ) * mesh) hm hmx hL : ℝ)
  have hscaled' :
      q * (rho * m / 2 + x * rho ^ 2 / 2 - x ^ 2 * rho ^ 3 / (24 * m) -
        2 * rho * mesh) -
        mesh * (Finset.sum (Finset.range A) errLow +
          Finset.sum (Finset.range Nhigh) errHigh) ≤
      mesh * lowSum + mesh * highSum := by
    simpa only [rank, lowSum, highSum,
      sourceNormalizedActualPositiveBallRankDeficit,
      generalBidegreePositiveRealWeightedRankDeficit] using hscaled
  have hcontiguous : lowSum + highSum = contiguousSum := by
    have hsplit :=
      sum_sourceNormalizedActualPositiveBallRankDeficits_low_high_eq_contiguous
        A B m x L mesh rho hm hmx hL A Nhigh hlow_align
    simpa only [lowSum, highSum, contiguousSum] using hsplit
  calc
    (B : ℝ) ^ 2 *
        (((A : ℝ) / (B : ℝ)) * m / 2 +
          x * ((A : ℝ) / (B : ℝ)) ^ 2 / 2 -
          x ^ 2 * ((A : ℝ) / (B : ℝ)) ^ 3 / (24 * m) -
          2 * ((A : ℝ) / (B : ℝ)) * (x / (B : ℝ))) -
        (x / (B : ℝ)) *
          ((∑ n ∈ Finset.range A,
              sourceNormalizedTriangularCapError B m x
                (((n + 1 : ℕ) : ℝ) * (x / (B : ℝ)))) +
            ∑ n ∈ Finset.range Nhigh,
              sourceNormalizedShellCapError B m x
                (x * ((A : ℝ) / (B : ℝ)) +
                  ((n + 1 : ℕ) : ℝ) * (x / (B : ℝ)))) ≤
        q * (rho * m / 2 + x * rho ^ 2 / 2 - x ^ 2 * rho ^ 3 / (24 * m) -
          2 * rho * mesh) -
          mesh * (Finset.sum (Finset.range A) errLow +
            Finset.sum (Finset.range Nhigh) errHigh) := by
          rfl
    _ ≤ mesh * lowSum + mesh * highSum := hscaled'
    _ = (lowSum + highSum) * mesh := by ring
    _ = contiguousSum * mesh := by rw [hcontiguous]
    _ = sourceNormalizedScaledActualPositiveBallRankDeficits A B m x L
        (x / (B : ℝ)) hm hmx hL (A + Nhigh) := by
        rfl

/-- **Source-ready floor-endpoint cubic bound.**  The high mesh length is
chosen as the natural floor of its terminal real length, so this theorem has
no irrational exact-alignment assumption.  The resulting third mesh-cell
loss is explicit, and every high shifted-cap condition is discharged by the
mesh algebra. -/
theorem sourceNormalized_actualRankDeficits_ge_cubic_sub_three_mesh_floor
    (A B : ℕ) (m x L : ℝ)
    (hB : 0 < B) (hm : 0 < m) (hmx : m ≤ x) (hL : 0 < L)
    (hshear : x * ((A : ℝ) / (B : ℝ)) ≤ 2 * m) :
    (B : ℝ) ^ 2 *
        (((A : ℝ) / (B : ℝ)) * m / 2 +
          x * ((A : ℝ) / (B : ℝ)) ^ 2 / 2 -
          x ^ 2 * ((A : ℝ) / (B : ℝ)) ^ 3 / (24 * m) -
          3 * ((A : ℝ) / (B : ℝ)) * (x / (B : ℝ))) -
        (x / (B : ℝ)) *
          ((∑ n ∈ Finset.range A,
              sourceNormalizedTriangularCapError B m x
                (((n + 1 : ℕ) : ℝ) * (x / (B : ℝ)))) +
            ∑ n ∈ Finset.range
                ⌊(m - x * ((A : ℝ) / (B : ℝ)) / 2) / (x / (B : ℝ))⌋₊,
              sourceNormalizedShellCapError B m x
                (x * ((A : ℝ) / (B : ℝ)) +
                  ((n + 1 : ℕ) : ℝ) * (x / (B : ℝ)))) ≤
      sourceNormalizedScaledActualPositiveBallRankDeficits A B m x L
        (x / (B : ℝ)) hm hmx hL
        (A + ⌊(m - x * ((A : ℝ) / (B : ℝ)) / 2) / (x / (B : ℝ))⌋₊) := by
  let rho : ℝ := (A : ℝ) / (B : ℝ)
  let mesh : ℝ := x / (B : ℝ)
  let q : ℝ := (B : ℝ) ^ 2
  let Nhigh : ℕ := ⌊(m - x * rho / 2) / mesh⌋₊
  let rank : ℝ → ℕ := fun lambda =>
    generalBidegreeCoefficientEvaluationRank A B
      (generalBidegreePositiveRealWeightedBall (m * L) (x * L)
        (lambda * (B : ℝ) * L) (mul_pos hm hL)
        (mul_le_mul_of_nonneg_right hmx hL.le))
  let errLow : ℕ → ℝ := fun n =>
    sourceNormalizedTriangularCapError B m x
      (((n + 1 : ℕ) : ℝ) * mesh)
  let errHigh : ℕ → ℝ := fun n =>
    sourceNormalizedShellCapError B m x
      (x * rho + ((n + 1 : ℕ) : ℝ) * mesh)
  have hB_real : 0 < (B : ℝ) := by exact_mod_cast hB
  have hx : 0 < x := hm.trans_le hmx
  have hrho : 0 ≤ rho := by
    dsimp [rho]
    positivity
  have hmesh : 0 < mesh := by
    dsimp [mesh]
    exact div_pos hx hB_real
  have hq : 0 ≤ q := by
    dsimp [q]
    positivity
  have hambient : q * rho ≤
      (Fintype.card (generalBidegreeGrid A B) : ℝ) := by
    dsimp [q, rho]
    exact sourceNormalized_squareScale_mul_rho_le_gridCard A B hB
  have hlow_align : (A : ℝ) * mesh = x * rho := by
    dsimp [mesh, rho]
    exact sourceNormalized_lowMesh_alignment A B x hB
  have herr_low : ∀ n ∈ Finset.range A, 0 ≤ errLow n := by
    intro n _
    dsimp [errLow]
    apply sourceNormalizedTriangularCapError_nonneg B hB hm hx
    exact mul_nonneg (by positivity) hmesh.le
  have hhigh_shift : ∀ n ∈ Finset.range Nhigh,
      0 ≤ (x * rho + ((n + 1 : ℕ) : ℝ) * mesh) * (B : ℝ) * L -
        ((A + 1 : ℕ) : ℝ) * (x * L) := by
    intro n _
    simpa only [rho, mesh] using
      (sourceNormalized_highMesh_shift_nonneg A B n hB hx.le hL.le)
  have herr_high : ∀ n ∈ Finset.range Nhigh, 0 ≤ errHigh n := by
    intro n hn
    dsimp [errHigh]
    exact sourceNormalizedShellCapError_nonneg_of_shift A B hB hm hx hL
      (hhigh_shift n hn)
  have hlow_cap : ∀ n ∈ Finset.range A,
      (rank (((n + 1 : ℕ) : ℝ) * mesh) : ℝ) ≤
        q * shearedTriangularCap m x (((n + 1 : ℕ) : ℝ) * mesh) + errLow n := by
    intro n _
    dsimp [rank, q, errLow]
    apply generalBidegreeCoefficientEvaluationRank_sourceNormalized_le_triangularCap
      A B m x (((n + 1 : ℕ) : ℝ) * mesh) L hB hm hmx hL
    exact mul_nonneg (by positivity) hmesh.le
  have hhigh_cap : ∀ n ∈ Finset.range Nhigh,
      (rank (x * rho + ((n + 1 : ℕ) : ℝ) * mesh) : ℝ) ≤
        q * shearedShellCap rho m x
          (x * rho + ((n + 1 : ℕ) : ℝ) * mesh) + errHigh n := by
    intro n hn
    dsimp [rank, q, errHigh]
    apply generalBidegreeCoefficientEvaluationRank_sourceNormalized_le_shellCap
      A B m x (x * rho + ((n + 1 : ℕ) : ℝ) * mesh) L hB hm hmx hL
    exact hhigh_shift n hn
  have hrank_dim : ∀ R, rank R ≤ Fintype.card (generalBidegreeGrid A B) := by
    intro R
    dsimp [rank]
    exact generalBidegreeCoefficientEvaluationRank_le_grid_card A B _
  have hscaled :=
    sheared_twoRegime_mesh_scaledRankDeficits_ge_scaledCubic_sub_three_mesh_floor
      rho m x mesh q A (Fintype.card (generalBidegreeGrid A B)) rank
      errLow errHigh hrho hm hx (by simpa [rho] using hshear) hmesh hq hambient
      hlow_align hrank_dim (by simpa only [Nhigh] using herr_low)
      (by simpa only [Nhigh] using herr_high) hlow_cap
      (by simpa only [Nhigh] using hhigh_cap)
  let lowSum : ℝ := ∑ n ∈ Finset.range A,
    (sourceNormalizedActualPositiveBallRankDeficit A B m x L
      (((n + 1 : ℕ) : ℝ) * mesh) hm hmx hL : ℝ)
  let highSum : ℝ := ∑ n ∈ Finset.range Nhigh,
    (sourceNormalizedActualPositiveBallRankDeficit A B m x L
      (x * rho + ((n + 1 : ℕ) : ℝ) * mesh) hm hmx hL : ℝ)
  let contiguousSum : ℝ := ∑ n ∈ Finset.range (A + Nhigh),
    (sourceNormalizedActualPositiveBallRankDeficit A B m x L
      (((n + 1 : ℕ) : ℝ) * mesh) hm hmx hL : ℝ)
  have hscaled' :
      q * (rho * m / 2 + x * rho ^ 2 / 2 - x ^ 2 * rho ^ 3 / (24 * m) -
        3 * rho * mesh) -
        mesh * (Finset.sum (Finset.range A) errLow +
          Finset.sum (Finset.range Nhigh) errHigh) ≤
      mesh * lowSum + mesh * highSum := by
    simpa only [rank, lowSum, highSum,
      sourceNormalizedActualPositiveBallRankDeficit,
      generalBidegreePositiveRealWeightedRankDeficit, Nhigh] using hscaled
  have hcontiguous : lowSum + highSum = contiguousSum := by
    have hsplit :=
      sum_sourceNormalizedActualPositiveBallRankDeficits_low_high_eq_contiguous
        A B m x L mesh rho hm hmx hL A Nhigh hlow_align
    simpa only [lowSum, highSum, contiguousSum] using hsplit
  have hfinal :
      q * (rho * m / 2 + x * rho ^ 2 / 2 - x ^ 2 * rho ^ 3 / (24 * m) -
        3 * rho * mesh) -
        mesh * (Finset.sum (Finset.range A) errLow +
          Finset.sum (Finset.range Nhigh) errHigh) ≤
      sourceNormalizedScaledActualPositiveBallRankDeficits A B m x L mesh
        hm hmx hL (A + Nhigh) := by
    calc
      q * (rho * m / 2 + x * rho ^ 2 / 2 - x ^ 2 * rho ^ 3 / (24 * m) -
        3 * rho * mesh) -
          mesh * (Finset.sum (Finset.range A) errLow +
            Finset.sum (Finset.range Nhigh) errHigh) ≤
          mesh * lowSum + mesh * highSum := hscaled'
      _ = (lowSum + highSum) * mesh := by ring
      _ = contiguousSum * mesh := by rw [hcontiguous]
      _ = sourceNormalizedScaledActualPositiveBallRankDeficits A B m x L mesh
          hm hmx hL (A + Nhigh) := by rfl
  simpa only [rho, mesh, q, Nhigh, errLow, errHigh] using hfinal

/-- The floor-endpoint normalized cubic bound with its two finite boundary
error sums replaced by the explicit polynomial budget. -/
theorem sourceNormalized_actualRankDeficits_ge_cubic_sub_three_mesh_floor_polynomial
    (A B : ℕ) (m x L : ℝ)
    (hB : 0 < B) (hm : 0 < m) (hmx : m ≤ x) (hL : 0 < L)
    (hshear : x * ((A : ℝ) / (B : ℝ)) ≤ 2 * m) :
    (B : ℝ) ^ 2 *
        (((A : ℝ) / (B : ℝ)) * m / 2 +
          x * ((A : ℝ) / (B : ℝ)) ^ 2 / 2 -
          x ^ 2 * ((A : ℝ) / (B : ℝ)) ^ 3 / (24 * m) -
          3 * ((A : ℝ) / (B : ℝ)) * (x / (B : ℝ))) -
        (x / (B : ℝ)) *
          ((A : ℝ) * ((A : ℝ) * (x / m + 1) + 1) +
            (⌊(m - x * ((A : ℝ) / (B : ℝ)) / 2) / (x / (B : ℝ))⌋₊ : ℝ) *
              (((A : ℝ) +
                  (⌊(m - x * ((A : ℝ) / (B : ℝ)) / 2) /
                    (x / (B : ℝ))⌋₊ : ℝ)) * (3 * x / (2 * m) + 1) + 1)) ≤
      sourceNormalizedScaledActualPositiveBallRankDeficits A B m x L
        (x / (B : ℝ)) hm hmx hL
        (A + ⌊(m - x * ((A : ℝ) / (B : ℝ)) / 2) / (x / (B : ℝ))⌋₊) := by
  let Nhigh : ℕ :=
    ⌊(m - x * ((A : ℝ) / (B : ℝ)) / 2) / (x / (B : ℝ))⌋₊
  let core : ℝ :=
    (B : ℝ) ^ 2 *
      (((A : ℝ) / (B : ℝ)) * m / 2 +
        x * ((A : ℝ) / (B : ℝ)) ^ 2 / 2 -
        x ^ 2 * ((A : ℝ) / (B : ℝ)) ^ 3 / (24 * m) -
        3 * ((A : ℝ) / (B : ℝ)) * (x / (B : ℝ)))
  let exactError : ℝ :=
    (x / (B : ℝ)) *
      ((∑ n ∈ Finset.range A,
          sourceNormalizedTriangularCapError B m x
            (((n + 1 : ℕ) : ℝ) * (x / (B : ℝ)))) +
        ∑ n ∈ Finset.range Nhigh,
          sourceNormalizedShellCapError B m x
            (x * ((A : ℝ) / (B : ℝ)) +
              ((n + 1 : ℕ) : ℝ) * (x / (B : ℝ))))
  let polynomialError : ℝ :=
    (x / (B : ℝ)) *
      ((A : ℝ) * ((A : ℝ) * (x / m + 1) + 1) +
        (Nhigh : ℝ) *
          (((A : ℝ) + (Nhigh : ℝ)) * (3 * x / (2 * m) + 1) + 1))
  have hx : 0 < x := hm.trans_le hmx
  have hbase := sourceNormalized_actualRankDeficits_ge_cubic_sub_three_mesh_floor
    A B m x L hB hm hmx hL hshear
  have hbase' : core - exactError ≤
      sourceNormalizedScaledActualPositiveBallRankDeficits A B m x L
        (x / (B : ℝ)) hm hmx hL (A + Nhigh) := by
    simpa only [core, exactError, Nhigh] using hbase
  have herror := sourceNormalized_mesh_errorSum_le_polynomial
    A B Nhigh m x hB hm hx
  have herror' : exactError ≤ polynomialError := by
    simpa only [exactError, polynomialError] using herror
  have hresult : core - polynomialError ≤
      sourceNormalizedScaledActualPositiveBallRankDeficits A B m x L
        (x / (B : ℝ)) hm hmx hL (A + Nhigh) := by
    linarith
  simpa only [core, polynomialError, Nhigh] using hresult

/-- The determinant-side rescaling of the source-ready floor-endpoint cubic
bound.  Unlike the exact-endpoint variant, this applies to arbitrary real
source exponents: the final partial high cell is absorbed by the explicit
third mesh-cell loss. -/
theorem sourceNormalized_actualRadiusRankDeficits_ge_rescaledCubic_sub_three_mesh_floor
    (A B : ℕ) (m x L : ℝ)
    (hB : 0 < B) (hm : 0 < m) (hmx : m ≤ x) (hL : 0 < L)
    (hshear : x * ((A : ℝ) / (B : ℝ)) ≤ 2 * m) :
    (B : ℝ) * L *
      ((B : ℝ) ^ 2 *
          (((A : ℝ) / (B : ℝ)) * m / 2 +
            x * ((A : ℝ) / (B : ℝ)) ^ 2 / 2 -
            x ^ 2 * ((A : ℝ) / (B : ℝ)) ^ 3 / (24 * m) -
            3 * ((A : ℝ) / (B : ℝ)) * (x / (B : ℝ))) -
          (x / (B : ℝ)) *
            ((∑ n ∈ Finset.range A,
                sourceNormalizedTriangularCapError B m x
                  (((n + 1 : ℕ) : ℝ) * (x / (B : ℝ)))) +
              ∑ n ∈ Finset.range
                  ⌊(m - x * ((A : ℝ) / (B : ℝ)) / 2) / (x / (B : ℝ))⌋₊,
                sourceNormalizedShellCapError B m x
                  (x * ((A : ℝ) / (B : ℝ)) +
                    ((n + 1 : ℕ) : ℝ) * (x / (B : ℝ))))) ≤
      generalBidegreeScaledActualPositiveBallRankDeficits A B (m * L) (x * L)
        (x * L) (mul_pos hm hL) (mul_le_mul_of_nonneg_right hmx hL.le)
        (A + ⌊(m - x * ((A : ℝ) / (B : ℝ)) / 2) / (x / (B : ℝ))⌋₊) := by
  have hB_real : 0 < (B : ℝ) := by exact_mod_cast hB
  have hnormalized :=
    sourceNormalized_actualRankDeficits_ge_cubic_sub_three_mesh_floor
      A B m x L hB hm hmx hL hshear
  have hscaled := mul_le_mul_of_nonneg_left hnormalized
    (mul_pos hB_real hL).le
  calc
    (B : ℝ) * L *
        ((B : ℝ) ^ 2 *
            (((A : ℝ) / (B : ℝ)) * m / 2 +
              x * ((A : ℝ) / (B : ℝ)) ^ 2 / 2 -
              x ^ 2 * ((A : ℝ) / (B : ℝ)) ^ 3 / (24 * m) -
              3 * ((A : ℝ) / (B : ℝ)) * (x / (B : ℝ))) -
            (x / (B : ℝ)) *
              ((∑ n ∈ Finset.range A,
                  sourceNormalizedTriangularCapError B m x
                    (((n + 1 : ℕ) : ℝ) * (x / (B : ℝ)))) +
                ∑ n ∈ Finset.range
                    ⌊(m - x * ((A : ℝ) / (B : ℝ)) / 2) / (x / (B : ℝ))⌋₊,
                  sourceNormalizedShellCapError B m x
                    (x * ((A : ℝ) / (B : ℝ)) +
                      ((n + 1 : ℕ) : ℝ) * (x / (B : ℝ))))) ≤
        (B : ℝ) * L *
          sourceNormalizedScaledActualPositiveBallRankDeficits A B m x L
            (x / (B : ℝ)) hm hmx hL
            (A + ⌊(m - x * ((A : ℝ) / (B : ℝ)) / 2) / (x / (B : ℝ))⌋₊) := hscaled
    _ = generalBidegreeScaledActualPositiveBallRankDeficits A B (m * L) (x * L)
          (x * L) (mul_pos hm hL) (mul_le_mul_of_nonneg_right hmx hL.le)
          (A + ⌊(m - x * ((A : ℝ) / (B : ℝ)) / 2) / (x / (B : ℝ))⌋₊) :=
      sourceNormalizedScaledActualPositiveBallRankDeficits_rescale_eq
        A B m x L hB hm hmx hL
        (A + ⌊(m - x * ((A : ℝ) / (B : ℝ)) / 2) / (x / (B : ℝ))⌋₊)

/-- The determinant-side floor-endpoint cubic bound with the mesh boundary
errors replaced by the explicit polynomial budget. -/
theorem sourceNormalized_actualRadiusRankDeficits_ge_rescaledCubic_sub_three_mesh_floor_polynomial
    (A B : ℕ) (m x L : ℝ)
    (hB : 0 < B) (hm : 0 < m) (hmx : m ≤ x) (hL : 0 < L)
    (hshear : x * ((A : ℝ) / (B : ℝ)) ≤ 2 * m) :
    (B : ℝ) * L *
      ((B : ℝ) ^ 2 *
          (((A : ℝ) / (B : ℝ)) * m / 2 +
            x * ((A : ℝ) / (B : ℝ)) ^ 2 / 2 -
            x ^ 2 * ((A : ℝ) / (B : ℝ)) ^ 3 / (24 * m) -
            3 * ((A : ℝ) / (B : ℝ)) * (x / (B : ℝ))) -
          (x / (B : ℝ)) *
            ((A : ℝ) * ((A : ℝ) * (x / m + 1) + 1) +
              (⌊(m - x * ((A : ℝ) / (B : ℝ)) / 2) / (x / (B : ℝ))⌋₊ : ℝ) *
                (((A : ℝ) +
                    (⌊(m - x * ((A : ℝ) / (B : ℝ)) / 2) /
                      (x / (B : ℝ))⌋₊ : ℝ)) * (3 * x / (2 * m) + 1) + 1))) ≤
      generalBidegreeScaledActualPositiveBallRankDeficits A B (m * L) (x * L)
        (x * L) (mul_pos hm hL) (mul_le_mul_of_nonneg_right hmx hL.le)
        (A + ⌊(m - x * ((A : ℝ) / (B : ℝ)) / 2) / (x / (B : ℝ))⌋₊) := by
  have hB_real : 0 < (B : ℝ) := by exact_mod_cast hB
  have hnormalized :=
    sourceNormalized_actualRankDeficits_ge_cubic_sub_three_mesh_floor_polynomial
      A B m x L hB hm hmx hL hshear
  have hscaled := mul_le_mul_of_nonneg_left hnormalized
    (mul_pos hB_real hL).le
  calc
    (B : ℝ) * L *
        ((B : ℝ) ^ 2 *
            (((A : ℝ) / (B : ℝ)) * m / 2 +
              x * ((A : ℝ) / (B : ℝ)) ^ 2 / 2 -
              x ^ 2 * ((A : ℝ) / (B : ℝ)) ^ 3 / (24 * m) -
              3 * ((A : ℝ) / (B : ℝ)) * (x / (B : ℝ))) -
            (x / (B : ℝ)) *
              ((A : ℝ) * ((A : ℝ) * (x / m + 1) + 1) +
                (⌊(m - x * ((A : ℝ) / (B : ℝ)) / 2) /
                  (x / (B : ℝ))⌋₊ : ℝ) *
                  (((A : ℝ) +
                      (⌊(m - x * ((A : ℝ) / (B : ℝ)) / 2) /
                        (x / (B : ℝ))⌋₊ : ℝ)) * (3 * x / (2 * m) + 1) + 1))) ≤
        (B : ℝ) * L *
          sourceNormalizedScaledActualPositiveBallRankDeficits A B m x L
            (x / (B : ℝ)) hm hmx hL
            (A + ⌊(m - x * ((A : ℝ) / (B : ℝ)) / 2) / (x / (B : ℝ))⌋₊) := hscaled
    _ = generalBidegreeScaledActualPositiveBallRankDeficits A B (m * L) (x * L)
          (x * L) (mul_pos hm hL) (mul_le_mul_of_nonneg_right hmx hL.le)
          (A + ⌊(m - x * ((A : ℝ) / (B : ℝ)) / 2) / (x / (B : ℝ))⌋₊) :=
      sourceNormalizedScaledActualPositiveBallRankDeficits_rescale_eq
        A B m x L hB hm hmx hL
        (A + ⌊(m - x * ((A : ℝ) / (B : ℝ)) / 2) / (x / (B : ℝ))⌋₊)

/-- The determinant-side version of the source-normalized cubic bound.
Multiplication by `B * L` converts the normalized mesh `x / B` to the
literal weighted-radius mesh `x * L` used by the Taylor determinant decay. -/
theorem sourceNormalized_actualRadiusRankDeficits_ge_rescaledCubic_sub_errors
    (A B Nhigh : ℕ) (m x L : ℝ)
    (hB : 0 < B) (hm : 0 < m) (hmx : m ≤ x) (hL : 0 < L)
    (hshear : x * ((A : ℝ) / (B : ℝ)) ≤ 2 * m)
    (hhigh_align : (Nhigh : ℝ) * (x / (B : ℝ)) =
      m - x * ((A : ℝ) / (B : ℝ)) / 2)
    (hhigh_shift : ∀ n ∈ Finset.range Nhigh,
      0 ≤ (x * ((A : ℝ) / (B : ℝ)) +
        ((n + 1 : ℕ) : ℝ) * (x / (B : ℝ))) * (B : ℝ) * L -
          ((A + 1 : ℕ) : ℝ) * (x * L)) :
    (B : ℝ) * L *
      ((B : ℝ) ^ 2 *
          (((A : ℝ) / (B : ℝ)) * m / 2 +
            x * ((A : ℝ) / (B : ℝ)) ^ 2 / 2 -
            x ^ 2 * ((A : ℝ) / (B : ℝ)) ^ 3 / (24 * m) -
            2 * ((A : ℝ) / (B : ℝ)) * (x / (B : ℝ))) -
          (x / (B : ℝ)) *
            ((∑ n ∈ Finset.range A,
                sourceNormalizedTriangularCapError B m x
                  (((n + 1 : ℕ) : ℝ) * (x / (B : ℝ)))) +
              ∑ n ∈ Finset.range Nhigh,
                sourceNormalizedShellCapError B m x
                  (x * ((A : ℝ) / (B : ℝ)) +
                    ((n + 1 : ℕ) : ℝ) * (x / (B : ℝ))))) ≤
      generalBidegreeScaledActualPositiveBallRankDeficits A B (m * L) (x * L)
        (x * L) (mul_pos hm hL) (mul_le_mul_of_nonneg_right hmx hL.le)
        (A + Nhigh) := by
  have hB_real : 0 < (B : ℝ) := by exact_mod_cast hB
  have hnormalized := sourceNormalized_actualRankDeficits_ge_cubic_sub_errors
    A B Nhigh m x L hB hm hmx hL hshear hhigh_align hhigh_shift
  have hscaled := mul_le_mul_of_nonneg_left hnormalized
    (mul_pos hB_real hL).le
  calc
    (B : ℝ) * L *
      ((B : ℝ) ^ 2 *
          (((A : ℝ) / (B : ℝ)) * m / 2 +
            x * ((A : ℝ) / (B : ℝ)) ^ 2 / 2 -
            x ^ 2 * ((A : ℝ) / (B : ℝ)) ^ 3 / (24 * m) -
            2 * ((A : ℝ) / (B : ℝ)) * (x / (B : ℝ))) -
          (x / (B : ℝ)) *
            ((∑ n ∈ Finset.range A,
                sourceNormalizedTriangularCapError B m x
                  (((n + 1 : ℕ) : ℝ) * (x / (B : ℝ)))) +
              ∑ n ∈ Finset.range Nhigh,
                sourceNormalizedShellCapError B m x
                  (x * ((A : ℝ) / (B : ℝ)) +
                    ((n + 1 : ℕ) : ℝ) * (x / (B : ℝ))))) ≤
        (B : ℝ) * L *
          sourceNormalizedScaledActualPositiveBallRankDeficits A B m x L
            (x / (B : ℝ)) hm hmx hL (A + Nhigh) := hscaled
    _ = generalBidegreeScaledActualPositiveBallRankDeficits A B (m * L) (x * L)
          (x * L) (mul_pos hm hL) (mul_le_mul_of_nonneg_right hmx hL.le)
          (A + Nhigh) :=
      sourceNormalizedScaledActualPositiveBallRankDeficits_rescale_eq
        A B m x L hB hm hmx hL (A + Nhigh)

end

end PellPaper
