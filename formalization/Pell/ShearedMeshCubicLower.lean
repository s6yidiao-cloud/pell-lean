import Pell.UniformMeshRiemannLower
import Pell.GeneralBidegreePositiveRealWeightedSharpTwoRegime
import Pell.ShearedContinuousCubicIntegral

/-!
# A mesh-level two-regime cubic lower bound

This module makes the finite Riemann-sum step in the sheared determinant
argument explicit.  A pair of exactly aligned mesh intervals samples the
positive rank deficits on the triangular and shell regimes.  The two endpoint
cells cost at most `2 * rho * mesh`; the continuous contribution is the
exact cubic from `ShearedContinuousCubicIntegral`.

The rank-cap adapter below is intentionally separate from the normalized
cubic statement: lattice-boundary terms can be supplied as pointwise errors
without changing the mesh calculation.
-/

namespace PellPaper

open scoped BigOperators Interval
open Set MeasureTheory

noncomputable section

/-- The positive part of the triangular continuous rank deficit. -/
def shearedTriangularDeficit (rho m x lambda : ℝ) : ℝ :=
  max (rho - shearedTriangularCap m x lambda) 0

/-- The positive part of the parallel-line shell continuous rank deficit. -/
def shearedShellDeficit (rho m x lambda : ℝ) : ℝ :=
  max (rho - shearedShellCap rho m x lambda) 0

/-- On a nonnegative interval, the triangular positive-part deficit is
antitone. -/
theorem antitoneOn_shearedTriangularDeficit
    (rho m x L : ℝ) (hm : 0 < m) (hx : 0 < x) :
    AntitoneOn (shearedTriangularDeficit rho m x) (Icc 0 L) := by
  intro a ha b hb hab
  have hden : 0 < 2 * m * x := by positivity
  have hsq : a ^ 2 ≤ b ^ 2 :=
    (sq_le_sq₀ ha.1 hb.1).mpr hab
  have hcap : shearedTriangularCap m x a ≤ shearedTriangularCap m x b := by
    rw [shearedTriangularCap, shearedTriangularCap]
    exact (div_le_div_iff_of_pos_right hden).mpr hsq
  exact max_le_max_right 0 (sub_le_sub_left hcap rho)

/-- The shell positive-part deficit is antitone on the whole line. -/
theorem antitone_shearedShellDeficit
    (rho m x : ℝ) (hrho : 0 ≤ rho) (hm : 0 < m) :
    Antitone (shearedShellDeficit rho m x) := by
  intro a b hab
  have hslope : 0 ≤ rho / m := div_nonneg hrho hm.le
  have hlinear : (rho / m) * a ≤ (rho / m) * b :=
    mul_le_mul_of_nonneg_left hab hslope
  have hcap : shearedShellCap rho m x a ≤ shearedShellCap rho m x b := by
    rw [shearedShellCap, shearedShellCap]
    convert sub_le_sub_right hlinear (x * rho ^ 2 / (2 * m)) using 1 <;> ring
  exact max_le_max_right 0 (sub_le_sub_left hcap rho)

/-- A natural rank deficit dominates the positive real deficit attached to
any real upper bound for that rank. -/
theorem positivePart_sub_le_cast_natSub_of_rank_le
    {H r : ℕ} {cap : ℝ} (hrH : r ≤ H) (hrcap : (r : ℝ) ≤ cap) :
    max ((H : ℝ) - cap) 0 ≤ ((H - r : ℕ) : ℝ) := by
  have hrH_cast : (r : ℝ) ≤ (H : ℝ) := by exact_mod_cast hrH
  have hsub : (H : ℝ) - cap ≤ (H : ℝ) - (r : ℝ) :=
    sub_le_sub_left hrcap _
  have hzero : 0 ≤ (H : ℝ) - (r : ℝ) := sub_nonneg.mpr hrH_cast
  rw [Nat.cast_sub hrH]
  exact max_le hsub hzero

/-- The same deficit comparison with a nonnegative additive rank-cap error.
This is the form used when a lattice cap differs from its continuous main
term by an explicit boundary term. -/
theorem positivePart_sub_le_cast_natSub_add_error_of_rank_le
    {H r : ℕ} {cap error : ℝ} (hrH : r ≤ H) (herror : 0 ≤ error)
    (hrcap : (r : ℝ) ≤ cap + error) :
    max ((H : ℝ) - cap) 0 ≤ ((H - r : ℕ) : ℝ) + error := by
  have hrH_cast : (r : ℝ) ≤ (H : ℝ) := by exact_mod_cast hrH
  have hsub : (H : ℝ) - cap ≤ (H : ℝ) - (r : ℝ) + error := by
    linarith
  have hzero : 0 ≤ (H : ℝ) - (r : ℝ) + error :=
    add_nonneg (sub_nonneg.mpr hrH_cast) herror
  rw [Nat.cast_sub hrH]
  exact max_le hsub hzero

/-- The sharp real two-regime rank cap gives a positive-part lower bound for
the corresponding integral rank deficit, after clipping at the ambient
dimension `H`. -/
theorem sharpTwoRegime_rankDeficit_ge_positivePart
    (A B H : ℕ) (ellM ellX R : ℝ)
    (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX) (hR : 0 ≤ R)
    (hH : generalBidegreeCoefficientEvaluationRank A B
      (generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell) ≤ H) :
    max ((H : ℝ) -
      min
        (R ^ 2 / (2 * ellM * ellX) + R / ellM + R / ellX + 1)
        ((R / ellX + 1) *
          (((((A + 1 : ℕ) : ℝ) * ellX) / ellM) + 1))) 0 ≤
      ((H - generalBidegreeCoefficientEvaluationRank A B
        (generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell) : ℕ) : ℝ) := by
  apply positivePart_sub_le_cast_natSub_of_rank_le hH
  exact generalBidegreeCoefficientEvaluationRank_positiveRealWeightedBall_cast_le_sharpTwoRegimeAreaEnvelope
    A B ellM ellX R hellM_pos hell hR

/-- An exactly aligned pair of right Riemann sums captures the continuous
two-regime cubic, with the two literal endpoint corrections displayed. -/
theorem sheared_twoRegime_mesh_positivePart_sum_ge_cubic_sub_endpoints
    (rho m x mesh : ℝ) (Nlow Nhigh : ℕ)
    (hrho : 0 ≤ rho) (hm : 0 < m) (hx : 0 < x)
    (hshear : x * rho ≤ 2 * m) (hmesh : 0 < mesh)
    (hlow_align : (Nlow : ℝ) * mesh = x * rho)
    (hhigh_align : (Nhigh : ℝ) * mesh = m - x * rho / 2) :
    rho * m / 2 + x * rho ^ 2 / 2 - x ^ 2 * rho ^ 3 / (24 * m) -
        mesh *
          ((shearedTriangularDeficit rho m x 0 -
              shearedTriangularDeficit rho m x (x * rho)) +
            (shearedShellDeficit rho m x (x * rho) -
              shearedShellDeficit rho m x (m + x * rho / 2))) ≤
      mesh * ∑ n ∈ Finset.range Nlow,
          shearedTriangularDeficit rho m x (((n + 1 : ℕ) : ℝ) * mesh) +
        mesh * ∑ n ∈ Finset.range Nhigh,
          shearedShellDeficit rho m x
            (x * rho + ((n + 1 : ℕ) : ℝ) * mesh) := by
  let f : ℝ → ℝ := shearedTriangularDeficit rho m x
  have hlow := uniformMesh_rightRiemannSum_ge_integral_sub_endpoint
    f mesh Nlow hmesh (antitoneOn_shearedTriangularDeficit rho m x
      ((Nlow : ℝ) * mesh) hm hx)
  have hlow' :
      (∫ lambda in 0..x * rho, f lambda) -
          mesh * (f 0 - f (x * rho)) ≤
        mesh * ∑ n ∈ Finset.range Nlow,
          f (((n + 1 : ℕ) : ℝ) * mesh) := by
    simpa only [hlow_align] using hlow
  let g : ℝ → ℝ := fun t => shearedShellDeficit rho m x (x * rho + t)
  have hganti : AntitoneOn g (Icc 0 ((Nhigh : ℝ) * mesh)) := by
    intro a _ b _ hab
    apply antitone_shearedShellDeficit rho m x hrho hm
    linarith
  have hhigh := uniformMesh_rightRiemannSum_ge_integral_sub_endpoint
    g mesh Nhigh hmesh hganti
  have hhigh_integral :
      (∫ t in 0..(Nhigh : ℝ) * mesh, g t) =
        ∫ lambda in x * rho..m + x * rho / 2,
          shearedShellDeficit rho m x lambda := by
    change (∫ t in 0..(Nhigh : ℝ) * mesh,
      shearedShellDeficit rho m x (x * rho + t)) = _
    calc
      (∫ t in 0..(Nhigh : ℝ) * mesh,
          shearedShellDeficit rho m x (x * rho + t)) =
          ∫ lambda in x * rho + 0..x * rho + (Nhigh : ℝ) * mesh,
            shearedShellDeficit rho m x lambda :=
        intervalIntegral.integral_comp_add_left
          (shearedShellDeficit rho m x) (x * rho)
      _ = ∫ lambda in x * rho..m + x * rho / 2,
            shearedShellDeficit rho m x lambda := by
          rw [hhigh_align]
          ring_nf
  have hhigh' :
      (∫ lambda in x * rho..m + x * rho / 2,
          shearedShellDeficit rho m x lambda) -
          mesh * (shearedShellDeficit rho m x (x * rho) -
            shearedShellDeficit rho m x (m + x * rho / 2)) ≤
        mesh * ∑ n ∈ Finset.range Nhigh,
            shearedShellDeficit rho m x
            (x * rho + ((n + 1 : ℕ) : ℝ) * mesh) := by
    rw [← hhigh_integral]
    convert hhigh using 1
    all_goals simp only [g, hhigh_align]
    all_goals ring_nf
  have hcubic :
      (∫ lambda in 0..x * rho, f lambda) +
        (∫ lambda in x * rho..m + x * rho / 2,
          shearedShellDeficit rho m x lambda) =
        rho * m / 2 + x * rho ^ 2 / 2 - x ^ 2 * rho ^ 3 / (24 * m) := by
    simpa only [f, shearedTriangularDeficit, shearedShellDeficit] using
      (sheared_twoRegime_continuous_positivePart_integral_eq_cubic
        rho m x hrho hm hx hshear)
  change rho * m / 2 + x * rho ^ 2 / 2 - x ^ 2 * rho ^ 3 / (24 * m) -
      mesh * ((f 0 - f (x * rho)) +
        (shearedShellDeficit rho m x (x * rho) -
          shearedShellDeficit rho m x (m + x * rho / 2))) ≤ _
  linarith

/-- The endpoint corrections in the aligned two-regime mesh sum cost at
most two mesh cells.  Thus the cubic lower bound loses only
`2 * rho * mesh`. -/
theorem sheared_twoRegime_mesh_positivePart_sum_ge_cubic_sub_two_mesh
    (rho m x mesh : ℝ) (Nlow Nhigh : ℕ)
    (hrho : 0 ≤ rho) (hm : 0 < m) (hx : 0 < x)
    (hshear : x * rho ≤ 2 * m) (hmesh : 0 < mesh)
    (hlow_align : (Nlow : ℝ) * mesh = x * rho)
    (hhigh_align : (Nhigh : ℝ) * mesh = m - x * rho / 2) :
    rho * m / 2 + x * rho ^ 2 / 2 - x ^ 2 * rho ^ 3 / (24 * m) -
        2 * rho * mesh ≤
      mesh * ∑ n ∈ Finset.range Nlow,
          shearedTriangularDeficit rho m x (((n + 1 : ℕ) : ℝ) * mesh) +
        mesh * ∑ n ∈ Finset.range Nhigh,
          shearedShellDeficit rho m x
            (x * rho + ((n + 1 : ℕ) : ℝ) * mesh) := by
  have hexact := sheared_twoRegime_mesh_positivePart_sum_ge_cubic_sub_endpoints
    rho m x mesh Nlow Nhigh hrho hm hx hshear hmesh hlow_align hhigh_align
  have htri_zero : shearedTriangularDeficit rho m x 0 = rho := by
    simp [shearedTriangularDeficit, shearedTriangularCap, hrho]
  have htri_end_nonneg : 0 ≤ shearedTriangularDeficit rho m x (x * rho) :=
    le_max_right _ _
  have htri_loss : shearedTriangularDeficit rho m x 0 -
      shearedTriangularDeficit rho m x (x * rho) ≤ rho := by
    rw [htri_zero]
    linarith
  have hshell_cap_start : 0 ≤ shearedShellCap rho m x (x * rho) := by
    rw [shearedShellCap]
    have hid : rho * (x * rho) / m - x * rho ^ 2 / (2 * m) =
        x * rho ^ 2 / (2 * m) := by
      field_simp [hm.ne']
      ring
    rw [hid]
    positivity
  have hshell_start_le : shearedShellDeficit rho m x (x * rho) ≤ rho := by
    rw [shearedShellDeficit]
    apply max_le
    · linarith
    · exact hrho
  have hshell_end_nonneg :
      0 ≤ shearedShellDeficit rho m x (m + x * rho / 2) := le_max_right _ _
  have hshell_loss : shearedShellDeficit rho m x (x * rho) -
      shearedShellDeficit rho m x (m + x * rho / 2) ≤ rho := by
    linarith
  have htotal_loss :
      (shearedTriangularDeficit rho m x 0 -
          shearedTriangularDeficit rho m x (x * rho)) +
        (shearedShellDeficit rho m x (x * rho) -
          shearedShellDeficit rho m x (m + x * rho / 2)) ≤ 2 * rho := by
    linarith
  have hmesh_loss : mesh *
      ((shearedTriangularDeficit rho m x 0 -
          shearedTriangularDeficit rho m x (x * rho)) +
        (shearedShellDeficit rho m x (x * rho) -
          shearedShellDeficit rho m x (m + x * rho / 2))) ≤
      2 * rho * mesh := by
    calc
      mesh *
          ((shearedTriangularDeficit rho m x 0 -
              shearedTriangularDeficit rho m x (x * rho)) +
            (shearedShellDeficit rho m x (x * rho) -
              shearedShellDeficit rho m x (m + x * rho / 2))) ≤
          mesh * (2 * rho) :=
        mul_le_mul_of_nonneg_left htotal_loss hmesh.le
      _ = 2 * rho * mesh := by ring
  linarith

/-- A meshwise rank cap by the two continuous branches converts the preceding
positive-part estimate into a lower bound for literal natural rank deficits.
This is the direct finite interface for the sharp lattice-cap calculation;
any lattice-boundary normalization error belongs in the two cap hypotheses. -/
theorem sheared_twoRegime_mesh_rankDeficits_ge_cubic_sub_two_mesh
    (rho m x mesh : ℝ) (Nlow Nhigh H : ℕ) (rank : ℝ → ℕ)
    (hrho : 0 ≤ rho) (hm : 0 < m) (hx : 0 < x)
    (hshear : x * rho ≤ 2 * m) (hmesh : 0 < mesh)
    (hH : (H : ℝ) = rho)
    (hlow_align : (Nlow : ℝ) * mesh = x * rho)
    (hhigh_align : (Nhigh : ℝ) * mesh = m - x * rho / 2)
    (hrank_dim : ∀ R, rank R ≤ H)
    (hlow_cap : ∀ n ∈ Finset.range Nlow,
      (rank (((n + 1 : ℕ) : ℝ) * mesh) : ℝ) ≤
        shearedTriangularCap m x (((n + 1 : ℕ) : ℝ) * mesh))
    (hhigh_cap : ∀ n ∈ Finset.range Nhigh,
      (rank (x * rho + ((n + 1 : ℕ) : ℝ) * mesh) : ℝ) ≤
        shearedShellCap rho m x (x * rho + ((n + 1 : ℕ) : ℝ) * mesh)) :
    rho * m / 2 + x * rho ^ 2 / 2 - x ^ 2 * rho ^ 3 / (24 * m) -
        2 * rho * mesh ≤
      mesh * ∑ n ∈ Finset.range Nlow,
          ((H - rank (((n + 1 : ℕ) : ℝ) * mesh) : ℕ) : ℝ) +
        mesh * ∑ n ∈ Finset.range Nhigh,
          ((H - rank (x * rho + ((n + 1 : ℕ) : ℝ) * mesh) : ℕ) : ℝ) := by
  have hpositive := sheared_twoRegime_mesh_positivePart_sum_ge_cubic_sub_two_mesh
    rho m x mesh Nlow Nhigh hrho hm hx hshear hmesh hlow_align hhigh_align
  have hlow_sum :
      (∑ n ∈ Finset.range Nlow,
        shearedTriangularDeficit rho m x (((n + 1 : ℕ) : ℝ) * mesh)) ≤
      ∑ n ∈ Finset.range Nlow,
        ((H - rank (((n + 1 : ℕ) : ℝ) * mesh) : ℕ) : ℝ) := by
    apply Finset.sum_le_sum
    intro n hn
    have h := positivePart_sub_le_cast_natSub_of_rank_le
      (hrank_dim (((n + 1 : ℕ) : ℝ) * mesh)) (hlow_cap n hn)
    rw [hH] at h
    simpa only [shearedTriangularDeficit] using h
  have hhigh_sum :
      (∑ n ∈ Finset.range Nhigh,
        shearedShellDeficit rho m x
          (x * rho + ((n + 1 : ℕ) : ℝ) * mesh)) ≤
      ∑ n ∈ Finset.range Nhigh,
        ((H - rank (x * rho + ((n + 1 : ℕ) : ℝ) * mesh) : ℕ) : ℝ) := by
    apply Finset.sum_le_sum
    intro n hn
    have h := positivePart_sub_le_cast_natSub_of_rank_le
      (hrank_dim (x * rho + ((n + 1 : ℕ) : ℝ) * mesh)) (hhigh_cap n hn)
    rw [hH] at h
    simpa only [shearedShellDeficit] using h
  have hlow_scaled := mul_le_mul_of_nonneg_left hlow_sum hmesh.le
  have hhigh_scaled := mul_le_mul_of_nonneg_left hhigh_sum hmesh.le
  linarith

/-- The meshwise rank-deficit bound with explicit nonnegative lattice-boundary
errors at every mesh point.  Besides the two endpoint cells, the loss is
exactly the mesh times the displayed finite error sums. -/
theorem sheared_twoRegime_mesh_rankDeficits_ge_cubic_sub_errors
    (rho m x mesh : ℝ) (Nlow Nhigh H : ℕ) (rank : ℝ → ℕ)
    (errLow : ℕ → ℝ) (errHigh : ℕ → ℝ)
    (hrho : 0 ≤ rho) (hm : 0 < m) (hx : 0 < x)
    (hshear : x * rho ≤ 2 * m) (hmesh : 0 < mesh)
    (hH : (H : ℝ) = rho)
    (hlow_align : (Nlow : ℝ) * mesh = x * rho)
    (hhigh_align : (Nhigh : ℝ) * mesh = m - x * rho / 2)
    (hrank_dim : ∀ R, rank R ≤ H)
    (herr_low : ∀ n ∈ Finset.range Nlow, 0 ≤ errLow n)
    (herr_high : ∀ n ∈ Finset.range Nhigh, 0 ≤ errHigh n)
    (hlow_cap : ∀ n ∈ Finset.range Nlow,
      (rank (((n + 1 : ℕ) : ℝ) * mesh) : ℝ) ≤
        shearedTriangularCap m x (((n + 1 : ℕ) : ℝ) * mesh) + errLow n)
    (hhigh_cap : ∀ n ∈ Finset.range Nhigh,
      (rank (x * rho + ((n + 1 : ℕ) : ℝ) * mesh) : ℝ) ≤
        shearedShellCap rho m x (x * rho + ((n + 1 : ℕ) : ℝ) * mesh) +
          errHigh n) :
    rho * m / 2 + x * rho ^ 2 / 2 - x ^ 2 * rho ^ 3 / (24 * m) -
        2 * rho * mesh -
          mesh * (Finset.sum (Finset.range Nlow) errLow +
            Finset.sum (Finset.range Nhigh) errHigh) ≤
      mesh * ∑ n ∈ Finset.range Nlow,
          ((H - rank (((n + 1 : ℕ) : ℝ) * mesh) : ℕ) : ℝ) +
        mesh * ∑ n ∈ Finset.range Nhigh,
          ((H - rank (x * rho + ((n + 1 : ℕ) : ℝ) * mesh) : ℕ) : ℝ) := by
  have hpositive := sheared_twoRegime_mesh_positivePart_sum_ge_cubic_sub_two_mesh
    rho m x mesh Nlow Nhigh hrho hm hx hshear hmesh hlow_align hhigh_align
  have hlow_sum :
      (∑ n ∈ Finset.range Nlow,
        shearedTriangularDeficit rho m x (((n + 1 : ℕ) : ℝ) * mesh)) ≤
      (Finset.sum (Finset.range Nlow)
          (fun n => ((H - rank (((n + 1 : ℕ) : ℝ) * mesh) : ℕ) : ℝ))) +
        (Finset.sum (Finset.range Nlow) errLow) := by
    calc
      (∑ n ∈ Finset.range Nlow,
          shearedTriangularDeficit rho m x (((n + 1 : ℕ) : ℝ) * mesh)) ≤
          (Finset.sum (Finset.range Nlow) (fun n =>
            (((H - rank (((n + 1 : ℕ) : ℝ) * mesh) : ℕ) : ℝ) + errLow n))) := by
          apply Finset.sum_le_sum
          intro n hn
          have h := positivePart_sub_le_cast_natSub_add_error_of_rank_le
            (hrank_dim (((n + 1 : ℕ) : ℝ) * mesh)) (herr_low n hn)
              (hlow_cap n hn)
          rw [hH] at h
          simpa only [shearedTriangularDeficit] using h
      _ = (Finset.sum (Finset.range Nlow)
            (fun n => ((H - rank (((n + 1 : ℕ) : ℝ) * mesh) : ℕ) : ℝ))) +
          (Finset.sum (Finset.range Nlow) errLow) := by
          rw [Finset.sum_add_distrib]
  have hhigh_sum :
      (∑ n ∈ Finset.range Nhigh,
        shearedShellDeficit rho m x
          (x * rho + ((n + 1 : ℕ) : ℝ) * mesh)) ≤
      (Finset.sum (Finset.range Nhigh)
          (fun n => ((H - rank (x * rho + ((n + 1 : ℕ) : ℝ) * mesh) : ℕ) : ℝ))) +
        (Finset.sum (Finset.range Nhigh) errHigh) := by
    calc
      (∑ n ∈ Finset.range Nhigh,
          shearedShellDeficit rho m x
            (x * rho + ((n + 1 : ℕ) : ℝ) * mesh)) ≤
          (Finset.sum (Finset.range Nhigh) (fun n =>
            (((H - rank (x * rho + ((n + 1 : ℕ) : ℝ) * mesh) : ℕ) : ℝ) +
              errHigh n))) := by
          apply Finset.sum_le_sum
          intro n hn
          have h := positivePart_sub_le_cast_natSub_add_error_of_rank_le
            (hrank_dim (x * rho + ((n + 1 : ℕ) : ℝ) * mesh)) (herr_high n hn)
              (hhigh_cap n hn)
          rw [hH] at h
          simpa only [shearedShellDeficit] using h
      _ = (Finset.sum (Finset.range Nhigh)
            (fun n => ((H - rank (x * rho + ((n + 1 : ℕ) : ℝ) * mesh) : ℕ) : ℝ))) +
          (Finset.sum (Finset.range Nhigh) errHigh) := by
          rw [Finset.sum_add_distrib]
  have hlow_scaled := mul_le_mul_of_nonneg_left hlow_sum hmesh.le
  have hhigh_scaled := mul_le_mul_of_nonneg_left hhigh_sum hmesh.le
  linarith

end

end PellPaper
