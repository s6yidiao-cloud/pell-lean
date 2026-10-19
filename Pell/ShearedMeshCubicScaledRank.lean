import Pell.ShearedMeshCubicLower

/-!
# A scaled finite-mesh cubic bound for literal natural ranks

The source rank has size on the order of `B^2`, whereas the continuous
two-regime caps are normalized by `B^2`.  This module is the exact finite
adapter between those normalizations.  It accepts natural rank values and an
ambient dimension `H`, assumes only that `scale * rho ≤ H`, and transports
pointwise normalized cap errors into the same cubic lower bound as the
unscaled mesh calculation.

No asymptotic estimate is hidden here: every endpoint and cap error remains
an explicit finite sum.
-/

namespace PellPaper

open scoped BigOperators Interval

noncomputable section

/-- A normalized positive-part deficit at scale `q` is controlled by the
literal natural rank deficit, provided `q * rho` fits inside the ambient
dimension. -/
private theorem scaled_positivePart_sub_le_cast_natSub_add_error_of_rank_le
    {q rho cap error : ℝ} {H r : ℕ}
    (hambient : q * rho ≤ (H : ℝ))
    (hrH : r ≤ H) (herror : 0 ≤ error)
    (hrcap : (r : ℝ) ≤ q * cap + error) :
    q * max (rho - cap) 0 ≤ ((H - r : ℕ) : ℝ) + error := by
  by_cases hdeficit : rho - cap ≤ 0
  · rw [max_eq_right hdeficit]
    have hsub_nonneg : 0 ≤ ((H - r : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith
  · have hdeficit_pos : 0 < rho - cap := lt_of_not_ge hdeficit
    rw [max_eq_left hdeficit_pos.le, Nat.cast_sub hrH]
    nlinarith

/-- **Scaled finite two-regime mesh bound.**  Suppose a natural rank is
bounded by `q` times the two normalized continuous caps, plus explicit
pointwise errors, and the literal ambient dimension contains `q * rho`.
Then its literal natural rank deficits dominate `q` times the cubic gain,
with exactly the endpoint loss and finite error sums displayed. -/
theorem sheared_twoRegime_mesh_scaledRankDeficits_ge_scaledCubic_sub_errors
    (rho m x mesh q : ℝ) (Nlow Nhigh H : ℕ) (rank : ℝ → ℕ)
    (errLow errHigh : ℕ → ℝ)
    (hrho : 0 ≤ rho) (hm : 0 < m) (hx : 0 < x)
    (hshear : x * rho ≤ 2 * m) (hmesh : 0 < mesh) (hq : 0 ≤ q)
    (hambient : q * rho ≤ (H : ℝ))
    (hlow_align : (Nlow : ℝ) * mesh = x * rho)
    (hhigh_align : (Nhigh : ℝ) * mesh = m - x * rho / 2)
    (hrank_dim : ∀ R, rank R ≤ H)
    (herr_low : ∀ n ∈ Finset.range Nlow, 0 ≤ errLow n)
    (herr_high : ∀ n ∈ Finset.range Nhigh, 0 ≤ errHigh n)
    (hlow_cap : ∀ n ∈ Finset.range Nlow,
      (rank (((n + 1 : ℕ) : ℝ) * mesh) : ℝ) ≤
        q * shearedTriangularCap m x (((n + 1 : ℕ) : ℝ) * mesh) + errLow n)
    (hhigh_cap : ∀ n ∈ Finset.range Nhigh,
      (rank (x * rho + ((n + 1 : ℕ) : ℝ) * mesh) : ℝ) ≤
        q * shearedShellCap rho m x
          (x * rho + ((n + 1 : ℕ) : ℝ) * mesh) + errHigh n) :
    q * (rho * m / 2 + x * rho ^ 2 / 2 - x ^ 2 * rho ^ 3 / (24 * m) -
        2 * rho * mesh) -
        mesh * (Finset.sum (Finset.range Nlow) errLow +
          Finset.sum (Finset.range Nhigh) errHigh) ≤
      mesh * ∑ n ∈ Finset.range Nlow,
          ((H - rank (((n + 1 : ℕ) : ℝ) * mesh) : ℕ) : ℝ) +
        mesh * ∑ n ∈ Finset.range Nhigh,
          ((H - rank (x * rho + ((n + 1 : ℕ) : ℝ) * mesh) : ℕ) : ℝ) := by
  have hpositive := sheared_twoRegime_mesh_positivePart_sum_ge_cubic_sub_two_mesh
    rho m x mesh Nlow Nhigh hrho hm hx hshear hmesh hlow_align hhigh_align
  have hlow_sum :
      q * (∑ n ∈ Finset.range Nlow,
        shearedTriangularDeficit rho m x (((n + 1 : ℕ) : ℝ) * mesh)) ≤
      Finset.sum (Finset.range Nlow) (fun n =>
        (((H - rank (((n + 1 : ℕ) : ℝ) * mesh) : ℕ) : ℝ) + errLow n)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    simpa only [shearedTriangularDeficit] using
      (scaled_positivePart_sub_le_cast_natSub_add_error_of_rank_le
        hambient
        (hrank_dim (((n + 1 : ℕ) : ℝ) * mesh)) (herr_low n hn)
        (hlow_cap n hn))
  have hhigh_sum :
      q * (∑ n ∈ Finset.range Nhigh,
        shearedShellDeficit rho m x
          (x * rho + ((n + 1 : ℕ) : ℝ) * mesh)) ≤
      Finset.sum (Finset.range Nhigh) (fun n =>
        (((H - rank (x * rho + ((n + 1 : ℕ) : ℝ) * mesh) : ℕ) : ℝ) +
          errHigh n)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    simpa only [shearedShellDeficit] using
      (scaled_positivePart_sub_le_cast_natSub_add_error_of_rank_le
        hambient
        (hrank_dim (x * rho + ((n + 1 : ℕ) : ℝ) * mesh))
        (herr_high n hn) (hhigh_cap n hn))
  have hdeficit_sum :
      q * ((∑ n ∈ Finset.range Nlow,
        shearedTriangularDeficit rho m x (((n + 1 : ℕ) : ℝ) * mesh) +
        ∑ n ∈ Finset.range Nhigh,
          shearedShellDeficit rho m x
            (x * rho + ((n + 1 : ℕ) : ℝ) * mesh))) ≤
      (Finset.sum (Finset.range Nlow) (fun n =>
        ((H - rank (((n + 1 : ℕ) : ℝ) * mesh) : ℕ) : ℝ)) +
        Finset.sum (Finset.range Nhigh) (fun n =>
          ((H - rank (x * rho + ((n + 1 : ℕ) : ℝ) * mesh) : ℕ) : ℝ)) +
        (Finset.sum (Finset.range Nlow) errLow +
          Finset.sum (Finset.range Nhigh) errHigh)) := by
    rw [Finset.sum_add_distrib] at hlow_sum hhigh_sum
    linarith
  have hscaled :
      q * (rho * m / 2 + x * rho ^ 2 / 2 - x ^ 2 * rho ^ 3 / (24 * m) -
        2 * rho * mesh) ≤
      mesh * (q * ((∑ n ∈ Finset.range Nlow,
        shearedTriangularDeficit rho m x (((n + 1 : ℕ) : ℝ) * mesh) +
        ∑ n ∈ Finset.range Nhigh,
          shearedShellDeficit rho m x
            (x * rho + ((n + 1 : ℕ) : ℝ) * mesh)))) := by
    calc
      q * (rho * m / 2 + x * rho ^ 2 / 2 - x ^ 2 * rho ^ 3 / (24 * m) -
          2 * rho * mesh) ≤
          q * (mesh * ∑ n ∈ Finset.range Nlow,
            shearedTriangularDeficit rho m x (((n + 1 : ℕ) : ℝ) * mesh) +
            mesh * ∑ n ∈ Finset.range Nhigh,
              shearedShellDeficit rho m x
                (x * rho + ((n + 1 : ℕ) : ℝ) * mesh)) :=
        mul_le_mul_of_nonneg_left hpositive hq
      _ = mesh * (q * ((∑ n ∈ Finset.range Nlow,
          shearedTriangularDeficit rho m x (((n + 1 : ℕ) : ℝ) * mesh) +
          ∑ n ∈ Finset.range Nhigh,
            shearedShellDeficit rho m x
              (x * rho + ((n + 1 : ℕ) : ℝ) * mesh)))) := by
          ring
  have hmesh_deficit := mul_le_mul_of_nonneg_left hdeficit_sum hmesh.le
  linarith

end

end PellPaper
