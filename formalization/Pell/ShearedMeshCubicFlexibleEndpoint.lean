import Pell.ShearedMeshCubicLower

/-!
# Flexible high endpoint for the sheared mesh cubic bound

The terminal shell length need not be an integral number of mesh cells.  This
module keeps the truncated terminal interval explicit and charges its
nonnegative omitted tail as a finite endpoint error.
-/

namespace PellPaper

open scoped BigOperators Interval
open Set MeasureTheory

noncomputable section

/-- On the translated shell ray, the shell cap is nonnegative. -/
theorem shearedShellCap_nonneg_on_translated_nonneg
    {rho m x t : ℝ} (hrho : 0 ≤ rho) (hm : 0 < m) (hx : 0 < x)
    (ht : 0 ≤ t) :
    0 ≤ shearedShellCap rho m x (x * rho + t) := by
  have hfactor : 0 ≤ rho / m := div_nonneg hrho hm.le
  have hinter : 0 ≤ x * rho / 2 + t := by positivity
  have hid : shearedShellCap rho m x (x * rho + t) =
      (rho / m) * (x * rho / 2 + t) := by
    rw [shearedShellCap]
    field_simp [hm.ne']
    ring
  rw [hid]
  exact mul_nonneg hfactor hinter

/-- The clipped shell deficit is at most `rho` on the translated positive
ray. -/
theorem shearedShellDeficit_le_rho_on_translated_nonneg
    {rho m x t : ℝ} (hrho : 0 ≤ rho) (hm : 0 < m) (hx : 0 < x)
    (ht : 0 ≤ t) :
    shearedShellDeficit rho m x (x * rho + t) ≤ rho := by
  rw [shearedShellDeficit]
  have hcap : 0 ≤ shearedShellCap rho m x (x * rho + t) :=
    shearedShellCap_nonneg_on_translated_nonneg hrho hm hx ht
  apply max_le
  · linarith
  · exact hrho

/-- Continuity of the translated clipped shell deficit. -/
theorem continuous_translated_shearedShellDeficit
    (rho m x : ℝ) :
    Continuous (fun t : ℝ => shearedShellDeficit rho m x (x * rho + t)) := by
  unfold shearedShellDeficit shearedShellCap
  fun_prop

/-- The omitted shell tail of length `T - E` is at most its length times
`rho`. -/
theorem integral_translated_shearedShellDeficit_tail_le
    (rho m x E T : ℝ) (hrho : 0 ≤ rho) (hm : 0 < m) (hx : 0 < x)
    (hE : 0 ≤ E) (hET : E ≤ T) :
    (∫ t in E..T, shearedShellDeficit rho m x (x * rho + t)) ≤
      (T - E) * rho := by
  let g : ℝ → ℝ := fun t => shearedShellDeficit rho m x (x * rho + t)
  have hgcont : Continuous g := by
    simpa only [g] using continuous_translated_shearedShellDeficit rho m x
  have hmono :
      (∫ t in E..T, g t) ≤ ∫ _t in E..T, rho := by
    apply intervalIntegral.integral_mono_on hET
    · exact hgcont.intervalIntegrable _ _
    · exact intervalIntegrable_const
    · intro t ht
      dsimp only [g]
      exact shearedShellDeficit_le_rho_on_translated_nonneg
        hrho hm hx (hE.trans ht.1)
  calc
    (∫ t in E..T, shearedShellDeficit rho m x (x * rho + t)) =
        ∫ t in E..T, g t := rfl
    _ ≤ ∫ _t in E..T, rho := hmono
    _ = (T - E) * rho := by
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul]

/-- A two-regime right mesh sum with a truncated high branch captures the
continuous cubic up to the two Riemann endpoint cells and the explicitly
omitted terminal shell interval. -/
theorem sheared_twoRegime_mesh_positivePart_sum_ge_cubic_sub_highGap
    (rho m x mesh : ℝ) (Nlow Nhigh : ℕ)
    (hrho : 0 ≤ rho) (hm : 0 < m) (hx : 0 < x)
    (hshear : x * rho ≤ 2 * m) (hmesh : 0 < mesh)
    (hlow_align : (Nlow : ℝ) * mesh = x * rho)
    (hhigh_le : (Nhigh : ℝ) * mesh ≤ m - x * rho / 2) :
    rho * m / 2 + x * rho ^ 2 / 2 - x ^ 2 * rho ^ 3 / (24 * m) -
        2 * rho * mesh -
          rho * (m - x * rho / 2 - (Nhigh : ℝ) * mesh) ≤
      mesh * ∑ n ∈ Finset.range Nlow,
          shearedTriangularDeficit rho m x (((n + 1 : ℕ) : ℝ) * mesh) +
        mesh * ∑ n ∈ Finset.range Nhigh,
          shearedShellDeficit rho m x
            (x * rho + ((n + 1 : ℕ) : ℝ) * mesh) := by
  let f : ℝ → ℝ := shearedTriangularDeficit rho m x
  let T : ℝ := m - x * rho / 2
  let E : ℝ := (Nhigh : ℝ) * mesh
  have hE_nonneg : 0 ≤ E := by
    dsimp [E]
    positivity
  have hT_nonneg : 0 ≤ T := by
    dsimp [T]
    nlinarith
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
  have hganti : AntitoneOn g (Icc 0 E) := by
    intro a _ b _ hab
    apply antitone_shearedShellDeficit rho m x hrho hm
    linarith
  have hhigh := uniformMesh_rightRiemannSum_ge_integral_sub_endpoint
    g mesh Nhigh hmesh hganti
  have hhigh' :
      (∫ t in 0..E, g t) - mesh * (g 0 - g E) ≤
        mesh * ∑ n ∈ Finset.range Nhigh,
          g (((n + 1 : ℕ) : ℝ) * mesh) := by
    simpa only [E] using hhigh
  have hgcont : Continuous g := by
    simpa only [g] using continuous_translated_shearedShellDeficit rho m x
  have htail :
      (∫ t in E..T, g t) ≤ (T - E) * rho := by
    simpa only [g] using
      (integral_translated_shearedShellDeficit_tail_le
        rho m x E T hrho hm hx hE_nonneg (by simpa only [E, T] using hhigh_le))
  have hadd :
      (∫ t in 0..E, g t) + (∫ t in E..T, g t) = ∫ t in 0..T, g t := by
    exact intervalIntegral.integral_add_adjacent_intervals
      (hgcont.intervalIntegrable _ _) (hgcont.intervalIntegrable _ _)
  have hfull :
      (∫ t in 0..T, g t) ≤ (∫ t in 0..E, g t) + (T - E) * rho := by
    rw [← hadd]
    linarith
  have hhigh_full :
      (∫ t in 0..T, g t) =
        ∫ lambda in x * rho..m + x * rho / 2,
          shearedShellDeficit rho m x lambda := by
    change (∫ t in 0..T,
      shearedShellDeficit rho m x (x * rho + t)) = _
    calc
      (∫ t in 0..T,
          shearedShellDeficit rho m x (x * rho + t)) =
          ∫ lambda in x * rho + 0..x * rho + T,
            shearedShellDeficit rho m x lambda :=
        intervalIntegral.integral_comp_add_left
          (shearedShellDeficit rho m x) (x * rho)
      _ = ∫ lambda in x * rho..m + x * rho / 2,
            shearedShellDeficit rho m x lambda := by
          dsimp [T]
          ring_nf
  have hcubic :
      (∫ lambda in 0..x * rho, f lambda) +
        (∫ t in 0..T, g t) =
        rho * m / 2 + x * rho ^ 2 / 2 - x ^ 2 * rho ^ 3 / (24 * m) := by
    rw [hhigh_full]
    simpa only [f, shearedTriangularDeficit, shearedShellDeficit] using
      (sheared_twoRegime_continuous_positivePart_integral_eq_cubic
        rho m x hrho hm hx hshear)
  have htri_zero : f 0 = rho := by
    simp [f, shearedTriangularDeficit, shearedTriangularCap, hrho]
  have htri_end_nonneg : 0 ≤ f (x * rho) := by
    dsimp [f]
    exact le_max_right _ _
  have htri_loss : f 0 - f (x * rho) ≤ rho := by
    rw [htri_zero]
    linarith
  have hhigh_start_le : g 0 ≤ rho := by
    dsimp [g]
    exact shearedShellDeficit_le_rho_on_translated_nonneg
      hrho hm hx (by positivity)
  have hhigh_end_nonneg : 0 ≤ g E := by
    dsimp [g]
    exact le_max_right _ _
  have hhigh_loss : g 0 - g E ≤ rho := by
    linarith
  have htotal_loss :
      (f 0 - f (x * rho)) + (g 0 - g E) ≤ 2 * rho := by
    linarith
  have hmesh_loss : mesh *
      ((f 0 - f (x * rho)) + (g 0 - g E)) ≤ 2 * rho * mesh := by
    calc
      mesh * ((f 0 - f (x * rho)) + (g 0 - g E)) ≤ mesh * (2 * rho) :=
        mul_le_mul_of_nonneg_left htotal_loss hmesh.le
      _ = 2 * rho * mesh := by ring
  have hsum :
      (∫ lambda in 0..x * rho, f lambda) + (∫ t in 0..E, g t) -
          mesh * ((f 0 - f (x * rho)) + (g 0 - g E)) ≤
        mesh * ∑ n ∈ Finset.range Nlow,
          f (((n + 1 : ℕ) : ℝ) * mesh) +
          mesh * ∑ n ∈ Finset.range Nhigh,
            g (((n + 1 : ℕ) : ℝ) * mesh) := by
    linarith
  change rho * m / 2 + x * rho ^ 2 / 2 - x ^ 2 * rho ^ 3 / (24 * m) -
      2 * rho * mesh - rho * (T - E) ≤ _
  linarith

/-- If the truncated high endpoint is within one mesh cell of the terminal
shell endpoint, the additional omitted-tail loss is at most one more
`rho * mesh` cell. -/
theorem sheared_twoRegime_mesh_positivePart_sum_ge_cubic_sub_three_mesh
    (rho m x mesh : ℝ) (Nlow Nhigh : ℕ)
    (hrho : 0 ≤ rho) (hm : 0 < m) (hx : 0 < x)
    (hshear : x * rho ≤ 2 * m) (hmesh : 0 < mesh)
    (hlow_align : (Nlow : ℝ) * mesh = x * rho)
    (hhigh_le : (Nhigh : ℝ) * mesh ≤ m - x * rho / 2)
    (hhigh_gap : m - x * rho / 2 - (Nhigh : ℝ) * mesh ≤ mesh) :
    rho * m / 2 + x * rho ^ 2 / 2 - x ^ 2 * rho ^ 3 / (24 * m) -
        3 * rho * mesh ≤
      mesh * ∑ n ∈ Finset.range Nlow,
          shearedTriangularDeficit rho m x (((n + 1 : ℕ) : ℝ) * mesh) +
        mesh * ∑ n ∈ Finset.range Nhigh,
          shearedShellDeficit rho m x
            (x * rho + ((n + 1 : ℕ) : ℝ) * mesh) := by
  have hbase := sheared_twoRegime_mesh_positivePart_sum_ge_cubic_sub_highGap
    rho m x mesh Nlow Nhigh hrho hm hx hshear hmesh hlow_align hhigh_le
  have htail : rho * (m - x * rho / 2 - (Nhigh : ℝ) * mesh) ≤
      rho * mesh :=
    mul_le_mul_of_nonneg_left hhigh_gap hrho
  linarith

/-- The floor choice for the high mesh endpoint always lies before the
terminal shell endpoint and leaves less than one mesh cell uncovered. -/
theorem sheared_twoRegime_mesh_positivePart_sum_ge_cubic_sub_three_mesh_floor
    (rho m x mesh : ℝ) (Nlow : ℕ)
    (hrho : 0 ≤ rho) (hm : 0 < m) (hx : 0 < x)
    (hshear : x * rho ≤ 2 * m) (hmesh : 0 < mesh)
    (hlow_align : (Nlow : ℝ) * mesh = x * rho) :
    rho * m / 2 + x * rho ^ 2 / 2 - x ^ 2 * rho ^ 3 / (24 * m) -
        3 * rho * mesh ≤
      mesh * ∑ n ∈ Finset.range Nlow,
          shearedTriangularDeficit rho m x (((n + 1 : ℕ) : ℝ) * mesh) +
        mesh * ∑ n ∈ Finset.range ⌊(m - x * rho / 2) / mesh⌋₊,
          shearedShellDeficit rho m x
            (x * rho + ((n + 1 : ℕ) : ℝ) * mesh) := by
  let T : ℝ := m - x * rho / 2
  let Nhigh : ℕ := ⌊T / mesh⌋₊
  have hT_nonneg : 0 ≤ T := by
    dsimp [T]
    nlinarith
  have hT_div_nonneg : 0 ≤ T / mesh := div_nonneg hT_nonneg hmesh.le
  have hfloor_le : (Nhigh : ℝ) ≤ T / mesh := by
    dsimp [Nhigh]
    exact Nat.floor_le hT_div_nonneg
  have hhigh_le : (Nhigh : ℝ) * mesh ≤ T :=
    (le_div_iff₀ hmesh).mp hfloor_le
  have hfloor_lt : T / mesh < (Nhigh : ℝ) + 1 := by
    dsimp [Nhigh]
    exact Nat.lt_floor_add_one _
  have hhigh_lt : T < ((Nhigh : ℝ) + 1) * mesh :=
    (div_lt_iff₀ hmesh).mp hfloor_lt
  have hhigh_gap : T - (Nhigh : ℝ) * mesh ≤ mesh := by
    linarith
  have hresult := sheared_twoRegime_mesh_positivePart_sum_ge_cubic_sub_three_mesh
    rho m x mesh Nlow Nhigh hrho hm hx hshear hmesh hlow_align
      (by simpa only [T] using hhigh_le)
      (by simpa only [T] using hhigh_gap)
  simpa only [Nhigh] using hresult

/-- The scaled rank-deficit comparison used to transport a normalized
positive-part lower bound into literal natural rank deficits. -/
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

/-- Any finite positive-part lower bound transports to literal scaled rank
deficits under pointwise normalized cap errors. -/
theorem scaledRankDeficits_ge_of_positivePart_meshLowerBound
    (rho m x mesh q gain : ℝ) (Nlow Nhigh H : ℕ) (rank : ℝ → ℕ)
    (errLow errHigh : ℕ → ℝ)
    (hq : 0 ≤ q) (hmesh : 0 ≤ mesh) (hambient : q * rho ≤ (H : ℝ))
    (hrank_dim : ∀ R, rank R ≤ H)
    (herr_low : ∀ n ∈ Finset.range Nlow, 0 ≤ errLow n)
    (herr_high : ∀ n ∈ Finset.range Nhigh, 0 ≤ errHigh n)
    (hlow_cap : ∀ n ∈ Finset.range Nlow,
      (rank (((n + 1 : ℕ) : ℝ) * mesh) : ℝ) ≤
        q * shearedTriangularCap m x (((n + 1 : ℕ) : ℝ) * mesh) + errLow n)
    (hhigh_cap : ∀ n ∈ Finset.range Nhigh,
      (rank (x * rho + ((n + 1 : ℕ) : ℝ) * mesh) : ℝ) ≤
        q * shearedShellCap rho m x
          (x * rho + ((n + 1 : ℕ) : ℝ) * mesh) + errHigh n)
    (hpositive : gain ≤
      mesh * ∑ n ∈ Finset.range Nlow,
        shearedTriangularDeficit rho m x (((n + 1 : ℕ) : ℝ) * mesh) +
      mesh * ∑ n ∈ Finset.range Nhigh,
        shearedShellDeficit rho m x
          (x * rho + ((n + 1 : ℕ) : ℝ) * mesh)) :
    q * gain - mesh *
        (Finset.sum (Finset.range Nlow) errLow +
          Finset.sum (Finset.range Nhigh) errHigh) ≤
      mesh * ∑ n ∈ Finset.range Nlow,
          ((H - rank (((n + 1 : ℕ) : ℝ) * mesh) : ℕ) : ℝ) +
        mesh * ∑ n ∈ Finset.range Nhigh,
          ((H - rank (x * rho + ((n + 1 : ℕ) : ℝ) * mesh) : ℕ) : ℝ) := by
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
      q *
        ((∑ n ∈ Finset.range Nlow,
            shearedTriangularDeficit rho m x
              (((n + 1 : ℕ) : ℝ) * mesh)) +
          (∑ n ∈ Finset.range Nhigh,
            shearedShellDeficit rho m x
              (x * rho + ((n + 1 : ℕ) : ℝ) * mesh))) ≤
      ((∑ n ∈ Finset.range Nlow,
          ((H - rank (((n + 1 : ℕ) : ℝ) * mesh) : ℕ) : ℝ)) +
        (∑ n ∈ Finset.range Nhigh,
          ((H - rank (x * rho + ((n + 1 : ℕ) : ℝ) * mesh) : ℕ) : ℝ)) +
        (Finset.sum (Finset.range Nlow) errLow +
          Finset.sum (Finset.range Nhigh) errHigh)) := by
    rw [Finset.sum_add_distrib] at hlow_sum hhigh_sum
    linarith
  have hscaled :
      q * gain ≤
        mesh * (q * ((∑ n ∈ Finset.range Nlow,
          shearedTriangularDeficit rho m x (((n + 1 : ℕ) : ℝ) * mesh) +
          ∑ n ∈ Finset.range Nhigh,
            shearedShellDeficit rho m x
              (x * rho + ((n + 1 : ℕ) : ℝ) * mesh)))) := by
    calc
      q * gain ≤ q *
          (mesh * ∑ n ∈ Finset.range Nlow,
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
  have hmesh_deficit := mul_le_mul_of_nonneg_left hdeficit_sum hmesh
  linarith

/-- The scaled literal-rank version of the floor-truncated two-regime mesh
bound.  It has no exact high-endpoint alignment assumption. -/
theorem sheared_twoRegime_mesh_scaledRankDeficits_ge_scaledCubic_sub_three_mesh_floor
    (rho m x mesh q : ℝ) (Nlow H : ℕ) (rank : ℝ → ℕ)
    (errLow errHigh : ℕ → ℝ)
    (hrho : 0 ≤ rho) (hm : 0 < m) (hx : 0 < x)
    (hshear : x * rho ≤ 2 * m) (hmesh : 0 < mesh) (hq : 0 ≤ q)
    (hambient : q * rho ≤ (H : ℝ))
    (hlow_align : (Nlow : ℝ) * mesh = x * rho)
    (hrank_dim : ∀ R, rank R ≤ H)
    (herr_low : ∀ n ∈ Finset.range Nlow, 0 ≤ errLow n)
    (herr_high : ∀ n ∈ Finset.range ⌊(m - x * rho / 2) / mesh⌋₊, 0 ≤ errHigh n)
    (hlow_cap : ∀ n ∈ Finset.range Nlow,
      (rank (((n + 1 : ℕ) : ℝ) * mesh) : ℝ) ≤
        q * shearedTriangularCap m x (((n + 1 : ℕ) : ℝ) * mesh) + errLow n)
    (hhigh_cap : ∀ n ∈ Finset.range ⌊(m - x * rho / 2) / mesh⌋₊,
      (rank (x * rho + ((n + 1 : ℕ) : ℝ) * mesh) : ℝ) ≤
        q * shearedShellCap rho m x
          (x * rho + ((n + 1 : ℕ) : ℝ) * mesh) + errHigh n) :
    q * (rho * m / 2 + x * rho ^ 2 / 2 - x ^ 2 * rho ^ 3 / (24 * m) -
        3 * rho * mesh) -
        mesh * (Finset.sum (Finset.range Nlow) errLow +
          Finset.sum (Finset.range ⌊(m - x * rho / 2) / mesh⌋₊) errHigh) ≤
      mesh * ∑ n ∈ Finset.range Nlow,
          ((H - rank (((n + 1 : ℕ) : ℝ) * mesh) : ℕ) : ℝ) +
        mesh * ∑ n ∈ Finset.range ⌊(m - x * rho / 2) / mesh⌋₊,
          ((H - rank (x * rho + ((n + 1 : ℕ) : ℝ) * mesh) : ℕ) : ℝ) := by
  apply scaledRankDeficits_ge_of_positivePart_meshLowerBound
    rho m x mesh q
      (rho * m / 2 + x * rho ^ 2 / 2 - x ^ 2 * rho ^ 3 / (24 * m) -
        3 * rho * mesh)
      Nlow ⌊(m - x * rho / 2) / mesh⌋₊ H rank errLow errHigh hq hmesh.le hambient
      hrank_dim herr_low herr_high hlow_cap hhigh_cap
  exact sheared_twoRegime_mesh_positivePart_sum_ge_cubic_sub_three_mesh_floor
    rho m x mesh Nlow hrho hm hx hshear hmesh hlow_align

end

end PellPaper
