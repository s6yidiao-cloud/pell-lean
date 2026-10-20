import Pell.DyadicTargetImageGeometry
import Pell.SlopeLatticeReducedCoordinates
import Pell.SL2FinitePrimitiveTransport
import Pell.IntegerSymmetricRectangle

/-!
# Finite reduced covers of literal dyadic target images

One actual integer basis is chosen before all source-cell data. Exact
integer rectangles cover its inverse images. Primitivity bounds the strict
thin branch by two targets; the nonempty full-rank branch retains the
rounded area and both side lengths needed by the later square sieve.
These are finite target-vector counts, not analytic estimates or tuple counts.
-/

namespace PellPaper

open scoped MatrixGroups

/-- Radius-two reduced widths have explicit rounded area, individual side
and perimeter budgets. The short-vector witness premise is supplied by a
nonempty actual cell in the application below. -/
theorem slope_reduced_integer_rectangle_budgets
    (U V M z : ℝ) (hU : 0 < U) (hV : 0 < V) (hM : 0 < M)
    (hshort : firstSlopeSupNorm U V M z ≤ 2)
    (hfull : 1 ≤ 4 * firstSlopeSupNorm U V M z / (M / (U * V))) :
    let mu := firstSlopeSupNorm U V M z
    let delta := M / (U * V)
    let A := 4 / mu
    let B := 4 * mu / delta
    2 ≤ A ∧
      ((integerSymmetricRectangle A B).card : ℝ) ≤ 144 * U * V / M ∧
      ((integerSymmetricInterval A).card : ℝ) ≤ 12 / mu ∧
      ((integerSymmetricInterval B).card : ℝ) ≤ 12 * mu / delta ∧
      ((integerSymmetricInterval A).card : ℝ) +
        ((integerSymmetricInterval B).card : ℝ) ≤ 24 / mu := by
  let mu := firstSlopeSupNorm U V M z
  let delta := M / (U * V)
  have hmu : 0 < mu := firstSlopeSupNorm_pos U V M z hU hV hM
  have hd : 0 < delta := div_pos hM (mul_pos hU hV)
  have hsq : mu ^ 2 ≤ delta := by
    have hu := firstSlopeSupNorm_le_sqrt U V M z hU hV hM
    have hs := Real.sq_sqrt hd.le
    change mu ≤ Real.sqrt delta at hu
    nlinarith [Real.sqrt_nonneg delta]
  have hA : 2 ≤ 4 / mu := (le_div_iff₀ hmu).mpr (by change mu ≤ 2 at hshort; linarith)
  have hB : 1 ≤ 4 * mu / delta := hfull
  have ha := card_integerSymmetricInterval_le_three_mul (show 1 ≤ 4 / mu by linarith)
  have hb := card_integerSymmetricInterval_le_three_mul hB
  have ha' : ((integerSymmetricInterval (4 / mu)).card : ℝ) ≤ 12 / mu := by
    convert ha using 1
    all_goals ring
  have hb' : ((integerSymmetricInterval (4 * mu / delta)).card : ℝ) ≤
      12 * mu / delta := by
    convert hb using 1
    all_goals ring
  have hbd : 12 * mu / delta ≤ 12 / mu := by
    apply (div_le_div_iff₀ hd hmu).mpr
    nlinarith
  refine ⟨hA, ?_, ha', hb', ?_⟩
  · calc
      _ ≤ 9 * (4 / mu) * (4 * mu / delta) :=
        card_integerSymmetricRectangle_le_nine_mul (by linarith) hB
      _ = 144 * U * V / M := by
        dsimp [delta]
        field_simp
        ring
  · have h := add_le_add ha' (hb'.trans hbd)
    calc
      _ ≤ 12 / mu + 12 / mu := h
      _ = 24 / mu := by ring

/-- For each fixed box, positive localization parameter and target ceiling,
one actual determinant-one basis covers every literal target image. The
basis is chosen before `theta`, `Y` and the source index `j` vary. No target
capacity, basis certificate or primitive-vector premise is supplied. -/
theorem exists_reduced_dyadicSourceTargetImage_cover
    (i : ℕ × ℕ × ℕ × ℕ) (M : ℕ) (k : ℤ) (hM : 0 < M) :
    let U : ℝ := ((2 ^ i.2.2.1 : ℕ) : ℝ)
    let V : ℝ := ((2 ^ i.2.2.2 : ℕ) : ℝ)
    let mu := firstSlopeSupNorm U V (M : ℝ) (k : ℝ)
    let delta := (M : ℝ) / (U * V)
    let A := 4 / mu
    let B := 4 * mu / delta
    ∃ W : SL(2, ℤ),
      slopeVectorSupNorm U V (M : ℝ) (k : ℝ) (W 0 0, W 1 0) = mu ∧
      ∀ (theta : ℝ) (Y j : ℕ),
        let T := dyadicSourceTargetImage theta Y i M j k
        let C := sl2InverseTargetImage W T
        C.card = T.card ∧
        (∀ x ∈ C, IsCoprime (x 0) (x 1)) ∧
        (∀ y ∈ T, W.toLin' (W.toLin'.symm y) = y) ∧
        C ⊆ integerSymmetricRectangle A B ∧
        (T.Nonempty → 2 ≤ A) ∧
        (B < 1 → T.card ≤ 2) ∧
        (T.Nonempty → 1 ≤ B →
          ((integerSymmetricRectangle A B).card : ℝ) ≤ 144 * U * V / (M : ℝ) ∧
          ((integerSymmetricInterval A).card : ℝ) ≤ 12 / mu ∧
          ((integerSymmetricInterval B).card : ℝ) ≤ 12 * mu / delta ∧
          ((integerSymmetricInterval A).card : ℝ) +
            ((integerSymmetricInterval B).card : ℝ) ≤ 24 / mu) := by
  let U : ℝ := ((2 ^ i.2.2.1 : ℕ) : ℝ)
  let V : ℝ := ((2 ^ i.2.2.2 : ℕ) : ℝ)
  let mu := firstSlopeSupNorm U V (M : ℝ) (k : ℝ)
  let delta := (M : ℝ) / (U * V)
  have hU : 0 < U := by dsimp [U]; positivity
  have hV : 0 < V := by dsimp [V]; positivity
  have hMr : 0 < (M : ℝ) := by exact_mod_cast hM
  have hmu : 0 < mu := firstSlopeSupNorm_pos U V (M : ℝ) (k : ℝ) hU hV hMr
  obtain ⟨W, hfirst, hcoords⟩ :=
    exists_SL2_reduced_slope_coordinates U V (M : ℝ) (k : ℝ) hU hV hMr
  refine ⟨W, hfirst, ?_⟩
  intro theta Y j
  let T := dyadicSourceTargetImage theta Y i M j k
  have hp : ∀ y ∈ T, IsCoprime (y 0) (y 1) :=
    fun _ hy => (dyadicSourceTargetImage_primitive_and_supNorm hy).1
  have hw : ∀ y ∈ T, |(W.toLin'.symm y 0 : ℝ)| ≤ 4 / mu ∧
      |(W.toLin'.symm y 1 : ℝ)| ≤ 4 * mu / delta := by
    intro y hy
    have h := hcoords 2 y (dyadicSourceTargetImage_primitive_and_supNorm hy).2
    dsimp [mu, delta]
    constructor
    · convert h.1 using 1
      all_goals ring
    · convert h.2 using 1
      all_goals ring
  refine ⟨card_sl2InverseTargetImage W T,
    primitive_sl2InverseTargetImage W T hp,
    fun y _ => W.toLin'.apply_symm_apply y, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    exact (mem_integerSymmetricRectangle _ _ _).mpr (hw y hy)
  · intro hT
    have hs : mu ≤ 2 := firstSlopeSupNorm_le_two_of_dyadicSourceTargetImage_nonempty hM hT
    exact (le_div_iff₀ hmu).mpr (by linarith)
  · exact card_targets_le_two_of_sl2_inverse_thin W T (4 * mu / delta) hp
      (fun y hy => (hw y hy).2)
  · intro hT hB
    have hs : mu ≤ 2 := firstSlopeSupNorm_le_two_of_dyadicSourceTargetImage_nonempty hM hT
    exact (slope_reduced_integer_rectangle_budgets U V (M : ℝ) (k : ℝ)
      hU hV hMr hs hB).2

end PellPaper
