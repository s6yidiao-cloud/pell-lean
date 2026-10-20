import Pell.SlopeLatticeReducedCoordinates
import Pell.SL2FinitePrimitiveTransport
import Pell.IntegerSymmetricRectangle
import Mathlib.Tactic

/-!
# Finite ball growth for a normalized rank-two slope lattice

Reduction by an attained first-minimum column turns every finite family in a
slope-norm ball into an integral rectangle.  If the first minimum is at least
one, the thin alternative costs linearly in the radius and the full
alternative costs quadratically divided by the determinant.  This is the
parameter-free lattice-counting core used by intrinsic completion.
-/

namespace PellPaper

open scoped MatrixGroups

noncomputable section

/-- A finite family of nonzero integer vectors in a normalized slope ball has
linear-plus-area growth when the actual first minimum is at least one.  The
determinant is the literal `M / (U*V)` of the displayed slope map. -/
theorem card_slopeVectorSupNorm_le_linear_add_area
    (T : Finset (Fin 2 → ℤ)) (U V M z H : ℝ)
    (hU : 0 < U) (hV : 0 < V) (hM : 0 < M) (hH : 1 ≤ H)
    (hmuOne : 1 ≤ firstSlopeSupNorm U V M z)
    (hnonzero : ∀ y ∈ T, y ≠ 0)
    (hball : ∀ y ∈ T, slopeVectorSupNorm U V M z (y 0, y 1) ≤ H) :
    (T.card : ℝ) ≤ 6 * H + 36 * H ^ 2 / (M / (U * V)) := by
  classical
  let mu := firstSlopeSupNorm U V M z
  let delta := M / (U * V)
  let A := 2 * H / mu
  let B := 2 * mu * H / delta
  have hmuPos : 0 < mu := by
    exact lt_of_lt_of_le zero_lt_one (by simpa only [mu] using hmuOne)
  have hdeltaPos : 0 < delta := by
    dsimp only [delta]
    positivity
  have hHnonneg : 0 ≤ H := zero_le_one.trans hH
  by_cases hT : T = ∅
  · subst T
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  obtain ⟨y₀, hy₀⟩ := Finset.nonempty_iff_ne_empty.mpr hT
  have hy₀Pair : (y₀ 0, y₀ 1) ≠ (0, 0) := by
    intro hp
    apply hnonzero y₀ hy₀
    funext i
    fin_cases i
    · exact congrArg Prod.fst hp
    · exact congrArg Prod.snd hp
  have hmuLeH : mu ≤ H := by
    exact (firstSlopeSupNorm_le U V M z hU hV hM
      (y₀ 0, y₀ 1) hy₀Pair).trans (hball y₀ hy₀)
  have hAOne : 1 ≤ A := by
    dsimp only [A]
    apply (le_div_iff₀ hmuPos).2
    nlinarith
  have hAnonneg : 0 ≤ A := zero_le_one.trans hAOne
  have hBnonneg : 0 ≤ B := by
    dsimp only [B]
    positivity
  obtain ⟨W, _hfirst, hcoords⟩ :=
    exists_SL2_reduced_slope_coordinates U V M z hU hV hM
  let C := sl2InverseTargetImage W T
  have hsubset : C ⊆ integerSymmetricRectangle A B := by
    intro x hx
    have hxT : W.toLin' x ∈ T :=
      (mem_sl2InverseTargetImage_iff W T x).1 hx
    have hc := hcoords H (W.toLin' x) (hball (W.toLin' x) hxT)
    rw [W.toLin'.symm_apply_apply] at hc
    exact (mem_integerSymmetricRectangle A B _).2 (by
      simpa only [A, B, mu, delta] using hc)
  by_cases hBOne : 1 ≤ B
  · have hcard : (T.card : ℝ) ≤
        ((integerSymmetricRectangle A B).card : ℝ) := by
      rw [← card_sl2InverseTargetImage W T]
      exact_mod_cast Finset.card_le_card hsubset
    have hrect := card_integerSymmetricRectangle_le_nine_mul hAOne hBOne
    have hareaNonneg : 0 ≤ 36 * H ^ 2 / delta := by positivity
    calc
      (T.card : ℝ) ≤ ((integerSymmetricRectangle A B).card : ℝ) := hcard
      _ ≤ 9 * A * B := hrect
      _ = 36 * H ^ 2 / delta := by
        dsimp only [A, B]
        field_simp [hmuPos.ne', hdeltaPos.ne']
        ring
      _ ≤ 6 * H + 36 * H ^ 2 / delta :=
        le_add_of_nonneg_left (mul_nonneg (by norm_num) hHnonneg)
  · have hBLt : B < 1 := lt_of_not_ge hBOne
    have hsecondZero : ∀ x ∈ C, x 1 = 0 := by
      intro x hx
      have hwidth := ((mem_integerSymmetricRectangle A B x).1 (hsubset hx)).2
      exact int_eq_zero_of_abs_cast_le_lt_one (x 1) B hwidth hBLt
    have hmaps : ∀ x ∈ C, x 0 ∈ integerSymmetricInterval A := by
      intro x hx
      exact (mem_integerSymmetricInterval A (x 0)).2
        (((mem_integerSymmetricRectangle A B x).1 (hsubset hx)).1)
    have hinj : ∀ x ∈ C, ∀ y ∈ C, x 0 = y 0 → x = y := by
      intro x hx y hy hxy
      funext i
      fin_cases i
      · simpa using hxy
      · simpa using (hsecondZero x hx).trans (hsecondZero y hy).symm
    have hcardNat : C.card ≤ (integerSymmetricInterval A).card :=
      Finset.card_le_card_of_injOn (fun x => x 0) hmaps hinj
    have hcard : (T.card : ℝ) ≤
        ((integerSymmetricInterval A).card : ℝ) := by
      rw [← card_sl2InverseTargetImage W T]
      exact_mod_cast hcardNat
    have hlinear : 3 * A ≤ 6 * H := by
      calc
        3 * A = 6 * H / mu := by dsimp only [A]; ring
        _ ≤ 6 * H := div_le_self (by positivity) (by simpa only [mu] using hmuOne)
    have hareaNonneg : 0 ≤ 36 * H ^ 2 / delta := by positivity
    calc
      (T.card : ℝ) ≤ ((integerSymmetricInterval A).card : ℝ) := hcard
      _ ≤ 3 * A := card_integerSymmetricInterval_le_three_mul hAOne
      _ ≤ 6 * H := hlinear
      _ ≤ 6 * H + 36 * H ^ 2 / delta := le_add_of_nonneg_right hareaNonneg

end

end PellPaper
