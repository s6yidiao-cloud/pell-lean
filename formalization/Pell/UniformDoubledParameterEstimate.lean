import Pell.UniformDoubledParameterRestoration
import Pell.Main3ElementarySquarefreeEstimate
import Pell.PaperExceptionalDefinitions
import Pell.UniformDoubledParameterScale
import Mathlib.Tactic

/-!
# The uniform exceptional estimate by the manuscript's doubled parameter

This route uses the squarefree count at `2 * theta`, the split by squarefree
kernel at `sqrt X`, and a geometric sum of dyadic kernel blocks.  It does not
invoke the existing arbitrary-radicand exceptional estimate.
-/

open Filter
open scoped BigOperators
namespace PellPaper
noncomputable section

/-- Multiplication of the root weight with the squarefree block estimate
leaves exponent `1/2-d` in the dyadic kernel scale. -/
theorem doubledParameter_weight_identity {X W d : ℝ}
    (hX : 0 ≤ X) (hW : 0 < W) :
    Real.sqrt (X / W) * W ^ (1 - d) =
      Real.sqrt X * W ^ (1 / 2 - d) := by
  rw [Real.sqrt_div hX, Real.sqrt_eq_rpow (x := W)]
  calc
    Real.sqrt X / W ^ (1 / 2 : ℝ) * W ^ (1 - d) =
        Real.sqrt X * (W ^ (1 - d) / W ^ (1 / 2 : ℝ)) := by ring
    _ = Real.sqrt X * W ^ ((1 - d) - 1 / 2) := by rw [← Real.rpow_sub hW]
    _ = Real.sqrt X * W ^ (1 / 2 - d) := by congr 2; ring

/-- Finite geometric aggregation of the actual square-part cover. The block
hypothesis is needed only for scales at least `sqrt X/2`, including the block
which straddles the kernel split. -/
theorem E_le_doubledParameter_geometric
    {theta X C d : ℝ} (htheta : 0 ≤ theta) (hX : 1 ≤ X)
    (hC : 0 ≤ C) (hd : 0 ≤ d) (hdquarter : d ≤ 1 / 4)
    (hblocks : ∀ k ∈ (Finset.range (Nat.log 2 ⌊X⌋₊ + 1)).filter
        (fun k => Real.sqrt X / 2 ≤ ((2 ^ k : ℕ) : ℝ)),
      (squarefreeDyadicExceptionalCount (2 * theta) (2 ^ k) : ℝ) ≤
        C * ((2 ^ k : ℕ) : ℝ) ^ (1 - d)) :
    E theta X ≤ (2 + 2 * C / ((2 : ℝ) ^ (1 / 4 : ℝ) - 1)) *
      X ^ (1 - d) := by
  classical
  let K : ℕ := Nat.log 2 ⌊X⌋₊ + 1
  let high : Finset ℕ := (Finset.range K).filter
    (fun k => Real.sqrt X / 2 ≤ ((2 ^ k : ℕ) : ℝ))
  let p : ℝ := 1 / 2 - d
  let D : ℝ := (2 : ℝ) ^ (1 / 4 : ℝ) - 1
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hp : 0 < p := by dsimp [p]; linarith
  have hpquarter : (1 / 4 : ℝ) ≤ p := by dsimp [p]; linarith
  have hpOne : p ≤ 1 := by dsimp [p]; linarith
  have hD : 0 < D := by
    dsimp [D]
    exact sub_pos.mpr (Real.one_lt_rpow (by norm_num) (by norm_num))
  have hcover : E theta X ≤
      ((doubledParameterLowCover X).card : ℝ) +
        ∑ k ∈ high, ((doubledParameterHighBlock theta X (2 ^ k)).card : ℝ) := by
    change ((exceptionalSet theta ⌊X⌋₊).card : ℝ) ≤ _
    have hsub := exceptionalSet_subset_doubledParameter_cover htheta hXpos.le
    calc
      ((exceptionalSet theta ⌊X⌋₊).card : ℝ) ≤
          ((doubledParameterLowCover X ∪
            high.biUnion (fun k => doubledParameterHighBlock theta X (2 ^ k))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      _ ≤ ((doubledParameterLowCover X).card : ℝ) +
          ((high.biUnion (fun k => doubledParameterHighBlock theta X (2 ^ k))).card : ℝ) := by
        exact_mod_cast Finset.card_union_le _ _
      _ ≤ _ := by
        gcongr
        exact_mod_cast Finset.card_biUnion_le
  have hpoint : ∀ k ∈ high,
      ((doubledParameterHighBlock theta X (2 ^ k)).card : ℝ) ≤
        C * Real.sqrt X * ((2 ^ k : ℕ) : ℝ) ^ p := by
    intro k hk
    have hWpos : (0 : ℝ) < ((2 ^ k : ℕ) : ℝ) := by positivity
    calc
      ((doubledParameterHighBlock theta X (2 ^ k)).card : ℝ) ≤
          Real.sqrt (X / ((2 ^ k : ℕ) : ℝ)) *
            (squarefreeDyadicExceptionalCount (2 * theta) (2 ^ k) : ℝ) :=
        doubledParameterHighBlock_card_le hXpos.le (by positivity)
      _ ≤ Real.sqrt (X / ((2 ^ k : ℕ) : ℝ)) *
          (C * ((2 ^ k : ℕ) : ℝ) ^ (1 - d)) :=
        mul_le_mul_of_nonneg_left (hblocks k hk) (Real.sqrt_nonneg _)
      _ = C * Real.sqrt X * ((2 ^ k : ℕ) : ℝ) ^ p := by
        rw [← mul_assoc, mul_comm (Real.sqrt _) C, mul_assoc,
          doubledParameter_weight_identity hXpos.le hWpos]
        dsimp [p]
        ring
  have hhigh :
      (∑ k ∈ high, ((doubledParameterHighBlock theta X (2 ^ k)).card : ℝ)) ≤
        C * Real.sqrt X * ∑ k ∈ Finset.range K, ((2 ^ k : ℕ) : ℝ) ^ p := by
    calc
      (∑ k ∈ high, ((doubledParameterHighBlock theta X (2 ^ k)).card : ℝ)) ≤
          ∑ k ∈ high, C * Real.sqrt X * ((2 ^ k : ℕ) : ℝ) ^ p :=
        Finset.sum_le_sum hpoint
      _ ≤ ∑ k ∈ Finset.range K, C * Real.sqrt X * ((2 ^ k : ℕ) : ℝ) ^ p := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.filter_subset _ _
        · intro k _ _
          positivity
      _ = _ := by rw [Finset.mul_sum]
  have hN : 1 ≤ ⌊X⌋₊ := (Nat.le_floor_iff hXpos.le).2 (by simpa using hX)
  have htop : ((2 ^ K : ℕ) : ℝ) ≤ 2 * X := by
    calc
      ((2 ^ K : ℕ) : ℝ) ≤ ((2 * ⌊X⌋₊ : ℕ) : ℝ) := by
        have hpow : 2 ^ Nat.log 2 ⌊X⌋₊ ≤ ⌊X⌋₊ :=
          Nat.pow_log_le_self 2 (by omega)
        have htopNat : 2 ^ K ≤ 2 * ⌊X⌋₊ := by
          dsimp [K]
          rw [pow_succ]
          simpa only [Nat.mul_comm] using Nat.mul_le_mul_right 2 hpow
        exact_mod_cast htopNat
      _ ≤ 2 * X := by
        push_cast
        gcongr
        exact Nat.floor_le hXpos.le
  have hden : D ≤ (2 : ℝ) ^ p - 1 := by
    dsimp [D]
    have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hpquarter
    linarith
  have htwo : (2 : ℝ) ^ p ≤ 2 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hpOne
  have htopPow : ((2 ^ K : ℕ) : ℝ) ^ p ≤ 2 * X ^ p := by
    calc
      ((2 ^ K : ℕ) : ℝ) ^ p ≤ (2 * X) ^ p :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) htop hp.le
      _ = (2 : ℝ) ^ p * X ^ p := Real.mul_rpow (by norm_num) hXpos.le
      _ ≤ 2 * X ^ p := mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hXpos.le _)
  have hgeom : (∑ k ∈ Finset.range K, ((2 ^ k : ℕ) : ℝ) ^ p) ≤
      2 * X ^ p / D := by
    apply (sum_cast_two_pow_rpow_le p hp K).trans
    exact div_le_div₀ (by positivity) htopPow hD hden
  have hpowers : Real.sqrt X * X ^ p = X ^ (1 - d) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hXpos]
    congr 1
    dsimp [p]
    ring
  have hhighFinal :
      (∑ k ∈ high, ((doubledParameterHighBlock theta X (2 ^ k)).card : ℝ)) ≤
        (2 * C / D) * X ^ (1 - d) := by
    calc
      _ ≤ C * Real.sqrt X * (2 * X ^ p / D) :=
        hhigh.trans (mul_le_mul_of_nonneg_left hgeom (by positivity))
      _ = (2 * C / D) * (Real.sqrt X * X ^ p) := by ring
      _ = _ := by rw [hpowers]
  have hlow : ((doubledParameterLowCover X).card : ℝ) ≤ 2 * X ^ (1 - d) := by
    apply (doubledParameterLowCover_card_le hXpos.le).trans
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hX (by linarith : (3 / 4 : ℝ) ≤ 1 - d))
      (by norm_num)
  calc
    E theta X ≤ ((doubledParameterLowCover X).card : ℝ) +
        ∑ k ∈ high, ((doubledParameterHighBlock theta X (2 ^ k)).card : ℝ) := hcover
    _ ≤ 2 * X ^ (1 - d) + (2 * C / D) * X ^ (1 - d) := add_le_add hlow hhighFinal
    _ = _ := by dsimp [D]; ring

/-- The manuscript's doubled-parameter restoration, with all squarefree
inputs discharged by the proved elementary squarefree estimate. One threshold
and one constant work for every admissible `theta`. -/
theorem uniform_exceptional_E_doubled_parameter :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ X : ℝ in atTop, ∀ theta : ℝ,
        3 ≤ theta →
        theta ≤ ((1 : ℝ) / 3200) *
          Real.sqrt (Real.log X / Real.log (Real.log X)) →
        E theta X ≤
          C * X ^ (1 - 1 / (1600 * theta ^ 2)) := by
  obtain ⟨Csf, hCsf, hsf⟩ :=
    exists_pos_uniform_squarefreeDyadicExceptionalCount_cast_le_elementary
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1
    (hsf ((1 : ℝ) / 200) (by norm_num) (by norm_num))
  let D : ℝ := (2 : ℝ) ^ (1 / 4 : ℝ) - 1
  have hD : 0 < D := by
    dsimp [D]
    exact sub_pos.mpr (Real.one_lt_rpow (by norm_num) (by norm_num))
  refine ⟨2 + 2 * Csf / D, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop
    (max (Real.exp 12) ((2 * (N₀ : ℝ)) ^ 2))] with X hXlarge
  have hXexp : Real.exp 12 ≤ X := (le_max_left _ _).trans hXlarge
  have hXsq : (2 * (N₀ : ℝ)) ^ 2 ≤ X := (le_max_right _ _).trans hXlarge
  have hXpos : 0 < X := (Real.exp_pos _).trans_le hXexp
  have hXone : 1 ≤ X := by
    have : (1 : ℝ) < Real.exp 12 := Real.one_lt_exp_iff.mpr (by norm_num)
    exact this.le.trans hXexp
  intro theta htheta hadm
  have hthetaPos : 0 < theta := by linarith
  have hthetaSq : 0 < theta ^ 2 := sq_pos_of_pos hthetaPos
  let d : ℝ := 1 / (1600 * theta ^ 2)
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hdquarter : d ≤ 1 / 4 := by
    dsimp [d]
    apply (div_le_iff₀ (by positivity : 0 < 1600 * theta ^ 2)).2
    nlinarith
  have hQadm : UniformAdmissible ((1 : ℝ) / 3200) theta X :=
    (uniformQ_le_theta htheta).trans hadm
  have hblocks : ∀ k ∈ (Finset.range (Nat.log 2 ⌊X⌋₊ + 1)).filter
        (fun k => Real.sqrt X / 2 ≤ ((2 ^ k : ℕ) : ℝ)),
      (squarefreeDyadicExceptionalCount (2 * theta) (2 ^ k) : ℝ) ≤
        Csf * ((2 ^ k : ℕ) : ℝ) ^ (1 - d) := by
    intro k hk
    obtain ⟨hkRange, hkLower⟩ := Finset.mem_filter.mp hk
    have hkLog : k ≤ Nat.log 2 ⌊X⌋₊ := by
      have := Finset.mem_range.mp hkRange
      omega
    have hNpos : ⌊X⌋₊ ≠ 0 := by
      have : 1 ≤ ⌊X⌋₊ := (Nat.le_floor_iff hXpos.le).2 (by simpa using hXone)
      omega
    have hWupper : ((2 ^ k : ℕ) : ℝ) ≤ X := by
      calc
        ((2 ^ k : ℕ) : ℝ) ≤ (⌊X⌋₊ : ℝ) := by
          exact_mod_cast Nat.pow_le_of_le_log hNpos hkLog
        _ ≤ X := Nat.floor_le hXpos.le
    have hsqrtN : 2 * (N₀ : ℝ) ≤ Real.sqrt X := by
      calc
        2 * (N₀ : ℝ) = Real.sqrt ((2 * (N₀ : ℝ)) ^ 2) := by
          rw [Real.sqrt_sq (by positivity)]
        _ ≤ Real.sqrt X := Real.sqrt_le_sqrt hXsq
    have hN₀W : N₀ ≤ 2 ^ k := by
      have : (N₀ : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := by linarith
      exact_mod_cast this
    have hthetaW := theta_le_eight_mul_of_uniformAdmissible_of_sqrt_half_le_two_mul
      (by norm_num : (0 : ℝ) ≤ 1 / 3200) hXexp hkLower
      (hWupper.trans (by linarith : X ≤ 2 * X)) hQadm
    have hdoubleW : 2 * theta ≤ ((1 : ℝ) / 200) *
        Real.sqrt (Real.log ((2 ^ k : ℕ) : ℝ) /
          Real.log (Real.log ((2 ^ k : ℕ) : ℝ))) := by
      linarith
    have hsfW := hN₀ (2 ^ k) hN₀W (2 * theta) (by linarith) hdoubleW
    have hmono : squarefreeDyadicExceptionalCount (2 * theta) (2 ^ k) ≤
        squarefreeDyadicExceptionalCount (2 * theta + 1 / 4) (2 ^ k) := by
      apply Finset.card_le_card
      intro w hw
      obtain ⟨hlo, hhi, hsfw, hsmall⟩ := mem_squarefreeDyadicExceptionalSet.mp hw
      exact mem_squarefreeDyadicExceptionalSet.mpr
        ⟨hlo, hhi, hsfw, smallFundamentalSolution_mono (by linarith) hsmall⟩
    have hexponent : 1 - 1 / (400 * (2 * theta) ^ 2) = 1 - d := by
      dsimp [d]
      congr 1
      congr 1
      ring
    rw [hexponent] at hsfW
    exact (show (squarefreeDyadicExceptionalCount (2 * theta) (2 ^ k) : ℝ) ≤
      (squarefreeDyadicExceptionalCount (2 * theta + 1 / 4) (2 ^ k) : ℝ)
      by exact_mod_cast hmono).trans hsfW
  exact E_le_doubledParameter_geometric hthetaPos.le hXone hCsf.le hd hdquarter hblocks

/-- The doubled-parameter proof in the degree notation used by the
class-number estimates. The conversion preserves a uniform threshold. -/
theorem uniformExceptionalEstimate_doubled_parameter :
    UniformExceptionalEstimate ((1 : ℝ) / 6400) := by
  obtain ⟨C, hC, hmain⟩ := uniform_exceptional_E_doubled_parameter
  refine ⟨by norm_num, (1 : ℝ) / 6400, C, by norm_num, hC, ?_⟩
  filter_upwards [hmain, eventually_ge_atTop (1 : ℝ)] with X hX hXone
  intro theta htheta hadm
  have hthetaPos : 0 < theta := by linarith
  have hQpos : 0 < (uniformQ theta : ℝ) := uniformQ_pos htheta
  have hthetaQ : theta ≤ 2 * (uniformQ theta : ℝ) := by
    linarith [theta_add_half_le_two_mul_uniformQ theta]
  have hrange : theta ≤ ((1 : ℝ) / 3200) *
      Real.sqrt (Real.log X / Real.log (Real.log X)) := by
    unfold UniformAdmissible at hadm
    linarith
  have hsave : ((1 : ℝ) / 6400) / (uniformQ theta : ℝ) ^ 2 ≤
      1 / (1600 * theta ^ 2) := by
    have hthetaSq : theta ^ 2 ≤ 4 * (uniformQ theta : ℝ) ^ 2 := by
      nlinarith [mul_self_le_mul_self hthetaPos.le hthetaQ]
    have hden : 1600 * theta ^ 2 ≤ 6400 * (uniformQ theta : ℝ) ^ 2 := by
      nlinarith
    calc
      ((1 : ℝ) / 6400) / (uniformQ theta : ℝ) ^ 2 =
          1 / (6400 * (uniformQ theta : ℝ) ^ 2) := by ring
      _ ≤ 1 / (1600 * theta ^ 2) :=
        one_div_le_one_div_of_le (by positivity) hden
  apply (hX theta htheta hrange).trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact Real.rpow_le_rpow_of_exponent_le hXone (by linarith)

/-- The manuscript's strict exceptional-set theorem, with the same positive
constant in its growing parameter range and its saving. -/
theorem uniform_exceptional_doubled_parameter :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ X : ℝ in atTop, ∀ theta : ℝ,
        3 ≤ theta →
        theta ≤ ((1 : ℝ) / 3200) *
          Real.sqrt (Real.log X / Real.log (Real.log X)) →
        (paperExceptionalCount theta X : ℝ) ≤
          C * X ^ (1 - ((1 : ℝ) / 3200) / theta ^ 2) := by
  obtain ⟨C, hC, hmain⟩ := uniform_exceptional_E_doubled_parameter
  refine ⟨C, hC, ?_⟩
  filter_upwards [hmain, eventually_ge_atTop (1 : ℝ)] with X hX hXone
  intro theta htheta hadm
  apply (paperExceptionalCount_le_E theta X).trans
  apply (hX theta htheta hadm).trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.rpow_le_rpow_of_exponent_le hXone
  have hthetaPos : 0 < theta := by linarith
  have hsave : ((1 : ℝ) / 3200) / theta ^ 2 ≤ 1 / (1600 * theta ^ 2) := by
    field_simp
    norm_num
  linarith

end
end PellPaper
