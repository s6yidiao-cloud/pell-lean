import Pell.ElementaryQuadraticCharacterSieveBypass
import Mathlib.Tactic

/-!
# The sharp anisotropic square sieve

This module formalizes `L:anisotropic-square` of `main_v4.tex`.
The polynomial has arbitrary odd homogeneous degree, with repeated factors
permitted. All constants are chosen before the polynomial and rectangle.
The sieve scale is the ceiling of the square root of the shorter side.
-/

namespace PellPaper

open Filter

noncomputable section

/-- The elementary sieve with no bad-prime certificate: odd homogeneity alone
is sufficient, and no bound depending on the degree or coefficients is needed. -/
theorem eventually_oddHomogeneous_rectangle_squareSieve :
    ∀ᶠ N : ℕ in atTop, ∀ W : ℝ,
      ∀ F : MvPolynomial (Fin 2) ℤ, ∀ d : ℕ,
      ∀ x0 y0 : ℤ, ∀ L₁ L₂ : ℕ,
      Real.log W ≤ (Real.log 2 / 16) * (N : ℝ) →
      F.IsHomogeneous d → Odd d →
      (∀ xy ∈ (Finset.range L₁).product (Finset.range L₂),
        ((MvPolynomial.eval ![x0 + (xy.1 : ℤ), y0 + (xy.2 : ℤ)] F).natAbs : ℝ) ≤ W) →
      ((((Finset.range L₁).product (Finset.range L₂)).filter
        (fun xy =>
          MvPolynomial.eval ![x0 + (xy.1 : ℤ), y0 + (xy.2 : ℤ)] F ≠ 0 ∧
          IsSquare (MvPolynomial.eval ![x0 + (xy.1 : ℤ), y0 + (xy.2 : ℤ)] F))).card : ℝ) ≤
        (32 / Real.log 2) * (L₁ : ℝ) * (L₂ : ℝ) *
            Real.log (N : ℝ) / (N : ℝ) +
          36 * (N : ℝ) *
            ((16 * (N : ℝ) ^ 2) *
                (1 + Real.log (16 * (N : ℝ) ^ 2)) ^ 2 +
              ((L₁ : ℝ) + (L₂ : ℝ)) *
                (1 + Real.log (16 * (N : ℝ) ^ 2))) := by
  filter_upwards
    [eventually_squareSieve_oddHomogeneous_polynomial_rectangle_le_trivial] with N hN
  intro W F d x0 y0 L₁ L₂ hW hF hd hsize
  have h := hN 1 1 W F d x0 y0 L₁ L₂
    (fun xy => MvPolynomial.eval ![x0 + (xy.1 : ℤ), y0 + (xy.2 : ℤ)] F)
    (fun _ => 1) (by norm_num) (by norm_num) (by simp; positivity)
    hW hF hd (by intro xy _; simp) hsize
  exact h

private theorem sharpSieve_log_bounds
    (S N : ℝ) (hS : 1 ≤ S) (hN : 1 ≤ N) (hNr : N ≤ 2 * Real.sqrt S) :
    Real.log N ≤ Real.log (2 * S) ∧
      1 + Real.log (16 * N ^ 2) ≤
        (1 / Real.log 2 + 6) * Real.log (2 * S) := by
  have hSpos : 0 < S := by linarith
  have hNpos : 0 < N := by linarith
  have hsqrt : Real.sqrt S ≤ S := Real.sqrt_le_self_iff.mpr (Or.inr hS)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogS : Real.log 2 ≤ Real.log (2 * S) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hlogN : Real.log N ≤ Real.log (2 * S) :=
    Real.log_le_log hNpos (by nlinarith)
  refine ⟨hlogN, ?_⟩
  have hlog16 : Real.log 16 = 4 * Real.log 2 := by
    have h := Real.log_pow 2 4
    norm_num at h ⊢
    exact h
  rw [Real.log_mul (by norm_num) (pow_ne_zero _ hNpos.ne'),
    Real.log_pow, hlog16]
  have hone : 1 ≤ Real.log (2 * S) / Real.log 2 :=
    (one_le_div hlog2).mpr hlogS
  have hone' : 1 ≤ (1 / Real.log 2) * Real.log (2 * S) := by
    simpa only [one_div_mul_eq_div] using hone
  nlinarith

/-- The sharp bound for an integer-shifted rectangle with real side budgets.
The two constants are absolute and are uniform in the degree, coefficients,
offsets, side lengths and value bound. Empty rectangles and the zero polynomial
are included. -/
theorem anisotropic_sharp_squareSieve_rectangle :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ (F : MvPolynomial (Fin 2) ℤ) (d : ℕ)
        (S₁ S₂ W : ℝ) (x0 y0 : ℤ) (L₁ L₂ : ℕ),
        F.IsHomogeneous d → Odd d →
        1 ≤ S₂ → S₂ ≤ S₁ → 2 ≤ W →
        (L₁ : ℝ) ≤ 2 * S₁ → (L₂ : ℝ) ≤ 2 * S₂ →
        (∀ xy ∈ (Finset.range L₁).product (Finset.range L₂),
          ((MvPolynomial.eval ![x0 + (xy.1 : ℤ), y0 + (xy.2 : ℤ)] F).natAbs : ℝ) ≤ W) →
        C * Real.log W ≤ Real.sqrt S₂ →
        ((((Finset.range L₁).product (Finset.range L₂)).filter
          (fun xy =>
            MvPolynomial.eval ![x0 + (xy.1 : ℤ), y0 + (xy.2 : ℤ)] F ≠ 0 ∧
            IsSquare (MvPolynomial.eval ![x0 + (xy.1 : ℤ), y0 + (xy.2 : ℤ)] F))).card : ℝ) ≤
          K * (Real.log (2 * S₂)) ^ 2 * S₁ * Real.sqrt S₂ := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp eventually_oddHomogeneous_rectangle_squareSieve
  let a : ℝ := 1 / Real.log 2 + 6
  let C : ℝ := ((N₀ : ℝ) + 16) / Real.log 2
  let K : ℝ := 128 / (Real.log 2) ^ 2 + 4608 * a ^ 2 + 288 * a / Real.log 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ha : 0 < a := by dsimp [a]; positivity
  refine ⟨C, K, by dsimp [C]; positivity, by dsimp [K]; positivity, ?_⟩
  intro F d S₁ S₂ W x0 y0 L₁ L₂ hF hd hS₂ hS₁ hW hL₁ hL₂ hsize hscale
  let r : ℝ := Real.sqrt S₂
  let N : ℕ := ⌈r⌉₊
  let L : ℝ := Real.log (2 * S₂)
  let H : ℝ := 1 + Real.log (16 * (N : ℝ) ^ 2)
  have hr : 1 ≤ r := Real.one_le_sqrt.mpr hS₂
  have hrpos : 0 < r := by linarith
  have hS₁pos : 0 < S₁ := by linarith
  have hS₂pos : 0 < S₂ := by linarith
  have hrN : r ≤ (N : ℝ) := Nat.le_ceil r
  have hNr : (N : ℝ) ≤ 2 * r := Nat.ceil_le_two_mul (by linarith)
  have hNpos : (0 : ℝ) < N := hrpos.trans_le hrN
  have hNOne : (1 : ℝ) ≤ N := hr.trans hrN
  have hlogW : Real.log 2 ≤ Real.log W := Real.log_le_log (by norm_num) hW
  have hCpos : 0 < C := by dsimp [C]; positivity
  have hN₀r : (N₀ : ℝ) ≤ r := by
    have hmul := mul_le_mul_of_nonneg_left hlogW hCpos.le
    have hCeq : C * Real.log 2 = (N₀ : ℝ) + 16 := by
      dsimp [C]
      field_simp
    rw [hCeq] at hmul
    change C * Real.log W ≤ r at hscale
    linarith
  have hNN₀ : N₀ ≤ N := by exact_mod_cast hN₀r.trans hrN
  have hWbudget : Real.log W ≤ (Real.log 2 / 16) * (N : ℝ) := by
    have hN₀nonneg : (0 : ℝ) ≤ N₀ := by positivity
    have hscale' : ((N₀ : ℝ) + 16) * Real.log W ≤ r * Real.log 2 := by
      dsimp [C] at hscale
      rw [div_mul_eq_mul_div] at hscale
      exact (div_le_iff₀ hlog2).mp hscale
    have hlogWnonneg : 0 ≤ Real.log W := hlog2.le.trans hlogW
    have hprod : 0 ≤ (N₀ : ℝ) * Real.log W := mul_nonneg hN₀nonneg hlogWnonneg
    nlinarith
  have hbound := hN₀ N hNN₀ W F d x0 y0 L₁ L₂ hWbudget hF hd hsize
  obtain ⟨hlogN, hH⟩ := sharpSieve_log_bounds S₂ (N : ℝ) hS₂ hNOne hNr
  change Real.log (N : ℝ) ≤ L at hlogN
  change H ≤ a * L at hH
  have hL : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by linarith)
  have hLpos : 0 < L := hlog2.trans_le hL
  have hHnonneg : 0 ≤ H := by
    dsimp [H]
    have hN2 : (1 : ℝ) ≤ 16 * (N : ℝ) ^ 2 := by nlinarith
    linarith [Real.log_nonneg hN2]
  have hLsq : L ≤ L ^ 2 / Real.log 2 := by
    apply (le_div_iff₀ hlog2).mpr
    nlinarith
  have harea : (L₁ : ℝ) * (L₂ : ℝ) ≤ 4 * S₁ * S₂ := by
    calc
      _ ≤ (2 * S₁) * (2 * S₂) := mul_le_mul hL₁ hL₂ (by positivity) (by positivity)
      _ = _ := by ring
  have hperimeter : (L₁ : ℝ) + (L₂ : ℝ) ≤ 4 * S₁ := by linarith
  have hrsq : r ^ 2 = S₂ := Real.sq_sqrt hS₂pos.le
  have hdiag :
      (32 / Real.log 2) * (L₁ : ℝ) * (L₂ : ℝ) * Real.log (N : ℝ) / (N : ℝ) ≤
        (128 / (Real.log 2) ^ 2) * S₁ * r * L ^ 2 := by
    calc
      _ ≤ (32 / Real.log 2) * (4 * S₁ * S₂) * L / r := by
        have hlogNnonneg : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hNOne
        apply (div_le_div_of_nonneg_right ?_ hNpos.le).trans
          (div_le_div_of_nonneg_left (by positivity) hrpos hrN)
        calc
          _ = (32 / Real.log 2) * ((L₁ : ℝ) * (L₂ : ℝ)) * Real.log (N : ℝ) := by ring
          _ ≤ (32 / Real.log 2) * (4 * S₁ * S₂) * L := by gcongr
      _ = (128 / Real.log 2) * S₁ * r * L := by
        rw [← hrsq]
        field_simp
        ring
      _ ≤ (128 / Real.log 2) * S₁ * r * (L ^ 2 / Real.log 2) := by gcongr
      _ = _ := by ring
  have hcube : (N : ℝ) ^ 3 ≤ 8 * S₁ * r := by
    calc
      (N : ℝ) ^ 3 ≤ (2 * r) ^ 3 := by gcongr
      _ = 8 * S₂ * r := by rw [← hrsq]; ring
      _ ≤ 8 * S₁ * r := by gcongr
  have hbulk : 576 * (N : ℝ) ^ 3 * H ^ 2 ≤ 4608 * a ^ 2 * S₁ * r * L ^ 2 := by
    calc
      _ ≤ 576 * (8 * S₁ * r) * (a * L) ^ 2 := by gcongr
      _ = _ := by ring
  have hper : 36 * (N : ℝ) * ((L₁ : ℝ) + (L₂ : ℝ)) * H ≤
      (288 * a / Real.log 2) * S₁ * r * L ^ 2 := by
    calc
      _ ≤ 36 * (2 * r) * (4 * S₁) * (a * L) := by gcongr
      _ = 288 * a * S₁ * r * L := by ring
      _ ≤ 288 * a * S₁ * r * (L ^ 2 / Real.log 2) := by gcongr
      _ = _ := by ring
  calc
    _ ≤ (32 / Real.log 2) * (L₁ : ℝ) * (L₂ : ℝ) *
          Real.log (N : ℝ) / (N : ℝ) +
        576 * (N : ℝ) ^ 3 * H ^ 2 +
        36 * (N : ℝ) * ((L₁ : ℝ) + (L₂ : ℝ)) * H := by
      convert hbound using 1
      dsimp [H]
      ring
    _ ≤ (128 / (Real.log 2) ^ 2) * S₁ * r * L ^ 2 +
        4608 * a ^ 2 * S₁ * r * L ^ 2 +
        (288 * a / Real.log 2) * S₁ * r * L ^ 2 :=
      add_le_add (add_le_add hdiag hbulk) hper
    _ = K * (Real.log (2 * S₂)) ^ 2 * S₁ * Real.sqrt S₂ := by
      dsimp [K, L, r]
      ring

/-- The integer points in a closed rectangle with real endpoints. -/
def closedRealRectangle (a₁ b₁ a₂ b₂ : ℝ) : Finset (ℤ × ℤ) :=
  (Finset.Icc ⌈a₁⌉ ⌊b₁⌋).product (Finset.Icc ⌈a₂⌉ ⌊b₂⌋)

private theorem integerInterval_length_budget
    (a b : ℝ) (h : 1 ≤ b - a) :
    (((⌊b⌋ + 1 - ⌈a⌉).toNat : ℕ) : ℝ) ≤ 2 * (b - a) := by
  have hf := Int.floor_le b
  have hc := Int.le_ceil a
  by_cases hq : 0 ≤ ⌊b⌋ + 1 - ⌈a⌉
  · have heq : (((⌊b⌋ + 1 - ⌈a⌉).toNat : ℕ) : ℝ) =
        (⌊b⌋ : ℝ) + 1 - (⌈a⌉ : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hq
    rw [heq]
    linarith
  · rw [Int.toNat_eq_zero.mpr (by omega)]
    simp only [Nat.cast_zero]
    linarith

/-- The sharp anisotropic bound on arbitrary closed real intervals, under an
arbitrary upper bound `W ≥ 2` for the absolute polynomial values. -/
theorem anisotropic_sharp_squareSieve_intervals :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ (F : MvPolynomial (Fin 2) ℤ) (d : ℕ)
        (a₁ b₁ a₂ b₂ W : ℝ),
        F.IsHomogeneous d → Odd d →
        1 ≤ b₂ - a₂ → b₂ - a₂ ≤ b₁ - a₁ → 2 ≤ W →
        (∀ xy ∈ closedRealRectangle a₁ b₁ a₂ b₂,
          ((MvPolynomial.eval ![xy.1, xy.2] F).natAbs : ℝ) ≤ W) →
        C * Real.log W ≤ Real.sqrt (b₂ - a₂) →
        (((closedRealRectangle a₁ b₁ a₂ b₂).filter
          (fun xy => MvPolynomial.eval ![xy.1, xy.2] F ≠ 0 ∧
            IsSquare (MvPolynomial.eval ![xy.1, xy.2] F))).card : ℝ) ≤
          K * (Real.log (2 * (b₂ - a₂))) ^ 2 *
            (b₁ - a₁) * Real.sqrt (b₂ - a₂) := by
  obtain ⟨C, K, hC, hK, hsieve⟩ := anisotropic_sharp_squareSieve_rectangle
  refine ⟨C, K, hC, hK, ?_⟩
  intro F d a₁ b₁ a₂ b₂ W hF hd hS₂ hS₁ hW hsize hscale
  let x0 : ℤ := ⌈a₁⌉
  let y0 : ℤ := ⌈a₂⌉
  let L₁ : ℕ := (⌊b₁⌋ + 1 - ⌈a₁⌉).toNat
  let L₂ : ℕ := (⌊b₂⌋ + 1 - ⌈a₂⌉).toNat
  let e₁ : ℕ ↪ ℤ := Nat.castEmbedding.trans (addLeftEmbedding x0)
  let e₂ : ℕ ↪ ℤ := Nat.castEmbedding.trans (addLeftEmbedding y0)
  have hrect : closedRealRectangle a₁ b₁ a₂ b₂ =
      ((Finset.range L₁).product (Finset.range L₂)).map (e₁.prodMap e₂) := by
    dsimp [closedRealRectangle]
    rw [Int.Icc_eq_finset_map, Int.Icc_eq_finset_map]
    exact (Finset.prodMap_map_product e₁ e₂ (Finset.range L₁) (Finset.range L₂)).symm
  have hsize' : ∀ xy ∈ (Finset.range L₁).product (Finset.range L₂),
      ((MvPolynomial.eval ![x0 + (xy.1 : ℤ), y0 + (xy.2 : ℤ)] F).natAbs : ℝ) ≤ W := by
    intro xy hxy
    have hm : (e₁.prodMap e₂) xy ∈ closedRealRectangle a₁ b₁ a₂ b₂ := by
      rw [hrect]
      exact Finset.mem_map.mpr ⟨xy, hxy, rfl⟩
    have hfirst : ((e₁.prodMap e₂) xy).1 = x0 + (xy.1 : ℤ) := rfl
    have hsecond : ((e₁.prodMap e₂) xy).2 = y0 + (xy.2 : ℤ) := rfl
    simpa only [hfirst, hsecond] using hsize _ hm
  have hb := hsieve F d (b₁ - a₁) (b₂ - a₂) W x0 y0 L₁ L₂
    hF hd hS₂ hS₁ hW (integerInterval_length_budget a₁ b₁ (by linarith))
    (integerInterval_length_budget a₂ b₂ hS₂) hsize' hscale
  rw [hrect, Finset.filter_map, Finset.card_map]
  have hpred : (fun xy : ℤ × ℤ =>
      MvPolynomial.eval ![xy.1, xy.2] F ≠ 0 ∧
        IsSquare (MvPolynomial.eval ![xy.1, xy.2] F)) ∘ (e₁.prodMap e₂) =
      (fun xy : ℕ × ℕ =>
        MvPolynomial.eval ![x0 + (xy.1 : ℤ), y0 + (xy.2 : ℤ)] F ≠ 0 ∧
        IsSquare (MvPolynomial.eval ![x0 + (xy.1 : ℤ), y0 + (xy.2 : ℤ)] F)) := by
    funext xy
    have hfirst : ((e₁.prodMap e₂) xy).1 = x0 + (xy.1 : ℤ) := rfl
    have hsecond : ((e₁.prodMap e₂) xy).2 = y0 + (xy.2 : ℤ) := rfl
    simp only [Function.comp_apply, hfirst, hsecond]
  simpa only [hpred] using hb

/-- `2 + max |F(x,y)|` on the integer rectangle; the maximum is zero when
there are no integer points, matching the manuscript convention. -/
def homogeneousRectangleValueHeight
    (F : MvPolynomial (Fin 2) ℤ) (a₁ b₁ a₂ b₂ : ℝ) : ℝ :=
  2 + ((closedRealRectangle a₁ b₁ a₂ b₂).sup
    (fun xy => (MvPolynomial.eval ![xy.1, xy.2] F).natAbs) : ℕ)

/-- The standalone sharp square-sieve lemma `L:anisotropic-square` of
`main_v4.tex`, with its literal value height and `log²(2 S₂)` factor.
All constants are independent of the polynomial and its degree. -/
theorem anisotropic_sharp_squareSieve :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ (F : MvPolynomial (Fin 2) ℤ) (d : ℕ)
        (a₁ b₁ a₂ b₂ : ℝ),
        F.IsHomogeneous d → Odd d →
        1 ≤ b₂ - a₂ → b₂ - a₂ ≤ b₁ - a₁ →
        C * Real.log (homogeneousRectangleValueHeight F a₁ b₁ a₂ b₂) ≤
          Real.sqrt (b₂ - a₂) →
        (((closedRealRectangle a₁ b₁ a₂ b₂).filter
          (fun xy => MvPolynomial.eval ![xy.1, xy.2] F ≠ 0 ∧
            IsSquare (MvPolynomial.eval ![xy.1, xy.2] F))).card : ℝ) ≤
          K * (Real.log (2 * (b₂ - a₂))) ^ 2 *
            (b₁ - a₁) * Real.sqrt (b₂ - a₂) := by
  obtain ⟨C, K, hC, hK, hsieve⟩ := anisotropic_sharp_squareSieve_intervals
  refine ⟨C, K, hC, hK, ?_⟩
  intro F d a₁ b₁ a₂ b₂ hF hd hS₂ hS₁ hscale
  apply hsieve F d a₁ b₁ a₂ b₂ (homogeneousRectangleValueHeight F a₁ b₁ a₂ b₂)
    hF hd hS₂ hS₁
  · dsimp [homogeneousRectangleValueHeight]
    exact le_add_of_nonneg_right (Nat.cast_nonneg _)
  · intro xy hxy
    have h := Finset.le_sup (f := fun xy : ℤ × ℤ =>
      (MvPolynomial.eval ![xy.1, xy.2] F).natAbs) hxy
    have h' : ((MvPolynomial.eval ![xy.1, xy.2] F).natAbs : ℝ) ≤
        ((closedRealRectangle a₁ b₁ a₂ b₂).sup
          (fun xy => (MvPolynomial.eval ![xy.1, xy.2] F).natAbs) : ℕ) := by
      exact_mod_cast h
    dsimp [homogeneousRectangleValueHeight]
    linarith
  · exact hscale

/-- The product-hypothesis corollary used in the manuscript's balanced and
unbalanced applications. The real side budgets bound the actual integer
window; enlarging the second budget does not enlarge that window or its
value-height bound. -/
theorem anisotropic_product_squareSieve_rectangle :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ (F : MvPolynomial (Fin 2) ℤ) (d : ℕ)
        (S₁ S₂ W : ℝ) (x0 y0 : ℤ) (L₁ L₂ : ℕ),
        F.IsHomogeneous d → Odd d →
        1 ≤ S₂ → S₂ ≤ S₁ → 2 ≤ W →
        (L₁ : ℝ) ≤ 2 * S₁ → (L₂ : ℝ) ≤ 2 * S₂ →
        (∀ xy ∈ (Finset.range L₁).product (Finset.range L₂),
          ((MvPolynomial.eval ![x0 + (xy.1 : ℤ), y0 + (xy.2 : ℤ)] F).natAbs : ℝ) ≤ W) →
        C * Real.log W ≤ (S₁ * S₂) ^ (1 / 4 : ℝ) →
        ((((Finset.range L₁).product (Finset.range L₂)).filter
          (fun xy =>
            MvPolynomial.eval ![x0 + (xy.1 : ℤ), y0 + (xy.2 : ℤ)] F ≠ 0 ∧
            IsSquare (MvPolynomial.eval ![x0 + (xy.1 : ℤ), y0 + (xy.2 : ℤ)] F))).card : ℝ) ≤
          K * (Real.log (2 * (S₁ * S₂))) ^ 2 *
            S₁ ^ (5 / 4 : ℝ) * S₂ ^ (1 / 4 : ℝ) := by
  obtain ⟨C, K, hC, hK, hsieve⟩ := anisotropic_sharp_squareSieve_rectangle
  refine ⟨C, K, hC, hK, ?_⟩
  intro F d S₁ S₂ W x0 y0 L₁ L₂ hF hd hS₂ hS₁ hW hL₁ hL₂ hsize hscale
  let A : ℝ := Real.sqrt (S₁ * S₂)
  have hS₂pos : 0 < S₂ := by linarith
  have hS₁pos : 0 < S₁ := hS₂pos.trans_le hS₁
  have hprodpos : 0 < S₁ * S₂ := mul_pos hS₁pos hS₂pos
  have hprodOne : 1 ≤ S₁ * S₂ := by nlinarith
  have hAone : 1 ≤ A := Real.one_le_sqrt.mpr hprodOne
  have hS₂A : S₂ ≤ A := by
    apply Real.le_sqrt_of_sq_le
    have h := mul_le_mul_of_nonneg_right hS₁ hS₂pos.le
    nlinarith
  have hAS₁ : A ≤ S₁ := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨hS₁pos.le, ?_⟩
    have h := mul_le_mul_of_nonneg_left hS₁ hS₁pos.le
    nlinarith
  have hAprod : A ≤ S₁ * S₂ :=
    Real.sqrt_le_self_iff.mpr (Or.inr hprodOne)
  have hroot : Real.sqrt A = (S₁ * S₂) ^ (1 / 4 : ℝ) := by
    dsimp [A]
    simp only [Real.sqrt_eq_rpow]
    rw [← Real.rpow_mul hprodpos.le]
    norm_num
  have hL₂A : (L₂ : ℝ) ≤ 2 * A := by linarith
  have hscaleA : C * Real.log W ≤ Real.sqrt A := by simpa only [hroot] using hscale
  have hb := hsieve F d S₁ A W x0 y0 L₁ L₂
    hF hd hAone hAS₁ hW hL₁ hL₂A hsize hscaleA
  have hlog0 : 0 ≤ Real.log (2 * A) := Real.log_nonneg (by linarith)
  have hlog : Real.log (2 * A) ≤ Real.log (2 * (S₁ * S₂)) :=
    Real.log_le_log (by positivity : 0 < 2 * A) (by linarith)
  have hlogSq : (Real.log (2 * A)) ^ 2 ≤
      (Real.log (2 * (S₁ * S₂))) ^ 2 := pow_le_pow_left₀ hlog0 hlog 2
  have hS₁power : S₁ * S₁ ^ (1 / 4 : ℝ) = S₁ ^ (5 / 4 : ℝ) := by
    calc
      S₁ * S₁ ^ (1 / 4 : ℝ) = S₁ ^ (1 : ℝ) * S₁ ^ (1 / 4 : ℝ) := by
        rw [Real.rpow_one]
      _ = S₁ ^ ((1 : ℝ) + 1 / 4) := (Real.rpow_add hS₁pos _ _).symm
      _ = _ := by norm_num
  have hpower : S₁ * Real.sqrt A =
      S₁ ^ (5 / 4 : ℝ) * S₂ ^ (1 / 4 : ℝ) := by
    rw [hroot, Real.mul_rpow hS₁pos.le hS₂pos.le, ← mul_assoc, hS₁power]
  calc
    _ ≤ K * (Real.log (2 * A)) ^ 2 * S₁ * Real.sqrt A := hb
    _ ≤ K * (Real.log (2 * (S₁ * S₂))) ^ 2 * S₁ * Real.sqrt A := by gcongr
    _ = K * (Real.log (2 * (S₁ * S₂))) ^ 2 *
        (S₁ ^ (5 / 4 : ℝ) * S₂ ^ (1 / 4 : ℝ)) := by
      rw [← hpower]
      ring
    _ = _ := by ring

/-- The product-hypothesis square sieve on closed real intervals, under an
arbitrary upper bound `W ≥ 2` for the absolute polynomial values. -/
theorem anisotropic_product_squareSieve_intervals :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ (F : MvPolynomial (Fin 2) ℤ) (d : ℕ)
        (a₁ b₁ a₂ b₂ W : ℝ),
        F.IsHomogeneous d → Odd d →
        1 ≤ b₂ - a₂ → b₂ - a₂ ≤ b₁ - a₁ → 2 ≤ W →
        (∀ xy ∈ closedRealRectangle a₁ b₁ a₂ b₂,
          ((MvPolynomial.eval ![xy.1, xy.2] F).natAbs : ℝ) ≤ W) →
        C * Real.log W ≤ ((b₁ - a₁) * (b₂ - a₂)) ^ (1 / 4 : ℝ) →
        (((closedRealRectangle a₁ b₁ a₂ b₂).filter
          (fun xy => MvPolynomial.eval ![xy.1, xy.2] F ≠ 0 ∧
            IsSquare (MvPolynomial.eval ![xy.1, xy.2] F))).card : ℝ) ≤
          K * (Real.log (2 * ((b₁ - a₁) * (b₂ - a₂)))) ^ 2 *
            (b₁ - a₁) ^ (5 / 4 : ℝ) * (b₂ - a₂) ^ (1 / 4 : ℝ) := by
  obtain ⟨C, K, hC, hK, hsieve⟩ := anisotropic_product_squareSieve_rectangle
  refine ⟨C, K, hC, hK, ?_⟩
  intro F d a₁ b₁ a₂ b₂ W hF hd hS₂ hS₁ hW hsize hscale
  let x0 : ℤ := ⌈a₁⌉
  let y0 : ℤ := ⌈a₂⌉
  let L₁ : ℕ := (⌊b₁⌋ + 1 - ⌈a₁⌉).toNat
  let L₂ : ℕ := (⌊b₂⌋ + 1 - ⌈a₂⌉).toNat
  let e₁ : ℕ ↪ ℤ := Nat.castEmbedding.trans (addLeftEmbedding x0)
  let e₂ : ℕ ↪ ℤ := Nat.castEmbedding.trans (addLeftEmbedding y0)
  have hrect : closedRealRectangle a₁ b₁ a₂ b₂ =
      ((Finset.range L₁).product (Finset.range L₂)).map (e₁.prodMap e₂) := by
    dsimp [closedRealRectangle]
    rw [Int.Icc_eq_finset_map, Int.Icc_eq_finset_map]
    exact (Finset.prodMap_map_product e₁ e₂ (Finset.range L₁) (Finset.range L₂)).symm
  have hsize' : ∀ xy ∈ (Finset.range L₁).product (Finset.range L₂),
      ((MvPolynomial.eval ![x0 + (xy.1 : ℤ), y0 + (xy.2 : ℤ)] F).natAbs : ℝ) ≤ W := by
    intro xy hxy
    have hm : (e₁.prodMap e₂) xy ∈ closedRealRectangle a₁ b₁ a₂ b₂ := by
      rw [hrect]
      exact Finset.mem_map.mpr ⟨xy, hxy, rfl⟩
    have hfirst : ((e₁.prodMap e₂) xy).1 = x0 + (xy.1 : ℤ) := rfl
    have hsecond : ((e₁.prodMap e₂) xy).2 = y0 + (xy.2 : ℤ) := rfl
    simpa only [hfirst, hsecond] using hsize _ hm
  have hb := hsieve F d (b₁ - a₁) (b₂ - a₂) W x0 y0 L₁ L₂
    hF hd hS₂ hS₁ hW (integerInterval_length_budget a₁ b₁ (by linarith))
    (integerInterval_length_budget a₂ b₂ hS₂) hsize' hscale
  rw [hrect, Finset.filter_map, Finset.card_map]
  have hpred : (fun xy : ℤ × ℤ =>
      MvPolynomial.eval ![xy.1, xy.2] F ≠ 0 ∧
        IsSquare (MvPolynomial.eval ![xy.1, xy.2] F)) ∘ (e₁.prodMap e₂) =
      (fun xy : ℕ × ℕ =>
        MvPolynomial.eval ![x0 + (xy.1 : ℤ), y0 + (xy.2 : ℤ)] F ≠ 0 ∧
        IsSquare (MvPolynomial.eval ![x0 + (xy.1 : ℤ), y0 + (xy.2 : ℤ)] F)) := by
    funext xy
    have hfirst : ((e₁.prodMap e₂) xy).1 = x0 + (xy.1 : ℤ) := rfl
    have hsecond : ((e₁.prodMap e₂) xy).2 = y0 + (xy.2 : ℤ) := rfl
    simp only [Function.comp_apply, hfirst, hsecond]
  simpa only [hpred] using hb

/-- The product-hypothesis corollary `C:anisotropic-square` of
`main_v4.tex`, with its literal value height and logarithm of the area.
All constants are independent of the polynomial and its degree. -/
theorem anisotropic_product_squareSieve :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ (F : MvPolynomial (Fin 2) ℤ) (d : ℕ)
        (a₁ b₁ a₂ b₂ : ℝ),
        F.IsHomogeneous d → Odd d →
        1 ≤ b₂ - a₂ → b₂ - a₂ ≤ b₁ - a₁ →
        C * Real.log (homogeneousRectangleValueHeight F a₁ b₁ a₂ b₂) ≤
          ((b₁ - a₁) * (b₂ - a₂)) ^ (1 / 4 : ℝ) →
        (((closedRealRectangle a₁ b₁ a₂ b₂).filter
          (fun xy => MvPolynomial.eval ![xy.1, xy.2] F ≠ 0 ∧
            IsSquare (MvPolynomial.eval ![xy.1, xy.2] F))).card : ℝ) ≤
          K * (Real.log (2 * ((b₁ - a₁) * (b₂ - a₂)))) ^ 2 *
            (b₁ - a₁) ^ (5 / 4 : ℝ) * (b₂ - a₂) ^ (1 / 4 : ℝ) := by
  obtain ⟨C, K, hC, hK, hsieve⟩ := anisotropic_product_squareSieve_intervals
  refine ⟨C, K, hC, hK, ?_⟩
  intro F d a₁ b₁ a₂ b₂ hF hd hS₂ hS₁ hscale
  apply hsieve F d a₁ b₁ a₂ b₂ (homogeneousRectangleValueHeight F a₁ b₁ a₂ b₂)
    hF hd hS₂ hS₁
  · dsimp [homogeneousRectangleValueHeight]
    exact le_add_of_nonneg_right (Nat.cast_nonneg _)
  · intro xy hxy
    have h := Finset.le_sup (f := fun xy : ℤ × ℤ =>
      (MvPolynomial.eval ![xy.1, xy.2] F).natAbs) hxy
    have h' : ((MvPolynomial.eval ![xy.1, xy.2] F).natAbs : ℝ) ≤
        ((closedRealRectangle a₁ b₁ a₂ b₂).sup
          (fun xy => (MvPolynomial.eval ![xy.1, xy.2] F).natAbs) : ℕ) := by
      exact_mod_cast h
    dsimp [homogeneousRectangleValueHeight]
    linarith
  · exact hscale


end

end PellPaper
