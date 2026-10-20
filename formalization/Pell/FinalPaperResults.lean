import Pell.Main3ElementaryFinalAssembly
import Pell.PaperExceptionalDefinitions
import Pell.ClassCutoffGrowth
import Pell.ExceptionalMonotonicity
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Tactic

/-!
# The headline Pell exceptional-set theorem in `paper/main.tex`

The paper counts positive nonsquare integers `D < X`. The definitions in
`PaperExceptionalDefinitions` express that strict cutoff. The uniform bound
below uses the manuscript's split at squarefree kernel `sqrt X` and the
squarefree estimate at parameter `2 * theta`.
-/

open Filter
open scoped Topology

namespace PellPaper

noncomputable section

/-- `paper/main.tex`, Theorem `T:uniform-exceptional`: one absolute positive `c`
controls both the saving and the growing range, and one absolute positive `C`
and one threshold work uniformly for every admissible `θ`. -/
theorem final_uniform_exceptional :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ᶠ X : ℝ in atTop, ∀ θ : ℝ,
        3 ≤ θ →
        θ ≤ c * Real.sqrt (Real.log X / Real.log (Real.log X)) →
        (paperExceptionalCount θ X : ℝ) ≤
          C * X ^ (1 - c / θ ^ 2) := by
  obtain ⟨C, hC, hmain⟩ := uniform_exceptional_doubled_parameter
  exact ⟨(1 : ℝ) / 3200, C, by norm_num, hC, hmain⟩

/-- The logarithmic growth scale in Corollary `C:pell-unit-growth`.
For large `D` this equals `(log D)^(3/2) / sqrt (log log D)`. -/
def paperPellLogGrowth (D : ℕ) : ℝ :=
  Real.log (D : ℝ) *
    Real.sqrt (Real.log (D : ℝ) / Real.log (Real.log (D : ℝ)))

/-- A fixed cutoff beyond which all logarithms in the growth scale are
positive and `log D ≥ exp 1`. -/
def paperGrowthStart : ℕ :=
  ⌈Real.exp (Real.exp 1)⌉₊

private theorem log_bounds_of_paperGrowthStart {D : ℕ}
    (hD : paperGrowthStart ≤ D) :
    Real.exp 1 ≤ Real.log (D : ℝ) ∧
      1 ≤ Real.log (Real.log (D : ℝ)) := by
  have hbase : Real.exp (Real.exp 1) ≤ (D : ℝ) := by
    calc
      Real.exp (Real.exp 1) ≤ (paperGrowthStart : ℝ) := Nat.le_ceil _
      _ ≤ (D : ℝ) := by exact_mod_cast hD
  have hlog : Real.exp 1 ≤ Real.log (D : ℝ) := by
    calc
      Real.exp 1 = Real.log (Real.exp (Real.exp 1)) := (Real.log_exp _).symm
      _ ≤ Real.log (D : ℝ) := Real.log_le_log (Real.exp_pos _) hbase
  refine ⟨hlog, ?_⟩
  calc
    (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp _).symm
    _ ≤ Real.log (Real.log (D : ℝ)) := Real.log_le_log (Real.exp_pos _) hlog

/-- The internal growth scale is exactly the displayed expression in
`paper/main.tex`, once its iterated logarithm is positive. -/
theorem paperPellLogGrowth_eq_displayed {D : ℕ}
    (hD : paperGrowthStart ≤ D) :
    paperPellLogGrowth D =
      Real.log (D : ℝ) ^ ((3 : ℝ) / 2) /
        Real.sqrt (Real.log (Real.log (D : ℝ))) := by
  obtain ⟨hlogD, hloglogD⟩ := log_bounds_of_paperGrowthStart hD
  have hL : 0 < Real.log (D : ℝ) :=
    (Real.exp_pos _).trans_le hlogD
  have hM : 0 < Real.log (Real.log (D : ℝ)) := by linarith
  have hpow : Real.log (D : ℝ) ^ ((3 : ℝ) / 2) =
      Real.log (D : ℝ) * Real.sqrt (Real.log (D : ℝ)) := by
    rw [show ((3 : ℝ) / 2) = 1 + 1 / 2 by norm_num,
      Real.rpow_add hL, Real.rpow_one, Real.sqrt_eq_rpow]
  unfold paperPellLogGrowth
  rw [Real.sqrt_div hL.le, hpow]
  ring

/-- The ratio `log D / log log D` increases once `D` exceeds the fixed
starting cutoff.  This is the point that lets a single moving parameter at
the global cutoff `X` control the genuinely `D`-dependent growth scale. -/
private theorem paper_growth_ratio_mono {D : ℕ} {X : ℝ}
    (hD : paperGrowthStart ≤ D) (hDX : (D : ℝ) ≤ X) :
    Real.log (D : ℝ) / Real.log (Real.log (D : ℝ)) ≤
      Real.log X / Real.log (Real.log X) := by
  obtain ⟨hlogD, hloglogD⟩ := log_bounds_of_paperGrowthStart hD
  have hDpos : 0 < (D : ℝ) := by
    have hbase := Nat.le_ceil (Real.exp (Real.exp 1))
    have : 0 < (paperGrowthStart : ℝ) :=
      (Real.exp_pos _).trans_le hbase
    exact this.trans_le (by exact_mod_cast hD)
  have hlogDX : Real.log (D : ℝ) ≤ Real.log X :=
    Real.log_le_log hDpos hDX
  have hlogX : Real.exp 1 ≤ Real.log X := hlogD.trans hlogDX
  have hloglogX : 1 ≤ Real.log (Real.log X) := by
    calc
      (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp _).symm
      _ ≤ Real.log (Real.log X) := Real.log_le_log (Real.exp_pos _) hlogX
  have hanti :
      Real.log (Real.log X) / Real.log X ≤
        Real.log (Real.log (D : ℝ)) / Real.log (D : ℝ) :=
    Real.log_div_self_antitoneOn
      (Set.mem_Ici.mpr hlogD) (Set.mem_Ici.mpr hlogX) hlogDX
  have hcross :=
    (div_le_div_iff₀ (lt_of_lt_of_le (Real.exp_pos _) hlogX)
      (lt_of_lt_of_le (Real.exp_pos _) hlogD)).1 hanti
  apply (div_le_div_iff₀ (by linarith : 0 < Real.log (Real.log (D : ℝ)))
    (by linarith : 0 < Real.log (Real.log X))).2
  nlinarith

/-- A fundamental solution whose logarithm falls below the paper's growth
scale is exceptional for the moving exponent at the global cutoff. -/
private theorem smallFundamentalSolution_of_small_paper_growth
    {D : ℕ} {X c : ℝ} (hc : 0 < c)
    (hD : paperGrowthStart ≤ D) (hDX : (D : ℝ) ≤ X)
    {a : Pell.Solution₁ (D : ℤ)} (ha : Pell.IsFundamental a)
    (hsmall : Real.log (epsilon a) ≤ c * paperPellLogGrowth D) :
    SmallFundamentalSolution
      (c * Real.sqrt (Real.log X / Real.log (Real.log X))) D := by
  obtain ⟨hlogD, hloglogD⟩ := log_bounds_of_paperGrowthStart hD
  have hratio := paper_growth_ratio_mono hD hDX
  have hsqrt := Real.sqrt_le_sqrt hratio
  have hlogDpos : 0 ≤ Real.log (D : ℝ) :=
    (Real.exp_pos _).le.trans hlogD
  have hbound : Real.log (epsilon a) ≤
      (c * Real.sqrt (Real.log X / Real.log (Real.log X))) *
        Real.log (D : ℝ) := by
    calc
      Real.log (epsilon a) ≤ c * paperPellLogGrowth D := hsmall
      _ = (c * Real.sqrt (Real.log (D : ℝ) /
            Real.log (Real.log (D : ℝ)))) * Real.log (D : ℝ) := by
        unfold paperPellLogGrowth
        ring
      _ ≤ (c * Real.sqrt (Real.log X / Real.log (Real.log X))) *
            Real.log (D : ℝ) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsqrt hc.le) hlogDpos
  have hDreal : 0 < (D : ℝ) := by
    have hbase := Nat.le_ceil (Real.exp (Real.exp 1))
    have : 0 < (paperGrowthStart : ℝ) :=
      (Real.exp_pos _).trans_le hbase
    exact this.trans_le (by exact_mod_cast hD)
  have heps : 0 < epsilon a :=
    lt_trans zero_lt_one (one_lt_epsilon_of_isFundamental ha)
  apply (smallFundamentalSolution_iff_of_isFundamental ha).2
  exact (Real.le_rpow_iff_log_le heps hDreal).2 hbound

/-- The literal bad family for Corollary `C:pell-unit-growth`.  A fundamental
Pell witness makes the radicand positive and nonsquare, and `D < X` is strict.
Its cardinality divided by `X` is proved to tend to zero below. -/
def paperPellGrowthBadSet (c X : ℝ) : Finset ℕ :=
  by
    classical
    exact (Finset.Icc 1 ⌊X⌋₊).filter fun D =>
      (D : ℝ) < X ∧
        ∃ a : Pell.Solution₁ (D : ℤ), Pell.IsFundamental a ∧
          Real.log (epsilon a) ≤
            c * (Real.log (D : ℝ) ^ ((3 : ℝ) / 2) /
              Real.sqrt (Real.log (Real.log (D : ℝ))))

theorem mem_paperPellGrowthBadSet {c X : ℝ} {D : ℕ} :
    D ∈ paperPellGrowthBadSet c X ↔
      0 < D ∧ (D : ℝ) < X ∧
        ∃ a : Pell.Solution₁ (D : ℤ), Pell.IsFundamental a ∧
          Real.log (epsilon a) ≤
            c * (Real.log (D : ℝ) ^ ((3 : ℝ) / 2) /
              Real.sqrt (Real.log (Real.log (D : ℝ)))) := by
  classical
  simp only [paperPellGrowthBadSet, Finset.mem_filter, Finset.mem_Icc,
    Nat.one_le_iff_ne_zero, Nat.pos_iff_ne_zero]
  constructor
  · rintro ⟨⟨hD, _⟩, hDX, ha⟩
    exact ⟨hD, hDX, ha⟩
  · rintro ⟨hD, hDX, ha⟩
    exact ⟨⟨hD, Nat.le_floor hDX.le⟩, hDX, ha⟩

/-- All growth failures are either among a fixed finite initial segment or
are exceptional for the global moving exponent. -/
theorem paperPellGrowthBad_card_le (c X : ℝ) (hc : 0 < c) :
    ((paperPellGrowthBadSet c X).card : ℝ) ≤
      (paperGrowthStart : ℝ) +
        (paperExceptionalCount
          (c * Real.sqrt (Real.log X / Real.log (Real.log X))) X : ℝ) := by
  let θ := c * Real.sqrt (Real.log X / Real.log (Real.log X))
  have hsubset : paperPellGrowthBadSet c X ⊆
      Finset.range paperGrowthStart ∪ paperExceptionalSet θ X := by
    intro D hD
    obtain ⟨hDpos, hDX, a, ha, hsmall⟩ :=
      mem_paperPellGrowthBadSet.mp hD
    by_cases hDsmall : D < paperGrowthStart
    · exact Finset.mem_union_left _ (Finset.mem_range.mpr hDsmall)
    · apply Finset.mem_union_right
      exact mem_paperExceptionalSet.mpr
        ⟨hDpos, hDX,
          smallFundamentalSolution_of_small_paper_growth hc
            (Nat.le_of_not_gt hDsmall) hDX.le ha (by
              rw [paperPellLogGrowth_eq_displayed
                (Nat.le_of_not_gt hDsmall)]
              exact hsmall)⟩
  have hcard := Finset.card_le_card hsubset
  have hunion := Finset.card_union_le
    (Finset.range paperGrowthStart) (paperExceptionalSet θ X)
  have hnat : (paperPellGrowthBadSet c X).card ≤
      paperGrowthStart + (paperExceptionalSet θ X).card := by
    simpa using hcard.trans hunion
  exact_mod_cast hnat

/-- At the edge of the uniform range, the power saving becomes a negative
power of `log X`. -/
private theorem moving_exceptional_power_ratio
    {c X : ℝ} (hc : 0 < c) (hX : 0 < X)
    (hlogX : 0 < Real.log X)
    (hloglogX : 0 < Real.log (Real.log X)) :
    X ^ (1 - c /
      (c * Real.sqrt (Real.log X / Real.log (Real.log X))) ^ 2) / X =
      Real.exp (-Real.log (Real.log X) / c) := by
  have hr : 0 ≤ Real.log X / Real.log (Real.log X) :=
    div_nonneg hlogX.le hloglogX.le
  rw [← Real.rpow_sub_one (ne_of_gt hX), Real.rpow_def_of_pos hX]
  congr 1
  rw [mul_pow, Real.sq_sqrt hr]
  field_simp
  ring

/-- `paper/main.tex`, Corollary `C:pell-unit-growth`: one absolute positive
constant works in the genuinely `D`-dependent lower bound.  The proportion
of positive nonsquare `D < X` whose fundamental Pell solution fails the
bound tends to zero.  The witness formulation is equivalent to referring to
the unique fundamental solution for each positive nonsquare `D`. -/
theorem final_pell_unit_growth_density :
    ∃ c : ℝ, 0 < c ∧
      Tendsto (fun X : ℝ =>
        ((paperPellGrowthBadSet c X).card : ℝ) / X) atTop (𝓝 0) := by
  obtain ⟨c, C, hc, hC, hmain⟩ := final_uniform_exceptional
  refine ⟨c, hc, ?_⟩
  let θ : ℝ → ℝ := fun X =>
    c * Real.sqrt (Real.log X / Real.log (Real.log X))
  have hθtop : Tendsto θ atTop atTop :=
    tendsto_classAverageCutoffFactor_atTop.const_mul_atTop hc
  have hθevent : ∀ᶠ X : ℝ in atTop, 3 ≤ θ X :=
    hθtop.eventually_ge_atTop 3
  have hlogevent : ∀ᶠ X : ℝ in atTop, 2 ≤ Real.log X :=
    Real.tendsto_log_atTop.eventually_ge_atTop 2
  have hupper : ∀ᶠ X : ℝ in atTop,
      ((paperPellGrowthBadSet c X).card : ℝ) / X ≤
        (paperGrowthStart : ℝ) / X +
          C * Real.exp (-Real.log (Real.log X) / c) := by
    filter_upwards [hmain, hθevent, hlogevent,
      eventually_ge_atTop (1 : ℝ)] with X hmainX hθX hlogXtwo hXge
    have hXone : 1 < X := by
      have hlogXpos : 0 < Real.log X := by linarith
      exact (Real.log_pos_iff (by linarith : 0 ≤ X)).1 hlogXpos
    have hXpos : 0 < X := by linarith
    have hlogX : 0 < Real.log X := by linarith
    have hloglogX : 0 < Real.log (Real.log X) :=
      Real.log_pos (by linarith)
    have hbad := paperPellGrowthBad_card_le c X hc
    have hmain' := hmainX (θ X) hθX (le_refl _)
    have htotal : ((paperPellGrowthBadSet c X).card : ℝ) ≤
        (paperGrowthStart : ℝ) +
          C * X ^ (1 - c / (θ X) ^ 2) := by
      change ((paperPellGrowthBadSet c X).card : ℝ) ≤
        (paperGrowthStart : ℝ) + (paperExceptionalCount (θ X) X : ℝ) at hbad
      exact hbad.trans (by simpa [add_comm] using
        (add_le_add_right hmain' (paperGrowthStart : ℝ)))
    calc
      ((paperPellGrowthBadSet c X).card : ℝ) / X ≤
          ((paperGrowthStart : ℝ) +
            C * X ^ (1 - c / (θ X) ^ 2)) / X :=
        div_le_div_of_nonneg_right htotal hXpos.le
      _ = (paperGrowthStart : ℝ) / X +
            C * (X ^ (1 - c / (θ X) ^ 2) / X) := by ring
      _ = (paperGrowthStart : ℝ) / X +
            C * Real.exp (-Real.log (Real.log X) / c) := by
        rw [show θ X =
          c * Real.sqrt (Real.log X / Real.log (Real.log X)) from rfl,
          moving_exceptional_power_ratio hc hXpos hlogX hloglogX]
  have hfirst : Tendsto (fun X : ℝ => (paperGrowthStart : ℝ) / X)
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have hloglogTop : Tendsto (fun X : ℝ => Real.log (Real.log X))
      atTop atTop := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hbot : Tendsto (fun X : ℝ => -Real.log (Real.log X) / c)
      atTop atBot := by
    have hneg : -(1 / c) < 0 := by
      have hrecip : 0 < 1 / c := one_div_pos.mpr hc
      linarith
    convert (tendsto_const_mul_atBot_of_neg hneg).2 hloglogTop using 1
    funext X
    ring
  have htail : Tendsto (fun X : ℝ =>
      C * Real.exp (-Real.log (Real.log X) / c)) atTop (𝓝 0) :=
    by simpa only [Function.comp_def, mul_zero] using
      (Real.tendsto_exp_atBot.comp hbot).const_mul C
  have hlimit : Tendsto (fun X : ℝ =>
      (paperGrowthStart : ℝ) / X +
        C * Real.exp (-Real.log (Real.log X) / c)) atTop (𝓝 0) := by
    convert hfirst.add htail using 1; simp
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hlimit
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
    exact div_nonneg (Nat.cast_nonneg _) (by linarith)
  · exact hupper

/-- The last sentence of Corollary `C:pell-unit-growth`: for any fixed positive
power, the strict-count proportion of radicands with `ε_D ≤ D^θ` vanishes. -/
theorem final_fixed_power_density (θ : ℝ) (_hθ : 0 < θ) :
    Tendsto (fun X : ℝ =>
      (paperExceptionalCount θ X : ℝ) / X) atTop (𝓝 0) := by
  obtain ⟨c, C, hc, hC, hmain⟩ := final_uniform_exceptional
  let φ : ℝ := max 3 θ
  have hφ : 3 ≤ φ := le_max_left _ _
  have hθφ : θ ≤ φ := le_max_right _ _
  have hδ : 0 < c / φ ^ 2 := by
    have hφpos : 0 < φ := by linarith
    positivity
  have hrange : ∀ᶠ X : ℝ in atTop,
      φ ≤ c * Real.sqrt (Real.log X / Real.log (Real.log X)) :=
    (tendsto_classAverageCutoffFactor_atTop.const_mul_atTop hc).eventually_ge_atTop φ
  have hbound : ∀ᶠ X : ℝ in atTop,
      (paperExceptionalCount θ X : ℝ) / X ≤
        C * X ^ (-(c / φ ^ 2)) := by
    filter_upwards [hmain, hrange, eventually_ge_atTop (1 : ℝ)] with X hmainX hrangeX hX
    have hXpos : 0 < X := by linarith
    have hcount : (paperExceptionalCount θ X : ℝ) ≤
        C * X ^ (1 - c / φ ^ 2) := by
      have hmono : (paperExceptionalCount θ X : ℝ) ≤
          (paperExceptionalCount φ X : ℝ) := by
        exact_mod_cast (paperExceptionalCount_mono (X := X) hθφ)
      exact hmono.trans (hmainX φ hφ hrangeX)
    calc
      (paperExceptionalCount θ X : ℝ) / X ≤
          (C * X ^ (1 - c / φ ^ 2)) / X :=
        div_le_div_of_nonneg_right hcount hXpos.le
      _ = C * X ^ (-(c / φ ^ 2)) := by
        rw [mul_div_assoc, ← Real.rpow_sub_one (ne_of_gt hXpos)]
        congr 1
        ring_nf
  have htail : Tendsto (fun X : ℝ => C * X ^ (-(c / φ ^ 2)))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_rpow_neg_atTop hδ).const_mul C
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds htail
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
    exact div_nonneg (Nat.cast_nonneg _) (by linarith)
  · exact hbound

end

end PellPaper
