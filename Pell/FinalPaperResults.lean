import Pell.Main3ElementaryFinalAssembly
import Pell.ClassCutoffGrowth
import Pell.ExceptionalMonotonicity
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Tactic

/-!
# The headline Pell exceptional-set theorem in `paper/main.tex`

The paper counts positive nonsquare integers `D < X`.  The earlier `E` API uses
the closed cutoff `D ≤ ⌊X⌋₊`; the filter below restores the paper's strict
endpoint.  The uniform estimate proved by the elementary square-sieve route
has a degree parameter `uniformQ θ`.  In the range `θ ≥ 3`, this degree is at
most `θ`, so it implies the displayed saving in the paper with a single
absolute constant in both the saving and the admissible range.
-/

open Filter
open scoped Topology

namespace PellPaper

noncomputable section

/-- The literal exceptional set in `paper/main.tex`, with strict real cutoff `D < X`. -/
def paperExceptionalSet (θ X : ℝ) : Finset ℕ :=
  (exceptionalSet θ ⌊X⌋₊).filter fun D => (D : ℝ) < X

/-- The literal count `E_θ(X)` from `paper/main.tex`. -/
def paperExceptionalCount (θ X : ℝ) : ℕ :=
  (paperExceptionalSet θ X).card

theorem mem_paperExceptionalSet {θ X : ℝ} {D : ℕ} :
    D ∈ paperExceptionalSet θ X ↔
      0 < D ∧ (D : ℝ) < X ∧ SmallFundamentalSolution θ D := by
  simp only [paperExceptionalSet, Finset.mem_filter, mem_exceptionalSet,
    Nat.one_le_iff_ne_zero, Nat.pos_iff_ne_zero]
  constructor
  · rintro ⟨⟨hD, _, hsmall⟩, hDX⟩
    exact ⟨hD, hDX, hsmall⟩
  · rintro ⟨hD, hDX, hsmall⟩
    refine ⟨⟨hD, ?_, hsmall⟩, hDX⟩
    exact Nat.le_floor hDX.le

/-- Strict-endpoint counts are bounded by the closed-cutoff API used in the
analytic proof. -/
theorem paperExceptionalCount_le_E (θ X : ℝ) :
    (paperExceptionalCount θ X : ℝ) ≤ E θ X := by
  change ((paperExceptionalSet θ X).card : ℝ) ≤
    ((exceptionalSet θ ⌊X⌋₊).card : ℝ)
  unfold paperExceptionalSet
  exact_mod_cast Finset.card_filter_le
    (s := exceptionalSet θ ⌊X⌋₊) (p := fun D : ℕ => (D : ℝ) < X)

theorem paperExceptionalCount_mono {θ φ X : ℝ} (hθφ : θ ≤ φ) :
    paperExceptionalCount θ X ≤ paperExceptionalCount φ X := by
  unfold paperExceptionalCount
  apply Finset.card_le_card
  intro D hD
  obtain ⟨hDpos, hDX, hsmall⟩ := mem_paperExceptionalSet.mp hD
  exact mem_paperExceptionalSet.mpr
    ⟨hDpos, hDX, smallFundamentalSolution_mono hθφ hsmall⟩

/-- In the theorem's range, the ceiling degree is no larger than `θ`. -/
theorem uniformQ_le_theta {θ : ℝ} (hθ : 3 ≤ θ) :
    (uniformQ θ : ℝ) ≤ θ := by
  linarith [two_mul_uniformQ_lt hθ]

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
  obtain ⟨_, cExc, C, hcExc, hC, hmain⟩ :=
    uniformExceptionalEstimate_one_div_6400_elementary_proved
  let c : ℝ := min cExc ((1 : ℝ) / 6400)
  have hc : 0 < c := lt_min hcExc (by norm_num)
  have hcExc' : c ≤ cExc := min_le_left _ _
  have hcSave : c ≤ (1 : ℝ) / 6400 := min_le_right _ _
  refine ⟨c, C, hc, hC, ?_⟩
  filter_upwards [hmain, eventually_ge_atTop (1 : ℝ)] with X hX hXone
  intro θ hθ hrange
  have hθpos : 0 < θ := by linarith
  have hQpos : 0 < (uniformQ θ : ℝ) := uniformQ_pos hθ
  have hQle : (uniformQ θ : ℝ) ≤ θ := uniformQ_le_theta hθ
  have hsqrt : 0 ≤ Real.sqrt (Real.log X / Real.log (Real.log X)) :=
    Real.sqrt_nonneg _
  have hAdmissible : UniformAdmissible cExc θ X := by
    unfold UniformAdmissible
    calc
      (uniformQ θ : ℝ) ≤ θ := hQle
      _ ≤ c * Real.sqrt (Real.log X / Real.log (Real.log X)) := hrange
      _ ≤ cExc * Real.sqrt (Real.log X / Real.log (Real.log X)) :=
        mul_le_mul_of_nonneg_right hcExc' hsqrt
  have hsave : c / θ ^ 2 ≤ ((1 : ℝ) / 6400) / (uniformQ θ : ℝ) ^ 2 := by
    have hsq : (uniformQ θ : ℝ) ^ 2 ≤ θ ^ 2 :=
      pow_le_pow_left₀ hQpos.le hQle _
    have hqSq : 0 < (uniformQ θ : ℝ) ^ 2 := sq_pos_of_pos hQpos
    have hθSq : 0 < θ ^ 2 := sq_pos_of_pos hθpos
    apply (div_le_div_iff₀ hθSq hqSq).2
    calc
      c * (uniformQ θ : ℝ) ^ 2 ≤
          ((1 : ℝ) / 6400) * (uniformQ θ : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hcSave hqSq.le
      _ ≤ ((1 : ℝ) / 6400) * θ ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (by norm_num)
  have hexp :
      1 - ((1 : ℝ) / 6400) / (uniformQ θ : ℝ) ^ 2 ≤
        1 - c / θ ^ 2 := by linarith
  have hpow := Real.rpow_le_rpow_of_exponent_le hXone hexp
  calc
    (paperExceptionalCount θ X : ℝ) ≤ E θ X := paperExceptionalCount_le_E θ X
    _ ≤ C * X ^ (1 - ((1 : ℝ) / 6400) / (uniformQ θ : ℝ) ^ 2) :=
      hX θ hθ hAdmissible
    _ ≤ C * X ^ (1 - c / θ ^ 2) :=
      mul_le_mul_of_nonneg_left hpow hC.le

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
