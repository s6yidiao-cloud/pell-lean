import Pell.DirichletCharacterAbelContinuation
import Pell.ReciprocalPrefixTailBound

/-!
# Ordered reciprocal prefixes and the actual value at one

Modified adaptation of FormalPantheon, commit
`ffbb65c21afc8a36ace67720f1b0df1c63d26bd1`, file
`BoundedGaps/BoundedGaps/BombieriVinogradov/Analytic/NonprincipalLFunctionAbel.lean`.
Upstream: https://github.com/frenzymath/FormalPantheon
Apache-2.0; full license: `third_party/FormalPantheon-LICENSE`.

Changes: all external PV constants/imports are removed; the theorems use an
explicit bound `B` on actual natural character prefixes. The unnecessary
`1 < q` hypothesis is removed. Integral continuation and finite tails are
proved in the two locally checked prerequisite modules. No unordered infinite
sum at `s = 1` is asserted or used.
-/

open Asymptotics Complex Filter MeasureTheory Set
open scoped BigOperators Real Topology

namespace PellPaper

/-- Bounded natural prefixes imply that the ordered reciprocal prefixes
converge to the actual analytic Dirichlet L-value at one. -/
theorem tendsto_dirichletCharacter_reciprocalPrefix_of_prefixBound
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) (B : ℝ)
    (hprefix : ∀ N : ℕ,
      ‖∑ n ∈ Finset.Icc 1 N, chi (n : ZMod q)‖ ≤ B) :
    Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.Icc 1 N,
      chi (n : ZMod q) / (n : ℂ)) atTop
      (𝓝 (DirichletCharacter.LFunction chi (1 : ℂ))) := by
  have hq : q ≠ 1 := fun h ↦ hchi (DirichletCharacter.level_one' chi h)
  have habel := dirichletCharacter_LFunction_eq_abelIntegral_of_prefixBound
    chi hchi B hprefix (1 : ℂ) (by norm_num)
  let c : ℕ → ℂ := fun n ↦ chi (n : ZMod q)
  let f : ℝ → ℂ := fun t ↦ (t : ℂ) ^ (-(1 : ℂ))
  have hc0 : c 0 = 0 := by
    simpa [c] using chi.map_zero' hq
  have hCumulative (n : ℕ) :
      ∑ k ∈ Finset.Icc 0 n, c k = ∑ k ∈ Finset.Icc 1 n, c k := by
    rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le n), Finset.sum_cons, hc0,
      zero_add, ← Finset.Icc_add_one_left_eq_Ioc 0 n]
    norm_num
  have hfDiff : ∀ t ∈ Ici (1 : ℝ), DifferentiableAt ℝ f t := by
    intro t ht
    exact differentiableAt_id.ofReal_cpow_const
      (zero_lt_one.trans_le ht).ne' (by norm_num)
  have hfInt : LocallyIntegrableOn (deriv f) (Ici (1 : ℝ)) := by
    exact (Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi
      (integrableOn_Ioi_deriv_ofReal_cpow zero_lt_one
        (by norm_num))).locallyIntegrableOn
  have hEndpoint : Tendsto
      (fun n : ℕ ↦ f n * ∑ k ∈ Finset.Icc 0 n, c k) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (g := fun n : ℕ ↦ B / (n : ℝ))
    · exact Eventually.of_forall fun n ↦ norm_nonneg _
    · filter_upwards [eventually_gt_atTop 0] with n hn
      rw [hCumulative, norm_mul]
      have hfn : ‖f n‖ = (n : ℝ)⁻¹ := by
        change ‖(n : ℂ) ^ (-(1 : ℂ))‖ = (n : ℝ)⁻¹
        rw [Complex.cpow_neg_one, norm_inv, Complex.norm_natCast]
      rw [hfn]
      calc
        (n : ℝ)⁻¹ * ‖∑ k ∈ Finset.Icc 1 n, c k‖ ≤
            (n : ℝ)⁻¹ * B :=
          mul_le_mul_of_nonneg_left (hprefix n)
            (inv_nonneg.mpr (by positivity))
        _ = B / (n : ℝ) := by ring
    · simpa [div_eq_mul_inv] using
        ((tendsto_const_nhds (x := B)).mul
          (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)))
  have hDom :
      (fun t ↦ deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) =O[atTop]
        (fun t : ℝ ↦ t ^ (-2 : ℝ)) := by
    refine isBigO_iff.mpr ⟨B, ?_⟩
    filter_upwards [eventually_gt_atTop 1] with t ht
    rw [norm_mul, hCumulative]
    have ht0 : 0 < t := zero_lt_one.trans ht
    have hderiv : ‖deriv f t‖ = t ^ (-2 : ℝ) := by
      rw [show deriv f t =
          deriv (fun u : ℝ ↦ (u : ℂ) ^ (-(1 : ℂ))) t by rfl,
        deriv_ofReal_cpow_const ht0.ne' (by norm_num), norm_mul,
        norm_neg, norm_one, one_mul,
        Complex.norm_cpow_eq_rpow_re_of_pos ht0]
      norm_num
    rw [hderiv]
    have hgNonneg : 0 ≤ t ^ (-2 : ℝ) := Real.rpow_nonneg ht0.le _
    calc
      t ^ (-2 : ℝ) * ‖∑ k ∈ Finset.Icc 1 ⌊t⌋₊, c k‖ ≤
          t ^ (-2 : ℝ) * B :=
        mul_le_mul_of_nonneg_left (hprefix _) hgNonneg
      _ = B * ‖t ^ (-2 : ℝ)‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg hgNonneg]
        ring
  have hconv := tendsto_sum_mul_atTop_nhds_one_sub_integral₀
    (f := f) (l := 0) c hc0 hfDiff hfInt hEndpoint hDom
      (integrableAtFilter_rpow_atTop_iff.mpr (by norm_num))
  have hleft (n : ℕ) :
      (∑ k ∈ Finset.Icc 0 n, f k * c k) =
        ∑ k ∈ Finset.Icc 1 n, chi (k : ZMod q) / (k : ℂ) := by
    rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le n), Finset.sum_cons, hc0,
      mul_zero, zero_add, ← Finset.Icc_add_one_left_eq_Ioc 0 n]
    norm_num [f, c, Complex.cpow_neg_one, div_eq_mul_inv, mul_comm]
  have hright :
      0 - ∫ t in Ioi (1 : ℝ),
          deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k =
        DirichletCharacter.LFunction chi (1 : ℂ) := by
    rw [habel, one_mul, zero_sub, ← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change -(deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) = _
    rw [show deriv f t =
        deriv (fun u : ℝ ↦ (u : ℂ) ^ (-(1 : ℂ))) t by rfl,
      deriv_ofReal_cpow_const (zero_lt_one.trans ht).ne' (by norm_num),
      hCumulative]
    dsimp only [c]
    ring_nf
  rw [← hright]
  exact hconv.congr' (Eventually.of_forall hleft)

/-- The actual analytic value at one differs from its ordered prefix through
`N > 0` by at most `2 * B / N`. -/
theorem norm_LFunction_one_sub_reciprocalPrefix_le_of_prefixBound
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) (B : ℝ)
    (hprefix : ∀ Y : ℕ,
      ‖∑ n ∈ Finset.Icc 1 Y, chi (n : ZMod q)‖ ≤ B)
    (N : ℕ) (hN : 0 < N) :
    ‖DirichletCharacter.LFunction chi (1 : ℂ) -
        ∑ n ∈ Finset.Icc 1 N, chi (n : ZMod q) / (n : ℂ)‖ ≤
      2 * B / (N : ℝ) := by
  let P : ℕ → ℂ := fun Y ↦ ∑ n ∈ Finset.Icc 1 Y,
    chi (n : ZMod q) / (n : ℂ)
  have htail {Y : ℕ} (hNY : N ≤ Y) :
      P Y - P N = ∑ n ∈ Finset.Ioc N Y,
        chi (n : ZMod q) / (n : ℂ) := by
    have hunion : Finset.Icc 1 N ∪ Finset.Ioc N Y = Finset.Icc 1 Y := by
      ext n
      simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
      constructor
      · rintro (hn | hn) <;> omega
      · intro hn
        by_cases hnN : n ≤ N
        · exact Or.inl ⟨hn.1, hnN⟩
        · exact Or.inr ⟨lt_of_not_ge hnN, hn.2⟩
    have hdis : Disjoint (Finset.Icc 1 N) (Finset.Ioc N Y) := by
      rw [Finset.disjoint_left]
      intro n hncc hnoc
      simp only [Finset.mem_Icc] at hncc
      simp only [Finset.mem_Ioc] at hnoc
      omega
    change (∑ n ∈ Finset.Icc 1 Y, chi (n : ZMod q) / (n : ℂ)) -
      (∑ n ∈ Finset.Icc 1 N, chi (n : ZMod q) / (n : ℂ)) = _
    rw [← hunion, Finset.sum_union hdis]
    ring
  have hconv := tendsto_dirichletCharacter_reciprocalPrefix_of_prefixBound
    chi hchi B hprefix
  have hlim : Tendsto (fun Y ↦ ‖P Y - P N‖) atTop
      (𝓝 ‖DirichletCharacter.LFunction chi (1 : ℂ) - P N‖) :=
    (hconv.sub_const (P N)).norm
  apply le_of_tendsto hlim
  filter_upwards [eventually_ge_atTop N] with Y hNY
  rw [htail hNY]
  have hq : q ≠ 1 := fun h ↦ hchi (DirichletCharacter.level_one' chi h)
  exact norm_reciprocal_sum_Ioc_le_of_prefixBound
    (fun n ↦ chi (n : ZMod q)) (by simpa using chi.map_zero' hq)
    B hprefix N Y hN

end PellPaper
