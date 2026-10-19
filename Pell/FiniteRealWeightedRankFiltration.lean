import Pell.FiniteWeightedRankFiltration
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

/-!
# Finite real weighted rank filtrations

The determinant argument assigns real logarithmic weights to a finite family
of Taylor coefficient vectors.  This module turns those weights into natural
layers at an arbitrary positive mesh size and transports the discrete
rank-filtration inequality without discarding the scale factor.

It deliberately stops at a supplied cap for the rounded filtration.  The
source-specific task of proving that cap from a real weighted monomial ball is
kept separate.
-/

namespace PellPaper

open scoped BigOperators
open Finset

universe u v w

/-- The lower mesh approximation to a nonnegative real weight. -/
noncomputable def finiteRealWeightRounded {ι : Type u} (weight : ι → ℝ) (mesh : ℝ) : ι → ℕ :=
  fun i => ⌊weight i / mesh⌋₊

/-- A rounded layer times the positive mesh does not exceed the original
weight. -/
theorem finiteRealWeightRounded_mul_mesh_le
    {ι : Type u} (weight : ι → ℝ) (mesh : ℝ) (hmesh : 0 < mesh)
    (hweight : ∀ i, 0 ≤ weight i) (i : ι) :
    (finiteRealWeightRounded weight mesh i : ℝ) * mesh ≤ weight i := by
  unfold finiteRealWeightRounded
  have hdiv : 0 ≤ weight i / mesh := div_nonneg (hweight i) hmesh.le
  exact (le_div_iff₀ hmesh).mp (Nat.floor_le hdiv)

/-- Summing lower mesh approximations preserves a lower bound after restoring
the mesh factor. -/
theorem sum_finiteRealWeightRounded_mul_mesh_le
    {ι : Type u} [Fintype ι] (weight : ι → ℝ) (mesh : ℝ) (hmesh : 0 < mesh)
    (hweight : ∀ i, 0 ≤ weight i) :
    (∑ i, (finiteRealWeightRounded weight mesh i : ℝ)) * mesh ≤ ∑ i, weight i := by
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  exact finiteRealWeightRounded_mul_mesh_le weight mesh hmesh hweight i

/-- The span of a family whose real weights lie below a real threshold. -/
noncomputable def finiteRealWeightFilteredSpan
    {K : Type v} {V : Type w} [Field K] [AddCommGroup V] [Module K V]
    {ι : Type u} (f : ι → V) (weight : ι → ℝ) (R : ℝ) : Submodule K V :=
  Submodule.span K (Set.range (fun i : {i : ι // weight i ≤ R} => f i.1))

/-- A rounded natural layer is contained in the next real mesh threshold. -/
theorem finiteWeightFilteredSpan_rounded_le_realWeightFilteredSpan
    {K : Type v} {V : Type w} [Field K] [AddCommGroup V] [Module K V]
    {ι : Type u} (f : ι → V) (weight : ι → ℝ) (mesh : ℝ)
    (hmesh : 0 < mesh) (hweight : ∀ i, 0 ≤ weight i) (n : ℕ) :
    finiteWeightFilteredSpan (K := K) f (finiteRealWeightRounded weight mesh) n ≤
      finiteRealWeightFilteredSpan (K := K) f weight (((n + 1 : ℕ) : ℝ) * mesh) := by
  unfold finiteWeightFilteredSpan finiteRealWeightFilteredSpan
  refine Submodule.span_le.mpr ?_
  rintro x ⟨i, rfl⟩
  apply Submodule.subset_span
  refine ⟨⟨i.1, ?_⟩, rfl⟩
  have hdiv_nonneg : 0 ≤ weight i.1 / mesh :=
    div_nonneg (hweight i.1) hmesh.le
  have hfloor_lt : ⌊weight i.1 / mesh⌋₊ < n + 1 :=
    Nat.lt_succ_iff.mpr i.2
  have hdiv_lt : weight i.1 / mesh < ((n + 1 : ℕ) : ℝ) :=
    (Nat.floor_lt hdiv_nonneg).mp hfloor_lt
  exact (div_lt_iff₀ hmesh).mp hdiv_lt |>.le

/-- Consequently, filtered rank for rounded weights is bounded by filtered
rank at the next real mesh threshold. -/
theorem finrank_finiteWeightFilteredSpan_rounded_le_realWeightFilteredSpan
    {K : Type v} {V : Type w} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {ι : Type u} (f : ι → V) (weight : ι → ℝ)
    (mesh : ℝ) (hmesh : 0 < mesh) (hweight : ∀ i, 0 ≤ weight i) (n : ℕ) :
    Module.finrank K
      (finiteWeightFilteredSpan (K := K) f
        (finiteRealWeightRounded weight mesh) n) ≤
      Module.finrank K
        (finiteRealWeightFilteredSpan (K := K) f weight
          (((n + 1 : ℕ) : ℝ) * mesh)) :=
  Submodule.finrank_mono
    (finiteWeightFilteredSpan_rounded_le_realWeightFilteredSpan
      (K := K) f weight mesh hmesh hweight n)

/-- **Scaled real weighted rank-filtration bound.**  A finite independent
family with nonnegative real weights has total weight at least `mesh` times
the discrete rank deficits of its lower rounded layers. -/
theorem totalRealWeight_ge_scaledRoundedRankCapDeficit
    {K : Type v} {V : Type w} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {ι : Type u} [Fintype ι]
    (f : ι → V) (weight : ι → ℝ) (mesh : ℝ) (rankCap : ℕ → ℕ)
    (hlin : LinearIndependent K f) (hmesh : 0 < mesh)
    (hweight : ∀ i, 0 ≤ weight i) (Q : ℕ)
    (hcap : ∀ n ∈ Finset.range Q,
      Module.finrank K
        (finiteWeightFilteredSpan (K := K) f
          (finiteRealWeightRounded weight mesh) n) ≤ rankCap n) :
    (∑ n ∈ Finset.range Q, ((Fintype.card ι - rankCap n : ℕ) : ℝ)) * mesh ≤
      ∑ i, weight i := by
  have hnat := totalWeight_ge_rankCapDeficit (K := K) f
    (finiteRealWeightRounded weight mesh) rankCap hlin Q hcap
  have hcast :
      ∑ n ∈ Finset.range Q, ((Fintype.card ι - rankCap n : ℕ) : ℝ) ≤
        ∑ i, (finiteRealWeightRounded weight mesh i : ℝ) := by
    exact_mod_cast hnat
  have hscaled := mul_le_mul_of_nonneg_right hcast hmesh.le
  exact hscaled.trans
    (sum_finiteRealWeightRounded_mul_mesh_le weight mesh hmesh hweight)

/-- The real-weight version of the finite greedy bound.  A rank cap at the
real thresholds `(n + 1) * mesh` supplies the cap needed for the corresponding
rounded natural layers. -/
theorem totalRealWeight_ge_scaledRealRankCapDeficit
    {K : Type v} {V : Type w} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {ι : Type u} [Fintype ι]
    (f : ι → V) (weight : ι → ℝ) (mesh : ℝ) (rankCap : ℕ → ℕ)
    (hlin : LinearIndependent K f) (hmesh : 0 < mesh)
    (hweight : ∀ i, 0 ≤ weight i) (Q : ℕ)
    (hcap : ∀ n ∈ Finset.range Q,
      Module.finrank K
        (finiteRealWeightFilteredSpan (K := K) f weight
          (((n + 1 : ℕ) : ℝ) * mesh)) ≤ rankCap n) :
    (∑ n ∈ Finset.range Q, ((Fintype.card ι - rankCap n : ℕ) : ℝ)) * mesh ≤
      ∑ i, weight i := by
  apply totalRealWeight_ge_scaledRoundedRankCapDeficit
    (K := K) f weight mesh rankCap hlin hmesh hweight Q
  intro n hn
  exact (finrank_finiteWeightFilteredSpan_rounded_le_realWeightFilteredSpan
    (K := K) f weight mesh hmesh hweight n).trans (hcap n hn)

end PellPaper
