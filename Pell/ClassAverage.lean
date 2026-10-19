import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Nat.Squarefree

/-!
# Specification of the real-quadratic class-number average

This file records the precise target of `main.tex`, Theorem `T:field-class-average`.
It is a **specification and conditional interface**, not a formal proof of that theorem.

In particular, `ClassNumberModel.formClassNumber` is supplied data.  It is not a
definition in Mathlib of proper equivalence classes of primitive indefinite binary
quadratic forms.  Likewise, this file does not construct quadratic fields or identify
their ordinary/narrow class numbers.  A future arithmetic implementation must supply
those objects, justify their discriminant parametrization, and instantiate the model.
The analytic estimate is recorded separately as `FieldClassAverageAssertion`; no
proof of that assertion is provided here.

The verified results below concern only finite sums and the two pointwise comparison
inequalities explicitly required by the model.
-/

namespace PellPaper

noncomputable section

/-- A finite cutoff decomposition useful before the analytic estimates enter.

For nonnegative weights `L i` and parameters `r i ≥ r₀ > 0`, split at `T ≥ r₀`.
On the lower part use `1 / r i ≤ 1 / r₀`; on the upper part use
`1 / r i ≤ 1 / T`.  This elementary lemma is a finite-sum substitute for the
layer-cake integral in the paper; obtaining a strong bound for the two numerator
sums remains an analytic task. -/
theorem finite_sum_div_split {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (L r : ι → ℝ) (r₀ T : ℝ)
    (hL : ∀ i ∈ s, 0 ≤ L i) (hr : ∀ i ∈ s, r₀ ≤ r i)
    (hr₀ : 0 < r₀) (hT : r₀ ≤ T) :
    (∑ i ∈ s, L i / r i) ≤
      (∑ i ∈ s.filter fun i ↦ r i ≤ T, L i) / r₀ +
        (∑ i ∈ s.filter fun i ↦ T < r i, L i) / T := by
  classical
  have hTpos : 0 < T := hr₀.trans_le hT
  calc
    (∑ i ∈ s, L i / r i) =
        (∑ i ∈ s.filter (fun i ↦ r i ≤ T), L i / r i) +
          ∑ i ∈ s.filter (fun i ↦ ¬r i ≤ T), L i / r i := by
            rw [Finset.sum_filter_add_sum_filter_not]
    _ ≤ (∑ i ∈ s.filter (fun i ↦ r i ≤ T), L i / r₀) +
          ∑ i ∈ s.filter (fun i ↦ ¬r i ≤ T), L i / T := by
            apply add_le_add <;> apply Finset.sum_le_sum
            · intro i hi
              exact div_le_div_of_nonneg_left
                (hL i (Finset.mem_filter.mp hi).1) hr₀
                (hr i (Finset.mem_filter.mp hi).1)
            · intro i hi
              exact div_le_div_of_nonneg_left
                (hL i (Finset.mem_filter.mp hi).1) hTpos
                (lt_of_not_ge (Finset.mem_filter.mp hi).2).le
    _ = (∑ i ∈ s.filter fun i ↦ r i ≤ T, L i) / r₀ +
          (∑ i ∈ s.filter fun i ↦ T < r i, L i) / T := by
            simp only [div_eq_mul_inv, Finset.sum_mul, not_le]

/-- The usual squarefree/modulo-four characterization of the positive fundamental
discriminants of genuine quadratic fields.  The condition `1 < D` excludes the
trivial discriminant `1`.  This is an arithmetic predicate, not a theorem
identifying it with the discriminants of real quadratic fields. -/
def PositiveFundamentalDiscriminant (D : ℕ) : Prop :=
  1 < D ∧
    ((Squarefree D ∧ D % 4 = 1) ∨
      ∃ d : ℕ, D = 4 * d ∧ Squarefree d ∧ (d % 4 = 2 ∨ d % 4 = 3))

/-- A model of the ordinary class number `h(K_D)` and the proper primitive indefinite
form class number `H(D)` at positive fundamental discriminants.

The positivity and comparison fields are hypotheses of this interface.  They do not
claim that an arithmetic construction of either class number has been formalized.
Values away from positive fundamental discriminants are irrelevant to the sums. -/
structure ClassNumberModel where
  ordinaryClassNumber : ℕ → ℕ
  formClassNumber : ℕ → ℕ
  ordinaryClassNumber_pos : ∀ D, PositiveFundamentalDiscriminant D →
    0 < ordinaryClassNumber D
  formClassNumber_pos : ∀ D, PositiveFundamentalDiscriminant D →
    0 < formClassNumber D
  ordinary_le_form : ∀ D, PositiveFundamentalDiscriminant D →
    ordinaryClassNumber D ≤ formClassNumber D
  form_le_twice_ordinary : ∀ D, PositiveFundamentalDiscriminant D →
    formClassNumber D ≤ 2 * ordinaryClassNumber D

/-- Positive fundamental discriminants with the strict real cutoff `D < X`.
The natural ceiling makes this a finite set even when `X` is not an integer. -/
def fundamentalDiscriminantsBelow (X : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range ⌈X⌉₊).filter PositiveFundamentalDiscriminant

@[simp]
theorem mem_fundamentalDiscriminantsBelow {D : ℕ} {X : ℝ} :
    D ∈ fundamentalDiscriminantsBelow X ↔
      PositiveFundamentalDiscriminant D ∧ (D : ℝ) < X := by
  simp [fundamentalDiscriminantsBelow, Nat.lt_ceil, and_comm]

theorem fundamentalDiscriminantsBelow_mono {X Y : ℝ} (hXY : X ≤ Y) :
    fundamentalDiscriminantsBelow X ⊆ fundamentalDiscriminantsBelow Y := by
  intro D hD
  rcases mem_fundamentalDiscriminantsBelow.mp hD with ⟨hfund, hDX⟩
  exact mem_fundamentalDiscriminantsBelow.mpr ⟨hfund, hDX.trans_le hXY⟩

namespace ClassNumberModel

/-- Discriminant-indexed ordinary class-number sum.  Interpreting this as a sum over
real quadratic fields requires the arithmetic realization of the model. -/
def ordinaryClassSum (M : ClassNumberModel) (X : ℝ) : ℝ :=
  ∑ D ∈ fundamentalDiscriminantsBelow X, (M.ordinaryClassNumber D : ℝ)

/-- Proper primitive indefinite form class-number sum, with strict cutoff. -/
def formClassSum (M : ClassNumberModel) (X : ℝ) : ℝ :=
  ∑ D ∈ fundamentalDiscriminantsBelow X, (M.formClassNumber D : ℝ)

theorem ordinaryClassSum_nonneg (M : ClassNumberModel) (X : ℝ) :
    0 ≤ M.ordinaryClassSum X := by
  unfold ordinaryClassSum
  exact Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _

theorem formClassSum_nonneg (M : ClassNumberModel) (X : ℝ) :
    0 ≤ M.formClassSum X := by
  unfold formClassSum
  exact Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _

/-- The first inequality in `T:field-class-average`, conditional on the model's
pointwise field/form comparison. -/
theorem ordinaryClassSum_le_formClassSum (M : ClassNumberModel) (X : ℝ) :
    M.ordinaryClassSum X ≤ M.formClassSum X := by
  apply Finset.sum_le_sum
  intro D hD
  exact (Nat.cast_le (α := ℝ)).mpr
    (M.ordinary_le_form D (mem_fundamentalDiscriminantsBelow.mp hD).1)

/-- The reverse comparison costs at most the factor two already present in the model. -/
theorem formClassSum_le_twice_ordinaryClassSum (M : ClassNumberModel) (X : ℝ) :
    M.formClassSum X ≤ 2 * M.ordinaryClassSum X := by
  unfold formClassSum ordinaryClassSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro D hD
  simpa using (Nat.cast_le (α := ℝ)).mpr
    (M.form_le_twice_ordinary D (mem_fundamentalDiscriminantsBelow.mp hD).1)

theorem ordinaryClassSum_mono (M : ClassNumberModel) {X Y : ℝ} (hXY : X ≤ Y) :
    M.ordinaryClassSum X ≤ M.ordinaryClassSum Y := by
  unfold ordinaryClassSum
  apply Finset.sum_le_sum_of_subset_of_nonneg (fundamentalDiscriminantsBelow_mono hXY)
  intro D _ _
  exact Nat.cast_nonneg _

theorem formClassSum_mono (M : ClassNumberModel) {X Y : ℝ} (hXY : X ≤ Y) :
    M.formClassSum X ≤ M.formClassSum Y := by
  unfold formClassSum
  apply Finset.sum_le_sum_of_subset_of_nonneg (fundamentalDiscriminantsBelow_mono hXY)
  intro D _ _
  exact Nat.cast_nonneg _

end ClassNumberModel

/-- The exact real-valued scale `X^(3/2) * sqrt(log(log X)) / (log X)^(3/2)`.
The target assertion uses this expression only for `X ≥ 3`. -/
def classAverageScale (X : ℝ) : ℝ :=
  Real.rpow X (3 / 2) * Real.sqrt (Real.log (Real.log X)) /
    Real.rpow (Real.log X) (3 / 2)

theorem classAverageScale_nonneg {X : ℝ} (hX : 1 ≤ X) : 0 ≤ classAverageScale X := by
  unfold classAverageScale
  exact div_nonneg
    (mul_nonneg (Real.rpow_nonneg (zero_le_one.trans hX) _)
      (Real.sqrt_nonneg _))
    (Real.rpow_nonneg (Real.log_nonneg hX) _)

/-- The analytic upper-bound component of `T:field-class-average`. The other
comparison in the theorem follows from `ordinaryClassSum_le_formClassSum`. -/
def FormClassAverageUpperBound (M : ClassNumberModel) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 3 ≤ X →
    M.formClassSum X ≤ C * classAverageScale X

/-- The exact target assertion of `main.tex`, Theorem `T:field-class-average`, in a
discriminant-indexed class-number model.

The implied constant is made explicit: one positive real `C` must work for every
real `X ≥ 3`.  Both sums use `D < X`, not `D ≤ X`.  The first comparison is elementary
from the model; the upper bound is the unproved analytic target of this specification.
Instantiating this proposition with genuine class numbers additionally requires the
arithmetic realization described in the module documentation. -/
def FieldClassAverageAssertion (M : ClassNumberModel) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 3 ≤ X →
    M.ordinaryClassSum X ≤ M.formClassSum X ∧
      M.formClassSum X ≤ C * classAverageScale X

/-- Within a `ClassNumberModel`, the full target assertion is equivalent to its
analytic form-class-number upper bound: the first displayed inequality of the
paper is already a proved finite-sum consequence of the model. -/
theorem fieldClassAverageAssertion_iff_formClassAverageUpperBound (M : ClassNumberModel) :
    FieldClassAverageAssertion M ↔ FormClassAverageUpperBound M := by
  constructor
  · rintro ⟨C, hC, hbound⟩
    exact ⟨C, hC, fun X hX ↦ (hbound X hX).2⟩
  · rintro ⟨C, hC, hbound⟩
    exact ⟨C, hC, fun X hX ↦
      ⟨M.ordinaryClassSum_le_formClassSum X, hbound X hX⟩⟩

/-- A named alias for the formal target corresponding to
`T:field-class-average`.  It remains a target proposition until a genuine
arithmetic model and the analytic inputs of the manuscript are formalized. -/
abbrev FieldClassAverageTheorem (M : ClassNumberModel) : Prop :=
  FieldClassAverageAssertion M

end

end PellPaper
