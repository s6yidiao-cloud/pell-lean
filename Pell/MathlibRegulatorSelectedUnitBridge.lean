import Pell.QuadraticOrderPellFundamentalUnitModel
import Pell.QuadraticAlgebraDedekindZetaResidue
import Mathlib.NumberTheory.NumberField.Units.Regulator

/-!
# A rank-one selected-unit bridge for Mathlib's regulator

Mathlib defines `NumberField.Units.regulator` as the covolume of the full
unit lattice.  A `FundamentalUnitRealModel` in this project instead gives a
selected positive unit and a signed-power description of all units.  This
file proves the group-theoretic part of the connection: in rank one, the
selected unit has the same `regOfFamily` as Mathlib's regulator.

The generic endpoint below makes the required infinite-place presentation
explicit.  The final specialization supplies that presentation for the
positive rational quadratic algebra, identifying Mathlib's regulator with
the selected unit logarithm.  No class-number or headline theorem is
asserted here.
-/

namespace PellPaper

noncomputable section

set_option maxHeartbeats 1000000

open NumberField NumberField.Units

/-- A rank-one signed generator together with torsion generates the full
unit group.  This is the exact group-theoretic input needed to compare its
one-element `regOfFamily` with Mathlib's full regulator. -/
theorem closure_range_const_sup_torsion_eq_top_of_rank_one_signed_zpow
    (K : Type*) [Field K] [NumberField K]
    (hrank : NumberField.Units.rank K = 1)
    (etaUnit : (NumberField.RingOfIntegers K)ˣ)
    (hsigned : ∀ u : (NumberField.RingOfIntegers K)ˣ, ∃ n : ℤ,
      u = etaUnit ^ n ∨ u = -(etaUnit ^ n)) :
    Subgroup.closure (Set.range (fun _ : Fin (NumberField.Units.rank K) ↦ etaUnit)) ⊔
        NumberField.Units.torsion K = ⊤ := by
  let i0 : Fin (NumberField.Units.rank K) := ⟨0, by omega⟩
  let S : Subgroup (NumberField.RingOfIntegers K)ˣ :=
    Subgroup.closure (Set.range (fun _ : Fin (NumberField.Units.rank K) ↦ etaUnit)) ⊔
      NumberField.Units.torsion K
  apply top_unique
  intro u _
  obtain ⟨n, hu | hu⟩ := hsigned u
  · rw [hu]
    have heta : etaUnit ∈ S := by
      exact (show Subgroup.closure
          (Set.range (fun _ : Fin (NumberField.Units.rank K) ↦ etaUnit)) ≤ S from le_sup_left)
        (Subgroup.subset_closure ⟨i0, rfl⟩)
    exact S.zpow_mem heta n
  · rw [hu]
    have heta : etaUnit ∈ S := by
      exact (show Subgroup.closure
          (Set.range (fun _ : Fin (NumberField.Units.rank K) ↦ etaUnit)) ≤ S from le_sup_left)
        (Subgroup.subset_closure ⟨i0, rfl⟩)
    have hminus : (-1 : (NumberField.RingOfIntegers K)ˣ) ∈ S := by
      apply (show NumberField.Units.torsion K ≤ S from le_sup_right)
      rw [NumberField.Units.torsion, CommGroup.mem_torsion]
      exact ⟨2, by norm_num, by simp [Function.IsPeriodicPt, Function.IsFixedPt]⟩
    have hsign : -(etaUnit ^ n) = (-1 : (NumberField.RingOfIntegers K)ˣ) * etaUnit ^ n := by
      apply Units.ext
      simp
    rw [hsign]
    exact S.mul_mem hminus (S.zpow_mem heta n)

/-- In rank one, a selected unit whose signed powers exhaust the unit group
has exactly Mathlib's regulator as its one-element family regulator. -/
theorem regOfFamily_const_eq_regulator_of_rank_one_signed_zpow
    (K : Type*) [Field K] [NumberField K]
    (hrank : NumberField.Units.rank K = 1)
    (etaUnit : (NumberField.RingOfIntegers K)ˣ)
    (hsigned : ∀ u : (NumberField.RingOfIntegers K)ˣ, ∃ n : ℤ,
      u = etaUnit ^ n ∨ u = -(etaUnit ^ n)) :
    NumberField.Units.regOfFamily
      (fun _ : Fin (NumberField.Units.rank K) ↦ etaUnit) =
        NumberField.Units.regulator K := by
  let u : Fin (NumberField.Units.rank K) → (NumberField.RingOfIntegers K)ˣ :=
    fun _ ↦ etaUnit
  have htop : Subgroup.closure (Set.range u) ⊔ NumberField.Units.torsion K = ⊤ :=
    closure_range_const_sup_torsion_eq_top_of_rank_one_signed_zpow K hrank etaUnit hsigned
  have hratio := NumberField.Units.regOfFamily_div_regulator u
  rw [htop, Subgroup.index_top] at hratio
  have hreg : NumberField.Units.regulator K ≠ 0 :=
    NumberField.Units.regulator_ne_zero K
  have hfamily := (div_eq_iff hreg).mp (by simpa using hratio)
  have hfamily' : NumberField.Units.regOfFamily u = NumberField.Units.regulator K := by
    simpa using hfamily
  simpa [u] using hfamily'

/-- The finite type of infinite places other than a specified one has exactly
the unit rank.  This is a variant of Mathlib's internally chosen indexing
equivalence, exposed here so a selected real place can be retained in a
regulator formula. -/
noncomputable def infinitePlacesExceptEquivFinRank
    (K : Type*) [Field K] [NumberField K]
    (wDrop : NumberField.InfinitePlace K)
    [DecidableEq (NumberField.InfinitePlace K)] :
    {w : NumberField.InfinitePlace K // w ≠ wDrop} ≃ Fin (NumberField.Units.rank K) :=
  by
    classical
    let _ : Fintype {w : NumberField.InfinitePlace K // w = wDrop} :=
      Fintype.ofFinite _
    exact Fintype.equivOfCardEq <| by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq,
        Fintype.card_fin, NumberField.Units.rank]

/-- A fully explicit rank-one determinant presentation for a selected signed
generator.  The `honly` premise says that after omitting `wDrop`, `wKeep` is
the sole remaining infinite place.  Thus this theorem is an actual bridge to
Mathlib's `regulator`, while the caller remains responsible for identifying
`wKeep` with a concrete real embedding. -/
theorem regulator_eq_abs_mul_log_at_unique_remaining_place_of_rank_one_signed_zpow
    (K : Type*) [Field K] [NumberField K]
    (hrank : NumberField.Units.rank K = 1)
    (etaUnit : (NumberField.RingOfIntegers K)ˣ)
    (hsigned : ∀ u : (NumberField.RingOfIntegers K)ˣ, ∃ n : ℤ,
      u = etaUnit ^ n ∨ u = -(etaUnit ^ n))
    (wDrop wKeep : NumberField.InfinitePlace K)
    (hwKeep : wKeep ≠ wDrop)
    (honly : ∀ w : NumberField.InfinitePlace K, w ≠ wDrop → w = wKeep) :
    NumberField.Units.regulator K =
      |(wKeep.mult : ℝ) * Real.log (wKeep (etaUnit : K))| := by
  classical
  let u : Fin (NumberField.Units.rank K) → (NumberField.RingOfIntegers K)ˣ :=
    fun _ ↦ etaUnit
  let e := infinitePlacesExceptEquivFinRank K wDrop
  let q : {w : NumberField.InfinitePlace K // w ≠ wDrop} := ⟨wKeep, hwKeep⟩
  let _ : Subsingleton {w : NumberField.InfinitePlace K // w ≠ wDrop} :=
    ⟨fun a b ↦ Subtype.ext <| (honly a a.property).trans (honly b b.property).symm⟩
  calc
    NumberField.Units.regulator K = NumberField.Units.regOfFamily u := by
      symm
      simpa [u] using
        regOfFamily_const_eq_regulator_of_rank_one_signed_zpow K hrank etaUnit hsigned
    _ = |(Matrix.of fun i w : {w : NumberField.InfinitePlace K // w ≠ wDrop} ↦
        (w.val.mult : ℝ) * Real.log (w.val (u (e i) : K))).det| := by
      exact NumberField.Units.regOfFamily_eq_det u wDrop e
    _ = |(wKeep.mult : ℝ) * Real.log (wKeep (etaUnit : K))| := by
      rw [Matrix.det_eq_elem_of_subsingleton _ q]
      change |(q.val.mult : ℝ) * Real.log (q.val (etaUnit : K))| = _
      simp only [q]

/-- If the retained unique place is real and its absolute value on the
selected unit is the displayed positive real number `eta`, the preceding
determinant formula is exactly `log eta`.  The place/value hypotheses are
kept explicit because they are the real-embedding normalization not supplied
by the abstract Dirichlet-unit API. -/
theorem regulator_eq_log_of_rank_one_signed_zpow_of_unique_real_place
    (K : Type*) [Field K] [NumberField K]
    (hrank : NumberField.Units.rank K = 1)
    (etaUnit : (NumberField.RingOfIntegers K)ˣ)
    (hsigned : ∀ u : (NumberField.RingOfIntegers K)ˣ, ∃ n : ℤ,
      u = etaUnit ^ n ∨ u = -(etaUnit ^ n))
    (eta : ℝ) (heta : 1 < eta)
    (wDrop wKeep : NumberField.InfinitePlace K)
    (hwKeep : wKeep ≠ wDrop)
    (honly : ∀ w : NumberField.InfinitePlace K, w ≠ wDrop → w = wKeep)
    (hwReal : NumberField.InfinitePlace.IsReal wKeep)
    (hvalue : wKeep (etaUnit : K) = eta) :
    NumberField.Units.regulator K = Real.log eta := by
  rw [regulator_eq_abs_mul_log_at_unique_remaining_place_of_rank_one_signed_zpow
    K hrank etaUnit hsigned wDrop wKeep hwKeep honly,
    hwReal.mult_eq_one]
  simp only [Nat.cast_one, one_mul]
  rw [hvalue, abs_of_pos (Real.log_pos heta)]

/-- A `FundamentalUnitRealModel` specializes the signed-generator input of
`regulator_eq_log_of_rank_one_signed_zpow_of_unique_real_place`.  It is the
generic Mathlib-regulator-to-selected-unit bridge, with the identification of
the selected real evaluation and a chosen real infinite place retained as an
explicit hypothesis. -/
theorem regulator_eq_log_of_rank_one_fundamentalUnitRealModel_of_unique_real_place
    (K : Type*) [Field K] [NumberField K]
    (hrank : NumberField.Units.rank K = 1)
    (realEval : NumberField.RingOfIntegers K →+* ℝ)
    (model : FundamentalUnitRealModel (NumberField.RingOfIntegers K) realEval)
    (wDrop wKeep : NumberField.InfinitePlace K)
    (hwKeep : wKeep ≠ wDrop)
    (honly : ∀ w : NumberField.InfinitePlace K, w ≠ wDrop → w = wKeep)
    (hwReal : NumberField.InfinitePlace.IsReal wKeep)
    (hvalue : wKeep (model.etaUnit : K) = model.eta) :
    NumberField.Units.regulator K = Real.log model.eta := by
  exact regulator_eq_log_of_rank_one_signed_zpow_of_unique_real_place
    K hrank model.etaUnit model.signed_zpow model.eta model.eta_one_lt
    wDrop wKeep hwKeep honly hwReal hvalue

local instance mathlibRegulatorSelectedUnitBridge_rationalQuadraticAlgebra_numberField_instance
    (d : ℤ) [Fact (rationalQuadraticAlgebraNoRationalRoot d)] :
    NumberField (rationalQuadraticAlgebra d) :=
  rationalQuadraticAlgebra_numberField d

/-- The infinite place induced by the explicitly chosen positive real
embedding of the rational quadratic algebra. -/
noncomputable def rationalQuadraticAlgebraPositiveRealInfinitePlace
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ))] :
    NumberField.InfinitePlace (rationalQuadraticAlgebra (D : ℤ)) :=
  NumberField.InfinitePlace.mk
    (rationalQuadraticAlgebraComplexEmbedding (D : ℤ)
      (int_pos_of_positiveFundamentalDiscriminant hD).le)

/-- **Concrete Mathlib-regulator bridge.**  For the actual positive
fundamental quadratic algebra, Mathlib's regulator is the logarithm of the
selected oriented rank-one fundamental unit.  The proof uses the two-real-
place signature and identifies the positive place directly with the project's
explicit real embedding; it does not assert that the unit has norm `+1` (a
fundamental generator may have norm `-1`). -/
theorem rationalQuadraticAlgebra_regulator_eq_log_concreteFundamentalUnitRealModel
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ))] :
    NumberField.Units.regulator (rationalQuadraticAlgebra (D : ℤ)) =
      Real.log (concreteFundamentalUnitRealModel D hD).eta := by
  let wKeep : NumberField.InfinitePlace (rationalQuadraticAlgebra (D : ℤ)) :=
    rationalQuadraticAlgebraPositiveRealInfinitePlace D hD
  have hwReal : NumberField.InfinitePlace.IsReal wKeep := by
    dsimp [wKeep, rationalQuadraticAlgebraPositiveRealInfinitePlace]
    exact NumberField.InfinitePlace.isReal_mk_iff.mpr
      (rationalQuadraticAlgebraComplexEmbedding_isReal (D : ℤ)
        (int_pos_of_positiveFundamentalDiscriminant hD).le)
  have hcard : Fintype.card (NumberField.InfinitePlace
      (rationalQuadraticAlgebra (D : ℤ))) = 2 := by
    obtain ⟨hreal, hcomplex⟩ := rationalQuadraticAlgebra_signature_of_nonneg (D : ℤ)
      (int_pos_of_positiveFundamentalDiscriminant hD).le
    rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, hreal, hcomplex]
  have hcardNat : Nat.card (NumberField.InfinitePlace
      (rationalQuadraticAlgebra (D : ℤ))) = 2 := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  obtain ⟨wDrop, hDrop, hunique⟩ :=
    (Nat.card_eq_two_iff' wKeep).mp hcardNat
  have hwKeep : wKeep ≠ wDrop := hDrop.symm
  have honly : ∀ w : NumberField.InfinitePlace (rationalQuadraticAlgebra (D : ℤ)),
      w ≠ wDrop → w = wKeep := by
    intro w hw
    by_contra hwKeep'
    exact hw (hunique w hwKeep')
  have hvalue : wKeep
      ((concreteFundamentalUnitRealModel D hD).etaUnit :
        rationalQuadraticAlgebra (D : ℤ)) =
      (concreteFundamentalUnitRealModel D hD).eta := by
    have hetaEval : rationalQuadraticAlgebraRealEmbedding (D : ℤ)
        (int_pos_of_positiveFundamentalDiscriminant hD).le
        (((concreteFundamentalUnitRealModel D hD).etaUnit :
          NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))) :
          rationalQuadraticAlgebra (D : ℤ)) =
        (concreteFundamentalUnitRealModel D hD).eta := by
      simpa [quadraticOrderPellRealEval] using
        (concreteFundamentalUnitRealModel D hD).eta_eval
    change ‖Complex.ofReal
      (rationalQuadraticAlgebraRealEmbedding (D : ℤ)
        (int_pos_of_positiveFundamentalDiscriminant hD).le
        (((concreteFundamentalUnitRealModel D hD).etaUnit :
          NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))) :
          rationalQuadraticAlgebra (D : ℤ)))‖ =
      (concreteFundamentalUnitRealModel D hD).eta
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by rw [hetaEval]; linarith
        [(concreteFundamentalUnitRealModel D hD).eta_one_lt])]
    exact hetaEval
  exact regulator_eq_log_of_rank_one_fundamentalUnitRealModel_of_unique_real_place
    (rationalQuadraticAlgebra (D : ℤ))
    (quadraticOrderPellUnitRank_eq_one_of_positiveFundamentalDiscriminant D hD)
    (quadraticOrderPellRealEval (D : ℤ)
      (int_pos_of_positiveFundamentalDiscriminant hD).le)
    (concreteFundamentalUnitRealModel D hD)
    wDrop wKeep hwKeep honly hwReal hvalue

/-- Caller-instance-free version of the concrete regulator bridge, expressed
in the exact regulator wrapper used by the quadratic Dedekind-zeta
class-number formula. -/
theorem rationalQuadraticAlgebraRegulatorAtPositiveFundamentalDiscriminant_eq_log_concreteFundamentalUnitRealModel
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D) :
    rationalQuadraticAlgebraRegulatorAtPositiveFundamentalDiscriminant D hD =
      let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
        ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
      Real.log (concreteFundamentalUnitRealModel D hD).eta := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  exact rationalQuadraticAlgebra_regulator_eq_log_concreteFundamentalUnitRealModel D hD

end

end PellPaper
