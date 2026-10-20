import Pell.QuadraticOrderPellUnitRank

/-!
# A concrete fundamental-unit model for the positive quadratic order

Mathlib's `NumberField.Units.fundSystem` supplies arbitrary lifts of a basis
of the torsion quotient.  In rank one, its sole lift generates every unit up
to torsion.  For the positive rational quadratic algebra, the concrete real
embedding makes torsion exactly `{1, -1}`.  We orient that lift (or its inverse
and/or negative) to obtain a unit whose real value is strictly greater than
one, thereby constructing `FundamentalUnitRealModel` without an additional
fundamental-unit axiom.
-/

namespace PellPaper

noncomputable section

open scoped NumberField

open NumberField NumberField.Units

local instance fundamentalUnitModel_rationalQuadraticAlgebra_numberField_instance (d : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot d)] :
    NumberField (rationalQuadraticAlgebra d) :=
  rationalQuadraticAlgebra_numberField d

/-- A member of a Mathlib fundamental system represents a nontrivial class in
the quotient by torsion, so it is not itself torsion. -/
theorem fundSystem_not_mem_torsion
    (K : Type*) [Field K] [NumberField K]
    (i : Fin (NumberField.Units.rank K)) :
    NumberField.Units.fundSystem K i ∉ NumberField.Units.torsion K := by
  let _ : CommGroup
      ((NumberField.RingOfIntegers K)ˣ ⧸ NumberField.Units.torsion K) :=
    QuotientGroup.Quotient.commGroup _
  let _ : AddCommGroup
      (Additive ((NumberField.RingOfIntegers K)ˣ ⧸ NumberField.Units.torsion K)) :=
    Additive.addCommGroup
  let _ : Module ℤ
      (Additive ((NumberField.RingOfIntegers K)ˣ ⧸ NumberField.Units.torsion K)) :=
    AddCommGroup.toIntModule _
  intro hi
  have hq : (QuotientGroup.mk (NumberField.Units.fundSystem K i) :
      (NumberField.RingOfIntegers K)ˣ ⧸ NumberField.Units.torsion K) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hi
  have hzero : NumberField.Units.basisModTorsion K i = 0 := by
    rw [← NumberField.Units.fundSystem_mk, hq]
    rfl
  have hrepr := Module.Basis.repr_self (NumberField.Units.basisModTorsion K) i
  rw [hzero] at hrepr
  have hcoord := congrArg (fun f => f i) hrepr
  simp at hcoord

/-- The sole member of Mathlib's fundamental system when the unit rank is
one.  It is not yet oriented at the real place. -/
noncomputable def rankOneFundamentalUnit (K : Type*) [Field K] [NumberField K]
    (hrank : NumberField.Units.rank K = 1) : (NumberField.RingOfIntegers K)ˣ :=
  NumberField.Units.fundSystem K ⟨0, by omega⟩

/-- In rank one, if torsion consists of the two signs, the sole fundamental
system lift generates all units up to sign. -/
theorem rankOneFundamentalUnit_signed_zpow
    (K : Type*) [Field K] [NumberField K]
    (hrank : NumberField.Units.rank K = 1)
    (htorsion : ∀ z : (NumberField.RingOfIntegers K)ˣ,
      z ∈ NumberField.Units.torsion K → z = 1 ∨ z = -1) :
    ∀ u : (NumberField.RingOfIntegers K)ˣ, ∃ n : ℤ,
      u = (rankOneFundamentalUnit K hrank) ^ n ∨
        u = -((rankOneFundamentalUnit K hrank) ^ n) := by
  intro u
  let i0 : Fin (NumberField.Units.rank K) := ⟨0, by omega⟩
  obtain ⟨⟨z, f⟩, hu, _⟩ := NumberField.Units.exist_unique_eq_mul_prod K u
  refine ⟨f i0, ?_⟩
  have hall : ∀ i : Fin (NumberField.Units.rank K), i = i0 := by
    intro i
    apply Fin.ext
    omega
  have huniv : (Finset.univ : Finset (Fin (NumberField.Units.rank K))) = {i0} := by
    ext i
    simp [hall i]
  have hprod : (∏ i, (NumberField.Units.fundSystem K i) ^ (f i)) =
      (NumberField.Units.fundSystem K i0) ^ (f i0) := by
    rw [huniv]
    simp
  rcases htorsion z z.property with hz | hz
  · left
    simpa [rankOneFundamentalUnit, i0, hprod, hz] using hu
  · right
    simpa [rankOneFundamentalUnit, i0, hprod, hz] using hu

private theorem zpow_eq_zpow_or_neg_zpow_neg
    {R : Type*} [CommRing R] (g : Rˣ) (n : ℤ) :
    g ^ n = (-g) ^ n ∨ g ^ n = -((-g) ^ n) := by
  rcases Int.even_or_odd n with hn | hn
  · left
    rw [hn.neg_zpow]
  · right
    rw [hn.neg_zpow]
    simp

private theorem signed_zpow_neg_of_signed_zpow
    {R : Type*} [CommRing R] (g : Rˣ)
    (hsigned : ∀ u : Rˣ, ∃ n : ℤ, u = g ^ n ∨ u = -(g ^ n)) :
    ∀ u : Rˣ, ∃ n : ℤ, u = (-g) ^ n ∨ u = -((-g) ^ n) := by
  intro u
  obtain ⟨n, hu | hu⟩ := hsigned u
  · rcases zpow_eq_zpow_or_neg_zpow_neg g n with h | h
    · exact ⟨n, Or.inl (hu.trans h)⟩
    · exact ⟨n, Or.inr (hu.trans h)⟩
  · rcases zpow_eq_zpow_or_neg_zpow_neg g n with h | h
    · exact ⟨n, Or.inr (hu.trans (congrArg Neg.neg h))⟩
    · exact ⟨n, Or.inl (hu.trans (by simpa using congrArg Neg.neg h))⟩

private theorem signed_zpow_inv_of_signed_zpow
    {R : Type*} [CommRing R] (g : Rˣ)
    (hsigned : ∀ u : Rˣ, ∃ n : ℤ, u = g ^ n ∨ u = -(g ^ n)) :
    ∀ u : Rˣ, ∃ n : ℤ, u = g⁻¹ ^ n ∨ u = -(g⁻¹ ^ n) := by
  intro u
  obtain ⟨n, hu | hu⟩ := hsigned u
  · refine ⟨-n, Or.inl ?_⟩
    simpa [inv_zpow'] using hu
  · refine ⟨-n, Or.inr ?_⟩
    simpa [inv_zpow'] using hu

private theorem realEval_unit_inv
    {R : Type*} [CommRing R] (realEval : R →+* ℝ) (u : Rˣ) :
    realEval ((u⁻¹ : Rˣ) : R) = (realEval (u : R))⁻¹ := by
  calc
    realEval ((u⁻¹ : Rˣ) : R) =
        ((Units.map realEval.toMonoidHom (u⁻¹) : ℝˣ) : ℝ) :=
      (Units.coe_map realEval.toMonoidHom (u⁻¹)).symm
    _ = ((Units.map realEval.toMonoidHom u : ℝˣ)⁻¹ : ℝˣ) := by
      rw [(Units.map realEval.toMonoidHom).map_inv]
    _ = ((Units.map realEval.toMonoidHom u : ℝˣ) : ℝ)⁻¹ := by
      rw [Units.val_inv_eq_inv_val]
    _ = (realEval (u : R))⁻¹ := by
      rw [Units.coe_map]
      rfl

private theorem realEval_neg_unit
    {R : Type*} [CommRing R] (realEval : R →+* ℝ) (u : Rˣ) :
    realEval ((-u : Rˣ) : R) = -realEval (u : R) := by
  rw [Units.val_neg]
  exact map_neg realEval (u : R)

private theorem nonemptyFundamentalUnitRealModel_of_signedGenerator
    {R : Type*} [CommRing R] (realEval : R →+* ℝ) (g : Rˣ)
    (hzero : realEval (g : R) ≠ 0)
    (hone : realEval (g : R) ≠ 1)
    (hnegone : realEval (g : R) ≠ -1)
    (hsigned : ∀ u : Rˣ, ∃ n : ℤ, u = g ^ n ∨ u = -(g ^ n)) :
    Nonempty (FundamentalUnitRealModel R realEval) := by
  let x : ℝ := realEval (g : R)
  have hxzero : x ≠ 0 := by simpa [x] using hzero
  have hxone : x ≠ 1 := by simpa [x] using hone
  have hxnegone : x ≠ -1 := by simpa [x] using hnegone
  rcases lt_or_gt_of_ne hxzero with hxneg | hxpos
  · rcases lt_or_gt_of_ne hxnegone with hxlt | hxgt
    · refine ⟨{
        etaUnit := -g
        eta := -x
        eta_eval := ?_
        eta_one_lt := by linarith
        signed_zpow := signed_zpow_neg_of_signed_zpow g hsigned
      }⟩
      simp [x]
    · refine ⟨{
        etaUnit := -(g⁻¹)
        eta := -(x⁻¹)
        eta_eval := ?_
        eta_one_lt := ?_
        signed_zpow := signed_zpow_neg_of_signed_zpow (g⁻¹)
          (signed_zpow_inv_of_signed_zpow g hsigned)
      }⟩
      · calc
          realEval ((-(g⁻¹) : Rˣ) : R) = -realEval ((g⁻¹ : Rˣ) : R) :=
            realEval_neg_unit realEval (g⁻¹)
          _ = -(realEval (g : R))⁻¹ := by rw [realEval_unit_inv]
          _ = -(x⁻¹) := by rfl
      · have hpos : 0 < -x := by linarith
        have hlt : -x < 1 := by linarith
        have hinv : 1 < (-x)⁻¹ := (one_lt_inv₀ hpos).mpr hlt
        simpa only [neg_inv] using hinv
  · rcases lt_or_gt_of_ne hxone with hxlt | hxgt
    · refine ⟨{
        etaUnit := g⁻¹
        eta := x⁻¹
        eta_eval := ?_
        eta_one_lt := (one_lt_inv₀ hxpos).mpr hxlt
        signed_zpow := signed_zpow_inv_of_signed_zpow g hsigned
      }⟩
      simp [x]
    · exact ⟨{
        etaUnit := g
        eta := x
        eta_eval := by rfl
        eta_one_lt := hxgt
        signed_zpow := hsigned
      }⟩

private theorem rankOneFundamentalUnit_realEval_ne_one
    (d : ℤ) (hd : 0 ≤ d) [Fact (rationalQuadraticAlgebraNoRationalRoot d)]
    (hrank : NumberField.Units.rank (rationalQuadraticAlgebra d) = 1) :
    quadraticOrderPellRealEval d hd
      ((rankOneFundamentalUnit (rationalQuadraticAlgebra d) hrank :
        (NumberField.RingOfIntegers (rationalQuadraticAlgebra d))ˣ) :
          NumberField.RingOfIntegers (rationalQuadraticAlgebra d)) ≠ 1 := by
  intro h
  have hg : rankOneFundamentalUnit (rationalQuadraticAlgebra d) hrank = 1 := by
    apply Units.ext
    apply quadraticOrderPellRealEval_injective d hd
    simpa using h
  have hnot : rankOneFundamentalUnit (rationalQuadraticAlgebra d) hrank ∉
      NumberField.Units.torsion (rationalQuadraticAlgebra d) := by
    unfold rankOneFundamentalUnit
    exact fundSystem_not_mem_torsion (rationalQuadraticAlgebra d) ⟨0, by omega⟩
  apply hnot
  rw [hg]
  exact (NumberField.Units.torsion (rationalQuadraticAlgebra d)).one_mem

private theorem rankOneFundamentalUnit_realEval_ne_neg_one
    (d : ℤ) (hd : 0 ≤ d) [Fact (rationalQuadraticAlgebraNoRationalRoot d)]
    (hrank : NumberField.Units.rank (rationalQuadraticAlgebra d) = 1) :
    quadraticOrderPellRealEval d hd
      ((rankOneFundamentalUnit (rationalQuadraticAlgebra d) hrank :
        (NumberField.RingOfIntegers (rationalQuadraticAlgebra d))ˣ) :
          NumberField.RingOfIntegers (rationalQuadraticAlgebra d)) ≠ -1 := by
  intro h
  have hg : rankOneFundamentalUnit (rationalQuadraticAlgebra d) hrank = -1 := by
    apply Units.ext
    apply quadraticOrderPellRealEval_injective d hd
    simpa using h
  have hnot : rankOneFundamentalUnit (rationalQuadraticAlgebra d) hrank ∉
      NumberField.Units.torsion (rationalQuadraticAlgebra d) := by
    unfold rankOneFundamentalUnit
    exact fundSystem_not_mem_torsion (rationalQuadraticAlgebra d) ⟨0, by omega⟩
  apply hnot
  rw [hg]
  rw [NumberField.Units.torsion, CommGroup.mem_torsion]
  exact ⟨2, by norm_num, by simp [Function.IsPeriodicPt, Function.IsFixedPt]⟩

private theorem nonemptyFundamentalUnitRealModel_quadratic
    (d : ℤ) (hd : 0 ≤ d) [Fact (rationalQuadraticAlgebraNoRationalRoot d)]
    (hrank : NumberField.Units.rank (rationalQuadraticAlgebra d) = 1) :
    Nonempty (FundamentalUnitRealModel
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra d))
      (quadraticOrderPellRealEval d hd)) := by
  apply nonemptyFundamentalUnitRealModel_of_signedGenerator
    (quadraticOrderPellRealEval d hd)
    (rankOneFundamentalUnit (rationalQuadraticAlgebra d) hrank)
  · intro hevalzero
    have hvalzero :
        ((rankOneFundamentalUnit (rationalQuadraticAlgebra d) hrank :
          (NumberField.RingOfIntegers (rationalQuadraticAlgebra d))ˣ) :
            NumberField.RingOfIntegers (rationalQuadraticAlgebra d)) = 0 := by
      apply quadraticOrderPellRealEval_injective d hd
      simpa using hevalzero
    exact Units.ne_zero _ hvalzero
  · exact rankOneFundamentalUnit_realEval_ne_one d hd hrank
  · exact rankOneFundamentalUnit_realEval_ne_neg_one d hd hrank
  · apply rankOneFundamentalUnit_signed_zpow (rationalQuadraticAlgebra d) hrank
    intro z hz
    apply quadraticOrderPellUnit_eq_one_or_neg_one_of_mem_torsion d hd z
    simpa [NumberField.Units.torsion] using hz

/-- Mathlib's rank-one fundamental system, oriented through the concrete
positive real embedding, supplies the signed-power normalization required by
`FundamentalUnitRealModel`. -/
noncomputable def quadraticOrderPellFundamentalUnitRealModel
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ))] :
    FundamentalUnitRealModel
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ)))
      (quadraticOrderPellRealEval (D : ℤ)
        (int_pos_of_positiveFundamentalDiscriminant hD).le) :=
  Classical.choice
    (nonemptyFundamentalUnitRealModel_quadratic (D : ℤ)
      (int_pos_of_positiveFundamentalDiscriminant hD).le
      (quadraticOrderPellUnitRank_eq_one_of_positiveFundamentalDiscriminant D hD))

/-- Version of `quadraticOrderPellFundamentalUnitRealModel` which derives the
nonsquare field hypothesis directly from a positive fundamental discriminant. -/
noncomputable def quadraticOrderPellFundamentalUnitRealModelAtPositiveFundamentalDiscriminant
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D) :
    let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
      ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
    FundamentalUnitRealModel
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ)))
      (quadraticOrderPellRealEval (D : ℤ)
        (int_pos_of_positiveFundamentalDiscriminant hD).le) := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  exact quadraticOrderPellFundamentalUnitRealModel D hD

/-- A short name for the concretely oriented fundamental-unit model. -/
noncomputable def concreteFundamentalUnitRealModel
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ))] :
    FundamentalUnitRealModel
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ)))
      (quadraticOrderPellRealEval (D : ℤ)
        (int_pos_of_positiveFundamentalDiscriminant hD).le) :=
  quadraticOrderPellFundamentalUnitRealModel D hD

/-- The comparison with the fundamental Pell unit, now with the concrete
Mathlib-derived fundamental-unit model rather than an external model input. -/
theorem concreteFundamentalUnitRealModel_eta_le_epsilon_le_eta_pow_six
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ))]
    {a : Pell.Solution₁ (D : ℤ)} (ha : Pell.IsFundamental a) :
    (concreteFundamentalUnitRealModel D hD).eta ≤ epsilon a ∧
      epsilon a ≤ (concreteFundamentalUnitRealModel D hD).eta ^ 6 := by
  exact eta_le_epsilon_le_eta_pow_six_of_concreteFundamentalUnitRealModel D hD
    (concreteFundamentalUnitRealModel D hD) ha

/-- Unconditional positive-fundamental-discriminant form of the fundamental
unit/Pell-unit comparison.  The needed nonsquare field instance is built from
the discriminant hypothesis inside the statement. -/
theorem concreteFundamentalUnitRealModel_eta_le_epsilon_le_eta_pow_six_at_positiveFundamentalDiscriminant
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D)
    {a : Pell.Solution₁ (D : ℤ)} (ha : Pell.IsFundamental a) :
    let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
      ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
    (concreteFundamentalUnitRealModel D hD).eta ≤ epsilon a ∧
      epsilon a ≤ (concreteFundamentalUnitRealModel D hD).eta ^ 6 := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  exact concreteFundamentalUnitRealModel_eta_le_epsilon_le_eta_pow_six D hD ha

end

end PellPaper
