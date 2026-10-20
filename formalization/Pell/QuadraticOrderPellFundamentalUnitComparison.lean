import Pell.UnitQuotientCardinality
import Pell.QuadraticOrderPellRealEmbedding
import Pell.PellEpsilonMultiplicative

/-!
# Conditional comparison of a maximal-order fundamental unit with the Pell unit

The finite quotient calculation in `UnitQuotientCardinality` gives a bounded
power of every maximal-order unit in the standard Pell subgroup.  This file
packages the remaining order-theoretic input as an explicit *real fundamental
unit model*, and proves the resulting numerical comparison
`eta ≤ epsilon ≤ eta ^ 6`.

The model is deliberately an input: Mathlib's general Dirichlet-unit API does
not presently specialize its arbitrary fundamental system to the concrete
positive generator of a real quadratic order, nor identify the torsion units
there with `{±1}`.  Thus this module proves the exact bridge once those two
facts have been supplied, without silently treating them as axioms.
-/

namespace PellPaper

noncomputable section

/-- A chosen positive generator for a real-order unit group, together with a
real evaluation.  The last field is the source normalization
`O^× = {± etaUnit^n}`. -/
structure FundamentalUnitRealModel (R : Type*) [CommRing R]
    (realEval : R →+* ℝ) where
  etaUnit : Rˣ
  eta : ℝ
  eta_eval : realEval ((etaUnit : Rˣ) : R) = eta
  eta_one_lt : 1 < eta
  signed_zpow : ∀ u : Rˣ, ∃ n : ℤ,
    u = etaUnit ^ n ∨ u = -(etaUnit ^ n)

/-- Restriction of the explicitly chosen positive real embedding of the
rational quadratic algebra to its ring of integers. -/
noncomputable def quadraticOrderPellRealEval (d : ℤ) (hd : 0 ≤ d)
    [Fact (rationalQuadraticAlgebraNoRationalRoot d)] :
    NumberField.RingOfIntegers (rationalQuadraticAlgebra d) →+* ℝ :=
  (rationalQuadraticAlgebraRealEmbedding d hd).toRingHom.comp
    (algebraMap (NumberField.RingOfIntegers (rationalQuadraticAlgebra d))
      (rationalQuadraticAlgebra d))

/-- Under the restricted real embedding, the concrete embedded Pell unit has
real value `epsilon`. -/
theorem quadraticOrderPellRealEval_pellUnit
    {d : ℤ} (hd : 0 ≤ d) [Fact (rationalQuadraticAlgebraNoRationalRoot d)]
    (a : Pell.Solution₁ d) :
    quadraticOrderPellRealEval d hd
      ((quadraticOrderPellUnitEmbedding d a :
        (NumberField.RingOfIntegers (rationalQuadraticAlgebra d))ˣ) :
          NumberField.RingOfIntegers (rationalQuadraticAlgebra d)) = epsilon a := by
  simpa [quadraticOrderPellRealEval] using
    rationalQuadraticAlgebraRealEmbedding_quadraticOrderPellUnit hd a

/-- Evaluating an integral power of a unit may be done after evaluating the
unit.  We phrase this through `Units.map` because a ring homomorphism need not
preserve arbitrary inverses, whereas it does preserve units. -/
private theorem realEval_unit_zpow
    {R : Type*} [CommRing R] (realEval : R →+* ℝ) (u : Rˣ) (n : ℤ) :
    realEval ((u ^ n : Rˣ) : R) = realEval (u : R) ^ n := by
  calc
    realEval ((u ^ n : Rˣ) : R) =
        ((Units.map realEval.toMonoidHom (u ^ n) : ℝˣ) : ℝ) :=
      (Units.coe_map realEval.toMonoidHom (u ^ n)).symm
    _ = ((Units.map realEval.toMonoidHom u : ℝˣ) ^ n : ℝˣ) := by
      rw [(Units.map realEval.toMonoidHom).map_zpow]
    _ = ((Units.map realEval.toMonoidHom u : ℝˣ) : ℝ) ^ n :=
      Units.val_zpow_eq_zpow_val _ _
    _ = realEval (u : R) ^ n := by
      rw [Units.coe_map]
      rfl

/-- The corresponding elementary statement for natural powers. -/
private theorem realEval_unit_pow
    {R : Type*} [CommRing R] (realEval : R →+* ℝ) (u : Rˣ) (n : ℕ) :
    realEval ((u ^ n : Rˣ) : R) = realEval (u : R) ^ n := by
  rw [Units.val_pow_eq_pow_val, map_pow]

/-- Evaluation commutes with the sign of a unit. -/
private theorem realEval_neg_unit
    {R : Type*} [CommRing R] (realEval : R →+* ℝ) (u : Rˣ) :
    realEval ((-u : Rˣ) : R) = -realEval (u : R) := by
  rw [Units.val_neg]
  exact map_neg realEval (u : R)

/-- A positive real which is a signed integral power of a positive generator
is at least that generator. -/
private theorem eta_le_of_one_lt_and_eq_zpow_or_neg_zpow
    {eta epsilon : ℝ} (heta : 1 < eta) (hepsilon : 1 < epsilon)
    {n : ℤ} (h : epsilon = eta ^ n ∨ epsilon = -(eta ^ n)) :
    eta ≤ epsilon := by
  rcases h with h | h
  · have hn : 0 < n := by
      rw [h] at hepsilon
      exact (one_lt_zpow_iff_right₀ heta).mp hepsilon
    have hpow : eta ^ (1 : ℤ) ≤ eta ^ n :=
      (zpow_le_zpow_iff_right₀ heta).mpr (by omega)
    simpa [h] using hpow
  · have hpowpos : 0 < eta ^ n := zpow_pos (zero_lt_one.trans heta) n
    rw [h] at hepsilon
    linarith

/-- If a bounded positive power of `eta` is a signed integral power of
`epsilon`, then `epsilon` is at most `eta ^ 6`. -/
private theorem epsilon_le_eta_pow_six_of_bounded_descent
    {eta epsilon : ℝ} (heta : 1 < eta) (hepsilon : 1 < epsilon)
    {j : ℕ} (hjpos : 1 ≤ j) (hjle : j ≤ 3)
    {n : ℤ}
    (h : eta ^ (2 * j) = epsilon ^ n ∨ eta ^ (2 * j) = -(epsilon ^ n)) :
    epsilon ≤ eta ^ 6 := by
  have hleft : 1 < eta ^ (2 * j) :=
    one_lt_pow₀ heta (by omega)
  rcases h with h | h
  · have hn : 0 < n := by
      rw [h] at hleft
      exact (one_lt_zpow_iff_right₀ hepsilon).mp hleft
    have hfirst : epsilon ≤ eta ^ (2 * j) := by
      have hpow : epsilon ^ (1 : ℤ) ≤ epsilon ^ n :=
        (zpow_le_zpow_iff_right₀ hepsilon).mpr (by omega)
      simpa [h] using hpow
    exact hfirst.trans (pow_le_pow_right₀ heta.le (by omega))
  · have hpowpos : 0 < epsilon ^ n := zpow_pos (zero_lt_one.trans hepsilon) n
    rw [h] at hleft
    linarith

/-- The abstract comparison lemma.  It separates the finite-index/descent
input from the choice of a positive fundamental maximal-order unit. -/
theorem FundamentalUnitRealModel.eta_le_pellValue_le_eta_pow_six
    {R : Type*} [CommRing R] (realEval : R →+* ℝ)
    (model : FundamentalUnitRealModel R realEval)
    (pellUnit : Rˣ) (epsilon : ℝ)
    (hpell_eval : realEval ((pellUnit : Rˣ) : R) = epsilon)
    (hepsilon : 1 < epsilon)
    (hdescent : ∃ j : ℕ, 1 ≤ j ∧ j ≤ 3 ∧ ∃ n : ℤ,
      model.etaUnit ^ (2 * j) = pellUnit ^ n ∨
      model.etaUnit ^ (2 * j) = -(pellUnit ^ n)) :
    model.eta ≤ epsilon ∧ epsilon ≤ model.eta ^ 6 := by
  obtain ⟨n0, hpell | hpell⟩ := model.signed_zpow pellUnit
  · have hpell_real : epsilon = model.eta ^ n0 := by
      have hval := congrArg (fun u : Rˣ => realEval (u : R)) hpell
      calc
        epsilon = realEval (pellUnit : R) := hpell_eval.symm
        _ = realEval ((model.etaUnit ^ n0 : Rˣ) : R) := hval
        _ = model.eta ^ n0 := by
          rw [realEval_unit_zpow, model.eta_eval]
    have hlower : model.eta ≤ epsilon :=
      eta_le_of_one_lt_and_eq_zpow_or_neg_zpow model.eta_one_lt hepsilon
        (Or.inl hpell_real)
    obtain ⟨j, hjpos, hjle, n, hdescent | hdescent⟩ := hdescent
    · have hdescent_real : model.eta ^ (2 * j) = epsilon ^ n := by
        have hval := congrArg (fun u : Rˣ => realEval (u : R)) hdescent
        rw [realEval_unit_pow, realEval_unit_zpow, model.eta_eval, hpell_eval] at hval
        exact hval
      exact ⟨hlower, epsilon_le_eta_pow_six_of_bounded_descent
        model.eta_one_lt hepsilon hjpos hjle (Or.inl hdescent_real)⟩
    · have hdescent_real : model.eta ^ (2 * j) = -(epsilon ^ n) := by
        have hval := congrArg (fun u : Rˣ => realEval (u : R)) hdescent
        rw [realEval_unit_pow, realEval_neg_unit, realEval_unit_zpow,
          model.eta_eval, hpell_eval] at hval
        exact hval
      exact ⟨hlower, epsilon_le_eta_pow_six_of_bounded_descent
        model.eta_one_lt hepsilon hjpos hjle (Or.inr hdescent_real)⟩
  · have hpell_real : epsilon = -(model.eta ^ n0) := by
      have hval := congrArg (fun u : Rˣ => realEval (u : R)) hpell
      calc
        epsilon = realEval (pellUnit : R) := hpell_eval.symm
        _ = realEval (-(model.etaUnit ^ n0 : Rˣ) : R) := hval
        _ = -realEval ((model.etaUnit ^ n0 : Rˣ) : R) := by
          exact map_neg realEval ((model.etaUnit ^ n0 : Rˣ) : R)
        _ = -(model.eta ^ n0) := by
          rw [realEval_unit_zpow, model.eta_eval]
    have hlower : model.eta ≤ epsilon :=
      eta_le_of_one_lt_and_eq_zpow_or_neg_zpow model.eta_one_lt hepsilon
        (Or.inr hpell_real)
    obtain ⟨j, hjpos, hjle, n, hdescent | hdescent⟩ := hdescent
    · have hdescent_real : model.eta ^ (2 * j) = epsilon ^ n := by
        have hval := congrArg (fun u : Rˣ => realEval (u : R)) hdescent
        rw [realEval_unit_pow, realEval_unit_zpow, model.eta_eval, hpell_eval] at hval
        exact hval
      exact ⟨hlower, epsilon_le_eta_pow_six_of_bounded_descent
        model.eta_one_lt hepsilon hjpos hjle (Or.inl hdescent_real)⟩
    · have hdescent_real : model.eta ^ (2 * j) = -(epsilon ^ n) := by
        have hval := congrArg (fun u : Rˣ => realEval (u : R)) hdescent
        rw [realEval_unit_pow, realEval_neg_unit, realEval_unit_zpow,
          model.eta_eval, hpell_eval] at hval
        exact hval
      exact ⟨hlower, epsilon_le_eta_pow_six_of_bounded_descent
        model.eta_one_lt hepsilon hjpos hjle (Or.inr hdescent_real)⟩

/-- At a positive fundamental discriminant, the finite quotient theorem supplies
the bounded descent required by `eta_le_pellValue_le_eta_pow_six`.  The only
remaining input is a real-order fundamental-unit model and its compatibility
with the chosen real evaluation. -/
theorem eta_le_epsilon_le_eta_pow_six_of_positiveFundamentalDiscriminant
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ))]
    (realEval : NumberField.RingOfIntegers
      (rationalQuadraticAlgebra (D : ℤ)) →+* ℝ)
    (model : FundamentalUnitRealModel
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))) realEval)
    {a : Pell.Solution₁ (D : ℤ)} (ha : Pell.IsFundamental a)
    (hpell_eval : realEval
      ((quadraticOrderPellUnitEmbedding (D : ℤ) a :
        (NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ)))ˣ) :
          NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))) = epsilon a) :
    model.eta ≤ epsilon a ∧ epsilon a ≤ model.eta ^ 6 := by
  apply FundamentalUnitRealModel.eta_le_pellValue_le_eta_pow_six realEval model
    (quadraticOrderPellUnitEmbedding (D : ℤ) a) (epsilon a) hpell_eval
    (one_lt_epsilon_of_isFundamental ha)
  obtain ⟨j, hjpos, hjle, hmem⟩ :=
    exists_j_le_three_quadraticOrderPellUnitEmbedding_pow_two_mul_mem_range_of_positiveFundamentalDiscriminant
      D hD model.etaUnit
  rcases (mem_range_quadraticOrderPellUnitEmbedding_iff (D : ℤ) ha
    (model.etaUnit ^ (2 * j))).mp hmem with ⟨n, hn | hn⟩
  · exact ⟨j, hjpos, hjle, n, Or.inl hn⟩
  · exact ⟨j, hjpos, hjle, n, Or.inr hn⟩

/-- Concrete-real-embedding form of the comparison.  Supplying the
fundamental-unit model is now the sole order-theoretic premise; the real value
of the embedded Pell unit is verified by
`quadraticOrderPellRealEval_pellUnit`. -/
theorem eta_le_epsilon_le_eta_pow_six_of_concreteFundamentalUnitRealModel
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ))]
    (model : FundamentalUnitRealModel
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ)))
      (quadraticOrderPellRealEval (D : ℤ)
        (int_pos_of_positiveFundamentalDiscriminant hD).le))
    {a : Pell.Solution₁ (D : ℤ)} (ha : Pell.IsFundamental a) :
    model.eta ≤ epsilon a ∧ epsilon a ≤ model.eta ^ 6 := by
  exact eta_le_epsilon_le_eta_pow_six_of_positiveFundamentalDiscriminant D hD
    (quadraticOrderPellRealEval (D : ℤ)
      (int_pos_of_positiveFundamentalDiscriminant hD).le)
    model ha
    (quadraticOrderPellRealEval_pellUnit
      (int_pos_of_positiveFundamentalDiscriminant hD).le a)

end

end PellPaper
