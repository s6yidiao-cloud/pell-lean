import Pell.FiniteZpowHeightCount
import Pell.QuadraticFormIdealIntegerCoordinates
import Pell.QuadraticFormRepresentationUnitOrbit

/-!
# Height count in one quadratic-form representation-ideal fibre

Fix a nonzero value represented by one integral binary quadratic form and one
quotient ideal attached to those representations.  Relative to any selected
representation in the fibre, every other form-ideal vector differs by a unit.
After transport through a ring equivalence, a `FundamentalUnitRealModel` writes
that unit as a signed integral power of its positive generator.

The sign gives two possibilities and the exponent lies in a logarithmic
height interval.  Consequently a finite fibre in a positive absolute
real-evaluation window has size at most twice the standard exponent count.
This is the unit-orbit/height-window component of the manuscript; it
does not count the possible quotient ideals or establish the eventual dyadic
height window.
-/

namespace PellPaper
namespace IntegralBinaryQuadraticForm

noncomputable section

local instance representationUnitHeight_numberField_instance (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    NumberField (rationalQuadraticAlgebra D) :=
  rationalQuadraticAlgebra_numberField D

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

/-- A finite family of representations in one quotient-ideal fibre and one
nonzero value has at most two logarithmic unit-orbit capacities in any
positive absolute real-evaluation height window. -/
theorem card_formRepresentationQuotientIdeal_fibre_le_two_mul_log_height
    {R : Type*} [CommRing R]
    (D : ℤ) (hD : 0 ≤ D)
    (Q : IntegralBinaryQuadraticForm) (hQ : Q.discriminant = D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)]
    (ha : Q.a ≠ 0) (m : ℤ) (hm : m ≠ 0)
    (J : Ideal (NumberField.RingOfIntegers (rationalQuadraticAlgebra D)))
    (S : Finset (ℤ × ℤ))
    (e : NumberField.RingOfIntegers (rationalQuadraticAlgebra D) ≃+* R)
    (realEval : R →+* ℝ) (model : FundamentalUnitRealModel R realEval)
    (L H : ℝ) (hL : 0 < L) (hLH : L ≤ H)
    (hvalue : ∀ p ∈ S, Q.eval p.1 p.2 = m)
    (hideal : ∀ p ∈ S,
      formRepresentationQuotientIdeal D Q hQ p.1 p.2 = J)
    (hheight : ∀ p ∈ S,
      L ≤ |realEval (e (formIdealVector D Q hQ p.1 p.2))| ∧
        |realEval (e (formIdealVector D Q hQ p.1 p.2))| ≤ H) :
    (S.card : ℝ) ≤
      2 * (1 + Real.log (H / L) / Real.log model.eta) := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hS
  · have hnonneg : 0 ≤
        1 + Real.log (H / L) / Real.log model.eta := by
      simpa using card_finset_zpow_height_le ∅ model.eta 1 L H
        model.eta_one_lt zero_lt_one hL hLH (by simp)
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  · obtain ⟨r0, hr0⟩ := hS
    let r : S := ⟨r0, hr0⟩
    let beta : ℤ × ℤ → R := fun p =>
      e (formIdealVector D Q hQ p.1 p.2)
    let signedPower : ℤ × Bool → R := fun c =>
      if c.2 then -((model.etaUnit ^ c.1 : Rˣ) : R)
      else ((model.etaUnit ^ c.1 : Rˣ) : R)
    have horbit : ∀ z : S, ∃ c : ℤ × Bool,
        beta z = beta r * signedPower c := by
      intro z
      have hvalueEq : Q.eval r.val.1 r.val.2 = Q.eval z.val.1 z.val.2 :=
        (hvalue r r.property).trans (hvalue z z.property).symm
      have hvalue0 : Q.eval r.val.1 r.val.2 ≠ 0 := by
        rw [hvalue r r.property]
        exact hm
      have hidealEq :
          formRepresentationQuotientIdeal D Q hQ r.val.1 r.val.2 =
            formRepresentationQuotientIdeal D Q hQ z.val.1 z.val.2 :=
        (hideal r r.property).trans (hideal z z.property).symm
      obtain ⟨u, _, _, hu, _⟩ :=
        exists_norm_one_signed_rankOneFundamentalUnit_orbit
          D hD Q hQ ha hvalueEq hvalue0 hidealEq
      let v : Rˣ := Units.map e.toMonoidHom u
      have hbeta : beta z = beta r * (v : R) := by
        calc
          beta z = e (formIdealVector D Q hQ z.val.1 z.val.2) := rfl
          _ = e (formIdealVector D Q hQ r.val.1 r.val.2 *
              (u : NumberField.RingOfIntegers
                (rationalQuadraticAlgebra D))) := congrArg e hu.symm
          _ = e (formIdealVector D Q hQ r.val.1 r.val.2) *
              e (u : NumberField.RingOfIntegers
                (rationalQuadraticAlgebra D)) := map_mul e _ _
          _ = beta r * (v : R) := by rfl
      obtain ⟨n, hn | hn⟩ := model.signed_zpow v
      · refine ⟨(n, false), ?_⟩
        calc
          beta z = beta r * (v : R) := hbeta
          _ = beta r * ((model.etaUnit ^ n : Rˣ) : R) := by rw [hn]
          _ = beta r * signedPower (n, false) := by simp [signedPower]
      · refine ⟨(n, true), ?_⟩
        calc
          beta z = beta r * (v : R) := hbeta
          _ = beta r * (-(model.etaUnit ^ n) : Rˣ) := by rw [hn]
          _ = beta r * signedPower (n, true) := by simp [signedPower]
    choose code hcode using horbit
    have hcode_injective : Function.Injective code := by
      intro z w hzw
      apply Subtype.ext
      have hbetaEq : beta z = beta w := by
        rw [hcode z, hcode w, hzw]
      have hsourceEq :
          formIdealVector D Q hQ z.val.1 z.val.2 =
            formIdealVector D Q hQ w.val.1 w.val.2 := by
        apply e.injective
        simp only [beta] at hbetaEq
        exact hbetaEq
      apply formAssociatedIdeal_int_coordinates_injective D Q hQ ha
      simpa only [formIdealVector] using hsourceEq
    let C : Finset (ℤ × Bool) := Finset.univ.image code
    let E : Finset ℤ := Finset.univ.image (fun z : S => (code z).1)
    have hCcard : C.card = S.card := by
      dsimp only [C]
      rw [Finset.card_image_of_injective _ hcode_injective]
      exact Finset.card_attach
    have hCsub : C ⊆ E.product (Finset.univ : Finset Bool) := by
      intro c hc
      obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hc
      exact Finset.mem_product.mpr
        ⟨Finset.mem_image.mpr ⟨z, Finset.mem_univ _, rfl⟩,
          Finset.mem_univ _⟩
    have hcardNat : S.card ≤ 2 * E.card := by
      calc
        S.card = C.card := hCcard.symm
        _ ≤ (E.product (Finset.univ : Finset Bool)).card :=
          Finset.card_le_card hCsub
        _ = E.card * 2 := by simp
        _ = 2 * E.card := Nat.mul_comm _ _
    have hheightCode : ∀ z : S,
        |realEval (beta z)| =
          |realEval (beta r)| * model.eta ^ (code z).1 := by
      intro z
      have hetaPos : 0 < model.eta := zero_lt_one.trans model.eta_one_lt
      have hpowPos : 0 < model.eta ^ (code z).1 := zpow_pos hetaPos _
      rw [hcode z, map_mul, abs_mul]
      cases hb : (code z).2 <;>
        simp [signedPower, hb, realEval_unit_zpow, model.eta_eval,
          abs_of_pos hpowPos]
    have halpha : 0 < |realEval (beta r)| :=
      hL.trans_le (by simpa only [beta] using (hheight r r.property).1)
    have hE : ∀ n ∈ E,
        L ≤ |realEval (beta r)| * model.eta ^ n ∧
          |realEval (beta r)| * model.eta ^ n ≤ H := by
      intro n hn
      obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hn
      have hz := hheight z z.property
      rw [← hheightCode z]
      simpa only [beta] using hz
    have hEcard := card_finset_zpow_height_le E model.eta
      |realEval (beta r)| L H model.eta_one_lt halpha hL hLH hE
    calc
      (S.card : ℝ) ≤ 2 * (E.card : ℝ) := by exact_mod_cast hcardNat
      _ ≤ 2 * (1 + Real.log (H / L) / Real.log model.eta) :=
        mul_le_mul_of_nonneg_left hEcard (by norm_num)

end
end IntegralBinaryQuadraticForm
end PellPaper
