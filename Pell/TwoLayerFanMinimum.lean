import Pell.TwoLayerBasisWeightSeparation
import Pell.GeneralBidegreeSelectedRealWeightedFiltration
import Pell.TwoLayerNormalRowRank
import Pell.FiniteRealWeightFilteredCount
import Pell.FiniteRealWeightSortedDominance
import Mathlib.Tactic

/-!
# The exact minimum-weight theorem in the two-layer fan

This module proves that the standard two-row monomial basis has no larger
total logarithmic weight than any coefficient-monomial family whose
evaluation minor on `generalBidegreeGrid 1 B` is nonzero.  The proof uses the
actual parallel-line rank bound, identifies its width-`2 * ellX` shell with
the normal-form rows `j = 0,1`, applies the frozen fan-separation lemma, and
then invokes finite order-statistics dominance.  No weighted-rank assertion
is assumed as a hypothesis.
-/

namespace PellPaper

open scoped BigOperators
open Finset

private theorem generalBidegreeRealWeight_eq_twoLayerMonomialWeight
    (ellM ellX : ℝ) (m : generalBidegreeCoefficientMonomialIndex) :
    generalBidegreeRealWeight ellM ellX m =
      twoLayerMonomialWeight ellM ellX (m 0, m 1) := by
  rfl

private theorem card_filter_comp_equiv_eq
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (w : κ → ℝ) (e : ι ≃ κ) (R : ℝ) :
    (Finset.univ.filter fun i => w (e i) ≤ R).card =
      (Finset.univ.filter fun i => w i ≤ R).card := by
  classical
  let ef : {i : ι // i ∈ Finset.univ.filter fun i => w (e i) ≤ R} ≃
      {i : κ // i ∈ Finset.univ.filter fun i => w i ≤ R} :=
    { toFun := fun i => ⟨e i.1, by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact (Finset.mem_filter.mp i.2).2⟩
      invFun := fun i => ⟨e.symm i.1, by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        simpa using (Finset.mem_filter.mp i.2).2⟩
      left_inv := fun i => by
        apply Subtype.ext
        exact e.symm_apply_apply i.1
      right_inv := fun i => by
        apply Subtype.ext
        exact e.apply_symm_apply i.1 }
  rw [← Fintype.card_coe, ← Fintype.card_coe]
  exact Fintype.card_congr ef

/-- The finite sorted-dominance theorem reindexed across two equivalent
finite types. -/
private theorem sum_le_sum_of_card_filter_le_card_filter_of_equiv
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (lighter : κ → ℝ) (heavier : ι → ℝ)
    (hcount : ∀ R : ℝ,
      (Finset.univ.filter fun i => heavier i ≤ R).card ≤
        (Finset.univ.filter fun i => lighter i ≤ R).card) :
    ∑ i, lighter i ≤ ∑ i, heavier i := by
  classical
  let eFin : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let lighterFin : Fin (Fintype.card ι) → ℝ :=
    lighter ∘ (eFin.trans e)
  let heavierFin : Fin (Fintype.card ι) → ℝ := heavier ∘ eFin
  have hcountFin : ∀ R : ℝ,
      (Finset.univ.filter fun i => heavierFin i ≤ R).card ≤
        (Finset.univ.filter fun i => lighterFin i ≤ R).card := by
    intro R
    simpa only [heavierFin, lighterFin, Function.comp_apply,
      card_filter_comp_equiv_eq heavier eFin R,
      card_filter_comp_equiv_eq lighter (eFin.trans e) R] using hcount R
  have hsum := sum_le_sum_of_card_filter_le_card_filter
    lighterFin heavierFin hcountFin
  change (∑ i, lighter ((eFin.trans e) i)) ≤
    ∑ i, heavier (eFin i) at hsum
  calc
    ∑ i, lighter i = ∑ j, lighter ((eFin.trans e) j) :=
      (Equiv.sum_comp (eFin.trans e) lighter).symm
    _ ≤ ∑ j, heavier (eFin j) := hsum
    _ = ∑ i, heavier i := Equiv.sum_comp eFin heavier

private theorem card_filter_subtype_eq_filter
    {α : Type*} [DecidableEq α] (t : Finset α) (P : α → Prop)
    [DecidablePred P] :
    (Finset.univ.filter fun x : t => P x.1).card = (t.filter P).card := by
  apply Finset.card_bij (fun x _ => x.1)
  · intro x hx
    exact Finset.mem_filter.mpr
      ⟨x.2, (Finset.mem_filter.mp hx).2⟩
  · intro x hx y hy hxy
    exact Subtype.ext hxy
  · intro y hy
    refine ⟨⟨y, (Finset.mem_filter.mp hy).1⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (Finset.mem_filter.mp hy).2⟩

/-- **Exact two-layer fan minimum.**  A nonzero full coefficient minor on
`generalBidegreeGrid 1 B` selects a monomial basis whose total real weight is
at least the manuscript's standard two-layer weight. -/
theorem twoLayerWeight_le_sum_realWeight_of_selectedCoefficientMinor_ne_zero
    (B k : ℕ) (ellM ellX : ℝ)
    (hellM : 0 < ellM)
    (hkpos : 1 ≤ k) (hkB : k ≤ B)
    (hfanLower : (2 * (k : ℝ) - 1) * ellM ≤ ellX)
    (hfanUpper : ellX ≤ (2 * (k : ℝ) + 1) * ellM)
    (s : generalBidegreeGrid 1 B →
      generalBidegreeCoefficientMonomialIndex)
    (hminor :
      (generalBidegreeSelectedCoefficientEvaluationMatrix 1 B s).det ≠ 0) :
    twoLayerWeight B k ellM ellX ≤
      ∑ q, generalBidegreeRealWeight ellM ellX (s q) := by
  classical
  have hellM_nonneg : 0 ≤ ellM := hellM.le
  have hkreal : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkpos
  have hcoeff : (1 : ℝ) ≤ 2 * (k : ℝ) - 1 := by linarith
  have hell : ellM ≤ ellX := by
    calc
      ellM = 1 * ellM := by ring
      _ ≤ (2 * (k : ℝ) - 1) * ellM :=
        mul_le_mul_of_nonneg_right hcoeff hellM_nonneg
      _ ≤ ellX := hfanLower
  have hfanLower' : (((2 * k : ℕ) : ℝ) * ellM - ellM) ≤ ellX := by
    push_cast
    nlinarith
  have hfanUpper' : ellX ≤ (((2 * k + 1 : ℕ) : ℝ) * ellM) := by
    push_cast
    nlinarith
  have hlin :=
    linearIndependent_generalBidegreeSelectedCoefficientEvaluation_of_det_ne_zero
      1 B s hminor
  have hselected_normal (R : ℝ) :
      (Finset.univ.filter fun q : generalBidegreeGrid 1 B =>
          generalBidegreeRealWeight ellM ellX (s q) ≤ R).card ≤
        (twoLayerNormalRowPositiveRealWeightedBall
          ellM ellX R hellM hell).card := by
    let weight : generalBidegreeGrid 1 B → ℝ :=
      fun q => generalBidegreeRealWeight ellM ellX (s q)
    have hcardSpan :=
      card_le_finrank_finiteRealWeightFilteredSpan
        (generalBidegreeSelectedCoefficientEvaluation 1 B s) weight hlin R
    have hspanRank :=
      finrank_finiteRealWeightFilteredSpan_selectedCoefficientEvaluation_le_positiveBall
        1 B s weight ellM ellX R hellM hell (fun _ => rfl)
    have hrank :=
      generalBidegreeCoefficientEvaluationRank_positiveRealWeightedBall_le_twoLayerNormalRows
        B ellM ellX R hellM hell
    change (Finset.univ.filter fun q : generalBidegreeGrid 1 B =>
      weight q ≤ R).card ≤ _
    calc
      (Finset.univ.filter fun q : generalBidegreeGrid 1 B =>
          weight q ≤ R).card ≤
          Module.finrank ℚ
            (finiteRealWeightFilteredSpan (K := ℚ)
              (generalBidegreeSelectedCoefficientEvaluation 1 B s) weight R) :=
        hcardSpan
      _ ≤ generalBidegreeCoefficientEvaluationRank 1 B
          (generalBidegreePositiveRealWeightedBall ellM ellX R hellM hell) :=
        hspanRank
      _ ≤ (twoLayerNormalRowPositiveRealWeightedBall
          ellM ellX R hellM hell).card := hrank
  have hthreshold (R : ℝ) :
      (Finset.univ.filter fun q : generalBidegreeGrid 1 B =>
          generalBidegreeRealWeight ellM ellX (s q) ≤ R).card ≤
        ((twoLayerBasisIndices B k).filter fun ij =>
          twoLayerMonomialWeight ellM ellX ij ≤ R).card := by
    let normal := twoLayerNormalRowPositiveRealWeightedBall
      ellM ellX R hellM hell
    by_cases hmissing : ∃ m, m ∈ normal ∧
        (m 0, m 1) ∉ twoLayerBasisIndices B k
    · rcases hmissing with ⟨m, hmnormal, hmnot⟩
      have hmdata : m ∈ generalBidegreePositiveRealWeightedBall
            ellM ellX R hellM hell ∧ m 1 ≤ 1 := by
        simpa [normal, twoLayerNormalRowPositiveRealWeightedBall] using hmnormal
      have hmS := hmdata.1
      have hmj := hmdata.2
      have hmweight : twoLayerMonomialWeight ellM ellX (m 0, m 1) ≤ R := by
        rw [← generalBidegreeRealWeight_eq_twoLayerMonomialWeight]
        exact (mem_generalBidegreePositiveRealWeightedBall_iff
          ellM ellX R hellM hell m).mp hmS
      have hall : ∀ ij ∈ twoLayerBasisIndices B k,
          twoLayerMonomialWeight ellM ellX ij ≤ R := by
        intro ij hij
        exact (twoLayerBasisMonomialWeight_le_of_secondCoordinate_le_one
          B k hkB ellM ellX hellM_nonneg hfanLower' hfanUpper'
          hij hmj hmnot).trans hmweight
      have hfilter :
          (twoLayerBasisIndices B k).filter
              (fun ij => twoLayerMonomialWeight ellM ellX ij ≤ R) =
            twoLayerBasisIndices B k :=
        Finset.filter_eq_self.mpr hall
      calc
        (Finset.univ.filter fun q : generalBidegreeGrid 1 B =>
            generalBidegreeRealWeight ellM ellX (s q) ≤ R).card ≤
            (Finset.univ : Finset (generalBidegreeGrid 1 B)).card :=
          Finset.card_filter_le _ _
        _ = 2 * (B + 1) := by
          rw [Finset.card_univ, Fintype.card_coe,
            card_generalBidegreeGrid]
        _ = (twoLayerBasisIndices B k).card :=
          (card_twoLayerBasisIndices B k hkB).symm
        _ = ((twoLayerBasisIndices B k).filter fun ij =>
            twoLayerMonomialWeight ellM ellX ij ≤ R).card := by
          rw [hfilter]
    · have hnormal_basis : normal.card ≤
          ((twoLayerBasisIndices B k).filter fun ij =>
            twoLayerMonomialWeight ellM ellX ij ≤ R).card := by
        apply Finset.card_le_card_of_injOn (fun m => (m 0, m 1))
        · intro m hm
          change (m 0, m 1) ∈
            (twoLayerBasisIndices B k).filter
              (fun ij => twoLayerMonomialWeight ellM ellX ij ≤ R)
          rw [Finset.mem_filter]
          constructor
          · by_contra hmnot
            exact hmissing ⟨m, hm, hmnot⟩
          · rw [← generalBidegreeRealWeight_eq_twoLayerMonomialWeight]
            have hmdata : m ∈ generalBidegreePositiveRealWeightedBall
                ellM ellX R hellM hell ∧ m 1 ≤ 1 := by
              simpa [normal, twoLayerNormalRowPositiveRealWeightedBall] using hm
            have hmS := hmdata.1
            exact (mem_generalBidegreePositiveRealWeightedBall_iff
              ellM ellX R hellM hell m).mp hmS
        · intro m hm n hn hmn
          apply Finsupp.ext
          intro a
          fin_cases a
          · exact congrArg Prod.fst hmn
          · exact congrArg Prod.snd hmn
      exact (hselected_normal R).trans hnormal_basis
  let e : generalBidegreeGrid 1 B ≃
      {ij // ij ∈ twoLayerBasisIndices B k} :=
    Fintype.equivOfCardEq (by
      calc
        Fintype.card (generalBidegreeGrid 1 B) =
            (generalBidegreeGrid 1 B).card := Fintype.card_coe _
        _ = (1 + 1) * (B + 1) := card_generalBidegreeGrid 1 B
        _ = 2 * (B + 1) := by omega
        _ = (twoLayerBasisIndices B k).card :=
          (card_twoLayerBasisIndices B k hkB).symm
        _ = Fintype.card {ij // ij ∈ twoLayerBasisIndices B k} :=
          (Fintype.card_coe _).symm)
  have hsum := sum_le_sum_of_card_filter_le_card_filter_of_equiv e
    (fun ij : {ij // ij ∈ twoLayerBasisIndices B k} =>
      twoLayerMonomialWeight ellM ellX ij.1)
    (fun q : generalBidegreeGrid 1 B =>
      generalBidegreeRealWeight ellM ellX (s q)) (by
        intro R
        have hcard := card_filter_subtype_eq_filter
          (twoLayerBasisIndices B k)
          (fun ij => twoLayerMonomialWeight ellM ellX ij ≤ R)
        exact (hthreshold R).trans_eq hcard.symm)
  rw [Finset.sum_coe_sort,
    sum_twoLayerBasisMonomialWeight_eq_twoLayerWeight] at hsum
  exact hsum

end PellPaper
