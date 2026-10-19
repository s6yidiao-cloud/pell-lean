import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Ordered triple-factor fibres

This file isolates the elementary divisor-counting input denoted by
`tau_3` in the proof of the Friedlander--Iwaniec bilinear Jacobi-symbol
estimate.  Our convention is the source-faithful Dirichlet convolution

`tauThree = zeta * sigma 0`.

Thus `tauThree ell` counts ordered positive triples with product `ell`.
The explicit finite fibre below uses the box `[1, ell]^3`; it is empty at
`ell = 0`, and at every positive `ell` that box contains every positive
triple with product `ell`.
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

/-- The ordered three-divisor function `tau_3 = zeta * sigma 0`. -/
def tauThree : ArithmeticFunction ℕ :=
  ArithmeticFunction.zeta * ArithmeticFunction.sigma 0

/-- Ordered positive triples in `[1, ell]^3` whose product is `ell`. -/
def positiveOrderedTripleFactorFibre (ell : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.Icc 1 ell).product
    ((Finset.Icc 1 ell).product (Finset.Icc 1 ell))).filter
      (fun t ↦ t.1 * t.2.1 * t.2.2 = ell)

@[simp] theorem tauThree_zero : tauThree 0 = 0 := by
  simp [tauThree]

@[simp] theorem tauThree_one : tauThree 1 = 1 := by
  simp [tauThree]

@[simp] theorem positiveOrderedTripleFactorFibre_zero :
    positiveOrderedTripleFactorFibre 0 = ∅ := by
  simp [positiveOrderedTripleFactorFibre]

@[simp] theorem positiveOrderedTripleFactorFibre_one :
    positiveOrderedTripleFactorFibre 1 = {(1, 1, 1)} := by
  simp [positiveOrderedTripleFactorFibre]

/-- Divisor-chain data `b ∣ d ∣ ell`, used to enumerate the triple
`(ell / d, b, d / b)`. -/
private def tauThreeFactorData (ell : ℕ) : Finset (Σ _d : ℕ, ℕ) :=
  ell.divisors.sigma fun d ↦ d.divisors

private def tauThreeFactorDataToTriple
    (ell : ℕ) (x : Σ _d : ℕ, ℕ) : ℕ × ℕ × ℕ :=
  (ell / x.1, x.2, x.1 / x.2)

private def tripleToTauThreeFactorData
    (t : ℕ × ℕ × ℕ) : Σ _d : ℕ, ℕ :=
  ⟨t.2.1 * t.2.2, t.2.1⟩

private theorem card_tauThreeFactorData_eq (ell : ℕ) :
    (tauThreeFactorData ell).card = tauThree ell := by
  rw [tauThreeFactorData, Finset.card_sigma]
  unfold tauThree
  symm
  simpa only [ArithmeticFunction.natCoe_nat,
    ArithmeticFunction.sigma_zero_apply] using
    (ArithmeticFunction.coe_zeta_mul_apply
      (R := ℕ) (f := ArithmeticFunction.sigma 0) (x := ell))

/-- The explicit ordered positive triple-factor fibre has cardinality
exactly `tauThree ell`, uniformly including `ell = 0` and `ell = 1`. -/
theorem card_positiveOrderedTripleFactorFibre_eq_tauThree (ell : ℕ) :
    (positiveOrderedTripleFactorFibre ell).card = tauThree ell := by
  rcases eq_or_ne ell 0 with rfl | hell
  · simp [positiveOrderedTripleFactorFibre, tauThree]
  have hellPos : 0 < ell := Nat.pos_of_ne_zero hell
  rw [← card_tauThreeFactorData_eq ell]
  symm
  apply Finset.card_bij'
      (fun x _ ↦ tauThreeFactorDataToTriple ell x)
      (fun t _ ↦ tripleToTauThreeFactorData t)
  · intro x hx
    rw [tauThreeFactorData, Finset.mem_sigma] at hx
    obtain ⟨hd, hb⟩ := hx
    have hdDvd : x.1 ∣ ell := Nat.dvd_of_mem_divisors hd
    have hbDvd : x.2 ∣ x.1 := Nat.dvd_of_mem_divisors hb
    have hdPos : 0 < x.1 := Nat.pos_of_mem_divisors hd
    have hbPos : 0 < x.2 := Nat.pos_of_mem_divisors hb
    have hquotDPos : 0 < x.1 / x.2 :=
      Nat.div_pos (Nat.le_of_dvd hdPos hbDvd) hbPos
    have hquotEllPos : 0 < ell / x.1 :=
      Nat.div_pos (Nat.le_of_dvd hellPos hdDvd) hdPos
    have hdLe : x.1 ≤ ell := Nat.le_of_dvd hellPos hdDvd
    have hbLe : x.2 ≤ ell := (Nat.le_of_dvd hdPos hbDvd).trans hdLe
    have hquotDLe : x.1 / x.2 ≤ ell := (Nat.div_le_self _ _).trans hdLe
    have hquotEllLe : ell / x.1 ≤ ell := Nat.div_le_self _ _
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hquotEllPos, hquotEllLe⟩,
      Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hbPos, hbLe⟩,
        Finset.mem_Icc.mpr ⟨hquotDPos, hquotDLe⟩⟩⟩, ?_⟩
    dsimp only [tauThreeFactorDataToTriple]
    calc
      ell / x.1 * x.2 * (x.1 / x.2) = ell / x.1 * x.1 := by
        rw [mul_assoc, Nat.mul_div_cancel' hbDvd]
      _ = ell := Nat.div_mul_cancel hdDvd
  · intro t ht
    obtain ⟨htBox, htProd⟩ := Finset.mem_filter.mp ht
    obtain ⟨haMem, hbcMem⟩ := Finset.mem_product.mp htBox
    obtain ⟨hbMem, hcMem⟩ := Finset.mem_product.mp hbcMem
    obtain ⟨haPos, _haLe⟩ := Finset.mem_Icc.mp haMem
    obtain ⟨hbPos, _hbLe⟩ := Finset.mem_Icc.mp hbMem
    obtain ⟨hcPos, _hcLe⟩ := Finset.mem_Icc.mp hcMem
    have hbcDvd : t.2.1 * t.2.2 ∣ ell := by
      refine ⟨t.1, ?_⟩
      rw [← htProd]
      ring
    have hbcNe : t.2.1 * t.2.2 ≠ 0 :=
      Nat.mul_ne_zero (Nat.one_le_iff_ne_zero.mp hbPos)
        (Nat.one_le_iff_ne_zero.mp hcPos)
    have hbDvd : t.2.1 ∣ t.2.1 * t.2.2 := dvd_mul_right _ _
    rw [tauThreeFactorData, Finset.mem_sigma]
    exact ⟨Nat.mem_divisors.mpr ⟨hbcDvd, hell⟩,
      Nat.mem_divisors.mpr ⟨hbDvd, hbcNe⟩⟩
  · intro x hx
    rw [tauThreeFactorData, Finset.mem_sigma] at hx
    obtain ⟨_hd, hb⟩ := hx
    have hbDvd : x.2 ∣ x.1 := Nat.dvd_of_mem_divisors hb
    apply Sigma.ext
    · exact Nat.mul_div_cancel' hbDvd
    · rfl
  · intro t ht
    obtain ⟨htBox, htProd⟩ := Finset.mem_filter.mp ht
    obtain ⟨_haMem, hbcMem⟩ := Finset.mem_product.mp htBox
    obtain ⟨hbMem, hcMem⟩ := Finset.mem_product.mp hbcMem
    obtain ⟨hbPos, _hbLe⟩ := Finset.mem_Icc.mp hbMem
    obtain ⟨hcPos, _hcLe⟩ := Finset.mem_Icc.mp hcMem
    apply Prod.ext
    · dsimp only [tauThreeFactorDataToTriple, tripleToTauThreeFactorData]
      have hellFactor : ell = t.1 * (t.2.1 * t.2.2) := by
        rw [← htProd]
        ring
      rw [hellFactor]
      exact Nat.mul_div_left t.1 (Nat.mul_pos hbPos hcPos)
    · apply Prod.ext
      · rfl
      · dsimp only [tauThreeFactorDataToTriple, tripleToTauThreeFactorData]
        simpa [Nat.mul_comm] using Nat.mul_div_left t.2.2 hbPos

/-- Ordered positive triples in `[1,A]^3` whose product is `ell`.  This is
the fibre that occurs after grouping the cubic expansion in the
Friedlander--Iwaniec argument. -/
def positiveOrderedTripleFactorFibreUpTo
    (A ell : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.Icc 1 A).product
    ((Finset.Icc 1 A).product (Finset.Icc 1 A))).filter
      (fun t ↦ t.1 * t.2.1 * t.2.2 = ell)

/-- A box-bounded ordered triple-factor fibre has at most `tauThree ell`
elements.  No positivity hypothesis on `A` or `ell` is needed. -/
theorem card_positiveOrderedTripleFactorFibreUpTo_le_tauThree
    (A ell : ℕ) :
    (positiveOrderedTripleFactorFibreUpTo A ell).card ≤ tauThree ell := by
  have hsubset : positiveOrderedTripleFactorFibreUpTo A ell ⊆
      positiveOrderedTripleFactorFibre ell := by
    intro t ht
    obtain ⟨htBox, htProd⟩ := Finset.mem_filter.mp ht
    obtain ⟨haMem, hbcMem⟩ := Finset.mem_product.mp htBox
    obtain ⟨hbMem, hcMem⟩ := Finset.mem_product.mp hbcMem
    obtain ⟨haPos, _haLe⟩ := Finset.mem_Icc.mp haMem
    obtain ⟨hbPos, _hbLe⟩ := Finset.mem_Icc.mp hbMem
    obtain ⟨hcPos, _hcLe⟩ := Finset.mem_Icc.mp hcMem
    have haProd : t.1 ≤ t.1 * t.2.1 * t.2.2 :=
      (Nat.le_mul_of_pos_right t.1 hbPos).trans
        (Nat.le_mul_of_pos_right (t.1 * t.2.1) hcPos)
    have hbProd : t.2.1 ≤ t.1 * t.2.1 * t.2.2 :=
      (Nat.le_mul_of_pos_left t.2.1 haPos).trans
        (Nat.le_mul_of_pos_right (t.1 * t.2.1) hcPos)
    have hcProd : t.2.2 ≤ t.1 * t.2.1 * t.2.2 :=
      Nat.le_mul_of_pos_left t.2.2 (Nat.mul_pos haPos hbPos)
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr ⟨
      Finset.mem_Icc.mpr ⟨haPos, haProd.trans_eq htProd⟩,
      Finset.mem_product.mpr ⟨
        Finset.mem_Icc.mpr ⟨hbPos, hbProd.trans_eq htProd⟩,
        Finset.mem_Icc.mpr ⟨hcPos, hcProd.trans_eq htProd⟩⟩⟩,
      htProd⟩
  calc
    (positiveOrderedTripleFactorFibreUpTo A ell).card ≤
        (positiveOrderedTripleFactorFibre ell).card :=
      Finset.card_le_card hsubset
    _ = tauThree ell := card_positiveOrderedTripleFactorFibre_eq_tauThree ell

end

end PellPaper
