import Pell.DyadicFactorSeparation
import Pell.FixedHeight

/-!
# Finite reduction of squarefree exceptions to factor tuples

Every radicand in the fixed-height dyadic exceptional set is the product of
the squarefree coordinates of a bounded positive tuple `(d,e,u,v)`.  These
tuples satisfy one of the four difference equations used in the manuscript,
and their square-part product has the height restriction coming from the
fundamental Pell unit.  Consequently the exceptional count is bounded by
the cardinality of an explicit finite set of such tuples.

This reduction does not estimate that cardinality by a power saving.  The
determinant and divisor estimates for the balanced and unbalanced parts of
this finite set remain necessary for `FixedHeightSquarefree`.
-/

namespace PellPaper

/-- A common integral coordinate bound for the positive square parts. -/
noncomputable def dyadicFactorHeight (θ : ℝ) (Y : ℕ) : ℕ :=
  ⌈((2 * Y : ℕ) : ℝ) ^ θ⌉₊

/-- The arithmetic and height conditions retained by the finite counting
reduction.  The squarefree factors are oriented by `v ≤ u`. -/
def DyadicFactorCondition (θ : ℝ) (Y d e u v : ℕ) : Prop :=
  0 < d ∧ 0 < e ∧ 0 < u ∧ 0 < v ∧
  d ≤ dyadicFactorHeight θ Y ∧ e ≤ dyadicFactorHeight θ Y ∧
  u < 2 * Y ∧ v < 2 * Y ∧
  Squarefree u ∧ Squarefree v ∧ u.Coprime v ∧
  Y ≤ u * v ∧ u * v < 2 * Y ∧ v ≤ u ∧ v ^ 2 < 2 * Y ∧
  ((e : ℤ) ^ 2 * v - (d : ℤ) ^ 2 * u = 1 ∨
    (e : ℤ) ^ 2 * v - (d : ℤ) ^ 2 * u = -1 ∨
    (e : ℤ) ^ 2 * v - (d : ℤ) ^ 2 * u = 2 ∨
    (e : ℤ) ^ 2 * v - (d : ℤ) ^ 2 * u = -2) ∧
  ((d * e : ℕ) : ℝ) * Real.sqrt (Y : ℝ) ≤ ((2 * Y : ℕ) : ℝ) ^ θ

/-- Every dyadic squarefree exception gives bounded factor data.  In addition
to the finite-set conditions, the fundamental solution and the exact
relation `y = de` or `y = 2de` are retained. -/
theorem dyadic_exception_has_bounded_factors {θ : ℝ} {Y m : ℕ}
    (hθ : 0 ≤ θ) (hm : m ∈ squarefreeDyadicExceptionalSet θ Y) :
    ∃ (a : Pell.Solution₁ (m : ℤ)) (d e u v : ℕ),
      Pell.IsFundamental a ∧ epsilon a ≤ (m : ℝ) ^ θ ∧
      DyadicFactorCondition θ Y d e u v ∧ u * v = m ∧
      (a.y = (d : ℤ) * e ∨ a.y = 2 * (d : ℤ) * e) := by
  obtain ⟨hmlo, hmhi, hsm, a, ha, hsmall⟩ :=
    mem_squarefreeDyadicExceptionalSet.mp hm
  have hmpos : 0 < m := by exact_mod_cast ha.d_pos
  obtain ⟨d, e, u, v, h, hd, he, hu, hv, hsu, hsv, hcop, huv, hvu, hh, hdiff, hy⟩ :=
    pell_factor_separation_oriented a hmpos hsm ha.1 ha.2.1
  have hyR : 0 ≤ (a.y : ℝ) := by exact_mod_cast ha.2.1.le
  have hxR : 0 ≤ (a.x : ℝ) := by exact_mod_cast ha.x_pos.le
  have hroot : 1 ≤ Real.sqrt (m : ℝ) :=
    Real.one_le_sqrt.mpr (by exact_mod_cast hmpos)
  have hysqrt : (a.y : ℝ) * Real.sqrt (m : ℝ) ≤ epsilon a := by
    simp only [epsilon, Int.cast_natCast]
    linarith
  have hyunit : (a.y : ℝ) ≤ epsilon a :=
    (le_mul_of_one_le_right hyR hroot).trans hysqrt
  have hheight : epsilon a ≤ ((2 * Y : ℕ) : ℝ) ^ θ :=
    hsmall.trans (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hmhi.le) hθ)
  have hde : (d : ℤ) * e ≤ a.y := by
    rcases hy with hy | hy
    · exact hy.ge
    · rw [hy]
      have hnonneg : (0 : ℤ) ≤ (d : ℤ) * e := by positivity
      nlinarith
  have hdeR : ((d * e : ℕ) : ℝ) ≤ (a.y : ℝ) := by exact_mod_cast hde
  have hdde : d ≤ d * e := Nat.le_mul_of_pos_right d he
  have hede : e ≤ d * e := Nat.le_mul_of_pos_left e hd
  have hdeheight : ((d * e : ℕ) : ℝ) ≤ (dyadicFactorHeight θ Y : ℝ) :=
    hdeR.trans (hyunit.trans (hheight.trans (Nat.le_ceil _)))
  have hdheight : d ≤ dyadicFactorHeight θ Y := by
    exact_mod_cast (le_trans (by exact_mod_cast hdde : (d : ℝ) ≤ (d * e : ℕ)) hdeheight)
  have heheight : e ≤ dyadicFactorHeight θ Y := by
    exact_mod_cast (le_trans (by exact_mod_cast hede : (e : ℝ) ≤ (d * e : ℕ)) hdeheight)
  have hum : u ≤ m := huv ▸ Nat.le_mul_of_pos_right u hv
  have hvm : v ≤ m := huv ▸ Nat.le_mul_of_pos_left v hu
  have hvsmall : v ^ 2 < 2 * Y := by
    have hsq : v * v ≤ u * v := Nat.mul_le_mul_right v hvu
    rw [huv] at hsq
    nlinarith
  have hprodheight :
      ((d * e : ℕ) : ℝ) * Real.sqrt (Y : ℝ) ≤ ((2 * Y : ℕ) : ℝ) ^ θ := by
    calc
      _ ≤ (a.y : ℝ) * Real.sqrt (Y : ℝ) :=
        mul_le_mul_of_nonneg_right hdeR (Real.sqrt_nonneg _)
      _ ≤ (a.y : ℝ) * Real.sqrt (m : ℝ) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by exact_mod_cast hmlo)) hyR
      _ ≤ epsilon a := hysqrt
      _ ≤ ((2 * Y : ℕ) : ℝ) ^ θ := hheight
  refine ⟨a, d, e, u, v, ha, hsmall, ?_, huv, hy⟩
  refine ⟨hd, he, hu, hv, hdheight, heheight, hum.trans_lt hmhi, hvm.trans_lt hmhi,
    hsu, hsv, hcop, huv ▸ hmlo, huv ▸ hmhi, hvu, hvsmall, ?_, hprodheight⟩
  rcases hh with hh | hh | hh | hh
  · exact Or.inl (hdiff.trans hh)
  · exact Or.inr (Or.inl (hdiff.trans hh))
  · exact Or.inr (Or.inr (Or.inl (hdiff.trans hh)))
  · exact Or.inr (Or.inr (Or.inr (hdiff.trans hh)))

/-- The explicit finite collection of tuples to which the determinant and
divisor estimates apply. -/
noncomputable def dyadicFactorTuples (θ : ℝ) (Y : ℕ) :
    Finset (ℕ × ℕ × ℕ × ℕ) := by
  classical
  exact ((Finset.Icc 1 (dyadicFactorHeight θ Y)).product
    ((Finset.Icc 1 (dyadicFactorHeight θ Y)).product
      ((Finset.Ico 1 (2 * Y)).product (Finset.Ico 1 (2 * Y))))).filter
    (fun p => DyadicFactorCondition θ Y p.1 p.2.1 p.2.2.1 p.2.2.2)

/-- The interval restrictions in the definition of the finite tuple set
are already part of its arithmetic predicate. -/
@[simp] theorem mem_dyadicFactorTuples {θ : ℝ} {Y d e u v : ℕ} :
    (d, e, u, v) ∈ dyadicFactorTuples θ Y ↔ DyadicFactorCondition θ Y d e u v := by
  classical
  simp only [dyadicFactorTuples, Finset.mem_filter]
  constructor
  · intro h
    exact h.2
  · intro h
    refine ⟨?_, h⟩
    rcases h with ⟨hd, he, hu, hv, hdH, heH, huH, hvH, _⟩
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hd, hdH⟩,
      Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨he, heH⟩,
        Finset.mem_product.mpr ⟨Finset.mem_Ico.mpr ⟨hu, huH⟩,
          Finset.mem_Ico.mpr ⟨hv, hvH⟩⟩⟩⟩

/-- Taking the product of the two squarefree coordinates recovers every
exceptional radicand.  This avoids any choice of a tuple for each radicand. -/
theorem squarefreeDyadicExceptionalSet_subset_factor_image {θ : ℝ} {Y : ℕ}
    (hθ : 0 ≤ θ) :
    squarefreeDyadicExceptionalSet θ Y ⊆
      (dyadicFactorTuples θ Y).image (fun p => p.2.2.1 * p.2.2.2) := by
  classical
  intro m hm
  obtain ⟨a, d, e, u, v, _, _, hdata, huv, _⟩ :=
    dyadic_exception_has_bounded_factors hθ hm
  exact Finset.mem_image.mpr ⟨(d, e, u, v), mem_dyadicFactorTuples.mpr hdata, huv⟩

/-- The finite counting reduction needed before the analytic determinant
estimates: the exceptional count is at most the number of bounded separated
factor tuples. -/
theorem squarefreeDyadicExceptionalCount_le_factor_card {θ : ℝ} {Y : ℕ}
    (hθ : 0 ≤ θ) :
    squarefreeDyadicExceptionalCount θ Y ≤ (dyadicFactorTuples θ Y).card := by
  classical
  exact (Finset.card_le_card
    (squarefreeDyadicExceptionalSet_subset_factor_image hθ)).trans Finset.card_image_le

end PellPaper
