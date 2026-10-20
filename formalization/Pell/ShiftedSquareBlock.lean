import Pell.UnbalancedShiftAdmissibility

/-!
# Exact finite shifted-square blocks

The unbalanced Pell substitution is

`a = -h * v`, `n = e * v`, and `w = u * v`.

This file records the exact half-open dyadic block counted in the manuscript,
its squarefree-`w` subblock, and the finite injective map from a fixed `(h,v)`
fibre of admissible unbalanced factor tuples.  No analytic estimate for the
block cardinality is asserted here.
-/

namespace PellPaper

noncomputable section

/-- The exact finite shifted-square block with positive natural coordinates:
`d^2 w = n^2 + a`, with `d`, `w`, and `n` in the indicated half-open
dyadic intervals. -/
noncomputable def shiftedSquareBlock (a : ℤ) (D Y N : ℕ) :
    Finset (ℕ × ℕ × ℕ) := by
  classical
  exact ((Finset.Ico D (2 * D)).product
    ((Finset.Ico Y (2 * Y)).product (Finset.Ico N (2 * N)))).filter fun p =>
      0 < p.1 ∧ 0 < p.2.1 ∧ 0 < p.2.2 ∧
        (p.1 : ℤ) ^ 2 * (p.2.1 : ℤ) = (p.2.2 : ℤ) ^ 2 + a

/-- Exact membership in a shifted-square block. -/
@[simp] theorem mem_shiftedSquareBlock {a : ℤ} {D Y N d w n : ℕ} :
    (d, w, n) ∈ shiftedSquareBlock a D Y N ↔
      0 < d ∧ 0 < w ∧ 0 < n ∧
      D ≤ d ∧ d < 2 * D ∧
      Y ≤ w ∧ w < 2 * Y ∧
      N ≤ n ∧ n < 2 * N ∧
      (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a := by
  classical
  simp only [shiftedSquareBlock, Finset.mem_filter]
  aesop

/-- The manuscript's squarefree block `N_a^sf`, obtained by imposing
squarefreeness on the `w` coordinate. -/
noncomputable def squarefreeShiftedSquareBlock (a : ℤ) (D Y N : ℕ) :
    Finset (ℕ × ℕ × ℕ) := by
  classical
  exact (shiftedSquareBlock a D Y N).filter fun p => Squarefree p.2.1

/-- Exact membership in the squarefree shifted-square block. -/
@[simp] theorem mem_squarefreeShiftedSquareBlock
    {a : ℤ} {D Y N d w n : ℕ} :
    (d, w, n) ∈ squarefreeShiftedSquareBlock a D Y N ↔
      0 < d ∧ 0 < w ∧ 0 < n ∧
      D ≤ d ∧ d < 2 * D ∧
      Y ≤ w ∧ w < 2 * Y ∧
      N ≤ n ∧ n < 2 * N ∧
      (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a ∧
      Squarefree w := by
  classical
  simp only [squarefreeShiftedSquareBlock, Finset.mem_filter,
    mem_shiftedSquareBlock]
  aesop

/-- A shifted-square equation with squarefree nonzero shift has primitive
source coordinates `(d,n)`. -/
theorem shiftedSquare_coprime_of_squarefree_shift
    {a : ℤ} {d w n : ℕ} (ha : Squarefree a)
    (heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a) :
    d.Coprime n := by
  let g := d.gcd n
  have hgd : (g : ℤ) ∣ (d : ℤ) :=
    Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left d n)
  have hgn : (g : ℤ) ∣ (n : ℤ) :=
    Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right d n)
  have hgdSquare : (g : ℤ) * g ∣ (d : ℤ) ^ 2 := by
    simpa only [pow_two] using mul_dvd_mul hgd hgd
  have hgnSquare : (g : ℤ) * g ∣ (n : ℤ) ^ 2 := by
    simpa only [pow_two] using mul_dvd_mul hgn hgn
  have hga : (g : ℤ) * g ∣ a := by
    have haIdentity : a = (d : ℤ) ^ 2 * (w : ℤ) - (n : ℤ) ^ 2 := by
      linarith
    rw [haIdentity]
    exact dvd_sub (dvd_mul_of_dvd_left hgdSquare _) hgnSquare
  have hunit : IsUnit (g : ℤ) := ha (g : ℤ) hga
  have hgabs : Int.natAbs (g : ℤ) = 1 := Int.isUnit_iff_natAbs_eq.mp hunit
  have hg : g = 1 := by simpa using hgabs
  exact Nat.coprime_iff_gcd_eq_one.mpr hg

/-- Every point of a squarefree shifted-square block is primitive in its
source coordinates when the fixed shift is squarefree. -/
theorem coprime_of_mem_squarefreeShiftedSquareBlock
    {a : ℤ} {D Y N d w n : ℕ} (ha : Squarefree a)
    (hp : (d, w, n) ∈ squarefreeShiftedSquareBlock a D Y N) :
    d.Coprime n := by
  exact shiftedSquare_coprime_of_squarefree_shift ha
    (mem_squarefreeShiftedSquareBlock.mp hp).2.2.2.2.2.2.2.2.2.1

/-- The literal unbalanced substitution on a factor tuple. -/
def shiftedSquareTupleMap (p : ℕ × ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  (p.1, p.2.2.1 * p.2.2.2, p.2.1 * p.2.2.2)

/-- The fixed-`(h,v)` part of the admissible unbalanced tuple set, further
cut into exact half-open `d` and `n=e*v` intervals. -/
noncomputable def admissibleUnbalancedShiftedSquareFibre
    (theta : ℝ) (Y R : ℕ) (h : ℤ) (v D N : ℕ) :
    Finset (ℕ × ℕ × ℕ × ℕ) := by
  classical
  exact (admissibleUnbalancedDyadicFactorTuples theta Y R).filter fun p =>
    p.2.2.2 = v ∧
      (p.2.1 : ℤ) ^ 2 * p.2.2.2 - (p.1 : ℤ) ^ 2 * p.2.2.1 = h ∧
      D ≤ p.1 ∧ p.1 < 2 * D ∧
      N ≤ p.2.1 * p.2.2.2 ∧ p.2.1 * p.2.2.2 < 2 * N

/-- Exact membership in the fixed-`(h,v)` factor-tuple fibre. -/
@[simp] theorem mem_admissibleUnbalancedShiftedSquareFibre
    {theta : ℝ} {Y R : ℕ} {h : ℤ} {v D N d e u v' : ℕ} :
    (d, e, u, v') ∈ admissibleUnbalancedShiftedSquareFibre theta Y R h v D N ↔
      DyadicFactorCondition theta Y d e u v' ∧ v' < R ∧
      DyadicShiftAdmissible d e u v' ∧
      v' = v ∧
      (e : ℤ) ^ 2 * v' - (d : ℤ) ^ 2 * u = h ∧
      D ≤ d ∧ d < 2 * D ∧
      N ≤ e * v' ∧ e * v' < 2 * N := by
  classical
  simp only [admissibleUnbalancedShiftedSquareFibre, Finset.mem_filter,
    mem_admissibleUnbalancedDyadicFactorTuples]
  aesop

/-- A tuple in the fixed fibre maps to the exact squarefree shifted-square
block with shift `-h*v`. -/
theorem shiftedSquareTupleMap_mem_squarefreeShiftedSquareBlock
    {theta : ℝ} {Y R : ℕ} {h : ℤ} {v D N : ℕ}
    {p : ℕ × ℕ × ℕ × ℕ}
    (hp : p ∈ admissibleUnbalancedShiftedSquareFibre theta Y R h v D N) :
    shiftedSquareTupleMap p ∈
      squarefreeShiftedSquareBlock (shiftedSquareA h v) D Y N := by
  rcases p with ⟨d, e, u, v'⟩
  obtain ⟨hcond, _hvR, hshiftData, hv, hdiff, hdD, hdD', hnN, hnN'⟩ :=
    mem_admissibleUnbalancedShiftedSquareFibre.mp hp
  subst v'
  rcases hcond with ⟨hd, he, hu, hvpos, _hdH, _heH, _huH, _hvH,
    hsu, hsv, huv, hYuv, huvY, _hvu, _hvsmall, _hsign, _hheight⟩
  rcases hshiftData with ⟨h', _hh', hdiff', hshift⟩
  have hh : h' = h := by linarith
  subst h'
  have hsquarefree : Squarefree (u * v) :=
    (Nat.squarefree_mul huv).mpr ⟨hsu, hsv⟩
  have heq := shifted_square_identity hdiff
  apply mem_squarefreeShiftedSquareBlock.mpr
  refine ⟨hd, Nat.mul_pos hu hvpos, Nat.mul_pos he hvpos,
    hdD, hdD', hYuv, huvY, hnN, hnN', ?_, hsquarefree⟩
  simpa only [shiftedSquareTupleMap, shiftedSquareW, shiftedSquareN,
    Nat.cast_mul] using heq

/-- The admissibility certificate on a fixed fibre makes the mapped source
pair primitive, as required by the direct shifted-square estimate. -/
theorem shiftedSquareTupleMap_coprime_of_mem_fibre
    {theta : ℝ} {Y R : ℕ} {h : ℤ} {v D N : ℕ}
    {p : ℕ × ℕ × ℕ × ℕ}
    (hp : p ∈ admissibleUnbalancedShiftedSquareFibre theta Y R h v D N) :
    (shiftedSquareTupleMap p).1.Coprime (shiftedSquareTupleMap p).2.2 := by
  have hp' := mem_admissibleUnbalancedShiftedSquareFibre.mp hp
  rcases hp'.2.2.1 with ⟨h', _hh', hdiff', hshift⟩
  have hh : h' = h := by
    linarith [hdiff', hp'.2.2.2.2.1]
  have ha : Squarefree (shiftedSquareA h v) := by
    rw [← hh, ← hp'.2.2.2.1]
    exact hshift.1
  exact coprime_of_mem_squarefreeShiftedSquareBlock ha
    (shiftedSquareTupleMap_mem_squarefreeShiftedSquareBlock hp)

/-- The tuple map is injective on every fixed positive-`v` fibre. -/
theorem shiftedSquareTupleMap_injective_on_fixed_v
    {v : ℕ} (hv : 0 < v) :
    Set.InjOn shiftedSquareTupleMap
      {p : ℕ × ℕ × ℕ × ℕ | p.2.2.2 = v} := by
  rintro ⟨d, e, u, v₁⟩ hv₁ ⟨d', e', u', v₂⟩ hv₂ heq
  simp only [Set.mem_ofPred_eq] at hv₁ hv₂
  subst v₁
  subst v₂
  simp only [shiftedSquareTupleMap, Prod.mk.injEq] at heq
  obtain ⟨hd, hu, he⟩ := heq
  have hu' : u = u' := Nat.mul_right_cancel hv hu
  have he' : e = e' := Nat.mul_right_cancel hv he
  subst d'
  subst u'
  subst e'
  rfl

/-- The exact finite cardinality reduction for a fixed `(h,v)` fibre. -/
theorem card_admissibleUnbalancedShiftedSquareFibre_le_squarefreeBlock
    {theta : ℝ} {Y R : ℕ} {h : ℤ} {v D N : ℕ} :
    (admissibleUnbalancedShiftedSquareFibre theta Y R h v D N).card ≤
      (squarefreeShiftedSquareBlock (shiftedSquareA h v) D Y N).card := by
  classical
  apply Finset.card_le_card_of_injOn shiftedSquareTupleMap
  · intro p hp
    exact shiftedSquareTupleMap_mem_squarefreeShiftedSquareBlock hp
  · intro p hp q hq hpq
    have hp' := mem_admissibleUnbalancedShiftedSquareFibre.mp hp
    have hq' := mem_admissibleUnbalancedShiftedSquareFibre.mp hq
    have hvpos : 0 < v := by
      have hpv : 0 < p.2.2.2 := hp'.1.2.2.2.1
      simpa only [hp'.2.2.2.1] using hpv
    exact shiftedSquareTupleMap_injective_on_fixed_v hvpos hp'.2.2.2.1 hq'.2.2.2.1 hpq

end

end PellPaper
