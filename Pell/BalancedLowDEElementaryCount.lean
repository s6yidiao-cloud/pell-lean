import Pell.DyadicFactorBoxNormalization
import Pell.DyadicRawPairPrimitivity
import Pell.SeparatedRealCenterCounting
import Mathlib.Tactic

/-!
# Elementary counting in a dyadic Pell-factor box

For fixed dyadic source coordinates `d,e` and fixed signed difference
`h`, the equation

`e^2 v - d^2 u = h`

puts all admissible `v` coordinates in one residue class modulo `d^2`.
The actual factor condition proves `d` and `e` coprime, so distinct tuples
in that fibre have `v` coordinates separated by at least `d^2`.  Packing
these coordinates into their dyadic interval and summing over `d,e` and
the four signed values gives the explicit bound

`#cell <= 4 D E (1 + V / D^2)`.

The Pell equation also gives `E^2 V <= 24 D^2 U`, while a nonempty actual
cell gives `UV < 2Y`.  Thus `EV/D <= 7 sqrt(Y)` and consequently

`#cell <= 4 D E + 28 sqrt(Y)`.

No determinant estimate, curve estimate, asymptotic premise, or black-box
counting assertion is used.
-/

namespace PellPaper

noncomputable section

private def dyadicTupleSignedLevel (p : ℕ × ℕ × ℕ × ℕ) : ℤ :=
  (p.2.1 : ℤ) ^ 2 * p.2.2.2 - (p.1 : ℤ) ^ 2 * p.2.2.1

private def dyadicTupleFibreKey (p : ℕ × ℕ × ℕ × ℕ) : ℕ × ℕ × ℤ :=
  (p.1, p.2.1, dyadicTupleSignedLevel p)

private theorem dyadicTupleSignedLevel_signed
    {theta : ℝ} {Y : ℕ} {i : ℕ × ℕ × ℕ × ℕ}
    {p : ℕ × ℕ × ℕ × ℕ}
    (hp : p ∈ dyadicFactorBoxCell theta Y i) :
    IsSignedDyadicDifference (dyadicTupleSignedLevel p) := by
  rcases Finset.mem_inter.mp hp with ⟨hfactor, _⟩
  exact isSignedDyadicDifference_of_dyadicFactorCondition
    (mem_dyadicFactorTuples.mp hfactor) rfl

private theorem dyadicTuple_eq_of_same_fibreKey_and_v
    {theta : ℝ} {Y : ℕ} {i : ℕ × ℕ × ℕ × ℕ}
    {p q : ℕ × ℕ × ℕ × ℕ}
    (hp : p ∈ dyadicFactorBoxCell theta Y i)
    (hq : q ∈ dyadicFactorBoxCell theta Y i)
    (hkey : dyadicTupleFibreKey p = dyadicTupleFibreKey q)
    (hv : p.2.2.2 = q.2.2.2) : p = q := by
  rcases p with ⟨d, e, u, v⟩
  rcases q with ⟨d', e', u', v'⟩
  simp only [dyadicTupleFibreKey, dyadicTupleSignedLevel] at hkey hv ⊢
  have hd : d = d' := congrArg Prod.fst hkey
  have he : e = e' := congrArg (fun z => z.2.1) hkey
  subst d'
  subst e'
  subst v'
  have hlevel :
      (e : ℤ) ^ 2 * (v : ℤ) - (d : ℤ) ^ 2 * (u : ℤ) =
        (e : ℤ) ^ 2 * (v : ℤ) - (d : ℤ) ^ 2 * (u' : ℤ) :=
    congrArg (fun z => z.2.2) hkey
  have hcond : DyadicFactorCondition theta Y d e u v :=
    mem_dyadicFactorTuples.mp (Finset.mem_inter.mp hp).1
  have hd0 : (d : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hcond.1)
  have hpow0 : (d : ℤ) ^ 2 ≠ 0 := pow_ne_zero _ hd0
  have hu : (u : ℤ) = (u' : ℤ) := by
    apply (mul_left_cancel₀ hpow0)
    linarith
  have hunat : u = u' := by exact_mod_cast hu
  subst u'
  rfl

private theorem dyadicTuple_v_separated_of_same_fibreKey
    {theta : ℝ} {Y : ℕ} {i : ℕ × ℕ × ℕ × ℕ}
    {p q : ℕ × ℕ × ℕ × ℕ}
    (hp : p ∈ dyadicFactorBoxCell theta Y i)
    (hq : q ∈ dyadicFactorBoxCell theta Y i)
    (hkey : dyadicTupleFibreKey p = dyadicTupleFibreKey q)
    (hpq : p ≠ q) :
    (((2 ^ i.1 : ℕ) : ℝ) ^ 2) ≤
      |(p.2.2.2 : ℝ) - (q.2.2.2 : ℝ)| := by
  rcases p with ⟨d, e, u, v⟩
  rcases q with ⟨d', e', u', v'⟩
  simp only [dyadicTupleFibreKey, dyadicTupleSignedLevel] at hkey ⊢
  have hd : d = d' := congrArg Prod.fst hkey
  have he : e = e' := congrArg (fun z => z.2.1) hkey
  subst d'
  subst e'
  have hlevel :
      (e : ℤ) ^ 2 * (v : ℤ) - (d : ℤ) ^ 2 * (u : ℤ) =
        (e : ℤ) ^ 2 * (v' : ℤ) - (d : ℤ) ^ 2 * (u' : ℤ) :=
    congrArg (fun z => z.2.2) hkey
  have hvne : v ≠ v' := by
    intro hv
    apply hpq
    exact dyadicTuple_eq_of_same_fibreKey_and_v hp hq hkey hv
  have hcond : DyadicFactorCondition theta Y d e u v :=
    mem_dyadicFactorTuples.mp (Finset.mem_inter.mp hp).1
  have hcop : IsCoprime ((d : ℤ) ^ 2) ((e : ℤ) ^ 2) :=
    (dyadicFactorCondition_primitive_raw_pairs hcond).1.pow
  have hdivmul : (d : ℤ) ^ 2 ∣ (e : ℤ) ^ 2 * ((v : ℤ) - (v' : ℤ)) := by
    refine ⟨(u : ℤ) - (u' : ℤ), ?_⟩
    linarith
  have hdiv : (d : ℤ) ^ 2 ∣ (v : ℤ) - (v' : ℤ) :=
    hcop.dvd_of_dvd_mul_left hdivmul
  obtain ⟨z, hz⟩ := hdiv
  have hz0 : z ≠ 0 := by
    intro hz0
    subst z
    simp only [mul_zero] at hz
    have : (v : ℤ) = (v' : ℤ) := sub_eq_zero.mp hz
    exact hvne (by exact_mod_cast this)
  have habsz : (1 : ℤ) ≤ |z| := Int.one_le_abs hz0
  have hdnonneg : (0 : ℤ) ≤ (d : ℤ) ^ 2 := sq_nonneg _
  have hint : (d : ℤ) ^ 2 ≤ |(v : ℤ) - (v' : ℤ)| := by
    rw [hz, abs_mul, abs_of_nonneg hdnonneg]
    exact le_mul_of_one_le_right hdnonneg habsz
  have hbox := (Finset.mem_inter.mp hp).2
  have hDle : ((2 ^ i.1 : ℕ) : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast (dyadicBox_coordinate_lower_bounds hbox).1
  calc
    ((2 ^ i.1 : ℕ) : ℝ) ^ 2 ≤ (d : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hDle 2
    _ ≤ |(v : ℝ) - (v' : ℝ)| := by exact_mod_cast hint

/-- Fixing the two source coordinates and the signed Pell level in an
actual dyadic factor cell leaves at most `1 + V / D^2` tuples.  This is the
direct residue-class packing step of the elementary low-`DE` count. -/
private theorem card_dyadicFactorBoxCell_fixed_source_signed_fibre_le
    (theta : ℝ) (Y : ℕ) (i : ℕ × ℕ × ℕ × ℕ)
    (key : ℕ × ℕ × ℤ) :
    (((dyadicFactorBoxCell theta Y i).filter
      (fun p => dyadicTupleFibreKey p = key)).card : ℝ) ≤
        1 + ((2 ^ i.2.2.2 : ℕ) : ℝ) /
          (((2 ^ i.1 : ℕ) : ℝ) ^ 2) := by
  let J := (dyadicFactorBoxCell theta Y i).filter
    (fun p => dyadicTupleFibreKey p = key)
  let D : ℝ := ((2 ^ i.1 : ℕ) : ℝ)
  let V : ℝ := ((2 ^ i.2.2.2 : ℕ) : ℝ)
  change (J.card : ℝ) ≤ 1 + V / D ^ 2
  have hD : 0 < D := by dsimp [D]; positivity
  have hV : 0 < V := by dsimp [V]; positivity
  have hpack := card_le_one_add_div_of_separated_real_centers J
    (fun p => (p.2.2.2 : ℝ)) V (2 * V) (D ^ 2)
    (by positivity) (by linarith) (by
      intro p hp
      have hpCell := (Finset.mem_filter.mp hp).1
      have hbox := (Finset.mem_inter.mp hpCell).2
      have hlower := (dyadicBox_coordinate_lower_bounds hbox).2.2.2
      have hupper := (dyadicBox_coordinate_upper_bounds hbox).2.2.2
      constructor
      · dsimp [V]
        exact_mod_cast hlower
      · dsimp [V]
        exact_mod_cast hupper) (by
      intro p hp q hq hpq
      apply dyadicTuple_v_separated_of_same_fibreKey
      · exact (Finset.mem_filter.mp hp).1
      · exact (Finset.mem_filter.mp hq).1
      · exact (Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm
      · exact hpq)
  convert hpack using 1
  ring

/-- Summing the separated fixed-`d,e,h` fibres over the two source dyadic
intervals and the four signed Pell levels gives a completely explicit
box count. -/
theorem dyadicFactorBoxCell_card_le_four_mul_sourceProduct_mul_packing
    (theta : ℝ) (Y : ℕ) (i : ℕ × ℕ × ℕ × ℕ) :
    ((dyadicFactorBoxCell theta Y i).card : ℝ) ≤
      4 * (((2 ^ i.1 : ℕ) : ℝ) * ((2 ^ i.2.1 : ℕ) : ℝ)) *
        (1 + ((2 ^ i.2.2.2 : ℕ) : ℝ) /
          (((2 ^ i.1 : ℕ) : ℝ) ^ 2)) := by
  classical
  let S := dyadicFactorBoxCell theta Y i
  let K : Finset (ℕ × ℕ × ℤ) :=
    (dyadicInterval i.1).product
      ((dyadicInterval i.2.1).product ({1, -1, 2, -2} : Finset ℤ))
  have hmap : (S : Set (ℕ × ℕ × ℕ × ℕ)).MapsTo dyadicTupleFibreKey K := by
    intro p hp
    have hbox := (Finset.mem_inter.mp hp).2
    unfold dyadicBox at hbox
    rcases Finset.mem_product.mp hbox with ⟨hd, hrest⟩
    rcases Finset.mem_product.mp hrest with ⟨he, _⟩
    refine Finset.mem_product.mpr ⟨hd, Finset.mem_product.mpr ⟨he, ?_⟩⟩
    simpa only [dyadicTupleFibreKey, Finset.mem_insert, Finset.mem_singleton,
      IsSignedDyadicDifference]
      using dyadicTupleSignedLevel_signed hp
  have hpartition :
      S.card = ∑ key ∈ K, (S.filter fun p => dyadicTupleFibreKey p = key).card :=
    Finset.card_eq_sum_card_fiberwise hmap
  have hsum :
      (S.card : ℝ) ≤ ∑ _key ∈ K,
        (1 + ((2 ^ i.2.2.2 : ℕ) : ℝ) /
          (((2 ^ i.1 : ℕ) : ℝ) ^ 2)) := by
    rw [hpartition, Nat.cast_sum]
    apply Finset.sum_le_sum
    intro key hkey
    exact card_dyadicFactorBoxCell_fixed_source_signed_fibre_le theta Y i key
  have hKcard : K.card = 4 * (2 ^ i.1) * (2 ^ i.2.1) := by
    simp [K, dyadicInterval, Nat.card_Ico, pow_succ, Nat.mul_comm,
      Nat.mul_left_comm]
    have hd : 2 * 2 ^ i.1 - 2 ^ i.1 = 2 ^ i.1 := by omega
    have he : 2 * 2 ^ i.2.1 - 2 ^ i.2.1 = 2 ^ i.2.1 := by omega
    rw [hd, he]
  rw [Finset.sum_const, nsmul_eq_mul, hKcard] at hsum
  norm_num at hsum ⊢
  nlinarith

/-- The elementary Reuss-section count for one actual dyadic factor box.
It is valid without a low-endpoint hypothesis: the latter is needed only
afterwards to make the displayed `DE` term a power saving. -/
theorem dyadicFactorBoxCell_card_le_four_sourceProduct_add_twentyEight_sqrt
    (theta : ℝ) (Y : ℕ) (i : ℕ × ℕ × ℕ × ℕ)
    (hcell : (dyadicFactorBoxCell theta Y i).Nonempty) :
    ((dyadicFactorBoxCell theta Y i).card : ℝ) ≤
      4 * (((2 ^ i.1 : ℕ) : ℝ) * ((2 ^ i.2.1 : ℕ) : ℝ)) +
        28 * Real.sqrt (Y : ℝ) := by
  let D : ℝ := ((2 ^ i.1 : ℕ) : ℝ)
  let E : ℝ := ((2 ^ i.2.1 : ℕ) : ℝ)
  let U : ℝ := ((2 ^ i.2.2.1 : ℕ) : ℝ)
  let V : ℝ := ((2 ^ i.2.2.2 : ℕ) : ℝ)
  have hD : 0 < D := by dsimp [D]; positivity
  have hE : 0 < E := by dsimp [E]; positivity
  have hU : 0 < U := by dsimp [U]; positivity
  have hV : 0 < V := by dsimp [V]; positivity
  obtain ⟨p, hp⟩ := hcell
  have hcond := mem_dyadicFactorTuples.mp (Finset.mem_inter.mp hp).1
  have hbox := (Finset.mem_inter.mp hp).2
  have hcompare := dyadicFactorCondition_dyadicBox_endpoint_scales_comparable hcond hbox
  have hnormalize := dyadicFactorCondition_dyadicBox_endpoint_normalization hcond hbox
  change ((dyadicFactorBoxCell theta Y i).card : ℝ) ≤
    4 * (D * E) + 28 * Real.sqrt (Y : ℝ)
  have hcount :=
    dyadicFactorBoxCell_card_le_four_mul_sourceProduct_mul_packing theta Y i
  change ((dyadicFactorBoxCell theta Y i).card : ℝ) ≤
    4 * (D * E) * (1 + V / D ^ 2) at hcount
  have hxSq : (E * V / D) ^ 2 ≤ 48 * (Y : ℝ) := by
    have hstep : E ^ 2 * V ^ 2 ≤ 24 * D ^ 2 * (U * V) := by
      nlinarith [mul_le_mul_of_nonneg_right hcompare.1 hV.le]
    have hYnonneg : (0 : ℝ) ≤ Y := by positivity
    calc
      (E * V / D) ^ 2 = (E ^ 2 * V ^ 2) / D ^ 2 := by field_simp
      _ ≤ (24 * D ^ 2 * (U * V)) / D ^ 2 :=
        div_le_div_of_nonneg_right hstep (sq_nonneg D)
      _ = 24 * (U * V) := by field_simp
      _ ≤ 48 * (Y : ℝ) := by nlinarith [hnormalize.1]
  have hsqrtSq : Real.sqrt (Y : ℝ) ^ 2 = (Y : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hx : E * V / D ≤ 7 * Real.sqrt (Y : ℝ) := by
    have hxnonneg : 0 ≤ E * V / D := by positivity
    have hsqrtnonneg := Real.sqrt_nonneg (Y : ℝ)
    nlinarith
  have hexpand : 4 * (D * E) * (1 + V / D ^ 2) =
      4 * (D * E) + 4 * (E * V / D) := by field_simp
  rw [hexpand] at hcount
  nlinarith

/-- The literal complementary low-`DE` branch of the manuscript.  Its endpoint
hypothesis replaces the source-product term in the unconditional elementary
cell bound; all arithmetic counting remains proved above. -/
theorem main3BalancedLowDE_dyadicFactorBoxCell_card_le
    (theta : ℝ) (Y : ℕ) (i : ℕ × ℕ × ℕ × ℕ)
    (hcell : (dyadicFactorBoxCell (theta + 1 / 4) Y i).Nonempty)
    (hlowDE :
      ((2 ^ i.1 : ℕ) : ℝ) * ((2 ^ i.2.1 : ℕ) : ℝ) ≤
        (Y : ℝ) ^ (1 - 1 / (100 * theta ^ 2))) :
    ((dyadicFactorBoxCell (theta + 1 / 4) Y i).card : ℝ) ≤
      4 * (Y : ℝ) ^ (1 - 1 / (100 * theta ^ 2)) +
        28 * Real.sqrt (Y : ℝ) := by
  have hcount :=
    dyadicFactorBoxCell_card_le_four_sourceProduct_add_twentyEight_sqrt
      (theta + 1 / 4) Y i hcell
  nlinarith

end

end PellPaper
