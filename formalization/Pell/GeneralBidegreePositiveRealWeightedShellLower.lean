import Pell.GeneralBidegreePositiveRealWeightedCount

/-!
# Lower bounds for positive real weighted lattice shells

The weighted rank cap is a difference of two weighted-ball cardinalities.
This file constructs an explicit rectangle of lattice points inside such a
shell.  It gives both a discrete floor-product lower bound and a coarser
real area-style main term.

These estimates are intentionally uniform and elementary.  They do not yet
recover the manuscript's sharper piecewise lattice calculation or its
subsequent integral estimate.
-/

namespace PellPaper

/-- Positive real weighted balls are monotone in their radius. -/
theorem generalBidegreePositiveRealWeightedBall_subset_of_radius_le
    (ellM ellX R₁ R₂ : ℝ) (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX)
    (hR : R₁ ≤ R₂) :
    generalBidegreePositiveRealWeightedBall ellM ellX R₁ hellM_pos hell ⊆
      generalBidegreePositiveRealWeightedBall ellM ellX R₂ hellM_pos hell := by
  intro m hm
  rw [mem_generalBidegreePositiveRealWeightedBall_iff] at hm ⊢
  exact hm.trans hR

/-- A rectangular family of lattice points lies in the weighted shell between
radii `R - d` and `R`.  Its cardinality gives a discrete lower bound for the
shell count. -/
theorem floorRectangle_le_card_sub_card_generalBidegreePositiveRealWeightedBall
    (ellM ellX R d : ℝ) (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX)
    (hd : 0 ≤ d) (hR_sub_d : 0 ≤ R - d) :
    ⌊d / ellM⌋₊ * (⌊(R - d) / ellX⌋₊ + 1) ≤
      (generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell).card -
        (generalBidegreePositiveRealWeightedBall ellM ellX (R - d)
          hellM_pos hell).card := by
  classical
  have hellX_pos : 0 < ellX := hellM_pos.trans_le hell
  let q : ℕ := ⌊d / ellM⌋₊
  let J : ℕ := ⌊(R - d) / ellX⌋₊
  let S := generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell
  let T := generalBidegreePositiveRealWeightedBall ellM ellX (R - d)
    hellM_pos hell
  have hTsubS : T ⊆ S := by
    dsimp only [S, T]
    apply generalBidegreePositiveRealWeightedBall_subset_of_radius_le
    linarith
  have hmem_shell (j k : ℕ) (hj : j < J + 1) (hk : k < q) :
      Finsupp.single (0 : Fin 2)
          (⌊(R - d - (j : ℝ) * ellX) / ellM⌋₊ + 1 + k) +
        Finsupp.single (1 : Fin 2) j ∈ S \ T := by
    have hjle : j ≤ J := by omega
    have hjfloor : j ≤ ⌊(R - d) / ellX⌋₊ := by
      simpa only [J] using hjle
    have hR_sub_d_div_nonneg : 0 ≤ (R - d) / ellX :=
      div_nonneg hR_sub_d hellX_pos.le
    have hjdiv : (j : ℝ) ≤ (R - d) / ellX :=
      (Nat.le_floor_iff hR_sub_d_div_nonneg).mp hjfloor
    have hjmul : (j : ℝ) * ellX ≤ R - d :=
      (le_div_iff₀ hellX_pos).mp hjdiv
    have hres_nonneg : 0 ≤ R - d - (j : ℝ) * ellX := by linarith
    let L : ℕ := ⌊(R - d - (j : ℝ) * ellX) / ellM⌋₊
    let i : ℕ := L + 1 + k
    let m : generalBidegreeWeightedMonomialIndex :=
      Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) j
    have hL : (L : ℝ) ≤ (R - d - (j : ℝ) * ellX) / ellM := by
      dsimp only [L]
      exact Nat.floor_le (div_nonneg hres_nonneg hellM_pos.le)
    have hq : (q : ℝ) ≤ d / ellM := by
      dsimp only [q]
      exact Nat.floor_le (div_nonneg hd hellM_pos.le)
    have hk_le : k + 1 ≤ q := by omega
    have hi_le : i ≤ L + q := by
      dsimp only [i]
      omega
    have hi_cast : (i : ℝ) ≤ (L : ℝ) + (q : ℝ) := by
      exact_mod_cast hi_le
    have houter_div : (i : ℝ) ≤ (R - (j : ℝ) * ellX) / ellM := by
      calc
        (i : ℝ) ≤ (L : ℝ) + (q : ℝ) := hi_cast
        _ ≤ (R - d - (j : ℝ) * ellX) / ellM + d / ellM :=
          add_le_add hL hq
        _ = (R - (j : ℝ) * ellX) / ellM := by
          field_simp [ne_of_gt hellM_pos]
          ring
    have hi_outer : (i : ℝ) * ellM ≤ R - (j : ℝ) * ellX :=
      (le_div_iff₀ hellM_pos).mp houter_div
    have hfloor_lt : (R - d - (j : ℝ) * ellX) / ellM < (L : ℝ) + 1 := by
      dsimp only [L]
      simpa only [Nat.cast_add, Nat.cast_one] using
        Nat.lt_floor_add_one ((R - d - (j : ℝ) * ellX) / ellM)
    have hi_lower : L + 1 ≤ i := by
      dsimp only [i]
      omega
    have hdiv_lt : (R - d - (j : ℝ) * ellX) / ellM < (i : ℝ) := by
      calc
        (R - d - (j : ℝ) * ellX) / ellM < (L : ℝ) + 1 := hfloor_lt
        _ ≤ (i : ℝ) := by exact_mod_cast hi_lower
    have hi_inner : R - d - (j : ℝ) * ellX < (i : ℝ) * ellM :=
      (div_lt_iff₀ hellM_pos).mp hdiv_lt
    have hmzero : m 0 = i := by simp [m]
    have hmone : m 1 = j := by simp [m]
    have hm_outer : m ∈ S := by
      dsimp only [S]
      rw [mem_generalBidegreePositiveRealWeightedBall_iff]
      rw [generalBidegreeRealWeight, hmzero, hmone]
      linarith
    have hm_inner : m ∉ T := by
      intro hm
      dsimp only [T] at hm
      rw [mem_generalBidegreePositiveRealWeightedBall_iff] at hm
      rw [generalBidegreeRealWeight, hmzero, hmone] at hm
      linarith
    have hm_eq :
        Finsupp.single (0 : Fin 2)
            (⌊(R - d - (j : ℝ) * ellX) / ellM⌋₊ + 1 + k) +
          Finsupp.single (1 : Fin 2) j = m := by
      simp only [m, i, L]
    rw [hm_eq]
    exact Finset.mem_sdiff.mpr ⟨hm_outer, hm_inner⟩
  let f : Fin (J + 1) × Fin q → ↥(S \ T) := fun x =>
    ⟨Finsupp.single (0 : Fin 2)
          (⌊(R - d - ((x.1 : ℕ) : ℝ) * ellX) / ellM⌋₊ + 1 + (x.2 : ℕ)) +
        Finsupp.single (1 : Fin 2) (x.1 : ℕ),
      hmem_shell (x.1 : ℕ) (x.2 : ℕ) x.1.isLt x.2.isLt⟩
  have hf : Function.Injective f := by
    rintro ⟨j, k⟩ ⟨j', k'⟩ h
    have hjval : (j : ℕ) = (j' : ℕ) := by
      have hcoord := congrArg (fun z : ↥(S \ T) => z.1 1) h
      simpa [f] using hcoord
    have hj : j = j' := Fin.ext hjval
    subst j'
    have hkval : (k : ℕ) = (k' : ℕ) := by
      have hcoord := congrArg (fun z : ↥(S \ T) => z.1 0) h
      simp [f] at hcoord
      omega
    exact Prod.ext rfl (Fin.ext hkval)
  have hcard : q * (J + 1) ≤ (S \ T).card := by
    have h := Fintype.card_le_of_injective f hf
    simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_fin,
      Nat.mul_comm] using h
  calc
    ⌊d / ellM⌋₊ * (⌊(R - d) / ellX⌋₊ + 1) = q * (J + 1) := by rfl
    _ ≤ (S \ T).card := hcard
    _ = S.card - T.card := Finset.card_sdiff_of_subset hTsubS
    _ = (generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell).card -
          (generalBidegreePositiveRealWeightedBall ellM ellX (R - d)
            hellM_pos hell).card := by rfl

/-- A real area-style consequence of the floor-rectangle shell bound.  The
main term is the area of an inscribed rectangle; the `-1` is the elementary
rounding loss in the first coordinate. -/
theorem realAreaLower_le_card_sub_card_generalBidegreePositiveRealWeightedBall
    (ellM ellX R d : ℝ) (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX)
    (hd : 0 ≤ d) (hR_sub_d : 0 ≤ R - d) (hellM_le_d : ellM ≤ d) :
    (d / ellM - 1) * ((R - d) / ellX) ≤
      ((generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell).card -
        (generalBidegreePositiveRealWeightedBall ellM ellX (R - d)
          hellM_pos hell).card : ℕ) := by
  have hellX_pos : 0 < ellX := hellM_pos.trans_le hell
  have hdisc := floorRectangle_le_card_sub_card_generalBidegreePositiveRealWeightedBall
    ellM ellX R d hellM_pos hell hd hR_sub_d
  have hq_lower : d / ellM - 1 ≤ (⌊d / ellM⌋₊ : ℝ) := by
    have hfloor := Nat.lt_floor_add_one (d / ellM)
    linarith
  have hJ_lower : (R - d) / ellX ≤ ((⌊(R - d) / ellX⌋₊ : ℝ) + 1) :=
    le_of_lt (Nat.lt_floor_add_one ((R - d) / ellX))
  have hres_div_nonneg : 0 ≤ (R - d) / ellX :=
    div_nonneg hR_sub_d hellX_pos.le
  have hq_nonneg : 0 ≤ (⌊d / ellM⌋₊ : ℝ) := by positivity
  have hmain_nonneg : 0 ≤ d / ellM - 1 := by
    have hone : 1 ≤ d / ellM := (one_le_div₀ hellM_pos).mpr hellM_le_d
    linarith
  have hproduct :
      (d / ellM - 1) * ((R - d) / ellX) ≤
        (⌊d / ellM⌋₊ : ℝ) * ((⌊(R - d) / ellX⌋₊ : ℝ) + 1) :=
    mul_le_mul hq_lower hJ_lower hres_div_nonneg hq_nonneg
  have hdisc_cast :
      ((⌊d / ellM⌋₊ * (⌊(R - d) / ellX⌋₊ + 1) : ℕ) : ℝ) ≤
        ((generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell).card -
          (generalBidegreePositiveRealWeightedBall ellM ellX (R - d)
            hellM_pos hell).card : ℕ) := by
    exact_mod_cast hdisc
  calc
    (d / ellM - 1) * ((R - d) / ellX) ≤
        (⌊d / ellM⌋₊ : ℝ) * ((⌊(R - d) / ellX⌋₊ : ℝ) + 1) := hproduct
    _ = ((⌊d / ellM⌋₊ * (⌊(R - d) / ellX⌋₊ + 1) : ℕ) : ℝ) := by
      push_cast
      ring
    _ ≤ ((generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell).card -
          (generalBidegreePositiveRealWeightedBall ellM ellX (R - d)
            hellM_pos hell).card : ℕ) := hdisc_cast

/-- Specialization of the discrete shell lower bound to the parallel-line
shift `(A + 1) * ellX` appearing in the weighted rank filtration. -/
theorem floorRectangle_le_parallelLine_rankDefect
    (A : ℕ) (ellM ellX R : ℝ) (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX)
    (hshift : 0 ≤ R - ((A + 1 : ℕ) : ℝ) * ellX) :
    ⌊(((A + 1 : ℕ) : ℝ) * ellX / ellM)⌋₊ *
        (⌊(R - ((A + 1 : ℕ) : ℝ) * ellX) / ellX⌋₊ + 1) ≤
      (generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell).card -
        (generalBidegreePositiveRealWeightedBall ellM ellX
          (R - ((A + 1 : ℕ) : ℝ) * ellX) hellM_pos hell).card := by
  have hellX_pos : 0 < ellX := hellM_pos.trans_le hell
  have hshift_nonneg : 0 ≤ ((A + 1 : ℕ) : ℝ) * ellX :=
    mul_nonneg (by positivity) hellX_pos.le
  exact floorRectangle_le_card_sub_card_generalBidegreePositiveRealWeightedBall
    ellM ellX R (((A + 1 : ℕ) : ℝ) * ellX) hellM_pos hell hshift_nonneg hshift

/-- A simple real main-term lower bound for the parallel-line weighted shell.
It is the explicit area estimate corresponding to the preceding floor
product. -/
theorem realAreaLower_le_parallelLine_rankDefect
    (A : ℕ) (ellM ellX R : ℝ) (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX)
    (hshift : 0 ≤ R - ((A + 1 : ℕ) : ℝ) * ellX) :
    ((((A + 1 : ℕ) : ℝ) * ellX / ellM - 1) *
        ((R - ((A + 1 : ℕ) : ℝ) * ellX) / ellX)) ≤
      ((generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell).card -
        (generalBidegreePositiveRealWeightedBall ellM ellX
          (R - ((A + 1 : ℕ) : ℝ) * ellX) hellM_pos hell).card : ℕ) := by
  have hellX_pos : 0 < ellX := hellM_pos.trans_le hell
  have hshift_nonneg : 0 ≤ ((A + 1 : ℕ) : ℝ) * ellX :=
    mul_nonneg (by positivity) hellX_pos.le
  have hA_one : (1 : ℝ) ≤ ((A + 1 : ℕ) : ℝ) := by
    norm_cast
    omega
  have hellM_le_shift : ellM ≤ ((A + 1 : ℕ) : ℝ) * ellX := by
    calc
      ellM ≤ ellX := hell
      _ = 1 * ellX := by ring
      _ ≤ ((A + 1 : ℕ) : ℝ) * ellX :=
        mul_le_mul_of_nonneg_right hA_one hellX_pos.le
  exact realAreaLower_le_card_sub_card_generalBidegreePositiveRealWeightedBall
    ellM ellX R (((A + 1 : ℕ) : ℝ) * ellX) hellM_pos hell hshift_nonneg
      hshift hellM_le_shift

/-- The discrete shell lower bound rewritten through the exact floor-sum
formula for `N(R)`. -/
theorem floorRectangle_le_parallelLine_floorSumDefect
    (A : ℕ) (ellM ellX R : ℝ) (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX)
    (hshift : 0 ≤ R - ((A + 1 : ℕ) : ℝ) * ellX) :
    ⌊(((A + 1 : ℕ) : ℝ) * ellX / ellM)⌋₊ *
        (⌊(R - ((A + 1 : ℕ) : ℝ) * ellX) / ellX⌋₊ + 1) ≤
      generalBidegreePositiveRealWeightedFloorSum ellM ellX R -
        generalBidegreePositiveRealWeightedFloorSum ellM ellX
          (R - ((A + 1 : ℕ) : ℝ) * ellX) := by
  have hellX_pos : 0 < ellX := hellM_pos.trans_le hell
  have hshift_nonneg : 0 ≤ ((A + 1 : ℕ) : ℝ) * ellX :=
    mul_nonneg (by positivity) hellX_pos.le
  have hR : 0 ≤ R := by linarith
  have hbound := floorRectangle_le_parallelLine_rankDefect
    A ellM ellX R hellM_pos hell hshift
  rw [card_generalBidegreePositiveRealWeightedBall_eq_floorSum'
        ellM ellX R hellM_pos hell hR,
    card_generalBidegreePositiveRealWeightedBall_eq_floorSum'
      ellM ellX (R - ((A + 1 : ℕ) : ℝ) * ellX) hellM_pos hell hshift] at hbound
  exact hbound

/-- A direct real main-term lower bound for the exact floor-sum defect in the
parallel-line rank filtration. -/
theorem realAreaLower_le_parallelLine_floorSumDefect
    (A : ℕ) (ellM ellX R : ℝ) (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX)
    (hshift : 0 ≤ R - ((A + 1 : ℕ) : ℝ) * ellX) :
    ((((A + 1 : ℕ) : ℝ) * ellX / ellM - 1) *
        ((R - ((A + 1 : ℕ) : ℝ) * ellX) / ellX)) ≤
      ((generalBidegreePositiveRealWeightedFloorSum ellM ellX R -
        generalBidegreePositiveRealWeightedFloorSum ellM ellX
          (R - ((A + 1 : ℕ) : ℝ) * ellX) : ℕ) : ℝ) := by
  have hellX_pos : 0 < ellX := hellM_pos.trans_le hell
  have hshift_nonneg : 0 ≤ ((A + 1 : ℕ) : ℝ) * ellX :=
    mul_nonneg (by positivity) hellX_pos.le
  have hR : 0 ≤ R := by linarith
  have hbound := realAreaLower_le_parallelLine_rankDefect
    A ellM ellX R hellM_pos hell hshift
  rw [card_generalBidegreePositiveRealWeightedBall_eq_floorSum'
        ellM ellX R hellM_pos hell hR,
    card_generalBidegreePositiveRealWeightedBall_eq_floorSum'
      ellM ellX (R - ((A + 1 : ℕ) : ℝ) * ellX) hellM_pos hell hshift] at hbound
  exact hbound

end PellPaper
