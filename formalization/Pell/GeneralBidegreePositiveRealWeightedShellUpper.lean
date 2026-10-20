import Pell.GeneralBidegreePositiveRealWeightedShellLower

/-!
# Upper bounds for positive real weighted lattice shells

This module supplies the complementary finite lattice estimate for the
parallel-line rank cap.  Each lattice point in the shell between radii
`R - d` and `R` is encoded by its second exponent and its distance from the
outer boundary in the first exponent.  This gives a linear-in-`R` rectangle
bound, the discrete analogue of the second branch of the manuscript's
piecewise area calculation.
-/

namespace PellPaper

/-- The shell between radii `R - d` and `R` injects into a rectangle indexed
by the outer second-coordinate range and the thickness in the first
coordinate. -/
theorem card_sub_card_generalBidegreePositiveRealWeightedBall_le_floorRectangle
    (ellM ellX R d : ℝ) (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX)
    (hd : 0 ≤ d) :
    (generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell).card -
        (generalBidegreePositiveRealWeightedBall ellM ellX (R - d)
          hellM_pos hell).card ≤
      (⌊R / ellX⌋₊ + 1) * ⌈d / ellM⌉₊ := by
  classical
  have hellX_pos : 0 < ellX := hellM_pos.trans_le hell
  let J : ℕ := ⌊R / ellX⌋₊
  let q : ℕ := ⌈d / ellM⌉₊
  let S := generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell
  let T := generalBidegreePositiveRealWeightedBall ellM ellX (R - d)
    hellM_pos hell
  have hTsubS : T ⊆ S := by
    dsimp only [S, T]
    apply generalBidegreePositiveRealWeightedBall_subset_of_radius_le
    linarith
  let upperIndex : generalBidegreeWeightedMonomialIndex → ℕ := fun m =>
    ⌊(R - (m 1 : ℝ) * ellX) / ellM⌋₊
  have hsecond_le (m : ↥(S \ T)) : m.1 1 ≤ J := by
    have hmS : m.1 ∈ S := (Finset.mem_sdiff.mp m.2).1
    have hm_weight : generalBidegreeRealWeight ellM ellX m.1 ≤ R := by
      dsimp only [S] at hmS
      exact (mem_generalBidegreePositiveRealWeightedBall_iff
        ellM ellX R hellM_pos hell m.1).mp hmS
    have hfirst_nonneg : 0 ≤ (m.1 0 : ℝ) * ellM :=
      mul_nonneg (by positivity) hellM_pos.le
    have hsecond : (m.1 1 : ℝ) * ellX ≤ R := by
      rw [generalBidegreeRealWeight] at hm_weight
      linarith
    have hdiv : (m.1 1 : ℝ) ≤ R / ellX :=
      (le_div_iff₀ hellX_pos).mpr hsecond
    have hfloor : m.1 1 ≤ ⌊R / ellX⌋₊ := Nat.le_floor hdiv
    simpa only [J] using hfloor
  have hfirst_le_outerIndex (m : ↥(S \ T)) : m.1 0 ≤ upperIndex m.1 := by
    have hmS : m.1 ∈ S := (Finset.mem_sdiff.mp m.2).1
    have hm_weight : generalBidegreeRealWeight ellM ellX m.1 ≤ R := by
      dsimp only [S] at hmS
      exact (mem_generalBidegreePositiveRealWeightedBall_iff
        ellM ellX R hellM_pos hell m.1).mp hmS
    have hsecond_nonneg : 0 ≤ (m.1 1 : ℝ) * ellX :=
      mul_nonneg (by positivity) hellX_pos.le
    have hfirst : (m.1 0 : ℝ) * ellM ≤ R - (m.1 1 : ℝ) * ellX := by
      rw [generalBidegreeRealWeight] at hm_weight
      linarith
    have hdiv : (m.1 0 : ℝ) ≤ (R - (m.1 1 : ℝ) * ellX) / ellM :=
      (le_div_iff₀ hellM_pos).mpr hfirst
    dsimp only [upperIndex]
    exact Nat.le_floor hdiv
  have hoffset_lt (m : ↥(S \ T)) : upperIndex m.1 - m.1 0 < q := by
    have hmS : m.1 ∈ S := (Finset.mem_sdiff.mp m.2).1
    have hmT : m.1 ∉ T := (Finset.mem_sdiff.mp m.2).2
    have hm_weight_outer : generalBidegreeRealWeight ellM ellX m.1 ≤ R := by
      dsimp only [S] at hmS
      exact (mem_generalBidegreePositiveRealWeightedBall_iff
        ellM ellX R hellM_pos hell m.1).mp hmS
    have hm_weight_inner : R - d < generalBidegreeRealWeight ellM ellX m.1 := by
      apply lt_of_not_ge
      intro hle
      apply hmT
      dsimp only [T]
      exact (mem_generalBidegreePositiveRealWeightedBall_iff
        ellM ellX (R - d) hellM_pos hell m.1).mpr hle
    have hfirst_nonneg : 0 ≤ (m.1 0 : ℝ) * ellM :=
      mul_nonneg (by positivity) hellM_pos.le
    have houter_res_nonneg : 0 ≤ R - (m.1 1 : ℝ) * ellX := by
      rw [generalBidegreeRealWeight] at hm_weight_outer
      linarith
    have hupper_floor : (upperIndex m.1 : ℝ) ≤
        (R - (m.1 1 : ℝ) * ellX) / ellM := by
      dsimp only [upperIndex]
      exact Nat.floor_le (div_nonneg houter_res_nonneg hellM_pos.le)
    have hinner_first : R - d - (m.1 1 : ℝ) * ellX < (m.1 0 : ℝ) * ellM := by
      rw [generalBidegreeRealWeight] at hm_weight_inner
      linarith
    have hinner_div : (R - d - (m.1 1 : ℝ) * ellX) / ellM < (m.1 0 : ℝ) :=
      (div_lt_iff₀ hellM_pos).mpr hinner_first
    have hsub_cast : ((upperIndex m.1 - m.1 0 : ℕ) : ℝ) =
        (upperIndex m.1 : ℝ) - (m.1 0 : ℝ) := by
      exact_mod_cast Nat.cast_sub (hfirst_le_outerIndex m)
    have hoffset_lt : ((upperIndex m.1 - m.1 0 : ℕ) : ℝ) < d / ellM := by
      rw [hsub_cast]
      calc
        (upperIndex m.1 : ℝ) - (m.1 0 : ℝ) ≤
            (R - (m.1 1 : ℝ) * ellX) / ellM - (m.1 0 : ℝ) :=
          sub_le_sub_right hupper_floor _
        _ < (R - (m.1 1 : ℝ) * ellX) / ellM -
            (R - d - (m.1 1 : ℝ) * ellX) / ellM :=
          sub_lt_sub_left hinner_div _
        _ = d / ellM := by
          field_simp [ne_of_gt hellM_pos]
          ring
    have hfloor : upperIndex m.1 - m.1 0 < ⌈d / ellM⌉₊ :=
      Nat.lt_ceil.mpr hoffset_lt
    simpa only [q] using hfloor
  let f : ↥(S \ T) → Fin (J + 1) × Fin q := fun m =>
    (⟨m.1 1, by
      simpa only [Nat.succ_eq_add_one] using Nat.lt_succ_iff.mpr (hsecond_le m)⟩,
      ⟨upperIndex m.1 - m.1 0, by
      exact hoffset_lt m⟩)
  have hf : Function.Injective f := by
    intro m n hmn
    have hsecond : m.1 1 = n.1 1 := by
      have hcoord := congrArg (fun p : Fin (J + 1) × Fin q => (p.1 : ℕ)) hmn
      simpa [f] using hcoord
    have hupper_eq : upperIndex m.1 = upperIndex n.1 := by
      simp only [upperIndex, hsecond]
    have hoffset : upperIndex m.1 - m.1 0 = upperIndex n.1 - n.1 0 := by
      have hcoord := congrArg (fun p : Fin (J + 1) × Fin q => (p.2 : ℕ)) hmn
      simpa [f] using hcoord
    rw [← hupper_eq] at hoffset
    have hfirst : m.1 0 = n.1 0 := by
      have hmle := hfirst_le_outerIndex m
      have hnle : n.1 0 ≤ upperIndex m.1 := by
        rw [hupper_eq]
        exact hfirst_le_outerIndex n
      calc
        m.1 0 = upperIndex m.1 - (upperIndex m.1 - m.1 0) :=
          (Nat.sub_sub_self hmle).symm
        _ = upperIndex m.1 - (upperIndex m.1 - n.1 0) := by rw [hoffset]
        _ = n.1 0 := Nat.sub_sub_self hnle
    apply Subtype.ext
    apply Finsupp.ext
    intro k
    fin_cases k
    · exact hfirst
    · exact hsecond
  have hcard : (S \ T).card ≤ (J + 1) * q := by
    have h := Fintype.card_le_of_injective f hf
    simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_fin] using h
  change S.card - T.card ≤ (J + 1) * q
  calc
    S.card - T.card = (S \ T).card := (Finset.card_sdiff_of_subset hTsubS).symm
    _ ≤ (J + 1) * q := hcard

/-- Applying the outer-boundary shell rectangle to the parallel-line shift
gives a linear finite rank cap.  Unlike the raw ball rectangle, this grows
linearly in the weight radius `R`. -/
theorem generalBidegreeCoefficientEvaluationRank_positiveRealWeightedBall_le_shellRectangle
    (A B : ℕ) (ellM ellX R : ℝ)
    (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX) :
    generalBidegreeCoefficientEvaluationRank A B
      (generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell) ≤
      (⌊R / ellX⌋₊ + 1) *
        ⌈(((A + 1 : ℕ) : ℝ) * ellX / ellM)⌉₊ := by
  have hellX_pos : 0 < ellX := hellM_pos.trans_le hell
  have hshift_nonneg : 0 ≤ ((A + 1 : ℕ) : ℝ) * ellX :=
    mul_nonneg (by positivity) hellX_pos.le
  calc
    generalBidegreeCoefficientEvaluationRank A B
        (generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell) ≤
        (generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell).card -
          (generalBidegreePositiveRealWeightedBall ellM ellX
            (R - ((A + 1 : ℕ) : ℝ) * ellX) hellM_pos hell).card :=
      generalBidegreeCoefficientEvaluationRank_positiveRealWeightedBall_le_shifted
        A B ellM ellX R hellM_pos hell
    _ ≤ (⌊R / ellX⌋₊ + 1) *
          ⌈(((A + 1 : ℕ) : ℝ) * ellX / ellM)⌉₊ :=
      card_sub_card_generalBidegreePositiveRealWeightedBall_le_floorRectangle
        ellM ellX R (((A + 1 : ℕ) : ℝ) * ellX) hellM_pos hell hshift_nonneg

/-- A real main-term form of the linear shell rank cap.  The leading product
`R * ((A+1)*ellX) / (ellM*ellX)` is the area scale of the parallel-line
shell; the added ones are explicit lattice-boundary losses. -/
theorem generalBidegreeCoefficientEvaluationRank_positiveRealWeightedBall_cast_le_shellArea
    (A B : ℕ) (ellM ellX R : ℝ)
    (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX) (hR : 0 ≤ R) :
    (generalBidegreeCoefficientEvaluationRank A B
      (generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell) : ℕ) ≤
      (R / ellX + 1) * (((((A + 1 : ℕ) : ℝ) * ellX) / ellM) + 1) := by
  have hellX_pos : 0 < ellX := hellM_pos.trans_le hell
  have hshift_nonneg : 0 ≤ ((A + 1 : ℕ) : ℝ) * ellX :=
    mul_nonneg (by positivity) hellX_pos.le
  have hR_div_nonneg : 0 ≤ R / ellX := div_nonneg hR hellX_pos.le
  have hshift_div_nonneg : 0 ≤ (((A + 1 : ℕ) : ℝ) * ellX) / ellM :=
    div_nonneg hshift_nonneg hellM_pos.le
  push_cast at hshift_div_nonneg
  have hnat := generalBidegreeCoefficientEvaluationRank_positiveRealWeightedBall_le_shellRectangle
    A B ellM ellX R hellM_pos hell
  have hnat_cast :
      (generalBidegreeCoefficientEvaluationRank A B
        (generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell) : ℕ) ≤
        ((⌊R / ellX⌋₊ + 1 : ℕ) : ℝ) *
          (⌈(((A + 1 : ℕ) : ℝ) * ellX / ellM)⌉₊ : ℝ) := by
    exact_mod_cast hnat
  have hR_floor : ((⌊R / ellX⌋₊ + 1 : ℕ) : ℝ) ≤ R / ellX + 1 := by
    push_cast
    linarith [Nat.floor_le hR_div_nonneg]
  have hshift_floor :
      (⌈(((A + 1 : ℕ) : ℝ) * ellX / ellM)⌉₊ : ℝ) ≤
        (((A + 1 : ℕ) : ℝ) * ellX) / ellM + 1 := by
    push_cast
    exact (Nat.ceil_lt_add_one hshift_div_nonneg).le
  calc
    (generalBidegreeCoefficientEvaluationRank A B
        (generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell) : ℕ) ≤
        ((⌊R / ellX⌋₊ + 1 : ℕ) : ℝ) *
          (⌈(((A + 1 : ℕ) : ℝ) * ellX / ellM)⌉₊ : ℝ) := hnat_cast
    _ ≤ (R / ellX + 1) * (((((A + 1 : ℕ) : ℝ) * ellX) / ellM) + 1) :=
      mul_le_mul hR_floor hshift_floor (by positivity) (by positivity)

/-- The shell-rectangle cap stated directly for the exact floor-sum defect
when both radii are nonnegative. -/
theorem parallelLine_floorSumDefect_le_floorRectangle
    (A : ℕ) (ellM ellX R : ℝ) (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX)
    (hshift : 0 ≤ R - ((A + 1 : ℕ) : ℝ) * ellX) :
    generalBidegreePositiveRealWeightedFloorSum ellM ellX R -
        generalBidegreePositiveRealWeightedFloorSum ellM ellX
          (R - ((A + 1 : ℕ) : ℝ) * ellX) ≤
      (⌊R / ellX⌋₊ + 1) *
        ⌈(((A + 1 : ℕ) : ℝ) * ellX / ellM)⌉₊ := by
  have hellX_pos : 0 < ellX := hellM_pos.trans_le hell
  have hshift_nonneg : 0 ≤ ((A + 1 : ℕ) : ℝ) * ellX :=
    mul_nonneg (by positivity) hellX_pos.le
  have hR : 0 ≤ R := by linarith
  have hbound := card_sub_card_generalBidegreePositiveRealWeightedBall_le_floorRectangle
    ellM ellX R (((A + 1 : ℕ) : ℝ) * ellX) hellM_pos hell hshift_nonneg
  rw [card_generalBidegreePositiveRealWeightedBall_eq_floorSum'
        ellM ellX R hellM_pos hell hR,
    card_generalBidegreePositiveRealWeightedBall_eq_floorSum'
      ellM ellX (R - ((A + 1 : ℕ) : ℝ) * ellX) hellM_pos hell hshift] at hbound
  exact hbound

/-- A two-sided finite lattice sandwich for the exact parallel-line
floor-sum defect.  The lower bound is an inscribed rectangle, while the upper
bound records the outer horizontal range and the ceiling of the shell
thickness. -/
theorem parallelLine_floorSumDefect_floorSandwich
    (A : ℕ) (ellM ellX R : ℝ) (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX)
    (hshift : 0 ≤ R - ((A + 1 : ℕ) : ℝ) * ellX) :
    ⌊(((A + 1 : ℕ) : ℝ) * ellX / ellM)⌋₊ *
        (⌊(R - ((A + 1 : ℕ) : ℝ) * ellX) / ellX⌋₊ + 1) ≤
      generalBidegreePositiveRealWeightedFloorSum ellM ellX R -
        generalBidegreePositiveRealWeightedFloorSum ellM ellX
          (R - ((A + 1 : ℕ) : ℝ) * ellX) ∧
    generalBidegreePositiveRealWeightedFloorSum ellM ellX R -
        generalBidegreePositiveRealWeightedFloorSum ellM ellX
          (R - ((A + 1 : ℕ) : ℝ) * ellX) ≤
      (⌊R / ellX⌋₊ + 1) *
        ⌈(((A + 1 : ℕ) : ℝ) * ellX / ellM)⌉₊ := by
  exact ⟨floorRectangle_le_parallelLine_floorSumDefect
      A ellM ellX R hellM_pos hell hshift,
    parallelLine_floorSumDefect_le_floorRectangle
      A ellM ellX R hellM_pos hell hshift⟩

/-- A finite two-regime envelope for the parallel-line rank cap.  The first
entry is the exact triangular floor sum (useful below the shift), while the
second is the linear shell rectangle (useful above it).  Taking their minimum
is a literal, finite counterpart of the manuscript's two lattice regimes. -/
theorem generalBidegreeCoefficientEvaluationRank_positiveRealWeightedBall_le_twoRegimeEnvelope
    (A B : ℕ) (ellM ellX R : ℝ)
    (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX) (hR : 0 ≤ R) :
    generalBidegreeCoefficientEvaluationRank A B
      (generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell) ≤
      min (generalBidegreePositiveRealWeightedFloorSum ellM ellX R)
        ((⌊R / ellX⌋₊ + 1) *
          ⌈(((A + 1 : ℕ) : ℝ) * ellX / ellM)⌉₊) := by
  have hfloor :
      generalBidegreeCoefficientEvaluationRank A B
        (generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell) ≤
        generalBidegreePositiveRealWeightedFloorSum ellM ellX R := by
    calc
      generalBidegreeCoefficientEvaluationRank A B
          (generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell) ≤
          (generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell).card -
            (generalBidegreePositiveRealWeightedBall ellM ellX
              (R - ((A + 1 : ℕ) : ℝ) * ellX) hellM_pos hell).card :=
        generalBidegreeCoefficientEvaluationRank_positiveRealWeightedBall_le_shifted
          A B ellM ellX R hellM_pos hell
      _ ≤ (generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell).card :=
        Nat.sub_le _ _
      _ = generalBidegreePositiveRealWeightedFloorSum ellM ellX R :=
        card_generalBidegreePositiveRealWeightedBall_eq_floorSum'
          ellM ellX R hellM_pos hell hR
  exact le_min hfloor
    (generalBidegreeCoefficientEvaluationRank_positiveRealWeightedBall_le_shellRectangle
      A B ellM ellX R hellM_pos hell)

end PellPaper
