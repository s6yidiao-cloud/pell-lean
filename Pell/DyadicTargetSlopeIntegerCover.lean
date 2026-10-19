import Pell.SlopeLatticeReciprocalMinimumSum

/-!
# A literal right-endpoint integer-center cover for dyadic target points

For `U < u ≤ 2U` and `V < v ≤ 2V`, assign the integer center
`ceil(M*U*v/(V*u))`.  This is intentionally the right-endpoint ceiling
convention: for a nonintegral normalized ratio it shifts the manuscript's
floor index by one cell.  The displacement belongs to `(-1,0]`, preserving
unit cell width, and the actual vector `(v,u)` has normalized sup norm at
most two.  The finite centers are literally `Icc ceil(M/2) floor(3M)`.

No source-to-target pairing, multiplicity bound, or curve count is asserted.
-/

namespace PellPaper

noncomputable section

/-- The finite integer centers used by the right-endpoint target cover. -/
def targetSlopeIntegerCenters (M : ℝ) : Finset ℤ :=
  Finset.Icc ⌈M / 2⌉ ⌊3 * M⌋

/-- The right-endpoint integer index of an actual dyadic target point `(u,v)`. -/
def targetSlopeRightIndex (U V M : ℝ) (u v : ℤ) : ℤ :=
  ⌈M * U * (v : ℝ) / (V * (u : ℝ))⌉

theorem targetSlopeIntegerCenters_range (M : ℝ) {k : ℤ}
    (hk : k ∈ targetSlopeIntegerCenters M) : M / 2 ≤ (k : ℝ) ∧ (k : ℝ) ≤ 3 * M := by
  obtain ⟨hl, hr⟩ := Finset.mem_Icc.mp hk
  exact ⟨Int.ceil_le.mp hl, Int.le_floor.mp hr⟩

/-- Integer centers have separation one, independently of the cutoff. -/
theorem targetSlopeIntegerCenters_separated (M : ℝ) :
    ∀ i ∈ targetSlopeIntegerCenters M, ∀ j ∈ targetSlopeIntegerCenters M,
      i ≠ j → (1 : ℝ) ≤ |(i : ℝ) - (j : ℝ)| := by
  intro i _ j _ hij
  exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hij)

/-- The exact half-open displacement for the ceiling convention. -/
theorem targetSlopeRightIndex_displacement (U V M : ℝ) (u v : ℤ) :
    -1 < M * U * (v : ℝ) / (V * (u : ℝ)) - (targetSlopeRightIndex U V M u v : ℝ) ∧
      M * U * (v : ℝ) / (V * (u : ℝ)) - (targetSlopeRightIndex U V M u v : ℝ) ≤ 0 := by
  have hl := Int.le_ceil (M * U * (v : ℝ) / (V * (u : ℝ)))
  have hu := Int.ceil_lt_add_one (M * U * (v : ℝ) / (V * (u : ℝ)))
  dsimp [targetSlopeRightIndex]
  constructor <;> linarith

/-- Every actual integer point in the target dyadic box has its assigned
right-endpoint center in the literal finite center interval. -/
theorem targetSlopeRightIndex_mem_integerCenters
    (U V M : ℝ) (hU : 0 < U) (hV : 0 < V) (hM : 1 ≤ M)
    (u v : ℤ) (hu : U < (u : ℝ) ∧ (u : ℝ) ≤ 2 * U)
    (hv : V < (v : ℝ) ∧ (v : ℝ) ≤ 2 * V) :
    targetSlopeRightIndex U V M u v ∈ targetSlopeIntegerCenters M := by
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hupos : 0 < (u : ℝ) := hU.trans hu.1
  let r := M * U * (v : ℝ) / (V * (u : ℝ))
  have hrlo : M / 2 ≤ r := by
    apply (le_div_iff₀ (mul_pos hV hupos)).mpr
    calc
      (M / 2) * (V * (u : ℝ)) ≤ (M / 2) * (V * (2 * U)) := by gcongr; exact hu.2
      _ = M * U * V := by ring
      _ ≤ M * U * (v : ℝ) := mul_le_mul_of_nonneg_left hv.1.le (by positivity)
  have hrhi : r ≤ 2 * M := by
    apply (div_le_iff₀ (mul_pos hV hupos)).mpr
    calc
      M * U * (v : ℝ) ≤ M * U * (2 * V) := mul_le_mul_of_nonneg_left hv.2 (by positivity)
      _ = (2 * M * V) * U := by ring
      _ ≤ (2 * M * V) * (u : ℝ) := mul_le_mul_of_nonneg_left hu.1.le (by positivity)
      _ = (2 * M) * (V * (u : ℝ)) := by ring
  have hklo : M / 2 ≤ (targetSlopeRightIndex U V M u v : ℝ) := hrlo.trans (Int.le_ceil r)
  have hkhi : (targetSlopeRightIndex U V M u v : ℝ) ≤ 3 * M := by
    have hceil : (targetSlopeRightIndex U V M u v : ℝ) < r + 1 := Int.ceil_lt_add_one r
    linarith
  exact Finset.mem_Icc.mpr ⟨Int.ceil_le.mpr hklo, Int.le_floor.mpr hkhi⟩

/-- The actual integer vector `(v,u)` has normalized sup norm at most two
in its assigned right-endpoint target cell. -/
theorem targetSlopeRightIndex_supNorm_le_two
    (U V M : ℝ) (hU : 0 < U) (hV : 0 < V)
    (u v : ℤ) (hu : U < (u : ℝ) ∧ (u : ℝ) ≤ 2 * U) :
    slopeVectorSupNorm U V M (targetSlopeRightIndex U V M u v : ℝ) (v, u) ≤ 2 := by
  have hupos : 0 < (u : ℝ) := hU.trans hu.1
  let r := M * U * (v : ℝ) / (V * (u : ℝ))
  let k := targetSlopeRightIndex U V M u v
  have hdisp : |r - (k : ℝ)| ≤ 1 := by
    have hd := targetSlopeRightIndex_displacement U V M u v
    exact abs_le.mpr ⟨hd.1.le, hd.2.trans (by norm_num)⟩
  have hratio : (u : ℝ) / U ≤ 2 := (div_le_iff₀ hU).mpr hu.2
  have heq : M * (v : ℝ) / V - (k : ℝ) * (u : ℝ) / U =
      ((u : ℝ) / U) * (r - (k : ℝ)) := by
    dsimp [r]
    field_simp
  apply max_le
  · change |M * (v : ℝ) / V - (k : ℝ) * (u : ℝ) / U| ≤ 2
    calc
      |M * (v : ℝ) / V - (k : ℝ) * (u : ℝ) / U| =
          ((u : ℝ) / U) * |r - (k : ℝ)| := by rw [heq, abs_mul, abs_of_pos (div_pos hupos hU)]
      _ ≤ ((u : ℝ) / U) * 1 := mul_le_mul_of_nonneg_left hdisp (div_nonneg hupos.le hU.le)
      _ ≤ 2 := by simpa only [mul_one] using hratio
  · change |(u : ℝ) / U| ≤ 2
    simpa only [abs_of_pos (div_pos hupos hU)] using hratio

/-- Literal finite target-cover coverage for every actual dyadic target point. -/
theorem exists_integerCenter_covering_dyadic_target
    (U V M : ℝ) (hU : 0 < U) (hV : 0 < V) (hM : 1 ≤ M)
    (u v : ℤ) (hu : U < (u : ℝ) ∧ (u : ℝ) ≤ 2 * U)
    (hv : V < (v : ℝ) ∧ (v : ℝ) ≤ 2 * V) :
    ∃ k ∈ targetSlopeIntegerCenters M, slopeVectorSupNorm U V M (k : ℝ) (v, u) ≤ 2 :=
  ⟨targetSlopeRightIndex U V M u v,
    targetSlopeRightIndex_mem_integerCenters U V M hU hV hM u v hu hv,
    targetSlopeRightIndex_supNorm_le_two U V M hU hV u v hu⟩

/-- The sum of actual reciprocal first minima over the literal target-center
interval has explicit coefficient sixty-four; no center premises remain. -/
theorem sum_reciprocalFirstSlopeSupNorm_integerCenters_le
    (U V M : ℝ) (hU : 0 < U) (hV : 0 < V) (hM : 1 ≤ M) :
    (∑ k ∈ targetSlopeIntegerCenters M, reciprocalFirstSlopeSupNorm U V M (k : ℝ)) ≤
      64 * (Real.sqrt (U * V * M) + U + V) *
        (1 + Real.log (1 + U / Real.sqrt (U * V / M))) := by
  have hbound := sum_reciprocalFirstSlopeSupNorm_le (targetSlopeIntegerCenters M)
    (fun k : ℤ => (k : ℝ)) U V M 3 1 hU hV hM (by norm_num) (by norm_num)
    (fun _ hk => targetSlopeIntegerCenters_range M hk) (targetSlopeIntegerCenters_separated M)
  norm_num at hbound ⊢
  exact hbound

end

end PellPaper
