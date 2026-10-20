import Mathlib.Order.Northcott
import Mathlib.Data.Int.Interval
import Pell.SlopeLatticeShortVectorExistence

/-!
# An attained positive first sup-norm minimum for the slope map

The displayed map on integer pairs is `(a,b) ↦ (M*a/V-z*b/U,b/U)`.
Positive `U,V,M` give finite bounded sup-norm sublevels by explicit integer
coordinate bounds.  The first minimum on nonzero pairs is therefore attained
and positive.  No supplied attainment, lattice-minimum, center-cover, or
curve-count assumption is used.
-/

namespace PellPaper

noncomputable section

/-- The literal sup norm of the normalized slope-map image of an integer pair. -/
def slopeVectorSupNorm (U V M z : ℝ) (v : ℤ × ℤ) : ℝ :=
  max |M * (v.1 : ℝ) / V - z * (v.2 : ℝ) / U| |(v.2 : ℝ) / U|

theorem slopeVectorSupNorm_nonneg (U V M z : ℝ) (v : ℤ × ℤ) :
    0 ≤ slopeVectorSupNorm U V M z v :=
  (abs_nonneg _).trans (le_max_right _ _)

/-- Explicit bounded-sublevel coordinate bounds; the radius may be any real
number, since a nonempty sublevel already forces it to be nonnegative. -/
theorem abs_coordinates_le_of_slopeVectorSupNorm_le
    (U V M z R : ℝ) (hU : 0 < U) (hV : 0 < V) (hM : 0 < M)
    (v : ℤ × ℤ) (hv : slopeVectorSupNorm U V M z v ≤ R) :
    |(v.1 : ℝ)| ≤ (V / M) * (1 + |z|) * R ∧ |(v.2 : ℝ)| ≤ U * R := by
  obtain ⟨hfirst, hsecond⟩ := max_le_iff.mp hv
  have hb : |(v.2 : ℝ)| ≤ U * R := by
    rw [abs_div, abs_of_pos hU] at hsecond
    simpa only [mul_comm] using (div_le_iff₀ hU).mp hsecond
  have hzterm : |z * (v.2 : ℝ) / U| ≤ |z| * R := by
    calc
      |z * (v.2 : ℝ) / U| = |z| * |(v.2 : ℝ)| / U := by
        rw [abs_div, abs_mul, abs_of_pos hU]
      _ ≤ |z| * (U * R) / U := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hb (abs_nonneg _)) hU.le
      _ = |z| * R := by field_simp
  have haterm : |M * (v.1 : ℝ) / V| ≤ (1 + |z|) * R := by
    calc
      |M * (v.1 : ℝ) / V| =
          |(M * (v.1 : ℝ) / V - z * (v.2 : ℝ) / U) + z * (v.2 : ℝ) / U| := by
        congr 1
        ring
      _ ≤ |M * (v.1 : ℝ) / V - z * (v.2 : ℝ) / U| + |z * (v.2 : ℝ) / U| :=
        abs_add_le _ _
      _ ≤ R + |z| * R := add_le_add hfirst hzterm
      _ = (1 + |z|) * R := by ring
  have ha : |(v.1 : ℝ)| ≤ (V / M) * (1 + |z|) * R := by
    rw [abs_div, abs_mul, abs_of_pos hM, abs_of_pos hV] at haterm
    have hh := (div_le_iff₀ hV).mp haterm
    calc
      |(v.1 : ℝ)| ≤ ((1 + |z|) * R) * V / M :=
        (le_div_iff₀ hM).mpr (by simpa only [mul_comm] using hh)
      _ = (V / M) * (1 + |z|) * R := by ring
  exact ⟨ha, hb⟩

/-- Every real-radius sublevel is finite, proved by an explicit integer box. -/
theorem finite_slopeVectorSupNorm_sublevel
    (U V M z R : ℝ) (hU : 0 < U) (hV : 0 < V) (hM : 0 < M) :
    {v : ℤ × ℤ | slopeVectorSupNorm U V M z v ≤ R}.Finite := by
  let A := (V / M) * (1 + |z|) * R
  let B := U * R
  apply (Set.finite_Icc ((⌈-A⌉ : ℤ), (⌈-B⌉ : ℤ)) (⌊A⌋, ⌊B⌋)).subset
  intro v hv
  obtain ⟨ha, hb⟩ := abs_coordinates_le_of_slopeVectorSupNorm_le U V M z R hU hV hM v hv
  obtain ⟨hal, har⟩ := abs_le.mp ha
  obtain ⟨hbl, hbr⟩ := abs_le.mp hb
  exact ⟨⟨Int.ceil_le.mpr hal, Int.ceil_le.mpr hbl⟩,
    ⟨Int.le_floor.mpr har, Int.le_floor.mpr hbr⟩⟩

/-- The actual normalized integer-vector sup norm has the Northcott property. -/
theorem northcott_slopeVectorSupNorm
    (U V M z : ℝ) (hU : 0 < U) (hV : 0 < V) (hM : 0 < M) :
    Northcott (slopeVectorSupNorm U V M z) :=
  ⟨fun R => finite_slopeVectorSupNorm_sublevel U V M z R hU hV hM⟩

/-- Invertibility of the displayed map, expressed at its zero sup-norm fiber. -/
theorem slopeVectorSupNorm_eq_zero_iff
    (U V M z : ℝ) (hU : 0 < U) (hV : 0 < V) (hM : 0 < M) (v : ℤ × ℤ) :
    slopeVectorSupNorm U V M z v = 0 ↔ v = 0 := by
  constructor
  · intro hv
    have hmax := max_le_iff.mp hv.le
    have hbdiv : (v.2 : ℝ) / U = 0 :=
      abs_eq_zero.mp (le_antisymm hmax.2 (abs_nonneg _))
    have hbR : (v.2 : ℝ) = 0 := (div_eq_zero_iff.mp hbdiv).resolve_right hU.ne'
    have hb : v.2 = 0 := by exact_mod_cast hbR
    have hadiv : M * (v.1 : ℝ) / V = 0 := by
      apply abs_eq_zero.mp
      exact le_antisymm (by simpa only [hb, Int.cast_zero, mul_zero, zero_div, sub_zero]
        using hmax.1) (abs_nonneg _)
    have haR : (v.1 : ℝ) = 0 :=
      (mul_eq_zero.mp ((div_eq_zero_iff.mp hadiv).resolve_right hV.ne')).resolve_left hM.ne'
    have ha : v.1 = 0 := by exact_mod_cast haR
    exact Prod.ext ha hb
  · intro hv
    subst v
    simp [slopeVectorSupNorm]

theorem slopeVectorSupNorm_pos
    (U V M z : ℝ) (hU : 0 < U) (hV : 0 < V) (hM : 0 < M)
    (v : ℤ × ℤ) (hv : v ≠ 0) : 0 < slopeVectorSupNorm U V M z v := by
  have hne : slopeVectorSupNorm U V M z v ≠ 0 :=
    mt (slopeVectorSupNorm_eq_zero_iff U V M z hU hV hM v).mp hv
  exact lt_of_le_of_ne (slopeVectorSupNorm_nonneg U V M z v) hne.symm

/-- The first sup-norm minimum is attained by an actual nonzero integer pair,
is positive, and satisfies the determinant-scale bound with constant one. -/
theorem exists_positive_first_slopeVectorSupNorm
    (U V M z : ℝ) (hU : 0 < U) (hV : 0 < V) (hM : 0 < M) :
    ∃ v : ℤ × ℤ, v ≠ 0 ∧ 0 < slopeVectorSupNorm U V M z v ∧
      (∀ w : ℤ × ℤ, w ≠ 0 → slopeVectorSupNorm U V M z v ≤ slopeVectorSupNorm U V M z w) ∧
      slopeVectorSupNorm U V M z v ≤ Real.sqrt (M / (U * V)) := by
  let := northcott_slopeVectorSupNorm U V M z hU hV hM
  obtain ⟨v, hv, hmin⟩ := Northcott.exists_min_image (slopeVectorSupNorm U V M z)
    {w : ℤ × ℤ | w ≠ 0} ⟨(1, 0), by simp⟩
  obtain ⟨a, b, hab, hbound⟩ :=
    exists_nonzero_int_slope_vector_sup_norm_le_sqrt U V M z hU hV hM
  have habne : (a, b) ≠ (0 : ℤ × ℤ) := by
    intro heq
    have ha := congrArg Prod.fst heq
    have hb := congrArg Prod.snd heq
    rcases hab with ha' | hb'
    · exact ha' ha
    · exact hb' hb
  exact ⟨v, hv, slopeVectorSupNorm_pos U V M z hU hV hM v hv,
    hmin, (hmin (a, b) habne).trans hbound⟩

/-- The actual first sup-norm value, defined as the infimum of the norms of
all nonzero integer vectors.  Positivity and attainment are proved below
for positive normalization parameters, not supplied as hypotheses. -/
def firstSlopeSupNorm (U V M z : ℝ) : ℝ :=
  sInf (slopeVectorSupNorm U V M z '' {v : ℤ × ℤ | v ≠ 0})

/-- The actual infimum is positive, attained, globally minimal, and at most
the square root of the determinant of the displayed slope map. -/
theorem firstSlopeSupNorm_spec
    (U V M z : ℝ) (hU : 0 < U) (hV : 0 < V) (hM : 0 < M) :
    0 < firstSlopeSupNorm U V M z ∧
      (∃ v : ℤ × ℤ, v ≠ 0 ∧ slopeVectorSupNorm U V M z v = firstSlopeSupNorm U V M z) ∧
      (∀ v : ℤ × ℤ, v ≠ 0 → firstSlopeSupNorm U V M z ≤ slopeVectorSupNorm U V M z v) ∧
      firstSlopeSupNorm U V M z ≤ Real.sqrt (M / (U * V)) := by
  obtain ⟨v, hv, hpos, hmin, hupper⟩ :=
    exists_positive_first_slopeVectorSupNorm U V M z hU hV hM
  have hleast : IsLeast (slopeVectorSupNorm U V M z '' {w : ℤ × ℤ | w ≠ 0})
      (slopeVectorSupNorm U V M z v) := by
    refine ⟨⟨v, hv, rfl⟩, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    exact hmin w hw
  have heq : firstSlopeSupNorm U V M z = slopeVectorSupNorm U V M z v := hleast.csInf_eq
  rw [heq]
  exact ⟨hpos, ⟨v, hv, rfl⟩, hmin, hupper⟩

theorem firstSlopeSupNorm_pos
    (U V M z : ℝ) (hU : 0 < U) (hV : 0 < V) (hM : 0 < M) :
    0 < firstSlopeSupNorm U V M z :=
  (firstSlopeSupNorm_spec U V M z hU hV hM).1

theorem exists_nonzero_slopeVector_attaining_firstSupNorm
    (U V M z : ℝ) (hU : 0 < U) (hV : 0 < V) (hM : 0 < M) :
    ∃ v : ℤ × ℤ, v ≠ 0 ∧ slopeVectorSupNorm U V M z v = firstSlopeSupNorm U V M z :=
  (firstSlopeSupNorm_spec U V M z hU hV hM).2.1

theorem firstSlopeSupNorm_le
    (U V M z : ℝ) (hU : 0 < U) (hV : 0 < V) (hM : 0 < M)
    (v : ℤ × ℤ) (hv : v ≠ 0) :
    firstSlopeSupNorm U V M z ≤ slopeVectorSupNorm U V M z v :=
  (firstSlopeSupNorm_spec U V M z hU hV hM).2.2.1 v hv

theorem firstSlopeSupNorm_le_sqrt
    (U V M z : ℝ) (hU : 0 < U) (hV : 0 < V) (hM : 0 < M) :
    firstSlopeSupNorm U V M z ≤ Real.sqrt (M / (U * V)) :=
  (firstSlopeSupNorm_spec U V M z hU hV hM).2.2.2

end

end PellPaper
