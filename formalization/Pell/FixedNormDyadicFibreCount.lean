import Pell.FixedNormLinearQCount
import Pell.DyadicFactorScaleComparability

/-!
# Counting a literal fixed-parameter dyadic Pell fibre

The dyadic indices have the actual `(d,e,u,v)` order. The scale used here is
the manuscript's `x=E^2*V`, not a rescaled determinant parameter. Box
membership supplies the weighted-square cutoff. For a finite natural-pair
family at fixed raw `u,v,h`, the actual factor condition supplies positivity,
squarefreeness and nonsquareness; the real-parameter count then gives `24*Q`.
No transformed target-slope reconstruction or global aggregation is asserted.
-/

namespace PellPaper

/-- Literal box membership bounds the actual first weighted square by
eight times the unrescaled endpoint scale `E^2*V`. -/
theorem dyadicBox_weighted_square_le_eight_mul_scale
    {i : ℕ × ℕ × ℕ × ℕ} {d e u v : ℕ}
    (hbox : (d, e, u, v) ∈ dyadicBox i) :
    (v : ℝ) * (e : ℝ) ^ 2 ≤
      8 * (((2 ^ i.2.1 : ℕ) : ℝ) ^ 2 * ((2 ^ i.2.2.2 : ℕ) : ℝ)) := by
  have hb := dyadicBox_coordinate_upper_bounds hbox
  have he : (e : ℝ) ≤ 2 * ((2 ^ i.2.1 : ℕ) : ℝ) := by exact_mod_cast hb.2.1
  have hv : (v : ℝ) ≤ 2 * ((2 ^ i.2.2.2 : ℕ) : ℝ) := by exact_mod_cast hb.2.2.2
  have he2 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ e) he 2
  calc
    (v : ℝ) * (e : ℝ) ^ 2 ≤
        (2 * ((2 ^ i.2.2.2 : ℕ) : ℝ)) * (2 * ((2 ^ i.2.1 : ℕ) : ℝ)) ^ 2 :=
      mul_le_mul hv he2 (sq_nonneg _) (by positivity)
    _ = _ := by ring

/-- A finite family of natural `(d,e)` in one actual dyadic box at fixed
raw `u,v,h` costs at most `24*Q`. The signed level and nonsquare Pell
parameter are derived from the actual factor condition when nonempty. -/
theorem card_dyadic_fixedNorm_pairs_le_twentyFour_mul_Q
    (θ Q : ℝ) (Y u v : ℕ) (h : ℤ) (i : ℕ × ℕ × ℕ × ℕ)
    (hY : 2 ≤ Y) (hQ : 2 ≤ Q)
    (hxQ : ((2 ^ i.2.1 : ℕ) : ℝ) ^ 2 * ((2 ^ i.2.2.2 : ℕ) : ℝ) ≤
      (Y : ℝ) ^ (2 * Q))
    (S : Finset (ℕ × ℕ))
    (hcond : ∀ z ∈ S, DyadicFactorCondition θ Y z.1 z.2 u v)
    (hbox : ∀ z ∈ S, (z.1, z.2, u, v) ∈ dyadicBox i)
    (hn : ∀ z ∈ S, (v : ℤ) * (z.2 : ℤ) ^ 2 - (u : ℤ) * (z.1 : ℤ) ^ 2 = h) :
    (S.card : ℝ) ≤ 24 * Q := by
  classical
  by_cases hempty : S = ∅
  · simp only [hempty, Finset.card_empty, Nat.cast_zero]
    linarith
  obtain ⟨z, hz⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  rcases hcond z hz with
    ⟨_, _, hu, hv, _, _, _, _, hsu, hsv, hcop, hYuv, _⟩
  have hsf : Squarefree (u * v) := (Nat.squarefree_mul hcop).mpr ⟨hsu, hsv⟩
  have hnsN : ¬ IsSquare (u * v) := by
    rintro ⟨k, hk⟩
    have hkunit : IsUnit k := hsf k (by rw [hk])
    have huv1 : u * v = 1 := by simpa [Nat.isUnit_iff.mp hkunit] using hk
    omega
  have hns : ¬ IsSquare ((u : ℤ) * v) := by
    simpa only [← Nat.cast_mul, Int.isSquare_natCast_iff] using hnsN
  obtain ⟨h', hh', heq⟩ := dyadicFactorCondition_exists_difference (hcond z hz)
  have hheq : h' = h := by
    rw [← heq, ← hn z hz]
    ring
  have hh : IsSignedDyadicDifference h := hheq ▸ hh'
  let f : (ℕ × ℕ) → ℤ × ℤ := fun z => (z.1, z.2)
  have hf : Function.Injective f := by
    intro a b hab
    dsimp [f] at hab
    apply Prod.ext
    · have hfst : (a.1 : ℤ) = (b.1 : ℤ) := congrArg Prod.fst hab
      exact_mod_cast hfst
    · have hsnd : (a.2 : ℤ) = (b.2 : ℤ) := congrArg Prod.snd hab
      exact_mod_cast hsnd
  have hx : 1 ≤ ((2 ^ i.2.1 : ℕ) : ℝ) ^ 2 * ((2 ^ i.2.2.2 : ℕ) : ℝ) := by
    have hE : (1 : ℝ) ≤ ((2 ^ i.2.1 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.one_le_two_pow : 1 ≤ 2 ^ i.2.1)
    have hV : (1 : ℝ) ≤ ((2 ^ i.2.2.2 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.one_le_two_pow : 1 ≤ 2 ^ i.2.2.2)
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hE) hV
  have hc := card_fixedNorm_points_le_twentyFour_mul_Q (u : ℤ) v h Y Q
    (((2 ^ i.2.1 : ℕ) : ℝ) ^ 2 * ((2 ^ i.2.2.2 : ℕ) : ℝ))
    (by exact_mod_cast hu) (by exact_mod_cast hv) hns hh
    (by exact_mod_cast hY) hQ hx (by exact_mod_cast hYuv) hxQ (S.image f)
    (by
      intro w hw
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hw
      have hpcond := hcond p hp
      dsimp [f]
      exact ⟨by exact_mod_cast hpcond.1, by exact_mod_cast hpcond.2.1⟩)
    (by
      intro w hw
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hw
      exact hn p hp)
    (by
      intro w hw
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hw
      simpa [f] using dyadicBox_weighted_square_le_eight_mul_scale (hbox p hp))
  simpa only [Finset.card_image_of_injective _ hf] using hc

end PellPaper
