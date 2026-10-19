import Pell.CorollaryOddClassMain4WilsonPublishedInputs
import Pell.FriedlanderIwaniecTranspose

/-!
# The proved Friedlander--Iwaniec input for Main4

This module identifies the ordinary rectangle used in the manuscript with the
source-oriented Jacobi bilinear sum and transports the fully proved real
Friedlander--Iwaniec estimate into the previously named Main4 interface.
-/

namespace PellPaper

noncomputable section

/-- The Main4 rectangle is the FI bilinear sum after commuting its two finite
sums and swapping the names of the two cutoffs. -/
theorem main4OrdinaryJacobiRectangle_eq_friedlanderIwaniecJacobiBilinear
    (a b : ℕ → ℝ) (M N : ℕ) :
    main4OrdinaryJacobiRectangle a b M N =
      friedlanderIwaniecJacobiBilinear a b N M := by
  symm
  simpa only [main4OrdinaryJacobiRectangle] using
    friedlanderIwaniecJacobiBilinear_eq_sum_modulus a b N M

/-- For positive cutoffs, the negative-sixth-power presentation used in
Main4 is exactly the two-monomial presentation in FI equation (17). -/
theorem friedlanderIwaniecBilinearScale_eq_main4
    (M N : ℕ) (hM : 1 ≤ M) (hN : 1 ≤ N) :
    friedlanderIwaniecBilinearScale N M =
      main4FriedlanderIwaniecRectangleScale M N := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (Nat.zero_lt_of_lt hM)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hMCancel :
      (M : ℝ) * (M : ℝ) ^ (-1 / 6 : ℝ) =
        (M : ℝ) ^ (5 / 6 : ℝ) := by
    calc
      (M : ℝ) * (M : ℝ) ^ (-1 / 6 : ℝ) =
          (M : ℝ) ^ (1 : ℝ) * (M : ℝ) ^ (-1 / 6 : ℝ) := by
        rw [Real.rpow_one]
      _ = (M : ℝ) ^ ((1 : ℝ) + (-1 / 6 : ℝ)) :=
        (Real.rpow_add hM0 _ _).symm
      _ = (M : ℝ) ^ (5 / 6 : ℝ) := by norm_num
  have hNCancel :
      (N : ℝ) * (N : ℝ) ^ (-1 / 6 : ℝ) =
        (N : ℝ) ^ (5 / 6 : ℝ) := by
    calc
      (N : ℝ) * (N : ℝ) ^ (-1 / 6 : ℝ) =
          (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-1 / 6 : ℝ) := by
        rw [Real.rpow_one]
      _ = (N : ℝ) ^ ((1 : ℝ) + (-1 / 6 : ℝ)) :=
        (Real.rpow_add hN0 _ _).symm
      _ = (N : ℝ) ^ (5 / 6 : ℝ) := by norm_num
  have hcore :
      (M : ℝ) * (N : ℝ) *
          ((N : ℝ) ^ (-1 / 6 : ℝ) +
            (M : ℝ) ^ (-1 / 6 : ℝ)) =
        (M : ℝ) * (N : ℝ) ^ (5 / 6 : ℝ) +
          (M : ℝ) ^ (5 / 6 : ℝ) * (N : ℝ) := by
    calc
      (M : ℝ) * (N : ℝ) *
          ((N : ℝ) ^ (-1 / 6 : ℝ) +
            (M : ℝ) ^ (-1 / 6 : ℝ)) =
          (M : ℝ) * ((N : ℝ) * (N : ℝ) ^ (-1 / 6 : ℝ)) +
            ((M : ℝ) * (M : ℝ) ^ (-1 / 6 : ℝ)) * (N : ℝ) := by
        ring
      _ = (M : ℝ) * (N : ℝ) ^ (5 / 6 : ℝ) +
          (M : ℝ) ^ (5 / 6 : ℝ) * (N : ℝ) := by
        rw [hNCancel, hMCancel]
  unfold friedlanderIwaniecBilinearScale
  unfold main4FriedlanderIwaniecRectangleScale
  rw [hcore]
  have hlogArg :
      3 * (N : ℝ) * (M : ℝ) = 3 * (M : ℝ) * (N : ℝ) := by
    ring
  rw [hlogArg]
  ring

/-- The Main4 real specialization of FI equation (17), with the explicit
absolute constant four delivered by the proved transpose argument. -/
theorem main4FriedlanderIwaniecRectangleEstimateWith_four :
    Main4FriedlanderIwaniecRectangleEstimateWith 4 := by
  intro M N hM hN a b ha hb
  rw [main4OrdinaryJacobiRectangle_eq_friedlanderIwaniecJacobiBilinear,
    ← friedlanderIwaniecBilinearScale_eq_main4 M N (by omega) (by omega)]
  exact abs_friedlanderIwaniecJacobiBilinear_le_four_mul_scale
    a b N M hN hM ha.1 hb.1 ha.2 hb.2

/-- The previously external FI rectangle proposition is now inhabited. -/
theorem main4FriedlanderIwaniecRectangleEstimate_proved :
    Main4FriedlanderIwaniecRectangleEstimate := by
  exact ⟨4, by norm_num, main4FriedlanderIwaniecRectangleEstimateWith_four⟩

end

end PellPaper
