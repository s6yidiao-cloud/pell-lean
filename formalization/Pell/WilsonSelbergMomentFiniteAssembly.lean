import Pell.WilsonPrimorialOddNeutralizerBridge
import Pell.WilsonOddNeutralizerSquareTotalMass

/-!
# Finite Wilson moment assembly for full-primorial Selberg weights

This module combines the completed Cauchy, square, nonsquare, and parity
reductions.  It is agnostic about how the upper-Moebius coefficients and
their total mass are constructed.  In the Selberg application the
coefficients live on the full primorial; only the nonsquare character-sum
step passes to its odd part, which leaves the odd neutralizer unchanged.
-/

namespace PellPaper

noncomputable section

/-- The complete finite second-moment bound for upper-Moebius coefficients
on a full primorial.  The only quantitative inputs are the original
reciprocal-divisor mass `A` and the total neutralizer mass `B`; the
nonsquare term retains the explicit absolute coefficient mass. -/
theorem abs_main4OrdinaryJacobiRectangle_reciprocalDivisor_sq_le_of_primorialNeutralizer
    (a b : ℕ → ℝ) (z M N : ℕ) (lambdaPlus : ℕ → ℝ)
    (A B : ℝ) (hz : 2 ≤ z)
    (hUpper : BoundingSieve.IsUpperMoebius lambdaPlus)
    (ha : main4OddSupportedUnitBound a)
    (hb : main4OddSupportedUnitBound b)
    (hmass :
      wilsonWeightedMass b main4WilsonReciprocalDivisorWeight M ≤ A)
    (htotal :
      main4WilsonNeutralizerTotalMass (primorial z) M lambdaPlus ≤ B) :
    |main4OrdinaryJacobiRectangle a
        (fun m ↦ b m * main4WilsonReciprocalDivisorWeight m) M N| ^ 2 ≤
      A *
        (B * ((N : ℝ) * (1 + Real.log (N : ℝ))) +
          (N : ℝ) ^ 2 *
            (main4WilsonNeutralizerCoefficientMass
                (primorial z) lambdaPlus *
              (4 * (N : ℝ) *
                (1 + Real.log ((2 * (N : ℝ)) ^ 2))))) := by
  let Q := main4WilsonOddPrimorial z
  let coeffScale : ℝ :=
    4 * (N : ℝ) * (1 + Real.log ((2 * (N : ℝ)) ^ 2))
  have hcoeffScale : 0 ≤ coeffScale := by
    rcases eq_or_ne N 0 with rfl | hN
    · simp [coeffScale]
    · have hNpos : 0 < N := Nat.pos_of_ne_zero hN
      have hlog : 0 ≤ Real.log ((2 * (N : ℝ)) ^ 2) := by
        apply Real.log_nonneg
        nlinarith [show (1 : ℝ) ≤ (N : ℝ) by exact_mod_cast hNpos]
      dsimp [coeffScale]
      positivity
  apply
    abs_main4OrdinaryJacobiRectangle_reciprocalDivisor_sq_le_of_oddNeutralizer_bounds
      a b (primorial z) M N lambdaPlus A
        (B * ((N : ℝ) * (1 + Real.log (N : ℝ))))
        ((N : ℝ) ^ 2 *
          (main4WilsonNeutralizerCoefficientMass
              (primorial z) lambdaPlus * coeffScale))
  · exact squarefree_primorial z
  · exact hUpper
  · exact hb
  · exact hmass
  · exact
      abs_sum_square_wilsonOddNeutralizerCorrelation_le_of_totalMass
        a (primorial z) M N lambdaPlus B
          (squarefree_primorial z) hUpper ha.2 htotal
  · rw [main4WilsonOddNeutralizerMajorant_primorial_fun_eq
      z hz lambdaPlus]
    have hQ :=
      abs_sum_nonsquare_wilsonOddNeutralizerCorrelation_le_coefficientMass
        a Q M N (main4WilsonOddPrimorial_ne_zero hz)
          (main4WilsonOddPrimorial_odd hz) lambdaPlus ha
    apply hQ.trans
    dsimp only [Q]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg (N : ℝ))
    apply mul_le_mul_of_nonneg_right _ hcoeffScale
    exact main4WilsonNeutralizerCoefficientMass_oddPrimorial_le_primorial
      z hz lambdaPlus

end

end PellPaper
