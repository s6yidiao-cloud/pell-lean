import Pell.CorollaryOddClassMain4WilsonPublishedInputs

/-!
# Algebraic scale handoff for Wilson's finite Selberg moment

This module contains only the real-variable algebra which turns the finite
second-moment estimate produced by the Selberg neutralizer into the exact
two-term scale used by `main4WilsonWeightedRectangleScale`.  The arithmetic
and sieve inputs remain explicit hypotheses.
-/

namespace PellPaper

noncomputable section

/-- The finite Wilson moment bound, together with the three quantitative
Selberg inputs, implies the published weighted-rectangle scale. -/
theorem abs_le_four_hundred_mul_main4WilsonWeightedRectangleScale_of_moment_bounds
    {M N : ℕ} {S A B E : ℝ}
    (hM : 2 ≤ M) (hN : 2 ≤ N)
    (_hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (hE0 : 0 ≤ E)
    (hA : A ≤
      80 * ((M : ℝ) / Real.sqrt (Real.log (M : ℝ))))
    (hB : B ≤
      80 * ((M : ℝ) / Real.sqrt (Real.log (M : ℝ))))
    (hE : E ≤ 64 * (M : ℝ) ^ (3 / 50 : ℝ))
    (hS : |S| ^ 2 ≤
      A *
        (B * ((N : ℝ) * (1 + Real.log (N : ℝ))) +
          (N : ℝ) ^ 2 *
            (E *
              (4 * (N : ℝ) *
                (1 + Real.log ((2 * (N : ℝ)) ^ 2)))))) :
    |S| ≤ 400 * main4WilsonWeightedRectangleScale M N := by
  let m : ℝ := M
  let n : ℝ := N
  let ellM : ℝ := Real.log m
  let ellN : ℝ := Real.log n
  let mass : ℝ := m / Real.sqrt ellM
  let firstScale : ℝ :=
    m * Real.sqrt n * ellN / Real.sqrt ellM
  let secondScale : ℝ :=
    m ^ (2 / 3 : ℝ) * n ^ (3 / 2 : ℝ) * Real.sqrt ellN /
      ellM ^ (1 / 4 : ℝ)

  have hmTwo : (2 : ℝ) ≤ m := by
    dsimp [m]
    exact_mod_cast hM
  have hmOne : (1 : ℝ) ≤ m := by linarith
  have hmPos : 0 < m := zero_lt_one.trans_le hmOne
  have hnTwo : (2 : ℝ) ≤ n := by
    dsimp [n]
    exact_mod_cast hN
  have hnPos : 0 < n := by positivity
  have hellM : 0 < ellM := by
    dsimp [ellM]
    exact Real.log_pos (lt_of_lt_of_le one_lt_two hmTwo)
  have hellN : 0 < ellN := by
    dsimp [ellN]
    exact Real.log_pos (lt_of_lt_of_le one_lt_two hnTwo)
  have hsqrtEllM : 0 < Real.sqrt ellM := Real.sqrt_pos.2 hellM

  have hlogTwoLe : Real.log 2 ≤ ellN := by
    dsimp [ellN, n]
    exact Real.log_le_log (by norm_num) (by exact_mod_cast hN)
  have hlogTwoLower : (2 / 3 : ℝ) ≤ Real.log 2 := by
    exact ((by norm_num : (2 / 3 : ℝ) < 0.6931471803).trans
      Real.log_two_gt_d9).le
  have hellNLower : (2 / 3 : ℝ) ≤ ellN :=
    hlogTwoLower.trans hlogTwoLe
  have hOneLeTwoEllN : (1 : ℝ) ≤ 2 * ellN := by
    nlinarith [hellNLower]
  have hellNSqLower : (2 / 3 : ℝ) * ellN ≤ ellN ^ 2 := by
    calc
      (2 / 3 : ℝ) * ellN ≤ ellN * ellN :=
        mul_le_mul_of_nonneg_right hellNLower hellN.le
      _ = ellN ^ 2 := by ring
  have hOneAddLog : 1 + ellN ≤ 4 * ellN ^ 2 := by
    nlinarith [hellNSqLower, hellNLower]
  have hWideLogIdentity :
      Real.log ((2 * n) ^ 2) = 2 * (Real.log 2 + ellN) := by
    dsimp [ellN]
    rw [Real.log_pow, Real.log_mul (by norm_num) hnPos.ne']
    norm_num
  have hWideLog :
      1 + Real.log ((2 * n) ^ 2) ≤ 6 * ellN := by
    rw [hWideLogIdentity]
    nlinarith [hOneLeTwoEllN, hlogTwoLe]
  have hWideLog0 : 0 ≤ 1 + Real.log ((2 * n) ^ 2) := by
    rw [hWideLogIdentity]
    positivity

  have hmSmallPower :
      m ^ (3 / 50 : ℝ) ≤ m ^ (1 / 3 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hmOne (by norm_num)
  have hmPowerProduct :
      m * m ^ (3 / 50 : ℝ) ≤ m ^ (4 / 3 : ℝ) := by
    calc
      m * m ^ (3 / 50 : ℝ) ≤
          m * m ^ (1 / 3 : ℝ) :=
        mul_le_mul_of_nonneg_left hmSmallPower hmPos.le
      _ = m ^ (1 : ℝ) * m ^ (1 / 3 : ℝ) := by rw [Real.rpow_one]
      _ = m ^ ((1 : ℝ) + 1 / 3) := (Real.rpow_add hmPos _ _).symm
      _ = m ^ (4 / 3 : ℝ) := by norm_num
  have hmassPower :
      mass * m ^ (3 / 50 : ℝ) ≤
        m ^ (4 / 3 : ℝ) / Real.sqrt ellM := by
    dsimp [mass]
    rw [show m / Real.sqrt ellM * m ^ (3 / 50 : ℝ) =
      (m * m ^ (3 / 50 : ℝ)) / Real.sqrt ellM by ring]
    exact (div_le_div_iff_of_pos_right hsqrtEllM).2 hmPowerProduct

  have hfirstScaleSq :
      firstScale ^ 2 = mass ^ 2 * n * ellN ^ 2 := by
    dsimp [firstScale, mass]
    calc
      (m * Real.sqrt n * ellN / Real.sqrt ellM) ^ 2 =
          (m / Real.sqrt ellM) ^ 2 * (Real.sqrt n) ^ 2 * ellN ^ 2 := by
        ring
      _ = (m / Real.sqrt ellM) ^ 2 * n * ellN ^ 2 := by
        rw [Real.sq_sqrt hnPos.le]

  have hmRpowSq :
      (m ^ (2 / 3 : ℝ)) ^ 2 = m ^ (4 / 3 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hmPos.le]
    norm_num
  have hnRpowSq :
      (n ^ (3 / 2 : ℝ)) ^ 2 = n ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnPos.le]
    norm_num
  have hquartSq :
      (ellM ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt ellM := by
    rw [Real.sqrt_eq_rpow]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hellM.le]
    norm_num
  have hsecondScaleSq :
      secondScale ^ 2 =
        (m ^ (4 / 3 : ℝ) / Real.sqrt ellM) * n ^ 3 * ellN := by
    dsimp [secondScale]
    calc
      (m ^ (2 / 3 : ℝ) * n ^ (3 / 2 : ℝ) * Real.sqrt ellN /
          ellM ^ (1 / 4 : ℝ)) ^ 2 =
        (m ^ (2 / 3 : ℝ)) ^ 2 *
            (n ^ (3 / 2 : ℝ)) ^ 2 * (Real.sqrt ellN) ^ 2 /
              (ellM ^ (1 / 4 : ℝ)) ^ 2 := by ring
      _ = m ^ (4 / 3 : ℝ) * n ^ 3 * ellN /
          Real.sqrt ellM := by
        rw [hmRpowSq, hnRpowSq, Real.sq_sqrt hellN.le, hquartSq]
      _ = (m ^ (4 / 3 : ℝ) / Real.sqrt ellM) * n ^ 3 * ellN := by
        ring

  change A ≤ 80 * mass at hA
  change B ≤ 80 * mass at hB
  change E ≤ 64 * m ^ (3 / 50 : ℝ) at hE
  change |S| ^ 2 ≤
    A *
      (B * (n * (1 + ellN)) +
        n ^ 2 * (E * (4 * n *
          (1 + Real.log ((2 * n) ^ 2))))) at hS

  have hmass0 : 0 ≤ mass := by
    dsimp [mass]
    positivity
  have hAB : A * B ≤ 6400 * mass ^ 2 := by
    calc
      A * B ≤ (80 * mass) * B :=
        mul_le_mul_of_nonneg_right hA hB0
      _ ≤ (80 * mass) * (80 * mass) :=
        mul_le_mul_of_nonneg_left hB (by positivity)
      _ = 6400 * mass ^ 2 := by ring
  have hAE : A * E ≤
      5120 * mass * m ^ (3 / 50 : ℝ) := by
    calc
      A * E ≤ (80 * mass) * E :=
        mul_le_mul_of_nonneg_right hA hE0
      _ ≤ (80 * mass) * (64 * m ^ (3 / 50 : ℝ)) :=
        mul_le_mul_of_nonneg_left hE (by positivity)
      _ = 5120 * mass * m ^ (3 / 50 : ℝ) := by ring

  have hfirstTerm :
      A * (B * (n * (1 + ellN))) ≤
        160000 * firstScale ^ 2 := by
    calc
      A * (B * (n * (1 + ellN))) =
          (A * B) * (n * (1 + ellN)) := by ring
      _ ≤ (6400 * mass ^ 2) * (n * (1 + ellN)) :=
        mul_le_mul_of_nonneg_right hAB (by positivity)
      _ ≤ (6400 * mass ^ 2) * (n * (4 * ellN ^ 2)) := by
        gcongr
      _ = 25600 * firstScale ^ 2 := by
        rw [hfirstScaleSq]
        ring
      _ ≤ 160000 * firstScale ^ 2 := by
        nlinarith [sq_nonneg firstScale]

  have hsecondTerm :
      A * (n ^ 2 *
        (E * (4 * n * (1 + Real.log ((2 * n) ^ 2))))) ≤
          160000 * secondScale ^ 2 := by
    calc
      A * (n ^ 2 *
          (E * (4 * n * (1 + Real.log ((2 * n) ^ 2))))) =
        (A * E) *
          (4 * n ^ 3 * (1 + Real.log ((2 * n) ^ 2))) := by ring
      _ ≤ (5120 * mass * m ^ (3 / 50 : ℝ)) *
          (4 * n ^ 3 * (1 + Real.log ((2 * n) ^ 2))) :=
        mul_le_mul_of_nonneg_right hAE
          (mul_nonneg (by positivity) hWideLog0)
      _ ≤ (5120 * (m ^ (4 / 3 : ℝ) / Real.sqrt ellM)) *
          (4 * n ^ 3 * (1 + Real.log ((2 * n) ^ 2))) := by
        apply mul_le_mul_of_nonneg_right _
          (mul_nonneg (by positivity) hWideLog0)
        calc
          5120 * mass * m ^ (3 / 50 : ℝ) =
              5120 * (mass * m ^ (3 / 50 : ℝ)) := by ring
          _ ≤ 5120 * (m ^ (4 / 3 : ℝ) / Real.sqrt ellM) :=
            mul_le_mul_of_nonneg_left hmassPower (by norm_num)
      _ ≤ (5120 * (m ^ (4 / 3 : ℝ) / Real.sqrt ellM)) *
          (4 * n ^ 3 * (6 * ellN)) := by
        apply mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hWideLog (by positivity))
        exact mul_nonneg (by norm_num)
          (div_nonneg (Real.rpow_nonneg hmPos.le _) hsqrtEllM.le)
      _ = 122880 * secondScale ^ 2 := by
        rw [hsecondScaleSq]
        ring
      _ ≤ 160000 * secondScale ^ 2 := by
        exact mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg secondScale)

  have hmoment :
      |S| ^ 2 ≤ 160000 * (firstScale + secondScale) ^ 2 := by
    calc
      |S| ^ 2 ≤
          A * (B * (n * (1 + ellN)) +
            n ^ 2 * (E * (4 * n *
              (1 + Real.log ((2 * n) ^ 2))))) := hS
      _ = A * (B * (n * (1 + ellN))) +
          A * (n ^ 2 * (E * (4 * n *
            (1 + Real.log ((2 * n) ^ 2))))) := by ring
      _ ≤ 160000 * firstScale ^ 2 +
          160000 * secondScale ^ 2 :=
        add_le_add hfirstTerm hsecondTerm
      _ ≤ 160000 * (firstScale + secondScale) ^ 2 := by
        have hfirst0 : 0 ≤ firstScale := by
          dsimp [firstScale]
          positivity
        have hsecond0 : 0 ≤ secondScale := by
          dsimp [secondScale]
          positivity
        calc
          160000 * firstScale ^ 2 + 160000 * secondScale ^ 2 =
              160000 * (firstScale ^ 2 + secondScale ^ 2) := by ring
          _ ≤ 160000 *
              (firstScale ^ 2 + secondScale ^ 2 +
                2 * firstScale * secondScale) := by
            apply mul_le_mul_of_nonneg_left
              (le_add_of_nonneg_right
                (mul_nonneg
                  (mul_nonneg (by norm_num) hfirst0) hsecond0))
              (by norm_num)
          _ = 160000 * (firstScale + secondScale) ^ 2 := by ring

  have hscale0 : 0 ≤ 400 * (firstScale + secondScale) := by
    have hfirst0 : 0 ≤ firstScale := by
      dsimp [firstScale]
      positivity
    have hsecond0 : 0 ≤ secondScale := by
      dsimp [secondScale]
      positivity
    positivity
  have habs0 : 0 ≤ |S| := abs_nonneg S
  have habsBound : |S| ≤ 400 * (firstScale + secondScale) := by
    apply (sq_le_sq₀ habs0 hscale0).mp
    calc
      |S| ^ 2 ≤ 160000 * (firstScale + secondScale) ^ 2 := hmoment
      _ = (400 * (firstScale + secondScale)) ^ 2 := by ring
  change |S| ≤ 400 * (firstScale + secondScale)
  exact habsBound

end

end PellPaper
