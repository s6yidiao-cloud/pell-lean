import Pell.ShiftedSquareAuxiliaryParameterBounds
import Pell.Main3ShiftedSquareRawCoordinateBounds
import Pell.ShiftedSquareCoordinateEncoding
import Mathlib.Tactic

/-!
# A coarse finite container for shifted-square coordinate codes

The auxiliary parameters `C₀`, `r`, and `ell` lie in explicit natural
intervals depending only on `|a|`.  The two primitive coordinate vectors lie
in the explicit symmetric integer rectangles supplied by the raw-coordinate
bounds.  Their fivefold product is therefore a literal finite container for
the complete `ShiftedSquareCoordinateCode`.

The exact cardinality retains every floor and endpoint.  A second bound
replaces the rectangle cardinalities by a transparent polynomial expression.
This is only a coarse ambient-code bound; it is not the manuscript's local
`O(M)` cell-pair estimate.
-/

namespace PellPaper

noncomputable section

/-- The left-associated product carrying the five fields of a complete
shifted-square coordinate code. -/
abbrev ShiftedSquareCoordinateContainerTuple :=
  ((((ℕ × ℕ) × ℕ) × (Fin 2 → ℤ)) × (Fin 2 → ℤ))

/-- The tautological equivalence between the fivefold product and the public
coordinate-code structure. -/
def shiftedSquareCoordinateCodeEquiv :
    ShiftedSquareCoordinateContainerTuple ≃ ShiftedSquareCoordinateCode where
  toFun p :=
    ⟨p.1.1.1.1, p.1.1.1.2, p.1.1.2, p.1.2, p.2⟩
  invFun C := ((((C.C₀, C.r), C.ell), C.x), C.y)
  left_inv := by
    rintro ⟨⟨⟨⟨C₀, r⟩, ell⟩, x⟩, y⟩
    rfl
  right_inv := by
    rintro ⟨C₀, r, ell, x, y⟩
    rfl

/-- The literal complete coordinate code attached to one simultaneous
normalized package. -/
def shiftedSquareCoordinateCodeOfPackage
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq) :
    ShiftedSquareCoordinateCode :=
  ⟨P.minkowski.C₀, P.r, P.ell, P.x, P.y⟩

/-- A fivefold finite product containing all codes whose auxiliary scalars
obey the reviewed `|a|` bounds and whose two coordinate vectors obey the
specified symmetric-rectangle bounds. -/
def shiftedSquareCoordinateContainer (a : ℤ)
    (sourceRadius targetRadius : ℝ) : Finset ShiftedSquareCoordinateCode :=
  (((((Finset.range (32 * a.natAbs + 1)).product
          (Finset.range (64 * a.natAbs + 1))).product
        (Finset.range (32 * a.natAbs + 1))).product
      (integerSymmetricRectangle sourceRadius sourceRadius)).product
    (integerSymmetricRectangle targetRadius targetRadius)).map
      shiftedSquareCoordinateCodeEquiv.toEmbedding

/-- Membership is exactly the three closed natural bounds and the two
literal rectangle-membership conditions. -/
theorem mem_shiftedSquareCoordinateContainer
    (a : ℤ) (sourceRadius targetRadius : ℝ)
    (C : ShiftedSquareCoordinateCode) :
    C ∈ shiftedSquareCoordinateContainer a sourceRadius targetRadius ↔
      C.C₀ ≤ 32 * a.natAbs ∧
        C.r ≤ 64 * a.natAbs ∧
      C.ell ≤ 32 * a.natAbs ∧
        C.x ∈ integerSymmetricRectangle sourceRadius sourceRadius ∧
        C.y ∈ integerSymmetricRectangle targetRadius targetRadius := by
  rw [shiftedSquareCoordinateContainer, Finset.mem_map_equiv]
  simp [shiftedSquareCoordinateCodeEquiv]
  tauto

/-- Exact cardinality of the finite code container, retaining floors and the
added endpoint in every factor. -/
theorem card_shiftedSquareCoordinateContainer_exact
    (a : ℤ) (sourceRadius targetRadius : ℝ) :
    (shiftedSquareCoordinateContainer a sourceRadius targetRadius).card =
      (32 * a.natAbs + 1) * (64 * a.natAbs + 1) *
        (32 * a.natAbs + 1) *
        (2 * ⌊sourceRadius⌋ + 1).toNat ^ 2 *
        (2 * ⌊targetRadius⌋ + 1).toNat ^ 2 := by
  simp [shiftedSquareCoordinateContainer, card_integerSymmetricRectangle]
  ring

/-- Package-dependent specialization of the explicit container at the
reviewed source and target raw-coordinate radii. -/
def shiftedSquareCoordinateContainerForPackage
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq) :
    Finset ShiftedSquareCoordinateCode :=
  shiftedSquareCoordinateContainer a
    (shiftedSquareRawCoordinateScaleLoss a *
      Real.sqrt (shiftedSquareEAlpha P))
    (shiftedSquareRawCoordinateScaleLoss a *
      Real.sqrt (shiftedSquareEGamma P))

/-- The complete code of a simultaneous package belongs to its explicit
finite container. -/
theorem shiftedSquareCoordinateCodeOfPackage_mem_containerForPackage
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (ha : Squarefree a) (hd : 0 < d)
    (hn : 2 * Real.sqrt |(a : ℝ)| ≤ (n : ℝ))
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq) :
    shiftedSquareCoordinateCodeOfPackage P ∈
      shiftedSquareCoordinateContainerForPackage P := by
  have ha0 : a ≠ 0 := by
    intro ha0
    have hnoRoot :=
      Fact.out (p := rationalQuadraticAlgebraNoRationalRoot (-a)) 0
    apply hnoRoot
    simp [ha0]
  have haux := shiftedSquare_auxiliaryParameterBounds ha0 P
  have hxy := shiftedSquare_primitiveRawCoordinates_mem_scaleRectangles
    ha hd hn P
  rw [shiftedSquareCoordinateContainerForPackage,
    mem_shiftedSquareCoordinateContainer]
  exact ⟨haux.1, haux.2.1, haux.2.2.1, hxy.1, hxy.2⟩

/-- Primitivity plus the source raw-coordinate bounds shows that the source
rectangle radius is at least one. -/
theorem shiftedSquare_sourceRawCoordinateRadius_one_le
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (ha : Squarefree a) (hd : 0 < d)
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq) :
    (1 : ℝ) ≤ shiftedSquareRawCoordinateScaleLoss a *
      Real.sqrt (shiftedSquareEAlpha P) := by
  have hx := shiftedSquare_sourceRawCoordinates_scaleBounds ha hd P
  rcases P.x_primitive.ne_zero_or_ne_zero with hx0 | hx1
  · have hone : (1 : ℝ) ≤ |(P.x 0 : ℝ)| := by
      exact_mod_cast Int.one_le_abs hx0
    exact hone.trans hx.1
  · have hone : (1 : ℝ) ≤ |(P.x 1 : ℝ)| := by
      exact_mod_cast Int.one_le_abs hx1
    exact hone.trans hx.2.1

/-- The same primitivity argument makes the target rectangle radius at least
one on the large shifted-square range. -/
theorem shiftedSquare_targetRawCoordinateRadius_one_le
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (ha : Squarefree a) (hd : 0 < d)
    (hn : 2 * Real.sqrt |(a : ℝ)| ≤ (n : ℝ))
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq) :
    (1 : ℝ) ≤ shiftedSquareRawCoordinateScaleLoss a *
      Real.sqrt (shiftedSquareEGamma P) := by
  have hy := shiftedSquare_targetRawCoordinates_scaleBounds ha hd hn P
  rcases P.y_primitive.ne_zero_or_ne_zero with hy0 | hy1
  · have hone : (1 : ℝ) ≤ |(P.y 0 : ℝ)| := by
      exact_mod_cast Int.one_le_abs hy0
    exact hone.trans hy.1
  · have hone : (1 : ℝ) ≤ |(P.y 1 : ℝ)| := by
      exact_mod_cast Int.one_le_abs hy1
    exact hone.trans hy.2.1

/-- Before simplifying the auxiliary factor, the rectangle estimates give a
transparent product upper bound for the finite container. -/
theorem card_shiftedSquareCoordinateContainer_le_auxiliary_mul_radii
    (a : ℤ) {sourceRadius targetRadius : ℝ}
    (hsource : 1 ≤ sourceRadius) (htarget : 1 ≤ targetRadius) :
    ((shiftedSquareCoordinateContainer
        a sourceRadius targetRadius).card : ℝ) ≤
      (((32 * a.natAbs + 1) * (64 * a.natAbs + 1) *
          (32 * a.natAbs + 1) : ℕ) : ℝ) *
        (9 * sourceRadius * sourceRadius) *
        (9 * targetRadius * targetRadius) := by
  have hcard :
      (shiftedSquareCoordinateContainer a sourceRadius targetRadius).card =
        (32 * a.natAbs + 1) * (64 * a.natAbs + 1) *
          (32 * a.natAbs + 1) *
          (integerSymmetricRectangle sourceRadius sourceRadius).card *
          (integerSymmetricRectangle targetRadius targetRadius).card := by
    simp [shiftedSquareCoordinateContainer]
  rw [hcard]
  push_cast
  have hs := card_integerSymmetricRectangle_le_nine_mul
    hsource hsource
  have ht := card_integerSymmetricRectangle_le_nine_mul
    htarget htarget
  gcongr

/-- The product of the three auxiliary natural ranges is at most a cubic
polynomial in `natAbs a`. -/
theorem shiftedSquare_auxiliaryCoordinateRangeProduct_le
    {a : ℤ} (ha : a ≠ 0) :
    (32 * a.natAbs + 1) * (64 * a.natAbs + 1) *
        (32 * a.natAbs + 1) ≤
      70785 * a.natAbs ^ 3 := by
  have hA : 1 ≤ a.natAbs :=
    (Nat.one_le_iff_ne_zero).2 (Int.natAbs_ne_zero.mpr ha)
  have h32 : 32 * a.natAbs + 1 ≤ 33 * a.natAbs := by omega
  have h64 : 64 * a.natAbs + 1 ≤ 65 * a.natAbs := by omega
  calc
    (32 * a.natAbs + 1) * (64 * a.natAbs + 1) *
        (32 * a.natAbs + 1) ≤
      (33 * a.natAbs) * (65 * a.natAbs) * (33 * a.natAbs) := by
        gcongr
    _ = 70785 * a.natAbs ^ 3 := by ring

/-- Coarse polynomial cardinality bound for a nonzero shift and radii at
least one.  The numerical coefficient is
`33 * 65 * 33 * 9 * 9 = 5733585`. -/
theorem card_shiftedSquareCoordinateContainer_le_polynomial
    {a : ℤ} (ha : a ≠ 0) {sourceRadius targetRadius : ℝ}
    (hsource : 1 ≤ sourceRadius) (htarget : 1 ≤ targetRadius) :
    ((shiftedSquareCoordinateContainer
        a sourceRadius targetRadius).card : ℝ) ≤
      5733585 * (a.natAbs : ℝ) ^ 3 * sourceRadius ^ 2 *
        targetRadius ^ 2 := by
  have hbase :=
    card_shiftedSquareCoordinateContainer_le_auxiliary_mul_radii
      a hsource htarget
  have hauxNat := shiftedSquare_auxiliaryCoordinateRangeProduct_le ha
  have hauxReal :
      (((32 * a.natAbs + 1) * (64 * a.natAbs + 1) *
          (32 * a.natAbs + 1) : ℕ) : ℝ) ≤
        70785 * (a.natAbs : ℝ) ^ 3 := by
    exact_mod_cast hauxNat
  calc
    ((shiftedSquareCoordinateContainer
        a sourceRadius targetRadius).card : ℝ) ≤
        (((32 * a.natAbs + 1) * (64 * a.natAbs + 1) *
            (32 * a.natAbs + 1) : ℕ) : ℝ) *
          (9 * sourceRadius * sourceRadius) *
          (9 * targetRadius * targetRadius) := hbase
    _ ≤ (70785 * (a.natAbs : ℝ) ^ 3) *
          (9 * sourceRadius * sourceRadius) *
          (9 * targetRadius * targetRadius) := by
      gcongr
    _ = 5733585 * (a.natAbs : ℝ) ^ 3 * sourceRadius ^ 2 *
          targetRadius ^ 2 := by ring

/-- The specialized package container satisfies the preceding explicit
polynomial bound with its literal raw-coordinate radii. -/
theorem card_shiftedSquareCoordinateContainerForPackage_le_polynomial
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (ha : Squarefree a) (hd : 0 < d)
    (hn : 2 * Real.sqrt |(a : ℝ)| ≤ (n : ℝ))
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq) :
    ((shiftedSquareCoordinateContainerForPackage P).card : ℝ) ≤
      5733585 * (a.natAbs : ℝ) ^ 3 *
        (shiftedSquareRawCoordinateScaleLoss a *
          Real.sqrt (shiftedSquareEAlpha P)) ^ 2 *
        (shiftedSquareRawCoordinateScaleLoss a *
          Real.sqrt (shiftedSquareEGamma P)) ^ 2 := by
  have ha0 : a ≠ 0 := by
    intro ha0
    have hnoRoot :=
      Fact.out (p := rationalQuadraticAlgebraNoRationalRoot (-a)) 0
    apply hnoRoot
    simp [ha0]
  exact card_shiftedSquareCoordinateContainer_le_polynomial ha0
    (shiftedSquare_sourceRawCoordinateRadius_one_le ha hd P)
    (shiftedSquare_targetRawCoordinateRadius_one_le ha hd hn P)

/-- A finite family of fixed-basis encoded solutions is bounded by any one
coordinate container containing all of its codes. -/
theorem card_shiftedSquareEncodedFixedBasisSolution_le_coordinateContainer
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {basis : Module.Basis (Fin 2) ℤ
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a)))}
    {t c : ℤ}
    (S : Finset (ShiftedSquareEncodedFixedBasisSolution a basis t c))
    (sourceRadius targetRadius : ℝ)
    (hmem : ∀ Q ∈ S, Q.code ∈
      shiftedSquareCoordinateContainer a sourceRadius targetRadius) :
    S.card ≤
      (shiftedSquareCoordinateContainer a sourceRadius targetRadius).card := by
  apply card_shiftedSquareEncodedFixedBasisSolution_le_of_codes_subset
    S (shiftedSquareCoordinateContainer a sourceRadius targetRadius)
  intro C hC
  simp only [Finset.mem_image] at hC
  obtain ⟨Q, hQS, rfl⟩ := hC
  exact hmem Q hQS

end

end PellPaper
