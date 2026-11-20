import SGPT.Okounkov.SchemeNativeBirationalCycleCoefficient
import SGPT.Okounkov.SchemeComplexPointClosedImage
import SGPT.NAPotential.SmoothDivisorNormalOrder

/-! Pushforward of the original singleton prime cycle and its complex-point carrier. -/
set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov

open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes Set
open SGPT.Projective.NumEq.AlgebraicCurveDegree
open SGPT.NAPotential.SmoothDivisorNormalOrder
open scoped BigOperators Classical

/-- The integer cycle supported at one original scheme point. -/
abbrev schemePointCycle {X : Scheme.{0}} (x : X) (a : ℤ) : AlgebraicCycle X ℤ :=
  Function.locallyFinsuppWithin.single x a

/-- The actual cycle map sends a singleton to the singleton at its image, with the
actual residue-degree/dimension coefficient. This does not require a singleton fibre. -/
theorem schemePointCycle_map_single {V X : Scheme.{0}} (p : V ⟶ X) [QuasiCompact p]
    (v : V) (a : ℤ) :
    AlgebraicCycle.map p (pointDimension V) (pointDimension X)
        (schemePointCycle v a) =
      schemePointCycle (p v)
        (a * (AlgebraicCycle.mapCoeff p (pointDimension V) (pointDimension X) v : ℤ)) := by
  classical
  apply Function.locallyFinsuppWithin.ext
  intro x
  change (∑ᶠ z ∈ p ⁻¹' ({x} : Set X),
      schemePointCycle v a z *
        (AlgebraicCycle.mapCoeff p (pointDimension V) (pointDimension X) z : ℤ)) = _
  rw [finsum_mem_def, finsum_eq_single _ v]
  · by_cases hx : p v = x
    · simp [schemePointCycle, Set.indicator, hx]
    · simp [schemePointCycle, Set.indicator, hx, Ne.symm hx]
  · intro z hz
    simp [schemePointCycle, Set.indicator, hz]

/-- Dimension drop kills the original prime cycle under the actual algebraic pushforward. -/
theorem schemePointCycle_map_single_eq_zero_of_dimension_drop {V X : Scheme.{0}}
    (p : V ⟶ X) [QuasiCompact p] (v : V)
    (hdrop : pointDimension X (p v) < pointDimension V v) :
    AlgebraicCycle.map p (pointDimension V) (pointDimension X)
      (schemePointCycle v (1 : ℤ)) = 0 := by
  classical
  rw [schemePointCycle_map_single, AlgebraicCycle.mapCoeff, if_neg hdrop.ne.symm]
  simp [schemePointCycle]
  rfl

/-- A proper birational transition between smooth integral schemes pushes a prime whose
image has codimension one to the original target prime with coefficient one. The
complex-point image of its carrier is the carrier of that same target prime. -/
theorem nativeBirational_primeCycle_map_and_complexCarrier_of_codimOne_image
    {V X : Scheme.{0}} [IsIntegral V] [IsIntegral X] (p : V ⟶ X) [IsProper p]
    (hη : p (genericPoint V) = genericPoint X) [IsIso (p.stalkMap (genericPoint V))]
    (v : V) (f : X ⟶ Spec (.of ℂ)) (m : ℕ)
    [SmoothOfRelativeDimension (m + 1) f] [SmoothOfRelativeDimension (m + 1) (p ≫ f)]
    [IsSeparated f] [QuasiCompact f] [IsSeparated (p ≫ f)] [QuasiCompact (p ≫ f)]
    (hV : Order.coheight v = 1) (hX : Order.coheight (p v) = 1) :
    let P := identityPrimeDivisor (p ≫ f) m v hV
    let Q := identityPrimeDivisor f m (p v) hX
    AlgebraicCycle.map p (pointDimension V) (pointDimension X)
        (schemePointCycle P.point (1 : ℤ)) =
      schemePointCycle Q.point (1 : ℤ) ∧
    schemeComplexPointMap (p ≫ f) f p rfl ''
        schemeNativeAlgebraicTrace (p ≫ f) (closure ({P.point} : Set V)) =
      schemeNativeAlgebraicTrace f (closure ({Q.point} : Set X)) := by
  classical
  let : Smooth f := SmoothOfRelativeDimension.smooth (m + 1) f
  let : Smooth (p ≫ f) := SmoothOfRelativeDimension.smooth (m + 1) (p ≫ f)
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  dsimp only
  constructor
  · change AlgebraicCycle.map p (pointDimension V) (pointDimension X)
      (schemePointCycle v (1 : ℤ)) =
        schemePointCycle (p v) (1 : ℤ)
    simp only [schemePointCycle_map_single,
      nativeBirational_mapCoeff_eq_one_of_smooth_codimOne_of_finiteType p hη v f (m + 1) hX,
      Nat.cast_one, mul_one]
  · exact schemeComplexPointMap_image_pointClosure f p v

end SGPT.Okounkov
