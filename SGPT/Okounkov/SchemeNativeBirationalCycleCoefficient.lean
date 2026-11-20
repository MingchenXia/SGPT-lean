import SGPT.Okounkov.SchemeNativeBirationalResidueDegree
import SGPT.Projective.BDivNativePointDimensionResidue

/-! The prime-cycle coefficient of a birational morphism at an original
point over a smooth codimension-one point, including equality of dimensions. -/
set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov

open CategoryTheory AlgebraicGeometry
open SGPT.Projective.BDivNov16 SGPT.Projective.NumEq.AlgebraicCurveDegree

/-- Finite type over the same field makes the original residue-field
isomorphism identify the point dimensions in the prime-cycle coefficient. -/
theorem nativeBirational_mapCoeff_eq_one_of_smooth_codimOne_of_finiteType
    {V X : Scheme.{0}} [IsIntegral V] [IsIntegral X] (p : V ⟶ X)
    (hη : p (genericPoint V) = genericPoint X) [IsIso (p.stalkMap (genericPoint V))]
    (v : V) (f : X ⟶ Spec (.of ℂ)) (n : ℕ) [SmoothOfRelativeDimension n f]
    [IsSeparated f] [QuasiCompact f] [IsLocallyNoetherian X]
    [LocallyOfFiniteType f] [LocallyOfFiniteType (p ≫ f)]
    (hv : Order.coheight (p v) = 1) :
    AlgebraicCycle.mapCoeff p (pointDimension V) (pointDimension X) v = 1 := by
  let : IsDiscreteValuationRing (X.presheaf.stalk (p v)) :=
    SGPT.NAPotential.AlgPrimes2.isDiscreteValuationRing_stalk f n hv
  have hsurj := (nativeBirational_stalkMap_bijective_of_valuation p hη v).surjective
  have hres := nativeResidueFieldMap_bijective_of_stalkMap_surjective p v hsurj
  exact nativeBirational_mapCoeff_eq_one_of_smooth_codimOne p hη v f n hv
    (nativePointDimension_eq_of_residueFieldMap_bijective p f v hres)

end SGPT.Okounkov
