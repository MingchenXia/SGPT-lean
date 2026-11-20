import SGPT.NAPotential.BJDivisorialSpecComplex
import SGPT.Checks.LiteratureBridge.BJPointBridge
import SGPT.Foundations.PublishedEnvelope.AlgGeom.ProjectiveFactorizationRingIso
import SGPT.Foundations.PublishedEnvelope.AlgGeom.SchemeStalkCenteredDVR

/-! Actual original prime-divisor stalks, field maps and residue valuations.
These are geometric input producers for the divisorial dictionary; no
native divisoriality, comparison or desired model is assumed or claimed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.NAPotential.BJ.Divisorial
open AlgebraicGeometry CategoryTheory
open SGPT.NAPotential.Berkovich
open SGPT.Foundations.PublishedEnvelope SGPT.Foundations.PublishedEnvelope.Berkovich
open scoped Classical NNReal
variable {X : Scheme.{0}}

/-- The actual original function-field pullback is bijective, derived from
the original birational morphism and the canonical generic residue map. -/
theorem primeDivisor_pullback_bijective (E : PrimeDivisorOver X) :
    Function.Bijective E.pullback :=
  E.residueEquiv.symm.bijective.comp E.birational

/-- The original field identification is produced, not passed to a comparison. -/
def primeDivisor_pullbackEquiv (E : PrimeDivisorOver X) :
    X.residueField (E.π (genericPoint E.Y)) ≃+* E.Y.functionField :=
  RingEquiv.ofBijective E.pullback (primeDivisor_pullback_bijective E)

theorem primeDivisor_pullbackEquiv_apply (E : PrimeDivisorOver X)
    (g : X.residueField (E.π (genericPoint E.Y))) :
    primeDivisor_pullbackEquiv E g = E.pullback g := rfl

variable (p : X ⟶ Spec (.of ℂ)) [IsProjective p]
local instance : IsProper p := (ProjectiveFactorizationRingIso.of_isProjective p).isProper

/-- An actual original prime-divisor stalk is essentially of finite type
over C, using its SAME composed original structure morphism. -/
theorem primeDivisor_stalk_essFiniteType (E : PrimeDivisorOver X) :
    let := (E.π ≫ p).stalkAlgebra E.point
    Algebra.EssFiniteType ℂ (E.Y.presheaf.stalk E.point) := by
  let := (E.π ≫ p).stalkAlgebra E.point
  exact SchemeStalkCenteredDVR.essFiniteType_stalkAlgebra (E.π ≫ p) E.point

/-- Both true geometric DVR properties are manufactured from the actual
normal proper birational model and its actual codimension-one point. -/
theorem primeDivisor_stalk_geometricDVR (E : PrimeDivisorOver X) :
    let := (E.π ≫ p).stalkAlgebra E.point
    IsDiscreteValuationRing (E.Y.presheaf.stalk E.point) ∧
      Algebra.EssFiniteType ℂ (E.Y.presheaf.stalk E.point) := by
  let := (E.π ≫ p).stalkAlgebra E.point
  exact ⟨inferInstance, primeDivisor_stalk_essFiniteType p E⟩

omit [IsProjective p] in
/-- Every nonzero original rational function retains its true exponential
divisorial value in the actual native residue-field point. -/
theorem pointEquiv_ordVal_value (E : PrimeDivisorOver X) (t : ℚ)
    (ht : (0 : ℝ) < t) {g : X.residueField (E.π (genericPoint E.Y))} (hg : g ≠ 0) :
    (((pointEquiv p (E.ordVal p t ht)).1.residueVal g) : ℝ) =
      Real.exp (-((t : ℝ) * (E.ord g : ℝ))) := by
  rw [pointEquiv_residueVal, E.ordVal_valAt t ht hg, BerkovichPoint.expNeg_coe]

end SGPT.NAPotential.BJ.Divisorial
