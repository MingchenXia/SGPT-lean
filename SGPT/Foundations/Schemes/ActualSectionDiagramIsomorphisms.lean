import SGPT.Foundations.Schemes.ActualSheafSectionDiagramMaps
import SGPT.Foundations.Schemes.NonemptySubsetCechComparison
import Mathlib.Algebra.Homology.EulerCharacteristic

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
namespace SGPT.Foundations.Schemes
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

/-- Actual sheaf isomorphisms yield isomorphisms of ORIGINAL base-linear
section diagrams, with the forward map literally the existing induced map. -/
def actualSchemeModuleBaseSubsetIso {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N)
    {I : Type u} [LinearOrder I] (U : I → X.Opens)
    {K : Type u} [CommRing K] (c : K →+* Γ(X, ⊤)) :
    actualSchemeModuleBaseSubsetDiagram M U c ≅ actualSchemeModuleBaseSubsetDiagram N U c := by
  let τ := actualSchemeModuleBaseSubsetMap e.hom U c
  let : ∀ S : Finset I, IsIso (τ.app S) := fun S ↦ by
    apply (ConcreteCategory.isIso_iff_bijective (τ.app S)).mpr
    change Function.Bijective (e.hom.val.app (op (actualSchemeSubsetOpen U S)))
    exact ((SheafOfModules.evaluation (R := X.ringCatSheaf)
      (op (actualSchemeSubsetOpen U S))).mapIso e).toLinearEquiv.bijective
  let : IsIso τ := NatIso.isIso_of_isIso_app τ
  exact asIso τ

/-- Raw homological Euler isomorphism invariance. This alone makes no
homology-finiteness or intrinsic/global sheaf-Euler assertion. -/
theorem cochain_homologyEulerChar_eq_of_iso {K : Type} [Field K]
    {C D : CochainComplex (ModuleCat K) ℕ} (e : C ≅ D) :
    C.homologyEulerChar = D.homologyEulerChar := by
  unfold HomologicalComplex.homologyEulerChar GradedObject.eulerChar
  apply finsum_congr
  intro p
  rw [(HomologicalComplex.homologyMapIso e p).toLinearEquiv.finrank_eq]

end
end SGPT.Foundations.Schemes
