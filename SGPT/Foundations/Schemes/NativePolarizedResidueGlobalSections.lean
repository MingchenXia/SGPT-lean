import SGPT.Foundations.Schemes.NativePolarizedResidueComparison
import SGPT.Foundations.Schemes.SchemeModulePushforwardCech
import SGPT.Foundations.Schemes.NativeProjectiveGlobalSectionsFiniteness
/-!
# NativePolarizedResidueGlobalSections

Genuine sheaf isomorphisms induce literal global-section maps preserving actual structural scalars. The actual residue pushforward comparison identifies original source power sections with true projective tensor-twist sections over that structural field.
-/

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
namespace SGPT.Foundations.Schemes
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

/-- An actual sheaf isomorphism gives its literal global-section isomorphism with the genuine chosen structural scalars. -/
def nativeModuleIsoBaseGlobalSections {Y : Scheme.{u}} {P Q : Y.Modules}
    (E : P ≅ Q) {K : Type u} [CommRing K] (c : K →+* Γ(Y, ⊤)) :
    actualSchemeModuleBaseGlobalSections P c ≅ actualSchemeModuleBaseGlobalSections Q c := by
  let G : ModuleCat.of Γ(Y, ⊤) (bundleSections P ⊤) ≅
      ModuleCat.of Γ(Y, ⊤) (bundleSections Q ⊤) := {
    hom := E.hom.val.app (.op ⊤)
    inv := E.inv.val.app (.op ⊤)
    hom_inv_id := congrArg (fun a ↦ a.val.app (.op ⊤)) E.hom_inv_id
    inv_hom_id := congrArg (fun a ↦ a.val.app (.op ⊤)) E.inv_hom_id }
  exact (ModuleCat.restrictScalars c).mapIso G

/-- Literal actual sheaf-map readback of the scalar-preserving global-section comparison. -/
theorem nativeModuleIsoBaseGlobalSections_hom_apply {Y : Scheme.{u}} {P Q : Y.Modules}
    (E : P ≅ Q) {K : Type u} [CommRing K] (c : K →+* Γ(Y, ⊤)) (s : bundleSections P ⊤) :
    (nativeModuleIsoBaseGlobalSections E c).hom s = E.hom.val.app (.op ⊤) s := rfl

section Polarized
variable {X : Scheme} (L : IntrinsicLineBundle X)
    {K : Type} [Field K] (n : ℕ) (f : X ⟶ polynomialProj K n) (q : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra
variable (e : bundleTensorPower L.sheaf q ≅
    (Scheme.Modules.pullback f).obj (polynomialProjTwistingLine K n).sheaf)

/-- The genuine polarized residue sheaf comparison identifies the literal source power sections with true projective tensor-twist sections, preserving actual structural K actions. -/
def nativePolarizedResidueGlobalSectionsIso (m r : ℕ) :
    actualSchemeModuleBaseGlobalSections (bundleTensorPower L.sheaf (q * m + r))
      (schemeGlobalConstants (actualPolynomialProjectivePullbackStructureMap f)) ≅
    actualSchemeModuleBaseGlobalSections
      (polynomialProjModuleTensorTwist K n
        ((Scheme.Modules.pushforward f).obj (bundleTensorPower L.sheaf r)) m)
      (schemeConstantMap (polynomialProjStructureMap K n)) :=
  (actualPolynomialProjectivePushforwardGlobalSectionsIso f
    (bundleTensorPower L.sheaf (q * m + r))).symm ≪≫
  eqToIso (congrArg (actualSchemeModuleBaseGlobalSections
      ((Scheme.Modules.pushforward f).obj (bundleTensorPower L.sheaf (q * m + r))))
    (polynomialProj_identityPullback_constants K n)) ≪≫
  nativeModuleIsoBaseGlobalSections
    (nativePolarizedResiduePushforwardTensorTwistIso L n f q e m r)
    (schemeConstantMap (polynomialProjStructureMap K n))

/-- The genuine scalar-preserving residue comparison is a linear equivalence of the actual source power sections and true twisted projective global sections. -/
def nativePolarizedResidueGlobalSectionsEquiv (m r : ℕ) :
    letI := schemeGlobalSectionModule (actualPolynomialProjectivePullbackStructureMap f)
      (bundleTensorPower L.sheaf (q * m + r))
    bundlePowerGlobalSections L.sheaf (q * m + r) ≃ₗ[K]
      actualSchemeModuleBaseGlobalSections
        (polynomialProjModuleTensorTwist K n
          ((Scheme.Modules.pushforward f).obj (bundleTensorPower L.sheaf r)) m)
        (schemeConstantMap (polynomialProjStructureMap K n)) :=
  (nativePolarizedResidueGlobalSectionsIso L n f q e m r).toLinearEquiv

end Polarized
end
end SGPT.Foundations.Schemes
