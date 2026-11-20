import SGPT.Projective.OriginalNormalizationFiniteMap
import SGPT.Foundations.Schemes.NativeProjectivePushforward
import SGPT.Foundations.Schemes.NativeProjectiveLineCechEuler

/-! TRUE finite line Cech homology of the SAME original normalizer on
inverse images of the UNCHANGED original projective coordinate cover.
No new normalized closed-projective embedding is assumed or manufactured
as a desired-output input. Blueprint: original-finite-projective-line-cech.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes TopCat TopologicalSpace Opposite
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Actual FINITE original maps give finite original inverse-affine line
sections over the genuine original ambient coefficient ring. -/
theorem originalFiniteMap_pushforwardLineSections_finite {Y Z : Scheme.{0}}
    (i : Z ⟶ Y) [IsFinite i] {L : Z.Modules} (a : LineBundleAtlas L)
    {U : Y.Opens} (hU : IsAffineOpen U) :
    Module.Finite Γ(Y,U) Γ((Scheme.Modules.pushforward i).obj L,U) := by
  let := (i.app U).hom.toAlgebra
  let : Module.Finite Γ(Y,U) Γ(Z,i ⁻¹ᵁ U) := i.finite_app U hU
  let : Module Γ(Z,i ⁻¹ᵁ U) Γ((Scheme.Modules.pushforward i).obj L,U) :=
    inferInstanceAs (Module Γ(Z,i ⁻¹ᵁ U) Γ(L,i ⁻¹ᵁ U))
  let : Module.Finite Γ(Z,i ⁻¹ᵁ U) Γ((Scheme.Modules.pushforward i).obj L,U) :=
    a.affineOpenSections_finite (hU.preimage i)
  let : IsScalarTower Γ(Y,U) Γ(Z,i ⁻¹ᵁ U) Γ((Scheme.Modules.pushforward i).obj L,U) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact Module.Finite.trans Γ(Z,i ⁻¹ᵁ U) Γ((Scheme.Modules.pushforward i).obj L,U)

/-- Genuine affine original maps preserve actual line quasicoherence
on EVERY original affine target chart, by the true affine tilde theorem. -/
theorem originalAffineMap_affineRestrictedPushforward_isQuasicoherent
    {Y Z : Scheme.{0}} (i : Z ⟶ Y) [IsAffineHom i]
    {L : Z.Modules} (a : LineBundleAtlas L) {U : Y.Opens} (hU : IsAffineOpen U) :
    (((Scheme.Modules.pushforward i).obj L).restrict U.ι).IsQuasicoherent := by
  let : IsAffine U.toScheme := hU
  let : IsAffine (i ⁻¹ᵁ U).toScheme := hU.preimage i
  let := a.isQuasicoherent
  let N := (Scheme.Modules.pushforward (i ∣_ U)).obj (L.restrict (i ⁻¹ᵁ U).ι)
  let : N.IsQuasicoherent :=
    affineSchemePushforward_isQuasicoherent (i ∣_ U) (L.restrict (i ⁻¹ᵁ U).ι)
  exact (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).prop_of_iso
    (pushforwardRestrictIso i U L).symm (inferInstance : N.IsQuasicoherent)

/-- Actual FINITE original projective maps give finite original coordinate
chart modules, without requiring the source map to be a closed immersion. -/
theorem originalFinitePolynomialProjPushforwardChartSections_finite
    {k : Type} [Field k] {Y : Scheme} {N : ℕ} (i : Y ⟶ polynomialProj k N)
    [IsFinite i] {L : Y.Modules} (a : LineBundleAtlas L) (j : Fin (N+1)) :
    Module.Finite (polynomialProjCoordinateRing k N j)
      Γ(polynomialProjModuleChart ((Scheme.Modules.pushforward i).obj L) j,⊤) := by
  let M := (Scheme.Modules.pushforward i).obj L
  let c := polynomialProjCoordinateImmersion k N j
  let : Module.Finite Γ(polynomialProj k N,c ''ᵁ ⊤) Γ(M,c ''ᵁ ⊤) := by
    rw [polynomialProjCoordinateImmersion_image_top]
    exact originalFiniteMap_pushforwardLineSections_finite i a
      (polynomialProjCoordinateOpen_isAffine k N j)
  exact affineOpenImmersionTopSections_finite c M

/-- ALL true coordinate-chart pushforwards of an actual FINITE original
projective map are genuinely quasicoherent, with no chart output premise. -/
theorem originalFinitePolynomialProjPushforwardChart_isQuasicoherent
    {k : Type} [Field k] {Y : Scheme} {N : ℕ} (i : Y ⟶ polynomialProj k N)
    [IsFinite i] {L : Y.Modules} (a : LineBundleAtlas L) (j : Fin (N+1)) :
    (polynomialProjModuleChart ((Scheme.Modules.pushforward i).obj L) j).IsQuasicoherent := by
  let M := (Scheme.Modules.pushforward i).obj L
  let c := polynomialProjCoordinateImmersion k N j
  have hU : IsAffineOpen c.opensRange := by
    rw [← c.image_top_eq_opensRange]
    change IsAffineOpen (polynomialProjCoordinateImmersion k N j ''ᵁ ⊤)
    rw [polynomialProjCoordinateImmersion_image_top]
    exact polynomialProjCoordinateOpen_isAffine k N j
  let : (M.restrict c.opensRange.ι).IsQuasicoherent :=
    originalAffineMap_affineRestrictedPushforward_isQuasicoherent i a hU
  let α : M.restrict c ≅ (M.restrict c.opensRange.ι).restrict c.isoOpensRange.hom :=
    ((Scheme.Modules.restrictFunctorCongr c.isoOpensRange_hom_ι).app M).symm ≪≫
      (Scheme.Modules.restrictFunctorComp c.isoOpensRange.hom c.opensRange.ι).app M
  exact (SheafOfModules.isQuasicoherent (Spec (.of (polynomialProjCoordinateRing k N j))).ringCatSheaf).prop_of_iso
    α.symm (inferInstance : ((M.restrict c.opensRange.ι).restrict c.isoOpensRange.hom).IsQuasicoherent)

/-- TRUE finite Cech homology of ANY original line for an actual FINITE
map to original projective space, retaining actual inverse-coordinate opens
and SAME original structural constants. No homology-finiteness premise. -/
theorem originalFinitePolynomialProjLineCech_homology_finite
    (k : Type) [Field k] (N : ℕ) {Y : Scheme} (i : Y ⟶ polynomialProj k N)
    [IsFinite i] {L : Y.Modules} (a : LineBundleAtlas L) (p : Y ⟶ Spec (.of k))
    (hp : actualPolynomialProjectivePullbackStructureMap i = p) (j : ℕ) :
    Module.Finite k ((subsetCechComplex (actualSchemeModuleBaseSubsetDiagram L
      (actualPolynomialProjectivePullbackCoordinateOpens i) (schemeGlobalConstants p))).homology j) := by
  subst p
  let M := (Scheme.Modules.pushforward i).obj L
  let : ∀ q, Module.Finite (polynomialProjCoordinateRing k N q)
      Γ(polynomialProjModuleChart M q,⊤) := fun q =>
    originalFinitePolynomialProjPushforwardChartSections_finite i a q
  let : ∀ q, (polynomialProjModuleChart M q).IsQuasicoherent := fun q =>
    originalFinitePolynomialProjPushforwardChart_isQuasicoherent i a q
  let c := schemeConstantMap (polynomialProjStructureMap k N)
  let U := polynomialProjCoordinateOpen k N
  let : Module.Finite k ((subsetCechComplex (actualSchemeModuleBaseSubsetDiagram M U c)).homology j) :=
    polynomialProjActualCech_homology_finite k N M j
  have hsrc : Module.Finite k ((subsetCechComplex (actualSchemeModuleBaseSubsetDiagram L
      (fun q => i ⁻¹ᵁ U q) (actualSchemePushforwardSourceConstants i c))).homology j) :=
    Module.Finite.equiv (actualSchemeModulePushforwardHomologyIso i L c U j).toLinearEquiv
  have hc := actualPolynomialProjectivePushforwardSourceConstants_eq i
  rw [polynomialProj_identityPullback_constants k N] at hc
  change Module.Finite k ((subsetCechComplex (actualSchemeModuleBaseSubsetDiagram L
    (fun q => i ⁻¹ᵁ U q) (schemeGlobalConstants (actualPolynomialProjectivePullbackStructureMap i)))).homology j)
  rw [← hc]
  exact hsrc

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))
    (E : ClosedProjectiveEmbedding f)

/-- The SAME actual normalizer, actual line, inverse of the UNCHANGED
original projective cover, and literal normalized structural complex action. -/
def originalNormalizedLineCechComplex (L : (originalNormalizationScheme X).Modules) :
    CochainComplex (ModuleCat ℂ) ℕ :=
  subsetCechComplex (actualSchemeModuleBaseSubsetDiagram L
    (fun j => originalNormalizationMap X ⁻¹ᵁ actualPolynomialProjectivePullbackCoordinateOpens E.map j)
    (schemeGlobalConstants (originalNormalizationMap X ≫ f)))

/-- Actual ORIGINAL normalization geometry PRODUCES all same-cover line
homology finiteness, WITHOUT any normalized closed-projective embedding.
The original map/cover/scalars and ALL branches are retained. -/
theorem originalNormalizedLineCech_homology_finite
    {L : (originalNormalizationScheme X).Modules} (a : LineBundleAtlas L) (j : ℕ) :
    Module.Finite ℂ ((originalNormalizedLineCechComplex f E L).homology j) := by
  let := originalNormalizationMap_finite X f E
  let i := originalNormalizationMap X ≫ E.map
  let p := originalNormalizationMap X ≫ f
  have hp : actualPolynomialProjectivePullbackStructureMap i = p := by
    change (originalNormalizationMap X ≫ E.map) ≫ polynomialProjStructureMap ℂ E.ambientDimension = _
    rw [Category.assoc,E.over_base]
  have h := originalFinitePolynomialProjLineCech_homology_finite ℂ E.ambientDimension i a p hp j
  have hU : actualPolynomialProjectivePullbackCoordinateOpens i =
      fun q => originalNormalizationMap X ⁻¹ᵁ actualPolynomialProjectivePullbackCoordinateOpens E.map q := by
    funext q
    rfl
  change Module.Finite ℂ ((subsetCechComplex (actualSchemeModuleBaseSubsetDiagram L
    (fun q => originalNormalizationMap X ⁻¹ᵁ actualPolynomialProjectivePullbackCoordinateOpens E.map q)
    (schemeGlobalConstants p))).homology j)
  rw [← hU]
  exact h

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
