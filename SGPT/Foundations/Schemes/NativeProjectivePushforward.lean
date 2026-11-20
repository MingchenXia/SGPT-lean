import SGPT.Foundations.Schemes.NativeClosedPushforwardSections
import SGPT.Foundations.Schemes.ModulePushforwardAffine

/-! # Actual closed-projective affine chart pushforward modules

True closed-immersion affine section finiteness is transported through native
chart section and coordinate-ring isomorphisms. No section-finiteness premise
is added to the projective geometry.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopCat TopologicalSpace

namespace SGPT.Foundations.Schemes

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Native open-chart scalar transport from its true whole image ring. -/
def affineOpenImmersionTopScalars {X : Scheme.{u}} {R : CommRingCat.{u}}
    (f : Spec R ⟶ X) [IsOpenImmersion f] : Γ(X, f ''ᵁ ⊤) ≃+* R :=
  ((f.appIso ⊤) ≪≫ Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv

/-- Actual chart sections use the native inverse scalar transport of the chart ring. -/
def affineOpenImmersionTopSections {X : Scheme.{u}} {R : CommRingCat.{u}}
    (f : Spec R ⟶ X) [IsOpenImmersion f] (M : X.Modules) :
    Γ(M, f ''ᵁ ⊤) →ₛₗ[(affineOpenImmersionTopScalars f).toRingHom]
      Γ(M.restrict f, ⊤) where
  toFun s := s
  map_add' _ _ := rfl
  map_smul' r s := by
    change r • s = (f.appIso ⊤).inv
      ((Scheme.ΓSpecIso R).inv ((affineOpenImmersionTopScalars f) r)) • s
    change r • s = (f.appIso ⊤).inv
      ((Scheme.ΓSpecIso R).inv ((Scheme.ΓSpecIso R).hom ((f.appIso ⊤).hom r))) • s
    simp only [Iso.hom_inv_id_apply]

/-- Genuine finite image sections give finite true affine-chart sections. -/
theorem affineOpenImmersionTopSections_finite {X : Scheme.{u}} {R : CommRingCat.{u}}
    (f : Spec R ⟶ X) [IsOpenImmersion f] (M : X.Modules)
    [Module.Finite Γ(X, f ''ᵁ ⊤) Γ(M, f ''ᵁ ⊤)] :
    Module.Finite R Γ(M.restrict f, ⊤) := by
  let : RingHomSurjective (affineOpenImmersionTopScalars f).toRingHom :=
    ⟨(affineOpenImmersionTopScalars f).surjective⟩
  exact Module.Finite.of_surjective (affineOpenImmersionTopSections f M) (fun s => ⟨s, rfl⟩)

/-- Every actual closed-projective pushforward chart is finite over its true coordinate ring. -/
theorem polynomialProjPushforwardChartSections_finite {K : Type} [Field K]
    {X : Scheme} {n : ℕ} (i : X ⟶ polynomialProj K n) [IsClosedImmersion i]
    {L : X.Modules} (a : LineBundleAtlas L) (j : Fin (n + 1)) :
    Module.Finite (polynomialProjCoordinateRing K n j)
      Γ(polynomialProjModuleChart ((Scheme.Modules.pushforward i).obj L) j, ⊤) := by
  let M := (Scheme.Modules.pushforward i).obj L
  let c := polynomialProjCoordinateImmersion K n j
  let : Module.Finite Γ(polynomialProj K n, c ''ᵁ ⊤) Γ(M, c ''ᵁ ⊤) := by
    rw [polynomialProjCoordinateImmersion_image_top]
    exact closedImmersion_pushforwardLineSections_finite i a
      (polynomialProjCoordinateOpen_isAffine K n j)
  exact affineOpenImmersionTopSections_finite c M

/-- Actual closed-immersion pushforward is quasicoherent on every genuine affine open. -/
theorem closedImmersion_affineRestrictedPushforward_isQuasicoherent
    {X Y : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i]
    {L : X.Modules} (a : LineBundleAtlas L) {U : Y.Opens} (hU : IsAffineOpen U) :
    (((Scheme.Modules.pushforward i).obj L).restrict U.ι).IsQuasicoherent := by
  let : IsAffine U.toScheme := hU
  let : IsAffine (i ⁻¹ᵁ U).toScheme := hU.preimage i
  let := a.isQuasicoherent
  let N := (Scheme.Modules.pushforward (i ∣_ U)).obj (L.restrict (i ⁻¹ᵁ U).ι)
  let : N.IsQuasicoherent :=
    affineSchemePushforward_isQuasicoherent (i ∣_ U) (L.restrict (i ⁻¹ᵁ U).ι)
  exact (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).prop_of_iso
    (pushforwardRestrictIso i U L).symm (inferInstance : N.IsQuasicoherent)

/-- Every actual closed-projective pushforward chart has genuine native quasicoherence. -/
theorem polynomialProjPushforwardChart_isQuasicoherent {K : Type} [Field K]
    {X : Scheme} {n : ℕ} (i : X ⟶ polynomialProj K n) [IsClosedImmersion i]
    {L : X.Modules} (a : LineBundleAtlas L) (j : Fin (n + 1)) :
    (polynomialProjModuleChart ((Scheme.Modules.pushforward i).obj L) j).IsQuasicoherent := by
  let M := (Scheme.Modules.pushforward i).obj L
  let c := polynomialProjCoordinateImmersion K n j
  have hU : IsAffineOpen c.opensRange := by
    rw [← c.image_top_eq_opensRange]
    change IsAffineOpen (polynomialProjCoordinateImmersion K n j ''ᵁ ⊤)
    rw [polynomialProjCoordinateImmersion_image_top]
    exact polynomialProjCoordinateOpen_isAffine K n j
  let : (M.restrict c.opensRange.ι).IsQuasicoherent :=
    closedImmersion_affineRestrictedPushforward_isQuasicoherent i a hU
  let α : M.restrict c ≅ (M.restrict c.opensRange.ι).restrict c.isoOpensRange.hom :=
    ((Scheme.Modules.restrictFunctorCongr c.isoOpensRange_hom_ι).app M).symm ≪≫
      (Scheme.Modules.restrictFunctorComp c.isoOpensRange.hom c.opensRange.ι).app M
  exact (SheafOfModules.isQuasicoherent (Spec (.of
    (polynomialProjCoordinateRing K n j))).ringCatSheaf).prop_of_iso α.symm
      (inferInstance : ((M.restrict c.opensRange.ι).restrict c.isoOpensRange.hom).IsQuasicoherent)

/-- Genuine closed-projective line geometry produces the actual ratio-overlap localization. -/
theorem polynomialProjPushforwardChartOverlapRestriction_isLocalized {K : Type} [Field K]
    {X : Scheme} {n : ℕ} (i : X ⟶ polynomialProj K n) [IsClosedImmersion i]
    {L : X.Modules} (a : LineBundleAtlas L) (j k : Fin (n + 1)) :
    IsLocalizedModule.Away (polynomialProjCoordinateRatio K n j k)
      (polynomialProjChartOverlapRestriction ((Scheme.Modules.pushforward i).obj L) j k) := by
  let := polynomialProjPushforwardChart_isQuasicoherent i a j
  exact polynomialProjChartOverlapRestriction_isLocalized _ j k

end

end SGPT.Foundations.Schemes
