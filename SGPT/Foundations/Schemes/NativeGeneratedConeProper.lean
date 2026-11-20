import SGPT.Foundations.Schemes.NativeLineSectionIncidence
/-!
# NativeGeneratedConeProper

The full section-ring contraction is over the actual affinization. Actual section coordinates give a literal cone factorization of the closed incidence map. Proper affine-base geometry and genuine generation produce proper contraction.
-/

open CategoryTheory Limits AlgebraicGeometry Opposite
namespace SGPT.Foundations.Schemes
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
variable {X : Scheme.{u}}

/-- Any actual proper morphism to an affine scheme makes the actual affinization proper. -/
theorem nativeAffinization_isProper {R : CommRingCat.{u}} (f : X ⟶ Spec R)
    [IsProper f] : IsProper X.toSpecΓ := by
  let g := Spec.map ((Scheme.ΓSpecIso R).inv ≫ f.appTop)
  have : IsProper (X.toSpecΓ ≫ g) := by
    change IsProper (X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso R).inv ≫ f.appTop))
    rw [nativeSchemeMap_eq_globalMap f]
    infer_instance
  exact IsProper.of_comp X.toSpecΓ g

/-- The actual section-ring cone is over the actual global structure ring through degree zero. -/
def IntrinsicLineBundle.nativeConeGlobalStructuralMap (L : IntrinsicLineBundle X) :
    L.sectionRingCone ⟶ Spec (.of Γ(X, ⊤)) :=
  Spec.map (CommRingCat.ofHom L.sectionRingConstants)

/-- Degree-zero genuine section evaluation is the literal regular base pullback. -/
theorem IntrinsicLineBundle.nativeChartEvaluation_constants (L : IntrinsicLineBundle X)
    (c : NativeFramedOpen L.atlas) :
    (L.nativeChartEvaluation c).comp L.sectionRingConstants =
      (nativeAffineLineProjection c.2.1.toScheme ≫ c.2.1.ι).appTop.hom := by
  ext r
  change L.nativeChartEvaluation c (L.ofSection 0 r) = _
  rw [L.nativeChartEvaluation_ofSection]
  simp only [nativeFramedHomogeneousFunction, nativeFramedSectionCoefficient_degree_zero,
    pow_zero, mul_one, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
    RingHom.comp_apply]

/-- The genuine cone evaluation is over the actual affinization of its actual base. -/
theorem IntrinsicLineBundle.nativeConeMap_over_affinization (L : IntrinsicLineBundle X) :
    L.nativeConeMap ≫ L.nativeConeGlobalStructuralMap =
      nativeDualLineProjection L.atlas ≫ X.toSpecΓ := by
  apply colimit.hom_ext
  intro c
  rw [← Category.assoc, L.nativeConeMap_on_open]
  change L.nativeChartConeMap c ≫ L.nativeConeGlobalStructuralMap =
    nativeFramedChart L.atlas c ≫ nativeDualLineProjection L.atlas ≫ X.toSpecΓ
  rw [← Category.assoc, nativeFramedChart_projection]
  unfold IntrinsicLineBundle.nativeChartConeMap IntrinsicLineBundle.nativeConeGlobalStructuralMap
  rw [Category.assoc, ← Spec.map_comp]
  have he : CommRingCat.ofHom L.sectionRingConstants ≫
      CommRingCat.ofHom (L.nativeChartEvaluation c) =
      (nativeAffineLineProjection c.2.1.toScheme ≫ c.2.1.ι).appTop := by
    apply CommRingCat.hom_ext
    exact L.nativeChartEvaluation_constants c
  rw [he]
  exact (Scheme.toSpecΓ_naturality _).symm

/-- Genuine degree-one sections define an actual map from the full cone to affine coordinate space. -/
def IntrinsicLineBundle.nativeConeSectionVector (L : IntrinsicLineBundle X) {I : Type u}
    (s : I → bundlePowerGlobalSections L.sheaf 1) :
    L.sectionRingCone ⟶ AffineSpace I (Spec (.of Γ(X, ⊤))) :=
  AffineSpace.homOfVector L.nativeConeGlobalStructuralMap
    (fun i ↦ (Scheme.ΓSpecIso (.of L.sectionRing)).inv (L.ofSection 1 (s i)))

/-- The true incidence projection factors through the true full-cone evaluation. -/
theorem IntrinsicLineBundle.nativeConeSectionVector_commutes (L : IntrinsicLineBundle X)
    {I : Type u} (s : I → bundlePowerGlobalSections L.sheaf 1) :
    L.nativeConeMap ≫ L.nativeConeSectionVector s =
      L.nativeSectionIncidence s ≫ AffineSpace.map I X.toSpecΓ := by
  apply AffineSpace.hom_ext
  · simp only [Category.assoc, IntrinsicLineBundle.nativeConeSectionVector,
      AffineSpace.homOfVector_over, AffineSpace.map_over,
      IntrinsicLineBundle.nativeSectionIncidence_projection_assoc]
    exact L.nativeConeMap_over_affinization
  · intro i
    change L.nativeConeMap.appTop
      ((L.nativeConeSectionVector s).appTop (AffineSpace.coord _ i)) =
      (L.nativeSectionIncidence s).appTop
        ((AffineSpace.map I X.toSpecΓ).appTop (AffineSpace.coord _ i))
    rw [show (L.nativeConeSectionVector s).appTop (AffineSpace.coord _ i) =
      (Scheme.ΓSpecIso (.of L.sectionRing)).inv (L.ofSection 1 (s i)) from
        AffineSpace.homOfVector_appTop_coord _ _ _, AffineSpace.map_appTop_coord]
    change L.nativeTotalEvaluation (L.ofSection 1 (s i)) =
      (AffineSpace.homOfVector (nativeDualLineProjection L.atlas)
        (fun j ↦ L.nativeTotalEvaluation (L.ofSection 1 (s j)))).appTop (AffineSpace.coord X i)
    exact (AffineSpace.homOfVector_appTop_coord (nativeDualLineProjection L.atlas)
      (fun j : I ↦ L.nativeTotalEvaluation (L.ofSection 1 (s j))) i).symm

/-- Actual generation and proper affinization make the genuine full-cone contraction proper. -/
theorem IntrinsicLineBundle.nativeConeMap_isProper_of_generated
    (L : IntrinsicLineBundle X) {I : Type u}
    (s : I → bundlePowerGlobalSections L.sheaf 1) (hs : L.NativeSectionsGenerate s)
    [IsProper X.toSpecΓ] : IsProper L.nativeConeMap := by
  have : IsAffine L.sectionRingCone := inferInstanceAs (IsAffine (Spec (.of L.sectionRing)))
  have : IsSeparated (L.nativeConeSectionVector s) := inferInstance
  have : IsClosedImmersion (L.nativeSectionIncidence s) :=
    L.nativeSectionIncidence_isClosedImmersion s hs
  have : IsProper (AffineSpace.map I X.toSpecΓ) :=
    MorphismProperty.of_isPullback (AffineSpace.isPullback_map X.toSpecΓ).flip inferInstance
  have : IsProper (L.nativeConeMap ≫ L.nativeConeSectionVector s) := by
    rw [L.nativeConeSectionVector_commutes s]
    infer_instance
  exact IsProper.of_comp L.nativeConeMap (L.nativeConeSectionVector s)

/-- Genuine generated line bundles over an actual proper affine base have proper full-cone evaluation. -/
theorem IntrinsicLineBundle.nativeConeMap_isProper_of_generated_over_affine
    (L : IntrinsicLineBundle X) {I : Type u}
    (s : I → bundlePowerGlobalSections L.sheaf 1) (hs : L.NativeSectionsGenerate s)
    {R : CommRingCat.{u}} (f : X ⟶ Spec R) [IsProper f] : IsProper L.nativeConeMap := by
  have := nativeAffinization_isProper f
  exact L.nativeConeMap_isProper_of_generated s hs

end
end SGPT.Foundations.Schemes
