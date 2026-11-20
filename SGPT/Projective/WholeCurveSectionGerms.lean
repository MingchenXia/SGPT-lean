import SGPT.Projective.WholeCurveZeroArtinian
import SGPT.Projective.OriginalTensorSectionLength
import SGPT.Projective.OriginalSectionOpenZeroGerm

/-! ALL actual original points/components: same original local domains and
ordinary section nonzero germs, genuine actual tensor componentwise nonzero.
Blueprint: whole-curve-section-germs.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.AlgebraicCurveDegree
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set
open SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

/-- ANY original pulled section/frame's exact SAME original germ/stalkMap square. -/
theorem originalSectionFrameGerm_pullback {X Y : Scheme.{0}} (f : X ⟶ Y) {L : Y.Modules}
    {U : Y.Opens} (e : LocalBundleFrame L U) (s : Γ(L, ⊤)) (x : X) (hx : f x ∈ U) :
    originalSectionFrameGerm (matePullbackFrame f e) (originalPulledSection f s) x hx =
      f.stalkMap x (originalSectionFrameGerm e s (f x) hx) := by
  unfold originalSectionFrameGerm
  have hc := originalPulledSection_coefficients f s e (𝟙 U)
  change (matePullbackFrame f e).coefficients (𝟙 (f ⁻¹ᵁ U))
    (((Scheme.Modules.pullback f).obj L).val.map (f ⁻¹ᵁ U).leTop.op (originalPulledSection f s)) =
    f.app U (e.coefficients (𝟙 U) (L.val.map U.leTop.op s)) at hc
  rw [hc]
  exact (Scheme.Hom.germ_stalkMap_apply f U x hx _).symm

/-- EVERY original point, including nonclosed, has SAME parent local domain via ACTUAL component stalk iso. -/
theorem smoothProjective_allPointStalk_isDomain {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ))
    (n : ℕ) [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]
    (E : ClosedProjectiveEmbedding f) (x : X) : IsDomain (X.presheaf.stalk x) := by
  obtain ⟨C, hC⟩ := smoothProjective_componentOpens_cover f n E x
  let U := smoothProjectiveComponentOpen f n E C.val C.property
  let := smoothProjective_component_isIntegral f n E C.val C.property
  let p : U := ⟨x, hC⟩
  let er := (asIso (U.ι.stalkMap p)).commRingCatIsoToRingEquiv
  exact Function.Injective.isDomain er er.injective

/-- Componentwise actual original nonzero section has nonzero SAME germ in EVERY frame/point. -/
theorem wholeCurveSectionFrameGerm_ne_zero {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ))
    (E : ClosedProjectiveEmbedding f) [SmoothOfRelativeDimension 1 f] [IsSeparated f] [QuasiCompact f]
    {L : X.Modules} (a : LineBundleAtlas L) (s : Γ(L, ⊤)) (hs : SectionNonzeroOnComponents f E s)
    {U : X.Opens} (e : LocalBundleFrame L U) (x : X) (hx : x ∈ U) :
    originalSectionFrameGerm e s x hx ≠ 0 := by
  obtain ⟨C, hC⟩ := smoothProjective_componentOpens_cover f 1 E x
  let V := smoothProjectiveComponentOpen f 1 E C.val C.property
  let := smoothProjective_component_isIntegral f 1 E C.val C.property
  let p : V := ⟨x, hC⟩
  have hn := originalSectionFrameGerm_ne_zero (matePullbackAtlas V.ι a) (matePullbackFrame V.ι e)
    (originalPulledSection V.ι s) (hs C) p hx
  have hg := originalSectionFrameGerm_pullback V.ι e s p hx
  intro hzero
  apply hn
  exact hg.trans ((congrArg (V.ι.stalkMap p) hzero).trans (map_zero _))

/-- Literal original tensor section is nonzero on EACH SAME original whole component. -/
theorem wholeCurveTensorSectionNonzeroOnComponents {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ))
    (E : ClosedProjectiveEmbedding f) [SmoothOfRelativeDimension 1 f] [IsSeparated f] [QuasiCompact f]
    {L N : X.Modules} (a : LineBundleAtlas L) (b : LineBundleAtlas N)
    (s : Γ(L, ⊤)) (hs : SectionNonzeroOnComponents f E s)
    (t : Γ(N, ⊤)) (ht : SectionNonzeroOnComponents f E t) :
    SectionNonzeroOnComponents (L := bundleTensor L N) f E (tensorSection L N ⊤ s t) := by
  intro C hzero
  obtain ⟨x, hxC⟩ := C.property.1.nonempty
  obtain ⟨i, hi⟩ := a.covers x
  obtain ⟨j, hj⟩ := b.covers x
  let U := a.opens i ⊓ b.opens j
  have hx : x ∈ U := ⟨hi, hj⟩
  let e : LocalBundleFrame L U := bundleHomRestrictionIso L
    (SheafOfModules.unit X.ringCatSheaf) (TopologicalSpace.Opens.infLELeft _ _) (a.frame i)
  let d : LocalBundleFrame N U := bundleHomRestrictionIso N
    (SheafOfModules.unit X.ringCatSheaf) (TopologicalSpace.Opens.infLERight _ _) (b.frame j)
  let := smoothProjective_allPointStalk_isDomain f 1 E x
  have hn := mul_ne_zero (wholeCurveSectionFrameGerm_ne_zero f E a s hs e x hx)
    (wholeCurveSectionFrameGerm_ne_zero f E b t ht d x hx)
  have hg : originalSectionFrameGerm (e.tensor d) (tensorSection L N ⊤ s t) x hx = 0 :=
    originalSection_coefficientGerm_eq_zero_of_open_pull_zero (M := bundleTensor L N)
      (smoothProjectiveComponentOpen f 1 E C.val C.property) (tensorSection L N ⊤ s t) hzero
      (e.tensor d) x hxC hx
  exact hn ((originalTensorSectionFrameGerm_mul e d s t x hx).symm.trans hg)

end SGPT.Projective.NumEq.AlgebraicCurveDegree
