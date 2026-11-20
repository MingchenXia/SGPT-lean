import SGPT.Trace.BertiniGlobalHolomorphicAdjunction

/-! Actual original global adjunction tensored with the SAME physical L.
All bundles/frames are native, and no arbitrary canonical norm is used. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace SGPT.Trace.Bertini

open Bundle Set Filter TensorProduct
open scoped Manifold ContDiff Topology TensorProduct
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DerivativeIdeal
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Toric.F1IntersectionDraft

private theorem actualTensorFrame_tmul {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {E F : HermitianHolomorphicLineBundle n M} (e : AtlasFrame E) (f : AtlasFrame F)
    (x : M) (he : x ∈ e.val.baseSet) (hf : x ∈ f.val.baseSet)
    (u : E.Fiber x) (v : F.Fiber x) :
    ((tensorAtlasFrame e f).val ⟨x, u ⊗ₜ[ℂ] v⟩).2 =
      (e.val ⟨x, u⟩).2 * (f.val ⟨x, v⟩).2 := by
  let := e.property
  let := f.property
  change tensorCoordinate _ _ e.val f.val x (u ⊗ₜ[ℂ] v) = _
  rw [tensorCoordinate_tmul, Trivialization.coe_linearMapAt_of_mem e.val he,
    Trivialization.coe_linearMapAt_of_mem f.val hf]

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (ζ : ComplexModel N)

def nativeBertiniMemberPullbackFrame
    (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint i ζ))
    (L : HermitianHolomorphicLineBundle (d + 1) X) (eL : AtlasFrame L) :
    letI := nativeBertiniMemberChartedSpace p i ζ hsm
    letI := nativeBertiniMemberComplex p i ζ hsm
    AtlasFrame (nativeHolomorphicPullbackBundle L (nativeBertiniMemberInclusionMap p i ζ hsm)) := by
  let := nativeBertiniMemberChartedSpace p i ζ hsm
  let := nativeBertiniMemberComplex p i ζ hsm
  exact ⟨eL.val.pullback (nativeBertiniMemberInclusionMap p i ζ hsm), by
    constructor
    exact ⟨eL.val, eL.property, rfl⟩⟩

def nativeBertiniPhysicalAdjunctionFiberEquiv
    (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint i ζ))
    (L : HermitianHolomorphicLineBundle (d + 1) X) (y : member p (affinePoint i ζ)) :
    letI := nativeBertiniMemberChartedSpace p i ζ hsm
    letI := nativeBertiniMemberComplex p i ζ hsm
    letI := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
    (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X))
      (nativeBertiniHyperplaneBundle p)) L).Fiber y.val ≃ₗ[ℂ]
    (tensor (nativeCanonicalBundle (n := d) (X := member p (affinePoint i ζ)))
      (nativeHolomorphicPullbackBundle L (nativeBertiniMemberInclusionMap p i ζ hsm))).Fiber y := by
  let := nativeBertiniMemberChartedSpace p i ζ hsm
  let := nativeBertiniMemberComplex p i ζ hsm
  let := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
  exact TensorProduct.congr (nativeBertiniAdjunctionFiberEquiv p i ζ hsm y)
    (LinearEquiv.refl ℂ (L.Fiber y.val))

theorem nativeBertiniPhysicalAdjunctionFrameCoefficient
    (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint i ζ))
    (L : HermitianHolomorphicLineBundle (d + 1) X)
    (y₀ : member p (affinePoint i ζ)) (x₀ : X) (j : Fin (N + 1)) (m : Fin (d + 1))
    (y : member p (affinePoint i ζ)) :
    letI := nativeBertiniMemberChartedSpace p i ζ hsm
    letI := nativeBertiniMemberComplex p i ζ hsm
    letI := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
    ∀ (_hy : y ∈ (complexChartAt (n := d) y₀).val.source)
      (_hx : y.val ∈ (complexChartAt (n := d + 1) x₀).val.source)
      (_hpj : p y.val ∈ (affineChart j).source)
      (_hm : chartDeriv (complexChartAt (n := d + 1) x₀) (EuclideanSpace.single m 1)
        (nativeBertiniLocalEquation p i ζ j) y.val ≠ 0)
      (eP : AtlasFrame (nativeBertiniHyperplaneBundle p)) (_hP : y.val ∈ eP.val.baseSet)
      (eL : AtlasFrame L) (_hL : y.val ∈ eL.val.baseSet)
      (T : (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X))
        (nativeBertiniHyperplaneBundle p)) L).Fiber y.val),
      ((tensorAtlasFrame (nativeCanonicalFrame (n := d) y₀)
        (nativeBertiniMemberPullbackFrame p i ζ hsm L eL)).val
        ⟨y, nativeBertiniPhysicalAdjunctionFiberEquiv p i ζ hsm L y T⟩).2 =
      ((tensorAtlasFrame (tensorAtlasFrame (nativeCanonicalFrame (n := d + 1) x₀) eP) eL).val
        ⟨y.val, T⟩).2 * ((eP.val ⟨y.val, nativeBertiniCoordinateSection p j y.val⟩).2)⁻¹ *
        (chartDeriv (complexChartAt (n := d + 1) x₀) (EuclideanSpace.single m 1)
          (nativeBertiniLocalEquation p i ζ j) y.val)⁻¹ *
        nativeChartCofactor (nativeBertiniMemberInclusionMap p i ζ hsm)
          (complexChartAt (n := d) y₀) (complexChartAt (n := d + 1) x₀) m
          ((complexChartAt (n := d) y₀).val y) := by
  let := nativeBertiniMemberChartedSpace p i ζ hsm
  let := nativeBertiniMemberComplex p i ζ hsm
  let := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
  intro hy hx hpj hm eP hP eL hL T
  let eK := nativeCanonicalFrame (n := d + 1) x₀
  let eH := nativeCanonicalFrame (n := d) y₀
  let q := tensorAtlasFrame eK eP
  let qL := tensorAtlasFrame q eL
  let lH := nativeBertiniMemberPullbackFrame p i ζ hsm L eL
  let tH := tensorAtlasFrame eH lH
  let := eK.property
  let := eH.property
  let := eP.property
  let := eL.property
  let := q.property
  let := qL.property
  let := lH.property
  let := tH.property
  have hK : y.val ∈ eK.val.baseSet := hx
  have hH : y ∈ eH.val.baseSet := hy
  have hq : y.val ∈ q.val.baseSet := ⟨hK, hP⟩
  have hqL : y.val ∈ qL.val.baseSet := ⟨hq, hL⟩
  have hlH : y ∈ lH.val.baseSet := hL
  have htH : y ∈ tH.val.baseSet := ⟨hH, hlH⟩
  let c := ((eP.val ⟨y.val, nativeBertiniCoordinateSection p j y.val⟩).2)⁻¹ *
    (chartDeriv (complexChartAt (n := d + 1) x₀) (EuclideanSpace.single m 1)
      (nativeBertiniLocalEquation p i ζ j) y.val)⁻¹ *
    nativeChartCofactor (nativeBertiniMemberInclusionMap p i ζ hsm)
      (complexChartAt (n := d) y₀) (complexChartAt (n := d + 1) x₀) m
      ((complexChartAt (n := d) y₀).val y)
  let F := (tH.val.linearEquivAt ℂ y htH).toLinearMap.comp
    (nativeBertiniPhysicalAdjunctionFiberEquiv p i ζ hsm L y).toLinearMap
  let G := c • (qL.val.linearEquivAt ℂ y.val hqL).toLinearMap
  have hFG : F = G := by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro A
    apply LinearMap.ext
    intro l
    change (tH.val ⟨y, nativeBertiniAdjunctionFiberEquiv p i ζ hsm y A ⊗ₜ[ℂ] l⟩).2 =
      c * (qL.val ⟨y.val, A ⊗ₜ[ℂ] l⟩).2
    rw [actualTensorFrame_tmul eH lH y hH hlH, actualTensorFrame_tmul q eL y.val hq hL,
      nativeBertiniAdjunctionFrameCoefficient p i ζ hsm y₀ x₀ j m y hy hx hpj hm eP hP]
    have hread : (lH.val ⟨y, l⟩).2 = (eL.val ⟨y.val, l⟩).2 := rfl
    rw [hread]
    dsimp only [c, q, eK]
    ring
  have h := LinearMap.congr_fun hFG T
  change (tH.val ⟨y, nativeBertiniPhysicalAdjunctionFiberEquiv p i ζ hsm L y T⟩).2 =
    c * (qL.val ⟨y.val, T⟩).2 at h
  rw [h]
  dsimp only [c, qL, q, eK]
  ring


def nativeBertiniPhysicalAdjunctionSection
    (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint i ζ))
    (L : HermitianHolomorphicLineBundle (d + 1) X)
    (S : HolomorphicSections (n := d + 1)
      (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) (nativeBertiniHyperplaneBundle p)) L).Fiber) :
    letI := nativeBertiniMemberChartedSpace p i ζ hsm
    letI := nativeBertiniMemberComplex p i ζ hsm
    letI := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
    HolomorphicSections (n := d) (tensor (nativeCanonicalBundle (n := d)
      (X := member p (affinePoint i ζ)))
      (nativeHolomorphicPullbackBundle L (nativeBertiniMemberInclusionMap p i ζ hsm))).Fiber := by
  let := nativeBertiniMemberChartedSpace p i ζ hsm
  let := nativeBertiniMemberComplex p i ζ hsm
  let := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
  refine { toFun := fun y => nativeBertiniPhysicalAdjunctionFiberEquiv p i ζ hsm L y (S y.val)
           contMDiff_toFun := ?_ }
  intro y₀
  let x₀ := y₀.val
  let eX := complexChartAt (n := d + 1) x₀
  let eH := complexChartAt (n := d) y₀
  let eK := nativeCanonicalFrame (n := d + 1) x₀
  let eP : AtlasFrame (nativeBertiniHyperplaneBundle p) :=
    ⟨trivializationAt ℂ (nativeBertiniHyperplaneBundle p).Fiber x₀, inferInstance⟩
  let eL : AtlasFrame L := ⟨trivializationAt ℂ L.Fiber x₀, inferInstance⟩
  let q := tensorAtlasFrame (tensorAtlasFrame eK eP) eL
  let fH := tensorAtlasFrame (nativeCanonicalFrame (n := d) y₀)
    (nativeBertiniMemberPullbackFrame p i ζ hsm L eL)
  let := eK.property
  let := eP.property
  let := eL.property
  let := q.property
  let := fH.property
  let inc := nativeBertiniMemberInclusionMap p i ζ hsm
  let j := chartIndex (p x₀)
  have hx₀ : x₀ ∈ eX.val.source := mem_complexChartAt_source x₀
  have hy₀ : y₀ ∈ eH.val.source := mem_complexChartAt_source y₀
  have hpj₀ : p x₀ ∈ (affineChart j).source := mem_affineChart_chartIndex (p x₀)
  have hP₀ : x₀ ∈ eP.val.baseSet := mem_baseSet_trivializationAt ℂ _ x₀
  have hK₀ : x₀ ∈ eK.val.baseSet := hx₀
  have hL₀ : x₀ ∈ eL.val.baseSet := mem_baseSet_trivializationAt ℂ _ x₀
  have hq₀ : x₀ ∈ q.val.baseSet := ⟨⟨hK₀, hP₀⟩, hL₀⟩
  have hfH₀ : y₀ ∈ fH.val.baseSet := ⟨hy₀, hL₀⟩
  obtain ⟨m, hm₀⟩ := exists_nativeBertiniChartPartial_ne_zero p i ζ j eX x₀ hx₀ hpj₀ y₀.property hsm
  let gm := chartDeriv eX (EuclideanSpace.single m 1) (nativeBertiniLocalEquation p i ζ j)
  let cs := fun x => (eP.val ⟨x, nativeBertiniCoordinateSection p j x⟩).2
  have hcs : ContMDiffAt 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ℂ) ∞ cs x₀ :=
    (eP.val.contMDiffAt_section_iff hP₀).mp ((nativeBertiniCoordinateSection p j).contMDiff x₀)
  have hcsne : cs x₀ ≠ 0 := by
    intro hz
    apply nativeBertiniCoordinateSection_ne_zero p j x₀ hpj₀
    apply (eP.val.linearEquivAt ℂ x₀ hP₀).injective
    exact hz.trans (map_zero _).symm
  have hgm := contMDiffAt_nativeBertiniChartPartial p i ζ j eX m x₀ hx₀ hpj₀
  have hs := (q.val.contMDiffAt_section_iff hq₀).mp (S.contMDiff x₀)
  have hprod := (((hs.comp y₀ inc.contMDiff.contMDiffAt).mul
    ((hcs.inv₀ hcsne).comp y₀ inc.contMDiff.contMDiffAt)).mul
    ((hgm.inv₀ hm₀).comp y₀ inc.contMDiff.contMDiffAt)).mul
    (contMDiffAt_nativeChartCofactor inc eH eX m y₀ hy₀ hx₀)
  apply (fH.val.contMDiffAt_section_iff hfH₀).mpr
  apply hprod.congr_of_eventuallyEq
  have hnearX : ∀ᶠ y : member p (affinePoint i ζ) in 𝓝 y₀, y.val ∈ eX.val.source :=
    inc.contMDiff.continuous.continuousAt.eventually (eX.val.open_source.mem_nhds hx₀)
  have hnearP : ∀ᶠ y : member p (affinePoint i ζ) in 𝓝 y₀, y.val ∈ eP.val.baseSet :=
    inc.contMDiff.continuous.continuousAt.eventually (eP.val.open_baseSet.mem_nhds hP₀)
  have hnearL : ∀ᶠ y : member p (affinePoint i ζ) in 𝓝 y₀, y.val ∈ eL.val.baseSet :=
    inc.contMDiff.continuous.continuousAt.eventually (eL.val.open_baseSet.mem_nhds hL₀)
  have hnearj : ∀ᶠ y : member p (affinePoint i ζ) in 𝓝 y₀, p y.val ∈ (affineChart j).source :=
    (p.contMDiff.continuous.comp inc.contMDiff.continuous).continuousAt.eventually
      ((affineChart j).open_source.mem_nhds hpj₀)
  have hgm0 : ContinuousAt gm x₀ := hgm.continuousAt
  have hgmH : ContinuousAt (fun y : member p (affinePoint i ζ) => gm y.val) y₀ :=
    hgm0.comp continuous_subtype_val.continuousAt
  have hnearm : ∀ᶠ y : member p (affinePoint i ζ) in 𝓝 y₀, gm y.val ≠ 0 :=
    hgmH.eventually_ne (show gm y₀.val ≠ 0 from hm₀)
  filter_upwards [eH.val.open_source.mem_nhds hy₀, hnearX, hnearP, hnearL, hnearj, hnearm]
    with y hy hx hP hL hpj hm
  exact (nativeBertiniPhysicalAdjunctionFrameCoefficient p i ζ hsm L y₀ x₀ j m y hy hx hpj hm eP hP eL hL (S y.val))

theorem nativeBertiniPhysicalAdjunctionSection_apply
    (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint i ζ))
    (L : HermitianHolomorphicLineBundle (d + 1) X)
    (S : HolomorphicSections (n := d + 1)
      (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) (nativeBertiniHyperplaneBundle p)) L).Fiber)
    (y : member p (affinePoint i ζ)) :
    letI := nativeBertiniMemberChartedSpace p i ζ hsm
    letI := nativeBertiniMemberComplex p i ζ hsm
    letI := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
    nativeBertiniPhysicalAdjunctionSection p i ζ hsm L S y =
      nativeBertiniPhysicalAdjunctionFiberEquiv p i ζ hsm L y (S y.val) := rfl


end SGPT.Trace.Bertini
