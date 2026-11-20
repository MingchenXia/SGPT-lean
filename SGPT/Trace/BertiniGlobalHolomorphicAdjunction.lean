import SGPT.Trace.BertiniAdjunctionFrameCoordinates
import SGPT.Trace.BertiniLocalOriginalDenominatorSmooth

/-! Genuine native global holomorphic adjunction sections, constructed from
original smooth-member geometry and exact original native coefficient formulas.
The full incidence base O_Lambda(1) stays explicit. -/

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

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (ζ : ComplexModel N)

def nativeBertiniAdjunctionSection
    (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint i ζ))
    (S : HolomorphicSections (n := d + 1)
      (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) (nativeBertiniHyperplaneBundle p)).Fiber) :
    letI := nativeBertiniMemberChartedSpace p i ζ hsm
    letI := nativeBertiniMemberComplex p i ζ hsm
    letI := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
    HolomorphicSections (n := d) (nativeCanonicalBundle (n := d)
      (X := member p (affinePoint i ζ))).Fiber := by
  let := nativeBertiniMemberChartedSpace p i ζ hsm
  let := nativeBertiniMemberComplex p i ζ hsm
  let := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
  refine { toFun := fun y => nativeBertiniAdjunctionFiberEquiv p i ζ hsm y (S y.val)
           contMDiff_toFun := ?_ }
  intro y₀
  let x₀ := y₀.val
  let eX := complexChartAt (n := d + 1) x₀
  let eH := complexChartAt (n := d) y₀
  let eK := nativeCanonicalFrame (n := d + 1) x₀
  let eP : AtlasFrame (nativeBertiniHyperplaneBundle p) :=
    ⟨trivializationAt ℂ (nativeBertiniHyperplaneBundle p).Fiber x₀, inferInstance⟩
  let q := tensorAtlasFrame eK eP
  let fH := nativeCanonicalFrame (n := d) y₀
  let := eK.property
  let := eP.property
  let := q.property
  let := fH.property
  let inc := nativeBertiniMemberInclusionMap p i ζ hsm
  let j := chartIndex (p x₀)
  have hx₀ : x₀ ∈ eX.val.source := mem_complexChartAt_source x₀
  have hy₀ : y₀ ∈ eH.val.source := mem_complexChartAt_source y₀
  have hpj₀ : p x₀ ∈ (affineChart j).source := mem_affineChart_chartIndex (p x₀)
  have hP₀ : x₀ ∈ eP.val.baseSet := mem_baseSet_trivializationAt ℂ _ x₀
  have hK₀ : x₀ ∈ eK.val.baseSet := hx₀
  have hq₀ : x₀ ∈ q.val.baseSet := ⟨hK₀, hP₀⟩
  have hfH₀ : y₀ ∈ fH.val.baseSet := hy₀
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
  have hnearj : ∀ᶠ y : member p (affinePoint i ζ) in 𝓝 y₀, p y.val ∈ (affineChart j).source :=
    (p.contMDiff.continuous.comp inc.contMDiff.continuous).continuousAt.eventually
      ((affineChart j).open_source.mem_nhds hpj₀)
  have hgm0 : ContinuousAt gm x₀ := hgm.continuousAt
  have hgmH : ContinuousAt (fun y : member p (affinePoint i ζ) => gm y.val) y₀ :=
    hgm0.comp continuous_subtype_val.continuousAt
  have hnearm : ∀ᶠ y : member p (affinePoint i ζ) in 𝓝 y₀, gm y.val ≠ 0 :=
    hgmH.eventually_ne (show gm y₀.val ≠ 0 from hm₀)
  filter_upwards [eH.val.open_source.mem_nhds hy₀, hnearX, hnearP, hnearj, hnearm]
    with y hy hx hP hpj hm
  exact (nativeBertiniAdjunctionFrameCoefficient p i ζ hsm y₀ x₀ j m y hy hx hpj hm eP hP (S y.val))

theorem nativeBertiniAdjunctionSection_apply
    (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint i ζ))
    (S : HolomorphicSections (n := d + 1)
      (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) (nativeBertiniHyperplaneBundle p)).Fiber)
    (y : member p (affinePoint i ζ)) :
    letI := nativeBertiniMemberChartedSpace p i ζ hsm
    letI := nativeBertiniMemberComplex p i ζ hsm
    letI := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
    nativeBertiniAdjunctionSection p i ζ hsm S y =
      nativeBertiniAdjunctionFiberEquiv p i ζ hsm y (S y.val) := rfl


def nativeBertiniAdjunctionRestriction
    (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint i ζ)) :
    letI := nativeBertiniMemberChartedSpace p i ζ hsm
    letI := nativeBertiniMemberComplex p i ζ hsm
    letI := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
    HolomorphicSections (n := d + 1)
      (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) (nativeBertiniHyperplaneBundle p)).Fiber →ₗ[ℂ]
    HolomorphicSections (n := d) (nativeCanonicalBundle (n := d)
      (X := member p (affinePoint i ζ))).Fiber := by
  let := nativeBertiniMemberChartedSpace p i ζ hsm
  let := nativeBertiniMemberComplex p i ζ hsm
  let := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
  refine { toFun := nativeBertiniAdjunctionSection p i ζ hsm
           map_add' := ?_
           map_smul' := ?_ }
  · intro S T
    ext y
    exact (nativeBertiniAdjunctionFiberEquiv p i ζ hsm y).map_add (S y.val) (T y.val)
  · intro c S
    ext y
    exact (nativeBertiniAdjunctionFiberEquiv p i ζ hsm y).map_smul c (S y.val)

theorem nativeBertiniAdjunctionSection_multiply_definingSection
    (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint i ζ))
    (s : HolomorphicSections (n := d + 1) (nativeCanonicalBundle (n := d + 1) (X := X)).Fiber) :
    letI := nativeBertiniMemberChartedSpace p i ζ hsm
    letI := nativeBertiniMemberComplex p i ζ hsm
    letI := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
    nativeBertiniAdjunctionSection p i ζ hsm
      (nativeTensorSection (nativeCanonicalBundle (n := d + 1) (X := X))
        (nativeBertiniHyperplaneBundle p) s (nativeBertiniAffineSection p i ζ)) = 0 := by
  let := nativeBertiniMemberChartedSpace p i ζ hsm
  let := nativeBertiniMemberComplex p i ζ hsm
  let := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
  ext y
  rw [nativeBertiniAdjunctionSection_apply]
  change nativeBertiniAdjunctionFiberEquiv p i ζ hsm y
    (s y.val ⊗ₜ[ℂ] nativeBertiniAffineSection p i ζ y.val) = 0
  rw [(nativeBertiniAffineSection_zero_iff p i ζ y.val).mpr y.property,
    TensorProduct.tmul_zero, map_zero]

end SGPT.Trace.Bertini
