import SGPT.Trace.BertiniMemberPullbackAdjunction

/-! Actual native member adjunction manufactures its original local
holomorphic unit, genuine holomorphic inverse and full native H0 equivalence. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
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

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (ζ : ComplexModel N)
  (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint i ζ))
  (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) X)

theorem exists_nativeBertiniPhysicalAdjunction_local_unit :
    letI := nativeBertiniMemberChartedSpace p i ζ hsm
    letI := nativeBertiniMemberComplex p i ζ hsm
    letI := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
    ∀ y₀ : member p (affinePoint i ζ),
      ∃ (e : AtlasFrame (nativeHolomorphicPullbackBundle
        (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) (nativeBertiniHyperplaneBundle p)) L)
        (nativeBertiniMemberInclusionMap p i ζ hsm)))
        (f : AtlasFrame (tensor (nativeCanonicalBundle (n := d) (X := member p (affinePoint i ζ)))
          (nativeHolomorphicPullbackBundle L (nativeBertiniMemberInclusionMap p i ζ hsm)))),
        y₀ ∈ e.val.baseSet ∧ y₀ ∈ f.val.baseSet ∧ ∃ C : member p (affinePoint i ζ) → ℂ,
        ContMDiffAt 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ℂ) ∞ C y₀ ∧ C y₀ ≠ 0 ∧
        ∀ᶠ y in 𝓝 y₀, ∀ T : (nativeHolomorphicPullbackBundle
          (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) (nativeBertiniHyperplaneBundle p)) L)
          (nativeBertiniMemberInclusionMap p i ζ hsm)).Fiber y,
          (f.val ⟨y,nativeBertiniPhysicalAdjunctionFiberEquiv p i ζ hsm L y T⟩).2 =
            (e.val ⟨y,T⟩).2 * C y := by
  let := nativeBertiniMemberChartedSpace p i ζ hsm
  let := nativeBertiniMemberComplex p i ζ hsm
  let := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
  intro y₀
  let x₀ := y₀.val
  let eX := complexChartAt (n := d + 1) x₀
  let eH := complexChartAt (n := d) y₀
  let eK := nativeCanonicalFrame (n := d + 1) x₀
  let eP : AtlasFrame (nativeBertiniHyperplaneBundle p) := ⟨trivializationAt ℂ _ x₀,inferInstance⟩
  let eL : AtlasFrame L := ⟨trivializationAt ℂ L.Fiber x₀,inferInstance⟩
  let q := tensorAtlasFrame (tensorAtlasFrame eK eP) eL
  let fH := tensorAtlasFrame (nativeCanonicalFrame (n := d) y₀) (nativeBertiniMemberPullbackFrame p i ζ hsm L eL)
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
  have hL₀ : x₀ ∈ eL.val.baseSet := mem_baseSet_trivializationAt ℂ _ x₀
  have hq₀ : x₀ ∈ q.val.baseSet := ⟨⟨hx₀,hP₀⟩,hL₀⟩
  have hfH₀ : y₀ ∈ fH.val.baseSet := ⟨hy₀,hL₀⟩
  obtain ⟨m,hm₀⟩ := exists_nativeBertiniChartPartial_ne_zero p i ζ j eX x₀ hx₀ hpj₀ y₀.property hsm
  let gm := chartDeriv eX (EuclideanSpace.single m 1) (nativeBertiniLocalEquation p i ζ j)
  let cs := fun x => (eP.val ⟨x,nativeBertiniCoordinateSection p j x⟩).2
  have hcs : ContMDiffAt 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ℂ) ∞ cs x₀ :=
    (eP.val.contMDiffAt_section_iff hP₀).mp ((nativeBertiniCoordinateSection p j).contMDiff x₀)
  have hcsne : cs x₀ ≠ 0 := by
    intro hz
    apply nativeBertiniCoordinateSection_ne_zero p j x₀ hpj₀
    apply (eP.val.linearEquivAt ℂ x₀ hP₀).injective
    exact hz.trans (map_zero _).symm
  have hgm := contMDiffAt_nativeBertiniChartPartial p i ζ j eX m x₀ hx₀ hpj₀
  let qp := nativeBertiniMemberPullbackFrame p i ζ hsm _ q
  let := qp.property
  have hqp₀ : y₀ ∈ qp.val.baseSet := hq₀
  let C : member p (affinePoint i ζ) → ℂ := fun y => (cs y.val)⁻¹ * (gm y.val)⁻¹ *
    nativeChartCofactor inc eH eX m (eH.val y)
  have hcsAlong : ContMDiffAt 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ℂ) ∞
      (fun y : member p (affinePoint i ζ) => cs y.val) y₀ :=
    ContMDiffAt.comp (f := (inc : member p (affinePoint i ζ) → X)) (g := cs) y₀ hcs inc.contMDiff.contMDiffAt
  have hgmAlongDiff : ContMDiffAt 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ℂ) ∞
      (fun y : member p (affinePoint i ζ) => gm y.val) y₀ :=
    hgm.comp y₀ inc.contMDiff.contMDiffAt
  have hcsH := hcsAlong.inv₀ hcsne
  have hgmH := hgmAlongDiff.inv₀ hm₀
  have hC : ContMDiffAt 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ℂ) ∞ C y₀ := by
    exact (hcsH.mul hgmH).mul (contMDiffAt_nativeChartCofactor inc eH eX m y₀ hy₀ hx₀)
  have hCne : C y₀ ≠ 0 := by
    let E := qp.val.linearEquivAt ℂ y₀ hqp₀
    let F := fH.val.linearEquivAt ℂ y₀ hfH₀
    let J := nativeBertiniPhysicalAdjunctionFiberEquiv p i ζ hsm L y₀
    have hunit : (q.val ⟨x₀,E.symm (1 : ℂ)⟩).2 = 1 := by
      change E (E.symm (1 : ℂ)) = 1
      exact E.apply_symm_apply 1
    have hcoefne : F (J (E.symm (1 : ℂ))) ≠ 0 := by
      intro hz
      have hJ : J (E.symm (1 : ℂ)) = 0 := F.injective (hz.trans (map_zero F).symm)
      have hE : E.symm (1 : ℂ) = 0 := J.injective (hJ.trans (map_zero J).symm)
      have h := congrArg E hE
      rw [LinearEquiv.apply_symm_apply,map_zero] at h
      exact one_ne_zero h
    intro hz
    apply hcoefne
    have h := nativeBertiniPhysicalAdjunctionFrameCoefficient p i ζ hsm L y₀ x₀ j m y₀ hy₀ hx₀ hpj₀ hm₀
      eP hP₀ eL hL₀ (E.symm (1 : ℂ))
    change F (J (E.symm (1 : ℂ))) = (q.val ⟨x₀,E.symm (1 : ℂ)⟩).2 *
      (cs x₀)⁻¹ * (gm x₀)⁻¹ * nativeChartCofactor inc eH eX m (eH.val y₀) at h
    rw [hunit,one_mul] at h
    exact h.trans hz
  refine ⟨qp,fH,hqp₀,hfH₀,C,hC,hCne,?_⟩
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
  have hgmAlong : ContinuousAt (fun y : member p (affinePoint i ζ) => gm y.val) y₀ :=
    hgm0.comp continuous_subtype_val.continuousAt
  have hnearm : ∀ᶠ y : member p (affinePoint i ζ) in 𝓝 y₀, gm y.val ≠ 0 :=
    hgmAlong.eventually_ne (show gm y₀.val ≠ 0 from hm₀)
  filter_upwards [eH.val.open_source.mem_nhds hy₀,hnearX,hnearP,hnearL,hnearj,hnearm]
    with y hy hx hP hL hpj hm
  intro T
  have h := nativeBertiniPhysicalAdjunctionFrameCoefficient p i ζ hsm L y₀ x₀ j m y hy hx hpj hm eP hP eL hL T
  change (fH.val ⟨y,nativeBertiniPhysicalAdjunctionFiberEquiv p i ζ hsm L y T⟩).2 =
    (q.val ⟨y.val,T⟩).2 * C y
  simpa only [C,cs,gm,eX,eH,inc,fH,q,eK,mul_assoc] using h

def nativeBertiniMemberPullbackAdjunctionInverseSection :
    letI := nativeBertiniMemberChartedSpace p i ζ hsm
    letI := nativeBertiniMemberComplex p i ζ hsm
    letI := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
    HolomorphicSections (n := d) (tensor (nativeCanonicalBundle (n := d) (X := member p (affinePoint i ζ)))
      (nativeHolomorphicPullbackBundle L (nativeBertiniMemberInclusionMap p i ζ hsm))).Fiber →
    HolomorphicSections (n := d) (nativeHolomorphicPullbackBundle
      (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) (nativeBertiniHyperplaneBundle p)) L)
      (nativeBertiniMemberInclusionMap p i ζ hsm)).Fiber := by
  let := nativeBertiniMemberChartedSpace p i ζ hsm
  let := nativeBertiniMemberComplex p i ζ hsm
  let := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
  intro R
  refine {
    toFun := fun y => (nativeBertiniPhysicalAdjunctionFiberEquiv p i ζ hsm L y).symm (R y)
    contMDiff_toFun := ?_ }
  intro y₀
  obtain ⟨e,f,he,hf,C,hC,hCne,hread⟩ := exists_nativeBertiniPhysicalAdjunction_local_unit p i ζ hsm L y₀
  let := e.property
  let := f.property
  have hR := (f.val.contMDiffAt_section_iff hf).mp (R.contMDiff y₀)
  have hprod := hR.mul (hC.inv₀ hCne)
  apply (e.val.contMDiffAt_section_iff he).mpr
  apply hprod.congr_of_eventuallyEq
  filter_upwards [hread,hC.continuousAt.eventually_ne hCne] with y hread hCy
  have h := hread ((nativeBertiniPhysicalAdjunctionFiberEquiv p i ζ hsm L y).symm (R y))
  rw [LinearEquiv.apply_symm_apply] at h
  exact (eq_mul_inv_iff_mul_eq₀ hCy).mpr h.symm

theorem nativeBertiniMemberPullbackAdjunctionInverseSection_apply :
    letI := nativeBertiniMemberChartedSpace p i ζ hsm
    letI := nativeBertiniMemberComplex p i ζ hsm
    letI := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
    ∀ (R : HolomorphicSections (n := d) (tensor (nativeCanonicalBundle (n := d) (X := member p (affinePoint i ζ)))
      (nativeHolomorphicPullbackBundle L (nativeBertiniMemberInclusionMap p i ζ hsm))).Fiber)
      (y : member p (affinePoint i ζ)),
      nativeBertiniMemberPullbackAdjunctionInverseSection p i ζ hsm L R y =
        (nativeBertiniPhysicalAdjunctionFiberEquiv p i ζ hsm L y).symm (R y) := by
  intros
  rfl

def nativeBertiniMemberPullbackAdjunctionEquiv :
    letI := nativeBertiniMemberChartedSpace p i ζ hsm
    letI := nativeBertiniMemberComplex p i ζ hsm
    letI := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
    HolomorphicSections (n := d) (nativeHolomorphicPullbackBundle
      (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) (nativeBertiniHyperplaneBundle p)) L)
      (nativeBertiniMemberInclusionMap p i ζ hsm)).Fiber ≃ₗ[ℂ]
    HolomorphicSections (n := d) (tensor (nativeCanonicalBundle (n := d) (X := member p (affinePoint i ζ)))
      (nativeHolomorphicPullbackBundle L (nativeBertiniMemberInclusionMap p i ζ hsm))).Fiber := by
  let := nativeBertiniMemberChartedSpace p i ζ hsm
  let := nativeBertiniMemberComplex p i ζ hsm
  let := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
  refine {
    toFun := nativeBertiniMemberPullbackAdjunctionSection p i ζ hsm L
    invFun := nativeBertiniMemberPullbackAdjunctionInverseSection p i ζ hsm L
    map_add' := fun S T => (nativeBertiniMemberPullbackAdjunctionLinearMap p i ζ hsm L).map_add S T
    map_smul' := fun c S => (nativeBertiniMemberPullbackAdjunctionLinearMap p i ζ hsm L).map_smul c S
    left_inv := ?_
    right_inv := ?_ }
  · intro S
    ext y
    exact (nativeBertiniPhysicalAdjunctionFiberEquiv p i ζ hsm L y).symm_apply_apply (S y)
  · intro R
    ext y
    exact (nativeBertiniPhysicalAdjunctionFiberEquiv p i ζ hsm L y).apply_symm_apply (R y)

end SGPT.Trace.Bertini
