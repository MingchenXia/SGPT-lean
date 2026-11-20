import SGPT.Trace.BertiniNativeTensorLeftComm
import SGPT.Trace.BertiniFixedNativeMemberLift
import SGPT.Trace.BertiniFamilyCanonicalModel

/-! ONE FIXED original smooth connected member: EVERY genuine intrinsic
canonical multiplier section eventually has an actual global multiplier
lift with exact SAME native physical adjunction value. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.Bertini
open Bundle Set Filter TensorProduct
open scoped Manifold ContDiff Topology TensorProduct
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.MultiplierSectionsDraft SGPT.Bergman.NativeKodairaPullback
open SGPT.Bergman.PolynomialH0Growth SGPT.Bergman.NativeHermitianMetric
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Toric.F1IntersectionDraft

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (ζ : ComplexModel N)
  (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint i ζ))

theorem exists_fixed_member_eventual_intrinsic_canonical_multiplier_lift
    (G E : HermitianHolomorphicLineBundle.{0,0} (d + 1) X)
    (hG : IsSourceSmoothHermitianMetric G) (hE : IsSourceSmoothHermitianMetric E)
    (hGpos : (sourceNativeFirstChernForm G hG).val.IsKahler)
    (φ : X → EReal) (hφ : IsGlobalQuasiPshPotential (n := d + 1) φ)
    (hconn : IsConnected (member p (affinePoint i ζ)))
    (hφY : ∃ x ∈ member p (affinePoint i ζ), φ x ≠ ⊥) :
    letI := nativeBertiniMemberChartedSpace p i ζ hsm
    letI := nativeBertiniMemberComplex p i ζ hsm
    letI := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
    ∃ k₀ : ℕ, 0 < k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      let L := twistedPower G E k
      ∀ R : nativeMultiplierSections
        (tensor (nativeCanonicalBundle (n := d) (X := member p (affinePoint i ζ)))
          (nativeHolomorphicPullbackBundle L (nativeBertiniMemberInclusionMap p i ζ hsm)))
        (fun y => φ y.val),
      ∃ T : nativeMultiplierSections
        (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) (nativeBertiniHyperplaneBundle p)) L) φ,
        nativeBertiniPhysicalAdjunctionSection p i ζ hsm L T.val = R.val := by
  let := nativeBertiniMemberChartedSpace p i ζ hsm
  let := nativeBertiniMemberComplex p i ζ hsm
  let := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
  let A := tensor (nativeCanonicalBundle (n := d + 1) (X := X)) (nativeBertiniHyperplaneBundle p)
  have hP : IsSourceSmoothHermitianMetric (nativeBertiniHyperplaneBundle p) :=
    nativeHolomorphicPullback_smooth (sourceProjectiveHyperplaneBundle N) p
      (sourceProjectiveHyperplaneBundle_sourceSmooth N)
  have hA : IsSourceSmoothHermitianMetric A := sourceNativeTensor_smooth _ _ nativeCanonicalBundle_smooth hP
  have hT : IsSourceSmoothHermitianMetric (tensor A E) := sourceNativeTensor_smooth A E hA hE
  have hW : IsClosedConnectedSubmanifold (d + 1) (member p (affinePoint i ζ)) d :=
    ⟨isClosed_member p p.contMDiff.continuous (affinePoint i ζ),hconn,nativeBertiniMemberRegularity p i ζ hsm⟩
  obtain ⟨k₀,hk₀,hall⟩ := exists_fixed_member_eventual_full_native_multiplier_lift G (tensor A E)
    hG hT hGpos φ hφ hW hφY
  refine ⟨k₀,hk₀,?_⟩
  intro k hkk₀
  dsimp only
  intro R
  cases k with
  | zero => omega
  | succ j =>
    let L := twistedPower G E (j + 1)
    let ι := nativeBertiniMemberInclusionMap p i ζ hsm
    have hφres : ManifoldQuasiPlurisubharmonic (n := d) (fun y : member p (affinePoint i ζ) => φ y.val) :=
      GlobalPotentialPullback.manifoldQuasiPlurisubharmonic_comp ι.contMDiff hφ.1
    let J := nativeBertiniMemberMultiplierAdjunctionEquiv p i ζ hsm L (fun y => φ y.val) hφres
    let Rinv := J.symm R
    let Q := nativeTensorLeftCommPullbackSection A (positivePower G j) E ι Rinv.val
    have hQ := nativeTensorLeftCommPullbackSection_mem_originalIdeal A (positivePower G j) E ι hφres
      Rinv.val Rinv.property
    let σ : nativeMultiplierSections (nativeHolomorphicPullbackBundle (twistedPower G (tensor A E) (j + 1)) ι)
        (fun y => φ y.val) := ⟨Q,hQ⟩
    obtain ⟨s,hs⟩ := hall (j + 1) hkk₀ σ
    let T := nativeTensorLeftCommSection (positivePower G j) A E s.val
    have hTmem := nativeTensorLeftCommSection_mem_originalIdeal (positivePower G j) A E hφ.1 s.val s.property
    refine ⟨⟨T,hTmem⟩,?_⟩
    have hJ : nativeBertiniMemberPullbackAdjunctionSection p i ζ hsm L Rinv.val = R.val := by
      change (J (J.symm R)).val = R.val
      exact congrArg Subtype.val (J.apply_symm_apply R)
    ext y
    have hsy := congrArg (fun H => H y) hs
    have hval : T y.val = Rinv.val y := by
      change nativeTensorLeftCommFiber (positivePower G j) A E y.val (s.val y.val) = Rinv.val y
      change s.val y.val = Q y at hsy
      rw [hsy]
      exact nativeTensorLeftCommFiber_roundtrip A (positivePower G j) E y.val (Rinv.val y)
    change nativeBertiniPhysicalAdjunctionFiberEquiv p i ζ hsm L y (T y.val) = R.val y
    rw [hval]
    exact congrArg (fun H => H y) hJ

end SGPT.Trace.Bertini
