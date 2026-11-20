import SGPT.Trace.BertiniUniversalAuxiliaryLift
import SGPT.Trace.BertiniNativeMemberNormalPole
import SGPT.Trace.BertiniFixedIntrinsicMemberLift
import SGPT.Trace.BertiniHodgeRawZeroDimensional

/-! ONE original physical canonical multiplier lifting threshold before
ALL smooth members and ALL semipositive twists. No member connectedness,
nonempty member or restricted nonpole point is required. -/
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniUniversal
open Bundle Set Filter TensorProduct
open scoped Manifold ContDiff Topology ENNReal TensorProduct
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.MultiplierSectionsDraft SGPT.Bergman.NativeKodairaPullback
open SGPT.Bergman.PolynomialH0Growth SGPT.Bergman.NativeHermitianMetric
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Toric.F1IntersectionDraft
open SGPT.Trace.Bertini
variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)

theorem exists_uniform_original_intrinsic_canonical_multiplier_lift
    (G : HermitianHolomorphicLineBundle.{0,0} (d + 1) X)
    (hG : IsSourceSmoothHermitianMetric G)
    (hGpos : (sourceNativeFirstChernForm G hG).val.IsKahler)
    (φ : X → EReal) (hφ : IsGlobalQuasiPshPotential (n := d + 1) φ) :
    ∃ k₀ : ℕ, 0 < k₀ ∧ ∀ (U : HermitianHolomorphicLineBundle.{0,0} (d + 1) X)
      (hU : IsSourceSmoothHermitianMetric U), (sourceNativeFirstChernForm U hU).val.IsSemipositive →
      ∀ k : ℕ, k₀ ≤ k → ∀ (i : Fin (N + 1)) (ζ : ComplexModel N)
        (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint i ζ)),
      letI := nativeBertiniMemberChartedSpace p i ζ hsm
      letI := nativeBertiniMemberComplex p i ζ hsm
      letI := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
      let L := twistedPower G U k
      ∀ R : nativeMultiplierSections
        (tensor (nativeCanonicalBundle (n := d) (X := member p (affinePoint i ζ)))
          (nativeHolomorphicPullbackBundle L (nativeBertiniMemberInclusionMap p i ζ hsm)))
        (fun y => φ y.val),
      ∃ T : nativeMultiplierSections
        (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) (nativeBertiniHyperplaneBundle p)) L) φ,
        nativeBertiniPhysicalAdjunctionSection p i ζ hsm L T.val = R.val := by
  let A := tensor (nativeCanonicalBundle (n := d + 1) (X := X)) (nativeBertiniHyperplaneBundle p)
  have hP : IsSourceSmoothHermitianMetric (nativeBertiniHyperplaneBundle p) :=
    nativeHolomorphicPullback_smooth (sourceProjectiveHyperplaneBundle N) p
      (sourceProjectiveHyperplaneBundle_sourceSmooth N)
  have hA : IsSourceSmoothHermitianMetric A := sourceNativeTensor_smooth _ _ nativeCanonicalBundle_smooth hP
  let ωG : KahlerBackground (d + 1) X := ⟨sourceNativeFirstChernForm G hG,hGpos⟩
  obtain ⟨b,hb,hPole⟩ := SGPT.Trace.BertiniNativeSectionPole.exists_uniform_nativeBertini_isGlobalNormalPole p ωG
  obtain ⟨k₀,hk₀,hall⟩ := exists_uniform_auxiliary_regular_native_multiplier_lift
    G A hG hA hGpos φ hφ b hb d (Nat.lt_succ_self d)
  refine ⟨k₀,hk₀,?_⟩
  intro U hU hUpos k hkk₀ i ζ hsm
  let := nativeBertiniMemberChartedSpace p i ζ hsm
  let := nativeBertiniMemberComplex p i ζ hsm
  let := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
  dsimp only
  intro R
  cases k with
  | zero => omega
  | succ j =>
    let L := twistedPower G U (j + 1)
    let ι := nativeBertiniMemberInclusionMap p i ζ hsm
    have hφres : ManifoldQuasiPlurisubharmonic (n := d) (fun y : member p (affinePoint i ζ) => φ y.val) :=
      GlobalPotentialPullback.manifoldQuasiPlurisubharmonic_comp ι.contMDiff hφ.1
    let J := nativeBertiniMemberMultiplierAdjunctionEquiv p i ζ hsm L (fun y => φ y.val) hφres
    let Rinv := J.symm R
    let Q := nativeTensorLeftCommPullbackSection A (positivePower G j) U ι Rinv.val
    have hQ := nativeTensorLeftCommPullbackSection_mem_originalIdeal A (positivePower G j) U ι hφres
      Rinv.val Rinv.property
    let σ : nativeMultiplierSections (nativeHolomorphicPullbackBundle (twistedPower G (tensor A U) (j + 1)) ι)
        (fun y => φ y.val) := ⟨Q,hQ⟩
    have hclosed := isClosed_member p p.contMDiff.continuous (affinePoint i ζ)
    have hreg := nativeBertiniMemberRegularity p i ζ hsm
    have hR := hPole i ζ hsm
    obtain ⟨s,hs⟩ := hall U hU hUpos (j + 1) hkk₀ (member p (affinePoint i ζ)) hclosed hreg
      (SGPT.Trace.BertiniNativeSectionPole.poleWeight (nativeBertiniHyperplaneBundle p)
        (nativeBertiniAffineSection p i ζ)) hR.1 hR.2.2 σ
    let T := nativeTensorLeftCommSection (positivePower G j) A U s.val
    have hTmem := nativeTensorLeftCommSection_mem_originalIdeal (positivePower G j) A U hφ.1 s.val s.property
    refine ⟨⟨T,hTmem⟩,?_⟩
    have hJ : nativeBertiniMemberPullbackAdjunctionSection p i ζ hsm L Rinv.val = R.val := by
      change (J (J.symm R)).val = R.val
      exact congrArg Subtype.val (J.apply_symm_apply R)
    ext y
    have hsy := congrArg (fun H => H y) hs
    have hval : T y.val = Rinv.val y := by
      change nativeTensorLeftCommFiber (positivePower G j) A U y.val (s.val y.val) = Rinv.val y
      change s.val y.val = Q y at hsy
      rw [hsy]
      exact nativeTensorLeftCommFiber_roundtrip A (positivePower G j) U y.val (Rinv.val y)
    change nativeBertiniPhysicalAdjunctionFiberEquiv p i ζ hsm L y (T y.val) = R.val y
    rw [hval]
    exact congrArg (fun H => H y) hJ

theorem exists_uniform_original_finiteHodge_canonical_lift
    (G : HermitianHolomorphicLineBundle.{0,0} (d + 1) X)
    (hG : IsSourceSmoothHermitianMetric G)
    (hGpos : (sourceNativeFirstChernForm G hG).val.IsKahler)
    (φ : X → EReal) (hφ : IsGlobalQuasiPshPotential (n := d + 1) φ) :
    ∃ k₀ : ℕ, 0 < k₀ ∧ ∀ (U : HermitianHolomorphicLineBundle.{0,0} (d + 1) X)
      (hU : IsSourceSmoothHermitianMetric U), (sourceNativeFirstChernForm U hU).val.IsSemipositive →
      ∀ k : ℕ, k₀ ≤ k → ∀ (i : Fin (N + 1)) (ζ : ComplexModel N)
        (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint i ζ)),
      letI := nativeBertiniMemberChartedSpace p i ζ hsm
      letI := nativeBertiniMemberComplex p i ζ hsm
      letI := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
      let L := twistedPower G U k
      ∀ R : HolomorphicSections (n := d)
        (tensor (nativeCanonicalBundle (n := d) (X := member p (affinePoint i ζ)))
          (nativeHolomorphicPullbackBundle L (nativeBertiniMemberInclusionMap p i ζ hsm))).Fiber,
      nativeBertiniMemberHodgeEnergy p i ζ hsm L φ R < ⊤ →
      ∃ T : nativeMultiplierSections
        (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) (nativeBertiniHyperplaneBundle p)) L) φ,
        nativeBertiniPhysicalAdjunctionSection p i ζ hsm L T.val = R := by
  obtain ⟨k₀,hk₀,hLift⟩ := exists_uniform_original_intrinsic_canonical_multiplier_lift p G hG hGpos φ hφ
  refine ⟨k₀,hk₀,?_⟩
  intro U hU hUpos k hk i ζ hsm
  let := nativeBertiniMemberChartedSpace p i ζ hsm
  let := nativeBertiniMemberComplex p i ζ hsm
  let := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
  intro L R hR
  have hmem := (nativeBertiniMemberHodgeEnergy_finite_iff_full_originalIdeal_allDimensions p i ζ hsm L hφ.1 R).mpr hR
  exact hLift U hU hUpos k hk i ζ hsm ⟨R,hmem⟩

end SGPT.Trace.BertiniUniversal
