import SGPT.Trace.BertiniGlobalGeneration
import SGPT.Trace.BertiniUniversalH0Range
import SGPT.Trace.BertiniMemberPullbackAdjunctionMultiplier
import SGPT.Trace.BertiniNativeTensorLeftComm
import SGPT.Trace.BertiniPhysicalQuotientRestriction
import SGPT.Foundations.Analysis.Pending.GlobalQuasiPshKahlerBackground

/-! Genuine Step2 generators are MANUFACTURED from native Siu generation;
only clearly labelled incoming actual all-high Step1.4 H0-image equality.
No generation, section-family or stalk-inclusion certificate is assumed. -/
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
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.MultiplierSectionsDraft SGPT.Bergman.NativeKodairaPullback
open SGPT.Bergman.PolynomialH0Growth SGPT.Bergman.NativeHermitianMetric
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Toric.F1IntersectionDraft SGPT.Trace.Bertini SGPT.Trace.BertiniGlobalGeneration

private theorem baseSectionIn_nativeMultiplier {n : ℕ} {Y : Type} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    (B : HermitianHolomorphicLineBundle.{0,0} n Y) {φ : Y → EReal}
    (hφ : IsGlobalQuasiPshPotential (n := n) φ)
    (S : HolomorphicSections (n := n) B.Fiber)
    (hS : IsBaseSectionIn B (multiplierIdeal (n := n) 1 φ) S) :
    S ∈ fullHolomorphicIdealSections (n := n) B.Fiber (sourceDegreeMultiplierIdeal (n := n) 1 φ) := by
  let I := sourceDegreeMultiplierIdeal (n := n) 1 φ
  have hI : I.IsCoherent := sourceDegreeMultiplierIdeal_isCoherent 1 hφ
  have hIeq : I = multiplierIdeal (n := n) 1 φ := by
    simpa only [Nat.cast_one] using sourceDegreeMultiplierIdeal_pos (n := n) 1 one_pos φ
  change globalSectionSheafEquiv (n := n) B.Fiber S ∈ idealOpenSectionSubmodule (n := n) B.Fiber I ⊤
  intro e y hy
  apply (localFrameCoefficientGerm_mem_iff_originalCoefficient (n := n) B.Fiber I hI e S hy).mpr
  rw [hIeq]
  apply MultiplierIdealProductComparison.mem_multiplierIdeal_congr (hS.2 y.val e hy)
  filter_upwards [e.val.open_baseSet.mem_nhds hy] with z hz
  exact Trivialization.continuousLinearMapAt_apply_of_mem (R := ℂ) e.val hz _

private theorem swapLastTwice {n : ℕ} {Y : Type} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    (E F G : HermitianHolomorphicLineBundle n Y) (x : Y)
    (v : (tensor (tensor E F) G).Fiber x) :
    NativeTensorSwap.swapLastFiber E G F x (NativeTensorSwap.swapLastFiber E F G x v) = v := by
  induction v using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add,ha,hb]
  | tmul a b =>
    induction a using TensorProduct.induction_on with
    | zero => simp only [TensorProduct.zero_tmul,map_zero]
    | add u v hu hv => simp only [TensorProduct.add_tmul,map_add,hu,hv]
    | tmul u v => rfl

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (ζ : ComplexModel N)
  (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint i ζ))

private theorem physicalPullback_mem_of_step14
    (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) X)
    {φ : X → EReal} (hφ : IsGlobalQuasiPshPotential (n := d + 1) φ) :
    letI := nativeBertiniMemberChartedSpace p i ζ hsm
    letI := nativeBertiniMemberComplex p i ζ hsm
    letI := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
    (nativeBertiniPhysicalQuotientRestriction p i ζ hsm L hφ).range =
      fullHolomorphicIdealSections (n := d)
        (tensor (nativeCanonicalBundle (n := d) (X := member p (affinePoint i ζ)))
          (nativeHolomorphicPullbackBundle L (nativeBertiniMemberInclusionMap p i ζ hsm))).Fiber
        (sourceDegreeMultiplierIdeal (n := d) 1 (fun y => φ y.val)) →
    ∀ T : nativeMultiplierSections
      (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) (nativeBertiniHyperplaneBundle p)) L) φ,
      sourceNativeHolomorphicSectionPullback _ (nativeBertiniMemberInclusionMap p i ζ hsm) T.val ∈
        fullHolomorphicIdealSections (n := d) (nativeHolomorphicPullbackBundle
          (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) (nativeBertiniHyperplaneBundle p)) L)
          (nativeBertiniMemberInclusionMap p i ζ hsm)).Fiber
          (sourceDegreeMultiplierIdeal (n := d) 1 (fun y => φ y.val)) := by
  let := nativeBertiniMemberChartedSpace p i ζ hsm
  let := nativeBertiniMemberComplex p i ζ hsm
  let := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
  intro hStep14 T
  let K := nativeCanonicalBundle (n := d + 1) (X := X)
  let P := nativeBertiniHyperplaneBundle p
  let Tq := nativeMultiplierSwapLastSectionMap K P L hφ T
  let M := nativeMultiplierSectionMap (tensor K L) P hφ (nativeBertiniAffineSection p i ζ)
  have hQ : nativeBertiniPhysicalQuotientRestriction p i ζ hsm L hφ (M.range.mkQ Tq) ∈
      fullHolomorphicIdealSections (n := d)
        (tensor (nativeCanonicalBundle (n := d) (X := member p (affinePoint i ζ)))
          (nativeHolomorphicPullbackBundle L (nativeBertiniMemberInclusionMap p i ζ hsm))).Fiber
        (sourceDegreeMultiplierIdeal (n := d) 1 (fun y => φ y.val)) := by
    rw [← hStep14]
    exact ⟨M.range.mkQ Tq,rfl⟩
  rw [nativeBertiniPhysicalQuotientRestriction_mk] at hQ
  have hswap : NativeTensorSwap.swapLastSection K L P Tq.val = T.val := by
    ext x
    exact swapLastTwice K P L x (T.val x)
  rw [hswap] at hQ
  have hφres := GlobalPotentialPullback.manifoldQuasiPlurisubharmonic_comp
    (nativeBertiniMemberInclusionMap p i ζ hsm).contMDiff hφ.1
  apply (nativeBertiniMemberPullbackAdjunction_mem_originalIdeal_iff p i ζ hsm L
    (fun y => φ y.val) hφres _).mpr
  rw [nativeBertiniMemberPullbackAdjunctionSection_ambient]
  exact hQ

theorem exists_actual_multiplier_generators_restricting_intrinsic_of_step14
    (G U : HermitianHolomorphicLineBundle.{0,0} (d + 1) X)
    (hG : IsSourceSmoothHermitianMetric G) (hU : IsSourceSmoothHermitianMetric U)
    (hGpos : (sourceNativeFirstChernForm G hG).val.IsKahler)
    (φ : X → EReal) (hφ : IsGlobalQuasiPshPotential (n := d + 1) φ) (k₀ : ℕ) :
    letI := nativeBertiniMemberChartedSpace p i ζ hsm
    letI := nativeBertiniMemberComplex p i ζ hsm
    letI := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
    (∀ k : ℕ, k₀ ≤ k → let L := twistedPower G U k
      (nativeBertiniPhysicalQuotientRestriction p i ζ hsm L hφ).range =
        fullHolomorphicIdealSections (n := d)
          (tensor (nativeCanonicalBundle (n := d) (X := member p (affinePoint i ζ)))
            (nativeHolomorphicPullbackBundle L (nativeBertiniMemberInclusionMap p i ζ hsm))).Fiber
          (sourceDegreeMultiplierIdeal (n := d) 1 (fun y => φ y.val))) →
    ∃ k : ℕ, k₀ ≤ k ∧
      let V := twistedPower G
        (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) (nativeBertiniHyperplaneBundle p)) U) k
      ∃ (m : ℕ) (S : Fin m → nativeMultiplierSections V φ),
        (∀ j, sourceNativeHolomorphicSectionPullback V (nativeBertiniMemberInclusionMap p i ζ hsm) (S j).val ∈
          fullHolomorphicIdealSections (n := d) (nativeHolomorphicPullbackBundle V
            (nativeBertiniMemberInclusionMap p i ζ hsm)).Fiber
            (sourceDegreeMultiplierIdeal (n := d) 1 (fun y => φ y.val))) ∧
        ∀ (x : X) (e : AtlasFrame V), x ∈ e.val.baseSet → ∀ g : X → ℂ,
          (multiplierIdeal (n := d + 1) 1 φ).mem x g →
          IsInSpanAt (n := d + 1)
            (fun h => ∃ j, h = fun z => e.val.continuousLinearMapAt ℂ z ((S j).val z)) x g := by
  let := nativeBertiniMemberChartedSpace p i ζ hsm
  let := nativeBertiniMemberComplex p i ζ hsm
  let := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
  intro hStep14
  let A := tensor (nativeCanonicalBundle (n := d + 1) (X := X)) (nativeBertiniHyperplaneBundle p)
  have hP : IsSourceSmoothHermitianMetric (nativeBertiniHyperplaneBundle p) :=
    nativeHolomorphicPullback_smooth (sourceProjectiveHyperplaneBundle N) p
      (sourceProjectiveHyperplaneBundle_sourceSmooth N)
  have hA : IsSourceSmoothHermitianMetric A := sourceNativeTensor_smooth _ _ nativeCanonicalBundle_smooth hP
  have hT : IsSourceSmoothHermitianMetric (tensor A U) := sourceNativeTensor_smooth A U hA hU
  let omegaG : KahlerBackground (d + 1) X := ⟨sourceNativeFirstChernForm G hG,hGpos⟩
  obtain ⟨C,_hC,hCφ⟩ := GlobalQuasiPshKahlerBackground.exists_pos_isThetaPshPotential_smul omegaG hφ
  obtain ⟨a₀,_ha₀,hgen⟩ := eventually_twistedMultiplier_finite_global_generators G (tensor A U)
    hG hT hGpos (C • omegaG.form)
  let a := max k₀ a₀
  have hka : k₀ ≤ a + 1 := (le_max_left _ _).trans (Nat.le_succ _)
  have hga : a₀ ≤ a + 1 := (le_max_right _ _).trans (Nat.le_succ _)
  obtain ⟨m,S,hS,hspan⟩ := hgen (a + 1) hga φ hCφ
  let V := twistedPower G (tensor A U) (a + 1)
  have hSmem (j : Fin m) : S j ∈ fullHolomorphicIdealSections (n := d + 1) V.Fiber
      (sourceDegreeMultiplierIdeal (n := d + 1) 1 φ) := baseSectionIn_nativeMultiplier V hφ (S j) (hS j)
  let Sn : Fin m → nativeMultiplierSections V φ := fun j => ⟨S j,hSmem j⟩
  refine ⟨a + 1,hka,m,Sn,?_,?_⟩
  · intro j
    let L := twistedPower G U (a + 1)
    let ι := nativeBertiniMemberInclusionMap p i ζ hsm
    let Tp := nativeTensorLeftCommSection (positivePower G a) A U (Sn j).val
    have hTp := nativeTensorLeftCommSection_mem_originalIdeal (positivePower G a) A U hφ.1 (Sn j).val (Sn j).property
    have hpull := physicalPullback_mem_of_step14 p i ζ hsm L hφ (hStep14 (a + 1) hka) ⟨Tp,hTp⟩
    let Rp := sourceNativeHolomorphicSectionPullback (tensor A L) ι Tp
    have hφres := GlobalPotentialPullback.manifoldQuasiPlurisubharmonic_comp ι.contMDiff hφ.1
    have hback := nativeTensorLeftCommPullbackSection_mem_originalIdeal A (positivePower G a) U ι
      hφres Rp hpull
    have hbackeq : nativeTensorLeftCommPullbackSection A (positivePower G a) U ι Rp =
        sourceNativeHolomorphicSectionPullback V ι (Sn j).val := by
      ext y
      exact nativeTensorLeftCommFiber_roundtrip (positivePower G a) A U y.val ((Sn j).val y.val)
    rw [hbackeq] at hback
    exact hback
  · exact hspan

end SGPT.Trace.BertiniUniversal
