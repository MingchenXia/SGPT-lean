import SGPT.Trace.BertiniFixedMemberGlobalLift
import SGPT.Trace.BertiniHodgeRawZeroDimensional
import SGPT.Trace.NativeTensorPullbackSectionRestriction

/-! The ENTIRE actual native pulled-back-bundle I(phi|W) H0 lifts into actual
global I(phi) after a FIXED-member threshold. No reverse ideal containment. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.Bertini
open Bundle Set Filter TensorProduct MeasureTheory
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace
open SGPT.Foundations.Analysis.Pending.HironakaSmoothCentreRealDomainActualIdealPresheaf
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Toric.F1IntersectionDraft
open SGPT.Bergman.PolynomialH0Growth SGPT.Bergman.NativeHermitianMetric
open SGPT.Bergman.MultiplierSectionsDraft SGPT.Bergman.NativeKodairaPullback
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Trace.TwistedL2

section Dictionary
variable {n m : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {W : Set X} [ChartedSpace (ComplexModel m) W] [IsComplexManifold m W]

theorem nativeRestrictedMultiplierSection_isAlong
    (B : HermitianHolomorphicLineBundle.{0,0} n X)
    (hι : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ (Subtype.val : W → X))
    (φ : X → EReal) (hφ : ManifoldQuasiPlurisubharmonic (n := n) φ)
    (S : nativeMultiplierSections
      (nativeHolomorphicPullbackBundle B
        (⟨Subtype.val,hι⟩ : ContMDiffMap 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) W X ∞))
      (fun y : W => φ y.val)) :
    IsAlongMultiplierSection B.Fiber (m := m) 1 (fun y : W => φ y.val) (fun y => S.val y) := by
  let f : ContMDiffMap 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) W X ∞ := ⟨Subtype.val,hι⟩
  let E := nativeHolomorphicPullbackBundle B f
  let I := sourceDegreeMultiplierIdeal (n := m) 1 (fun y : W => φ y.val)
  have hIeq : I = multiplierIdeal (n := m) 1 (fun y : W => φ y.val) := by
    simpa only [I,Nat.cast_one] using
      (sourceDegreeMultiplierIdeal_pos (n := m) 1 one_pos (fun y : W => φ y.val))
  have hI : I.IsCoherent := by
    rw [hIeq]
    exact raw_qpsh_multiplier_isCoherent_allDimensions
      (GlobalPotentialPullback.manifoldQuasiPlurisubharmonic_comp hι hφ) one_pos
  intro y
  let e : AtlasFrame B := ⟨trivializationAt ℂ B.Fiber y.val,inferInstance⟩
  let q := NativeTensorRestriction.pullbackFrame B f e
  have hq : y ∈ q.val.baseSet := mem_baseSet_trivializationAt ℂ _ _
  have hS := S.property
  change globalSectionSheafEquiv (n := m) E.Fiber S.val ∈ idealOpenSectionSubmodule (n := m) E.Fiber I ⊤ at hS
  have hcoeff := (localFrameCoefficientGerm_mem_iff_originalCoefficient (n := m) E.Fiber I hI q S.val hq).mp
    (hS q ⟨y,mem_univ y⟩ hq)
  rw [hIeq] at hcoeff
  change (multiplierIdeal (n := m) 1 (fun y : W => φ y.val)).mem y
    (alongCoefficient B.Fiber e.val (fun z => S.val z)) at hcoeff
  simpa only [EReal.coe_one,one_mul] using hcoeff
end Dictionary

variable {n m : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

theorem exists_fixed_member_eventual_full_native_multiplier_lift
    (G T : HermitianHolomorphicLineBundle.{0,0} n X)
    (hG : IsSourceSmoothHermitianMetric G) (hT : IsSourceSmoothHermitianMetric T)
    (hGpos : (sourceNativeFirstChernForm G hG).val.IsKahler)
    (φ : X → EReal) (hφ : IsGlobalQuasiPshPotential (n := n) φ)
    {W : Set X} (hW : IsClosedConnectedSubmanifold n W m)
    (hφW : ∃ y ∈ W, φ y ≠ ⊥) :
    let hk := le_of_isClosedConnectedSubmanifold hW
    letI := chartedSpace hk hW.2.2
    letI := isComplexManifold_chartedSpace hk hW.2.2
    let ι : ContMDiffMap 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) W X ∞ :=
      ⟨Subtype.val,contMDiff_val hk hW.2.2⟩
    ∃ k₀ : ℕ, 0 < k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      ∀ σ : nativeMultiplierSections (nativeHolomorphicPullbackBundle (twistedPower G T k) ι)
        (fun y : W => φ y.val),
      ∃ s : nativeMultiplierSections (twistedPower G T k) φ,
        sourceNativeHolomorphicSectionPullback (twistedPower G T k) ι s.val = σ.val := by
  let hk := le_of_isClosedConnectedSubmanifold hW
  let := chartedSpace hk hW.2.2
  let := isComplexManifold_chartedSpace hk hW.2.2
  let ι : ContMDiffMap 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) W X ∞ :=
    ⟨Subtype.val,contMDiff_val hk hW.2.2⟩
  obtain ⟨k₀,hk₀,hall⟩ := exists_fixed_member_eventual_original_multiplier_lift G T hG hT hGpos φ hφ hW hφW
  refine ⟨k₀,hk₀,?_⟩
  intro k hkk₀ σ
  have hσ := nativeRestrictedMultiplierSection_isAlong (twistedPower G T k)
    (contMDiff_val hk hW.2.2) φ hφ.1 σ
  obtain ⟨s,hseq⟩ := hall k hkk₀ (fun y => σ.val y) hσ
  refine ⟨s,?_⟩
  ext y
  exact hseq y

end SGPT.Trace.Bertini
