import SGPT.Okounkov.SchemeLineBundleMetricGeometry
import SGPT.Okounkov.SchemeSectionAnalyticDivisor
import SGPT.Okounkov.NativeFlagGermCartier
import SGPT.Foundations.Analysis.Pending.FactorizedWeightPsh
import SGPT.Foundations.Analysis.Pending.ExceptionalMetricProof
import SGPT.Foundations.Analysis.Pending.DivisorMetric
import SGPT.Foundations.Analysis.Pending.IdealWeightComparison
import SGPT.Foundations.Analysis.Pending.MultiplierIdeals
import SGPT.Foundations.Analysis.Pending.RestrictedApproximantComparison
import SGPT.Foundations.Analysis.Pending.NaturalThetaPshClosedCurrent
import SGPT.Foundations.Analysis.Pending.StepFourNoComponentContainsW

/-! # Genuine weights of the same original sections under one fixed metric

The complete mathematical route is `scheme-section-weight.tex`.
Original coefficient germs manufacture noncollapse; every degree uses the
same H and its actual tensor powers. Global Poincare--Lelong and integral
first-Chern-class comparisons remain separate.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.Okounkov

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open scoped Topology Manifold ContDiff ENNReal

variable {X : Scheme} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)

local instance : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance [IsSeparated f] [QuasiCompact f] : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

private def weightCoefficient {L : X.Modules} {U : X.Opens}
    (α : LocalBundleFrame L U) (k : ℕ) (s : bundlePowerGlobalSections L k) : Γ(X, U) :=
  (α.tensorPower k).coefficients (𝟙 U)
    ((bundleTensorPower L k).val.map (homOfLE le_top).op s)

private def weightFunction {L : X.Modules} {U : X.Opens}
    (α : LocalBundleFrame L U) (k : ℕ) (s : bundlePowerGlobalSections L k) :
    SchemeComplexPoint f → ℂ :=
  schemeOpenRegularFunction f n E U (weightCoefficient α k s)

namespace SchemeLineBundleMetric

variable {f n E} {L : X.Modules} (H : SchemeLineBundleMetric f n E L)

/-- The same original coefficient and fixed frame weight give atlas-independent norms. -/
theorem sectionNormSq_atlas_independent (a b : LineBundleAtlas L) (k : ℕ)
    (s : bundlePowerGlobalSections L k) : H.sectionNormSq a k s = H.sectionNormSq b k s := by
  funext p
  let α := schemePointFrame f p a
  have hp := schemePointFrame_mem f p a
  rw [H.sectionNormSq_frame a α k s p hp, H.sectionNormSq_frame b α k s p hp]

/-- Whole extended section logarithms retain exact original atlas independence. -/
theorem sectionLogNormSq_atlas_independent (a b : LineBundleAtlas L) (k : ℕ)
    (s : bundlePowerGlobalSections L k) : H.sectionLogNormSq a k s = H.sectionLogNormSq b k s := by
  unfold sectionLogNormSq
  rw [H.sectionNormSq_atlas_independent a b k s]

section Integral

variable [IsIntegral X]

/-- Actual integral-scheme faithfulness gives a nonzero norm in every nonempty open. -/
theorem exists_sectionNormSq_ne_zero_of_isOpen (a : LineBundleAtlas L) (k : ℕ)
    (s : bundlePowerGlobalSections L k) (hs : s ≠ 0)
    (W : Set (SchemeComplexPoint f)) (hW : IsOpen W) (hne : W.Nonempty) :
    ∃ q ∈ W, H.sectionNormSq a k s q ≠ 0 := by
  let := E.isSeparated
  let := E.quasiCompact
  obtain ⟨p, hpW⟩ := hne
  let U := schemePointFrameOpen f p a
  let α := schemePointFrame f p a
  let g := weightFunction f n E α k s
  have hpU : schemeComplexPointImage f p ∈ U := schemePointFrame_mem f p a
  have hU : IsOpen (schemeComplexPointImage f ⁻¹' U) :=
    U.isOpen.preimage (schemeComplexPointImage_continuous f)
  have hg : HolomorphicAt n g p := schemeOpenRegularFunction_holomorphicAt f n E U _ p hpU
  have hread : NativeHolGerm.mk g hg = schemePointPowerSectionNativeGerm f n p a k s := by
    dsimp only [g, weightFunction]
    rw [schemeOpenRegularFunction_germ]
    rfl
  by_contra! hzero
  have heq : g =ᶠ[𝓝 p] 0 := by
    filter_upwards [hW.mem_nhds hpW, hU.mem_nhds hpU] with q hqW hqU
    have hq := hzero q hqW
    rw [H.sectionNormSq_frame a α k s q hqU] at hq
    change g q = 0
    by_contra hgq
    exact (ne_of_gt (mul_pos (Complex.normSq_pos.mpr hgq)
      (pow_pos (H.positive α q hqU) k))) hq
  apply schemePointPowerSectionNativeGerm_ne_zero f n p a k s hs
  rw [← hread]
  apply Subtype.ext
  exact Germ.coe_eq.mpr heq

/-- The actual fixed-metric norm has a manufactured native factorization. -/
def sectionWeightFactorization (a : LineBundleAtlas L) (k : ℕ)
    (s : bundlePowerGlobalSections L k) (hs : s ≠ 0) :
    letI := E.isSeparated
    letI := E.quasiCompact
    FactorizedWeightForm.WeightFactorization n (H.sectionNormSq a k s) := by
  let := E.isSeparated
  let := E.quasiCompact
  exact {
    domain := fun p => schemeComplexPointImage f ⁻¹' schemePointFrameOpen f p a
    isOpen_domain := fun p => (schemePointFrameOpen f p a).isOpen.preimage
      (schemeComplexPointImage_continuous f)
    mem_domain := fun p => schemePointFrame_mem f p a
    gen := fun p => weightFunction f n E (schemePointFrame f p a) k s
    smoothPart := fun p q => H.frameNormSq (schemePointFrame f p a) q ^ k
    gen_mdifferentiable := fun p q hq =>
      (schemeOpenRegularFunction_holomorphicAt f n E _ _ q hq).mdifferentiableAt
    smooth := fun p e => (H.smooth (schemePointFrame f p a) e).pow k
    pos := fun p q hq => pow_pos (H.positive (schemePointFrame f p a) q hq) k
    factor := fun p q hq => H.sectionNormSq_frame a (schemePointFrame f p a) k s q hq
    nowhereZero := H.exists_sectionNormSq_ne_zero_of_isOpen a k s hs }

/-- The actual glued factorization form has exactly the fixed structural curvature. -/
theorem sectionWeightFactorization_curvature (a : LineBundleAtlas L) (k : ℕ)
    (s : bundlePowerGlobalSections L k) (hs : s ≠ 0) :
    letI := E.isSeparated
    letI := E.quasiCompact
    (-(H.sectionWeightFactorization a k s hs).closedForm).val.GeometricallyEq
      ((k : ℝ) • H.curvature a).val := by
  let := E.isSeparated
  let := E.quasiCompact
  intro e z hz
  let p := e.val.symm z
  let U := schemePointFrameOpen f p a
  let α := schemePointFrame f p a
  have hp : schemeComplexPointImage f p ∈ U := schemePointFrame_mem f p a
  let S := e.val.target ∩ e.val.symm ⁻¹' (schemeComplexPointImage f ⁻¹' U)
  have hS : IsOpen S := e.val.isOpen_inter_preimage_symm
    (U.isOpen.preimage (schemeComplexPointImage_continuous f))
  have hzS : z ∈ S := ⟨hz, hp⟩
  have hlog : ContDiffOn ℝ ∞ (fun u => Real.log (H.frameNormSq α (e.val.symm u))) S :=
    (H.smooth α e).log (fun u hu => (H.positive α _ hu.2).ne')
  have hfun : (fun u => Real.log (H.frameNormSq α (e.val.symm u) ^ k)) =
      fun u => (k : ℝ) • Real.log (H.frameNormSq α (e.val.symm u)) := by
    funext u
    exact Real.log_pow _ _
  rw [ClosedRealOneOneForm.coeff_neg,
    ((H.sectionWeightFactorization a k s hs).closedForm_coeff_eventuallyEq p e hz hp).self_of_nhds,
    ClosedRealOneOneForm.coeff_smul, H.curvature_coeff_frame a α e hz hp]
  change -(smoothDDC (fun u => Real.log (H.frameNormSq α (e.val.symm u) ^ k)) z) = _
  rw [hfun, smoothDDC_smul hS hlog (k : ℝ) hzS,
    smoothDDC_neg hS hlog hzS]
  simp

/-- Genuine local nondegeneracy is produced from the actual nonzero section. -/
theorem sectionLogNormSq_locallyNondegenerate (a : LineBundleAtlas L) (k : ℕ)
    (s : bundlePowerGlobalSections L k) (hs : s ≠ 0) :
    letI := E.isSeparated
    letI := E.quasiCompact
    LocallyNondegenerate (H.sectionLogNormSq a k s) := by
  let := E.isSeparated
  let := E.quasiCompact
  intro p W hW hp
  obtain ⟨q, hq, hnq⟩ := H.exists_sectionNormSq_ne_zero_of_isOpen a k s hs W hW ⟨p, hp⟩
  refine ⟨q, hq, ?_⟩
  have hpos : 0 < H.sectionNormSq a k s q :=
    lt_of_le_of_ne (H.sectionNormSq_nonneg a k s q) (Ne.symm hnq)
  rw [sectionLogNormSq, ENNReal.log_ofReal_of_pos hpos]
  exact EReal.coe_ne_bot _

/-- Full genuine kΘ-PSH of the same fixed-metric section weight, in all degrees. -/
theorem isThetaPshPotential_sectionLogNormSq (a : LineBundleAtlas L) (k : ℕ)
    (s : bundlePowerGlobalSections L k) (hs : s ≠ 0) :
    letI := E.isSeparated
    letI := E.quasiCompact
    IsThetaPshPotential ((k : ℝ) • H.curvature a).val (H.sectionLogNormSq a k s) := by
  let := E.isSeparated
  let := E.quasiCompact
  let F := H.sectionWeightFactorization a k s hs
  have hraw : ThetaPlurisubharmonic (-F.closedForm).val (H.sectionLogNormSq a k s) := by
    change ThetaPlurisubharmonic (-F.closedForm).val (fun p => ENNReal.log (ENNReal.ofReal (H.sectionNormSq a k s p)))
    simpa only [one_smul, EReal.coe_one, one_mul, FactorizedWeightPsh.logWeight,
      SchemeLineBundleMetric.sectionLogNormSq] using FactorizedWeightPsh.thetaPlurisubharmonic_logWeight F (c := 1) zero_lt_one
  exact ((H.sectionWeightFactorization_curvature a k s hs).thetaPshPotential_iff _).mp
    ⟨hraw, H.sectionLogNormSq_locallyNondegenerate a k s hs⟩

/-- Normalization is asserted only in positive degree; the raw theorem retains k=0. -/
theorem isThetaPshPotential_normalized_sectionLogNormSq (a : LineBundleAtlas L) (k : ℕ)
    (hk : 0 < k) (s : bundlePowerGlobalSections L k) (hs : s ≠ 0) :
    letI := E.isSeparated
    letI := E.quasiCompact
    IsThetaPshPotential (H.curvature a).val
      (fun p => (((k : ℝ)⁻¹ : ℝ) : EReal) * H.sectionLogNormSq a k s p) := by
  let := E.isSeparated
  let := E.quasiCompact
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have h := RestrictedApproximantComparison.isThetaPshPotential_smul
    (H.isThetaPshPotential_sectionLogNormSq a k s hs) (inv_pos.mpr hkR)
  simpa only [smul_smul, inv_mul_cancel₀ hkR.ne', one_smul] using h

/-- The existing native divisor constructor uses the SAME fixed H-norm. -/
def sectionMeteredDivisor (a : LineBundleAtlas L) (k : ℕ)
    (s : bundlePowerGlobalSections L k) (hs : s ≠ 0) :
    letI := E.isSeparated
    letI := E.quasiCompact
    MeteredEffectiveQDivisor n (SchemeComplexPoint f) := by
  let := E.isSeparated
  let := E.quasiCompact
  exact ExceptionalMetricProof.ofWeightFactorization (H.sectionWeightFactorization a k s hs) 1 one_pos

/-- Its entire extended weight is the actual original section logarithm. -/
theorem sectionMeteredDivisor_weight (a : LineBundleAtlas L) (k : ℕ)
    (s : bundlePowerGlobalSections L k) (hs : s ≠ 0) :
    letI := E.isSeparated
    letI := E.quasiCompact
    (H.sectionMeteredDivisor a k s hs).weight = H.sectionLogNormSq a k s := by
  let := E.isSeparated
  let := E.quasiCompact
  simp only [sectionMeteredDivisor, ExceptionalMetricProof.ofWeightFactorization,
    Rat.cast_one, EReal.coe_one, one_mul, FactorizedWeightPsh.logWeight]
  rfl

/-- Its actual curvature is the same kΘ on every original chart target. -/
theorem sectionMeteredDivisor_curvature (a : LineBundleAtlas L) (k : ℕ)
    (s : bundlePowerGlobalSections L k) (hs : s ≠ 0) :
    letI := E.isSeparated
    letI := E.quasiCompact
    (H.sectionMeteredDivisor a k s hs).curvature.val.GeometricallyEq
      ((k : ℝ) • H.curvature a).val := by
  let := E.isSeparated
  let := E.quasiCompact
  simpa only [sectionMeteredDivisor, ExceptionalMetricProof.ofWeightFactorization,
    Rat.cast_one, neg_one_smul] using H.sectionWeightFactorization_curvature a k s hs

/-- The same original coefficients identify the WHOLE actual section divisor ideal. -/
theorem sectionMeteredDivisor_isDivisorMetric (a : LineBundleAtlas L) (k : ℕ)
    (s : bundlePowerGlobalSections L k) (hs : s ≠ 0) :
    letI := E.isSeparated
    letI := E.quasiCompact
    DivisorMetric.IsDivisorMetric (schemeSectionAnalyticDivisor f n E a k s hs)
      (H.sectionMeteredDivisor a k s hs) := by
  let := E.isSeparated
  let := E.quasiCompact
  intro p
  let U := schemePointFrameOpen f p a
  let α := schemePointFrame f p a
  let V := schemeComplexPointImage f ⁻¹' U
  let g := weightFunction f n E α k s
  have hV : IsOpen V := U.isOpen.preimage (schemeComplexPointImage_continuous f)
  have hp : p ∈ V := schemePointFrame_mem f p a
  have hg (q : SchemeComplexPoint f) (hq : q ∈ V) : HolomorphicAt n g q :=
    schemeOpenRegularFunction_holomorphicAt f n E U _ q hq
  refine ⟨V, hV, hp, g, schemeOpenRegularFunction_mdifferentiableOn f n E U _, ?_,
    fun q => (k : ℝ) * Real.log (H.frameNormSq α q), ?_, ?_⟩
  · intro q hq h
    rw [schemeSectionAnalyticDivisor_ideal, schemeSectionAnalyticIdeal_mem_frame f n E a k s q α hq]
    have heq : NativeHolGerm.mk g (hg q hq) = schemeFramePowerSectionNativeGerm f n q α hq k s := by
      dsimp only [g, weightFunction]
      rw [schemeOpenRegularFunction_germ]
      rfl
    rw [← heq]
    constructor
    · rintro ⟨hh, hmem⟩
      exact (NativeHolGerm.mem_span_singleton_mk_iff h g hh (hg q hq)).mp hmem
    · intro hmem
      exact ⟨hmem.1, (NativeHolGerm.mem_span_singleton_mk_iff h g hmem.1 (hg q hq)).mpr hmem⟩
  · intro e
    exact ((H.smooth α e).log (fun u hu => (H.positive α _ hu.2).ne')).const_smul (k : ℝ)
  · intro q hq
    rw [H.sectionMeteredDivisor_weight a k s hs, H.sectionLogNormSq_frame a α k s q hq]
    congr 1
    simp [generatorLog_eq_log_sum, SGPT.Foundations.Analysis.logNormSq, g,
      weightFunction, weightCoefficient]

/-- Actual divisor metrics give analytic type in the SAME original section ideal. -/
theorem sectionLogNormSq_hasAnalyticSingularities (a : LineBundleAtlas L) (k : ℕ)
    (s : bundlePowerGlobalSections L k) (hs : s ≠ 0) :
    letI := E.isSeparated
    letI := E.quasiCompact
    GlobalAnalyticSingularities.HasAnalyticSingularitiesOfType (H.sectionLogNormSq a k s) 1
      (schemeSectionAnalyticDivisor f n E a k s hs).ideal := by
  let := E.isSeparated
  let := E.quasiCompact
  have h := DivisorMetric.hasAnalyticSingularitiesOfType_of_isDivisorMetric
    (H.sectionMeteredDivisor_isDivisorMetric a k s hs)
  rwa [H.sectionMeteredDivisor_weight a k s hs] at h

/-- The fixed-H metered divisor has exactly the actual section-divisor support. -/
theorem sectionMeteredDivisor_support (a : LineBundleAtlas L) (k : ℕ)
    (s : bundlePowerGlobalSections L k) (hs : s ≠ 0) :
    letI := E.isSeparated
    letI := E.quasiCompact
    (H.sectionMeteredDivisor a k s hs).support =
      (schemeSectionAnalyticDivisor f n E a k s hs).support := by
  let := E.isSeparated
  let := E.quasiCompact
  exact StepFourNoComponentContainsW.support_eq_of_isDivisorMetric
    (H.sectionMeteredDivisor_isDivisorMetric a k s hs)

/-- Same actual ideal and genuine compactness give metric-independent singularity type. -/
theorem sectionLogNormSq_sameSingularityType_metric (K : SchemeLineBundleMetric f n E L)
    (a b : LineBundleAtlas L) (k : ℕ) (s : bundlePowerGlobalSections L k) (hs : s ≠ 0) :
    letI := E.isSeparated
    letI := E.quasiCompact
    SameSingularityTypeOn (H.sectionLogNormSq a k s) (K.sectionLogNormSq b k s) univ := by
  let := E.isSeparated
  let := E.quasiCompact
  let := E.analyticCompact
  have hH := H.sectionLogNormSq_hasAnalyticSingularities a k s hs
  have hK := K.sectionLogNormSq_hasAnalyticSingularities b k s hs
  rw [schemeSectionAnalyticDivisor_ideal, schemeSectionAnalyticIdeal_atlas_independent f n E b a k s] at hK
  rw [schemeSectionAnalyticDivisor_ideal] at hH
  exact IdealWeightComparison.sameSingularityTypeOn_univ_of_eq_type hH hK

/-- The actual full multiplier germ ideals are independent of the reference metric. -/
theorem multiplierIdeal_sectionLogNormSq_metric_independent (K : SchemeLineBundleMetric f n E L)
    (a b : LineBundleAtlas L) (k : ℕ) (s : bundlePowerGlobalSections L k) (hs : s ≠ 0) (c : ℝ) :
    multiplierIdeal (n := n) c (H.sectionLogNormSq a k s) =
      multiplierIdeal (n := n) c (K.sectionLogNormSq b k s) := by
  let := E.isSeparated
  let := E.quasiCompact
  have hsame := H.sectionLogNormSq_sameSingularityType_metric K a b k s hs
  have hH := (H.isThetaPshPotential_sectionLogNormSq a k s hs).quasiPshPotential.1
  have hK := (K.isThetaPshPotential_sectionLogNormSq b k s hs).quasiPshPotential.1
  ext p g
  let e := complexChartAt (n := n) p
  have hp : p ∈ e.val.source := mem_complexChartAt_source p
  have hz := e.val.map_source hp
  have hchart : SameSingularityTypeOn (chartFunction (H.sectionLogNormSq a k s) e)
      (chartFunction (K.sectionLogNormSq b k s) e) univ := by
    exact ⟨⟨hsame.1.choose, fun z _ => hsame.1.choose_spec _ (mem_univ _)⟩,
      ⟨hsame.2.choose, fun z _ => hsame.2.choose_spec _ (mem_univ _)⟩⟩
  exact and_congr_right fun _ => multiplierIntegrableAt_iff_of_sameSingularityTypeOn
    (hH e _ hz) (hK e _ hz) (U := univ) univ_mem hchart

end Integral

/-- The same degree-zero unit has whole logarithmic norm zero. -/
theorem sectionLogNormSq_one (a : LineBundleAtlas L) :
    H.sectionLogNormSq a 0 (bundlePowerGlobalOne L) = 0 := by
  funext p
  simp [sectionLogNormSq, H.sectionNormSq_one]

/-- Whole homogeneous product identity, including actual zero sections. -/
theorem sectionLogNormSq_mul (a : LineBundleAtlas L) (k l : ℕ)
    (s : bundlePowerGlobalSections L k) (t : bundlePowerGlobalSections L l) :
    H.sectionLogNormSq a (k + l) (atlasPowerGlobalMul a k l s t) =
      fun p => H.sectionLogNormSq a k s p + H.sectionLogNormSq a l t p := by
  funext p
  rw [sectionLogNormSq, H.sectionNormSq_mul a k l s t p,
    ENNReal.ofReal_mul (H.sectionNormSq_nonneg a k s p), ENNReal.log_mul_add]
  rfl

/-- The original zero section has bottom logarithm, while nonzero sections may have zeros. -/
theorem sectionLogNormSq_zero (a : LineBundleAtlas L) (k : ℕ) :
    H.sectionLogNormSq a k (0 : bundlePowerGlobalSections L k) = fun _ => ⊥ := by
  funext p
  let U := schemePointFrameOpen f p a
  let α := schemePointFrame f p a
  have hp : schemeComplexPointImage f p ∈ U := schemePointFrame_mem f p a
  rw [sectionLogNormSq, H.sectionNormSq_frame a α k 0 p hp]
  have hz : schemeOpenRegularFunction f n E U (weightCoefficient α k 0) p = 0 := by
    rw [schemeOpenRegularFunction_apply f n E U _ p hp]
    have hc : weightCoefficient α k 0 = 0 := by
      unfold weightCoefficient
      rw [map_zero]
      exact ((α.tensorPower k).coefficients (𝟙 U)).map_zero
    rw [hc, map_zero, map_zero, map_zero]
  change ENNReal.log (ENNReal.ofReal (Complex.normSq
    (schemeOpenRegularFunction f n E U (weightCoefficient α k 0) p) * _)) = ⊥
  rw [hz]
  simp

end SchemeLineBundleMetric

end SGPT.Okounkov

namespace SGPT.Okounkov

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.LocalCurrents

variable {X : Scheme} {f : X ⟶ Spec (.of ℂ)} {m : ℕ}
  [SmoothOfRelativeDimension (m + 1) f] {E : ClosedProjectiveEmbedding f}
local instance : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance [IsSeparated f] [QuasiCompact f] : IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

namespace SchemeLineBundleMetric

variable {L : X.Modules} [IsIntegral X] (H : SchemeLineBundleMetric f (m + 1) E L)

/-- The actual native current uses the manufactured genuine weight and the same fixed H. -/
def sectionThetaCurrent (a : LineBundleAtlas L) (k : ℕ)
    (s : bundlePowerGlobalSections L k) (hs : s ≠ 0) :
    letI := E.isSeparated
    letI := E.quasiCompact
    GlobalCurrent (m + 1) (SchemeComplexPoint f) (degreeTwo (Nat.succ_pos m)) := by
  let := E.isSeparated
  let := E.quasiCompact
  exact NaturalThetaPshGeometricCurrent.thetaPotentialCurrent ((k : ℝ) • H.curvature a).val
    (H.sectionLogNormSq a k s) (H.isThetaPshPotential_sectionLogNormSq a k s hs)

/-- Closedness, actual type, and positivity on EVERY full strongly positive chart test. -/
theorem sectionThetaCurrent_closed_type_positive (a : LineBundleAtlas L) (k : ℕ)
    (s : bundlePowerGlobalSections L k) (hs : s ≠ 0) :
    letI := E.isSeparated
    letI := E.quasiCompact
    (H.sectionThetaCurrent a k s hs).IsClosed (CanonicalCurrentFrame.canonicalBasis (m + 1)) ∧
    (H.sectionThetaCurrent a k s hs).IsTypeOneOne
      (CanonicalCurrentFrame.canonicalBasis (m + 1)) (Nat.succ_pos m) ∧
    ∀ (e : ComplexChart (m + 1) (SchemeComplexPoint f))
      (α : TestForm (chartTarget e) (2 * m)),
      (∀ x, α x ∈ StronglyPositiveForms.spCone m) →
        0 ≤ (H.sectionThetaCurrent a k s hs).inChart e
          (CanonicalComplementaryCurrentTests.castTestDegree
            (by rw [complexModel_real_finrank]; omega :
              2 * m = Module.finrank ℝ (ComplexModel (m + 1)) - 2) α) := by
  let := E.isSeparated
  let := E.quasiCompact
  exact NaturalThetaPshClosedCurrent.thetaPotentialCurrent_closed_type_positive
    ((k : ℝ) • H.curvature a).val (H.sectionLogNormSq a k s)
    (H.isThetaPshPotential_sectionLogNormSq a k s hs)

end SchemeLineBundleMetric
end SGPT.Okounkov
