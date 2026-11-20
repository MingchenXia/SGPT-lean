import SGPT.Trace.BertiniFamilySmallMemberMarginal
import SGPT.Trace.BertiniFamilyBaseVolume

/-! Actual family normal-residue density and original member intrinsic Hodge integral. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniFamilyCanonical

open Bundle Set Filter TensorProduct MeasureTheory
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace
open ProductComplexManifold
open scoped ProductComplexManifold
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft SGPT.Toric.F1IntersectionDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Trace.Bertini SGPT.Trace.BertiniPencilFamily SGPT.Trace.BertiniPencilNormal SGPT.Trace.OTMargin
open SGPT.Trace.BertiniNativeNormalKernel

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (a v : ComplexModel N) (U : TopologicalSpace.Opens (ComplexModel 1))
  (hsm : ∀ t : U, IsSmoothHypersurfaceMember (d + 1) p (affinePoint i (a - t.val 0 • v)))

variable [MeasurableSpace X] [BorelSpace X]
variable [CompactSpace X] (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) X)

theorem exists_family_global_member_hodge_fubini (h0 : (0 : ComplexModel 1) ∈ U) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∃ r : ℝ, 0 < r ∧ Metric.closedBall (0 : ComplexModel 1) r ⊆ U ∧
      ∀ (V : TopologicalSpace.Opens (ComplexModel 1)) (hVU : V ≤ U),
        (V : Set (ComplexModel 1)) ⊆ Metric.closedBall (0 : ComplexModel 1) (r / 2) →
        letI := familyChartedSpace p i a v V p.contMDiff
          (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
        letI := isComplexManifold_family p i a v V p.contMDiff
          (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
        ∀ (S : HolomorphicSections (n := d + 1)
            (familyNativePhysicalModel p i a v V (familyBaseRestrictedSmoothness p i a v U V hVU hsm) L).Fiber)
          (w : familyIncidence p i a v U → ℝ≥0∞), Measurable w →
          Measurable (familySmallMemberHodgeMarginal p i a v U V hVU hsm L S w) ∧
          (∫⁻ q, ENNReal.ofReal (‖S q‖ ^ 2) * w (familyBaseInclusion p i a v U V hVU q)
            ∂familyMatchedVolume p i a v V (familyBaseRestrictedSmoothness p i a v U V hVU hsm)) =
            ∫⁻ τ : ℂ, familySmallMemberHodgeMarginal p i a v U V hVU hsm L S w τ ∂volume := by
  classical
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  obtain ⟨k,F,r,ψ,hr,hrU,_hrK,hF,hψ0,_hψc,hψs,_hsum,hone⟩ :=
    exists_family_finite_real_normal_cutoffs p i a v U hsm h0
  refine ⟨r,hr,hrU,?_⟩
  intro V hVU hVr
  let hsV := familyBaseRestrictedSmoothness p i a v U V hVU hsm
  let := familyChartedSpace p i a v V p.contMDiff hsV
  let := isComplexManifold_family p i a v V p.contMDiff hsV
  intro S w hw
  let β : Fin k → familyIncidence p i a v U → ℝ := fun j => ψ j
  have hβ (j : Fin k) : Continuous (β j) := (ψ j).contMDiff.continuous
  have hβone (q : familyIncidence p i a v U) (hq : q ∈ familyBaseTube p i a v U V) : ∑ j, β j q = 1 :=
    hone q (hVr hq)
  have hQ := familySmallMemberHodgeMarginal_measurable_partition p i a v U V hVU hsm L
    k F hF β hβ hψ0 hψs hβone S w hw
  refine ⟨hQ,?_⟩
  let S0 := familyPhysicalZeroExtension p i a v U V hVU hsm L S
  let n : familyIncidence p i a v U → ℝ≥0∞ := fun q => ENNReal.ofReal (‖S0 q‖ ^ 2)
  let G : familyIncidence p i a v U → ℝ≥0∞ := fun q => n q * w q
  let f : Fin k → familyIncidence p i a v U → ℝ≥0∞ := fun j q => n q * (ENNReal.ofReal (β j q) * w q)
  let M : Fin k → ℂ → ℝ≥0∞ := fun j => familyRawNormalMemberMarginal p i a v U hsm L (F j) S0
    (fun q => ENNReal.ofReal (β j q) * w q)
  let μ := familyMatchedVolume p i a v U hsm
  have hn : Measurable n := familyPhysicalZeroExtension_normSq_measurable p i a v U V hVU hsm L S
  have hG : Measurable G := hn.mul hw
  have hf (j : Fin k) : Measurable (f j) := hn.mul ((ENNReal.continuous_ofReal.comp (hβ j)).measurable.mul hw)
  have hM (j : Fin k) : Measurable (M j) := familyRawNormalMemberMarginal_measurable p i a v U hsm L
    (F j) (hF j) S0 hn (fun q => ENNReal.ofReal (β j q) * w q)
    ((ENNReal.continuous_ofReal.comp (hβ j)).measurable.mul hw)
  have hGs : Function.support G ⊆ familyBaseTube p i a v U V := by
    intro q hq
    by_contra hqt
    have hz : S0 q = 0 := familyPhysicalZeroExtension_outside p i a v U V hVU hsm L S q hqt
    apply hq
    change ENNReal.ofReal (‖S0 q‖ ^ 2) * w q = 0
    rw [hz,norm_zero,zero_pow (by decide : 2 ≠ 0),ENNReal.ofReal_zero,zero_mul]
  have hsmall :
      (∫⁻ q, ENNReal.ofReal (‖S q‖ ^ 2) * w (familyBaseInclusion p i a v U V hVU q)
        ∂familyMatchedVolume p i a v V hsV) = ∫⁻ q in (familyBaseTube p i a v U V : Set _), G q ∂μ := by
    rw [← familyBaseMatchedVolume_lintegral p i a v U V hVU hsm G hG]
    apply lintegral_congr
    intro q
    change ENNReal.ofReal (‖S q‖ ^ 2) * w (familyBaseInclusion p i a v U V hVU q) =
      ENNReal.ofReal (‖S0 (familyBaseInclusion p i a v U V hVU q)‖ ^ 2) * w (familyBaseInclusion p i a v U V hVU q)
    exact (congrArg (fun T : (familyNativePhysicalModel p i a v U hsm L).Fiber
        (familyBaseInclusion p i a v U V hVU q) =>
          ENNReal.ofReal (‖T‖ ^ 2) * w (familyBaseInclusion p i a v U V hVU q))
      (familyPhysicalZeroExtension_inside p i a v U V hVU hsm L S q)).symm
  have hpoint (q : familyIncidence p i a v U) : G q = ∑ j, f j q := by
    by_cases hq : q ∈ familyBaseTube p i a v U V
    · have ha : ∑ j, ENNReal.ofReal (β j q) = 1 := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hψ0 j q),hβone q hq,ENNReal.ofReal_one]
      change n q * w q = ∑ j, n q * (ENNReal.ofReal (β j q) * w q)
      rw [← Finset.mul_sum,← Finset.sum_mul,ha,one_mul]
    · have hz : S0 q = 0 := familyPhysicalZeroExtension_outside p i a v U V hVU hsm L S q hq
      change ENNReal.ofReal (‖S0 q‖ ^ 2) * w q =
        ∑ j, ENNReal.ofReal (‖S0 q‖ ^ 2) * (ENNReal.ofReal (β j q) * w q)
      simp only [hz,norm_zero,zero_pow (by decide : 2 ≠ 0),ENNReal.ofReal_zero,zero_mul,Finset.sum_const_zero]
  have hfs (j : Fin k) : Function.support (f j) ⊆ (F j).ambSource := by
    intro q hq
    by_contra hqt
    have hb : β j q = 0 := image_eq_zero_of_notMem_tsupport (fun h => hqt (hψs j h))
    apply hq
    change n q * (ENNReal.ofReal (β j q) * w q) = 0
    rw [hb,ENNReal.ofReal_zero,zero_mul,mul_zero]
  have hlocal (j : Fin k) : (∫⁻ q in (F j).ambSource, f j q ∂μ) = ∫⁻ τ : ℂ, M j τ ∂volume :=
    familyPhysical_integral_local_member_fubini p i a v U hsm L (F j) (hF j) S0 hn
      (fun q => ENNReal.ofReal (β j q) * w q)
      ((ENNReal.continuous_ofReal.comp (hβ j)).measurable.mul hw)
  calc
    _ = ∫⁻ q in (familyBaseTube p i a v U V : Set _), G q ∂μ := hsmall
    _ = ∫⁻ q, G q ∂μ := setLIntegral_eq_of_support_subset hGs
    _ = ∫⁻ q, ∑ j, f j q ∂μ := lintegral_congr hpoint
    _ = ∑ j, ∫⁻ q, f j q ∂μ := lintegral_finsetSum' _ (fun j _ => (hf j).aemeasurable)
    _ = ∑ j, ∫⁻ q in (F j).ambSource, f j q ∂μ := by
      apply Finset.sum_congr rfl
      intro j _
      exact (setLIntegral_eq_of_support_subset (hfs j)).symm
    _ = ∑ j, ∫⁻ τ : ℂ, M j τ ∂volume := by
      apply Finset.sum_congr rfl
      intro j _
      exact hlocal j
    _ = ∫⁻ τ : ℂ, ∑ j, M j τ ∂volume := (lintegral_finsetSum' _ (fun j _ => (hM j).aemeasurable)).symm
    _ = _ := by
      apply lintegral_congr
      intro τ
      exact (familySmallMemberHodgeMarginal_partition p i a v U V hVU hsm L
        k F hF β hβ hψ0 hψs hβone S w hw τ).symm

end SGPT.Trace.BertiniFamilyCanonical
