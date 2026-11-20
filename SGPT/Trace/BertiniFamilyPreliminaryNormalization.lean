import SGPT.Trace.BertiniFamilyBaseVolume
import SGPT.Trace.BertiniFamilyTubeKernelLimit
import SGPT.Trace.OptimalNormalEpsilonLimit
import SGPT.Trace.BertiniDiscExhaustion

/-! The literal smaller native engine normalization, with the original
annular mass factor and full actual central member Hodge energy. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniFamilyCanonical
open Bundle Set Filter TensorProduct MeasureTheory
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft SGPT.Toric.F1IntersectionDraft
open SGPT.Trace.Bertini SGPT.Trace.BertiniPencilFamily SGPT.Trace.BertiniPencilNormal
open SGPT.Trace.OptimalNormalResidueKernel SGPT.Trace.OptimalNormalRegularization
open SGPT.Trace.OptimalNativeNormalBackground SGPT.Trace.OptimalNativeNormalWeight
open SGPT.Trace.OptimalNormalEpsilonLimit SGPT.Trace.OptimalExtensionGainMass
open SGPT.Trace.OptimalGainCompactBounds SGPT.Trace.TwistedL2
open SGPT.Trace.BertiniDiscExhaustion

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (a v : ComplexModel N) (U : TopologicalSpace.Opens (ComplexModel 1))
  (hsm : ∀ t : U, IsSmoothHypersurfaceMember (d + 1) p (pencilParameter i a v t.val))
  (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) X)

def familyNativePreliminaryKernelEnergy :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ℝ → HolomorphicSections (n := d + 1) (familyNativePhysicalModel p i a v U hsm L).Fiber →
      (X → ℝ) → ℝ → ℝ → ℝ → ℝ≥0∞ := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  exact fun ρ S u ε σ δ => actualPreliminaryKernelEnergy
    (familyNativePhysicalModel p i a v U hsm L) (familyMatchedVolume p i a v U hsm)
    (normalizedPencilNormal p i a v U ρ) (fun q => u q.val.2) ε σ δ S

theorem familyNativePreliminaryKernelEnergy_baseRestriction
    (ρ : ℝ) (hVU : parameterDisc ρ ≤ U) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := familyChartedSpace p i a v (parameterDisc ρ) p.contMDiff
      (familyBaseRestrictedSmoothness p i a v U (parameterDisc ρ) hVU hsm)
    letI := isComplexManifold_family p i a v (parameterDisc ρ) p.contMDiff
      (familyBaseRestrictedSmoothness p i a v U (parameterDisc ρ) hVU hsm)
    ∀ (S : HolomorphicSections (n := d + 1) (familyNativePhysicalModel p i a v U hsm L).Fiber)
      (u : X → ℝ), Continuous u → ∀ (ε σ δ : ℝ), 0 < ε → 0 ≤ windowMass σ + δ →
      familyNativePreliminaryKernelEnergy p i a v (parameterDisc ρ)
        (familyBaseRestrictedSmoothness p i a v U (parameterDisc ρ) hVU hsm) L ρ
        (familyPhysicalBaseRestriction p i a v U (parameterDisc ρ) hVU hsm L S) u ε σ δ =
      ENNReal.ofReal (windowMass σ + δ) *
        familyTubeKernelEnergy p i a v U hsm L S (fun q => u q.val.2) ρ ρ ε := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let hsV := familyBaseRestrictedSmoothness p i a v U (parameterDisc ρ) hVU hsm
  let := familyChartedSpace p i a v (parameterDisc ρ) p.contMDiff hsV
  let := isComplexManifold_family p i a v (parameterDisc ρ) p.contMDiff hsV
  intro S u hu ε σ δ hε hm
  let B := familyNativePhysicalModel p i a v U hsm L
  let f := normalizedPencilNormal p i a v U ρ
  let g : familyIncidence p i a v U → ℝ≥0∞ := fun q =>
    ENNReal.ofReal ((windowMass σ + δ) * normalKernel ε (nativeRadius f q) *
      ‖S q‖ ^ 2 * Real.exp (-u q.val.2))
  have hS : SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := d + 1) B.Fiber S univ :=
    (S.contMDiff.mdifferentiable (by simp)).mdifferentiableOn
  have hn : Continuous (fun q => ‖S q‖) :=
    continuousOn_univ.mp (continuousOn_norm_of_holomorphic B hS)
  have hf : Continuous f := (contMDiff_normalizedPencilNormal p i a v U p.contMDiff hsm ρ).continuous
  have hk : Continuous (fun q => normalKernel ε (nativeRadius f q)) :=
    continuous_const.div ((continuous_const.add (hf.norm.pow 2)).pow 2)
      (fun q => pow_ne_zero 2 (ne_of_gt (add_pos_of_pos_of_nonneg hε (sq_nonneg _))))
  have hw : Continuous (fun q : familyIncidence p i a v U => Real.exp (-u q.val.2)) :=
    Real.continuous_exp.comp (hu.comp (continuous_snd.comp continuous_subtype_val)).neg
  have hg : Measurable g := (ENNReal.continuous_ofReal.comp
    (((continuous_const.mul hk).mul (hn.pow 2)).mul hw)).measurable
  calc
    _ = ∫⁻ q, g (familyBaseInclusion p i a v U (parameterDisc ρ) hVU q)
        ∂familyMatchedVolume p i a v (parameterDisc ρ) hsV := by
      apply lintegral_congr
      intro q
      rfl
    _ = ∫⁻ q in (familyBaseTube p i a v U (parameterDisc ρ) : Set (familyIncidence p i a v U)),
        g q ∂familyMatchedVolume p i a v U hsm :=
      familyBaseMatchedVolume_lintegral p i a v U (parameterDisc ρ) hVU hsm g hg
    _ = _ := by
      unfold familyTubeKernelEnergy
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro q
      change ENNReal.ofReal ((windowMass σ + δ) * residueKernel ε
        (scalarParameter p i a v U q / (ρ : ℂ)) * ‖S q‖ ^ 2 * Real.exp (-u q.val.2)) = _
      rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hm (residueKernel_nonneg hε.le _)) (sq_nonneg _)),
        ENNReal.ofReal_mul (mul_nonneg hm (residueKernel_nonneg hε.le _)),ENNReal.ofReal_mul hm]
      ac_rfl

theorem exists_family_preliminary_kernel_hodge_limit (h0 : (0 : ComplexModel 1) ∈ U) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∃ r : ℝ, 0 < r ∧ Metric.closedBall (0 : ComplexModel 1) r ⊆ U ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ r / 4 → ∃ hVU : parameterDisc ρ ≤ U,
      letI := familyChartedSpace p i a v (parameterDisc ρ) p.contMDiff
        (familyBaseRestrictedSmoothness p i a v U (parameterDisc ρ) hVU hsm)
      letI := isComplexManifold_family p i a v (parameterDisc ρ) p.contMDiff
        (familyBaseRestrictedSmoothness p i a v U (parameterDisc ρ) hVU hsm)
      ∀ (S : HolomorphicSections (n := d + 1) (familyNativePhysicalModel p i a v U hsm L).Fiber)
        (u : X → ℝ), Continuous u → ∀ (σ δ : ℝ), 0 ≤ windowMass σ + δ →
        familyNativeMemberHodgeEnergy p i a v U hsm L (fun x => (u x : EReal)) ⟨0,h0⟩ S < ⊤ ∧
        (∀ ε : ℝ, 0 < ε → familyNativePreliminaryKernelEnergy p i a v (parameterDisc ρ)
          (familyBaseRestrictedSmoothness p i a v U (parameterDisc ρ) hVU hsm) L ρ
          (familyPhysicalBaseRestriction p i a v U (parameterDisc ρ) hVU hsm L S) u ε σ δ < ⊤) ∧
        Tendsto (fun ε : ℝ => familyNativePreliminaryKernelEnergy p i a v (parameterDisc ρ)
          (familyBaseRestrictedSmoothness p i a v U (parameterDisc ρ) hVU hsm) L ρ
          (familyPhysicalBaseRestriction p i a v U (parameterDisc ρ) hVU hsm L S) u ε σ δ) (𝓝[>] 0)
          (𝓝 (ENNReal.ofReal (windowMass σ + δ) *
            (ENNReal.ofReal (Real.pi * ρ ^ 2) * familyNativeMemberHodgeEnergy p i a v U hsm L
              (fun x => (u x : EReal)) ⟨0,h0⟩ S))) := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  obtain ⟨r,hr,hrU,hall⟩ := exists_family_tube_kernel_hodge_limit p i a v U hsm L h0
  refine ⟨r,hr,hrU,?_⟩
  intro ρ hρ hρr
  have hρfull : ρ ≤ r := by linarith
  have hVU : parameterDisc ρ ≤ U :=
    Metric.ball_subset_closedBall.trans ((Metric.closedBall_subset_closedBall hρfull).trans hrU)
  refine ⟨hVU,?_⟩
  let hsV := familyBaseRestrictedSmoothness p i a v U (parameterDisc ρ) hVU hsm
  let := familyChartedSpace p i a v (parameterDisc ρ) p.contMDiff hsV
  let := isComplexManifold_family p i a v (parameterDisc ρ) p.contMDiff hsV
  intro S u hu σ δ hm
  obtain ⟨hcentral,hallρ⟩ := hall S u hu
  obtain ⟨hε,hlim⟩ := hallρ ρ hρ hρr
  refine ⟨hcentral,?_,?_⟩
  · intro ε hεpos
    rw [familyNativePreliminaryKernelEnergy_baseRestriction p i a v U hsm L ρ hVU S u hu ε σ δ hεpos hm]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hε ε hεpos)
  · have h := ENNReal.Tendsto.const_mul hlim (a := ENNReal.ofReal (windowMass σ + δ))
      (Or.inr ENNReal.ofReal_ne_top)
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hεpos
    exact (familyNativePreliminaryKernelEnergy_baseRestriction p i a v U hsm L ρ hVU S u hu ε σ δ hεpos hm).symm

end SGPT.Trace.BertiniFamilyCanonical
