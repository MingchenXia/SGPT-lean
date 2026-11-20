import SGPT.Trace.BertiniFamilyNormalCollar
import SGPT.Trace.TwistedL2SingularRemoval
import SGPT.Trace.OptimalNormalResidueKernel

/-! Actual finite physical matched-volume background on genuine compact collars. -/
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
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
open SGPT.Trace.Bertini SGPT.Trace.BertiniPencilFamily SGPT.Trace.BertiniPencilNormal SGPT.Trace.OTMargin
open SGPT.Trace.TwistedL2 SGPT.Trace.OptimalNormalResidueKernel SGPT.Trace.OptimalNormalRegularization

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (a v : ComplexModel N) (U : TopologicalSpace.Opens (ComplexModel 1))
  (hsm : ∀ t : U, IsSmoothHypersurfaceMember (d + 1) p (affinePoint i (a - t.val 0 • v)))

theorem familyMatchedVolume_locallyFinite :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    IsLocallyFiniteMeasure (familyMatchedVolume p i a v U hsm) := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  exact isLocallyFiniteMeasure_of_isSmoothPositiveVolume (familyMatchedVolume_smoothPositive p i a v U hsm)

theorem familyMatchedVolume_compact_lt_top :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (K : Set (familyIncidence p i a v U)), IsCompact K → familyMatchedVolume p i a v U hsm K < ⊤ := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let := familyMatchedVolume_locallyFinite p i a v U hsm
  intro K hK
  exact hK.measure_lt_top

theorem familyMatchedVolume_compact_real_integral_lt_top :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (K : Set (familyIncidence p i a v U)), IsCompact K →
      ∀ (g : familyIncidence p i a v U → ℝ), Continuous g →
      (∫⁻ q in K, ENNReal.ofReal (g q) ∂familyMatchedVolume p i a v U hsm) < ⊤ := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro K hK g hg
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
  calc
    _ ≤ ∫⁻ _ in K, ENNReal.ofReal C ∂familyMatchedVolume p i a v U hsm := by
      apply setLIntegral_mono' hK.isClosed.measurableSet
      intro q hq
      apply ENNReal.ofReal_le_ofReal
      exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hC q hq)
    _ = ENNReal.ofReal C * familyMatchedVolume p i a v U hsm K := setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (familyMatchedVolume_compact_lt_top p i a v U hsm K hK)

variable (L : HermitianHolomorphicLineBundle (d + 1) X)

theorem familyPhysical_compact_weighted_energy_lt_top :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (K : Set (familyIncidence p i a v U)), IsCompact K →
      ∀ (S : ∀ q, (familyNativePhysicalModel p i a v U hsm L).Fiber q),
      SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := d + 1)
        (familyNativePhysicalModel p i a v U hsm L).Fiber S univ →
      ∀ (ψ : familyIncidence p i a v U → ℝ), Continuous ψ →
      (∫⁻ q in K, ENNReal.ofReal (‖S q‖ ^ 2 * Real.exp (-ψ q)) ∂familyMatchedVolume p i a v U hsm) < ⊤ := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro K hK S hS ψ hψ
  have hn : Continuous (fun q => ‖S q‖) := continuousOn_univ.mp
    (ContinuousFiberNorm.continuous.comp_continuousOn hS.continuousOn)
  exact familyMatchedVolume_compact_real_integral_lt_top p i a v U hsm K hK _
    ((hn.pow 2).mul (Real.continuous_exp.comp hψ.neg))

theorem familyPhysical_parameter_tube_energy_lt_top (r : ℝ)
    (hrU : Metric.closedBall (0 : ComplexModel 1) r ⊆ U) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (S : ∀ q, (familyNativePhysicalModel p i a v U hsm L).Fiber q),
      SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := d + 1)
        (familyNativePhysicalModel p i a v U hsm L).Fiber S univ →
      ∀ (u : X → ℝ), Continuous u →
      (∫⁻ q in {q | q.val.1.val ∈ Metric.ball (0 : ComplexModel 1) r},
        ENNReal.ofReal (‖S q‖ ^ 2 * Real.exp (-u q.val.2)) ∂familyMatchedVolume p i a v U hsm) < ⊤ := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro S hS u hu
  have hψ : Continuous (fun q : familyIncidence p i a v U => u q.val.2) :=
    hu.comp (continuous_snd.comp continuous_subtype_val)
  have hsub : {q : familyIncidence p i a v U | q.val.1.val ∈ Metric.ball (0 : ComplexModel 1) r} ⊆
      familyClosedParameterCollar p i a v U r := fun _ hq => Metric.ball_subset_closedBall hq
  exact (lintegral_mono_set hsub).trans_lt
    (familyPhysical_compact_weighted_energy_lt_top p i a v U hsm L _
      (isCompact_familyClosedParameterCollar p i a v U r hrU) S hS _ hψ)

theorem familyPhysical_parameter_tube_kernel_energy_lt_top (r ρ ε : ℝ) (hε : 0 < ε)
    (hrU : Metric.closedBall (0 : ComplexModel 1) r ⊆ U) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (S : ∀ q, (familyNativePhysicalModel p i a v U hsm L).Fiber q),
      SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := d + 1)
        (familyNativePhysicalModel p i a v U hsm L).Fiber S univ →
      ∀ (u : X → ℝ), Continuous u →
      (∫⁻ q in {q | q.val.1.val ∈ Metric.ball (0 : ComplexModel 1) r},
        ENNReal.ofReal (residueKernel ε (scalarParameter p i a v U q / (ρ : ℂ)) *
          ‖S q‖ ^ 2 * Real.exp (-u q.val.2)) ∂familyMatchedVolume p i a v U hsm) < ⊤ := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro S hS u hu
  have hn : Continuous (fun q => ‖S q‖) := continuousOn_univ.mp
    (ContinuousFiberNorm.continuous.comp_continuousOn hS.continuousOn)
  have hψ : Continuous (fun q : familyIncidence p i a v U => u q.val.2) :=
    hu.comp (continuous_snd.comp continuous_subtype_val)
  have hf : Continuous (fun q : familyIncidence p i a v U => scalarParameter p i a v U q / (ρ : ℂ)) :=
    (contMDiff_scalarParameter p i a v U p.contMDiff hsm).continuous.div_const _
  have hR := hf.norm.pow 2
  have hker : Continuous (fun q : familyIncidence p i a v U => residueKernel ε (scalarParameter p i a v U q / (ρ : ℂ))) := by
    unfold residueKernel normalKernel
    apply continuous_const.div ((continuous_const.add hR).pow 2)
    intro q
    exact pow_ne_zero 2 (ne_of_gt (add_pos_of_pos_of_nonneg hε (sq_nonneg _)))
  have hsub : {q : familyIncidence p i a v U | q.val.1.val ∈ Metric.ball (0 : ComplexModel 1) r} ⊆
      familyClosedParameterCollar p i a v U r := fun _ hq => Metric.ball_subset_closedBall hq
  exact (lintegral_mono_set hsub).trans_lt
    (familyMatchedVolume_compact_real_integral_lt_top p i a v U hsm _
      (isCompact_familyClosedParameterCollar p i a v U r hrU) _
      ((hker.mul (hn.pow 2)).mul (Real.continuous_exp.comp hψ.neg)))

end SGPT.Trace.BertiniFamilyCanonical
