import SGPT.Bergman.SourceMultiplierSectionLocalMass

/-!
# MultiplierSectionCompactMass

A section lies in `I(cφ)` near a point iff `|s|² e^{-cφ}` has finite mass on a neighbourhood.

Ported from the previous team's drafts (`work/sgpt-active-lanes-20261102/bergman-*`).
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.Bergman.MultiplierSectionsDraft

open Bundle Set Filter TopologicalSpace CategoryTheory Opposite TensorProduct MeasureTheory Metric
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending.HironakaSmoothCentreRealDomainActualSheafStalk
  SGPT.Foundations.Analysis.Pending.HironakaSmoothCentreRealDomainActualIdealPresheaf

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  (V : X → Type) [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℂ (V x)]
  [TopologicalSpace (TotalSpace ℂ V)] [FiberBundle ℂ V] [VectorBundle ℂ ℂ V]
  [ContMDiffVectorBundle ∞ ℂ V (𝓘(ℂ, ComplexModel n))]

variable [MeasurableSpace X] [BorelSpace X] [ContinuousFiberNorm V]

/-- The ORIGINAL preferred coefficient multiplier condition is equivalent to an ACTUAL finite-mass neighborhood
of the SAME original Hermitian section and smooth positive volume. -/
theorem originalSection_local_finite_iff {φ : X → EReal} (hφ : Measurable φ)
    {c : ℝ} (hc : 0 < c) (s : HolomorphicSections (n := n) V)
    {μ : Measure X} (hμ : IsSmoothPositiveVolume (n := n) μ) (x : X) :
    (multiplierIdeal (n := n) c φ).mem x
        (sectionCoefficient V (preferredOriginalFrame V x).val s) ↔
      ∃ W : Set X, IsOpen W ∧ x ∈ W ∧
        (∫⁻ y in W, originalSectionDensity (n := n) V φ c s y ∂μ) < ⊤ := by
  let e := preferredOriginalFrame V x
  let := e.property
  let a := complexChartAt (n := n) x
  let z₀ := a.val x
  have hx : x ∈ a.val.source := mem_complexChartAt_source x
  have hz₀ : z₀ ∈ a.val.target := a.val.map_source hx
  have hinv : a.val.symm z₀ = x := a.val.left_inv hx
  have hxe : x ∈ e.val.baseSet := mem_baseSet_trivializationAt ℂ V x
  let F := sectionCoefficient V e.val s ∘ a.val.symm
  constructor
  · rintro ⟨_, _, U, hU, hzU, _, hL2⟩
    let D := U ∩ (a.val.target ∩ a.val.symm ⁻¹' e.val.baseSet)
    have hD : IsOpen D := hU.inter (a.val.isOpen_inter_preimage_symm e.val.open_baseSet)
    have hzD : z₀ ∈ D := ⟨hzU, hz₀, by change a.val.symm z₀ ∈ e.val.baseSet; rwa [hinv]⟩
    obtain ⟨R, hR, hRD⟩ := Metric.isOpen_iff.mp hD z₀ hzD
    let r := R / 2
    have hr : 0 < r := half_pos hR
    have hKD : closedBall z₀ r ⊆ D := (closedBall_subset_ball (half_lt_self hR)).trans hRD
    have hKt : closedBall z₀ r ⊆ a.val.target := fun z hz => (hKD hz).2.1
    have hKe : ∀ z ∈ closedBall z₀ r, a.val.symm z ∈ e.val.baseSet := fun z hz => (hKD hz).2.2
    have hcoef : (∫⁻ z in closedBall z₀ r, multiplierDensity (chartFunction φ a) c F z) < ⊤ :=
      (lintegral_mono_set (show closedBall z₀ r ⊆ U from fun z hz => (hKD hz).1)).trans_lt hL2.2
    have hmass := (originalSection_setLIntegral_finite_iff (n := n) V hφ c s e a hμ
      (isCompact_closedBall z₀ r) hKt hKe).mpr hcoef
    let W := a.val.source ∩ a.val ⁻¹' ball z₀ r
    refine ⟨W, a.val.isOpen_inter_preimage isOpen_ball, ⟨hx, mem_ball_self hr⟩, ?_⟩
    exact (lintegral_mono_set (show W ⊆ a.val.source ∩ a.val ⁻¹' closedBall z₀ r from
      fun y hy => ⟨hy.1, ball_subset_closedBall hy.2⟩)).trans_lt hmass
  · rintro ⟨W, hW, hxW, hmass⟩
    let D := a.val.target ∩ a.val.symm ⁻¹' (W ∩ e.val.baseSet)
    have hD : IsOpen D := a.val.isOpen_inter_preimage_symm (hW.inter e.val.open_baseSet)
    have hzD : z₀ ∈ D := ⟨hz₀, by change a.val.symm z₀ ∈ W ∩ e.val.baseSet; rw [hinv]; exact ⟨hxW, hxe⟩⟩
    obtain ⟨R, hR, hRD⟩ := Metric.isOpen_iff.mp hD z₀ hzD
    let r := R / 2
    have hr : 0 < r := half_pos hR
    have hKD : closedBall z₀ r ⊆ D := (closedBall_subset_ball (half_lt_self hR)).trans hRD
    have hKt : closedBall z₀ r ⊆ a.val.target := fun z hz => (hKD hz).1
    have hKe : ∀ z ∈ closedBall z₀ r, a.val.symm z ∈ e.val.baseSet := fun z hz => (hKD hz).2.2
    have hsub : a.val.source ∩ a.val ⁻¹' closedBall z₀ r ⊆ W := by
      intro y hy
      have hh := (hKD hy.2).2.1
      change a.val.symm (a.val y) ∈ W at hh
      rwa [a.val.left_inv hy.1] at hh
    have hcoef := (originalSection_setLIntegral_finite_iff (n := n) V hφ c s e a hμ
      (isCompact_closedBall z₀ r) hKt hKe).mp ((lintegral_mono_set hsub).trans_lt hmass)
    have hBt : ball z₀ r ⊆ a.val.target := ball_subset_closedBall.trans hKt
    have hBe : ∀ z ∈ ball z₀ r, a.val.symm z ∈ e.val.baseSet := fun z hz => hKe z (ball_subset_closedBall hz)
    have hF : DifferentiableOn ℂ F (ball z₀ r) :=
      (sectionCoefficient_chart_differentiable V e.val x s).mono (fun z hz => ⟨hBt hz, hBe z hz⟩)
    have hφa : AEMeasurable (chartFunction φ a) (volume.restrict (ball z₀ r)) :=
      hφ.comp_aemeasurable ((a.val.continuousOn_symm.mono hBt).aemeasurable isOpen_ball.measurableSet)
    have hweight : AEMeasurable (fun z => multiplierWeight c (chartFunction φ a z))
        (volume.restrict (ball z₀ r)) :=
      (measurable_originalMultiplierWeight measurable_id c).comp_aemeasurable hφa
    refine ⟨originalSectionCoefficient_holomorphicAt (n := n) V e s hxe,
      hc, ball z₀ r, isOpen_ball, mem_ball_self hr, hF, ?_, ?_⟩
    · exact ((hF.continuousOn.aemeasurable isOpen_ball.measurableSet).norm.pow_const 2).ennreal_ofReal.mul hweight
    · exact (lintegral_mono_set ball_subset_closedBall).trans_lt hcoef

end SGPT.Bergman.MultiplierSectionsDraft
