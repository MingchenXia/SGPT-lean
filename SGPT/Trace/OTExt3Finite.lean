import SGPT.Trace.OTExt2Statement
import SGPT.Bergman.SourceMultiplierSectionGlobalMass
import SGPT.PSH.GlobalL2CoverSystem
import SGPT.Foundations.Analysis.Pending.HiepThreeTermEstimate

/-!
# Sections along a compact submanifold in a multiplier ideal have finite norm

Blueprint `claude-ot-ext3.tex`, node `claude-ot-ext3:finite`.  Used in FPT
`cor:compact-positive-metric-extension` ("the finiteness of the norm on `Y` means that `f` lies
locally in the multiplier ideal of `kφ|_Y`"): on a compact complex manifold `W` with a smooth
positive volume `μ`, a section `s` of `V|_W` whose coefficients in the preferred frames are
holomorphic germs of `W` in `𝓘(c u)` (`IsAlongMultiplierSection`) satisfies
`∫_W |s|² e^{-cu} dμ < ∞` (`lintegral_lt_top_of_isAlongMultiplierSection`).

Proof: near `p ∈ W`, in the chart `a` of `W` at `p` and the preferred frame `E` of `V` at `p`,
`|s| = |coef| |E|`; the frame norm and the chart density of `μ` are bounded on a compact ball
of the chart, so the local integral is bounded by the Lebesgue integral of the coefficient,
finite by the definition of `𝓘(c u)`; compactness gives a finite cover.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Trace.OTExt3

open Set Filter Metric MeasureTheory Bundle
open scoped Topology ENNReal Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Bergman.CompactHolomorphicSectionsDraft
open SGPT.Trace.TwistedL2

variable {n m : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]
  (V : X → Type) [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℂ (V x)]
  [TopologicalSpace (TotalSpace ℂ V)] [FiberBundle ℂ V] [VectorBundle ℂ ℂ V]
  [ContinuousFiberNorm V]
  {W : Set X} [ChartedSpace (ComplexModel m) W] [IsComplexManifold m W]

theorem norm_eq_alongCoefficient_mul {s : (y : W) → V y} {y : W}
    (E : Trivialization ℂ (TotalSpace.proj :
      TotalSpace ℂ V → X)) [MemTrivializationAtlas E] (hyE : y.1 ∈ E.baseSet) :
    ‖s y‖ = ‖alongCoefficient V E s y‖ * frameNorm V E y.1 := by
  rw [SGPT.PSH.GlobalL2.norm_eq_coef_mul_norm_frame E hyE (s y),
    Trivialization.continuousLinearMapAt_apply_of_mem (R := ℂ) E hyE]
  rfl

/-- The norm of a section along `W` with holomorphic coefficients is continuous. -/
theorem continuous_norm_of_isAlongMultiplierSection {c : ℝ} {u : W → EReal}
    {s : (y : W) → V y} (hs : IsAlongMultiplierSection V (m := m) c u s) :
    Continuous fun y => ‖s y‖ := by
  refine continuous_iff_continuousAt.mpr fun p => ?_
  set E := trivializationAt ℂ V p.1
  have hpE : p.1 ∈ E.baseSet := mem_baseSet_trivializationAt ℂ V p.1
  have hhol := (hs p).1
  have hcoef : ContinuousAt (alongCoefficient V E s) p :=
    (hhol.self_of_nhds).continuousAt
  have hnbhd : ∀ᶠ y in 𝓝 p, y.1 ∈ E.baseSet :=
    (E.open_baseSet.preimage continuous_subtype_val).mem_nhds hpE
  have hfr : ContinuousAt (fun y : W => frameNorm V E y.1) p :=
    ((frameNorm_continuousOn V E).continuousAt (E.open_baseSet.mem_nhds hpE)).comp
      continuous_subtype_val.continuousAt
  refine (hcoef.norm.mul hfr).congr_of_eventuallyEq ?_
  filter_upwards [hnbhd] with y hy
  exact norm_eq_alongCoefficient_mul V E hy

variable [MeasurableSpace W] [BorelSpace W]

/-- **Finiteness of the norm of a section along a compact submanifold in a multiplier ideal.** -/
theorem lintegral_lt_top_of_isAlongMultiplierSection [CompactSpace W] {μ : Measure W}
    (hμ : IsSmoothPositiveVolume (n := m) μ) {c : ℝ} (hc : 0 < c) {u : W → EReal}
    (hu : Measurable u) {s : (y : W) → V y} (hs : IsAlongMultiplierSection V (m := m) c u s) :
    ∫⁻ y, ENNReal.ofReal (‖s y‖ ^ 2) * multiplierWeight c (u y) ∂μ < ⊤ := by
  have hnc := continuous_norm_of_isAlongMultiplierSection V hs
  have hfm : Measurable fun y => ENNReal.ofReal (‖s y‖ ^ 2) * multiplierWeight c (u y) :=
    (ENNReal.measurable_ofReal.comp (hnc.pow 2).measurable).mul
      ((continuous_multiplierWeight hc).measurable.comp hu)
  refine SGPT.Bergman.MultiplierSectionsDraft.lintegral_lt_top_of_finite_open_neighborhoods
    hfm fun p => ?_
  set E := trivializationAt ℂ V p.1
  have hpE : p.1 ∈ E.baseSet := mem_baseSet_trivializationAt ℂ V p.1
  set a := complexChartAt (n := m) p
  have hpa : p ∈ a.val.source := mem_complexChartAt_source p
  set z₀ := a.val p
  have hz₀ : z₀ ∈ a.val.target := a.val.map_source hpa
  obtain ⟨-, hMI⟩ := hs p
  have hMI' := (SGPT.Bergman.MultiplierSectionsDraft.multiplierIntegrableAt_scaled_one_iff
    (chartFunction u a) hc _ _ _).mp hMI
  obtain ⟨-, U, hU, hzU, -, -, hL2⟩ := hMI'
  set D := U ∩ (a.val.target ∩ a.val.symm ⁻¹' (Subtype.val ⁻¹' E.baseSet))
  have hD : IsOpen D := hU.inter (a.val.isOpen_inter_preimage_symm
    (E.open_baseSet.preimage continuous_subtype_val))
  have hzD : z₀ ∈ D := ⟨hzU, hz₀, by
    show (a.val.symm z₀).1 ∈ E.baseSet
    rw [a.val.left_inv hpa]; exact hpE⟩
  obtain ⟨R, hR, hRD⟩ := Metric.isOpen_iff.mp hD z₀ hzD
  set r := R / 2
  have hr : 0 < r := half_pos hR
  have hKD : closedBall z₀ r ⊆ D := (closedBall_subset_ball (half_lt_self hR)).trans hRD
  have hKt : closedBall z₀ r ⊆ a.val.target := fun z hz => (hKD hz).2.1
  have hKc : IsCompact (closedBall z₀ r) := isCompact_closedBall z₀ r
  obtain ⟨ρ, hρs, -, hmap⟩ := hμ a
  obtain ⟨Cρ, hCρ⟩ := hKc.exists_bound_of_continuousOn (hρs.continuousOn.mono hKt)
  have hfrc : ContinuousOn (fun z => frameNorm V E (a.val.symm z).1) (closedBall z₀ r) := by
    refine (frameNorm_continuousOn V E).comp (continuous_subtype_val.comp_continuousOn
      (a.val.continuousOn_symm.mono hKt)) fun z hz => (hKD hz).2.2
  obtain ⟨CF, hCF⟩ := hKc.exists_bound_of_continuousOn hfrc
  refine ⟨a.val.source ∩ a.val ⁻¹' ball z₀ r, a.val.isOpen_inter_preimage isOpen_ball,
    ⟨hpa, mem_ball_self hr⟩, ?_⟩
  refine (lintegral_mono_set (show a.val.source ∩ a.val ⁻¹' ball z₀ r ⊆
    a.val.source ∩ a.val ⁻¹' closedBall z₀ r from fun y hy => ⟨hy.1, ball_subset_closedBall hy.2⟩)).trans_lt ?_
  rw [setLIntegral_source_inter_preimage a hρs.continuousOn hmap hKc hKt hfm]
  calc ∫⁻ z in closedBall z₀ r, ENNReal.ofReal (ρ z) *
        (ENNReal.ofReal (‖s (a.val.symm z)‖ ^ 2) * multiplierWeight c (u (a.val.symm z)))
      ≤ ∫⁻ z in closedBall z₀ r, ENNReal.ofReal (|Cρ| * CF ^ 2) *
          multiplierDensity (chartFunction u a) c
            (fun z => alongCoefficient V E s (a.val.symm z)) z := by
        refine setLIntegral_mono' isClosed_closedBall.measurableSet fun z hz => ?_
        have hzE : (a.val.symm z).1 ∈ E.baseSet := (hKD hz).2.2
        rw [norm_eq_alongCoefficient_mul V E hzE]
        unfold multiplierDensity chartFunction
        have h1 : ρ z ≤ |Cρ| := by
          have := hCρ z hz; rw [Real.norm_eq_abs] at this
          exact (le_abs_self _).trans (this.trans (le_abs_self _))
        have hF0 : 0 ≤ frameNorm V E (a.val.symm z).1 := norm_nonneg _
        have h2 : frameNorm V E (a.val.symm z).1 ≤ CF := by
          have := hCF z hz; rw [Real.norm_eq_abs, abs_of_nonneg hF0] at this; exact this
        rw [← mul_assoc, ← mul_assoc]
        gcongr ?_ * _
        rw [← ENNReal.ofReal_mul' (sq_nonneg _), ← ENNReal.ofReal_mul' (sq_nonneg _)]
        refine ENNReal.ofReal_le_ofReal ?_
        set A := ‖alongCoefficient V E s (a.val.symm z)‖
        set Fz := frameNorm V E (a.val.symm z).1
        have hA : 0 ≤ A := norm_nonneg _
        have hX : 0 ≤ (A * Fz) ^ 2 := sq_nonneg _
        have hXY : (A * Fz) ^ 2 ≤ CF ^ 2 * A ^ 2 := by
          rw [mul_pow, mul_comm]
          exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hF0 h2 2) (sq_nonneg _)
        calc ρ z * (A * Fz) ^ 2 ≤ |Cρ| * (A * Fz) ^ 2 := mul_le_mul_of_nonneg_right h1 hX
          _ ≤ |Cρ| * (CF ^ 2 * A ^ 2) := mul_le_mul_of_nonneg_left hXY (abs_nonneg _)
          _ = |Cρ| * CF ^ 2 * A ^ 2 := by ring
    _ = ENNReal.ofReal (|Cρ| * CF ^ 2) * ∫⁻ z in closedBall z₀ r,
          multiplierDensity (chartFunction u a) c
            (fun z => alongCoefficient V E s (a.val.symm z)) z :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        ((lintegral_mono_set fun z hz => (hKD hz).1).trans_lt hL2)

end SGPT.Trace.OTExt3
