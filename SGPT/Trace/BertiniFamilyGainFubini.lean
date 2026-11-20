import SGPT.Trace.BertiniFamilyGlobalMemberFubini
import SGPT.Trace.BertiniMemberMarginalGain
import SGPT.Trace.BertiniDiscExhaustion

/-! Actual whole-small-family singular gain energy is the ordinary disc
integral of the SAME genuine full native original member Hodge marginal. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
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
open SGPT.Trace.BertiniNativeNormalKernel SGPT.Trace.BertiniDiscExhaustion

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (a v : ComplexModel N) (U : TopologicalSpace.Opens (ComplexModel 1))
  (hsm : ∀ t : U, IsSmoothHypersurfaceMember (d + 1) p (pencilParameter i a v t.val))
  (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) X)

theorem familySmallMemberHodgeMarginal_zero_outside
    (V : TopologicalSpace.Opens (ComplexModel 1)) (hVU : V ≤ U) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := familyChartedSpace p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    letI := isComplexManifold_family p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    ∀ (S : HolomorphicSections (n := d + 1)
      (familyNativePhysicalModel p i a v V (familyBaseRestrictedSmoothness p i a v U V hVU hsm) L).Fiber)
      (w : familyIncidence p i a v U → ℝ≥0∞) (τ : ℂ),
      modelOneScalarEquiv.symm τ ∉ V → familySmallMemberHodgeMarginal p i a v U V hVU hsm L S w τ = 0 := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let hsV := familyBaseRestrictedSmoothness p i a v U V hVU hsm
  let := familyChartedSpace p i a v V p.contMDiff hsV
  let := isComplexManifold_family p i a v V p.contMDiff hsV
  intro S w τ hτ
  unfold familySmallMemberHodgeMarginal
  rw [dif_neg hτ]

variable [MeasurableSpace X] [BorelSpace X]

theorem exists_family_disc_gain_hodge_fubini (h0 : (0 : ComplexModel 1) ∈ U) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∃ r : ℝ, 0 < r ∧ Metric.closedBall (0 : ComplexModel 1) r ⊆ U ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ r / 4 → ∃ hVU : parameterDisc ρ ≤ U,
      letI := familyChartedSpace p i a v (parameterDisc ρ) p.contMDiff
        (familyBaseRestrictedSmoothness p i a v U (parameterDisc ρ) hVU hsm)
      letI := isComplexManifold_family p i a v (parameterDisc ρ) p.contMDiff
        (familyBaseRestrictedSmoothness p i a v U (parameterDisc ρ) hVU hsm)
      ∀ (S : HolomorphicSections (n := d + 1)
        (familyNativePhysicalModel p i a v (parameterDisc ρ)
          (familyBaseRestrictedSmoothness p i a v U (parameterDisc ρ) hVU hsm) L).Fiber)
        (φ : X → EReal), Measurable φ → ∀ (G : ℂ → ℝ), Measurable G →
        Measurable (familySmallMemberHodgeMarginal p i a v U (parameterDisc ρ) hVU hsm L S
          (fun q => multiplierWeight 1 (φ q.val.2))) ∧
        (∫⁻ q, ENNReal.ofReal (G (scalarParameter p i a v (parameterDisc ρ) q) * ‖S q‖ ^ 2) *
          multiplierWeight 1 (φ q.val.2) ∂familyMatchedVolume p i a v (parameterDisc ρ)
            (familyBaseRestrictedSmoothness p i a v U (parameterDisc ρ) hVU hsm)) =
          ∫⁻ τ in Metric.ball (0 : ℂ) ρ, ENNReal.ofReal (G τ) *
            familySmallMemberHodgeMarginal p i a v U (parameterDisc ρ) hVU hsm L S
              (fun q => multiplierWeight 1 (φ q.val.2)) τ := by
  classical
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  obtain ⟨r,hr,hrU,hall⟩ := exists_family_global_member_hodge_fubini p i a v U hsm L h0
  refine ⟨r,hr,hrU,?_⟩
  intro ρ hρ hρr
  have hρfull : ρ ≤ r := by linarith
  have hρhalf : ρ ≤ r / 2 := by linarith
  have hVU : parameterDisc ρ ≤ U :=
    Metric.ball_subset_closedBall.trans ((Metric.closedBall_subset_closedBall hρfull).trans hrU)
  have hVr : (parameterDisc ρ : Set (ComplexModel 1)) ⊆ Metric.closedBall 0 (r / 2) :=
    Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall hρhalf)
  refine ⟨hVU,?_⟩
  let hsV := familyBaseRestrictedSmoothness p i a v U (parameterDisc ρ) hVU hsm
  let := familyChartedSpace p i a v (parameterDisc ρ) p.contMDiff hsV
  let := isComplexManifold_family p i a v (parameterDisc ρ) p.contMDiff hsV
  intro S φ hφ G hG
  let w : familyIncidence p i a v U → ℝ≥0∞ := fun q => multiplierWeight 1 (φ q.val.2)
  have hw : Measurable w := (continuous_multiplierWeight one_pos).measurable.comp
    (hφ.comp (continuous_snd.comp continuous_subtype_val).measurable)
  have hτ : Measurable (scalarParameter p i a v U) :=
    (contMDiff_scalarParameter p i a v U p.contMDiff hsm).continuous.measurable
  let wG : familyIncidence p i a v U → ℝ≥0∞ := fun q =>
    ENNReal.ofReal (G (scalarParameter p i a v U q)) * w q
  have hwG : Measurable wG := (ENNReal.measurable_ofReal.comp (hG.comp hτ)).mul hw
  let Q := familySmallMemberHodgeMarginal p i a v U (parameterDisc ρ) hVU hsm L S w
  refine ⟨(hall (parameterDisc ρ) hVU hVr S w hw).1,?_⟩
  have hsupp : Function.support (fun τ => ENNReal.ofReal (G τ) * Q τ) ⊆ Metric.ball (0 : ℂ) ρ := by
    intro τ hτsupp
    by_contra hnot
    have hout : modelOneScalarEquiv.symm τ ∉ parameterDisc ρ := by
      intro hin
      apply hnot
      change dist (modelOneScalarEquiv.symm τ) 0 < ρ at hin
      simpa only [Metric.mem_ball,dist_zero_right,modelOneScalarEquiv.symm.norm_map] using hin
    have hz := familySmallMemberHodgeMarginal_zero_outside p i a v U hsm L (parameterDisc ρ) hVU S w τ hout
    apply hτsupp
    change ENNReal.ofReal (G τ) * familySmallMemberHodgeMarginal p i a v U (parameterDisc ρ) hVU hsm L S w τ = 0
    rw [hz,mul_zero]
  calc
    _ = ∫⁻ q, ENNReal.ofReal (‖S q‖ ^ 2) * wG (familyBaseInclusion p i a v U (parameterDisc ρ) hVU q)
        ∂familyMatchedVolume p i a v (parameterDisc ρ) hsV := by
      apply lintegral_congr
      intro q
      rw [mul_comm (G _) (‖S q‖ ^ 2),ENNReal.ofReal_mul (sq_nonneg _)]
      change (ENNReal.ofReal (‖S q‖ ^ 2) *
        ENNReal.ofReal (G (scalarParameter p i a v (parameterDisc ρ) q))) * multiplierWeight 1 (φ q.val.2) =
        ENNReal.ofReal (‖S q‖ ^ 2) *
          (ENNReal.ofReal (G (scalarParameter p i a v (parameterDisc ρ) q)) * multiplierWeight 1 (φ q.val.2))
      exact mul_assoc _ _ _
    _ = ∫⁻ τ : ℂ, familySmallMemberHodgeMarginal p i a v U (parameterDisc ρ) hVU hsm L S wG τ :=
      (hall (parameterDisc ρ) hVU hVr S wG hwG).2
    _ = ∫⁻ τ : ℂ, ENNReal.ofReal (G τ) * Q τ := by
      apply lintegral_congr
      intro τ
      exact familySmallMemberHodgeMarginal_gain_factor p i a v U (parameterDisc ρ) hVU hsm L φ G S τ
    _ = _ := (setLIntegral_eq_of_support_subset hsupp).symm

end SGPT.Trace.BertiniFamilyCanonical
