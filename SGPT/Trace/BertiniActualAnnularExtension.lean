import SGPT.Trace.BertiniAmbientPhysicalSharpExtension
import SGPT.Trace.BertiniFamilyGainFubini
import SGPT.Trace.OptimalAnnularCircleSelection

/-! Actual original auxiliary/ambient singular extension on EVERY annulus,
with genuine full intrinsic member Hodge circle mean and no MEP premise. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniFamilyCanonical
open Bundle Set Filter TensorProduct MeasureTheory Complex
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft SGPT.Toric.F1IntersectionDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Bergman.PolynomialH0Growth SGPT.Bergman.NativeHermitianMetric
open SGPT.Trace.Bertini SGPT.Trace.BertiniPencilFamily SGPT.Trace.BertiniPencilNormal
open SGPT.Trace.OptimalNativeNormalWeight SGPT.Trace.OptimalNativeNormalBackground
open SGPT.Trace.OptimalExtensionGainMass SGPT.Trace.OptimalExtensionODE
open SGPT.Trace.BertiniDiscExhaustion SGPT.Trace.OptimalAnnularSelection
open SGPT.Trace.OptimalAnnularCircleSelection

section Circle
variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (a v : ComplexModel N) (U V : TopologicalSpace.Opens (ComplexModel 1)) (hVU : V ≤ U)
  (hsm : ∀ t : U, IsSmoothHypersurfaceMember (d + 1) p (pencilParameter i a v t.val))
  (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) X)

def familyNativeMemberCircleHodgeMean (φ : X → EReal) (s : ℝ) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := familyChartedSpace p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    letI := isComplexManifold_family p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    HolomorphicSections (n := d + 1)
      (familyNativePhysicalModel p i a v V (familyBaseRestrictedSmoothness p i a v U V hVU hsm) L).Fiber → ℝ≥0∞ := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let hsV := familyBaseRestrictedSmoothness p i a v U V hVU hsm
  let := familyChartedSpace p i a v V p.contMDiff hsV
  let := isComplexManifold_family p i a v V p.contMDiff hsV
  intro S
  exact (ENNReal.ofReal (2 * Real.pi))⁻¹ * ∫⁻ θ in Ioc (0 : ℝ) (2 * Real.pi),
    familySmallMemberHodgeMarginal p i a v U V hVU hsm L S
      (fun q => multiplierWeight 1 (φ q.val.2)) (circleMap 0 s θ)

theorem familyNativeMemberCircleHodgeMean_le (φ : X → EReal) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := familyChartedSpace p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    letI := isComplexManifold_family p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    ∀ (S : HolomorphicSections (n := d + 1)
      (familyNativePhysicalModel p i a v V (familyBaseRestrictedSmoothness p i a v U V hVU hsm) L).Fiber)
      (s η : ℝ) (B : ℝ≥0∞), 0 < η →
      (∫⁻ θ in Ioc (0 : ℝ) (2 * Real.pi), familySmallMemberHodgeMarginal p i a v U V hVU hsm L S
        (fun q => multiplierWeight 1 (φ q.val.2)) (circleMap 0 s θ)) ≤
        ENNReal.ofReal ((1 + η) * (2 * Real.pi)) * B →
      familyNativeMemberCircleHodgeMean p i a v U V hVU hsm L φ s S ≤ ENNReal.ofReal (1 + η) * B := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let hsV := familyBaseRestrictedSmoothness p i a v U V hVU hsm
  let := familyChartedSpace p i a v V p.contMDiff hsV
  let := isComplexManifold_family p i a v V p.contMDiff hsV
  intro S s η B hη hbound
  have hη0 : 0 ≤ 1 + η := by linarith
  have hp : 0 < ENNReal.ofReal (2 * Real.pi) := ENNReal.ofReal_pos.mpr (by positivity)
  rw [ENNReal.ofReal_mul hη0] at hbound
  unfold familyNativeMemberCircleHodgeMean
  calc
    _ ≤ (ENNReal.ofReal (2 * Real.pi))⁻¹ *
        ((ENNReal.ofReal (1 + η) * ENNReal.ofReal (2 * Real.pi)) * B) := mul_le_mul' le_rfl hbound
    _ = ((ENNReal.ofReal (2 * Real.pi))⁻¹ * ENNReal.ofReal (2 * Real.pi)) *
        (ENNReal.ofReal (1 + η) * B) := by ac_rfl
    _ = _ := by rw [ENNReal.inv_mul_cancel hp.ne' ENNReal.ofReal_ne_top,one_mul]
end Circle

variable {d : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

theorem exists_auxiliary_ambient_annular_hodge_extension_all_twists
    (omega : KahlerBackground (d + 1) X) (φ : X → EReal)
    (hφ : IsGlobalQuasiPshPotential (n := d + 1) φ)
    (G E : HermitianHolomorphicLineBundle.{0,0} (d + 1) X)
    (hG : IsSourceSmoothHermitianMetric G) (hE : IsSourceSmoothHermitianMetric E)
    (hGpos : (sourceNativeFirstChernForm G hG).val.IsKahler) :
    ∃ k₀ : ℕ, 0 < k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      ∀ (A : HermitianHolomorphicLineBundle.{0,0} (d + 1) X) (hA : IsSourceSmoothHermitianMetric A),
      (sourceNativeFirstChernForm A hA).val.IsSemipositive → ∀ b : ℕ,
      let L := twistedPower A (twistedPower G E k) b
      ∀ (N : ℕ)
        (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
        (i : Fin (N + 1)) (a v : ComplexModel N) (U : TopologicalSpace.Opens (ComplexModel 1))
        (hsm : ∀ t : U, IsSmoothHypersurfaceMember (d + 1) p (pencilParameter i a v t.val))
        (h0 : (0 : ComplexModel 1) ∈ U),
      letI := familyChartedSpace p i a v U p.contMDiff hsm
      letI := isComplexManifold_family p i a v U p.contMDiff hsm
      ∃ r : ℝ, 0 < r ∧ Metric.closedBall (0 : ComplexModel 1) r ⊆ U ∧
        ∀ ρ : ℝ, 0 < ρ → ρ ≤ r / 4 → ∃ hVU : parameterDisc ρ ≤ U,
        letI := familyChartedSpace p i a v (parameterDisc ρ) p.contMDiff
          (familyBaseRestrictedSmoothness p i a v U (parameterDisc ρ) hVU hsm)
        letI := isComplexManifold_family p i a v (parameterDisc ρ) p.contMDiff
          (familyBaseRestrictedSmoothness p i a v U (parameterDisc ρ) hVU hsm)
        ∀ ρ' : ℝ, 0 < ρ' → ρ' < ρ → ∀ η : ℝ, 0 < η →
        ∀ T : HolomorphicSections (n := d + 1)
          (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X))
            (nativeBertiniHyperplaneBundle p)) L).Fiber,
          nativeBertiniAdjunctionHodgeEnergy p i (a - (0 : ComplexModel 1) 0 • v)
            (hsm ⟨0,h0⟩) L φ T < ⊤ →
        ∃ S : HolomorphicSections (n := d + 1)
          (familyNativePhysicalModel p i a v (parameterDisc ρ)
            (familyBaseRestrictedSmoothness p i a v U (parameterDisc ρ) hVU hsm) L).Fiber,
          (∀ q, normalizedPencilNormal p i a v (parameterDisc ρ) ρ q = 0 → S q = T q.val.2) ∧
          ∃ s ∈ Ioo ρ' ρ, Metric.closedBall (0 : ℂ) s ⊆ Metric.ball (0 : ℂ) ρ ∧
            familyNativeMemberCircleHodgeMean p i a v U (parameterDisc ρ) hVU hsm L φ s S ≤
              ENNReal.ofReal (1 + η) * nativeBertiniAdjunctionHodgeEnergy p i
                (a - (0 : ComplexModel 1) 0 • v) (hsm ⟨0,h0⟩) L φ T := by
  obtain ⟨k₀,hk₀,hall⟩ :=
    exists_auxiliary_ambient_physical_hodge_sharp_extension_all_twists omega φ hφ G E hG hE hGpos
  refine ⟨k₀,hk₀,?_⟩
  intro k hk A hA hAsemi b
  dsimp only
  intro N p i a v U hsm h0
  let L := twistedPower A (twistedPower G E k) b
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  obtain ⟨rS,hrS,hrSU,hsharp⟩ := hall k hk A hA hAsemi b N p i a v U hsm h0
  obtain ⟨rF,hrF,_hrFU,hfubini⟩ := exists_family_disc_gain_hodge_fubini p i a v U hsm L h0
  refine ⟨min rS rF,lt_min hrS hrF,
    (Metric.closedBall_subset_closedBall (min_le_left rS rF)).trans hrSU,?_⟩
  intro ρ hρ hρr
  have hρS : ρ ≤ rS / 4 := by have h := min_le_left rS rF; linarith
  have hρF : ρ ≤ rF / 4 := by have h := min_le_right rS rF; linarith
  obtain ⟨hVU,hsmall⟩ := hsharp ρ hρ hρS
  obtain ⟨_hVUf,hfub⟩ := hfubini ρ hρ hρF
  refine ⟨hVU,?_⟩
  let hsV := familyBaseRestrictedSmoothness p i a v U (parameterDisc ρ) hVU hsm
  let := familyChartedSpace p i a v (parameterDisc ρ) p.contMDiff hsV
  let := isComplexManifold_family p i a v (parameterDisc ρ) p.contMDiff hsV
  intro ρ' hρ' hinner η hη T hfinite
  obtain ⟨σ,hσ,hann⟩ := exists_actual_log_window hρ' hinner
  let δ := slackRegularizer σ η
  have hδ : 0 < δ := slackRegularizer_pos hσ hη
  obtain ⟨S,htrace,henergy⟩ := hsmall σ δ hσ hδ T hfinite
  let Q := familySmallMemberHodgeMarginal p i a v U (parameterDisc ρ) hVU hsm L S
    (fun q => multiplierWeight 1 (φ q.val.2))
  let g : ℂ → ℝ := fun τ => gain (annularDensity σ δ) (-Real.log (‖τ / (ρ : ℂ)‖ ^ 2))
  have hRadius : Continuous (fun τ : ℂ => ‖τ / (ρ : ℂ)‖ ^ 2) := (continuous_id.div_const _).norm.pow 2
  have hTime : Measurable (fun τ : ℂ => -Real.log (‖τ / (ρ : ℂ)‖ ^ 2)) :=
    (Real.measurable_log.comp hRadius.measurable).neg
  have hg : Measurable g :=
    (Real.continuous_exp.mul (contDiff_annularDensity σ δ).continuous).measurable.comp hTime
  obtain ⟨hQ,hgain⟩ := hfub S φ hφ.1.upperSemicontinuous.measurable g hg
  let B := nativeBertiniAdjunctionHodgeEnergy p i (a - (0 : ComplexModel 1) 0 • v) (hsm ⟨0,h0⟩) L φ T
  have hm : 0 ≤ windowMass σ + δ := add_nonneg (windowMass_pos hσ).le hδ.le
  have hcoeff : ENNReal.ofReal (windowMass σ + δ) * (ENNReal.ofReal (Real.pi * ρ ^ 2) * B) =
      ENNReal.ofReal ((windowMass σ + δ) * Real.pi * ρ ^ 2) * B := by
    have hr : (windowMass σ + δ) * (Real.pi * ρ ^ 2) = (windowMass σ + δ) * Real.pi * ρ ^ 2 := by ring
    rw [← mul_assoc,← ENNReal.ofReal_mul hm,hr]
  have hdisc : (∫⁻ τ in Metric.ball (0 : ℂ) ρ, ENNReal.ofReal (g τ) * Q τ) ≤
      ENNReal.ofReal (windowMass σ + δ) * (ENNReal.ofReal (Real.pi * ρ ^ 2) * B) :=
    hgain.symm.le.trans henergy
  have hdiscBound := hdisc.trans_eq hcoeff
  obtain ⟨s,hs,hclosed,hcircle⟩ := exists_actual_annular_circle_of_sharp_gain hρ hσ hη hann hQ hfinite.ne hdiscBound
  refine ⟨S,htrace,s,hs,hclosed,?_⟩
  exact familyNativeMemberCircleHodgeMean_le p i a v U (parameterDisc ρ) hVU hsm L φ S s η B hη hcircle

end SGPT.Trace.BertiniFamilyCanonical
