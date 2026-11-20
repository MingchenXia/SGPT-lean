import SGPT.Trace.BertiniPhysicalSharpExtension

/-! One actual auxiliary-power choice, before every semipositive twist and
pencil, produces the actual singular sharp physical extension. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniFamilyCanonical
open Bundle Set Filter TensorProduct MeasureTheory
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft SGPT.Toric.F1IntersectionDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Bergman.PolynomialH0Growth SGPT.Bergman.NativeHermitianMetric
open SGPT.Trace.Bertini SGPT.Trace.BertiniPencilFamily
open SGPT.Trace.OptimalNativeNormalWeight SGPT.Trace.OptimalNativeNormalBackground
open SGPT.Trace.OptimalExtensionGainMass SGPT.Trace.OptimalExtensionODE
open SGPT.Trace.BertiniDiscExhaustion SGPT.Trace.TwistedL2
open SGPT.Trace.BertiniAuxiliaryCurvatureChoice

variable {d : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

theorem exists_auxiliary_physical_hodge_sharp_extension_all_twists
    (omega : KahlerBackground (d + 1) X) (φ : X → EReal)
    (hφ : IsGlobalQuasiPshPotential (n := d + 1) φ)
    (G E : HermitianHolomorphicLineBundle.{0,0} (d + 1) X)
    (hG : IsSourceSmoothHermitianMetric G) (hE : IsSourceSmoothHermitianMetric E)
    (hGpos : (sourceNativeFirstChernForm G hG).val.IsKahler) :
    ∃ k₀ : ℕ, 0 < k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      ∀ (T : HermitianHolomorphicLineBundle.{0,0} (d + 1) X) (hT : IsSourceSmoothHermitianMetric T),
      (sourceNativeFirstChernForm T hT).val.IsSemipositive → ∀ b : ℕ,
      let L := twistedPower T (twistedPower G E k) b
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
        ∀ (σ δ : ℝ), 0 < σ → 0 < δ →
        ∀ F : HolomorphicSections (n := d + 1) (familyNativePhysicalModel p i a v U hsm L).Fiber,
          familyNativeMemberHodgeEnergy p i a v U hsm L φ ⟨0,h0⟩ F < ⊤ →
        ∃ S : HolomorphicSections (n := d + 1)
          (familyNativePhysicalModel p i a v (parameterDisc ρ)
            (familyBaseRestrictedSmoothness p i a v U (parameterDisc ρ) hVU hsm) L).Fiber,
          (∀ q, normalizedPencilNormal p i a v (parameterDisc ρ) ρ q = 0 →
            S q = familyPhysicalBaseRestriction p i a v U (parameterDisc ρ) hVU hsm L F q) ∧
          (∫⁻ q, ENNReal.ofReal (gain (annularDensity σ δ)
            (-Real.log (nativeRadius (normalizedPencilNormal p i a v (parameterDisc ρ) ρ) q)) *
            ‖S q‖ ^ 2) * multiplierWeight 1 (φ q.val.2)
            ∂familyMatchedVolume p i a v (parameterDisc ρ)
              (familyBaseRestrictedSmoothness p i a v U (parameterDisc ρ) hVU hsm)) ≤
            ENNReal.ofReal (windowMass σ + δ) * (ENNReal.ofReal (Real.pi * ρ ^ 2) *
              familyNativeMemberHodgeEnergy p i a v U hsm L φ ⟨0,h0⟩ F) := by
  obtain ⟨C,_hC,hsharp⟩ := exists_original_physical_hodge_sharp_extension omega φ hφ
  obtain ⟨k₀,hk₀,hchoice⟩ := exists_actual_native_auxiliary_for_all_semipositive_twists
    omega G E hG hE hGpos C 1
  refine ⟨k₀,hk₀,?_⟩
  intro k hk T hT hTsemi b
  let L := twistedPower T (twistedPower G E k) b
  have hL : IsSourceSmoothHermitianMetric L := sourceNativeTwistedPower_smooth T (twistedPower G E k) hT
    (sourceNativeTwistedPower_smooth G E hG hE k) b
  exact hsharp L hL 1 zero_lt_one (hchoice k hk T hT hTsemi b)

end SGPT.Trace.BertiniFamilyCanonical
