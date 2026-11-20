import SGPT.Trace.BertiniAuxiliaryPhysicalSharpExtension
import SGPT.Trace.BertiniFamilyAmbientSection

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

section Central
variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (a v : ComplexModel N) (U : TopologicalSpace.Opens (ComplexModel 1))
  (hsm : ∀ t : U, IsSmoothHypersurfaceMember (d + 1) p (pencilParameter i a v t.val))

theorem familyNativeMemberAdjunction_of_original_central_values
    (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) X)
    (T : HolomorphicSections (n := d + 1)
      (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X))
        (nativeBertiniHyperplaneBundle p)) L).Fiber) (ρ : ℝ) (t : U) (ht : t.val = 0) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
    letI := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
    letI := isCompact_iff_compactSpace.mp
      (isClosed_member p p.contMDiff.continuous (affinePoint i (a - t.val 0 • v))).isCompact
    ∀ S : HolomorphicSections (n := d + 1) (familyNativePhysicalModel p i a v U hsm L).Fiber,
      (∀ q, normalizedPencilNormal p i a v U ρ q = 0 → S q = T q.val.2) →
      familyNativeMemberAdjunctionSection p i a v U hsm L t S =
        nativeBertiniPhysicalAdjunctionSection p i (a - t.val 0 • v) (hsm t) L T := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
  let := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
  let := isCompact_iff_compactSpace.mp
    (isClosed_member p p.contMDiff.continuous (affinePoint i (a - t.val 0 • v))).isCompact
  intro S htrace
  rw [← familyAmbientPhysicalSection_member p i a v U hsm L T t]
  apply familyNativeMemberAdjunctionSection_congr
  intro y
  apply htrace
  change t.val 0 / (ρ : ℂ) = 0
  rw [ht]
  simp
end Central

variable {d : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

theorem exists_auxiliary_ambient_physical_hodge_sharp_extension_all_twists
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
        ∀ T : HolomorphicSections (n := d + 1)
          (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X))
            (nativeBertiniHyperplaneBundle p)) L).Fiber,
          nativeBertiniAdjunctionHodgeEnergy p i (a - (0 : ComplexModel 1) 0 • v)
            (hsm ⟨0,h0⟩) L φ T < ⊤ →
        ∃ S : HolomorphicSections (n := d + 1)
          (familyNativePhysicalModel p i a v (parameterDisc ρ)
            (familyBaseRestrictedSmoothness p i a v U (parameterDisc ρ) hVU hsm) L).Fiber,
          (∀ q, normalizedPencilNormal p i a v (parameterDisc ρ) ρ q = 0 →
            S q = T q.val.2) ∧
          (∫⁻ q, ENNReal.ofReal (gain (annularDensity σ δ)
            (-Real.log (nativeRadius (normalizedPencilNormal p i a v (parameterDisc ρ) ρ) q)) *
            ‖S q‖ ^ 2) * multiplierWeight 1 (φ q.val.2)
            ∂familyMatchedVolume p i a v (parameterDisc ρ)
              (familyBaseRestrictedSmoothness p i a v U (parameterDisc ρ) hVU hsm)) ≤
            ENNReal.ofReal (windowMass σ + δ) * (ENNReal.ofReal (Real.pi * ρ ^ 2) *
              nativeBertiniAdjunctionHodgeEnergy p i (a - (0 : ComplexModel 1) 0 • v) (hsm ⟨0,h0⟩) L φ T) := by
  obtain ⟨k₀,hk₀,hall⟩ := exists_auxiliary_physical_hodge_sharp_extension_all_twists omega φ hφ G E hG hE hGpos
  refine ⟨k₀,hk₀,?_⟩
  intro k hk A hA hAsemi b
  dsimp only
  intro N p i a v U hsm h0
  let L := twistedPower A (twistedPower G E k) b
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  obtain ⟨r,hr,hrU,hρall⟩ := hall k hk A hA hAsemi b N p i a v U hsm h0
  refine ⟨r,hr,hrU,?_⟩
  intro ρ hρ hρr
  obtain ⟨hVU,hsmall⟩ := hρall ρ hρ hρr
  refine ⟨hVU,?_⟩
  let hsV := familyBaseRestrictedSmoothness p i a v U (parameterDisc ρ) hVU hsm
  let := familyChartedSpace p i a v (parameterDisc ρ) p.contMDiff hsV
  let := isComplexManifold_family p i a v (parameterDisc ρ) p.contMDiff hsV
  intro σ δ hσ hδ T hfinite
  let F := familyAmbientPhysicalSection p i a v U hsm L T
  have hF : familyNativeMemberHodgeEnergy p i a v U hsm L φ ⟨0,h0⟩ F < ⊤ := by
    rw [familyAmbientPhysicalSection_memberHodgeEnergy]
    exact hfinite
  obtain ⟨S,htrace,henergy⟩ := hsmall σ δ hσ hδ F hF
  refine ⟨S,?_,?_⟩
  · intro q hq
    exact htrace q hq
  · dsimp only [F] at henergy
    rw [familyAmbientPhysicalSection_memberHodgeEnergy] at henergy
    exact henergy

end SGPT.Trace.BertiniFamilyCanonical
