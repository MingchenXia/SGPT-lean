import SGPT.Okounkov.SourceMultiSliceOriginalRestriction
import SGPT.Okounkov.SourceMultiSliceOriginalInverse

/-! Actual arbitrary-codimension source approximation restrictions and
native trace limit on the SAME original flag target/class/functions. -/
set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Okounkov.SourceMultiSlice
open Set Filter
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SGPT.Foundations.Analysis.FirstPass.TraceBackground
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.SourceTraceRepresentativeDefinition
open SGPT.Foundations.Analysis.Pending.TraceRepresentativeConstruction
open SGPT.Foundations.Analysis.Pending.ThetaPshL1Topology
open SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityDistance
open SGPT.Foundations.Analysis.Pending.PluripolarCapacityDichotomy
open SGPT.PSH SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.PartialBody

/-- Exact source/native generic-zero normalization along the actual original
Y_k point inclusion, with the genuine factor two retained. -/
theorem nativeGeneric_zero_of_source_zero_of_pos (m k : ℕ)
    (F : OriginalFlagGeometry.{u} (m + k)) (hn : 0 < m + k) (φ : F.carrier → EReal)
    (hz : sourceGenericLelongNumber (n := m + k) (originalInclusion m k F) φ = 0) :
    (⨅ y, lelongNumber (n := m + k) φ (originalInclusion m k F y)) = 0 := by
  simp_rw [SquaredLogLelongSourceNormalization.lelongNumber_eq_two_mul_squaredLog hn.ne']
  rw [← ENNReal.mul_iInf_of_ne (by norm_num) (by norm_num)]
  change 2 * sourceGenericLelongNumber (n := m + k) (originalInclusion m k F) φ = 0
  rw [hz, mul_zero]

/-- Actual QEA restrictions and their native limit in the original iterated
restricted class. The generic-zero, stage restriction and convergence fields
are produced from the genuine original trace, never supplied as certificates. -/
theorem original_target_kahlerQEA_native_limit (m k : ℕ)
    (F : OriginalFlagGeometry.{u} (m + k))
    [MeasurableSpace (originalTail m k F).carrier] [BorelSpace (originalTail m k F).carrier]
    {θ : ClosedRealOneOneForm (m + k) F.carrier} {φ : F.carrier → EReal}
    {U : ℕ → F.carrier → EReal} (hU : IsKahlerQEA θ φ U)
    {κ : KahlerBackground (m + k) F.carrier}
    {ρ : (originalTail m k F).carrier → EReal}
    (hT : IsTraceRepresentativeAlong κ (originalTail m k F).omega
      (originalInclusion_contMDiff m k F) φ ρ)
    (hρ : IsThetaPshPotential (originalRestriction m k F θ).val ρ)
    (hbig : IsBigClass (RealBottChern.ofRepresentative (originalRestriction m k F θ))) :
    ∃ hr : ∀ j, IsThetaPshPotential (originalRestriction m k F θ).val
        (fun y => U j (originalInclusion m k F y)),
      Tendsto (fun j => (⟨fun y => U j (originalInclusion m k F y), hr j⟩ :
        ThetaPshL1 (originalRestriction m k F θ).val)) atTop
        (@nhds (ThetaPshL1 (originalRestriction m k F θ).val)
          (singularityPseudoMetricSpace (originalTail m k F).omega (originalRestriction m k F θ)
            hbig).toUniformSpace.toTopologicalSpace ⟨ρ,hρ⟩) := by
  let G := originalTail m k F
  have hι := originalInclusion_contMDiff m k F
  obtain ⟨omegaRef, ε, hfull⟩ := native_of_sourceQuasiEquisingularApproximation hU.1
  have hr (j : ℕ) : IsThetaPshPotential (originalRestriction m k F θ).val
      (fun y => U j (originalInclusion m k F y)) := by
    apply ((originalRestriction_geometricallyEq m k F θ).thetaPshPotential_iff _).mpr
    apply CompactAnalyticPoleLelongGap.isThetaPshPotential_comp_of_analytic_generic_inf_eq_zero
      hι (hU.2 j).1.1.1
    · intro x _
      exact hfull.term_hasAnalyticSingularityType j (complexChartAt (n := m + k) x)
        ((complexChartAt (n := m + k) x).val x)
        ((complexChartAt (n := m + k) x).val.map_source (mem_complexChartAt_source x))
    · exact AnalyticQuasiEquisingularRestriction.term_generic_lelong_inf_eq_zero
        hfull (originalInclusion m k F) hT.1 j
  have hTcopy := hT
  obtain ⟨hz, θ₀, δ, V, hV, β₀, hadm₀, hρ₀, hV₀, hlim₀⟩ := hTcopy
  obtain ⟨C, hC, hadmC, hmargin⟩ :=
    AdmissibleTraceBackgroundMargin.exists_admissible_background_with_uniform_margin
      hι omegaRef G.omega θ hfull.error_antitone
  let β : KahlerBackground m G.carrier := β₀.add (KahlerBackground.smul hC G.omega)
  have hβform : β.form = β₀.form + C • G.omega.form := rfl
  have hρβ : IsThetaPshPotential β.form.val ρ :=
    LocalPotentials.isThetaPshPotential_add_of_semipositive hρ₀
      (KahlerDomination.isSemipositive_smul G.omega.isSemipositive hC.le)
  have hadmβ : IsAdmissibleTraceBackground hι omegaRef θ ε β.form := by
    refine ⟨β.isKahler, fun j => ?_⟩
    have heq : β.form - ClosedRealOneOneForm.pullback hι (θ + ε j • omegaRef.form) =
        (C • G.omega.form - ClosedRealOneOneForm.pullback hι (θ + ε j • omegaRef.form)) + β₀.form := by
      rw [hβform]
      module
    change (β.form - ClosedRealOneOneForm.pullback hι (θ + ε j • omegaRef.form)).val.IsSemipositive
    rw [heq]
    exact UniformPerturbedKahlerLowerBound.isSemipositive_add (hadmC.2 j) β₀.isSemipositive
  obtain ⟨hUβ, hlimβ, hTout⟩ := TraceRepresentativeAllChoices.native_limit_of_isTraceRepresentativeAlong
    G.omega G.omega hι hT hfull β hadmβ hρβ
  refine ⟨hr, ?_⟩
  exact (SingularNativeCommonBackground.tendsto_native_iff_common_backgrounds
    G.omega (originalRestriction m k F θ) β.form hbig (isBigClass_kahler β) atTop
    hr hρ hUβ hρβ).mpr hlimβ
end SGPT.Okounkov.SourceMultiSlice
