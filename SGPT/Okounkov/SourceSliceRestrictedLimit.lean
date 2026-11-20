import SGPT.Okounkov.SourceSliceOriginalAnalytic
import SGPT.Okounkov.SourceSliceAntitoneBody
import SGPT.Foundations.Analysis.Pending.TraceRepresentativeAllChoices
import SGPT.Foundations.Analysis.Pending.AdmissibleTraceBackgroundMargin
import SGPT.Foundations.Analysis.Pending.CompactAnalyticPoleLelongGap
import SGPT.Foundations.Analysis.Pending.SingularNativeCommonBackground

/-! The original restricted Kähler-QEA stages converge to the same original
trace reader in its actual restricted class. No convergence certificate is supplied. -/
set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Okounkov.SourceSlice
open Set Filter
open scoped Topology Manifold ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SGPT.Foundations.Analysis.FirstPass.TraceBackground
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.TraceRepresentativeConstruction
open SGPT.Foundations.Analysis.Pending.SourceTraceRepresentativeDefinition
open SGPT.Foundations.Analysis.Pending.PluripolarCapacityDichotomy
open SGPT.Foundations.Analysis.Pending.ThetaPshL1Topology
open SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityDistance
open SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.PartialBody
open SGPT.PSH SGPT.Okounkov.TranscendentalMain SGPT.Okounkov.TranscendentalWN

/-- The actual source generic-zero condition is the same zero native
Lelong infimum, with the genuine factor-two normalization retained. -/
theorem nativeGeneric_zero_of_source_zero {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1)) (φ : F.carrier → EReal)
    (hz : sourceGenericLelongNumber (n := m + 1)
      (Subtype.val : F.tail.carrier → F.carrier) φ = 0) :
    (⨅ y : F.tail.carrier, lelongNumber (n := m + 1) φ y.val) = 0 := by
  simp_rw [SquaredLogLelongSourceNormalization.lelongNumber_eq_two_mul_squaredLog
    (Nat.succ_ne_zero m)]
  rw [← ENNReal.mul_iInf_of_ne (by norm_num) (by norm_num)]
  change 2 * sourceGenericLelongNumber (n := m + 1)
    (Subtype.val : F.tail.carrier → F.carrier) φ = 0
  rw [hz, mul_zero]

/-- Every actual source Kähler QEA has genuine original-class restrictions,
and their native limit is the given genuine trace reader. Approximation
independence and background transport produce the convergence internally. -/
theorem restricted_kahlerQEA_native_limit
    {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 2))
    [MeasurableSpace F.tail.carrier] [BorelSpace F.tail.carrier]
    {θ : ClosedRealOneOneForm (m + 2) F.carrier} {φ : F.carrier → EReal}
    {U : ℕ → F.carrier → EReal} (hU : IsKahlerQEA θ φ U)
    {κ : KahlerBackground (m + 2) F.carrier} {ρ : F.tail.carrier → EReal}
    (hT : IsTraceRepresentativeAlong κ F.tail.omega
      (contMDiff_firstFlagInclusion F) φ ρ)
    (hρ : IsThetaPshPotential (firstFlagRestriction F θ).val ρ)
    (hbig : IsBigClass (RealBottChern.ofRepresentative (firstFlagRestriction F θ))) :
    ∃ hr : ∀ j, IsThetaPshPotential (firstFlagRestriction F θ).val
        (fun y : F.tail.carrier => U j y.val),
      Tendsto (fun j => (⟨fun y : F.tail.carrier => U j y.val, hr j⟩ :
        ThetaPshL1 (firstFlagRestriction F θ).val)) atTop
        (@nhds (ThetaPshL1 (firstFlagRestriction F θ).val)
          (singularityPseudoMetricSpace F.tail.omega (firstFlagRestriction F θ)
            hbig).toUniformSpace.toTopologicalSpace ⟨ρ, hρ⟩) := by
  obtain ⟨ω, ε, hfull⟩ := native_of_sourceQuasiEquisingularApproximation hU.1
  have hι := contMDiff_firstFlagInclusion F
  have hr (j : ℕ) : IsThetaPshPotential (firstFlagRestriction F θ).val
      (fun y : F.tail.carrier => U j y.val) := by
    apply CompactAnalyticPoleLelongGap.isThetaPshPotential_comp_of_analytic_generic_inf_eq_zero
      hι (hU.2 j).1.1.1
    · intro x _
      exact hfull.term_hasAnalyticSingularityType j (complexChartAt (n := m + 2) x)
        ((complexChartAt (n := m + 2) x).val x)
        ((complexChartAt (n := m + 2) x).val.map_source (mem_complexChartAt_source x))
    · exact AnalyticQuasiEquisingularRestriction.term_generic_lelong_inf_eq_zero
        hfull (firstFlagInclusion F) hT.1 j
  have hTcopy := hT
  obtain ⟨hz, θ₀, δ, V, hV, β₀, hadm₀, hρ₀, hV₀, hlim₀⟩ := hTcopy
  obtain ⟨C, hC, hadmC, hmargin⟩ :=
    AdmissibleTraceBackgroundMargin.exists_admissible_background_with_uniform_margin
      hι ω F.tail.omega θ hfull.error_antitone
  let β : KahlerBackground (m + 1) F.tail.carrier :=
    β₀.add (KahlerBackground.smul hC F.tail.omega)
  have hβform : β.form = β₀.form + C • F.tail.omega.form := rfl
  have hρβ : IsThetaPshPotential β.form.val ρ :=
    LocalPotentials.isThetaPshPotential_add_of_semipositive hρ₀
      (KahlerDomination.isSemipositive_smul F.tail.omega.isSemipositive hC.le)
  have hadmβ : IsAdmissibleTraceBackground hι ω θ ε β.form := by
    refine ⟨β.isKahler, fun j => ?_⟩
    have heq : β.form - ClosedRealOneOneForm.pullback hι (θ + ε j • ω.form) =
        (C • F.tail.omega.form - ClosedRealOneOneForm.pullback hι (θ + ε j • ω.form)) +
          β₀.form := by rw [hβform]; module
    change (β.form - ClosedRealOneOneForm.pullback hι (θ + ε j • ω.form)).val.IsSemipositive
    rw [heq]
    exact UniformPerturbedKahlerLowerBound.isSemipositive_add (hadmC.2 j) β₀.isSemipositive
  obtain ⟨hUβ, hlimβ, hTout⟩ := TraceRepresentativeAllChoices.native_limit_of_isTraceRepresentativeAlong
    F.tail.omega F.tail.omega hι hT hfull β hadmβ hρβ
  refine ⟨hr, ?_⟩
  exact (SingularNativeCommonBackground.tendsto_native_iff_common_backgrounds
    F.tail.omega (firstFlagRestriction F θ) β.form hbig (isBigClass_kahler β) atTop
    hr hρ hUβ hρβ).mpr hlimβ
end SGPT.Okounkov.SourceSlice
