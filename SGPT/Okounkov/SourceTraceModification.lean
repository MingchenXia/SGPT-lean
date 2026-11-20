import SGPT.Okounkov.ModificationQuasiEquisingular
import SGPT.Okounkov.SourceTraceChoices
import SGPT.Okounkov.FlagCorrection
import SGPT.Okounkov.FlagLiftingStrictTransform
import SGPT.Foundations.Analysis.Pending.AdmissibleTraceBackgroundMargin
import SGPT.Foundations.Analysis.Pending.SingularNativeCommonBackground

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Okounkov

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.FirstPass.TraceBackground
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SGPT.Foundations.Analysis.Pending SourceTraceRepresentativeDefinition
open AnalyticModificationLocalDiscrepancy AnalyticModificationStrongPullback
open SingularCanonicalSingularityDistance ThetaPshL1Topology
open SingularGlobalPOrder PluripolarCapacityDichotomy

variable {n k : ℕ} {X Z V W : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]
  [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]
  [MeasurableSpace Z] [BorelSpace Z]
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]
  [TopologicalSpace W] [ChartedSpace (ComplexModel k) W] [IsComplexManifold k W]
  [MeasurableSpace W] [BorelSpace W] [CompactSpace W] [ConnectedSpace W]

/-- Arbitrary genuine recorded source data internally construct the literal
pulled trace through the actual commuting modifications and restricted maps. -/
theorem exists_sourceTraceRepresentative_modification_of_commuting
    {π : Z → X} (hπ : IsAnalyticModification (n := n) π)
    {pTail : W → V} (hpTail : IsAnalyticModification (n := k) pTail)
    (omegaX : KahlerBackground n X) (omegaZ : KahlerBackground n Z)
    (omegaV : KahlerBackground k V) (omegaW : KahlerBackground k W)
    {ιV : V → X} (hιV : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ιV)
    {ιW : W → Z} (hιW : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ιW)
    (hcomm : ∀ w, π (ιW w) = ιV (pTail w))
    {u : X → EReal} {τ : V → EReal}
    (htrace : IsSourceTraceRepresentativeAlong omegaX omegaV hιV u τ)
    (hzero : sourceGenericLelongNumber (n := n) ιW (u ∘ π) = 0) :
    ∃ κ : KahlerBackground n Z,
      IsSourceTraceRepresentativeAlong κ omegaW hιW (u ∘ π) (τ ∘ pTail) := by
  obtain ⟨_hzeroV, θ, ε, U, hqea, β, _hadmβ, hτβ, hUβ, hlimβ⟩ := htrace
  obtain ⟨κ, hqeaπ⟩ := exists_quasiEquisingularApproximation_modification
    hπ omegaX omegaZ θ hqea
  let θπ := ClosedRealOneOneForm.pullback hπ.1 θ
  obtain ⟨C, hC, hadmC, _hmarginC⟩ :=
    AdmissibleTraceBackgroundMargin.exists_admissible_background_with_uniform_margin
      hιW κ omegaW θπ hqeaπ.error_antitone
  let σ := ClosedRealOneOneForm.pullback hpTail.1 β.form
  have hσsemi : σ.val.IsSemipositive :=
    ClosedRealOneOneForm.pullback_isSemipositive hpTail.1 β.isSemipositive
  have hCsemi := KahlerDomination.isSemipositive_smul omegaW.isSemipositive hC.le
  have hΓK : (σ + (C + 1) • omegaW.form).val.IsKahler :=
    KahlerDomination.isKahler_add_smul_succ omegaW (by
      intro e z hz v
      simpa only [ClosedRealOneOneForm.coeff_add, ContinuousAlternatingMap.add_apply] using
        add_nonneg (hσsemi e z hz v) (hCsemi e z hz v))
  let Γ : KahlerBackground k W := ⟨σ + (C + 1) • omegaW.form, hΓK⟩
  have hΓadm : IsAdmissibleTraceBackground hιW κ θπ ε Γ.form := by
    refine ⟨Γ.isKahler, ?_⟩
    intro j
    have heq : Γ.form - ClosedRealOneOneForm.pullback hιW (θπ + ε j • κ.form) =
        σ + (C • omegaW.form -
          ClosedRealOneOneForm.pullback hιW (θπ + ε j • κ.form)) + omegaW.form := by
      dsimp only [Γ]
      module
    rw [FormDominates, heq]
    intro e z hz v
    simpa only [ClosedRealOneOneForm.coeff_add, ContinuousAlternatingMap.add_apply] using
      add_nonneg (add_nonneg (hσsemi e z hz v) (hadmC.2 j e z hz v))
        (omegaW.isSemipositive e z hz v)
  let Up : ℕ → W → EReal := fun j w => U j (π (ιW w))
  have hUσ (j : ℕ) : IsThetaPshPotential σ.val (Up j) := by
    simpa only [Up, hcomm, Function.comp_def] using
      isThetaPshPotential_comp_of_isAnalyticModification hpTail β.form (hUβ j)
  have hτσ : IsThetaPshPotential σ.val (τ ∘ pTail) :=
    isThetaPshPotential_comp_of_isAnalyticModification hpTail β.form hτβ
  have hσbig : IsBigClass (RealBottChern.ofRepresentative σ) :=
    isBigClass_modification_pullback hpTail omegaV omegaW β.form (isBigClass_kahler β)
  let Ui : ℕ → ThetaPshL1 β.form.val := fun j => ⟨fun v => U j (ιV v), hUβ j⟩
  let Vi : ThetaPshL1 β.form.val := ⟨τ, hτβ⟩
  have hlimσ : Tendsto (fun j => (⟨Up j, hUσ j⟩ : ThetaPshL1 σ.val)) atTop
      (@nhds (ThetaPshL1 σ.val)
        (singularityPseudoMetricSpace omegaW σ hσbig).toUniformSpace.toTopologicalSpace
        ⟨τ ∘ pTail, hτσ⟩) := by
    have hlim := (native_tendsto_modification_pullback_iff hpTail omegaV omegaW
      β.form (isBigClass_kahler β) atTop Ui Vi).mpr hlimβ
    change Tendsto (fun j =>
      (⟨fun w => U j (ιV (pTail w)),
        isThetaPshPotential_comp_of_isAnalyticModification hpTail β.form (hUβ j)⟩ :
        ThetaPshL1 σ.val)) atTop
      (@nhds (ThetaPshL1 σ.val)
        (singularityPseudoMetricSpace omegaW σ hσbig).toUniformSpace.toTopologicalSpace
        ⟨τ ∘ pTail, hτσ⟩) at hlim
    refine hlim.congr' (Eventually.of_forall fun j => ?_)
    apply Subtype.ext
    funext w
    exact congrArg (U j) (hcomm w).symm
  have hΓsemi : (Γ.form - σ).val.IsSemipositive := by
    have heq : Γ.form - σ = (C + 1) • omegaW.form := by
      dsimp only [Γ]
      module
    rw [heq]
    exact KahlerDomination.isSemipositive_smul omegaW.isSemipositive (by linarith)
  have hUΓ (j : ℕ) : IsThetaPshPotential Γ.form.val (Up j) := by
    have heq : σ + (Γ.form - σ) = Γ.form := by module
    simpa only [heq] using
      LocalPotentials.isThetaPshPotential_add_of_semipositive (hUσ j) hΓsemi
  have hτΓ : IsThetaPshPotential Γ.form.val (τ ∘ pTail) := by
    have heq : σ + (Γ.form - σ) = Γ.form := by module
    simpa only [heq] using
      LocalPotentials.isThetaPshPotential_add_of_semipositive hτσ hΓsemi
  have hlimΓ := (SingularNativeCommonBackground.tendsto_native_iff_common_backgrounds
    omegaW σ Γ.form hσbig (isBigClass_kahler Γ) atTop hUσ hτσ hUΓ hτΓ).mp hlimσ
  exact ⟨κ, hzero, θπ, ε, (fun j => U j ∘ π), hqeaπ, Γ, hΓadm,
    hτΓ, hUΓ, hlimΓ⟩

/-- An arbitrary genuine recorded upstairs trace is compared with the
internally produced literal pulled trace, without a trace-equivalence input. -/
theorem sourcePEquivalent_modification_of_sourceTraceRepresentatives
    (hk : k ≤ n) {π : Z → X} (hπ : IsAnalyticModification (n := n) π)
    {pTail : W → V} (hpTail : IsAnalyticModification (n := k) pTail)
    (omegaX : KahlerBackground n X) (omegaZ : KahlerBackground n Z)
    (omegaV : KahlerBackground k V) (omegaW omegaW' : KahlerBackground k W)
    {ιV : V → X} (hιV : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ιV)
    {ιW : W → Z} (hιW : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ιW)
    (hcomm : ∀ w, π (ιW w) = ιV (pTail w))
    {u : X → EReal} {τ : V → EReal} {ρ : W → EReal}
    (htraceV : IsSourceTraceRepresentativeAlong omegaX omegaV hιV u τ)
    (htraceW : IsSourceTraceRepresentativeAlong omegaZ omegaW' hιW (u ∘ π) ρ) :
    SourcePEquivalent (n := k) (τ ∘ pTail) ρ := by
  let : CompactSpace Z := compactSpace_of_isAnalyticModification hπ
  obtain ⟨κ, htraceP⟩ := exists_sourceTraceRepresentative_modification_of_commuting
    hπ hpTail omegaX omegaZ omegaV omegaW hιV hιW hcomm htraceV htraceW.1
  exact sourcePEquivalent_of_sourceTraceRepresentatives hk omegaW omegaW' hιW htraceP htraceW

/-- In the actual smooth-flag targets, the genuine tail modification and
literal inclusions supply the commuting diagram for arbitrary original traces. -/
theorem IsFlagLifting.sourcePEquivalent_first_sourceTrace_pullback {m : ℕ}
    {F G : OriginalFlagGeometry.{u} (m + 1)} {π : G.carrier → F.carrier}
    (hπ : IsFlagLifting F G π) {u : F.carrier → EReal}
    {τ : F.tail.carrier → EReal} {ρ : G.tail.carrier → EReal}
    (hτ : NaturalSubmanifoldSourceTraceDefinition.IsNaturalSourceTraceRepresentative
      F.omega F.firstDivisor u τ)
    (hρ : NaturalSubmanifoldSourceTraceDefinition.IsNaturalSourceTraceRepresentative
      G.omega G.firstDivisor (u ∘ π) ρ) :
    let : MeasurableSpace G.tail.carrier := borel G.tail.carrier
    let : BorelSpace G.tail.carrier := ⟨rfl⟩
    SourcePEquivalent (n := m) (τ ∘ hπ.tailMap) ρ := by
  let : MeasurableSpace F.carrier := borel F.carrier
  let : BorelSpace F.carrier := ⟨rfl⟩
  let : MeasurableSpace G.carrier := borel G.carrier
  let : BorelSpace G.carrier := ⟨rfl⟩
  let : MeasurableSpace F.tail.carrier := borel F.tail.carrier
  let : BorelSpace F.tail.carrier := ⟨rfl⟩
  let : MeasurableSpace G.tail.carrier := borel G.tail.carrier
  let : BorelSpace G.tail.carrier := ⟨rfl⟩
  let hιF := SubmanifoldChartedSpace.contMDiff_val (Nat.le_succ m) F.firstDivisor.2.2
  let hιG := SubmanifoldChartedSpace.contMDiff_val (Nat.le_succ m) G.firstDivisor.2.2
  change SourcePEquivalent (n := m) (τ ∘ hπ.tailMap) ρ
  change IsSourceTraceRepresentativeAlong F.omega F.tail.omega hιF u τ at hτ
  change IsSourceTraceRepresentativeAlong G.omega G.tail.omega hιG (u ∘ π) ρ at hρ
  exact sourcePEquivalent_modification_of_sourceTraceRepresentatives (Nat.le_succ m)
    hπ.1 hπ.tailMap_isFlagLifting.1 F.omega G.omega F.tail.omega
    G.tail.omega G.tail.omega hιF hιG (fun _ => rfl) hτ hρ

end SGPT.Okounkov
