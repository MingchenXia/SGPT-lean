import SGPT.PSH.QuasiEquisingular
import SGPT.Okounkov.ModificationNativeConvergence
import SGPT.Okounkov.IEnvelopeModification
import SGPT.Foundations.Analysis.Pending.QuasiEquisingularIEnvelopeNativeLimit
import SGPT.Foundations.Analysis.Pending.QuasiEquisingularBackgroundDomination
import SGPT.Foundations.Analysis.Pending.NativeStrictGapMultiplierInclusion
import SGPT.Foundations.Analysis.Pending.GenuineMultiplierIdealChartInclusion
import SGPT.Foundations.Analysis.Pending.AnalyticTypeHolomorphicPullback
import SGPT.Foundations.Analysis.Pending.DominationIntersectionNumbers

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Okounkov

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Foundations.Analysis.Pending
open AnalyticModificationLocalDiscrepancy AnalyticModificationStrongPullback
open SingularCanonicalSingularityDistance ThetaPshL1Topology
open DiagonalMass

variable {n : ℕ} {X Y : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  [MeasurableSpace Y] [BorelSpace Y]

/-- All genuine original QEA terms and the true target internally enter one
fixed positive big background with their actual I-envelope native limit. -/
theorem exists_fixed_positive_qea_native_limit
    (omega : KahlerBackground n X) (θ : ClosedRealOneOneForm n X)
    {u : X → EReal} {ε : ℕ → ℝ} {U : ℕ → X → EReal}
    (h : IsQuasiEquisingularApproximation omega θ u ε U) :
    ∃ (β : ClosedRealOneOneForm n X)
      (hbig : IsBigClass (RealBottChern.ofRepresentative β))
      (huβ : IsThetaPshPotential β.val u)
      (hUβ : ∀ j, IsThetaPshPotential β.val (U j)),
      HasPositivePotentialMass β u huβ ∧
      ∃ hE : IsThetaPshPotential β.val (iSingularityEnvelope β.val u),
        Tendsto (fun j => (⟨U j, hUβ j⟩ : ThetaPshL1 β.val))
          atTop (@nhds (ThetaPshL1 β.val)
            (singularityPseudoMetricSpace omega β hbig).toUniformSpace.toTopologicalSpace
            ⟨iSingularityEnvelope β.val u, hE⟩) := by
  let A : ℝ := ε 0 + 1
  have hA : 0 < A := by dsimp [A]; linarith [h.error_nonneg 0]
  let β : ClosedRealOneOneForm n X := θ + A • omega.form
  have huβ : IsThetaPshPotential β.val u :=
    LocalPotentials.isThetaPshPotential_add_of_semipositive h.target
      (KahlerDomination.isSemipositive_smul omega.isSemipositive hA.le)
  have hUβ (j : ℕ) : IsThetaPshPotential β.val (U j) := by
    have hj : 0 ≤ A - ε j := by
      have hle := h.error_antitone (Nat.zero_le j)
      dsimp [A]
      linarith
    have hform : θ + ε j • omega.form + (A - ε j) • omega.form = β := by
      dsimp only [β]
      module
    simpa only [hform] using LocalPotentials.isThetaPshPotential_add_of_semipositive
      (h.term j) (KahlerDomination.isSemipositive_smul omega.isSemipositive hj)
  have hsemi : (β - θ).val.IsSemipositive := by
    have hform : β - θ = A • omega.form := by dsimp only [β]; module
    rw [hform]
    exact KahlerDomination.isSemipositive_smul omega.isSemipositive hA.le
  have hβ : IsQuasiEquisingularApproximation omega β u ε U :=
    QuasiEquisingularBackgroundDomination.isQuasiEquisingularApproximation_of_background_domination
      h hsemi
  have hbig : IsBigClass (RealBottChern.ofRepresentative β) :=
    PositiveCurrentAssembly.isBigClass_add_smul_of_isThetaPshPotential omega θ h.target hA
  have hpos : HasPositivePotentialMass β u huβ :=
    SingularPositiveCommonBackgroundExistence.hasPositivePotentialMass_add_smul omega h.target hA
  obtain ⟨_, hE, _, hlim⟩ :=
    QuasiEquisingularIEnvelopeNativeLimit.iInf_envelopes_eq_iEnvelope_and_native_limit
      omega β hbig hβ hUβ hpos
  exact ⟨β, hbig, huβ, hUβ, hpos, hE, hlim⟩

/-- The original QEA, genuine modification and actual native strict-gap
producer manufacture the entire weighted multiplier tail in every upstairs chart. -/
theorem eventually_multiplierIdealIncluded_modification_of_qea
    {π : Y → X} (hπ : IsAnalyticModification (n := n) π)
    (omegaX : KahlerBackground n X) (omegaY : KahlerBackground n Y)
    (θ : ClosedRealOneOneForm n X)
    {u : X → EReal} {ε : ℕ → ℝ} {U : ℕ → X → EReal}
    (h : IsQuasiEquisingularApproximation omegaX θ u ε U)
    {c d : ℝ} (hc : 0 < c) (hcd : c < d) :
    ∀ᶠ j in atTop, MultiplierIdealIncluded (n := n) (U j ∘ π) d (u ∘ π) c := by
  let : CompactSpace Y := compactSpace_of_isAnalyticModification hπ
  let : ConnectedSpace Y := connectedSpace_iff_univ.mpr (by
    have hconn := AnalyticModificationConnectedFibres.isConnected_preimage_of_isConnected
      hπ (⟨univ, isOpen_univ⟩ : TopologicalSpace.Opens X) isConnected_univ
    change IsConnected (π ⁻¹' (univ : Set X)) at hconn
    simpa only [preimage_univ] using hconn)
  obtain ⟨β, hbig, huβ, hUβ, _hpos, hE, hlim⟩ :=
    exists_fixed_positive_qea_native_limit omegaX θ h
  let βπ := ClosedRealOneOneForm.pullback hπ.1 β
  let hbigπ := isBigClass_modification_pullback hπ omegaX omegaY β hbig
  let Ui : ℕ → ThetaPshL1 β.val := fun j => ⟨U j, hUβ j⟩
  let V : ThetaPshL1 β.val := ⟨iSingularityEnvelope β.val u, hE⟩
  let Uπ : ℕ → ThetaPshL1 βπ.val := fun j =>
    ⟨U j ∘ π, isThetaPshPotential_comp_of_isAnalyticModification hπ β (hUβ j)⟩
  let Vπ : ThetaPshL1 βπ.val :=
    ⟨iSingularityEnvelope β.val u ∘ π,
      isThetaPshPotential_comp_of_isAnalyticModification hπ β hE⟩
  have hlimπ : Tendsto Uπ atTop (@nhds (ThetaPshL1 βπ.val)
      (singularityPseudoMetricSpace omegaY βπ hbigπ).toUniformSpace.toTopologicalSpace Vπ) :=
    (native_tendsto_modification_pullback_iff hπ omegaX omegaY β hbig atTop Ui V).mpr hlim
  have htail := NativeStrictGapMultiplierInclusion.eventually_multiplierIdeal_le_of_native_limit
    omegaY βπ hbigπ atTop Uπ Vπ hc hcd hlimπ
  have hup : IsThetaPshPotential βπ.val (u ∘ π) :=
    isThetaPshPotential_comp_of_isAnalyticModification hπ β huβ
  have henv : iSingularityEnvelope βπ.val (u ∘ π) =
      iSingularityEnvelope β.val u ∘ π :=
    iSingularityEnvelope_modification_pullback hπ β huβ
  have hIE : IOrderOnManifold (n := n) (iSingularityEnvelope β.val u ∘ π) (u ∘ π) := by
    have he := (iEquivalent_iSingularityEnvelope βπ.val βπ.property.1 βπ.property.2
      hup.1.hasSmoothLocalPotentials (u ∘ π) hup).2
    simpa only [henv] using he
  have hle := PositiveCurrentTraceMultiplier.multiplierIdeal_le_of_iOrderOnManifold hIE hc
  filter_upwards [htail] with j hj
  apply GenuineMultiplierIdealChartInclusion.multiplierIdealIncluded_of_multiplierIdeal_le
    (Uπ j).property.1 hup.1 (hc.trans hcd) hc
  exact fun x g hg => hle x g (hj x g hg)

/-- All genuine full approximation clauses under modification, with the
actual original functions and errors and an internally dominated auxiliary form. -/
theorem exists_quasiEquisingularApproximation_modification
    {π : Y → X} (hπ : IsAnalyticModification (n := n) π)
    (omegaX : KahlerBackground n X) (omegaY : KahlerBackground n Y)
    (θ : ClosedRealOneOneForm n X)
    {u : X → EReal} {ε : ℕ → ℝ} {U : ℕ → X → EReal}
    (h : IsQuasiEquisingularApproximation omegaX θ u ε U) :
    ∃ κ : KahlerBackground n Y,
      IsQuasiEquisingularApproximation κ (ClosedRealOneOneForm.pullback hπ.1 θ)
        (u ∘ π) ε (fun j => U j ∘ π) := by
  let : CompactSpace Y := compactSpace_of_isAnalyticModification hπ
  let ωπ := ClosedRealOneOneForm.pullback hπ.1 omegaX.form
  obtain ⟨C, hC, hsemi⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul omegaY (-ωπ)
  let κ : KahlerBackground n Y := KahlerBackground.smul hC omegaY
  have hκ : (κ.form - ωπ).val.IsSemipositive := by
    have hform : -ωπ + C • omegaY.form = κ.form - ωπ := by
      dsimp only [κ, KahlerBackground.smul_form]
      module
    simpa only [hform] using hsemi
  refine ⟨κ, isThetaPshPotential_comp_of_isAnalyticModification hπ θ h.target,
    h.error, ?_, ?_, ?_, ?_⟩
  · intro j
    have hform : ClosedRealOneOneForm.pullback hπ.1 (θ + ε j • omegaX.form) +
        ε j • (κ.form - ωπ) = ClosedRealOneOneForm.pullback hπ.1 θ + ε j • κ.form := by
      rw [DominationIntersectionNumbers.pullback_add_smul]
      dsimp only [ωπ]
      module
    simpa only [hform, Function.comp_def] using LocalPotentials.isThetaPshPotential_add_of_semipositive
      (isThetaPshPotential_comp_of_isAnalyticModification hπ (θ + ε j • omegaX.form) (h.term j))
      (KahlerDomination.isSemipositive_smul hκ (h.error_nonneg j))
  · intro j
    exact AnalyticTypeHolomorphicPullback.hasManifoldAnalyticSingularityType_comp hπ.1
      (h.term_hasAnalyticSingularityType j)
  · exact ⟨fun y => h.term_antitone (π y), fun y => h.term_tendsto (π y)⟩
  · intro c d hc hcd
    exact eventually_multiplierIdealIncluded_modification_of_qea hπ omegaX omegaY θ h hc hcd

/-- The whole original source QEA pullback theorem, preserving every
original approximant and its values, including zero dimension and poles. -/
theorem sourceQuasiEquisingularApproximation_modification_pullback
    {π : Y → X} (hπ : IsAnalyticModification (n := n) π)
    (omegaY : KahlerBackground n Y) (θ : ClosedRealOneOneForm n X)
    {u : X → EReal} {U : ℕ → X → EReal}
    (h : SGPT.PSH.SourceQuasiEquisingularApproximation θ u U) :
    SGPT.PSH.SourceQuasiEquisingularApproximation (ClosedRealOneOneForm.pullback hπ.1 θ)
      (u ∘ π) (fun j => U j ∘ π) := by
  obtain ⟨omegaX, ε, happ⟩ := SGPT.PSH.native_of_sourceQuasiEquisingularApproximation h
  obtain ⟨κ, hκ⟩ := exists_quasiEquisingularApproximation_modification
    hπ omegaX omegaY θ happ
  exact SGPT.PSH.sourceQuasiEquisingularApproximation_of_native hκ

end SGPT.Okounkov
