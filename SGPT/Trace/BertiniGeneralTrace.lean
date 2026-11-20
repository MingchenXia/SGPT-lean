import SGPT.Trace.BertiniGeneralMember
import SGPT.Okounkov.SourceTraceOperations
import SGPT.PSH.SourceQuasiEquisingularCriterion
import SGPT.Foundations.Analysis.Pending.CalibratedQuasiEquisingularApproximation
import SGPT.Foundations.Analysis.Pending.FullQEANativeIGoodCriterion
import SGPT.Foundations.Analysis.Pending.IGoodPositiveBackgroundIndependence
import SGPT.Foundations.Analysis.Pending.IEnvelopeAnalytic
import SGPT.Foundations.Analysis.Pending.PositiveMassCurrentBelow
import SGPT.Foundations.Analysis.Pending.BoucksomMassBigness

/-!
# Traces along a single member: `cor:rest_gen_very_good` and `cor:tracegeneralwelldef`

Source: `chapter_trace.tex`, the proofs of `cor:rest_gen_very_good` and
`cor:tracegeneralwelldef` (blueprint `claude-bertini:rest-gen-very-good`,
`claude-bertini:tracegeneralwelldef`), for one target `ι : V → X` as in
`SGPT.Trace.BertiniGeneralMember`. The route differs from the book's: the book uses
`cor:ABTfortrace` (which needs the multiplier-ideal clause of `thm:Bert`); here both corollaries
follow from `lma:Igoodrest` applied to a quasi-equisingular approximation of an `𝓘`-good
potential, which converges to it in `d_S` (`thm:charIgoodasclosure`).

* `exists_iGood_trace_data`: for an `𝓘`-good `u`, a quasi-equisingular approximation `(U_j)`
  in a fixed background `θ` converging to `u` in `d_S`, together with the barriers of
  `lma:Igoodrest`;
* `isSourceTraceRepresentativeAlong_comp_of_iGood_data`: on every target where `u` and the
  barriers are not identically `-∞`, the ordinary restriction `u|_V` is a trace operator of `u`;
* `restriction_properties_of_iGood_data`: hence `u|_V` is `𝓘`-good, `ν(u, V) = 0` and every trace
  operator is `P`-equivalent to `u|_V` (items (ii)-(iv) of `cor:rest_gen_very_good`);
* `hasPositiveSourceTraceAlong_of_iEnvelope_trace`: if the restriction of `P_θ[φ]_𝓘` is a
  trace operator of `P_θ[φ]_𝓘` with positive mass, then `Tr^θ_V(φ)` is defined
  (`cor:tracegeneralwelldef`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal ContDiff

namespace SGPT.Trace.BertiniGeneral

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
  SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
  SGPT.Foundations.Analysis.FirstPass.IEnvelope
  SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.DiagonalMass
  SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination
  SGPT.Foundations.Analysis.Pending.SingularGlobalPOrder
  SGPT.Foundations.Analysis.Pending.SourceTraceRepresentativeDefinition

/-! ### Ambient data -/

section Ambient

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  [ConnectedSpace M]

/-- **`lma:kahcurrentposmass`, native form.** If `n > 0` and `u ∈ PSH(X,θ)_{>0}`, there are
`δ > 0` and `s ≤ u` with `s ∈ PSH(X, θ - δω)`, i.e. `θ_s` is a Kähler current. -/
theorem exists_kahlerCurrent_le (hn : 0 < n) (omega : KahlerBackground n M)
    {θ : ClosedRealOneOneForm n M} {u : M → EReal} (hu : IsThetaPshPotential θ.val u)
    (hpos : HasPositivePotentialMass θ u hu) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ s : M → EReal, IsThetaPshPotential (θ - δ • omega.form).val s ∧ s ≤ u :=
  PositiveMassCurrentBelow.exists_strict_thetaPsh_potential_le omega θ
    (BoucksomMassBigness.isBigClass_of_diagonalPotentialMass_pos hn omega θ hu hpos) hu hpos

/-- **The data of `cor:rest_gen_very_good` on `X`.** For an `𝓘`-good `u` there are a closed
real `(1,1)`-form `θ`, a quasi-equisingular approximation `(U_j)` of `u` in
`PSH(X, θ + ε_j ω)` with every `U_j ∈ PSH(X, θ)`, and barriers `η_m ∈ PSH(X, θ + ω)` with
`t_m U_j + (1 - t_m) η_m ≤ u` for some `j = j(m)`. (`U_j → u` in `d_S` by
`thm:charIgoodasclosure`; the barriers come from `lma:pathoenvelope`.) -/
theorem exists_iGood_trace_data (omega : KahlerBackground n M) {u : M → EReal}
    (hgood : IGood (n := n) u) :
    ∃ (θ : ClosedRealOneOneForm n M) (ε : ℕ → ℝ) (U η : ℕ → M → EReal),
      IsQuasiEquisingularApproximation omega θ u ε U ∧
      (∀ j, IsThetaPshPotential θ.val (U j)) ∧
      (∀ m, IsThetaPshPotential (θ + (1 : ℝ) • omega.form).val (η m)) ∧
      ∀ m : ℕ, ∃ j, convexComb (1 - ((m : ℝ) + 2)⁻¹) (U j) (η m) ≤ u := by
  obtain ⟨θ₁, hu₁, hgood₁⟩ := hgood
  have hu : IsThetaPshPotential (θ₁ + omega.form).val u :=
    LocalPotentials.isThetaPshPotential_add_of_semipositive hu₁ omega.isSemipositive
  have hgoodθ : IGoodWith (θ₁ + omega.form) u hu :=
    (IGoodPositiveBackgroundIndependence.iGoodWith_iff_add_kahler omega θ₁ hu₁
      hgood₁.positiveMass).mp hgood₁
  have hmargin : IsThetaPshPotential ((θ₁ + omega.form) - (1 : ℝ) • omega.form).val u := by
    rwa [one_smul, add_sub_cancel_right]
  obtain ⟨hbig, ε, U, happ, -, hU, -, -, -⟩ :=
    CalibratedQuasiEquisingularApproximation.exists_iEnvelope_native_analytic_approximation_of_current_margin
      omega (θ₁ + omega.form) one_pos hmargin
  have hg : IGoodWith (θ₁ + omega.form) u happ.target :=
    (iGoodWith_proof_independent _ u hu happ.target).mp hgoodθ
  have hlim := (FullQEANativeIGoodCriterion.native_qea_tendsto_target_iff_iGoodWith omega _ hbig
    happ hU hg.positiveMass).mpr hg
  have hle : ∀ j, u ≤ U j := fun j x =>
    (happ.term_antitone x).le_of_tendsto (happ.term_tendsto x) j
  obtain ⟨η, hη, hbar⟩ := exists_barriers_of_tendsto omega _ hbig hU happ.target hle hlim
  exact ⟨_, ε, U, η, happ, hU, hη, hbar⟩

end Ambient

/-! ### On the target -/

section Target

variable {n k : ℕ} {M V : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]
  {ι : V → M} (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)

/-- **`cor:rest_gen_very_good`, the trace on one member.** With the data of
`exists_iGood_trace_data`, if `u|_V ≢ -∞` and `η_m|_V ≢ -∞` for all `m`, then `U_j|_V → u|_V`
in `d_S` (`lma:Igoodrest`), so the ordinary restriction `u|_V` is a trace operator of `u`
along `V`. -/
theorem isSourceTraceRepresentativeAlong_comp_of_iGood_data (hn : n ≠ 0)
    (omega : KahlerBackground n M)
    (hpull : (ClosedRealOneOneForm.pullback hι omega.form).val.IsKahler)
    (omegaV : KahlerBackground k V) {θ : ClosedRealOneOneForm n M} {u : M → EReal}
    {ε : ℕ → ℝ} {U η : ℕ → M → EReal}
    (happ : IsQuasiEquisingularApproximation omega θ u ε U)
    (hU : ∀ j, IsThetaPshPotential θ.val (U j))
    (hη : ∀ m, IsThetaPshPotential (θ + (1 : ℝ) • omega.form).val (η m))
    (hbar : ∀ m : ℕ, ∃ j, convexComb (1 - ((m : ℝ) + 2)⁻¹) (U j) (η m) ≤ u)
    (hne : ∃ y, u (ι y) ≠ ⊥) (hηne : ∀ m, ∃ y, η m (ι y) ≠ ⊥) :
    IsSourceTraceRepresentativeAlong omega omegaV hι u (fun y => u (ι y)) := by
  have hle : ∀ j, u ≤ U j := fun j x =>
    (happ.term_antitone x).le_of_tendsto (happ.term_tendsto x) j
  have hconv := (tendstoSingularityType_comp_of_barriers hι omega hpull omegaV hU happ.target
    hle happ.term_antitone hη hbar hne hηne).2.2
  exact isSourceTraceRepresentativeAlong_comp_of_tendsto hι hn omega omegaV happ hU hne hconv

/-- **`cor:rest_gen_very_good`, items (ii)-(iv) on one member.** If the ordinary restriction
`u|_V` is a trace operator of `u` along `V`, then `u|_V` is `𝓘`-good, `ν(u, V) = 0`, and every
trace operator `τ` of `u` along `V` (with arbitrary auxiliary choices) satisfies
`τ ∼_P u|_V`. -/
theorem restriction_properties_of_trace [CompactSpace M] (hk : k ≤ n) {omega : KahlerBackground n M}
    {omegaV : KahlerBackground k V} {u : M → EReal}
    (htrace : IsSourceTraceRepresentativeAlong omega omegaV hι u (fun y => u (ι y))) :
    IGood (n := k) (fun y => u (ι y)) ∧ sourceGenericLelongNumber (n := n) ι u = 0 ∧
      ∀ (omega' : KahlerBackground n M) (omegaV' : KahlerBackground k V) (τ : V → EReal),
        IsSourceTraceRepresentativeAlong omega' omegaV' hι u τ →
          SourcePEquivalent (n := k) τ (fun y => u (ι y)) :=
  ⟨SGPT.Okounkov.iGood_of_sourceTraceRepresentative hk omegaV hι htrace, htrace.1,
    fun _ omegaV' _ hτ =>
      SGPT.Okounkov.sourcePEquivalent_of_sourceTraceRepresentatives hk omegaV' omegaV hι hτ htrace⟩

/-- **`cor:tracegeneralwelldef` on one member.** Let `φ ∈ PSH(X,θ)` with `φ|_V ≢ -∞` and
`ψ = P_θ[φ]_𝓘`. If the ordinary restriction `ψ|_V` is a trace operator of `ψ` along `V` and
`ψ|_V ∈ PSH(V, θ|_V)_{>0}`, then `ψ|_V` is a trace operator of `φ` along `V` (because
`φ ∼_𝓘 ψ`, `prop:tracelinear` and the closedness of traces under `∼_P`), so
`Tr^θ_V(φ)` is defined. -/
theorem hasPositiveSourceTraceAlong_of_iEnvelope_trace [CompactSpace M] (hk : k ≤ n)
    (hn : n ≠ 0) (omega : KahlerBackground n M) (omegaV : KahlerBackground k V)
    {θ : ClosedRealOneOneForm n M} {φ : M → EReal} (hφ : IsThetaPshPotential θ.val φ)
    (hne : ∃ y, φ (ι y) ≠ ⊥)
    (htrψ : IsSourceTraceRepresentativeAlong omega omegaV hι (iSingularityEnvelope θ.val φ)
      (fun y => iSingularityEnvelope θ.val φ (ι y)))
    (hψV : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι θ).val
      (fun y => iSingularityEnvelope θ.val φ (ι y)))
    (hψpos : HasPositivePotentialMass (ClosedRealOneOneForm.pullback hι θ)
      (fun y => iSingularityEnvelope θ.val φ (ι y)) hψV) :
    IsSourceTraceRepresentativeAlong omega omegaV hι φ
        (fun y => iSingularityEnvelope θ.val φ (ι y)) ∧
      HasPositiveSourceTraceAlong omega omegaV hι θ φ := by
  have : Nonempty M := ⟨ι (Classical.arbitrary V)⟩
  have hgeneric := sourceGenericLelongNumber_eq_zero (ι := ι) hn hφ hne
  obtain ⟨τ, hτ⟩ := SGPT.TraceOperations.exists_sourceTrace_of_globalQuasiPshPotential hk omega
    omegaV hφ.quasiPshPotential hι hgeneric
  have hI := iEquivalent_iSingularityEnvelope θ.val θ.property.1 θ.property.2
    hφ.1.hasSmoothLocalPotentials φ hφ
  have heq : SourcePEquivalent (n := k) τ (fun y => iSingularityEnvelope θ.val φ (ι y)) :=
    ⟨SGPT.TraceOperations.sourcePOrder_of_iOrder_of_sourceTraceRepresentatives hk omegaV omegaV hι hτ
        htrψ hI.1,
      SGPT.TraceOperations.sourcePOrder_of_iOrder_of_sourceTraceRepresentatives hk omegaV omegaV hι htrψ
        hτ hI.2⟩
  have htr := isSourceTraceRepresentativeAlong_of_sourcePEquivalent hι omega omegaV hτ hψV heq
  exact ⟨htr, _, htr, hψV, hψpos⟩

end Target

end SGPT.Trace.BertiniGeneral
