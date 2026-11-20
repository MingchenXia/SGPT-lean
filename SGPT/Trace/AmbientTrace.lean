import SGPT.Trace.SmoothTarget
import SGPT.PSH.SourceQuasiEquisingularCriterion
import SGPT.Okounkov.SourceTraceChoices
import SGPT.Foundations.Analysis.Pending.QuasiEquisingularApproximationDemailly
import SGPT.Foundations.Analysis.Pending.AdmissibleTraceBackgroundMargin
import SGPT.Foundations.Analysis.Pending.AnalyticQuasiEquisingularRestriction
import SGPT.Foundations.Analysis.Pending.SingularNativeCommonBackground
import SGPT.Foundations.Analysis.Pending.UniformPerturbedKahlerLowerBound

/-!
# The trace operator along the whole manifold

Source `ex:trace:L236` (`chapter_trace.tex`): let `φ ∈ QPSH(X)` and let `θ` be a closed
real smooth `(1,1)`-form with `φ ∈ PSH(X,θ)_{>0}`. Then
`Tr_X(φ) ∼_P P_θ[φ]_𝓘` and `Tr^θ_X(φ) = P_θ[φ]_𝓘`.

Here `Y = X`, whose normalization is `X` itself with the identity map, so the trace is
the source trace predicate along `id : X → X` (the target `X` carries its own complex
structure and an arbitrary Kähler background).

Main results:

* `SGPT.Trace.sourceGenericLelongNumber_id_eq_zero`: `ν(φ, X) = 0` for every
  `θ`-psh potential, so the trace along `X` is always defined;
* `SGPT.Trace.isSourceTraceRepresentativeAlong_id_iEnvelope`: `P_θ[φ]_𝓘` itself is a
  trace operator of `φ` along `X`;
* `SGPT.Trace.sourcePEquivalent_trace_id_iEnvelope`: every trace operator `τ` of `φ`
  along `X` satisfies `τ ∼_P P_θ[φ]_𝓘`;
* `SGPT.Trace.singularityEnvelope_trace_id_eq_iEnvelope`: for every trace operator
  `τ ∈ PSH(X,θ)_{>0}`, `Tr^θ_X(φ) = P_θ[τ] = P_θ[φ]_𝓘`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology Manifold ENNReal ContDiff

namespace SGPT.Trace

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
  SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
  SGPT.Foundations.Analysis.FirstPass.TraceBackground
  SGPT.Foundations.Analysis.FirstPass.IEnvelope
  SGPT.Foundations.Analysis.Pending
  SourceTraceRepresentativeDefinition TraceRepresentativeConstruction
  SquaredLogLelongSourceNormalization SingularGlobalPOrder ThetaPshL1Topology
  SingularCanonicalSingularityDistance PluripolarCapacityDichotomy DiagonalMass
open SGPT.PSH SGPT.PSH.VariableComplexAtlas

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- A `θ`-psh potential has generic Lelong number `0` along the whole manifold:
`ν(φ, X) = 0`. -/
theorem sourceGenericLelongNumber_id_eq_zero [Nonempty M] {θ : ClosedRealOneOneForm n M}
    {u : M → EReal} (hu : IsThetaPshPotential θ.val u) :
    sourceGenericLelongNumber (n := n) (id : M → M) u = 0 := by
  by_cases hn : n = 0
  · subst n
    exact sourceGenericLelongNumber_zero_dimension rfl id u
  obtain ⟨x, -, hx⟩ := hu.2 (Classical.arbitrary M) univ isOpen_univ (mem_univ _)
  have hzero : lelongNumber (n := n) u x = 0 := by
    by_contra hne
    exact hx (eq_bot_of_lelongNumber_pos (Nat.pos_of_ne_zero hn) hu.1 (pos_iff_ne_zero.mpr hne))
  apply (nativeGeneric_zero_iff_source hn id u).mp
  exact le_antisymm ((iInf_le _ x).trans_eq hzero) bot_le

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

/-- Source `ex:trace:L236`, existence and identification: if `φ ∈ PSH(X,θ)_{>0}`, then
the `𝓘`-envelope `P_θ[φ]_𝓘` is a trace operator of `φ` along `X` (for every auxiliary
Kähler form `omega` of the approximation and every Kähler background `omegaX` of the
target `X`). -/
theorem isSourceTraceRepresentativeAlong_id_iEnvelope
    (omega omegaX : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    {u : M → EReal} (hu : IsThetaPshPotential θ.val u)
    (hpos : HasPositivePotentialMass θ u hu) :
    IsSourceTraceRepresentativeAlong omega omegaX
      (contMDiff_id : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (id : M → M))
      u (iSingularityEnvelope θ.val u) := by
  let hι : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (id : M → M) := contMDiff_id
  have hgen := sourceGenericLelongNumber_id_eq_zero hu
  obtain ⟨ε, U, happ⟩ :=
    QuasiEquisingularApproximationDemailly.exists_quasiEquisingularApproximation omega θ hu
  -- an admissible Kähler background on the target containing every restricted term
  obtain ⟨C, hC, hadm, -⟩ :=
    AdmissibleTraceBackgroundMargin.exists_admissible_background_with_uniform_margin
      hι omega omegaX θ happ.error_antitone
  let β₀ : KahlerBackground n M := KahlerBackground.smul hC omegaX
  have hterms₀ (j : ℕ) : IsThetaPshPotential β₀.form.val (fun y => U j (id y)) := by
    by_cases hn : n = 0
    · subst n
      have hfin : ∀ y, U j y ≠ ⊤ ∧ U j y ≠ ⊥ := fun y =>
        ⟨(happ.term j).1.quasiPlurisubharmonic.ne_top y,
          RooftopDimZero.ne_bot_of_locallyNondegenerate_of_dim_zero rfl (happ.term j).2 y⟩
      exact RooftopDimZero.isThetaPshPotential_of_dim_zero rfl
        (LocalPotentials.closedRealOneOne_hasLocalPotentials β₀.form)
        (fun y => (hfin y).1) (fun y => (hfin y).2)
    have hp := AnalyticQuasiEquisingularRestriction.isThetaPshPotential_ordinaryRestriction_term
      happ hι ((nativeGeneric_zero_iff_source hn id u).mpr hgen) j
    have hform : ClosedRealOneOneForm.pullback hι (θ + ε j • omega.form) +
        (C • omegaX.form - ClosedRealOneOneForm.pullback hι (θ + ε j • omega.form)) =
        β₀.form := by
      dsimp only [β₀, KahlerBackground.smul_form]
      module
    simpa only [hform] using
      LocalPotentials.isThetaPshPotential_add_of_semipositive hp (hadm.2 j)
  -- the approximation converges to the `𝓘`-envelope in the enlarged background `θ + ω`
  have hbig₁ : IsBigClass (RealBottChern.ofRepresentative (θ + (1 : ℝ) • omega.form)) :=
    PositiveCurrentAssembly.isBigClass_add_smul_of_isThetaPshPotential omega θ hu one_pos
  have hsrc := sourceQuasiEquisingularApproximation_of_native happ
  have hnat := (sourceQEAEnlargedTendsto_iff_native omega omegaX θ u hu U 1 one_pos).mp
    (sourceQuasiEquisingular_enlarged_tendsto omega omegaX θ u ε U hu hpos happ.error
      happ.term hsrc 1 one_pos)
  obtain ⟨N, hU₁, hE₁, hlim₁⟩ := hnat
  -- one Kähler background dominating `β₀` and `θ + ω`
  obtain ⟨D, hD, hsemi⟩ := KahlerDomination.exists_pos_forall_isSemipositive_add_smul
    omegaX (fun b : Bool => -(if b then β₀.form else θ + (1 : ℝ) • omega.form))
  let γ : KahlerBackground n M := KahlerBackground.smul hD omegaX
  have hγof (b : Bool) {p : M → EReal}
      (hp : IsThetaPshPotential (if b then β₀.form else θ + (1 : ℝ) • omega.form).val p) :
      IsThetaPshPotential γ.form.val p := by
    have hform : (if b then β₀.form else θ + (1 : ℝ) • omega.form) +
        (-(if b then β₀.form else θ + (1 : ℝ) • omega.form) + D • omegaX.form) = γ.form := by
      dsimp only [γ, KahlerBackground.smul_form]
      module
    simpa only [hform] using
      LocalPotentials.isThetaPshPotential_add_of_semipositive hp (hsemi b)
  have htermsγ (j : ℕ) : IsThetaPshPotential γ.form.val (fun y => U j (id y)) :=
    hγof true (hterms₀ j)
  have hEγ : IsThetaPshPotential γ.form.val (iSingularityEnvelope θ.val u) := hγof false hE₁
  -- transport the tail convergence to `γ`, then remove the shift
  have hlimγtail := (SingularNativeCommonBackground.tendsto_native_iff_common_backgrounds
    omegaX (θ + (1 : ℝ) • omega.form) γ.form hbig₁ (isBigClass_kahler γ) atTop
    (u := fun j => U (j + N)) hU₁ hE₁ (fun j => htermsγ (j + N)) hEγ).mp hlim₁
  have hlimγ : Tendsto (fun j => (⟨fun y => U j (id y), htermsγ j⟩ : ThetaPshL1 γ.form.val))
      atTop (@nhds (ThetaPshL1 γ.form.val)
        (singularityPseudoMetricSpace omegaX γ.form
          (isBigClass_kahler γ)).toUniformSpace.toTopologicalSpace
        ⟨iSingularityEnvelope θ.val u, hEγ⟩) :=
    (tendsto_add_atTop_iff_nat (f := fun j =>
      (⟨fun y => U j (id y), htermsγ j⟩ : ThetaPshL1 γ.form.val)) N).mp hlimγtail
  -- `γ` is admissible
  have hadmγ : IsAdmissibleTraceBackground hι omega θ ε γ.form := by
    refine ⟨γ.isKahler, fun j => ?_⟩
    have hsum := UniformPerturbedKahlerLowerBound.isSemipositive_add (hadm.2 j) (hsemi true)
    have hform : C • omegaX.form - ClosedRealOneOneForm.pullback hι (θ + ε j • omega.form) +
        (-(if true = true then β₀.form else θ + (1 : ℝ) • omega.form) + D • omegaX.form) =
        γ.form - ClosedRealOneOneForm.pullback hι (θ + ε j • omega.form) := by
      dsimp only [γ, β₀, KahlerBackground.smul_form]
      simp only [if_true]
      module
    unfold FormDominates
    rw [← hform]
    exact hsum
  exact ⟨hgen, θ, ε, U, happ, γ, hadmγ, hEγ, htermsγ, hlimγ⟩

/-- Source `ex:trace:L236`: `Tr^θ_X(φ)` is defined, i.e. some trace operator of
`φ ∈ PSH(X,θ)_{>0}` along `X` lies in `PSH(X,θ)_{>0}` (namely `P_θ[φ]_𝓘`). -/
theorem exists_trace_id_positive (omega omegaX : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {u : M → EReal} (hu : IsThetaPshPotential θ.val u)
    (hpos : HasPositivePotentialMass θ u hu) :
    ∃ τ : M → EReal, IsSourceTraceRepresentativeAlong omega omegaX
      (contMDiff_id : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (id : M → M))
      u τ ∧ ∃ hτ : IsThetaPshPotential θ.val τ, HasPositivePotentialMass θ τ hτ :=
  ⟨iSingularityEnvelope θ.val u, isSourceTraceRepresentativeAlong_id_iEnvelope omega omegaX θ hu hpos,
    _, (originalIEnvelope_positive_iGood omegaX θ u hu hpos).1⟩

/-- Source `ex:trace:L236`, first claim: every trace operator `τ` of `φ ∈ PSH(X,θ)_{>0}`
along `X` (for any auxiliary choices) satisfies `τ ∼_P P_θ[φ]_𝓘`. -/
theorem sourcePEquivalent_trace_id_iEnvelope
    {omega omegaX : KahlerBackground n M} (θ : ClosedRealOneOneForm n M)
    {u : M → EReal} (hu : IsThetaPshPotential θ.val u)
    (hpos : HasPositivePotentialMass θ u hu) {τ : M → EReal}
    (htrace : IsSourceTraceRepresentativeAlong omega omegaX
      (contMDiff_id : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (id : M → M))
      u τ) :
    SourcePEquivalent (n := n) τ (iSingularityEnvelope θ.val u) :=
  SGPT.Okounkov.sourcePEquivalent_of_sourceTraceRepresentatives le_rfl omegaX omegaX
    contMDiff_id htrace (isSourceTraceRepresentativeAlong_id_iEnvelope omega omegaX θ hu hpos)

/-- Source `ex:trace:L236`, second claim: if a trace operator `τ` of `φ ∈ PSH(X,θ)_{>0}`
along `X` lies in `PSH(X,θ)_{>0}`, then `Tr^θ_X(φ) = P_θ[τ] = P_θ[φ]_𝓘`. -/
theorem singularityEnvelope_trace_id_eq_iEnvelope
    {omega omegaX : KahlerBackground n M} (θ : ClosedRealOneOneForm n M)
    {u : M → EReal} (hu : IsThetaPshPotential θ.val u)
    (hpos : HasPositivePotentialMass θ u hu) {τ : M → EReal}
    (htrace : IsSourceTraceRepresentativeAlong omega omegaX
      (contMDiff_id : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (id : M → M))
      u τ)
    (hτ : IsThetaPshPotential θ.val τ) (hτpos : HasPositivePotentialMass θ τ hτ) :
    singularityEnvelope θ.val τ = iSingularityEnvelope θ.val u := by
  have hE := iSingularityEnvelope_isThetaPshPotential θ.val θ.property.1 θ.property.2
    hu.1.hasSmoothLocalPotentials u hu
  have hgood := originalIEnvelope_positive_iGood omegaX θ u hu hpos
  have hPeq := sourcePEquivalent_trace_id_iEnvelope θ hu hpos htrace
  have h₁ := (sourcePOrder_iff_pOrderWith omegaX θ hτ hE hτpos hgood.1).mp hPeq.1
  have h₂ := (sourcePOrder_iff_pOrderWith omegaX θ hE hτ hgood.1 hτpos).mp hPeq.2
  have hPE : singularityEnvelope θ.val (iSingularityEnvelope θ.val u) =
      iSingularityEnvelope θ.val u :=
    hgood.2.trans (iSingularityEnvelope_idempotent θ.val θ.property.1 θ.property.2
      hu.1.hasSmoothLocalPotentials u hu)
  exact (le_antisymm h₁ h₂).trans hPE

end SGPT.Trace
