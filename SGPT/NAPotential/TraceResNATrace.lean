import SGPT.NAPotential.NATraceSmooth
import SGPT.Trace.RIsoBTraceResolutionMass

/-! # The non-Archimedean trace on every resolution target

Source `def:NApotential:L623` (`chapter_NApotential.tex`): for `Γ ∈ PSH^NA(X, θ)` and an
irreducible analytic subset `Y ⊆ X`, the trace of `Γ` along `Y` is *well-defined* if
`ν(Γ^{θ+ω}_τ, Y) = 0` for all sufficiently negative `τ` and every `ω ∈ Kah(X)`; then
`(Tr_Y Γ)_max := sup {τ < Γ_max : ν(Γ^{θ+ω}_τ, Y) = 0}` and `Tr_Y(Γ) ∈ PSH^NA(Ỹ, θ|_Ỹ)` is the
unique element whose component at `ω ∈ Kah(Ỹ)` has cutoff `(Tr_Y Γ)_max` and slices
`P_{θ|_Ỹ+ω}[Tr^{θ+ω̃}_Y(Γ^{θ+ω̃}_τ)]_𝓘`. *When `Ỹ` is not smooth, `PSH^NA(Ỹ, θ|_Ỹ)` is understood
as the set of non-Archimedean metrics on a resolution of `Ỹ`.*

`SGPT.NAPotential.NATrace` (`NATraceSmooth`) constructs `Tr_Y(Γ)` for a target `ι : V → X` whose
pullbacks of Kähler forms are Kähler (smooth `Y`). Its only use of that hypothesis is through
`SGPT.Trace.hasPositiveSourceTraceAlong_add_kahler` (`def:traceop2`: `Tr^{θ+ω}_Y(φ)` is defined).
Here that hypothesis is replaced by *positive volume of all Kähler pullbacks*
(`SGPT.Trace.RIsoB.PullbackKahlerVolumePos`: `∫_V (ι^*ω)^{dim V} > 0`), which holds both for
Kähler pullbacks (`pullbackKahlerVolumePos_of_isKahler`) and on **every resolution target** of
every irreducible analytic subset `Y` (`SGPT.Trace.RIsoB.pullbackKahlerVolumePos`: a resolution
is generically an immersion), where `ι^*ω` is only semipositive.

## Main results

* `hasPositiveSourceTraceAlong_add_kahler_of_volumePos`: `def:traceop2`, first observation, for
  every target whose Kähler pullbacks have positive volume.
* `naTraceRes`, `naTraceRes_max`, `naTraceRes_potential`, `naTraceRes_potential_traceEnvelope`,
  `naTraceRes_unique`, `source_naTraceRes`: the generalized construction (a copy of
  `NATraceSmooth` with the volume hypothesis); `naTraceRes_eq_naTrace`: it is the trace of
  `NATraceSmooth` whenever Kähler forms pull back to Kähler forms.
* `sliceTraceable_resolution_iff`, `traceWellDefined_resolution_iff`,
  `traceCutoff_resolution_eq`, `traceCutoff_resolution_independent`: on a resolution target the
  well-definedness condition and `(Tr_Y Γ)_max` are the book's, with `ν(·, Y)` the generic Lelong
  number along `Y` (independent of the resolution).
* `naTraceResolution`, `source_naTrace_resolution`: **source `def:NApotential:L623` for an
  arbitrary irreducible analytic subset `Y`, read on any resolution target `(Y', ι)` of `Y`**
  (`SGPT.Trace.Trace2Resolution.ResolutionTarget`; such targets exist,
  `Trace2Resolution.exists_resolutionTarget`). The reading on the normalization `Ỹ` itself (a
  normal Kähler space, `cor:PSH`) is not formalized.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.NAPotential.TraceRes

open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.SourceTraceRepresentativeDefinition
open SGPT.PSH.VariableComplexAtlas
open SGPT.NAPotential.NATrace
open SGPT.Trace.RIsoB (PullbackKahlerVolumePos)
open scoped Manifold ContDiff

universe u

variable {n k : ℕ} {X V : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)}

/-! ### `def:traceop2` for targets with Kähler pullbacks of positive volume -/

section Domain

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X] in
/-- Kähler pullbacks have positive volume. -/
theorem pullbackKahlerVolumePos_of_isKahler {ι : V → X}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (hpull : ∀ w : KahlerBackground n X, (ClosedRealOneOneForm.pullback hι w.form).val.IsKahler) :
    PullbackKahlerVolumePos (M := X) hι := fun w =>
  KahlerVolumePositive.diagonalPotentialMass_zero_pos
    (⟨ClosedRealOneOneForm.pullback hι w.form, hpull w⟩ : KahlerBackground k V)

omit [MeasurableSpace X] [BorelSpace X] [ConnectedSpace X] in
/-- **Source `def:traceop2`, first observation, for targets with Kähler pullbacks of positive
volume** (e.g. every resolution target of an irreducible analytic subset): if `u ∈ PSH(X, β)`
and `ν(u, Y) = 0`, then for every Kähler form `ω` on `X` the trace `Tr^{β+ω}_Y(u)` is defined. -/
theorem hasPositiveSourceTraceAlong_add_kahler_of_volumePos (hk : k ≤ n)
    (omega₀ omega : KahlerBackground n X) (omegaV : KahlerBackground k V) {ι : V → X}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (hvol : PullbackKahlerVolumePos (M := X) hι) {β : ClosedRealOneOneForm n X} {u : X → EReal}
    (hu : IsThetaPshPotential β.val u) (hgeneric : sourceGenericLelongNumber (n := n) ι u = 0) :
    SGPT.Trace.HasPositiveSourceTraceAlong omega₀ omegaV hι (β + omega.form) u := by
  by_cases hn : n = 0
  · obtain ⟨τ, hT⟩ := SGPT.TraceOperations.exists_sourceTrace_of_globalQuasiPshPotential hk
      omega₀ omegaV hu.quasiPshPotential hι hgeneric
    exact SGPT.Trace.hasPositiveSourceTraceAlong_of_dim_zero hk hn _ hT
  apply (SGPT.Trace.hasPositiveSourceTraceAlong_iff_auxiliary_choices hk omega omega₀ omegaV
    omegaV hι _ u).mp
  apply (SGPT.Trace.hasPositiveSourceTraceAlong_iff_native hn omega omegaV hι _ u).mpr
  refine SGPT.Trace.RIsoB.hasPositiveTraceRepresentativeAlong_of_current_margin omega omegaV hι
    hvol zero_lt_one ?_ ((nativeGeneric_zero_iff_source hn ι u).mpr hgeneric)
  simpa only [one_smul, add_sub_cancel_right] using hu

end Domain

/-! ### Good representatives of the trace slices -/

section Traces

variable (hk : k ≤ n) (omegaX : KahlerBackground n X) (omegaV : KahlerBackground k V)
  {ι : V → X} (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X] [MeasurableSpace V]
  [BorelSpace V] [CompactSpace V] [ConnectedSpace V] in
private theorem pullback_add' (a b : ClosedRealOneOneForm n X) :
    ClosedRealOneOneForm.pullback hι (a + b) =
      ClosedRealOneOneForm.pullback hι a + ClosedRealOneOneForm.pullback hι b := by
  apply ClosedRealOneOneForm.ext
  intro e z
  ext v
  rfl

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X] [MeasurableSpace V]
  [BorelSpace V] [CompactSpace V] [ConnectedSpace V] in
private theorem pullback_smul' (c : ℝ) (a : ClosedRealOneOneForm n X) :
    ClosedRealOneOneForm.pullback hι (c • a) = c • ClosedRealOneOneForm.pullback hι a := by
  apply ClosedRealOneOneForm.ext
  intro e z
  ext v
  rfl

/-- The trace operator of a slice has, up to `P`-equivalence, a representative in
`PSH(V, ι^*θ + ½ κ)` for every Kähler form `κ` on `V` (Kähler pullbacks of positive volume). -/
theorem exists_goodTraceSlice (hvol : PullbackKahlerVolumePos (M := X) hι)
    (Γ : SourceNAPotential θ) (κV : SourceKahlerForm k V) (τ : ℝ)
    (hτ : SliceTraceable ι Γ (sourceKahlerFormOfBackground omegaX) τ) :
    ∃ φ : V → EReal,
      IsThetaPshPotential (ClosedRealOneOneForm.pullback hι (atlasClosedFormToNative θ) +
        (1 / 2 : ℝ) • (sourceKahlerFormRepresentative κV).form).val φ ∧
      SingularGlobalPOrder.SourcePEquivalent (n := k) φ
        (traceSlice hk omegaX omegaV hι Γ τ hτ) := by
  obtain ⟨c, hc, hsemi⟩ := WholeClosureNA.exists_small_semipositive_difference
    (sourceKahlerFormRepresentative κV) (ClosedRealOneOneForm.pullback hι omegaX.form)
  have hε : (0 : ℝ) < c / 4 := by positivity
  let ωε := KahlerBackground.smul hε omegaX
  let κε := sourceKahlerFormOfBackground ωε
  have hτε : SliceTraceable ι Γ κε τ := sliceTraceable_index ι Γ hτ
  have hrmax : τ < (Γ.realizedComponent ωε).val.max := by
    rw [Γ.realizedComponent_max]
    exact hτε.1
  have hreal := Γ.realizedComponent_potential ωε τ hτε.1 hrmax
  have hu'nat : IsThetaPshPotential (atlasClosedFormToNative θ + ωε.form).val
      ((Γ.component κε).val.potential ⟨τ, hτε.1⟩) := by
    have h := (Γ.realizedComponent ωε).val.native_thetaPSH ⟨τ, hrmax⟩
    rw [hreal, sourceTestCurveEnlargedBackground_native] at h
    exact h
  obtain ⟨ψ', hT', hψ', _hpos⟩ := hasPositiveSourceTraceAlong_add_kahler_of_volumePos hk omegaX ωε
    omegaV hι hvol hu'nat hτε.2
  have hI := component_potential_iEquivalent Γ κε (sourceKahlerFormOfBackground omegaX) τ
    hτε.1 hτ.1
  have hspec := traceSlice_spec hk omegaX omegaV hι Γ τ hτ
  have h1 := SGPT.TraceOperations.sourcePOrder_of_iOrder_of_sourceTraceRepresentatives hk omegaV
    omegaV hι hT' hspec ((sourceIOrder_iff_native hI.1.1 hI.1.2.1).mp hI.1)
  have h2 := SGPT.TraceOperations.sourcePOrder_of_iOrder_of_sourceTraceRepresentatives hk omegaV
    omegaV hι hspec hT' ((sourceIOrder_iff_native hI.2.1 hI.2.2.1).mp hI.2)
  refine ⟨ψ', ?_, h1, h2⟩
  set P := ClosedRealOneOneForm.pullback hι omegaX.form
  set β := ClosedRealOneOneForm.pullback hι (atlasClosedFormToNative θ)
  set K := (sourceKahlerFormRepresentative κV).form
  have hpb : ClosedRealOneOneForm.pullback hι ((atlasClosedFormToNative θ + ωε.form) + ωε.form) =
      β + (c / 4) • P + (c / 4) • P := by
    rw [pullback_add' hι, pullback_add' hι]
    simp only [ωε, KahlerBackground.smul_form, pullback_smul' hι]
    rfl
  rw [hpb] at hψ'
  have hsemi' : ((1 / 2 : ℝ) • (K - c • P)).val.IsSemipositive :=
    KahlerDomination.isSemipositive_smul hsemi (by norm_num)
  have hadd := LocalPotentials.isThetaPshPotential_add_of_semipositive hψ' hsemi'
  have heq : β + (c / 4) • P + (c / 4) • P + (1 / 2 : ℝ) • (K - c • P) =
      β + (1 / 2 : ℝ) • K := by
    rw [smul_sub, smul_smul]
    have : (c / 4) • P + (c / 4) • P = ((1 / 2 : ℝ) * c) • P := by
      rw [← add_smul]
      congr 1
      ring
    rw [add_assoc β, this]
    abel
  rw [heq] at hadd
  exact hadd

/-- A good representative of the trace slice in the background `ι^*θ + κ`. -/
theorem exists_goodTraceSlice' (hvol : PullbackKahlerVolumePos (M := X) hι)
    (Γ : SourceNAPotential θ) (κV : SourceKahlerForm k V) (τ : ℝ)
    (hτ : SliceTraceable ι Γ (sourceKahlerFormOfBackground omegaX) τ) :
    ∃ φ : V → EReal,
      IsThetaPshPotential (ClosedRealOneOneForm.pullback hι (atlasClosedFormToNative θ) +
        (1 / 2 : ℝ) • (sourceKahlerFormRepresentative κV).form).val φ ∧
      sourceIEquivalent (ofFixedModel k V) φ (traceSlice hk omegaX omegaV hι Γ τ hτ) := by
  obtain ⟨φ, hφ, hP⟩ := exists_goodTraceSlice hk omegaX omegaV hι hvol Γ κV τ hτ
  have hq1 : (ofFixedModel k V).IsQPSH φ :=
    ⟨_, thetaPSH_traceBackground_of_half hι κV hφ⟩
  have hq2 := isQPSH_of_sourceTrace hι (traceSlice_spec hk omegaX omegaV hι Γ τ hτ)
  exact ⟨φ, hφ, sourceIOrder_of_sourcePOrder hq1 hq2 hP.1,
    sourceIOrder_of_sourcePOrder hq2 hq1 hP.2⟩

theorem traceComponentSlice_props_of_volumePos (hvol : PullbackKahlerVolumePos (M := X) hι)
    (Γ : SourceNAPotential θ) (κV : SourceKahlerForm k V)
    (τ : ℝ) (hτ : SliceTraceable ι Γ (sourceKahlerFormOfBackground omegaX) τ) :
    ∃ hP : (ofFixedModel k V).IsThetaPSH
        (sourceNAComponentBackground (θ.nativeHolomorphicPullback hι) κV)
        (traceComponentSlice hk omegaX omegaV hι Γ κV τ hτ),
      sourceIModel (sourceNAComponentBackground (θ.nativeHolomorphicPullback hι) κV)
        (traceComponentSlice hk omegaX omegaV hι Γ κV τ hτ) ∧
      0 < sourcePotentialNonPluripolarMeasure
        (sourceNAComponentBackground (θ.nativeHolomorphicPullback hι) κV)
        (traceComponentSlice hk omegaX omegaV hι Γ κV τ hτ) hP univ := by
  obtain ⟨φ, hφ, hE⟩ := exists_goodTraceSlice' hk omegaX omegaV hι hvol Γ κV τ hτ
  have hφα := thetaPSH_traceBackground_of_half hι κV hφ
  rw [traceComponentSlice_eq hk omegaX omegaV hι Γ κV τ hτ hE]
  exact ⟨isThetaPSH_sourceIEnvelope hφα, sourceIEnvelope_isIModel hφα,
    iEnvelope_traceBackground_mass_pos hι κV hφ⟩

end Traces

/-! ### Monotonicity and concavity of the trace slices -/

section Curve

open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination

private theorem ereal_convex_self' {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (a : EReal) :
    (t : EReal) * a + ((1 - t : ℝ) : EReal) * a = a := by
  induction a with
  | bot => simp only [EReal.coe_mul_bot_of_pos ht0,
      EReal.coe_mul_bot_of_pos (sub_pos.mpr ht1), EReal.bot_add]
  | top => simp only [EReal.coe_mul_top_of_pos ht0,
      EReal.coe_mul_top_of_pos (sub_pos.mpr ht1), EReal.top_add_top]
  | coe a =>
      rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
      congr 1
      ring

variable (hk : k ≤ n) (omegaX : KahlerBackground n X) (omegaV : KahlerBackground k V)
  {ι : V → X} (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)

/-- The trace slices decrease in `τ`. -/
theorem traceComponentSlice_antitone_of_volumePos (hvol : PullbackKahlerVolumePos (M := X) hι)
    (Γ : SourceNAPotential θ) (κV : SourceKahlerForm k V) {τ τ' : ℝ} (hle : τ ≤ τ')
    (hτ : SliceTraceable ι Γ (sourceKahlerFormOfBackground omegaX) τ)
    (hτ' : SliceTraceable ι Γ (sourceKahlerFormOfBackground omegaX) τ') :
    traceComponentSlice hk omegaX omegaV hι Γ κV τ' hτ' ≤
      traceComponentSlice hk omegaX omegaV hι Γ κV τ hτ := by
  let G := (Γ.component (sourceKahlerFormOfBackground omegaX)).val
  have hmono : ∀ x, G.potential ⟨τ', hτ'.1⟩ x ≤ G.potential ⟨τ, hτ.1⟩ x := fun x =>
    G.antitone x (show (⟨τ, hτ.1⟩ : Iio G.max) ≤ ⟨τ', hτ'.1⟩ from hle)
  have hIX : IEnvelope.IOrderOnManifold (n := n) (G.potential ⟨τ', hτ'.1⟩)
      (G.potential ⟨τ, hτ.1⟩) :=
    iOrderOnManifold_of_le_add (C := 0) (G.native_thetaPSH ⟨τ, hτ.1⟩).1.quasiPlurisubharmonic
      (fun x => by simpa only [EReal.coe_zero, add_zero] using hmono x)
  have hP := SGPT.TraceOperations.sourcePOrder_of_iOrder_of_sourceTraceRepresentatives hk omegaV
    omegaV hι (traceSlice_spec hk omegaX omegaV hι Γ τ' hτ')
    (traceSlice_spec hk omegaX omegaV hι Γ τ hτ) hIX
  obtain ⟨φ, hφ, hE⟩ := exists_goodTraceSlice' hk omegaX omegaV hι hvol Γ κV τ hτ
  obtain ⟨φ', hφ', hE'⟩ := exists_goodTraceSlice' hk omegaX omegaV hι hvol Γ κV τ' hτ'
  have hq := isQPSH_of_sourceTrace hι (traceSlice_spec hk omegaX omegaV hι Γ τ hτ)
  have hq' := isQPSH_of_sourceTrace hι (traceSlice_spec hk omegaX omegaV hι Γ τ' hτ')
  have hI := sourceIOrder_trans hE'.1 (sourceIOrder_trans (sourceIOrder_of_sourcePOrder hq' hq hP)
    hE.2)
  rw [traceComponentSlice_eq hk omegaX omegaV hι Γ κV τ hτ hE,
    traceComponentSlice_eq hk omegaX omegaV hι Γ κV τ' hτ' hE']
  exact (sourceIOrder_iff_sourceIEnvelope_le (thetaPSH_traceBackground_of_half hι κV hφ')
    (thetaPSH_traceBackground_of_half hι κV hφ)).mp hI

/-- The trace slices are concave in `τ`. -/
theorem traceComponentSlice_chord_of_volumePos (hvol : PullbackKahlerVolumePos (M := X) hι)
    (Γ : SourceNAPotential θ) (κV : SourceKahlerForm k V) {p q : ℝ} {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1)
    (hp : SliceTraceable ι Γ (sourceKahlerFormOfBackground omegaX) p)
    (hq : SliceTraceable ι Γ (sourceKahlerFormOfBackground omegaX) q)
    (hm : SliceTraceable ι Γ (sourceKahlerFormOfBackground omegaX) (t * p + (1 - t) * q)) :
    convexComb t (traceComponentSlice hk omegaX omegaV hι Γ κV p hp)
        (traceComponentSlice hk omegaX omegaV hι Γ κV q hq) ≤
      traceComponentSlice hk omegaX omegaV hι Γ κV (t * p + (1 - t) * q) hm := by
  let G := (Γ.component (sourceKahlerFormOfBackground omegaX)).val
  have ht1' : 0 < 1 - t := sub_pos.mpr ht1
  let up := G.potential ⟨p, hp.1⟩
  let uq := G.potential ⟨q, hq.1⟩
  have hqp : (ofFixedModel n X).IsQPSH up := ⟨_, G.thetaPSH ⟨p, hp.1⟩⟩
  have hqq : (ofFixedModel n X).IsQPSH uq := ⟨_, G.thetaPSH ⟨q, hq.1⟩⟩
  have hqtp := hqp.pos_smul ht0
  have hqtq := hqq.pos_smul ht1'
  have hqs := hqtp.add hqtq
  -- generic Lelong numbers
  have h0p : sourceGenericLelongNumber (n := n) ι (fun x => (t : EReal) * up x) = 0 := by
    rw [SGPT.TraceOperations.sourceGenericLelongNumber_pos_smul ι up ht0, hp.2, mul_zero]
  have h0q : sourceGenericLelongNumber (n := n) ι (fun x => ((1 - t : ℝ) : EReal) * uq x) = 0 := by
    rw [SGPT.TraceOperations.sourceGenericLelongNumber_pos_smul ι uq ht1', hq.2, mul_zero]
  have hM : max p q < G.max := max_lt hp.1 hq.1
  let uM := G.potential ⟨max p q, hM⟩
  have hMs : ∀ x, uM x ≤ (t : EReal) * up x + ((1 - t : ℝ) : EReal) * uq x := by
    intro x
    have h1 : uM x ≤ up x := G.antitone x
      (show (⟨p, hp.1⟩ : Iio G.max) ≤ ⟨max p q, hM⟩ from le_max_left p q)
    have h2 : uM x ≤ uq x := G.antitone x
      (show (⟨q, hq.1⟩ : Iio G.max) ≤ ⟨max p q, hM⟩ from le_max_right p q)
    calc uM x = (t : EReal) * uM x + ((1 - t : ℝ) : EReal) * uM x :=
          (ereal_convex_self' ht0 ht1 _).symm
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left h1 (EReal.coe_nonneg.mpr ht0.le))
          (mul_le_mul_of_nonneg_left h2 (EReal.coe_nonneg.mpr ht1'.le))
  have hMtr : SliceTraceable ι Γ (sourceKahlerFormOfBackground omegaX) (max p q) :=
    sliceTraceable_of_le ι Γ _ (if h : p ≤ q then by rw [max_eq_right h]; exact hq
      else by rw [max_eq_left (le_of_not_ge h)]; exact hp) le_rfl
  have h0s : sourceGenericLelongNumber (n := n) ι
      (fun x => (t : EReal) * up x + ((1 - t : ℝ) : EReal) * uq x) = 0 :=
    SGPT.Trace.sourceGenericLelongNumber_eq_zero_of_iOrder (G.native_thetaPSH ⟨max p q, hM⟩)
      (iOrderOnManifold_of_le_add (C := 0) (globalQPSH_of_isQPSH hqs).1
        (fun x => by simpa only [EReal.coe_zero, add_zero] using hMs x)) hMtr.2
  -- the three auxiliary traces
  obtain ⟨τu, hTu⟩ := SGPT.TraceOperations.exists_sourceTrace_of_globalQuasiPshPotential hk omegaX
    omegaV (globalQPSH_of_isQPSH hqtp) hι h0p
  obtain ⟨τv, hTv⟩ := SGPT.TraceOperations.exists_sourceTrace_of_globalQuasiPshPotential hk omegaX
    omegaV (globalQPSH_of_isQPSH hqtq) hι h0q
  obtain ⟨τs, hTs⟩ := SGPT.TraceOperations.exists_sourceTrace_of_globalQuasiPshPotential hk omegaX
    omegaV (globalQPSH_of_isQPSH hqs) hι h0s
  have hspp := traceSlice_spec hk omegaX omegaV hι Γ p hp
  have hspq := traceSlice_spec hk omegaX omegaV hι Γ q hq
  have hspm := traceSlice_spec hk omegaX omegaV hι Γ _ hm
  let ψp := traceSlice hk omegaX omegaV hι Γ p hp
  let ψq := traceSlice hk omegaX omegaV hι Γ q hq
  let ψm := traceSlice hk omegaX omegaV hι Γ _ hm
  have A := SGPT.TraceOperations.sourcePEquivalent_pos_smul_of_sourceTraceRepresentatives hk
    omegaV omegaV hι hspp ht0 hTu
  have B := SGPT.TraceOperations.sourcePEquivalent_pos_smul_of_sourceTraceRepresentatives hk
    omegaV omegaV hι hspq ht1' hTv
  have C := SGPT.TraceOperations.sourcePEquivalent_add_of_sourceTraceRepresentatives hk
    omegaV omegaV omegaV hι hTu hTv hTs
  have hchordX : ∀ x, (t : EReal) * up x + ((1 - t : ℝ) : EReal) * uq x ≤
      G.potential ⟨t * p + (1 - t) * q, hm.1⟩ x := fun x =>
    G.toSourceTestCurvePredata.convexComb_le ⟨p, hp.1⟩ ⟨q, hq.1⟩ ht0 ht1 x
  have D := SGPT.TraceOperations.sourcePOrder_of_iOrder_of_sourceTraceRepresentatives hk omegaV
    omegaV hι hTs hspm (iOrderOnManifold_of_le_add (C := 0)
      (G.native_thetaPSH ⟨t * p + (1 - t) * q, hm.1⟩).1.quasiPlurisubharmonic
      (fun x => by simpa only [EReal.coe_zero, add_zero] using hchordX x))
  -- good representatives
  obtain ⟨φp, hφp, hEp⟩ := exists_goodTraceSlice' hk omegaX omegaV hι hvol Γ κV p hp
  obtain ⟨φq, hφq, hEq⟩ := exists_goodTraceSlice' hk omegaX omegaV hι hvol Γ κV q hq
  obtain ⟨φm, hφm, hEm⟩ := exists_goodTraceSlice' hk omegaX omegaV hι hvol Γ κV _ hm
  have hαp := thetaPSH_traceBackground_of_half hι κV hφp
  have hαq := thetaPSH_traceBackground_of_half hι κV hφq
  have hαm := thetaPSH_traceBackground_of_half hι κV hφm
  have qφp : (ofFixedModel k V).IsQPSH φp := ⟨_, hαp⟩
  have qφq : (ofFixedModel k V).IsQPSH φq := ⟨_, hαq⟩
  have qψp := isQPSH_of_sourceTrace hι hspp
  have qψq := isQPSH_of_sourceTrace hι hspq
  have qψm := isQPSH_of_sourceTrace hι hspm
  have qτu := isQPSH_of_sourceTrace hι hTu
  have qτv := isQPSH_of_sourceTrace hι hTv
  have qτs := isQPSH_of_sourceTrace hι hTs
  -- the `𝓘`-order chain
  have I1 : sourceIOrder (ofFixedModel k V) (convexComb t φp φq) (convexComb t ψp ψq) :=
    SGPT.PSH.GlobalOrderAddition.sourceIOrder_add omegaV (qφp.pos_smul ht0) (qφq.pos_smul ht1')
      (qψp.pos_smul ht0) (qψq.pos_smul ht1')
      (sourceIEquivalent_pos_smul qφp qψp hEp ht0).1
      (sourceIEquivalent_pos_smul qφq qψq hEq ht1').1
  have I2 : sourceIOrder (ofFixedModel k V) (convexComb t ψp ψq) (fun y => τu y + τv y) :=
    SGPT.PSH.GlobalOrderAddition.sourceIOrder_add omegaV (qψp.pos_smul ht0) (qψq.pos_smul ht1')
      qτu qτv (sourceIOrder_of_sourcePOrder (qψp.pos_smul ht0) qτu A.2)
      (sourceIOrder_of_sourcePOrder (qψq.pos_smul ht1') qτv B.2)
  have I3 : sourceIOrder (ofFixedModel k V) (fun y => τu y + τv y) τs :=
    sourceIOrder_of_sourcePOrder (qτu.add qτv) qτs C.2
  have I4 : sourceIOrder (ofFixedModel k V) τs ψm := sourceIOrder_of_sourcePOrder qτs qψm D
  have hI := sourceIOrder_trans I1 (sourceIOrder_trans I2 (sourceIOrder_trans I3
    (sourceIOrder_trans I4 hEm.2)))
  rw [traceComponentSlice_eq hk omegaX omegaV hι Γ κV p hp hEp,
    traceComponentSlice_eq hk omegaX omegaV hι Γ κV q hq hEq,
    traceComponentSlice_eq hk omegaX omegaV hι Γ κV _ hm hEm]
  exact convexComb_sourceIEnvelope_le_of_iOrder hαp hαq hαm ht0 ht1 hI

end Curve

/-! ### The trace `Tr_Y(Γ) ∈ PSH^NA(Y', θ|_{Y'})` -/

section TraceMetric

variable (hk : k ≤ n) (omegaX : KahlerBackground n X) (omegaV : KahlerBackground k V)
  {ι : V → X} (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
  (hvol : PullbackKahlerVolumePos (M := X) hι)

/-- The preliminary test-curve data of the component of `Tr_Y(Γ)` at the Kähler index `κ` of
`V`: cutoff `(Tr_Y Γ)_max` and slices `P_{ι^*θ+κ}[Tr_Y(Γ_τ)]_𝓘`. -/
def resComponentPredata (Γ : SourceNAPotential θ) (hwd : TraceWellDefined ι Γ)
    (κV : SourceKahlerForm k V) :
    SourceTestCurvePredata (sourceNAComponentBackground (θ.nativeHolomorphicPullback hι) κV) where
  max := traceCutoff ι Γ (sourceKahlerFormOfBackground omegaX)
  potential τ := traceComponentSlice hk omegaX omegaV hι Γ κV τ.1
    (sliceTraceable_of_lt_traceCutoff hwd _ τ.2)
  thetaPSH τ := (traceComponentSlice_props_of_volumePos hk omegaX omegaV hι hvol Γ κV τ.1
    (sliceTraceable_of_lt_traceCutoff hwd _ τ.2)).choose
  antitone x := fun a b hab =>
    traceComponentSlice_antitone_of_volumePos hk omegaX omegaV hι hvol Γ κV hab _ _ x
  concave x := by
    apply sourceTestCurveNegativeTrace_convex_of_chords _ _ x
    intro p q t ht0 ht1
    exact traceComponentSlice_chord_of_volumePos hk omegaX omegaV hι hvol Γ κV ht0 ht1 _ _ _
  fixedPoint τ := by
    obtain ⟨_hP, hI, hpos⟩ := traceComponentSlice_props_of_volumePos hk omegaX omegaV hι hvol Γ κV
      τ.1 (sliceTraceable_of_lt_traceCutoff hwd _ τ.2)
    have hg := (sourceIModel_positive_iGood _ _ hI hpos).2
    rw [(sourceIGood_iff_PI_eq (sourceKahlerFormRepresentative κV) hI.1 hpos).mp hg]
    exact hI.2.symm

/-- The component of `Tr_Y(Γ)` at `κ`, as an actual test curve (its limit has positive mass
since it dominates a slice of positive mass). -/
def resComponentCurve (Γ : SourceNAPotential θ) (hwd : TraceWellDefined ι Γ)
    (κV : SourceKahlerForm k V) :
    SourceTestCurve (sourceNAComponentBackground (θ.nativeHolomorphicPullback hι) κV) where
  toSourceTestCurvePredata := resComponentPredata hk omegaX omegaV hι hvol Γ hwd κV
  positiveLimitMass := by
    let D := resComponentPredata hk omegaX omegaV hι hvol Γ hwd κV
    let p : Iio D.max := ⟨D.max - 1, by change D.max - 1 < D.max; linarith⟩
    obtain ⟨_hP, _hI, hpos⟩ := traceComponentSlice_props_of_volumePos hk omegaX omegaV hι hvol Γ
      κV p.1 (sliceTraceable_of_lt_traceCutoff hwd _ p.2)
    refine hpos.trans_le (sourcePotentialNonPluripolarMass_mono
      (sourceKahlerFormRepresentative κV) _ _
      ((SGPT.PSH.singularityLE_iff_exists_real _ _).mpr ⟨0, fun y => ?_⟩))
    rw [EReal.coe_zero, add_zero]
    exact (le_iSup (fun j => D.potential j y) p).trans
      (le_uscRegularization (fun z => ⨆ j, D.potential j z) y)

theorem resComponentCurve_mem (Γ : SourceNAPotential θ) (hwd : TraceWellDefined ι Γ)
    (κV : SourceKahlerForm k V) :
    resComponentCurve hk omegaX omegaV hι hvol Γ hwd κV ∈
      SourceIModelTestCurvesPositive
        (sourceNAComponentBackground (θ.nativeHolomorphicPullback hι) κV) :=
  (sourceIModelTestCurvesPositive_iff_slices (sourceKahlerFormRepresentative κV) _).mpr
    fun τ => (sourceIModel_iff_native _ _).mp (traceComponentSlice_props_of_volumePos hk omegaX
      omegaV hι hvol Γ κV τ.1 (sliceTraceable_of_lt_traceCutoff hwd _ τ.2)).2.1

/-- The component of `Tr_Y(Γ)` at `κ`, a positive `𝓘`-model test curve in `ι^*θ + κ`. -/
def resComponent (Γ : SourceNAPotential θ) (hwd : TraceWellDefined ι Γ)
    (κV : SourceKahlerForm k V) :
    SourcePositiveIModelTestCurve
      (sourceNAComponentBackground (θ.nativeHolomorphicPullback hι) κV) :=
  ⟨resComponentCurve hk omegaX omegaV hι hvol Γ hwd κV,
    resComponentCurve_mem hk omegaX omegaV hι hvol Γ hwd κV⟩

/-- Source `def:NApotential:L623` (targets with Kähler pullbacks of positive volume, e.g. any
resolution target of `Y`): the trace `Tr_Y(Γ) ∈ PSH^NA(V, ι^*θ)` of a non-Archimedean metric
whose trace along `Y` is well-defined. -/
def naTraceRes (Γ : SourceNAPotential θ) (hwd : TraceWellDefined ι Γ) :
    SourceNAPotential (θ.nativeHolomorphicPullback hι) where
  component κV := resComponent hk omegaX omegaV hι hvol Γ hwd κV
  compatible κ ζ h := by
    apply Subtype.ext
    apply SourceTestCurve.ext_of_max_potential
    · rw [sourceIModelTestCurveTransition_max]
      rfl
    · intro r hr hs
      have hr' : r < (resComponent hk omegaX omegaV hι hvol Γ hwd κ).val.max := by
        rw [sourceIModelTestCurveTransition_max] at hr
        exact hr
      rw [sourceIModelTestCurveTransition_potential _ _ _ r hr' hr]
      have hτ := sliceTraceable_of_lt_traceCutoff hwd (sourceKahlerFormOfBackground omegaX) hr'
      change sourceIEnvelope _ (traceComponentSlice hk omegaX omegaV hι Γ κ r hτ) =
        traceComponentSlice hk omegaX omegaV hι Γ ζ r hτ
      obtain ⟨φ, hφ, hE⟩ := exists_goodTraceSlice' hk omegaX omegaV hι hvol Γ κ r hτ
      rw [traceComponentSlice_eq hk omegaX omegaV hι Γ κ r hτ hE]
      unfold traceComponentSlice
      apply sourceIEnvelope_eq_of_equivalent
      exact sourceIEquivalent_trans
        (sourceIEquivalent_symm (sourceIEquivalent_iEnvelope
          (thetaPSH_traceBackground_of_half hι κ hφ))) hE

/-- Source `def:NApotential:L623`, eq:tracemax: every component of `Tr_Y(Γ)` has the cutoff
`(Tr_Y Γ)_max = sup {τ < Γ_max : ν(Γ^{θ+ω}_τ, Y) = 0}`, for any Kähler form `ω` of `X`. -/
theorem naTraceRes_max (Γ : SourceNAPotential θ) (hwd : TraceWellDefined ι Γ)
    (κV : SourceKahlerForm k V) (κ : SourceKahlerForm n X) :
    ((naTraceRes hk omegaX omegaV hι hvol Γ hwd).component κV).val.max = traceCutoff ι Γ κ :=
  traceCutoff_independent ι Γ _ κ

/-- Source `def:NApotential:L623`, item 2: for `τ < (Tr_Y Γ)_max`, every Kähler form `ω̃` of `X`
and every trace operator `ψ` of `Γ^{θ+ω̃}_τ` along `Y` (with arbitrary auxiliary choices),
`Tr_Y(Γ)^{θ|_Y+κ}_τ = P_{θ|_Y+κ}[ψ]_𝓘`; in particular the choice of the trace operator and of
`ω̃` is irrelevant. -/
theorem naTraceRes_potential (Γ : SourceNAPotential θ) (hwd : TraceWellDefined ι Γ)
    (κV : SourceKahlerForm k V) (κ : SourceKahlerForm n X) (τ : ℝ)
    (hτ : τ < ((naTraceRes hk omegaX omegaV hι hvol Γ hwd).component κV).val.max)
    (hτκ : τ < (Γ.component κ).val.max) (omega' : KahlerBackground n X)
    (omegaV' : KahlerBackground k V) {ψ : V → EReal}
    (hψ : IsSourceTraceRepresentativeAlong omega' omegaV' hι
      ((Γ.component κ).val.potential ⟨τ, hτκ⟩) ψ) :
    ((naTraceRes hk omegaX omegaV hι hvol Γ hwd).component κV).val.potential ⟨τ, hτ⟩ =
      sourceIEnvelope (sourceNAComponentBackground (θ.nativeHolomorphicPullback hι) κV) ψ := by
  have hτ0 := sliceTraceable_of_lt_traceCutoff hwd (sourceKahlerFormOfBackground omegaX) hτ
  change traceComponentSlice hk omegaX omegaV hι Γ κV τ hτ0 = _
  have hspec := traceSlice_spec hk omegaX omegaV hι Γ τ hτ0
  have hI := component_potential_iEquivalent Γ κ (sourceKahlerFormOfBackground omegaX) τ hτκ hτ0.1
  have h1 := SGPT.TraceOperations.sourcePOrder_of_iOrder_of_sourceTraceRepresentatives hk omegaV'
    omegaV hι hψ hspec ((sourceIOrder_iff_native hI.1.1 hI.1.2.1).mp hI.1)
  have h2 := SGPT.TraceOperations.sourcePOrder_of_iOrder_of_sourceTraceRepresentatives hk omegaV
    omegaV' hι hspec hψ ((sourceIOrder_iff_native hI.2.1 hI.2.2.1).mp hI.2)
  have hq1 := isQPSH_of_sourceTrace hι hψ
  have hq2 := isQPSH_of_sourceTrace hι hspec
  exact sourceIEnvelope_eq_of_equivalent
    ⟨sourceIOrder_of_sourcePOrder hq2 hq1 h2, sourceIOrder_of_sourcePOrder hq1 hq2 h1⟩

/-- Source `def:NApotential:L623`, item 2 with the normalized trace of `def:traceop2`: whenever
`Tr^{θ+ω̃}_Y(Γ^{θ+ω̃}_τ)` is defined (on these targets it always is, by
`hasPositiveSourceTraceAlong_add_kahler_of_volumePos`),
`Tr_Y(Γ)^{θ|_Y+κ}_τ = P_{θ|_Y+κ}[Tr^{θ+ω̃}_Y(Γ^{θ+ω̃}_τ)]_𝓘`. -/
theorem naTraceRes_potential_traceEnvelope (Γ : SourceNAPotential θ)
    (hwd : TraceWellDefined ι Γ) (κV : SourceKahlerForm k V) (κ : SourceKahlerForm n X) (τ : ℝ)
    (hτ : τ < ((naTraceRes hk omegaX omegaV hι hvol Γ hwd).component κV).val.max)
    (hτκ : τ < (Γ.component κ).val.max) (omega' : KahlerBackground n X)
    (omegaV' : KahlerBackground k V)
    (hdef : SGPT.Trace.HasPositiveSourceTraceAlong omega' omegaV' hι
      (atlasClosedFormToNative θ + (sourceKahlerFormRepresentative κ).form)
      ((Γ.component κ).val.potential ⟨τ, hτκ⟩)) :
    ((naTraceRes hk omegaX omegaV hι hvol Γ hwd).component κV).val.potential ⟨τ, hτ⟩ =
      sourceIEnvelope (sourceNAComponentBackground (θ.nativeHolomorphicPullback hι) κV)
        (SGPT.Trace.sourceTraceEnvelope omega' omegaV' hι
          (atlasClosedFormToNative θ + (sourceKahlerFormRepresentative κ).form)
          ((Γ.component κ).val.potential ⟨τ, hτκ⟩) hdef) := by
  obtain ⟨hT, hψ, hpos⟩ := Classical.choose_spec hdef
  rw [naTraceRes_potential hk omegaX omegaV hι hvol Γ hwd κV κ τ hτ hτκ omega' omegaV' hT]
  have hP := SGPT.PSH.GlobalPComparison.sourcePEquivalent_singularityEnvelope omegaV'
    (ClosedRealOneOneForm.pullback hι
      (atlasClosedFormToNative θ + (sourceKahlerFormRepresentative κ).form)) hψ hpos
  have hq1 : (ofFixedModel k V).IsQPSH (Classical.choose hdef) :=
    isQPSH_of_sourceTrace hι hT
  have hq2 : (ofFixedModel k V).IsQPSH (SGPT.Trace.sourceTraceEnvelope omega' omegaV' hι
      (atlasClosedFormToNative θ + (sourceKahlerFormRepresentative κ).form)
      ((Γ.component κ).val.potential ⟨τ, hτκ⟩) hdef) := by
    refine ⟨nativeClosedFormToAtlas (ClosedRealOneOneForm.pullback hι
      (atlasClosedFormToNative θ + (sourceKahlerFormRepresentative κ).form)),
      (isThetaPSH_iff_nativeThetaPotential _ _).mpr ?_⟩
    rw [sourceNativeAtlasForm_roundTrip]
    exact FirstPass.singularityEnvelope_isThetaPshPotential _
      (ClosedRealOneOneForm.pullback hι _).property.1
      (ClosedRealOneOneForm.pullback hι _).property.2 hψ.1.hasSmoothLocalPotentials _ hψ
  exact sourceIEnvelope_eq_of_equivalent
    ⟨sourceIOrder_of_sourcePOrder hq1 hq2 hP.1, sourceIOrder_of_sourcePOrder hq2 hq1 hP.2⟩

/-- `Tr_Y(Γ)` is the unique element of `PSH^NA(V, ι^*θ)` with the cutoff and slices of
`def:NApotential:L623`. -/
theorem naTraceRes_unique (Γ : SourceNAPotential θ) (hwd : TraceWellDefined ι Γ)
    (Δ : SourceNAPotential (θ.nativeHolomorphicPullback hι))
    (hmax : ∀ κV : SourceKahlerForm k V,
      (Δ.component κV).val.max = traceCutoff ι Γ (sourceKahlerFormOfBackground omegaX))
    (hpot : ∀ (κV : SourceKahlerForm k V) (τ : ℝ) (hτ : τ < (Δ.component κV).val.max)
      (hτκ : τ < (Γ.component (sourceKahlerFormOfBackground omegaX)).val.max) {ψ : V → EReal},
      IsSourceTraceRepresentativeAlong omegaX omegaV hι
        ((Γ.component (sourceKahlerFormOfBackground omegaX)).val.potential ⟨τ, hτκ⟩) ψ →
      (Δ.component κV).val.potential ⟨τ, hτ⟩ =
        sourceIEnvelope (sourceNAComponentBackground (θ.nativeHolomorphicPullback hι) κV) ψ) :
    Δ = naTraceRes hk omegaX omegaV hι hvol Γ hwd := by
  apply SourceNAPotential.ext
  intro κV
  apply Subtype.ext
  apply SourceTestCurve.ext_of_max_potential
  · exact hmax κV
  · intro r hr hs
    have hτ0 := sliceTraceable_of_lt_traceCutoff hwd (sourceKahlerFormOfBackground omegaX) hs
    rw [hpot κV r hr hτ0.1 (traceSlice_spec hk omegaX omegaV hι Γ r hτ0)]
    rfl

/-- When Kähler forms pull back to Kähler forms (smooth `Y`), the generalized trace is the trace
`NATrace.naTrace` of `NATraceSmooth`. -/
theorem naTraceRes_eq_naTrace
    (hpull : ∀ w : KahlerBackground n X, (ClosedRealOneOneForm.pullback hι w.form).val.IsKahler)
    (Γ : SourceNAPotential θ) (hwd : TraceWellDefined ι Γ) :
    naTraceRes hk omegaX omegaV hι hvol Γ hwd = naTrace hk omegaX omegaV hι hpull Γ hwd :=
  naTrace_unique hk omegaX omegaV hι hpull Γ hwd _
    (fun κV => naTraceRes_max hk omegaX omegaV hι hvol Γ hwd κV _)
    (fun κV τ hτ hτκ _ψ hψ => naTraceRes_potential hk omegaX omegaV hι hvol Γ hwd κV _ τ hτ hτκ
      omegaX omegaV hψ)

end TraceMetric

/-! ### The source-facing statement for targets with Kähler pullbacks of positive volume -/

section Source

/-- Source `def:NApotential:L623` for a target `ι : V → X` (compact connected complex manifold)
whose Kähler pullbacks have positive volume: if the trace of `Γ ∈ PSH^NA(X, θ)` along `ι` is
well-defined, there is a unique `Tr(Γ) ∈ PSH^NA(V, ι^*θ)` such that every component has the
cutoff `sup {τ < Γ_max : ν(Γ^{θ+ω}_τ, ι) = 0}` and, for `τ` below it, the slices
`Tr(Γ)^{ι^*θ+κ}_τ = P_{ι^*θ+κ}[ψ]_𝓘` for every Kähler form `ω̃` of `X` and every trace operator
`ψ` of `Γ^{θ+ω̃}_τ` along `ι`. -/
theorem source_naTraceRes (hk : k ≤ n) {ι : V → X}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (hvol : PullbackKahlerVolumePos (M := X) hι)
    (omegaX : KahlerBackground n X) (omegaV : KahlerBackground k V) (Γ : SourceNAPotential θ)
    (hwd : TraceWellDefined ι Γ) :
    ∃! Δ : SourceNAPotential (θ.nativeHolomorphicPullback hι),
      (∀ (κV : SourceKahlerForm k V) (κ : SourceKahlerForm n X),
        (Δ.component κV).val.max = traceCutoff ι Γ κ) ∧
      ∀ (κV : SourceKahlerForm k V) (κ : SourceKahlerForm n X) (τ : ℝ)
        (hτ : τ < (Δ.component κV).val.max) (hτκ : τ < (Γ.component κ).val.max)
        (omega' : KahlerBackground n X) (omegaV' : KahlerBackground k V) (ψ : V → EReal),
        IsSourceTraceRepresentativeAlong omega' omegaV' hι
          ((Γ.component κ).val.potential ⟨τ, hτκ⟩) ψ →
        (Δ.component κV).val.potential ⟨τ, hτ⟩ =
          sourceIEnvelope (sourceNAComponentBackground (θ.nativeHolomorphicPullback hι) κV) ψ := by
  refine ⟨naTraceRes hk omegaX omegaV hι hvol Γ hwd,
    ⟨fun κV κ => naTraceRes_max hk omegaX omegaV hι hvol Γ hwd κV κ,
      fun κV κ τ hτ hτκ omega' omegaV' ψ hψ =>
        naTraceRes_potential hk omegaX omegaV hι hvol Γ hwd κV κ τ hτ hτκ omega' omegaV' hψ⟩, ?_⟩
  rintro Δ ⟨hmax, hpot⟩
  exact naTraceRes_unique hk omegaX omegaV hι hvol Γ hwd Δ
    (fun κV => hmax κV _) (fun κV τ hτ hτκ ψ hψ => hpot κV _ τ hτ hτκ omegaX omegaV ψ hψ)

end Source

/-! ### Source `def:NApotential:L623` for an arbitrary irreducible `Y`, read on a resolution -/

section Resolution

open SGPT.Trace.Trace2Resolution

variable {Y : ClosedIrreducibleAnalyticSubvariety n X}

/-- On a resolution target, the generic Lelong condition of a slice is the book's
`ν(Γ^{θ+ω}_τ, Y) = 0`, with `ν(·, Y)` the generic Lelong number along `Y`. -/
theorem sliceTraceable_resolution_iff (R : ResolutionTarget Y) (Γ : SourceNAPotential θ)
    (κ : SourceKahlerForm n X) (τ : ℝ) :
    SliceTraceable R.ι Γ κ τ ↔ ∃ h : τ < (Γ.component κ).val.max,
      (ofFixedModel n X).sourceGenericLelong ((Γ.component κ).val.potential ⟨τ, h⟩) Y.carrier =
        0 := by
  unfold SliceTraceable
  simp_rw [sourceGenericLelongNumber_eq_sourceGenericLelong R.isResolutionOf.range_eq]

/-- On a resolution target, `TraceWellDefined` is the book's condition: `ν(Γ^{θ+ω}_τ, Y) = 0`
for all sufficiently negative `τ` and every Kähler form `ω`. -/
theorem traceWellDefined_resolution_iff (R : ResolutionTarget Y) (Γ : SourceNAPotential θ) :
    TraceWellDefined R.ι Γ ↔ ∀ κ : SourceKahlerForm n X, ∃ τ₀ : ℝ, ∀ τ < τ₀,
      ∃ h : τ < (Γ.component κ).val.max,
        (ofFixedModel n X).sourceGenericLelong ((Γ.component κ).val.potential ⟨τ, h⟩)
          Y.carrier = 0 := by
  unfold TraceWellDefined
  simp_rw [sliceTraceable_resolution_iff R Γ]

/-- On a resolution target, `(Tr_Y Γ)_max = sup {τ < Γ_max : ν(Γ^{θ+ω}_τ, Y) = 0}` with the
book's `ν(·, Y)`. -/
theorem traceCutoff_resolution_eq (R : ResolutionTarget Y) (Γ : SourceNAPotential θ)
    (κ : SourceKahlerForm n X) :
    traceCutoff R.ι Γ κ = sSup {τ | ∃ h : τ < (Γ.component κ).val.max,
      (ofFixedModel n X).sourceGenericLelong ((Γ.component κ).val.potential ⟨τ, h⟩) Y.carrier =
        0} := by
  unfold traceCutoff
  simp_rw [sliceTraceable_resolution_iff R Γ κ]

/-- The well-definedness condition and `(Tr_Y Γ)_max` do not depend on the resolution target. -/
theorem traceCutoff_resolution_independent (R₁ R₂ : ResolutionTarget Y)
    (Γ : SourceNAPotential θ) (κ : SourceKahlerForm n X) :
    (TraceWellDefined R₁.ι Γ ↔ TraceWellDefined R₂.ι Γ) ∧
      traceCutoff R₁.ι Γ κ = traceCutoff R₂.ι Γ κ := by
  rw [traceWellDefined_resolution_iff R₁, traceWellDefined_resolution_iff R₂,
    traceCutoff_resolution_eq R₁, traceCutoff_resolution_eq R₂]
  exact ⟨Iff.rfl, rfl⟩

/-- **Source `def:NApotential:L623` for an arbitrary irreducible `Y`, read on a resolution
target `(Y', ι)` of `Y`**: the trace `Tr_Y(Γ) ∈ PSH^NA(Y', θ|_{Y'})`. -/
def naTraceResolution (R : ResolutionTarget Y) (omegaX : KahlerBackground n X)
    (Γ : SourceNAPotential θ) (hwd : TraceWellDefined R.ι Γ) :
    SourceNAPotential (θ.nativeHolomorphicPullback R.contMDiff) :=
  naTraceRes Y.dim_le omegaX R.kahler R.contMDiff (SGPT.Trace.RIsoB.pullbackKahlerVolumePos R) Γ
    hwd

/-- **Source `def:NApotential:L623` for an arbitrary irreducible analytic subset `Y ⊆ X`, read on
any resolution target `(Y', ι)` of `Y`** (`Y'` a compact connected Kähler manifold of dimension
`dim Y`, `ι : Y' → X` a resolution of `Y`; for smooth `Y` one may take `Y' = Y = Ỹ`): if the
trace of `Γ ∈ PSH^NA(X, θ)` along `Y` is well-defined (`ν(Γ^{θ+ω}_τ, Y) = 0` for all sufficiently
negative `τ` and every `ω`, `traceWellDefined_resolution_iff`), there is a unique
`Tr_Y(Γ) ∈ PSH^NA(Y', θ|_{Y'})` such that every component (at every Kähler form `κ` of `Y'`) has
the cutoff `(Tr_Y Γ)_max = sup {τ < Γ_max : ν(Γ^{θ+ω}_τ, Y) = 0}` (for every Kähler form `ω` of
`X`; `traceCutoff_resolution_eq`) and, for `τ < (Tr_Y Γ)_max`, the slices
`Tr_Y(Γ)^{θ|_{Y'}+κ}_τ = P_{θ|_{Y'}+κ}[ψ]_𝓘` for every Kähler form `ω̃` of `X` and every trace
operator `ψ` of `Γ^{θ+ω̃}_τ` along `Y` (arbitrary auxiliary choices: the choice of the trace
operator is irrelevant). -/
theorem source_naTrace_resolution (R : ResolutionTarget Y) (omegaX : KahlerBackground n X)
    (Γ : SourceNAPotential θ) (hwd : TraceWellDefined R.ι Γ) :
    ∃! Δ : SourceNAPotential (θ.nativeHolomorphicPullback R.contMDiff),
      (∀ (κV : SourceKahlerForm Y.dim R.V) (κ : SourceKahlerForm n X),
        (Δ.component κV).val.max = traceCutoff R.ι Γ κ) ∧
      ∀ (κV : SourceKahlerForm Y.dim R.V) (κ : SourceKahlerForm n X) (τ : ℝ)
        (hτ : τ < (Δ.component κV).val.max) (hτκ : τ < (Γ.component κ).val.max)
        (omega' : KahlerBackground n X) (omegaV' : KahlerBackground Y.dim R.V)
        (ψ : R.V → EReal),
        IsSourceTraceRepresentativeAlong omega' omegaV' R.contMDiff
          ((Γ.component κ).val.potential ⟨τ, hτκ⟩) ψ →
        (Δ.component κV).val.potential ⟨τ, hτ⟩ =
          sourceIEnvelope (sourceNAComponentBackground
            (θ.nativeHolomorphicPullback R.contMDiff) κV) ψ :=
  source_naTraceRes Y.dim_le R.contMDiff (SGPT.Trace.RIsoB.pullbackKahlerVolumePos R) omegaX
    R.kahler Γ hwd

/-- The trace read on a resolution target is `naTraceResolution`, with the cutoff and slices of
`def:NApotential:L623`. -/
theorem naTraceResolution_spec (R : ResolutionTarget Y) (omegaX : KahlerBackground n X)
    (Γ : SourceNAPotential θ) (hwd : TraceWellDefined R.ι Γ) :
    (∀ (κV : SourceKahlerForm Y.dim R.V) (κ : SourceKahlerForm n X),
        ((naTraceResolution R omegaX Γ hwd).component κV).val.max = traceCutoff R.ι Γ κ) ∧
      ∀ (κV : SourceKahlerForm Y.dim R.V) (κ : SourceKahlerForm n X) (τ : ℝ)
        (hτ : τ < ((naTraceResolution R omegaX Γ hwd).component κV).val.max)
        (hτκ : τ < (Γ.component κ).val.max)
        (omega' : KahlerBackground n X) (omegaV' : KahlerBackground Y.dim R.V)
        (ψ : R.V → EReal),
        IsSourceTraceRepresentativeAlong omega' omegaV' R.contMDiff
          ((Γ.component κ).val.potential ⟨τ, hτκ⟩) ψ →
        ((naTraceResolution R omegaX Γ hwd).component κV).val.potential ⟨τ, hτ⟩ =
          sourceIEnvelope (sourceNAComponentBackground
            (θ.nativeHolomorphicPullback R.contMDiff) κV) ψ :=
  ⟨fun κV κ => naTraceRes_max Y.dim_le omegaX R.kahler R.contMDiff
      (SGPT.Trace.RIsoB.pullbackKahlerVolumePos R) Γ hwd κV κ,
    fun κV κ τ hτ hτκ omega' omegaV' _ψ hψ => naTraceRes_potential Y.dim_le omegaX R.kahler
      R.contMDiff (SGPT.Trace.RIsoB.pullbackKahlerVolumePos R) Γ hwd κV κ τ hτ hτκ omega'
      omegaV' hψ⟩

end Resolution

end SGPT.NAPotential.TraceRes

end
