import SGPT.Trace.TraceEnvelope
import SGPT.Trace.ModificationTrace
import SGPT.Okounkov.SourceTraceOperations
import SGPT.Okounkov.SourceTraceChoices
import SGPT.PSH.SourceGenericLelong
import SGPT.Foundations.Analysis.Pending.HironakaResolutionKahler
import SGPT.Foundations.Analysis.Pending.HironakaResolutionSpaceSingular
import SGPT.Foundations.Analysis.Pending.StrictTransformSubvarietySequence
import SGPT.Foundations.Analysis.Pending.PureDimension
import SGPT.Foundations.Analysis.Pending.HironakaChowLemma

/-!
# The trace operator along an arbitrary irreducible analytic subset, read on a resolution

Source: `chapter_trace.tex`, Sections "The definition of the trace operator" and "Properties of
the trace operator" (`def:traceop`, `prop:traceindquasiequisingapp`, `prop:traceunique`,
`prop:Trdominarest`, `ex:resanalyt`, `prop:tracelinear`, `prop:tracedeclimit`,
`lma:rescommpullback`), and Appendix B (`thm:res`, `cor:PSH`). Blueprint: `claude-trace2.tex`.

The book takes the trace of `φ ∈ QPSH(X)` along an irreducible analytic subset `Y` of a compact
connected Kähler manifold `X` with values on the normalization `Ỹ` of `Y`, a normal (hence
unibranch) compact Kähler space, whose pluripotential theory is that of any resolution
`ν : Y' → Ỹ` (`cor:PSH`: `ν^* : PSH(Ỹ, θ) ≅ PSH(Y', ν^*θ)`; non-pluripolar products, `P`-envelopes,
`𝓘`-envelopes, `d_S` on `Ỹ` are defined "mutatis mutandis", resp. through a resolution,
`def:unibranch:L212`). The existing trace theory (`SGPT.Trace.SmoothTarget`,
`SGPT.Okounkov.SourceTraceOperations`, ...) is stated for an arbitrary compact connected complex
manifold `V` with a holomorphic map `ι : V → X`. This file supplies the targets `V` for an
arbitrary irreducible `Y`:

* `IsResolutionOf Y ι`: `ι : V → X` (from a compact connected complex manifold `V` of dimension
  `dim Y`) is a resolution of `Y`: its image is `Y`, and over the complement of a closed analytic
  subset `B ⊇ Y_sing` it is injective with dense preimage. (Over `Y \ B ⊆ Y_reg` it is then a
  bijective holomorphic map between manifolds of the same dimension, i.e. a biholomorphism, and
  `ι⁻¹(B)` is a nowhere dense analytic subset: `ι` is a proper bimeromorphic morphism onto `Y`, a
  *resolution* in the sense of `def:primdiv`. Every resolution of `Y` factors through `Ỹ` and is a
  resolution of `Ỹ`.)
* `ResolutionTarget Y`: the bundled data (a compact connected Kähler manifold `V` of dimension
  `dim Y` with a resolution `ι : V → X` of `Y`).
* `exists_resolutionTarget` (**`thm:res` for `Y`, via G11a**): every irreducible analytic subset
  `Y` of a compact Kähler manifold has a resolution target: the strict transform of `Y` under the
  embedded resolution of `Y` (`HironakaResolutionSpace.exists_isStrictTransformResolution_of_isAnalytic`),
  connected because `Y` is irreducible, with the restriction of a Kähler form of the resolved
  ambient manifold.
* `sourceGenericLelongNumber_eq_sourceGenericLelong`: for a resolution, the generic Lelong number
  along `ι` is the book's `ν(φ, Y) = min_{x ∈ Y} ν(φ, x)` (`def:pshfunctions:L1101`).

The statements of the trace chapter for an arbitrary irreducible `Y`, read on a resolution target
(i.e. pulled back from `Ỹ` along a resolution `Y' → Ỹ`), are then: `exists_trace`,
`trace_independent_of_qea`, `tendsto_restricted_singularityDistance_zero`, `trace_unique`,
`sourcePOrder_restriction_trace`, `sourcePEquivalent_trace_restriction_of_analytic`,
`trace_linear`, `tendsto_trace_of_antitone_net`, and the comparison of traces along two
resolutions one of which dominates the other (`trace_comp_of_dominates`) and the general
`lma:rescommpullback` (`trace_pullback_of_modification`).

What is **not** formalized: the normalization `Ỹ` itself as a normal Kähler space and the
transport `cor:PSH` between `PSH(Ỹ, θ|_Ỹ)` and `PSH(Y', ν^*θ)` (with `P`-order, `𝓘`-goodness and
`d_S` on `Ỹ`); and the existence of a resolution dominating two given resolutions (needed to
compare traces read on two arbitrary resolutions).
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology Manifold ENNReal ContDiff

universe u

namespace SGPT.Trace.Trace2Resolution

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences
  SGPT.Foundations.Analysis.Pending
  SourceTraceRepresentativeDefinition SquaredLogLelongSourceNormalization
open HironakaEmbeddedAnalytic (singularSet)

/-! ### Resolutions of an irreducible analytic subset -/

section Resolution

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- `ι : V → X` is a **resolution** of the irreducible analytic subset `Y` (`V` being a compact
connected complex manifold of dimension `dim Y`, `ι` holomorphic): the image of `ι` is `Y`, and
there is a closed analytic subset `B ⊆ X` containing the singular locus of `Y` such that `ι` is
injective over `X \ B` and `ι⁻¹(X \ B)` is dense in `V`. Over `Y \ B ⊆ Y_reg` the map `ι` is then
a bijective holomorphic map between manifolds of the same dimension, hence biholomorphic, so `ι`
is a proper bimeromorphic morphism onto `Y` (`def:primdiv`). -/
structure IsResolutionOf (Y : ClosedIrreducibleAnalyticSubvariety n X) {V : Type*}
    [TopologicalSpace V] (ι : V → X) : Prop where
  range_eq : range ι = Y.carrier
  exists_isoLocus : ∃ B : Set X, IsComplexAnalyticSubset (n := n) B ∧ singularLocus Y ⊆ B ∧
    InjOn ι (ι ⁻¹' Bᶜ) ∧ Dense (ι ⁻¹' Bᶜ)

/-- A **resolution target** of the irreducible analytic subset `Y ⊆ X`: a compact connected
Kähler manifold `V` of dimension `dim Y` with a holomorphic resolution `ι : V → X` of `Y`. It is
a resolution `Y' → Ỹ` of the normalization `Ỹ` of `Y`, on which the book's trace `Tr_Y` is read. -/
structure ResolutionTarget (Y : ClosedIrreducibleAnalyticSubvariety n X) where
  /-- The resolving manifold. -/
  V : Type u
  [topologicalSpace : TopologicalSpace V]
  [chartedSpace : ChartedSpace (ComplexModel Y.dim) V]
  [isComplexManifold : IsComplexManifold Y.dim V]
  [compactSpace : CompactSpace V]
  [connectedSpace : ConnectedSpace V]
  /-- The resolution map. -/
  ι : V → X
  contMDiff : ContMDiff 𝓘(ℂ, ComplexModel Y.dim) 𝓘(ℂ, ComplexModel n) ∞ ι
  isResolutionOf : IsResolutionOf Y ι
  /-- A Kähler form on the resolving manifold. -/
  kahler : KahlerBackground Y.dim V

attribute [instance] ResolutionTarget.topologicalSpace ResolutionTarget.chartedSpace
  ResolutionTarget.isComplexManifold ResolutionTarget.compactSpace ResolutionTarget.connectedSpace

variable {Y : ClosedIrreducibleAnalyticSubvariety n X}

instance ResolutionTarget.instMeasurableSpace (R : ResolutionTarget Y) : MeasurableSpace R.V :=
  borel R.V

instance ResolutionTarget.instBorelSpace (R : ResolutionTarget Y) : BorelSpace R.V := ⟨rfl⟩

/-- The singular set of `Y` (points regular in no dimension) is the singular locus
`Y \ Y_reg` (regular points of dimension `dim Y`), because `Y` is pure-dimensional. -/
theorem singularSet_eq_singularLocus (Y : ClosedIrreducibleAnalyticSubvariety n X) :
    singularSet (n := n) Y.carrier = singularLocus Y := by
  ext x
  rw [HironakaEmbeddedAnalytic.mem_singularSet_iff]
  constructor
  · rintro ⟨hx, hreg⟩
    exact ⟨hx, hreg Y.dim⟩
  · rintro ⟨hx, hreg⟩
    refine ⟨hx, fun k hk => hreg ?_⟩
    have hkd := PureDimension.eq_dim_of_regularAtDim Y hk
    rw [hkd] at hk
    exact hk

/-- **`thm:res` for an irreducible analytic subset of a compact Kähler manifold (G11a).** Every
irreducible analytic subset `Y` of a compact complex manifold `X` with a Kähler form has a
resolution target: the strict transform `Y'` of `Y` under the embedded resolution of `Y` (a
finite sequence of blowups `σ : X' → X` with smooth centres over `Y_sing`), a compact connected
complex manifold of dimension `dim Y` with the restriction of a Kähler form of `X'`, and
`ι = σ|_{Y'}`. -/
theorem exists_resolutionTarget [CompactSpace X] (omega : KahlerBackground n X)
    (Y : ClosedIrreducibleAnalyticSubvariety n X) : Nonempty (ResolutionTarget Y) := by
  have hWa : IsComplexAnalyticSubset (n := n) Y.carrier := Y.analytic
  have hpure : AnalyticDimensionBasics.IsPureDim (n := n) Y.carrier Y.dim :=
    fun _ _ hy => PureDimension.eq_dim_of_regularAtDim Y hy
  obtain ⟨M', _, _, _, σ, E, h, hreg, _omega', hCM, hcpt, omegaW, -, hval⟩ :=
    HironakaResolutionKahler.exists_kahler_strictTransform_resolution hWa hpure Y.dim_le omega
  let := SubmanifoldChartedSpace.chartedSpace Y.dim_le hreg
  have hExcS : σ '' exceptionalLocus n σ ⊆ singularLocus Y := by
    rintro _ ⟨y, hy, rfl⟩
    by_contra hx
    have hc : σ y ∈ (singularSet (n := n) Y.carrier)ᶜ := by
      rw [singularSet_eq_singularLocus]
      exact hx
    exact Set.disjoint_left.mp h.isIsomorphismOver.2 hc hy
  have hconn := StrictTransformSubvarietySequence.isConnected_strictTransform_of_isBlowupSequence
    h.isBlowupSequence Y hExcS
  have : ConnectedSpace (strictTransform n σ Y.carrier) :=
    isConnected_iff_connectedSpace.mp hconn
  refine ⟨{
    V := strictTransform n σ Y.carrier
    ι := σ ∘ Subtype.val
    contMDiff := h.contMDiff.comp hval
    isResolutionOf := ?_
    kahler := omegaW }⟩
  refine ⟨?_, singularSet (n := n) Y.carrier,
    HironakaResolutionSpaceSingular.isComplexAnalyticSubset_singularSet hWa,
    (singularSet_eq_singularLocus Y).symm.subset, ?_, ?_⟩
  · rw [range_comp, Subtype.range_coe]
    exact h.image_eq
  · intro y₁ hy₁ y₂ hy₂ heq
    exact Subtype.ext (h.isIsomorphismOver.1.injOn hy₁ hy₂ heq)
  · rw [dense_iff_closure_eq, eq_univ_iff_forall]
    intro x
    rw [closure_subtype]
    have hx : x.1 ∈ closure (σ ⁻¹' (Y.carrier \ singularSet (n := n) Y.carrier)) := by
      rw [← h.eq_closure]
      exact x.2
    refine closure_mono ?_ hx
    intro z hz
    have hz' : z ∈ strictTransform n σ Y.carrier ∩ σ ⁻¹' (singularSet (n := n) Y.carrier)ᶜ := by
      rw [h.inter_preimage_compl]
      exact hz
    exact ⟨⟨z, hz'.1⟩, hz'.2, rfl⟩

/-- **The generic Lelong number along a resolution.** If the image of `ι` is `Y`, the generic
Lelong number along `ι` used in the trace predicate (`sourceGenericLelongNumber`) is the book's
`ν(φ, Y) = min_{x ∈ Y} ν(φ, x)` (`def:pshfunctions:L1101`, `sourceGenericLelong`). -/
theorem sourceGenericLelongNumber_eq_sourceGenericLelong {V : Type*} {ι : V → X}
    (hrange : range ι = Y.carrier) (u : X → EReal) :
    sourceGenericLelongNumber (n := n) ι u =
      (SGPT.PSH.VariableComplexAtlas.ofFixedModel n X).sourceGenericLelong u Y.carrier := by
  unfold sourceGenericLelongNumber SGPT.PSH.VariableComplexAtlas.sourceGenericLelong
  simp_rw [SGPT.PSH.VariableComplexAtlas.sourceLelong_ofFixedModel_eq]
  rw [← hrange, iInf_range]

end Resolution

/-! ### The trace operator along `Y`, read on a resolution -/

section Trace

open SingularGlobalPOrder ThetaPshL1Topology SingularCanonicalSingularityDistance
  SGPT.Foundations.Analysis.FirstPass.IEnvelope SGPT.Foundations.Analysis.FirstPass.TraceBackground
  SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
  PluripolarCapacityDichotomy AnalyticModificationLocalDiscrepancy

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [CompactSpace X] {Y : ClosedIrreducibleAnalyticSubvariety n X}
  (R : ResolutionTarget Y)

omit [CompactSpace X] in
/-- The generic clause of the trace predicate along a resolution is the book's `ν(φ, Y) = 0`. -/
theorem sourceGenericLelong_eq_zero_of_trace {omega : KahlerBackground n X} {omegaV : KahlerBackground Y.dim R.V}
    {u : X → EReal} {τ : R.V → EReal}
    (htrace : IsSourceTraceRepresentativeAlong omega omegaV R.contMDiff u τ) :
    (SGPT.PSH.VariableComplexAtlas.ofFixedModel n X).sourceGenericLelong u Y.carrier = 0 :=
  (sourceGenericLelongNumber_eq_sourceGenericLelong R.isResolutionOf.range_eq u).symm.trans
    htrace.1

/-- **Source `def:traceop` for an arbitrary irreducible `Y` (existence), read on a resolution.**
Every quasi-psh `φ` with `ν(φ, Y) = 0` has a trace operator along `Y` (on every resolution
target of `Y`). -/
theorem exists_trace (omega : KahlerBackground n X) {u : X → EReal}
    (hu : IsGlobalQuasiPshPotential (n := n) u)
    (hν : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n X).sourceGenericLelong u Y.carrier = 0) :
    ∃ τ : R.V → EReal, IsSourceTraceRepresentativeAlong omega R.kahler R.contMDiff u τ :=
  SGPT.TraceOperations.exists_sourceTrace_of_globalQuasiPshPotential Y.dim_le omega R.kahler hu
    R.contMDiff ((sourceGenericLelongNumber_eq_sourceGenericLelong R.isResolutionOf.range_eq u).trans
      hν)

/-- **Source `def:traceop` for an arbitrary irreducible `Y` (independence of the choices),
read on a resolution.** If `τ` is a trace operator of `u` along `Y`, then for every
quasi-equisingular approximation `(vSeq)` of `u` and every admissible Kähler background `β` on
the resolution with `τ ∈ PSH(Y', β)`, `vSeq j|_{Y'} → τ` in `d_{S,β}`. -/
theorem trace_independent_of_qea {omega₀ omega₁ : KahlerBackground n X}
    {u : X → EReal} {τ : R.V → EReal}
    (htrace : IsSourceTraceRepresentativeAlong omega₀ R.kahler R.contMDiff u τ)
    {θ : ClosedRealOneOneForm n X} {ε : ℕ → ℝ} {vSeq : ℕ → X → EReal}
    (happ : IsQuasiEquisingularApproximation omega₁ θ u ε vSeq)
    (β : KahlerBackground Y.dim R.V) (hadm : IsAdmissibleTraceBackground R.contMDiff omega₁ θ ε β.form)
    (hτ : IsThetaPshPotential β.form.val τ) :
    ∃ hv : ∀ j, IsThetaPshPotential β.form.val (fun y => vSeq j (R.ι y)),
      Tendsto (fun j => (⟨fun y => vSeq j (R.ι y), hv j⟩ : ThetaPshL1 β.form.val))
        atTop (@nhds (ThetaPshL1 β.form.val)
          (singularityPseudoMetricSpace R.kahler β.form
            (isBigClass_kahler β)).toUniformSpace.toTopologicalSpace ⟨τ, hτ⟩) ∧
      IsSourceTraceRepresentativeAlong omega₁ R.kahler R.contMDiff u τ :=
  isSourceTraceRepresentativeAlong_of_qea Y.dim_le R.kahler R.contMDiff htrace happ β hadm hτ

/-- **Source `prop:traceindquasiequisingapp` for an arbitrary irreducible `Y`, read on a
resolution.** For two quasi-equisingular approximations `U`, `W` of `φ` with `ν(φ, Y) = 0` and
every big `η` on the resolution containing the restrictions, `d_{S,η}(U_j|_{Y'}, W_j|_{Y'}) → 0`. -/
theorem tendsto_restrictedDistance_zero {θ₀ θ₁ : ClosedRealOneOneForm n X} {u : X → EReal}
    {U W : ℕ → X → EReal}
    (hU : SGPT.PSH.SourceQuasiEquisingularApproximation θ₀ u U)
    (hW : SGPT.PSH.SourceQuasiEquisingularApproximation θ₁ u W)
    (hν : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n X).sourceGenericLelong u Y.carrier = 0)
    (η : ClosedRealOneOneForm Y.dim R.V) (hbig : IsBigClass (RealBottChern.ofRepresentative η))
    (hUη : ∀ j, IsThetaPshPotential η.val (fun y => U j (R.ι y)))
    (hWη : ∀ j, IsThetaPshPotential η.val (fun y => W j (R.ι y))) :
    Tendsto (fun j => singularityDistance R.kahler η hbig
      (fun y => U j (R.ι y)) (fun y => W j (R.ι y))) atTop (𝓝 0) :=
  tendsto_restricted_singularityDistance_zero Y.dim_le R.kahler hU hW R.contMDiff
    ((sourceGenericLelongNumber_eq_sourceGenericLelong R.isResolutionOf.range_eq u).trans hν)
    η hbig hUη hWη

/-- **Source `prop:traceunique` for an arbitrary irreducible `Y`, read on a resolution.** Any two
trace operators of `φ` along `Y` are `𝓘`-good and `P`-equivalent. -/
theorem trace_unique {omega₀ omega₁ : KahlerBackground n X}
    {omegaV₀ omegaV₁ : KahlerBackground Y.dim R.V} {u : X → EReal} {τ₀ τ₁ : R.V → EReal}
    (htrace₀ : IsSourceTraceRepresentativeAlong omega₀ omegaV₀ R.contMDiff u τ₀)
    (htrace₁ : IsSourceTraceRepresentativeAlong omega₁ omegaV₁ R.contMDiff u τ₁) :
    IGood (n := Y.dim) τ₀ ∧ IGood (n := Y.dim) τ₁ ∧ SourcePEquivalent (n := Y.dim) τ₀ τ₁ :=
  ⟨SGPT.Okounkov.iGood_of_sourceTraceRepresentative Y.dim_le omegaV₀ R.contMDiff htrace₀,
    SGPT.Okounkov.iGood_of_sourceTraceRepresentative Y.dim_le omegaV₁ R.contMDiff htrace₁,
    SGPT.Okounkov.sourcePEquivalent_of_sourceTraceRepresentatives Y.dim_le omegaV₀ omegaV₁
      R.contMDiff htrace₀ htrace₁⟩

omit [CompactSpace X] in
/-- `φ|_Y ≢ -∞` in terms of the resolution. -/
theorem exists_ne_bot_comp {u : X → EReal} (hne : ∃ x ∈ Y.carrier, u x ≠ ⊥) :
    ∃ y : R.V, u (R.ι y) ≠ ⊥ := by
  obtain ⟨x, hx, hux⟩ := hne
  rw [← R.isResolutionOf.range_eq] at hx
  obtain ⟨y, rfl⟩ := hx
  exact ⟨y, hux⟩

omit [CompactSpace X] in
/-- **Source `prop:Trdominarest` for an arbitrary irreducible `Y`, read on a resolution.** If
`φ|_Y ≢ -∞`, then `φ|_{Y'} ⪯_P Tr_Y(φ)`. -/
theorem trace_dominates_restriction {omega : KahlerBackground n X}
    {omegaV : KahlerBackground Y.dim R.V} {u : X → EReal} {τ : R.V → EReal}
    (htrace : IsSourceTraceRepresentativeAlong omega omegaV R.contMDiff u τ)
    (hne : ∃ x ∈ Y.carrier, u x ≠ ⊥) :
    SourcePOrder (n := Y.dim) (fun y => u (R.ι y)) τ :=
  sourcePOrder_restriction_trace Y.dim_le R.kahler R.contMDiff htrace (exists_ne_bot_comp R hne)

/-- **Source `ex:resanalyt` for an arbitrary irreducible `Y`, read on a resolution.** If `φ` has
analytic singularities, `Tr_Y(φ) ∼_P φ|_{Y'}`. -/
theorem trace_equiv_restriction_of_analytic {omega : KahlerBackground n X}
    {omegaV : KahlerBackground Y.dim R.V} {u : X → EReal} {τ : R.V → EReal}
    (htrace : IsSourceTraceRepresentativeAlong omega omegaV R.contMDiff u τ)
    (hA : HasManifoldAnalyticSingularityType (n := n) u) :
    SourcePEquivalent (n := Y.dim) τ (fun y => u (R.ι y)) :=
  sourcePEquivalent_trace_restriction_of_analytic Y.dim_le R.kahler R.contMDiff htrace hA

/-- **Source `prop:tracelinear` for an arbitrary irreducible `Y`, read on a resolution.** For
trace operators `τ_φ`, `τ_ψ`, `τ_{φ+ψ}`, `τ_{λφ}`, `τ_{φ∨ψ}` of `φ`, `ψ`, `φ + ψ`, `λφ`
(`λ > 0`), `φ ∨ ψ` along `Y`: (1) `φ ⪯_𝓘 ψ` implies `τ_φ ⪯_P τ_ψ`; (2) `τ_{φ+ψ} ∼_P τ_φ + τ_ψ`;
(3) `τ_{λφ} ∼_P λ τ_φ`; (4) `τ_{φ∨ψ} ∼_P τ_φ ∨ τ_ψ`. -/
theorem trace_linear {omega₀ omega₁ omega₂ omega₃ omega₄ : KahlerBackground n X}
    {ωV₀ ωV₁ ωV₂ ωV₃ ωV₄ : KahlerBackground Y.dim R.V} {u v : X → EReal} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {τu τv τs τℓ τm : R.V → EReal}
    (hTu : IsSourceTraceRepresentativeAlong omega₀ ωV₀ R.contMDiff u τu)
    (hTv : IsSourceTraceRepresentativeAlong omega₁ ωV₁ R.contMDiff v τv)
    (hTs : IsSourceTraceRepresentativeAlong omega₂ ωV₂ R.contMDiff (fun x => u x + v x) τs)
    (hTℓ : IsSourceTraceRepresentativeAlong omega₃ ωV₃ R.contMDiff
      (fun x => (ℓ : EReal) * u x) τℓ)
    (hTm : IsSourceTraceRepresentativeAlong omega₄ ωV₄ R.contMDiff
      (fun x => max (u x) (v x)) τm) :
    (IOrderOnManifold (n := n) u v → SourcePOrder (n := Y.dim) τu τv) ∧
      SourcePEquivalent (n := Y.dim) τs (fun y => τu y + τv y) ∧
      SourcePEquivalent (n := Y.dim) τℓ (fun y => (ℓ : EReal) * τu y) ∧
      SourcePEquivalent (n := Y.dim) τm (fun y => max (τu y) (τv y)) :=
  ⟨fun hI => SGPT.TraceOperations.sourcePOrder_of_iOrder_of_sourceTraceRepresentatives Y.dim_le
      ωV₀ ωV₁ R.contMDiff hTu hTv hI,
    SGPT.TraceOperations.sourcePEquivalent_add_of_sourceTraceRepresentatives Y.dim_le ωV₀ ωV₁ ωV₂
      R.contMDiff hTu hTv hTs,
    SGPT.TraceOperations.sourcePEquivalent_pos_smul_of_sourceTraceRepresentatives Y.dim_le ωV₀ ωV₃
      R.contMDiff hTu hℓ hTℓ,
    SGPT.TraceOperations.sourcePEquivalent_max_of_sourceTraceRepresentatives Y.dim_le ωV₀ ωV₁ ωV₄
      R.contMDiff hTu hTv hTm⟩

/-- **Source `prop:tracedeclimit` for an arbitrary irreducible `Y`, read on a resolution.** For a
decreasing net `u_i` in `PSH(X, θ)` (`θ` big) converging in `d_S` to `u`, and trace operators
`τ_i`, `τ` of `u_i`, `u` along `Y` (all in `PSH(Y', η)`, `η` big), `τ_i → τ` in `d_{S,η}`. -/
theorem tendsto_trace_of_antitone_net [MeasurableSpace X] [BorelSpace X] [ConnectedSpace X]
    (omega : KahlerBackground n X)
    (θ : ClosedRealOneOneForm n X) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (ui : I → ThetaPshL1 θ.val) (u : ThetaPshL1 θ.val)
    (hanti : ∀ x, Antitone fun i => (ui i).val x)
    (hlim : Tendsto ui atTop (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace u))
    (η : ClosedRealOneOneForm Y.dim R.V) (hη : IsBigClass (RealBottChern.ofRepresentative η))
    (τi : I → ThetaPshL1 η.val) (τ : ThetaPshL1 η.val)
    {omegai : I → KahlerBackground n X} {omegaVi : I → KahlerBackground Y.dim R.V}
    {omega₀ : KahlerBackground n X} {omegaV₀ : KahlerBackground Y.dim R.V}
    (hTi : ∀ i, IsSourceTraceRepresentativeAlong (omegai i) (omegaVi i) R.contMDiff
      (ui i).val (τi i).val)
    (hT : IsSourceTraceRepresentativeAlong omega₀ omegaV₀ R.contMDiff u.val τ.val) :
    Tendsto τi atTop (@nhds (ThetaPshL1 η.val)
      (singularityPseudoMetricSpace R.kahler η hη).toUniformSpace.toTopologicalSpace τ) :=
  SGPT.Trace.tendsto_trace_of_antitone_net Y.dim_le omega R.kahler θ hbig ui u hanti hlim
    R.contMDiff η hη τi τ hTi hT

/-- **Traces read on two resolutions, one dominating the other.** If `p : Y'₂ → Y'₁` is a proper
modification between two resolution targets of `Y` with `ι₂ = ι₁ ∘ p`, then for every trace
operator `τ` of `φ` along `Y` read on `Y'₁`, `τ ∘ p` is a trace operator read on `Y'₂`, and every
trace operator read on `Y'₂` is `P`-equivalent to `τ ∘ p`. (So the trace read on a resolution
does not depend on the resolution, up to a dominating one.) -/
theorem trace_comp_of_dominates [MeasurableSpace X] [BorelSpace X] [ConnectedSpace X]
    (R₁ R₂ : ResolutionTarget Y) {p : R₂.V → R₁.V}
    (hp : IsAnalyticModification (n := Y.dim) p) (hcomm : ∀ w, R₂.ι w = R₁.ι (p w))
    (omega : KahlerBackground n X) {omegaV : KahlerBackground Y.dim R₁.V} {u : X → EReal}
    {τ : R₁.V → EReal} (htrace : IsSourceTraceRepresentativeAlong omega omegaV R₁.contMDiff u τ) :
    (∃ κ : KahlerBackground n X,
        IsSourceTraceRepresentativeAlong κ R₂.kahler R₂.contMDiff u (τ ∘ p)) ∧
      ∀ (omega' : KahlerBackground n X) (omegaV' : KahlerBackground Y.dim R₂.V)
        (ρ : R₂.V → EReal),
        IsSourceTraceRepresentativeAlong omega' omegaV' R₂.contMDiff u ρ →
          SourcePEquivalent (n := Y.dim) (τ ∘ p) ρ := by
  obtain ⟨-, hex, hP⟩ := SGPT.Trace.sourceTrace_modification_of_commuting Y.dim_le
    (π := (id : X → X)) HironakaChowLemma.isAnalyticModification_id hp omega omega omegaV
    R₂.kahler R₁.contMDiff R₂.contMDiff (fun w => hcomm w) htrace
  exact ⟨hex, fun omega' omegaV' ρ hρ => hP omega' omegaV' ρ hρ⟩

/-- **Source `lma:rescommpullback` for arbitrary irreducible `W`, `Y`, read on a resolution.**
Let `π : Z → X` be a proper modification of compact Kähler manifolds, `W ⊆ Z` irreducible and
`Y'_W` a resolution target of `W`. If `Π = π|_W : W → Y` is bimeromorphic, `π ∘ ι_W` is a
resolution of `Y` and, read on `Y'_W`, the book's `Π̃^* Tr_Y(φ)` is a trace operator of `φ` along
`π ∘ ι_W`. For every such trace operator `τ`: `ν(π^*φ, W) = 0`, `τ` is a trace operator of
`π^*φ` along `W` (read on `Y'_W`), and every trace operator of `π^*φ` along `W` is `P`-equivalent
to `τ` (`Π̃^* Tr_Y(φ) ∼_P Tr_W(π^*φ)`). -/
theorem trace_pullback_of_modification [MeasurableSpace X] [BorelSpace X] [ConnectedSpace X]
    {Z : Type u} [TopologicalSpace Z]
    [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z] [CompactSpace Z]
    [MeasurableSpace Z] [BorelSpace Z]
    {π : Z → X} (hπ : IsAnalyticModification (n := n) π)
    {W : ClosedIrreducibleAnalyticSubvariety n Z} (RW : ResolutionTarget W)
    (omegaX : KahlerBackground n X) (omegaZ : KahlerBackground n Z)
    {omegaV : KahlerBackground W.dim RW.V} {u : X → EReal} {τ : RW.V → EReal}
    (htrace : IsSourceTraceRepresentativeAlong omegaX omegaV (hπ.1.comp RW.contMDiff) u τ) :
    (SGPT.PSH.VariableComplexAtlas.ofFixedModel n Z).sourceGenericLelong (u ∘ π) W.carrier = 0 ∧
      (∃ κ : KahlerBackground n Z,
        IsSourceTraceRepresentativeAlong κ RW.kahler RW.contMDiff (u ∘ π) τ) ∧
      ∀ (omegaZ' : KahlerBackground n Z) (omegaW' : KahlerBackground W.dim RW.V)
        (ρ : RW.V → EReal),
        IsSourceTraceRepresentativeAlong omegaZ' omegaW' RW.contMDiff (u ∘ π) ρ →
          SourcePEquivalent (n := W.dim) τ ρ := by
  obtain ⟨h0, hex, hP⟩ := SGPT.Trace.sourceTrace_modification_of_commuting W.dim_le hπ
    (pTail := (id : RW.V → RW.V)) HironakaChowLemma.isAnalyticModification_id omegaX omegaZ
    omegaV RW.kahler (hπ.1.comp RW.contMDiff) RW.contMDiff (fun _ => rfl) htrace
  refine ⟨?_, hex, hP⟩
  rw [← sourceGenericLelongNumber_eq_sourceGenericLelong RW.isResolutionOf.range_eq]
  exact h0

end Trace

/-! ### `def:traceop2` along `Y`, read on a resolution -/

section Envelope

open SGPT.Foundations.Analysis.FirstPass.IEnvelope SGPT.Foundations.Analysis.FirstPass.POrder DiagonalMass

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [CompactSpace X] {Y : ClosedIrreducibleAnalyticSubvariety n X}
  (R : ResolutionTarget Y)

/-- **Source `def:traceop2` for an arbitrary irreducible `Y`, read on a resolution: the domain.**
Whether some trace operator of `φ` along `Y` lies in `PSH(Y', θ|_{Y'})_{>0}` (i.e. whether
`Tr^θ_Y(φ)` is defined) does not depend on the auxiliary Kähler forms. -/
theorem hasPositiveSourceTraceAlong_iff (omega₀ omega₁ : KahlerBackground n X)
    (omegaV₀ omegaV₁ : KahlerBackground Y.dim R.V) (θ : ClosedRealOneOneForm n X)
    (u : X → EReal) :
    HasPositiveSourceTraceAlong omega₀ omegaV₀ R.contMDiff θ u ↔
      HasPositiveSourceTraceAlong omega₁ omegaV₁ R.contMDiff θ u :=
  hasPositiveSourceTraceAlong_iff_auxiliary_choices Y.dim_le omega₀ omega₁ omegaV₀ omegaV₁
    R.contMDiff θ u

/-- **Source `def:traceop2` for an arbitrary irreducible `Y`, read on a resolution.** If
`Tr^θ_Y(φ)` is defined, then for EVERY trace operator `τ` (any auxiliary choices) lying in
`PSH(Y', θ|_{Y'})_{>0}`, `Tr^θ_Y(φ) = P_{θ|_{Y'}}[τ] = P_{θ|_{Y'}}[τ]_𝓘`; in particular it does not
depend on the choices. -/
theorem sourceTraceEnvelope_eq (omega₀ omega₁ : KahlerBackground n X)
    (omegaV₀ omegaV₁ : KahlerBackground Y.dim R.V) (θ : ClosedRealOneOneForm n X)
    (u : X → EReal) (hdefined : HasPositiveSourceTraceAlong omega₀ omegaV₀ R.contMDiff θ u)
    {τ : R.V → EReal} (htrace : IsSourceTraceRepresentativeAlong omega₁ omegaV₁ R.contMDiff u τ)
    (hτ : IsThetaPshPotential (ClosedRealOneOneForm.pullback R.contMDiff θ).val τ)
    (hpos : HasPositivePotentialMass (ClosedRealOneOneForm.pullback R.contMDiff θ) τ hτ) :
    sourceTraceEnvelope omega₀ omegaV₀ R.contMDiff θ u hdefined =
        singularityEnvelope (ClosedRealOneOneForm.pullback R.contMDiff θ).val τ ∧
      sourceTraceEnvelope omega₀ omegaV₀ R.contMDiff θ u hdefined =
        iSingularityEnvelope (ClosedRealOneOneForm.pullback R.contMDiff θ).val τ :=
  sourceTraceEnvelope_eq_envelopes Y.dim_le omegaV₀ omegaV₁ R.contMDiff θ u hdefined htrace hτ hpos

end Envelope

end SGPT.Trace.Trace2Resolution
