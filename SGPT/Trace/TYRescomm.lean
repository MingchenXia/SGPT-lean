import SGPT.Trace.TYTrace

/-!
# `lma:rescommpullback` on the normalizations

Source: `chapter_trace.tex`, `lma:rescommpullback`: let `π : Z → X` be a proper bimeromorphic
morphism of compact Kähler manifolds, `W ⊆ Z`, `Y ⊆ X` irreducible analytic subsets such that the
restriction `Π : W → Y` of `π` is defined and bimeromorphic, and `Π̃ : W̃ → Ỹ` the induced map of
normalizations. Then for `φ ∈ QPSH(X)` with `ν(φ, Y) = 0`, `ν(π^*φ, W) = 0` and
`Π̃^* Tr_Y(φ) ∼_P Tr_W(π^*φ)`.

* `IsBimeromorphicRestriction π W Y`: `Π = π|_W : W → Y` is bimeromorphic: `π(W) = Y`,
  `dim W = dim Y`, and `π` is injective on `W` over the complement of a closed analytic subset
  `B ⊆ X` containing `Y_sing` and not containing `Y` (a bimeromorphic map of irreducible analytic
  sets is an isomorphism over the complement of a nowhere dense analytic subset of the target,
  which may be enlarged by `Y_sing`; both have the same dimension).
* `isResolutionOf_comp`: then `π ∘ ι_W` is a resolution of `Y` for every resolution `ι_W` of `W`
  (Remmert's proper mapping theorem for the image of the bad set of `ι_W`).
* `rescommpullback`: the lemma on the normalizations, for any trace operator `ψ = Tr_Y(φ)` on `Ỹ`
  and any continuous `Π̃ : W̃ → Ỹ` over `π` (the induced map of normalizations).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Set Filter
open scoped Topology Manifold ENNReal ContDiff

universe u

namespace SGPT.Trace.TY

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
  SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
  SGPT.Foundations.Analysis.Pending.SourceTraceRepresentativeDefinition
  SGPT.Foundations.Analysis.Pending.SingularGlobalPOrder
  SGPT.Trace.Trace2Resolution SGPT.Unibranch

section Bimeromorphic

variable {n : ℕ} {X Z : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]
  [IsComplexManifold n Z]

/-- **`Π = π|_W : W → Y` is bimeromorphic** (`lma:rescommpullback`): `π(W) = Y`, `dim W = dim Y`,
and `π` is injective on `W` over the complement of a closed analytic subset `B ⊆ X` with
`Y_sing ⊆ B` and `Y ⊄ B`. -/
structure IsBimeromorphicRestriction (π : Z → X) (W : ClosedIrreducibleAnalyticSubvariety n Z)
    (Y : ClosedIrreducibleAnalyticSubvariety n X) : Prop where
  image_eq : π '' W.carrier = Y.carrier
  dim_eq : W.dim = Y.dim
  exists_isoLocus : ∃ B : Set X, IsComplexAnalyticSubset (n := n) B ∧ singularLocus Y ⊆ B ∧
    InjOn π (W.carrier ∩ π ⁻¹' Bᶜ) ∧ ¬ Y.carrier ⊆ B

/-- **A resolution of `W` composed with a bimeromorphic `Π = π|_W` is a resolution of `Y`.** -/
theorem isResolutionOf_comp [CompactSpace Z] {π : Z → X}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π)
    {W : ClosedIrreducibleAnalyticSubvariety n Z} {Y : ClosedIrreducibleAnalyticSubvariety n X}
    (hPi : IsBimeromorphicRestriction π W Y) {k : ℕ} {V : Type*} [TopologicalSpace V]
    [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V] [ConnectedSpace V] {ιW : V → Z}
    (hιW : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ιW)
    (hres : IsResolutionOf W ιW) : IsResolutionOf Y (π ∘ ιW) := by
  obtain ⟨B, hB, hsing, hinj, hYB⟩ := hPi.exists_isoLocus
  obtain ⟨BW, hBW, -, hinjW, hdenseW⟩ := hres.exists_isoLocus
  have hBWW : IsComplexAnalyticSubset (n := n) (BW ∩ W.carrier) := hBW.inter W.analytic
  have himg : IsComplexAnalyticSubset (n := n) (π '' (BW ∩ W.carrier)) :=
    ProperMappingTheorem.isComplexAnalyticSubset_image hπ hBWW fun K hK =>
      (hBWW.isClosed.inter (hK.isClosed.preimage hπ.continuous)).isCompact
  let B' : Set X := B ∪ π '' (BW ∩ W.carrier)
  have hB' : IsComplexAnalyticSubset (n := n) B' :=
    HironakaEmbeddedAnalyticLocal.isComplexAnalyticSubset_union hB himg
  have hmemW : ∀ v, ιW v ∈ W.carrier := fun v => by
    rw [← hres.range_eq]
    exact mem_range_self v
  -- a point of `V` over `Y \ B'` exists
  have hgood : ∀ v, π (ιW v) ∉ B' → ιW v ∉ BW ∧ π (ιW v) ∉ B := by
    intro v hv
    refine ⟨fun h => hv (Or.inr ⟨ιW v, ⟨h, hmemW v⟩, rfl⟩), fun h => hv (Or.inl h)⟩
  refine ⟨?_, B', hB', hsing.trans subset_union_left, ?_, ?_⟩
  · rw [range_comp, hres.range_eq, hPi.image_eq]
  · intro v₁ hv₁ v₂ hv₂ heq
    obtain ⟨h₁W, h₁B⟩ := hgood v₁ hv₁
    obtain ⟨h₂W, h₂B⟩ := hgood v₂ hv₂
    have hw : ιW v₁ = ιW v₂ := hinj ⟨hmemW v₁, h₁B⟩ ⟨hmemW v₂, h₂B⟩ heq
    exact hinjW h₁W h₂W hw
  · -- the bad set `(π ∘ ι_W)⁻¹ B'` is analytic and misses a point
    have hA : IsComplexAnalyticSubset (n := k) ((π ∘ ιW) ⁻¹' B') :=
      AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage (hπ.comp hιW) hB'
    obtain ⟨y, hyY, hyB⟩ := not_subset.mp hYB
    rw [← hPi.image_eq, ← hres.range_eq] at hyY
    obtain ⟨_, ⟨v₀, rfl⟩, hv₀⟩ := hyY
    have hopen : IsOpen ((π ∘ ιW) ⁻¹' Bᶜ) :=
      hB.isClosed.isOpen_compl.preimage (hπ.comp hιW).continuous
    obtain ⟨v, hvB, hvW⟩ := hdenseW.inter_open_nonempty _ hopen ⟨v₀, by
      change π (ιW v₀) ∈ Bᶜ
      rw [hv₀]
      exact hyB⟩
    have hvB' : v ∉ (π ∘ ιW) ⁻¹' B' := by
      rintro (h | ⟨w', ⟨hw'BW, hw'W⟩, hw'⟩)
      · exact hvB h
      · have hw'B : π w' ∉ B := by
          rw [hw']
          exact hvB
        have : w' = ιW v := hinj ⟨hw'W, hw'B⟩ ⟨hmemW v, hvB⟩ hw'
        exact hvW (this ▸ hw'BW)
    rw [preimage_compl, ← interior_eq_empty_iff_dense_compl]
    exact P5Wire.interior_eq_empty_of_not_mem hA hvB'

end Bimeromorphic

section Rescomm

variable {n : ℕ} {X Z : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [ConnectedSpace X]
  [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z] [CompactSpace Z]
  [MeasurableSpace Z] [BorelSpace Z]

/-- A trace operator `ψ` on `Ỹ` reads as a trace operator along every resolution `ι` of `Y` from a
compact connected Kähler manifold of dimension `d = dim Y` which lifts continuously to `Ỹ`. -/
private theorem isTrace_reading {Y : ClosedIrreducibleAnalyticSubvariety n X} {T : TildeY Y}
    {φ : X → EReal} {ψ : T.space.obj.left → EReal} (hψ : T.IsTrace φ ψ) {d : ℕ}
    (hd : d = Y.dim) (V : Type u) [TopologicalSpace V] [ChartedSpace (ComplexModel d) V]
    [IsComplexManifold d V] [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]
    (ι : V → X) (hι : ContMDiff 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (hres : IsResolutionOf Y ι) (κ : KahlerBackground d V) (ν : V → T.space.obj.left)
    (hν : Continuous ν) (hcomm : ∀ v, T.toX (ν v) = ι v) :
    ∃ (om : KahlerBackground n X) (omV : KahlerBackground d V),
      IsSourceTraceRepresentativeAlong om omV hι φ (ψ ∘ ν) := by
  subst hd
  obtain rfl : ‹MeasurableSpace V› = borel V := BorelSpace.measurable_eq
  let R : ResolutionTarget Y :=
    { V := V
      ι := ι
      contMDiff := hι
      isResolutionOf := hres
      kahler := κ }
  let N : T.Resolution := ⟨R, ν, hν, hcomm⟩
  exact hψ.2 N

/-- **Source `lma:rescommpullback` on the normalizations.** Let `π : Z → X` be a proper
bimeromorphic morphism of compact Kähler manifolds, `W ⊆ Z`, `Y ⊆ X` irreducible with
`Π = π|_W : W → Y` bimeromorphic, `W̃`, `Ỹ` the normalizations and `Π̃ : W̃ → Ỹ` a continuous map
over `π` (the induced map of normalizations). Let `ψ = Tr_Y(φ)` be a trace operator of `φ` along
`Y` (on `Ỹ`). Then `ν(π^*φ, W) = 0` and `Π̃^*ψ ∼_P Tr_W(π^*φ)` on `W̃` for every trace operator
`Tr_W(π^*φ)` of `π^*φ` along `W`; moreover the readings of `Π̃^*ψ` on the resolutions of `W̃` are
trace operators of `π^*φ`. -/
theorem rescommpullback {π : Z → X} (hπ : IsAnalyticModification (n := n) π)
    {W : ClosedIrreducibleAnalyticSubvariety n Z} {Y : ClosedIrreducibleAnalyticSubvariety n X}
    (hPi : IsBimeromorphicRestriction π W Y) (TW : TildeY W) (TY : TildeY Y)
    (Pi' : TW.space.obj.left → TY.space.obj.left) (hPic : Continuous Pi')
    (hPi' : ∀ w, TY.toX (Pi' w) = π (TW.toX w)) (omegaZ : KahlerBackground n Z) {φ : X → EReal} {ψ : TY.space.obj.left → EReal}
    (hψ : TY.IsTrace φ ψ) :
    (SGPT.PSH.VariableComplexAtlas.ofFixedModel n Z).sourceGenericLelong (φ ∘ π) W.carrier = 0 ∧
      (∀ NW : TW.Resolution, TildeY.IsTraceOn NW (φ ∘ π) ((ψ ∘ Pi') ∘ NW.ν)) ∧
      ∀ ρ : TW.space.obj.left → EReal, TW.IsTrace (φ ∘ π) ρ → TW.PEquivalent (ψ ∘ Pi') ρ := by
  have key : ∀ NW : TW.Resolution,
      (SGPT.PSH.VariableComplexAtlas.ofFixedModel n Z).sourceGenericLelong (φ ∘ π) W.carrier = 0 ∧
      (∃ κ : KahlerBackground n Z,
        IsSourceTraceRepresentativeAlong κ NW.R.kahler NW.R.contMDiff (φ ∘ π) ((ψ ∘ Pi') ∘ NW.ν)) ∧
      ∀ (omegaZ' : KahlerBackground n Z) (omegaW' : KahlerBackground W.dim NW.R.V)
        (ρ : NW.R.V → EReal),
        IsSourceTraceRepresentativeAlong omegaZ' omegaW' NW.R.contMDiff (φ ∘ π) ρ →
          SourcePEquivalent (n := W.dim) ((ψ ∘ Pi') ∘ NW.ν) ρ := by
    intro NW
    have hres : IsResolutionOf Y (π ∘ NW.R.ι) :=
      isResolutionOf_comp hπ.1 hPi NW.R.contMDiff NW.R.isResolutionOf
    obtain ⟨om, omV, ht⟩ := isTrace_reading hψ hPi.dim_eq NW.R.V (π ∘ NW.R.ι)
      (hπ.1.comp NW.R.contMDiff) hres NW.R.kahler (Pi' ∘ NW.ν) (hPic.comp NW.continuous)
      (fun v => (hPi' (NW.ν v)).trans (congrArg π (NW.toX_comp v)))
    exact trace_pullback_of_modification hπ NW.R om omegaZ ht
  obtain ⟨NW₀⟩ := TW.nonempty_resolution
  refine ⟨(key NW₀).1, fun NW => ?_, fun ρ hρ => ?_⟩
  · obtain ⟨κ, hκ⟩ := (key NW).2.1
    exact ⟨κ, NW.R.kahler, hκ⟩
  · have hP : ∀ NW : TW.Resolution,
        SourcePEquivalent (n := W.dim) ((ψ ∘ Pi') ∘ NW.ν) (ρ ∘ NW.ν) := by
      intro NW
      obtain ⟨om', omV', h'⟩ := hρ.2 NW
      exact (key NW).2.2 om' omV' _ h'
    exact ⟨fun NW => (hP NW).1, fun NW => (hP NW).2⟩

end Rescomm

end SGPT.Trace.TY
