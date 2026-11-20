import SGPT.Trace.P5WireTransition
import SGPT.Okounkov.ResolvedStrictTransformModification
import SGPT.PSH.RIsoACommonModel
import SGPT.Foundations.Analysis.Pending.EmbeddedResolution
import SGPT.Foundations.Analysis.Pending.SubmanifoldCodRestrict
import SGPT.Foundations.Analysis.Pending.AnalyticModelDomination
import SGPT.Foundations.Analysis.Pending.DominationLogResolution
import SGPT.Foundations.Analysis.Pending.SubmanifoldKahlerRestriction
import SGPT.Foundations.Analysis.Pending.ProductComplexManifold
import SGPT.Foundations.Analysis.Pending.HironakaEmbeddedAnalyticLocal

/-!
# A resolution target dominating two given resolution targets

Source: `chapter_trace.tex` (`def:traceop` and the trace chapter: the trace along an irreducible
`Y` is read on the normalization `Ỹ`, i.e. on any resolution of `Y`) and `chapter_NApotential.tex`
(`def:NApotential:L623`: "independent of the choice of the resolution"); SGPT.Foundations.Analysis
goal P5 (a common resolution of two given resolutions of a compact reduced complex space).

For two resolution targets `R₁ = (Y'₁, ι₁)`, `R₂ = (Y'₂, ι₂)` of an irreducible analytic subset
`Y` of a complex manifold `X` (`Trace2Resolution.ResolutionTarget`: compact connected Kähler
manifolds of dimension `dim Y` with resolutions `ιᵢ` of `Y`), we construct a third resolution
target `R₃` with modifications `p₁ : Y'₃ → Y'₁`, `p₂ : Y'₃ → Y'₂` and `ι₃ = ι₁ ∘ p₁ = ι₂ ∘ p₂`
(`exists_common_resolutionTarget`).

The construction is TN's common resolution over an embedded singular image
(`HironakaEmbeddedCommon.exists_compact_smooth_common_model`: the strict transform of the main
component of the fibre product `Y'₁ ×_X Y'₂` under its embedded resolution), with two additions:
its input, the biholomorphism between the good loci, is produced by
`P5Wire.exists_goodTransition` (`P5WireTransition.lean`); and the common model is **Kähler**:
the embedded resolution is a blowup sequence of the compact Kähler manifold `Y'₁ × Y'₂`, hence
Kähler (`DominationLogResolution.compactSpace_and_kahler_of_isBlowupSequence`), and the strict
transform carries the restricted Kähler form (`SubmanifoldKahlerRestriction.kahlerBackground`).
The proof of `exists_kahler_common_model` follows TN's proof of
`HironakaEmbeddedCommon.exists_compact_smooth_common_model` line by line, recording in addition
the Kähler form and the facts needed to see `ι₁ ∘ g₀` as a resolution.
-/

set_option autoImplicit false

noncomputable section

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff SGPT.Foundations.Analysis.Pending.ProductComplexManifold

universe u

namespace SGPT.Trace.P5Wire

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ProductComplexManifold
  SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
  SGPT.Foundations.Analysis.Pending.HironakaEmbeddedCommon
open SGPT.Trace.Trace2Resolution

section Model

/-- A holomorphic map with a holomorphic inverse over the complement of a nowhere dense analytic
set is a modification. (TN's private
`HironakaEmbeddedCommon.isAnalyticModification_of_open_inverse`, reproduced verbatim since it is
not exported.) -/
theorem isAnalyticModification_of_open_inverse {n : ℕ} {X Y : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    [Nonempty X] [ConnectedSpace Y]
    {f : Y → X}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hproper : IsProperMap f) {D : Set X}
    (hDa : IsComplexAnalyticSubset (n := n) D) (hDi : interior D = ∅)
    (s : (⟨Dᶜ, hDa.isClosed.isOpen_compl⟩ : Opens X) → Y)
    (hs : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ s)
    (hright : ∀ x, f (s x) = x.val)
    (hleft : ∀ y (hy : f y ∉ D), s ⟨f y, hy⟩ = y) :
    IsAnalyticModification (n := n) f := by
  let O : Opens X := ⟨Dᶜ, hDa.isClosed.isOpen_compl⟩
  have hsubrange : Dᶜ ⊆ range f := fun x hx => ⟨s ⟨x, hx⟩, hright ⟨x, hx⟩⟩
  have hdense : Dense (range f) :=
    (interior_eq_empty_iff_dense_compl.mp hDi).mono hsubrange
  have hrange : range f = univ :=
    hproper.isClosed_range.closure_eq.symm.trans hdense.closure_eq
  have hsurj : Function.Surjective f := by
    intro x
    have hx : x ∈ range f := by rw [hrange]; exact mem_univ x
    exact hx
  let t : X → Y := fun x => Classical.choose (hsurj x)
  have ht (x : X) : f (t x) = x := Classical.choose_spec (hsurj x)
  have heq : (fun x : O => t x.val) = s := by
    funext x
    have hnot : f (t x.val) ∉ D := by rw [ht]; exact x.property
    calc
      t x.val = s ⟨f (t x.val), hnot⟩ := (hleft _ hnot).symm
      _ = s x := congrArg s (Subtype.ext (ht x.val))
  have htsmooth : ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ t Dᶜ := by
    have hrest : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
        (fun x : O => t x.val) := heq.symm ▸ hs
    intro x hx
    exact (contMDiffAt_subtype_iff.mp (hrest ⟨x, hx⟩)).contMDiffWithinAt
  let A : Set Y := f ⁻¹' D
  have hAc : IsClosed A := hDa.isClosed.preimage hf.continuous
  have hAa : IsComplexAnalyticSubset (n := n) A :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hf hDa
  obtain ⟨x, hx⟩ := (interior_eq_empty_iff_dense_compl.mp hDi).nonempty
  have hsx : s ⟨x, hx⟩ ∉ A := by
    change f (s ⟨x, hx⟩) ∉ D
    rwa [hright]
  have hAne : A ≠ univ := fun h => hsx (h.symm ▸ mem_univ _)
  have hAi : interior A = ∅ := by
    rw [← not_nonempty_iff_eq_empty]
    exact fun h => hAne (hAa.eq_univ_of_interior_nonempty h)
  refine ⟨hf, hproper, A, D, t, hAc, hAa, hAi, hDa.isClosed, hDa, hDi,
    rfl, htsmooth, (fun x _ => ht x), ?_⟩
  intro y hy
  exact (congrFun heq (⟨f y, hy⟩ : O)).trans (hleft y hy)


/-- **A compact connected Kähler common model** (TN P5 over an embedded singular image, with the
Kähler form). Two holomorphic maps `c₀ : Y₀ → M`, `c₁ : Y₁ → M` from compact Kähler manifolds of
the same dimension, injective over `M \ B` (`B` analytic with nowhere dense preimages), with a
biholomorphism `e` between their good loci compatible with the maps, have a compact connected
Kähler common model `Z` with modifications `g₀ : Z → Y₀`, `g₁ : Z → Y₁`, `c₀ ∘ g₀ = c₁ ∘ g₁`; `g₀`
is surjective and `c₀ ∘ g₀` is injective over `M \ B` with nowhere dense preimage of `B`.
The proof is that of `HironakaEmbeddedCommon.exists_compact_smooth_common_model`, plus the
Kähler form of the blown-up product restricted to the strict transform. -/
theorem exists_kahler_common_model {m n : ℕ} {M Y₀ Y₁ : Type u}
    [TopologicalSpace M] [ChartedSpace (ComplexModel m) M] [IsComplexManifold m M]
    [TopologicalSpace Y₀] [ChartedSpace (ComplexModel n) Y₀] [IsComplexManifold n Y₀]
    [CompactSpace Y₀]
    [TopologicalSpace Y₁] [ChartedSpace (ComplexModel n) Y₁] [IsComplexManifold n Y₁]
    [CompactSpace Y₁] [ConnectedSpace Y₁]
    {c₀ : Y₀ → M} {c₁ : Y₁ → M} {B : Set M}
    (ω₀ : KahlerBackground n Y₀) (ω₁ : KahlerBackground n Y₁)
    (hc₀ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ c₀)
    (hc₁ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ c₁)
    (hBa : IsComplexAnalyticSubset (n := m) B)
    (hthin₀ : interior (c₀ ⁻¹' B) = ∅) (hthin₁ : interior (c₁ ⁻¹' B) = ∅)
    (e : goodOpen c₁ hc₁ B hBa.isClosed ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      goodOpen c₀ hc₀ B hBa.isClosed)
    (he : ∀ y, c₀ (e y).val = c₁ y.val)
    (hinj : InjOn c₀ (c₀ ⁻¹' Bᶜ)) :
    ∃ (Z : Type u) (_ : TopologicalSpace Z) (_ : ChartedSpace (ComplexModel n) Z)
      (_ : IsComplexManifold n Z) (_ : ConnectedSpace Z) (_ : CompactSpace Z)
      (_ : KahlerBackground n Z) (g₀ : Z → Y₀) (g₁ : Z → Y₁),
      IsAnalyticModification (n := n) g₀ ∧ IsAnalyticModification (n := n) g₁ ∧
      c₀ ∘ g₀ = c₁ ∘ g₁ ∧ InjOn (c₀ ∘ g₀) ((c₀ ∘ g₀) ⁻¹' Bᶜ) ∧
      interior ((c₀ ∘ g₀) ⁻¹' B) = ∅ := by
  classical
  obtain ⟨V, hVdim, _, hVclosure, hVF, hGreg⟩ :=
    exists_mainComponent_of_open_transition hc₀ hc₁ hBa hthin₁ e he hinj
  obtain ⟨Xt, instTop, instChart, instMfd, μ, hμ, hiso, hW⟩ :=
    EmbeddedResolution.exists_embeddedResolution V
  let W : Set Xt := strictTransform (n + n) μ V.carrier
  have hWn : IsClosedConnectedSubmanifold (n + n) W n := by
    simpa only [hVdim] using hW
  let := SubmanifoldChartedSpace.chartedSpace (Nat.le_add_right n n) hWn.2.2
  have := SubmanifoldChartedSpace.isComplexManifold_chartedSpace
    (Nat.le_add_right n n) hWn.2.2
  have : ConnectedSpace W := isConnected_iff_connectedSpace.mp hWn.2.1
  obtain ⟨hXtc, hXtK⟩ := DominationLogResolution.compactSpace_and_kahler_of_isBlowupSequence
    ⟨prodKahlerBackground ω₀ ω₁⟩ hμ
  have : CompactSpace Xt := hXtc
  have : CompactSpace W := isCompact_iff_compactSpace.mp hWn.1.isCompact
  have : Nonempty Xt := ⟨hWn.2.1.nonempty.choose⟩
  let ωW : KahlerBackground n W :=
    SubmanifoldKahlerRestriction.kahlerBackground (Nat.le_add_right n n) hWn.2.2 hXtK.some
  have hinc := SubmanifoldChartedSpace.contMDiff_val (Nat.le_add_right n n) hWn.2.2
  let g₀ : W → Y₀ := fun w => (μ w.val).1
  let g₁ : W → Y₁ := fun w => (μ w.val).2
  have hg₀ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g₀ :=
    (ProductComplexManifold.contMDiff_fst.comp hμ.contMDiff).comp hinc
  have hg₁ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g₁ :=
    (ProductComplexManifold.contMDiff_snd.comp hμ.contMDiff).comp hinc
  have hWpre : W ⊆ μ ⁻¹' V.carrier :=
    closure_minimal sdiff_subset (V.isClosed_carrier.preimage hμ.contMDiff.continuous)
  have hbase (w : W) : c₀ (g₀ w) = c₁ (g₁ w) := hVF (hWpre w.property)
  let U₁ := goodOpen c₁ hc₁ B hBa.isClosed
  let U₀ := goodOpen c₀ hc₀ B hBa.isClosed
  let γ : U₁ → Y₀ × Y₁ := fun y => ((e y).val, y.val)
  have hγ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel (n + n)) ∞ γ :=
    ProductComplexManifold.contMDiff_prodMk
      (contMDiff_subtype_val.comp e.contMDiff) contMDiff_subtype_val
  have hγG (y : U₁) : c₀ (γ y).1 = c₁ (γ y).2 ∧ c₀ (γ y).1 ∉ B :=
    ⟨he y, (e y).property⟩
  have hGoff {p : Y₀ × Y₁} (hp : c₀ p.1 = c₁ p.2 ∧ c₀ p.1 ∉ B) :
      p ∉ singularLocus V := by
    intro hs
    apply hs.2
    change RegularAtDim (n := n + n) V.carrier p V.dim
    rw [hVdim]
    exact hGreg p hp
  have hSingc : IsClosed (singularLocus V) := EmbeddedFromResolution.isClosed_singularLocus V
  let O : Opens (Y₀ × Y₁) := ⟨(singularLocus V)ᶜ, hSingc.isOpen_compl⟩
  let R : Y₀ × Y₁ → Xt := ModificationMassInvariance.invOver μ (singularLocus V)ᶜ
  have hR := SGPT.Okounkov.contMDiffOn_invOver_of_isIsomorphismOver hμ.contMDiff
    hSingc.isOpen_compl hiso
  have hRO : ContMDiff 𝓘(ℂ, ComplexModel (n + n)) 𝓘(ℂ, ComplexModel (n + n)) ∞
      (fun x : O => R x.val) := by
    intro x
    exact (hR.contMDiffAt (hSingc.isOpen_compl.mem_nhds x.property)).comp x
      (contMDiff_subtype_val x)
  let k : U₁ → O := fun y => ⟨γ y, hGoff (hγG y)⟩
  have hk : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel (n + n)) ∞ k :=
    BlowupRestrictOpen.contMDiff_opens_mk hγ (fun y => hGoff (hγG y))
  have hμR (p : Y₀ × Y₁) (hp : p ∉ singularLocus V) : μ (R p) = p :=
    (ModificationMassInvariance.invOver_mem hiso hp).2
  have hland (y : U₁) : R (γ y) ∈ W := by
    apply subset_closure
    refine ⟨?_, ?_⟩
    · change μ (R (γ y)) ∈ V.carrier
      rw [hμR _ (k y).property, hVclosure]
      exact subset_closure (hγG y)
    · exact fun h => disjoint_left.mp hiso.2
        (ModificationMassInvariance.invOver_mem hiso (k y).property).1 h
  let s₁ : U₁ → W := fun y => ⟨R (γ y), hland y⟩
  have hs₁ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ s₁ :=
    SubmanifoldCodRestrict.contMDiff_codRestrict (Nat.le_add_right n n) hWn.2.2
      (hRO.comp hk) hland
  have hμs (y : U₁) : μ (s₁ y).val = γ y := hμR _ (k y).property
  have hright₁ (y : U₁) : g₁ (s₁ y) = y.val := congrArg Prod.snd (hμs y)
  have hμGraph (w : W) (hw : c₁ (g₁ w) ∉ B) : μ w.val = γ ⟨g₁ w, hw⟩ := by
    apply Prod.ext
    · exact hinj (by change c₀ (g₀ w) ∉ B; rwa [hbase w])
        (e ⟨g₁ w, hw⟩).property ((hbase w).trans (he ⟨g₁ w, hw⟩).symm)
    · rfl
  have hleft₁ (w : W) (hw : c₁ (g₁ w) ∉ B) : s₁ ⟨g₁ w, hw⟩ = w := by
    apply Subtype.ext
    apply hiso.1.injOn
    · change μ (s₁ ⟨g₁ w, hw⟩).val ∉ singularLocus V
      rw [hμs]
      exact hGoff (hγG _)
    · change μ w.val ∉ singularLocus V
      rw [hμGraph w hw]
      exact hGoff (hγG _)
    · rw [hμs, hμGraph w hw]
  let s₀ : U₀ → W := fun y => s₁ (e.symm y)
  have hs₀ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ s₀ :=
    hs₁.comp e.symm.contMDiff
  have hright₀ (y : U₀) : g₀ (s₀ y) = y.val := by
    have h := congrArg Prod.fst (hμs (e.symm y))
    simpa only [γ, e.apply_symm_apply] using h
  have hleft₀ (w : W) (hw : c₀ (g₀ w) ∉ B) : s₀ ⟨g₀ w, hw⟩ = w := by
    have hw₁ : c₁ (g₁ w) ∉ B := by rwa [← hbase w]
    have heq : e.symm (⟨g₀ w, hw⟩ : U₀) = ⟨g₁ w, hw₁⟩ := by
      have hforward : (⟨g₀ w, hw⟩ : U₀) = e ⟨g₁ w, hw₁⟩ :=
        Subtype.ext (congrArg Prod.fst (hμGraph w hw₁))
      exact (congrArg (fun z : U₀ => e.symm z) hforward).trans (e.symm_apply_apply _)
    change s₁ (e.symm ⟨g₀ w, hw⟩) = w
    rw [heq]
    exact hleft₁ w hw₁
  have hE₀a := AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hc₀ hBa
  have hE₁a := AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hc₁ hBa
  obtain ⟨y, hy⟩ := (interior_eq_empty_iff_dense_compl.mp hthin₁).nonempty
  have : Nonempty Y₀ := ⟨(e ⟨y, hy⟩).val⟩
  have hmod₀ : IsAnalyticModification (n := n) g₀ :=
    isAnalyticModification_of_open_inverse hg₀ hg₀.continuous.isProperMap
      hE₀a hthin₀ s₀ hs₀ hright₀ hleft₀
  have hmod₁ : IsAnalyticModification (n := n) g₁ :=
    isAnalyticModification_of_open_inverse hg₁ hg₁.continuous.isProperMap
      hE₁a hthin₁ s₁ hs₁ hright₁ hleft₁
  -- the composite `c₀ ∘ g₀` is injective over `M \ B`
  have hinjW : InjOn (c₀ ∘ g₀) ((c₀ ∘ g₀) ⁻¹' Bᶜ) := by
    intro w hw w' hw' hww'
    have hg : g₀ w = g₀ w' := hinj hw hw' hww'
    have hw'' : c₀ (g₀ w') ∉ B := hw'
    rw [← hleft₀ w hw, ← hleft₀ w' hw'']
    exact congrArg s₀ (Subtype.ext hg)
  -- and the preimage of `B` in the common model is nowhere dense
  have hthinW : interior ((c₀ ∘ g₀) ⁻¹' B) = ∅ := by
    refine interior_eq_empty_of_not_mem
      (AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage (hc₀.comp hg₀) hBa)
      (v := s₁ ⟨y, hy⟩) ?_
    change c₀ (g₀ (s₁ ⟨y, hy⟩)) ∉ B
    rw [hbase, hright₁]
    exact hy
  exact ⟨W, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ωW,
    g₀, g₁, hmod₀, hmod₁, funext hbase, hinjW, hthinW⟩

end Model

/-! ### Two resolution targets of `Y` -/

section Pair

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : ClosedIrreducibleAnalyticSubvariety n X}

/-- Given the analytic sets `B₁`, `B₂` of `IsResolutionOf` for two resolution targets, some point
of `Y'₁` maps outside `B₁ ∪ B₂ ∪ ι₁(C₁) ∪ ι₂(C₂)`, `Cᵢ` the non-immersion loci. -/
theorem exists_good_point (R₁ R₂ : ResolutionTarget Y) {B₁ B₂ : Set X}
    (hB₁ : IsComplexAnalyticSubset (n := n) B₁) (hB₂ : IsComplexAnalyticSubset (n := n) B₂)
    (hinj₁ : InjOn R₁.ι (R₁.ι ⁻¹' B₁ᶜ)) (hd₁ : Dense (R₁.ι ⁻¹' B₁ᶜ))
    (hinj₂ : InjOn R₂.ι (R₂.ι ⁻¹' B₂ᶜ)) (hd₂ : Dense (R₂.ι ⁻¹' B₂ᶜ)) :
    ∃ v : R₁.V, R₁.ι v ∉ B₁ ∪ B₂ ∪ R₁.ι '' nonImmersionLocus Y.dim n R₁.ι ∪
      R₂.ι '' nonImmersionLocus Y.dim n R₂.ι := by
  set C₁ := nonImmersionLocus Y.dim n R₁.ι with hC₁
  set C₂ := nonImmersionLocus Y.dim n R₂.ι with hC₂
  have hC₁a := isComplexAnalyticSubset_nonImmersionLocus R₁.contMDiff
  have hC₂a := isComplexAnalyticSubset_nonImmersionLocus R₂.contMDiff
  have hI₁ := isComplexAnalyticSubset_image_nonImmersionLocus R₁
  have hY₁ : ∀ w : R₂.V, ∃ v : R₁.V, R₁.ι v = R₂.ι w :=
    exists_eq_of_range_eq (R₁.isResolutionOf.range_eq.trans R₂.isResolutionOf.range_eq.symm)
  have hY₂ : ∀ v : R₁.V, ∃ w : R₂.V, R₂.ι w = R₁.ι v :=
    exists_eq_of_range_eq (R₂.isResolutionOf.range_eq.trans R₁.isResolutionOf.range_eq.symm)
  have hpre₁ : interior (R₁.ι ⁻¹' B₁) = ∅ := by
    rw [interior_eq_empty_iff_dense_compl, ← preimage_compl]; exact hd₁
  have hpre₂ : interior (R₂.ι ⁻¹' B₂) = ∅ := by
    rw [interior_eq_empty_iff_dense_compl, ← preimage_compl]; exact hd₂
  obtain ⟨v₁, hv₁⟩ : ∃ v, v ∉ C₁ ∪ R₁.ι ⁻¹' B₁ := by
    apply exists_not_mem_of_interior_eq_empty
    rw [interior_union_isClosed_of_interior_empty hC₁a.isClosed hpre₁]
    exact interior_nonImmersionLocus R₁
  have hS₁ : interior (R₂.ι ⁻¹' B₁) = ∅ := by
    obtain ⟨v₀, hv₀⟩ := hd₁.nonempty
    obtain ⟨w₀, hw₀⟩ := hY₂ v₀
    refine interior_eq_empty_of_not_mem
      (AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage R₂.contMDiff hB₁) (v := w₀) ?_
    change R₂.ι w₀ ∉ B₁
    rw [hw₀]
    exact hv₀
  have hS₃ : interior (R₂.ι ⁻¹' (R₁.ι '' C₁)) = ∅ := by
    obtain ⟨w₁, hw₁⟩ := hY₂ v₁
    refine interior_eq_empty_of_not_mem
      (AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage R₂.contMDiff hI₁) (v := w₁) ?_
    rintro ⟨c, hc, hcv⟩
    rw [hw₁] at hcv
    have hv₁B : R₁.ι v₁ ∈ B₁ᶜ := fun h => hv₁ (Or.inr h)
    have hcv₁ : c = v₁ := hinj₁ (show R₁.ι c ∈ B₁ᶜ by rw [hcv]; exact hv₁B) hv₁B hcv
    exact hv₁ (Or.inl (hcv₁ ▸ hc))
  have hcl₁ : IsClosed (R₂.ι ⁻¹' B₁) := hB₁.isClosed.preimage R₂.contMDiff.continuous
  have hcl₂ : IsClosed (R₂.ι ⁻¹' B₂) := hB₂.isClosed.preimage R₂.contMDiff.continuous
  have hcl₃ : IsClosed (R₂.ι ⁻¹' (R₁.ι '' C₁)) := hI₁.isClosed.preimage R₂.contMDiff.continuous
  obtain ⟨w, hw⟩ : ∃ w, w ∉ R₂.ι ⁻¹' B₁ ∪ R₂.ι ⁻¹' B₂ ∪ R₂.ι ⁻¹' (R₁.ι '' C₁) ∪ C₂ := by
    apply exists_not_mem_of_interior_eq_empty
    rw [interior_union_isClosed_of_interior_empty ((hcl₁.union hcl₂).union hcl₃)
        (interior_nonImmersionLocus R₂),
      interior_union_isClosed_of_interior_empty (hcl₁.union hcl₂) hS₃,
      interior_union_isClosed_of_interior_empty hcl₁ hpre₂]
    exact hS₁
  obtain ⟨v, hv⟩ := hY₁ w
  refine ⟨v, ?_⟩
  rw [hv]
  rintro (((h | h) | h) | ⟨c, hc, hcw⟩)
  · exact hw (Or.inl (Or.inl (Or.inl h)))
  · exact hw (Or.inl (Or.inl (Or.inr h)))
  · exact hw (Or.inl (Or.inr h))
  · have hwB : R₂.ι w ∈ B₂ᶜ := fun h => hw (Or.inl (Or.inl (Or.inr h)))
    have hcw' : c = w := hinj₂ (show R₂.ι c ∈ B₂ᶜ by rw [hcw]; exact hwB) hwB hcw
    exact hw (Or.inr (hcw' ▸ hc))

/-- **The common good locus of two resolution targets.** There is a closed analytic subset
`B ⊇ Y_sing` of `X` with nowhere dense preimages in `Y'₁` and `Y'₂`, over whose complement both
resolutions are injective, and a biholomorphism `e` between the parts of `Y'₂` and `Y'₁` over
`X \ B` with `ι₁ ∘ e = ι₂`. -/
theorem exists_goodTransition (R₁ R₂ : ResolutionTarget Y) :
    ∃ (B : Set X) (hB : IsComplexAnalyticSubset (n := n) B),
      singularLocus Y ⊆ B ∧ interior (R₁.ι ⁻¹' B) = ∅ ∧ interior (R₂.ι ⁻¹' B) = ∅ ∧
      InjOn R₁.ι (R₁.ι ⁻¹' Bᶜ) ∧
      ∃ e : goodOpen R₂.ι R₂.contMDiff B hB.isClosed
          ≃ₘ⟮𝓘(ℂ, ComplexModel Y.dim), 𝓘(ℂ, ComplexModel Y.dim)⟯
          goodOpen R₁.ι R₁.contMDiff B hB.isClosed,
        ∀ y, R₁.ι (e y).val = R₂.ι y.val := by
  obtain ⟨B₁, hB₁, hs₁, hinj₁, hd₁⟩ := R₁.isResolutionOf.exists_isoLocus
  obtain ⟨B₂, hB₂, hs₂, hinj₂, hd₂⟩ := R₂.isResolutionOf.exists_isoLocus
  set C₁ := nonImmersionLocus Y.dim n R₁.ι with hC₁
  set C₂ := nonImmersionLocus Y.dim n R₂.ι with hC₂
  set B := B₁ ∪ B₂ ∪ R₁.ι '' C₁ ∪ R₂.ι '' C₂ with hBdef
  have hBa : IsComplexAnalyticSubset (n := n) B :=
    HironakaEmbeddedAnalyticLocal.isComplexAnalyticSubset_union
      (HironakaEmbeddedAnalyticLocal.isComplexAnalyticSubset_union
        (HironakaEmbeddedAnalyticLocal.isComplexAnalyticSubset_union hB₁ hB₂)
        (isComplexAnalyticSubset_image_nonImmersionLocus R₁))
      (isComplexAnalyticSubset_image_nonImmersionLocus R₂)
  have hsub₁ : B₁ ⊆ B := fun x hx => Or.inl (Or.inl (Or.inl hx))
  have hsub₂ : B₂ ⊆ B := fun x hx => Or.inl (Or.inl (Or.inr hx))
  have hinj₁' : InjOn R₁.ι (R₁.ι ⁻¹' Bᶜ) := hinj₁.mono fun v hv h => hv (hsub₁ h)
  have hinj₂' : InjOn R₂.ι (R₂.ι ⁻¹' Bᶜ) := hinj₂.mono fun v hv h => hv (hsub₂ h)
  have himm₁ : ∀ v, R₁.ι v ∉ B → v ∉ C₁ := fun v hv hc => hv (Or.inl (Or.inr ⟨v, hc, rfl⟩))
  have himm₂ : ∀ v, R₂.ι v ∉ B → v ∉ C₂ := fun v hv hc => hv (Or.inr ⟨v, hc, rfl⟩)
  obtain ⟨v, hv⟩ := exists_good_point R₁ R₂ hB₁ hB₂ hinj₁ hd₁ hinj₂ hd₂
  obtain ⟨w, hw⟩ := exists_good_point R₂ R₁ hB₂ hB₁ hinj₂ hd₂ hinj₁ hd₁
  have hw' : R₂.ι w ∉ B := by
    rintro (((h | h) | h) | h)
    · exact hw (Or.inl (Or.inl (Or.inr h)))
    · exact hw (Or.inl (Or.inl (Or.inl h)))
    · exact hw (Or.inr h)
    · exact hw (Or.inl (Or.inr h))
  have hrange : range R₁.ι = range R₂.ι :=
    R₁.isResolutionOf.range_eq.trans R₂.isResolutionOf.range_eq.symm
  exact ⟨B, hBa, fun x hx => hsub₁ (hs₁ hx),
    interior_eq_empty_of_not_mem
      (AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage R₁.contMDiff hBa) (v := v) hv,
    interior_eq_empty_of_not_mem
      (AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage R₂.contMDiff hBa) (v := w) hw',
    hinj₁', transitionDiffeomorph R₁.contMDiff R₂.contMDiff hBa.isClosed hrange hinj₁' hinj₂'
      himm₁ himm₂,
    transitionDiffeomorph_spec R₁.contMDiff R₂.contMDiff hBa.isClosed hrange hinj₁' hinj₂'
      himm₁ himm₂⟩

/-- **A resolution target dominating two given ones** (TN goal P5 for resolution targets). For
two resolution targets `R₁`, `R₂` of the irreducible analytic subset `Y`, there is a resolution
target `R₃` with modifications `p₁ : Y'₃ → Y'₁`, `p₂ : Y'₃ → Y'₂` such that
`ι₃ = ι₁ ∘ p₁ = ι₂ ∘ p₂`. -/
theorem exists_common_resolutionTarget (R₁ R₂ : ResolutionTarget Y) :
    ∃ (R₃ : ResolutionTarget Y) (p₁ : R₃.V → R₁.V) (p₂ : R₃.V → R₂.V),
      IsAnalyticModification (n := Y.dim) p₁ ∧ IsAnalyticModification (n := Y.dim) p₂ ∧
      (∀ w, R₃.ι w = R₁.ι (p₁ w)) ∧ ∀ w, R₃.ι w = R₂.ι (p₂ w) := by
  obtain ⟨B, hB, hsing, hthin₁, hthin₂, hinj₁, e, he⟩ := exists_goodTransition R₁ R₂
  obtain ⟨Z, iT, iC, iM, iConn, iComp, ωZ, g₁, g₂, hg₁, hg₂, hcomm, hinjZ, hthinZ⟩ :=
    exists_kahler_common_model R₁.kahler R₂.kahler R₁.contMDiff R₂.contMDiff hB hthin₁ hthin₂
      e he hinj₁
  have hsurj := SGPT.PSH.RIsoACommonModel.surjective_of_isAnalyticModification hg₁
  have hres : IsResolutionOf Y (R₁.ι ∘ g₁) := by
    refine ⟨?_, B, hB, hsing, hinjZ, ?_⟩
    · rw [range_comp, hsurj.range_eq, image_univ]
      exact R₁.isResolutionOf.range_eq
    · rw [preimage_compl]
      exact interior_eq_empty_iff_dense_compl.mp hthinZ
  let R₃ : ResolutionTarget Y :=
    { V := Z
      ι := R₁.ι ∘ g₁
      contMDiff := R₁.contMDiff.comp hg₁.1
      isResolutionOf := hres
      kahler := ωZ }
  exact ⟨R₃, g₁, g₂, hg₁, hg₂, fun w => rfl, fun w => congrFun hcomm w⟩

end Pair

end SGPT.Trace.P5Wire
