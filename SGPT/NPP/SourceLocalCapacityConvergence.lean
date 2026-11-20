import SGPT.NPP.Capacity2MonotoneLocal

/-!
# Local convergence in capacity in the revised SGPT book

This file implements the extra local notion added to
`def:conv_cap` in source commit `de08f12f`, preserving the existing global
notion. It packages the existing compact-core decreasing theorem as the
revised proposition's actual local convergence conclusion. The increasing
clause on general open sets is not addressed here.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open scoped ENNReal Topology

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [CompactSpace M]

/-- The revised `def:conv_cap`: both original order gaps tend to zero after
intersection with each compact subset of the original open domain. -/
def SourceTendstoLocallyInCapacity
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (U : Opens M) {I : Type*} (f : I → U → EReal) (l : Filter I) (g : U → EReal) : Prop :=
  (∀ i, Measurable (f i)) ∧ Measurable g ∧
    ∀ K : Set M, IsCompact K → K ⊆ U → ∀ δ : ℝ, 0 < δ →
      Tendsto (fun i => sourceThetaCapacity θ
        (K ∩ sourceCapacityUpperGap U (f i) g δ)) l (𝓝 0) ∧
      Tendsto (fun i => sourceThetaCapacity θ
        (K ∩ sourceCapacityLowerGap U (f i) g δ)) l (𝓝 0)

/-- The directed-net specialization of the revised local source definition. -/
def SourceNetConvergesLocallyInCapacity
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (U : Opens M) {I : Type*} [Preorder I] [IsDirected I (· ≤ ·)]
    (f : I → U → EReal) (g : U → EReal) : Prop :=
  SourceTendstoLocallyInCapacity θ U f atTop g

/-- Whole-domain convergence implies the revised local convergence. -/
theorem SourceTendstoInCapacity.locally
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {U : Opens M}
    {I : Type*} {f : I → U → EReal} {l : Filter I} {g : U → EReal}
    (h : SourceTendstoInCapacity θ U f l g) :
    SourceTendstoLocallyInCapacity θ U f l g := by
  refine ⟨h.1, h.2.1, fun K _ _ δ hδ => ⟨?_, ?_⟩⟩
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (h.2.2 δ hδ).1 (fun _ => zero_le)
      (fun _ => sourceThetaCapacity_mono θ inter_subset_right)
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (h.2.2 δ hδ).2 (fun _ => zero_le)
      (fun _ => sourceThetaCapacity_mono θ inter_subset_right)

/-- On a compact open domain the local and whole-domain notions coincide. -/
theorem sourceTendstoLocallyInCapacity_iff_of_isCompact
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (U : Opens M)
    {I : Type*} (f : I → U → EReal) (l : Filter I) (g : U → EReal)
    (hU : IsCompact (U : Set M)) :
    SourceTendstoLocallyInCapacity θ U f l g ↔ SourceTendstoInCapacity θ U f l g := by
  constructor
  · intro h
    refine ⟨h.1, h.2.1, fun δ hδ => ?_⟩
    have hup : ∀ i, (U : Set M) ∩ sourceCapacityUpperGap U (f i) g δ =
        sourceCapacityUpperGap U (f i) g δ := by
      intro i
      apply inter_eq_right.mpr
      rintro _ ⟨x, _, rfl⟩
      exact x.2
    have hlo : ∀ i, (U : Set M) ∩ sourceCapacityLowerGap U (f i) g δ =
        sourceCapacityLowerGap U (f i) g δ := by
      intro i
      apply inter_eq_right.mpr
      rintro _ ⟨x, _, rfl⟩
      exact x.2
    simpa only [hup, hlo] using h.2.2 (U : Set M) hU subset_rfl δ hδ
  · exact SourceTendstoInCapacity.locally

/-- The revised source sentence: on the whole compact manifold the two
capacity-convergence notions agree, for any indexing filter. -/
theorem sourceTendstoLocallyInCapacity_top_iff
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    {I : Type*} (f : I → (⊤ : Opens M) → EReal) (l : Filter I)
    (g : (⊤ : Opens M) → EReal) :
    SourceTendstoLocallyInCapacity θ ⊤ f l g ↔ SourceTendstoInCapacity θ ⊤ f l g :=
  sourceTendstoLocallyInCapacity_iff_of_isCompact θ ⊤ f l g isCompact_univ

/-- The same whole-manifold equivalence for directed nets. -/
theorem sourceNetConvergesLocallyInCapacity_top_iff
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    {I : Type*} [Preorder I] [IsDirected I (· ≤ ·)]
    (f : I → (⊤ : Opens M) → EReal) (g : (⊤ : Opens M) → EReal) :
    SourceNetConvergesLocallyInCapacity θ ⊤ f g ↔ SourceNetConvergesInCapacity θ ⊤ f g :=
  sourceTendstoLocallyInCapacity_top_iff θ f atTop g

end SGPT.PSH.VariableComplexAtlas

namespace SGPT.NPP

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open SGPT.PSH.VariableComplexAtlas

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- Revised `prop:mono_psh_cap` (1), directly in the source's new local
convergence predicate, retaining the original open domain and actual psh
inputs. The stronger existing compact-core theorem allows an independent
local background `θ'`; the source instance is `θ' = θ`. -/
theorem sourceMonoPshCap_decreasing_locally (omega : KahlerBackground n M)
    (θ θ' : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (U : Opens M) {I : Type*} [Preorder I] [IsDirected I (· ≤ ·)]
    {φ : I → M → EReal} {φ₀ : M → EReal}
    (hφ : ∀ i, (ofFixedModel n M).IsThetaPSHOn θ' (φ i) U)
    (hφ₀ : (ofFixedModel n M).IsThetaPSHOn θ' φ₀ U)
    (hanti : ∀ x ∈ (U : Set M), Antitone fun i => φ i x)
    (hlim : ∀ x ∈ (U : Set M), Tendsto (fun i => φ i x) atTop (𝓝 (φ₀ x))) :
    SourceNetConvergesLocallyInCapacity θ U (fun i x => φ i x.1) (fun x => φ₀ x.1) := by
  refine ⟨fun i => (isLocalQuasiPshOn_of_isThetaPSHOn U.isOpen (hφ i)).measurable_restrict,
    (isLocalQuasiPshOn_of_isThetaPSHOn U.isOpen hφ₀).measurable_restrict,
    fun K hK hKU δ hδ => ?_⟩
  exact sourceMonoPshCap_decreasing_compact omega θ θ' hbig U hφ hφ₀ hanti hlim hK hKU hδ

end SGPT.NPP
