import SGPT.NPP.LocalIncreasingCompactLower
import SGPT.NPP.SourceLocalCapacityConvergence

/-!
Whole revised prop:mono_psh_cap, source69360cfd/chapter_npp.tex:360–368.
The original open domain and original functions are preserved. All natural
dimensions and arbitrary directed nets are included. The independent local
PSH background α specializes to the source background θ.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.NPP.LocalIncreasingCapacityDraft

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open ThetaCapacity
open SGPT.PSH.VariableComplexAtlas

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- Actual compact lower-gap convergence for an arbitrary increasing directed
net, reduced by Choquet to one actual increasing sequence of original indices. -/
theorem tendsto_kahlerCapacity_compact_lowerGap_of_monotone_net
    (ω : KahlerBackground n M)
    (α : AtlasClosedRealOneOneForm (ofFixedModel n M)) (U : Opens M)
    {I : Type*} [Preorder I] [IsDirected I (· ≤ ·)]
    {u : I → M → EReal} {v : M → EReal}
    (hu : ∀ i, (ofFixedModel n M).IsThetaPSHOn α (u i) U)
    (hv : (ofFixedModel n M).IsThetaPSHOn α v U)
    (hm : ∀ x ∈ (U : Set M), Monotone fun i => u i x)
    (hae : NetChartTendstoAEOn (n := n) U u v)
    {K : Set M} (hK : IsCompact K) (hKU : K ⊆ U) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun i => thetaCapacity ω.form (fun _ => 0)
      (K ∩ sourceCapacityLowerGap U (fun x => u i x.1) (fun x => v x.1) δ))
      atTop (𝓝 0) := by
  classical
  rcases isEmpty_or_nonempty I with hI | hI
  · rw [Filter.filter_eq_bot_of_isEmpty (atTop : Filter I)]
    exact tendsto_bot
  have huq : ∀ i, IsLocalQuasiPshOn (n := n) (U : Set M) (u i) :=
    fun i => isLocalQuasiPshOn_of_isThetaPSHOn U.isOpen (hu i)
  have hvq := isLocalQuasiPshOn_of_isThetaPSHOn U.isOpen hv
  have hle := increasing_local_le_limit huq hvq hm hae
  obtain ⟨j, hjmono, hreg⟩ := exists_monotone_sequence_regularized_limit huq hvq hm hae
  have hseqm : ∀ x ∈ (U : Set M), Monotone fun k => u (j k) x :=
    fun x hx k l hkl => hm x hx (hjmono hkl)
  have hseqa := netChartTendstoAEOn_of_monotone_regularized_limit α U
    (fun k => hu (j k)) hv hseqm (fun k x hx => hle (j k) x hx) hreg
  have hseq := tendsto_kahlerCapacity_compact_lowerGap_of_monotone_sequence ω α U
    (fun k => hu (j k)) hv hseqm hseqa hK hKU hδ
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨k, hk⟩ := ((ENNReal.tendsto_nhds_zero.mp hseq) ε hε).exists
  filter_upwards [eventually_ge_atTop (j k)] with i hi
  refine (thetaCapacity_mono ?_).trans hk
  rintro _ ⟨hxK, ⟨x, hxgap, rfl⟩⟩
  exact ⟨hxK, ⟨x, (hm x.1 x.2 hi).trans_lt hxgap, rfl⟩⟩

/-- The genuine Kähler-to-big-capacity control transfers arbitrary null
capacity limits; it introduces no measurability or convergence certificate. -/
theorem tendsto_sourceCapacity_zero_of_kahlerCapacity_zero
    (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {I : Type*} {l : Filter I} (E : I → Set M)
    (hcap : Tendsto (fun i => thetaCapacity ω.form (fun _ => 0) (E i)) l (𝓝 0)) :
    Tendsto (fun i => sourceThetaCapacity θ (E i)) l (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  rcases eq_or_ne ε ⊤ with rfl | htop
  · exact Eventually.of_forall fun _ => le_top
  have hr : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' htop
  obtain ⟨C, hC, hctl⟩ := exists_source_capacity_control_by_kahler ω θ hbig (half_pos hr)
  have hsmall := (ENNReal.tendsto_nhds_zero.mp hcap)
    (ENNReal.ofReal (ε.toReal / 2 / C)) (ENNReal.ofReal_pos.mpr (by positivity))
  filter_upwards [hsmall] with i hi
  calc sourceThetaCapacity θ (E i)
      ≤ ENNReal.ofReal (ε.toReal / 2) + ENNReal.ofReal C *
          sourceThetaCapacity (nativeClosedFormToAtlas ω.form) (E i) := hctl _
    _ ≤ ENNReal.ofReal (ε.toReal / 2) + ENNReal.ofReal C * ENNReal.ofReal (ε.toReal / 2 / C) := by
      rw [sourceThetaCapacity_kahler]
      exact add_le_add le_rfl (mul_le_mul' le_rfl hi)
    _ = ε := by
      rw [← ENNReal.ofReal_mul hC.le, mul_div_cancel₀ _ hC.ne',
        ← ENNReal.ofReal_add (half_pos hr).le (half_pos hr).le, add_halves,
        ENNReal.ofReal_toReal htop]

end SGPT.NPP.LocalIncreasingCapacityDraft

namespace SGPT.NPP

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open SGPT.PSH.VariableComplexAtlas LocalIncreasingCapacityDraft

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- Whole revised increasing clause of prop:mono_psh_cap on arbitrary opens,
in every natural dimension, for arbitrary directed nets of actual functions. -/
theorem sourceMonoPshCap_increasing_locally (ω : KahlerBackground n M)
    (θ α : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (U : Opens M) {I : Type*} [Preorder I] [IsDirected I (· ≤ ·)]
    {u : I → M → EReal} {v : M → EReal}
    (hu : ∀ i, (ofFixedModel n M).IsThetaPSHOn α (u i) U)
    (hv : (ofFixedModel n M).IsThetaPSHOn α v U)
    (hm : ∀ x ∈ (U : Set M), Monotone fun i => u i x)
    (hae : NetChartTendstoAEOn (n := n) U u v) :
    SourceNetConvergesLocallyInCapacity θ U (fun i x => u i x.1) (fun x => v x.1) := by
  refine ⟨fun i => (isLocalQuasiPshOn_of_isThetaPSHOn U.isOpen (hu i)).measurable_restrict,
    (isLocalQuasiPshOn_of_isThetaPSHOn U.isOpen hv).measurable_restrict,
    fun K hK hKU δ hδ => ⟨?_, ?_⟩⟩
  · exact sourceMonoPshCap_increasing_upper_locally θ α U hu hv hm hae K hδ
  · exact tendsto_sourceCapacity_zero_of_kahlerCapacity_zero ω θ hbig _
      (tendsto_kahlerCapacity_compact_lowerGap_of_monotone_net ω α U hu hv hm hae hK hKU hδ)

/-- Full revised prop:mono_psh_cap, both alternatives, with original local
PSH inputs and the exact revised source local-capacity conclusion. The
source specialization is α = θ; the stronger independent form is harmless. -/
theorem sourceMonoPshCap_locally (ω : KahlerBackground n M)
    (θ α : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (U : Opens M) {I : Type*} [Preorder I] [IsDirected I (· ≤ ·)]
    {u : I → M → EReal} {v : M → EReal}
    (hu : ∀ i, (ofFixedModel n M).IsThetaPSHOn α (u i) U)
    (hv : (ofFixedModel n M).IsThetaPSHOn α v U)
    (hlim : ((∀ x ∈ (U : Set M), Antitone fun i => u i x) ∧
        ∀ x ∈ (U : Set M), Tendsto (fun i => u i x) atTop (𝓝 (v x))) ∨
      ((∀ x ∈ (U : Set M), Monotone fun i => u i x) ∧
        NetChartTendstoAEOn (n := n) U u v)) :
    SourceNetConvergesLocallyInCapacity θ U (fun i x => u i x.1) (fun x => v x.1) := by
  rcases hlim with ⟨hm, ht⟩ | ⟨hm, ht⟩
  · exact sourceMonoPshCap_decreasing_locally ω θ α hbig U hu hv hm ht
  · exact sourceMonoPshCap_increasing_locally ω θ α hbig U hu hv hm ht

end SGPT.NPP
