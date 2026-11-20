import SGPT.Foundations.Analysis.Pending.EmbeddedResolution
import SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace
import SGPT.Foundations.Analysis.Pending.HironakaAdmissibleCalculus
import SGPT.Foundations.Analysis.Pending.AnalyticFibreProductProperProjections
import SGPT.Foundations.Analysis.Pending.AnalyticFibreProductRegularGraph

set_option autoImplicit false
noncomputable section

/-! # Actual compact main-component lift with its canonical flattening atlas

Original compact smooth-base geometry internally supplies the actual SAME
regular graph, main component, embedded resolution, smooth strict-transform
subtype atlas, proper surjection to V, and proper holomorphic coordinate maps.
The point lift over the SAME graph is constructed from the real ambient
isomorphism; no resolution, graph regularity, inverse lift or component is input.
The output identifies this SAME atlas with the actual canonical flattening atlas
and retains its holomorphic inclusion for the next genuine inverse corestriction.
Actual analytic-modification inverse FUNCTIONS for these model maps remain next.
-/

namespace SGPT.Foundations.Analysis.Pending.AnalyticCompactMainComponentCanonicalLift

open FirstPass FirstPass.NonKahlerLocus FirstPass.BlowupSequences
  AnalyticModificationLocalDiscrepancy GlobalComponents
open Set
open scoped Topology Manifold ContDiff SGPT.Foundations.Analysis.Pending.ProductComplexManifold

universe u

variable {n : ℕ} {X Y₀ Y₁ : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [ConnectedSpace X] [CompactSpace X]
  [TopologicalSpace Y₀] [ChartedSpace (ComplexModel n) Y₀] [IsComplexManifold n Y₀]
  [TopologicalSpace Y₁] [ChartedSpace (ComplexModel n) Y₁] [IsComplexManifold n Y₁]

/-- The actual compact main component, SAME original regular inverse graph,
genuine embedded strict transform with its constructed n-dimensional subtype
atlas, proper surjection to V and both proper holomorphic coordinate maps.
No manifold structure is asserted on the singular V itself. -/
theorem exists_actual_compact_mainComponent_canonical_lift
    {c₀ : Y₀ → X} {c₁ : Y₁ → X}
    (hc₀ : IsAnalyticModification (n := n) c₀)
    (hc₁ : IsAnalyticModification (n := n) c₁) :
    ∃ (B : Set X) (s₀ : X → Y₀) (s₁ : X → Y₁),
      IsClosed B ∧ IsComplexAnalyticSubset (n := n) B ∧ interior B = ∅ ∧
      ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ s₀ Bᶜ ∧
      ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ s₁ Bᶜ ∧
      (∀ x ∉ B, c₀ (s₀ x) = x) ∧ (∀ x ∉ B, c₁ (s₁ x) = x) ∧
      (∀ y, c₀ y ∉ B → s₀ (c₀ y) = y) ∧
      (∀ y, c₁ y ∉ B → s₁ (c₁ y) = y) ∧
      ∃ V : ClosedIrreducibleAnalyticSubvariety (n + n) (Y₀ × Y₁),
        V.dim = n ∧
        V.carrier ∈ globalComponents (n := n + n) {p : Y₀ × Y₁ | c₀ p.1 = c₁ p.2} ∧
        V.carrier = closure {p : Y₀ × Y₁ | c₀ p.1 = c₁ p.2 ∧ c₀ p.1 ∉ B} ∧
        V.carrier ⊆ {p : Y₀ × Y₁ | c₀ p.1 = c₁ p.2} ∧
        (∀ p ∈ {q : Y₀ × Y₁ | c₀ q.1 = c₁ q.2 ∧ c₀ q.1 ∉ B},
          RegularAtDim (n := n + n) V.carrier p n) ∧
        {p : Y₀ × Y₁ | c₀ p.1 = c₁ p.2 ∧ c₀ p.1 ∉ B} =
          (fun x => (s₀ x, s₁ x)) '' Bᶜ ∧
        ∃ (Xt : Type u) (_ : TopologicalSpace Xt)
          (_ : ChartedSpace (ComplexModel (n + n)) Xt)
          (_ : IsComplexManifold (n + n) Xt) (μ : Xt → Y₀ × Y₁),
          IsBlowupSequence (n + n) (Y₀ × Y₁) Xt μ ∧
          IsIsomorphismOver (n + n) μ (singularLocus V)ᶜ ∧
          ∃ hWn : IsClosedConnectedSubmanifold (n + n) (strictTransform (n + n) μ V.carrier) n,
          ∃ cs : ChartedSpace (ComplexModel n) (strictTransform (n + n) μ V.carrier),
            cs = SubmanifoldChartedSpace.chartedSpace (Nat.le_add_right n n) hWn.2.2 ∧
            @IsComplexManifold n (strictTransform (n + n) μ V.carrier) _ cs ∧
            letI := cs
            ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel (n + n)) ∞
              (Subtype.val : (strictTransform (n + n) μ V.carrier) → Xt) ∧
            ∃ ρ : (strictTransform (n + n) μ V.carrier) → V.carrier,
              (∀ z, (ρ z).val = μ z.val) ∧ IsProperMap ρ ∧ Function.Surjective ρ ∧
              ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
                (fun z : strictTransform (n + n) μ V.carrier => (μ z.val).1) ∧
              ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
                (fun z : strictTransform (n + n) μ V.carrier => (μ z.val).2) ∧
              IsProperMap (fun z : strictTransform (n + n) μ V.carrier => (μ z.val).1) ∧
              IsProperMap (fun z : strictTransform (n + n) μ V.carrier => (μ z.val).2) ∧
              (∀ z : strictTransform (n + n) μ V.carrier,
                c₀ (μ z.val).1 = c₁ (μ z.val).2) ∧
              (∀ p ∈ {q : Y₀ × Y₁ | c₀ q.1 = c₁ q.2 ∧ c₀ q.1 ∉ B},
                ∃! z : strictTransform (n + n) μ V.carrier, (ρ z).val = p) := by
  classical
  obtain ⟨B, s₀, s₁, hBc, hBa, hBi, hs₀, hs₁, hright₀, hright₁,
    hleft₀, hleft₁, V, hVdim, hVcomponent, hVclosure, hVF, hGreg, hGimage⟩ :=
    AnalyticFibreProductRegularGraph.exists_actual_mainComponent_regular_graph hc₀ hc₁
  let : CompactSpace Y₀ :=
    AnalyticModificationStrongPullback.compactSpace_of_isAnalyticModification hc₀
  let : CompactSpace Y₁ :=
    AnalyticModificationStrongPullback.compactSpace_of_isAnalyticModification hc₁
  obtain ⟨Xt, instTop, instChart, instMfd, μ, hμ, hiso, hW⟩ :=
    EmbeddedResolution.exists_embeddedResolution V
  let W : Set Xt := strictTransform (n + n) μ V.carrier
  have hWn : IsClosedConnectedSubmanifold (n + n) W n := by
    simpa only [hVdim] using hW
  let cs : ChartedSpace (ComplexModel n) W :=
    SubmanifoldChartedSpace.chartedSpace (Nat.le_add_right n n) hWn.2.2
  have hcs : @IsComplexManifold n W _ cs :=
    SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_add_right n n) hWn.2.2
  have hincl : SubmanifoldChartedSpace.InclusionHolomorphicFor (n + n) n W cs :=
    SubmanifoldChartedSpace.contMDiff_val (Nat.le_add_right n n) hWn.2.2
  let := cs
  let := hcs
  have hWpre : W ⊆ μ ⁻¹' V.carrier :=
    closure_minimal sdiff_subset (V.isClosed_carrier.preimage hμ.contMDiff.continuous)
  let ρ : W → V.carrier := fun z => ⟨μ z.val, hWpre z.property⟩
  have hμproper : IsProperMap μ :=
    HironakaAdmissibleCalculus.isProperMap_of_isBlowupSequence hμ
  have hρcont : Continuous ρ :=
    (hμ.contMDiff.continuous.comp continuous_subtype_val).subtype_mk
      (fun z => hWpre z.property)
  have hρproper : IsProperMap ρ :=
    isProperMap_of_comp_of_inj hρcont continuous_subtype_val
      (hμproper.restrict hWn.1) Subtype.val_injective
  have hGlift (p : Y₀ × Y₁)
      (hp : p ∈ {q : Y₀ × Y₁ | c₀ q.1 = c₁ q.2 ∧ c₀ q.1 ∉ B}) :
      ∃! z : W, (ρ z).val = p := by
    have hpSing : p ∉ singularLocus V := by
      intro hsing
      apply hsing.2
      change RegularAtDim (n := n + n) V.carrier p V.dim
      rw [hVdim]
      exact hGreg p hp
    obtain ⟨z, hzU, hμz⟩ := hiso.1.2.2 hpSing
    have hzW : z ∈ W := by
      apply subset_closure
      refine ⟨?_, ?_⟩
      · change μ z ∈ V.carrier
        rw [hμz]
        rw [hVclosure]
        exact subset_closure hp
      · exact fun hzE => Set.disjoint_left.mp hiso.2 hzU hzE
    refine ⟨⟨z, hzW⟩, hμz, ?_⟩
    intro w hw
    apply Subtype.ext
    apply hiso.1.2.1 _ hzU
    · exact hw.trans hμz.symm
    · change μ w.val ∉ singularLocus V
      change μ w.val = p at hw
      rwa [hw]
  have hVimage : V.carrier ⊆ μ '' W := by
    rw [hVclosure]
    apply closure_minimal _ (hμproper.isClosedMap W hWn.1)
    intro p hp
    obtain ⟨z, hz, _⟩ := hGlift p hp
    exact ⟨z.val, z.property, hz⟩
  have hρsurj : Function.Surjective ρ := by
    intro v
    obtain ⟨z, hzW, hz⟩ := hVimage v.property
    exact ⟨⟨z, hzW⟩, Subtype.ext hz⟩
  have hπ₀ : IsProperMap (fun v : V.carrier => v.val.1) :=
    AnalyticFibreProductProperProjections.isProperMap_fst_of_closed_fibreProduct
      hc₀.1.continuous hc₁.2.1 V.isClosed_carrier hVF
  have hπ₁ : IsProperMap (fun v : V.carrier => v.val.2) :=
    AnalyticFibreProductProperProjections.isProperMap_snd_of_closed_fibreProduct
      hc₀.2.1 hc₁.1.continuous V.isClosed_carrier hVF
  have hinc : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel (n + n)) ∞
      (Subtype.val : W → Xt) := hincl
  refine ⟨B, s₀, s₁, hBc, hBa, hBi, hs₀, hs₁, hright₀, hright₁, hleft₀, hleft₁,
    V, hVdim, hVcomponent, hVclosure, hVF, hGreg, hGimage,
    Xt, instTop, instChart, instMfd, μ, hμ, hiso, hWn, cs, rfl, hcs, hinc, ρ,
    (fun _ => rfl), hρproper, hρsurj, ?_, ?_, hπ₀.comp hρproper, hπ₁.comp hρproper,
    ?_, hGlift⟩
  · exact (ProductComplexManifold.contMDiff_fst.comp hμ.contMDiff).comp hinc
  · exact (ProductComplexManifold.contMDiff_snd.comp hμ.contMDiff).comp hinc
  · intro z
    exact hVF (hWpre z.property)

end SGPT.Foundations.Analysis.Pending.AnalyticCompactMainComponentCanonicalLift
