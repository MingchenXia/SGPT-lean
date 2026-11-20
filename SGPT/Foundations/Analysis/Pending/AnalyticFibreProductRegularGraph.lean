import SGPT.Foundations.Analysis.Pending.AnalyticFibreProductMainComponent

/-! # The actual main component with its same regular inverse graph

The original two analytic modifications construct B, their actual original
inverse maps on B's complement, and the same n-dimensional main component.
The construction retains regularity of EVERY point of that very graph in
its actual main component. No graph regularity, inverse, analytic closure,
component, dimension, compactness or resolution is supplied as a premise.
The proof is an extracted strengthened core of the stable actual construction;
its former weaker result may eventually be recovered by forgetting fields.
No manifold structure on singular V is asserted. Smooth resolution and
actual resolved model-map inverses remain separate constructions.
-/

set_option autoImplicit false
noncomputable section

open Set
open scoped Manifold ContDiff SGPT.Foundations.Analysis.Pending.ProductComplexManifold

namespace SGPT.Foundations.Analysis.Pending.AnalyticFibreProductRegularGraph

open FirstPass FirstPass.BlowupSequences
  AnalyticModificationLocalDiscrepancy ProductComplexManifold
  RegularLocusComponent GlobalComponents
open Set Filter
open scoped Topology Manifold ContDiff SGPT.Foundations.Analysis.Pending.ProductComplexManifold

universe u

variable {n : ℕ} {X Y₀ Y₁ : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [ConnectedSpace X]
  [TopologicalSpace Y₀] [ChartedSpace (ComplexModel n) Y₀] [IsComplexManifold n Y₀]
  [TopologicalSpace Y₁] [ChartedSpace (ComplexModel n) Y₁] [IsComplexManifold n Y₁]

/-- The actual same main component and graph, strengthened with the original
holomorphic inverse functions and both round trips on the SAME B complement,
and actual main-component regularity at EVERY point of that very graph. -/
theorem exists_actual_mainComponent_regular_graph
    {c₀ : Y₀ → X} {c₁ : Y₁ → X}
    (hc₀ : IsAnalyticModification (n := n) c₀)
    (hc₁ : IsAnalyticModification (n := n) c₁) :
    ∃ (B : Set X) (s₀ : X → Y₀) (s₁ : X → Y₁),
      IsClosed B ∧ IsComplexAnalyticSubset (n := n) B ∧ interior B = ∅ ∧
      ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ s₀ Bᶜ ∧
      ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ s₁ Bᶜ ∧
      (∀ x ∉ B, c₀ (s₀ x) = x) ∧
      (∀ x ∉ B, c₁ (s₁ x) = x) ∧
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
          (fun x => (s₀ x, s₁ x)) '' Bᶜ := by
  classical
  obtain ⟨A₀, B₀, s₀, _hA₀c, _hA₀a, _hA₀i, hB₀c, hB₀a, hB₀i,
    hpre₀, hs₀, hright₀, hleft₀⟩ := hc₀.2.2
  obtain ⟨A₁, B₁, s₁, _hA₁c, _hA₁a, _hA₁i, hB₁c, hB₁a, hB₁i,
    hpre₁, hs₁, hright₁, hleft₁⟩ := hc₁.2.2
  obtain ⟨D, hDc, hDa, hDi, _hpreDa, _hpreDi, hiso⟩ :=
    AnalyticModificationStrongPullback.exists_isIsomorphismOver_of_isAnalyticModification hc₀
  let B : Set X := (B₀ ∪ B₁) ∪ D
  have hBc : IsClosed B := (hB₀c.union hB₁c).union hDc
  have hBa : IsComplexAnalyticSubset (n := n) B :=
    ConstantRankImage.IsComplexAnalyticSubset.union
      (ConstantRankImage.IsComplexAnalyticSubset.union hB₀a hB₁a) hDa
  have hBi : interior B = ∅ := by
    dsimp only [B]
    rw [interior_union_isClosed_of_interior_empty (hB₀c.union hB₁c) hDi,
      interior_union_isClosed_of_interior_empty hB₀c hB₁i]
    exact hB₀i
  have hUne : (Bᶜ).Nonempty := (interior_eq_empty_iff_dense_compl.mp hBi).nonempty
  have hBne : B ≠ univ := by
    intro heq
    obtain ⟨x, hx⟩ := hUne
    exact hx (heq.symm ▸ mem_univ x)
  let F : Set (Y₀ × Y₁) := {p | c₀ p.1 = c₁ p.2}
  let S : Set (Y₀ × Y₁) := {p | c₀ p.1 = c₁ p.2 ∧ c₀ p.1 ∉ B}
  let γ : X → Y₀ × Y₁ := fun x => (s₀ x, s₁ x)
  have hSimage : S = γ '' Bᶜ := by
    ext p
    constructor
    · rintro ⟨hpF, hpB⟩
      have hpB₀ : c₀ p.1 ∉ B₀ := fun h => hpB (Or.inl (Or.inl h))
      have hpB₁ : c₁ p.2 ∉ B₁ := by
        intro h
        apply hpB
        apply Or.inl
        apply Or.inr
        rwa [hpF]
      have hpA₀ : p.1 ∉ A₀ := by
        intro h
        apply hpB₀
        change p.1 ∈ c₀ ⁻¹' B₀
        rwa [hpre₀]
      have hpA₁ : p.2 ∉ A₁ := by
        intro h
        apply hpB₁
        change p.2 ∈ c₁ ⁻¹' B₁
        rwa [hpre₁]
      refine ⟨c₀ p.1, hpB, ?_⟩
      apply Prod.ext
      · exact hleft₀ p.1 hpA₀
      · change s₁ (c₀ p.1) = p.2
        rw [hpF]
        exact hleft₁ p.2 hpA₁
    · rintro ⟨x, hx, rfl⟩
      have hx₀ : x ∉ B₀ := fun h => hx (Or.inl (Or.inl h))
      have hx₁ : x ∉ B₁ := fun h => hx (Or.inl (Or.inr h))
      change c₀ (s₀ x) = c₁ (s₁ x) ∧ c₀ (s₀ x) ∉ B
      rw [hright₀ x hx₀, hright₁ x hx₁]
      exact ⟨rfl, hx⟩
  have hU₀ : Bᶜ ⊆ B₀ᶜ := by
    intro x hx h
    exact hx (Or.inl (Or.inl h))
  have hU₁ : Bᶜ ⊆ B₁ᶜ := by
    intro x hx h
    exact hx (Or.inl (Or.inr h))
  have hγ : ContinuousOn γ Bᶜ :=
    (hs₀.continuousOn.mono hU₀).prodMk (hs₁.continuousOn.mono hU₁)
  have hSconn : IsPreconnected S := by
    rw [hSimage]
    exact (AnalyticComplementConnected.isPreconnected_compl hBa hBne).image γ hγ
  have hSne : S.Nonempty := by
    rw [hSimage]
    exact hUne.image γ
  have hSreg (p : Y₀ × Y₁) (hp : p ∈ S) : RegularAtDim (n := n + n) F p n := by
    have hpD : c₀ p.1 ∈ Dᶜ := fun h => hp.2 (Or.inr h)
    have hnp : p.1 ∉ exceptionalLocus n c₀ := Set.disjoint_left.mp hiso.2 hpD
    exact AnalyticFibreProductMainComponent.regularAtDim_fibreProduct_of_not_exceptional_left
      hc₀.1 hc₁.1 hnp hp.1
  obtain ⟨c, hcS⟩ := hSne
  have hc : RegularAtDim (n := n + n) F c n := hSreg c hcS
  let C : Set (Y₀ × Y₁) := component (n := n + n) F c
  have hSC : S ⊆ C := subset_component_of_isPreconnected hSconn
    (fun p hp => ⟨n, hSreg p hp⟩) ⟨c, hcS, mem_component_self hc⟩
  have hFa : IsComplexAnalyticSubset (n := n + n) F :=
    AnalyticFibreProductCarrier.isComplexAnalyticSubset_fibreProduct hc₀.1 hc₁.1
  let T : Set (Y₀ × Y₁) := (fun p => c₀ p.1) ⁻¹' B
  have hTa : IsComplexAnalyticSubset (n := n + n) T :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage
      (hc₀.1.comp ProductComplexManifold.contMDiff_fst) hBa
  have hCT : ¬ C ⊆ T := fun h => hcS.2 (h (mem_component_self hc))
  have hCS : C \ T ⊆ S := fun p hp => ⟨component_subset F c hp.1, hp.2⟩
  have hCdense := (ComponentComplementConnected.isPreconnected_component_diff_and_subset_closure
    hFa hTa hc hCT).2
  have hclosure : closure C = closure S := by
    apply Set.Subset.antisymm
    · exact closure_minimal (hCdense.trans (closure_mono hCS)) isClosed_closure
    · exact closure_mono hSC
  let V : ClosedIrreducibleAnalyticSubvariety (n + n) (Y₀ × Y₁) :=
    { carrier := closure C
      isClosed_carrier := isClosed_closure
      irreducible_carrier := isComplexAnalyticallyIrreducible_closure_component hFa hc
      dim := n
      dim_le := Nat.le_add_right n n
      regularLocus_nonempty := ⟨c, regularAtDim_closure_component hc (mem_component_self hc)⟩ }
  have hleftB₀ (y : Y₀) (hy : c₀ y ∉ B) : s₀ (c₀ y) = y := by
    apply hleft₀ y
    intro hyA
    apply hy
    apply Or.inl
    apply Or.inl
    change y ∈ c₀ ⁻¹' B₀
    rwa [hpre₀]
  have hleftB₁ (y : Y₁) (hy : c₁ y ∉ B) : s₁ (c₁ y) = y := by
    apply hleft₁ y
    intro hyA
    apply hy
    apply Or.inl
    apply Or.inr
    change y ∈ c₁ ⁻¹' B₁
    rwa [hpre₁]
  refine ⟨B, s₀, s₁, hBc, hBa, hBi, hs₀.mono hU₀, hs₁.mono hU₁,
    (fun x hx => hright₀ x (hU₀ hx)), (fun x hx => hright₁ x (hU₁ hx)),
    hleftB₀, hleftB₁, V, rfl, closure_component_mem_globalComponents hc,
    hclosure, closure_minimal (component_subset F c) hFa.isClosed, ?_, hSimage⟩
  intro p hp
  exact regularAtDim_closure_component hc (hSC hp)

end SGPT.Foundations.Analysis.Pending.AnalyticFibreProductRegularGraph
