import SGPT.Foundations.Analysis.Pending.AnalyticModificationExceptionalFibres
import SGPT.Foundations.Analysis.Pending.AnalyticComplementConnected
import SGPT.Foundations.Analysis.Pending.AnalyticSubsetOpens
import Mathlib.Topology.Connected.LocallyConnected

set_option autoImplicit false

/-!
# Connected fibres of a modification to a smooth target

The connected complement of a proper analytic subset and the actual inverse
equations of an analytic modification produce connected inverse images of
connected open sets.  Compact-fibre separation and proper closed images then
give connected compact fibres.  The analytic exceptional witnesses may be
enlarged, and no blowup factorization or ambient compactness is used.

This is the smooth-target case of Xia, Appendix B.1, Theorem B.1.1.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace SGPT.Foundations.Analysis.Pending.AnalyticModificationConnectedFibres

open FirstPass AnalyticModificationLocalDiscrepancy

noncomputable section

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {Y : Type u} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- The inverse image of a nonempty connected open set under an actual
analytic modification is nonempty and connected. -/
theorem isConnected_preimage_of_isConnected {g : Y → X}
    (hg : IsAnalyticModification (n := n) g) (U : Opens X)
    (hU : IsConnected (U : Set X)) : IsConnected (g ⁻¹' (U : Set X)) := by
  obtain ⟨A, B, s, _, _, hAi, _, hBa, hBi, hpre, hs, hright, hleft⟩ := hg.2.2
  let : ConnectedSpace U := isConnected_iff_connectedSpace.mp hU
  have hT : IsComplexAnalyticSubset (n := n) ((↑) ⁻¹' B : Set U) :=
    AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hBa U
  have hTne : ((↑) ⁻¹' B : Set U) ≠ univ := by
    intro heq
    have hUB : (U : Set X) ⊆ B := by
      intro x hx
      have hxT : (⟨x, hx⟩ : U) ∈ ((↑) ⁻¹' B : Set U) := by rw [heq]; trivial
      exact hxT
    obtain ⟨x, hx⟩ := hU.nonempty
    have h := interior_maximal hUB U.isOpen hx
    rw [hBi] at h
    exact h
  have hcomp := AnalyticComplementConnected.isPreconnected_compl hT hTne
  have hval : (Subtype.val : U → X) '' (((↑) ⁻¹' B : Set U)ᶜ) =
      (U : Set X) \ B := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, hy⟩
    · intro hx
      exact ⟨⟨x, hx.1⟩, hx.2, rfl⟩
  have hUB : IsPreconnected ((U : Set X) \ B) := by
    rw [← hval]
    exact hcomp.image Subtype.val continuous_subtype_val.continuousOn
  have hEq : s '' ((U : Set X) \ B) = (g ⁻¹' (U : Set X)) \ A := by
    ext y
    constructor
    · rintro ⟨x, ⟨hxU, hxB⟩, rfl⟩
      have heq := hright x hxB
      refine ⟨by change g (s x) ∈ U; rwa [heq], ?_⟩
      intro hsA
      rw [← hpre] at hsA
      change g (s x) ∈ B at hsA
      exact hxB (heq ▸ hsA)
    · rintro ⟨hyU, hyA⟩
      have hyB : g y ∉ B := by
        intro hyB
        apply hyA
        rw [← hpre]
        exact hyB
      exact ⟨g y, ⟨hyU, hyB⟩, hleft y hyA⟩
  have hP : IsPreconnected ((g ⁻¹' (U : Set X)) \ A) := by
    rw [← hEq]
    exact hUB.image s (hs.continuousOn.mono fun _ hx => hx.2)
  have hdense : (g ⁻¹' (U : Set X)) ⊆ closure ((g ⁻¹' (U : Set X)) \ A) := by
    intro y hy
    rw [mem_closure_iff_nhds]
    intro N hN
    have hO : IsOpen (interior N ∩ g ⁻¹' (U : Set X)) :=
      isOpen_interior.inter (U.isOpen.preimage hg.1.continuous)
    have hyO : y ∈ interior N ∩ g ⁻¹' (U : Set X) :=
      ⟨mem_interior_iff_mem_nhds.mpr hN, hy⟩
    have hnot : ¬ interior N ∩ g ⁻¹' (U : Set X) ⊆ A := by
      intro hsub
      have h := interior_maximal hsub hO hyO
      rw [hAi] at h
      exact h
    obtain ⟨z, ⟨hzN, hzU⟩, hzA⟩ := not_subset.mp hnot
    exact ⟨z, interior_subset hzN, hzU, hzA⟩
  refine ⟨?_, hP.subset_closure sdiff_subset hdense⟩
  obtain ⟨x, hx⟩ := hU.nonempty
  obtain ⟨y, hy⟩ := AnalyticModificationStrongPullback.surjective_of_isAnalyticModification hg x
  exact ⟨y, by change g y ∈ U; rwa [hy]⟩

/-- Every actual fibre of an analytic modification is a nonempty connected
compact set, in every dimension. -/
theorem isConnected_fibre {g : Y → X} (hg : IsAnalyticModification (n := n) g)
    (x : X) : IsConnected (g ⁻¹' ({x} : Set X)) ∧
      IsCompact (g ⁻¹' ({x} : Set X)) := by
  have hFc : IsCompact (g ⁻¹' ({x} : Set X)) :=
    hg.2.1.isCompact_preimage isCompact_singleton
  have hFne : (g ⁻¹' ({x} : Set X)).Nonempty := by
    obtain ⟨y, hy⟩ := AnalyticModificationStrongPullback.surjective_of_isAnalyticModification hg x
    exact ⟨y, hy⟩
  refine ⟨⟨hFne, isPreconnected_closed_iff.mpr ?_⟩, hFc⟩
  intro K L hK hL hcover hFK hFL
  by_contra hnot
  have hd : Disjoint ((g ⁻¹' ({x} : Set X)) ∩ K) ((g ⁻¹' ({x} : Set X)) ∩ L) := by
    rw [disjoint_left]
    intro y hyK hyL
    exact hnot ⟨y, hyK.1, hyK.2, hyL.2⟩
  obtain ⟨O₁, O₂, hO₁, hO₂, hKO₁, hLO₂, hdisj⟩ :=
    SeparatedNhds.of_isCompact_isCompact_isClosed (hFc.inter_right hK)
      (hFc.inter_right hL) (hFc.inter_right hL).isClosed hd
  have hFO : g ⁻¹' ({x} : Set X) ⊆ O₁ ∪ O₂ := by
    intro y hy
    rcases hcover hy with hyK | hyL
    · exact Or.inl (hKO₁ ⟨hy, hyK⟩)
    · exact Or.inr (hLO₂ ⟨hy, hyL⟩)
  have hNo : IsOpen (g '' (O₁ ∪ O₂)ᶜ)ᶜ :=
    (hg.2.1.isClosedMap _ (hO₁.union hO₂).isClosed_compl).isOpen_compl
  have hxN : x ∈ (g '' (O₁ ∪ O₂)ᶜ)ᶜ := by
    rintro ⟨y, hyO, hyx⟩
    exact hyO (hFO hyx)
  have hpreN : g ⁻¹' (g '' (O₁ ∪ O₂)ᶜ)ᶜ ⊆ O₁ ∪ O₂ := by
    intro y hy
    by_contra hyO
    exact hy ⟨y, hyO, rfl⟩
  let : LocallyConnectedSpace X := ChartedSpace.locallyConnectedSpace (ComplexModel n) X
  obtain ⟨U, ⟨hUo, hxU, hUconn⟩, hUN⟩ :=
    (LocallyConnectedSpace.open_connected_basis x).mem_iff.mp (hNo.mem_nhds hxN)
  have hpreU := isConnected_preimage_of_isConnected hg (⟨U, hUo⟩ : Opens X) hUconn
  have hsub : g ⁻¹' U ⊆ O₁ ∪ O₂ := fun y hy => hpreN (hUN hy)
  have hmeet₁ : (g ⁻¹' U ∩ O₁).Nonempty := by
    obtain ⟨y, hyF, hyK⟩ := hFK
    refine ⟨y, ?_, hKO₁ ⟨hyF, hyK⟩⟩
    change g y ∈ U
    change g y = x at hyF
    rwa [hyF]
  have hmeet₂ : (g ⁻¹' U ∩ O₂).Nonempty := by
    obtain ⟨y, hyF, hyL⟩ := hFL
    refine ⟨y, ?_, hLO₂ ⟨hyF, hyL⟩⟩
    change g y ∈ U
    change g y = x at hyF
    rwa [hyF]
  obtain ⟨y, _, hy₁, hy₂⟩ := hpreU.isPreconnected O₁ O₂ hO₁ hO₂ hsub hmeet₁ hmeet₂
  exact disjoint_left.mp hdisj hy₁ hy₂

end

end SGPT.Foundations.Analysis.Pending.AnalyticModificationConnectedFibres
