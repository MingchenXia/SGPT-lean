import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Instances.EReal.Lemmas

set_option autoImplicit false

namespace SGPT.PSH

open Set Filter
open scoped Topology

variable {X I : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
  [Preorder I] [IsDirectedOrder I] [Nonempty I]

/-- Compact USC superlevels manufacture an actual maximum of the whole directed
infimum, and the literal extended supremum-infimum interchange. No countable
cofinality or non-bottom limit witness is an input. -/
theorem exists_maximum_iInf_of_compact_antitone (u : I → X → EReal)
    (hu : ∀ i, UpperSemicontinuous (u i))
    (hanti : ∀ x, Antitone (fun i ↦ u i x)) :
    ∃ p : X, (⨅ i, u i p) = (⨅ i, ⨆ x, u i x) ∧
      (⨆ x, ⨅ i, u i x) = (⨅ i, ⨆ x, u i x) := by
  classical
  let M : EReal := ⨅ i, ⨆ x, u i x
  let K : I → Set X := fun i ↦ (u i) ⁻¹' Ici M
  have hclosed (i : I) : IsClosed (K i) := (hu i).isClosed_preimage M
  have hcompact (i : I) : IsCompact (K i) := (hclosed i).isCompact
  have hnonempty (i : I) : (K i).Nonempty := by
    obtain ⟨q, _hq, hmax⟩ := (upperSemicontinuousOn_univ_iff.mpr (hu i)).exists_isMaxOn
      Set.univ_nonempty isCompact_univ
    refine ⟨q, ?_⟩
    change M ≤ u i q
    exact (iInf_le (fun i ↦ ⨆ x, u i x) i).trans
      (iSup_le (fun x ↦ hmax (mem_univ x)))
  have hdir : Directed (· ⊇ ·) K := by
    intro i j
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    refine ⟨k, ?_, ?_⟩
    · intro x hx
      exact hx.trans (hanti x hik)
    · intro x hx
      exact hx.trans (hanti x hjk)
  obtain ⟨p, hp⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    K hdir hnonempty hcompact hclosed
  have hlower : M ≤ ⨅ i, u i p := le_iInf (fun i ↦ mem_iInter.mp hp i)
  have hupper (x : X) : (⨅ i, u i x) ≤ M := by
    exact le_iInf (fun i ↦ (iInf_le (fun j ↦ u j x) i).trans
      (le_iSup (fun y ↦ u i y) x))
  have heq : (⨅ i, u i p) = M := le_antisymm (hupper p) hlower
  refine ⟨p, heq, le_antisymm (iSup_le hupper) ?_⟩
  exact heq.symm.le.trans (le_iSup (fun x ↦ ⨅ i, u i x) p)

/-- The original uniform finite lower bound on global suprema produces a true
point where the whole infimum is non-bottom. Componentwise nondegeneracy is
a separate source obligation. -/
theorem exists_iInf_ne_bot_of_compact_antitone_iSup_lower_bound (u : I → X → EReal)
    (hu : ∀ i, UpperSemicontinuous (u i))
    (hanti : ∀ x, Antitone (fun i ↦ u i x)) (a : ℝ)
    (ha : ∀ i, (a : EReal) ≤ ⨆ x, u i x) :
    ∃ p : X, (⨅ i, u i p) ≠ ⊥ := by
  obtain ⟨p, hp, _hsup⟩ := exists_maximum_iInf_of_compact_antitone u hu hanti
  refine ⟨p, ?_⟩
  intro hbot
  have hbound : (a : EReal) ≤ ⨅ i, ⨆ x, u i x := le_iInf ha
  rw [← hp, hbot] at hbound
  exact EReal.coe_ne_bot a (le_antisymm hbound bot_le)

/-- Supremum convergence for the actual arbitrary directed net, with either
infinite extended limit retained. -/
theorem tendsto_iSup_of_compact_antitone (u : I → X → EReal)
    (hu : ∀ i, UpperSemicontinuous (u i))
    (hanti : ∀ x, Antitone (fun i ↦ u i x)) :
    Tendsto (fun i ↦ ⨆ x, u i x) atTop (𝓝 (⨆ x, ⨅ i, u i x)) := by
  have hsanti : Antitone (fun i ↦ ⨆ x, u i x) := by
    intro i j hij
    exact iSup_mono (fun x ↦ hanti x hij)
  obtain ⟨_p, _hp, hs⟩ := exists_maximum_iInf_of_compact_antitone u hu hanti
  rw [hs]
  exact tendsto_atTop_iInf hsanti

end SGPT.PSH
