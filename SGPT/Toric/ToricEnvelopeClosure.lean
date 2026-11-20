import SGPT.Convex.Closure

set_option autoImplicit false
noncomputable section

namespace SGPT.Toric

open Set SGPT.Convex
open scoped Topology

variable {X : Type*} [TopologicalSpace X]

/-- An independent finite real reference restricted to the literal given domain. -/
def realReferenceOnDomain (g : X → ℝ) (D : Set X) : X → EReal := by
  classical
  exact fun x ↦ if x ∈ D then (g x : EReal) else ⊤

omit [TopologicalSpace X] in
/-- The true all-real-shift infimum, including both infinite input values. -/
theorem iInf_max_sub_realReference (g : X → ℝ) (G : X → EReal) :
    (fun x ↦ ⨅ C : ℝ, max (g x : EReal) (G x - (C : EReal))) =
      realReferenceOnDomain g (effectiveDomain G) := by
  classical
  funext x
  cases h : G x using EReal.rec with
  | bot => simp [realReferenceOnDomain, effectiveDomain, h]
  | top => simp [realReferenceOnDomain, effectiveDomain, h]
  | coe r =>
    have hmem : x ∈ effectiveDomain G := by
      simpa only [effectiveDomain, mem_ofPred_eq, h] using EReal.coe_lt_top r
    rw [realReferenceOnDomain, if_pos hmem]
    apply le_antisymm
    · apply iInf_le_of_le (r - g x)
      rw [← EReal.coe_sub]
      simp
    · exact le_iInf fun _ ↦ le_max_left _ _

/-- Relative continuity on the actual domain closure computes its whole epigraph closure. -/
theorem regularization_realReferenceOnDomain (g : X → ℝ) (D : Set X)
    (hg : ContinuousOn g (closure D)) :
    regularization (realReferenceOnDomain g D) =
      realReferenceOnDomain g (closure D) := by
  classical
  have hep (S : Set X) : epigraph (realReferenceOnDomain g S) =
      {p : X × ℝ | p.1 ∈ S ∧ g p.1 ≤ p.2} := by
    ext p
    by_cases hp : p.1 ∈ S <;> simp [epigraph, realReferenceOnDomain, hp]
  let C : Set (X × ℝ) := Prod.fst ⁻¹' closure D
  have hC : IsClosed C := isClosed_closure.preimage continuous_fst
  have hgc : ContinuousOn (fun p : X × ℝ ↦ g p.1) C :=
    hg.comp continuous_fst.continuousOn (fun _ hp ↦ hp)
  have hs : IsClosed {p : X × ℝ | p.1 ∈ closure D ∧ g p.1 ≤ p.2} := by
    convert (hgc.sub continuous_snd.continuousOn).preimage_isClosed_of_isClosed hC
      (isClosed_Iic : IsClosed (Iic (0 : ℝ))) using 1
    ext p
    simp [C]
  have hclosure : closure {p : X × ℝ | p.1 ∈ D ∧ g p.1 ≤ p.2} =
      {p : X × ℝ | p.1 ∈ closure D ∧ g p.1 ≤ p.2} := by
    apply le_antisymm
    · exact closure_minimal (fun _ hp ↦ ⟨subset_closure hp.1, hp.2⟩) hs
    · intro p hp
      let T : X → X × ℝ := fun y ↦ (y, g y + (p.2 - g p.1))
      have hT : ContinuousOn T (closure D) :=
        continuous_id.continuousOn.prodMk (hg.add continuous_const.continuousOn)
      have hm : MapsTo T D {q : X × ℝ | q.1 ∈ D ∧ g q.1 ≤ q.2} := by
        intro y hy
        refine ⟨hy, ?_⟩
        dsimp [T]
        linarith [hp.2]
      have ht := hm.closure_of_continuousOn hT hp.1
      simpa only [T, add_sub_cancel] using ht
  have heq : epigraph (regularization (realReferenceOnDomain g D)) =
      epigraph (realReferenceOnDomain g (closure D)) := by
    rw [epigraph_regularization, hep, hep, hclosure]
  apply le_antisymm
  · apply le_iff_epigraph_subset.mpr
    rw [heq]
  · apply le_iff_epigraph_subset.mpr
    rw [heq]

/-- The genuine source convex closure takes the regularization branch and fills precisely the
actual finite-domain closure, without an assumed envelope or domain identity. -/
theorem convexClosure_iInf_max_sub_realReference (g : X → ℝ) (G : X → EReal)
    (hg : ContinuousOn g (closure (effectiveDomain G))) :
    convexClosure (fun x ↦ ⨅ C : ℝ, max (g x : EReal) (G x - (C : EReal))) =
      realReferenceOnDomain g (closure (effectiveDomain G)) := by
  classical
  rw [iInf_max_sub_realReference]
  rw [convexClosure_of_forall_ne_bot]
  · exact regularization_realReferenceOnDomain g _ hg
  · intro x
    by_cases hx : x ∈ effectiveDomain G <;> simp [realReferenceOnDomain, hx]

end SGPT.Toric
