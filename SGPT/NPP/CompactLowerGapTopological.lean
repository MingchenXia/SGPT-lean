import SGPT.NPP.Capacity2MonotoneLocal

/-!
The finite-cover atom of the actual increasing compact lower-gap proof.
The original real representatives are continuous only on the given
quasi-continuity compact core. One open neighborhood of the fixed positive
persistent gap suffices; convergence off the entire raw deficit is not an
assumption. Full source plan: compact-lower-gap.tex.
-/

set_option autoImplicit false
noncomputable section

open Set Filter
open scoped Topology

namespace SGPT.NPP.LocalIncreasingCapacityDraft

variable {M : Type*} [TopologicalSpace M]

/-- Continuous real representatives make the fixed persistent positive gap
compact, without imposing ambient continuity off the original compact core. -/
theorem isCompact_fixed_persistent_gap
    {L : Set M} (hL : IsCompact L) {f : ℕ → M → ℝ} {g : M → ℝ}
    (hf : ∀ j, ContinuousOn (f j) L) (hg : ContinuousOn g L) (a : ℝ) :
    IsCompact {x | x ∈ L ∧ ∀ j, f j x + a ≤ g x} := by
  let : CompactSpace L := isCompact_iff_compactSpace.mp hL
  have hf' : ∀ j, Continuous (fun x : L => f j x.1) :=
    fun j => continuousOn_iff_continuous_domRestrict.mp (hf j)
  have hg' : Continuous (fun x : L => g x.1) :=
    continuousOn_iff_continuous_domRestrict.mp hg
  have hA : IsClosed {x : L | ∀ j, f j x.1 + a ≤ g x.1} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun j => isClosed_le ((hf' j).add continuous_const) hg'
  have himage := hA.isCompact.image continuous_subtype_val
  convert himage using 1
  ext x
  simp only [mem_ofPred_eq, mem_image, Subtype.exists, exists_and_right,
    exists_eq_right, exists_prop]

/-- A finite compact-core cover turns exclusion of one fixed persistent
positive gap into a uniform finite-stage lower-gap bound. -/
theorem exists_eventually_lowerGap_subset_of_fixed_persistent_cover
    {L H : Set M} (hL : IsCompact L) (hHo : IsOpen H)
    {f : ℕ → M → ℝ} {g : M → ℝ}
    (hf : ∀ j, ContinuousOn (f j) L) (hg : ContinuousOn g L)
    (hm : ∀ x ∈ L, Monotone fun j => f j x)
    {δ : ℝ} (hδ : 0 < δ)
    (hcover : ∀ x ∈ L, (∀ j, f j x + δ / 2 ≤ g x) → x ∈ H) :
    ∃ N : ℕ, ∀ j, N ≤ j → ∀ x ∈ L, g x - δ > f j x → x ∈ H := by
  classical
  let K : Set M := L ∩ Hᶜ
  have hK : IsCompact K := hL.inter_right hHo.isClosed_compl
  have hloc : ∀ x ∈ K, ∃ (j : ℕ) (W : Set M), IsOpen W ∧ x ∈ W ∧
      ∀ y ∈ W ∩ K, g y - f j y < δ := by
    intro x hx
    have hnot : ¬ ∀ j, f j x + δ / 2 ≤ g x :=
      fun h => hx.2 (hcover x hx.1 h)
    push Not at hnot
    obtain ⟨j, hj⟩ := hnot
    have hpoint : g x - f j x < δ := by linarith
    have hc : ContinuousWithinAt (fun y => g y - f j y) K x :=
      ((hg x hx.1).sub (hf j x hx.1)).mono inter_subset_left
    have hev : ∀ᶠ y in 𝓝[K] x, g y - f j y < δ :=
      hc.eventually (gt_mem_nhds hpoint)
    obtain ⟨W, hWo, hxW, hW⟩ := mem_nhdsWithin.mp hev
    exact ⟨j, W, hWo, hxW, hW⟩
  choose! idx W hWo hxW hWlt using hloc
  obtain ⟨t, htcover⟩ := hK.elim_nhds_subcover' (fun x hx => W x)
    (fun x hx => (hWo x hx).mem_nhds (hxW x hx))
  obtain ⟨N, hN⟩ := Finset.exists_le (t.image fun x => idx x.1)
  refine ⟨N, fun j hj x hx hgap => ?_⟩
  by_contra hxH
  have hxK : x ∈ K := ⟨hx, hxH⟩
  obtain ⟨z, hzt, hxz⟩ := mem_iUnion₂.mp (htcover hxK)
  have hle : idx z.1 ≤ j := (hN _ (Finset.mem_image_of_mem _ hzt)).trans hj
  have hsmall := hWlt z.1 z.2 x ⟨hxz, hxK⟩
  have hmono := hm x hx hle
  linarith

end SGPT.NPP.LocalIncreasingCapacityDraft
