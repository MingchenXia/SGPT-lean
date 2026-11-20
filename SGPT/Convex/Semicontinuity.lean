import SGPT.Convex.Duality
import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Closed real-height epigraphs

The SGPT epigraph uses heights in `ℝ`, whereas mathlib's general epigraph
characterization of lower semicontinuity uses heights in the codomain `EReal`.
This module proves that these conventions give the same closedness condition,
without any vector-space or finite-dimensionality hypothesis on the domain.
It also implements the source's closed-convex classification: constant `-∞`,
constant `+∞`, or proper and lower semicontinuous. The conjugate has that full
classification; closed epigraphs alone would not imply it for arbitrary functions.
-/

namespace SGPT.Convex

open Set Filter Topology

section Topology

variable {V : Type*} [TopologicalSpace V]

/-- Lower semicontinuity is equivalent to closedness of the source's real-height epigraph. -/
theorem isClosed_epigraph_iff_lowerSemicontinuous {f : V → EReal} :
    IsClosed (epigraph f) ↔ LowerSemicontinuous f := by
  constructor
  · intro h x a ha
    obtain ⟨r, har, hrx⟩ := EReal.exists_between_coe_real ha
    have hclosed : IsClosed {y : V | f y ≤ (r : EReal)} := by
      simpa only [epigraph, Set.preimage_ofPred_eq, id_eq] using
        h.preimage (continuous_id.prodMk (continuous_const : Continuous (fun _ : V ↦ r)))
    have hopen : IsOpen {y : V | (r : EReal) < f y} := by
      simpa only [Set.compl_ofPred, not_le] using hclosed.isOpen_compl
    filter_upwards [hopen.mem_nhds hrx] with y hy
    exact lt_trans har hy
  · intro h
    have hmap : Continuous (fun p : V × ℝ ↦ (p.1, (p.2 : EReal))) :=
      continuous_fst.prodMk (continuous_coe_real_ereal.comp continuous_snd)
    simpa only [epigraph, Set.preimage_ofPred_eq] using h.isClosed_epigraph.preimage hmap

end Topology

section ClosedConvex

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]

/-- The precise closed-convex predicate of SGPT `def:convexclosure`, including its
exceptional infinite constants. This does not define the closure operation itself. -/
def IsClosedConvex (f : V → EReal) : Prop :=
  f = (fun _ ↦ ⊥) ∨ f = (fun _ ↦ ⊤) ∨ (IsProper f ∧ LowerSemicontinuous f)

/-- The source's closed-convex classification includes convexity in all cases. -/
theorem isConvex_of_isClosedConvex {f : V → EReal} (hf : IsClosedConvex f) :
    IsConvex f := by
  rcases hf with h | h | h
  · rw [h]
    exact isConvex_bot
  · rw [h]
    exact isConvex_top
  · exact h.1.1

end ClosedConvex

section Conjugation

variable {V W : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W]

/-- A support function is proper exactly when its indexing set is nonempty.
The set need not be convex or closed, and the bilinear pairing may be degenerate. -/
theorem isProper_support_iff_nonempty (B : V →ₗ[ℝ] W →ₗ[ℝ] ℝ) (P : Set V) :
    IsProper (support B P) ↔ P.Nonempty := by
  classical
  constructor
  · intro hf
    by_contra hP
    have hempty : P = ∅ := Set.not_nonempty_iff_eq_empty.mp hP
    simpa [hempty, support] using hf.2.2 (0 : W)
  · rintro ⟨x, hx⟩
    have hz : support B P (0 : W) = 0 := by
      apply le_antisymm
      · exact iSup_le fun _ ↦ by simp
      · simpa [support] using
          (le_iSup (fun p : P ↦ (B p (0 : W) : EReal)) ⟨x, hx⟩)
    refine ⟨isConvex_support B P, ⟨0, ?_⟩, ?_⟩
    · change support B P 0 < ⊤
      rw [hz]
      exact EReal.coe_lt_top 0
    · intro y
      exact ne_of_gt ((EReal.bot_lt_coe (B x y)).trans_le
        (le_iSup (fun p : P ↦ (B p y : EReal)) ⟨x, hx⟩))

/-- Unless the obstacle is everywhere `+∞`, a conjugate never takes the value `-∞`. -/
theorem conjugate_ne_bot_of_exists_ne_top (B : V →ₗ[ℝ] W →ₗ[ℝ] ℝ) (f : V → EReal)
    (h : ∃ x, f x ≠ ⊤) : ∀ y, conjugate B f y ≠ ⊥ := by
  obtain ⟨x, hx⟩ := h
  intro y
  have hterm : (B x y : EReal) - f x ≤ conjugate B f y :=
    le_iSup (fun z ↦ (B z y : EReal) - f z) x
  cases hc : f x using EReal.rec with
  | bot =>
    have htop : (⊤ : EReal) ≤ conjugate B f y := by simpa [hc] using hterm
    exact ne_of_gt (lt_of_lt_of_le bot_lt_top htop)
  | coe r =>
    have hfinite : ((B x y - r : ℝ) : EReal) ≤ conjugate B f y := by
      simpa only [hc, ← EReal.coe_sub] using hterm
    exact ne_of_gt ((EReal.bot_lt_coe _).trans_le hfinite)
  | top => exact False.elim (hx hc)

variable [TopologicalSpace W] [IsTopologicalAddGroup W] [ContinuousSMul ℝ W]
  [T2Space W] [FiniteDimensional ℝ W]

/-- The conjugate is lower semicontinuous, with the SGPT real-height convention. -/
theorem lowerSemicontinuous_conjugate (B : V →ₗ[ℝ] W →ₗ[ℝ] ℝ) (f : V → EReal) :
    LowerSemicontinuous (conjugate B f) :=
  isClosed_epigraph_iff_lowerSemicontinuous.mp (isClosed_epigraph_conjugate B f)

/-- Full closed-convex clause of SGPT `thm:Legendredual`, for arbitrary obstacles.
Properness preservation and biconjugation are separate statements. -/
theorem isClosedConvex_conjugate (B : V →ₗ[ℝ] W →ₗ[ℝ] ℝ) (f : V → EReal) :
    IsClosedConvex (conjugate B f) := by
  classical
  unfold IsClosedConvex
  by_cases htop : f = (fun _ ↦ ⊤)
  · left
    rw [htop]
    funext y
    simp [conjugate]
  have hex : ∃ x, f x ≠ ⊤ := by
    by_contra h
    apply htop
    funext x
    by_contra hx
    exact h ⟨x, hx⟩
  have hnobot := conjugate_ne_bot_of_exists_ne_top B f hex
  by_cases hg : conjugate B f = (fun _ ↦ ⊤)
  · exact Or.inr (Or.inl hg)
  · refine Or.inr (Or.inr ⟨⟨isConvex_conjugate B f, ?_, hnobot⟩,
      lowerSemicontinuous_conjugate B f⟩)
    have hexg : ∃ y, conjugate B f y ≠ ⊤ := by
      by_contra h
      apply hg
      funext y
      by_contra hy
      exact h ⟨y, hy⟩
    obtain ⟨y, hy⟩ := hexg
    exact ⟨y, lt_top_iff_ne_top.mpr hy⟩

/-- The support function has the source's exact closed-convex classification,
also for the empty set, by indicator conjugation. -/
theorem isClosedConvex_support (B : V →ₗ[ℝ] W →ₗ[ℝ] ℝ) (P : Set V) :
    IsClosedConvex (support B P) := by
  rw [← conjugate_indicator B P]
  exact isClosedConvex_conjugate B (indicator P)

end Conjugation

end SGPT.Convex
