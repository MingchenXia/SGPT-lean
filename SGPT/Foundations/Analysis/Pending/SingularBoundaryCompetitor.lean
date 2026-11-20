import SGPT.Foundations.Analysis.Pending.ERealBoundaryMaxPastingPSH

set_option autoImplicit false

/-! # Actual pointwise boundary competitors for singular Perron maximum pasting -/

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SingularBoundaryCompetitor

open ERealBoundaryMaxPastingTopology ERealBoundaryMaxPastingPSH

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Actual closure upper semicontinuity and actual pointwise boundary comparison give genuine PSH pasting. -/
theorem plurisubharmonicOn_gluedMax_of_boundary_le
    {Ω D : Set E} {v u : E → EReal} (hΩ : IsOpen Ω) (hD : IsOpen D)
    (hu : PlurisubharmonicOn u Ω) (hv : PlurisubharmonicOn v D)
    (hvusc : UpperSemicontinuousOn v (closure D))
    (hvu : ∀ x ∈ Ω ∩ frontier D, v x ≤ u x) :
    PlurisubharmonicOn (gluedMax D v u) Ω :=
  plurisubharmonicOn_gluedMax hΩ hD hu hv
    (boundaryDominatedOn_of_upperSemicontinuousOn_closure hvusc hvu)

/-- The actual source boundary competitor on an actual compact patch closure internally has a real upper bound, retaining poles. -/
theorem exists_boundary_competitor_upper_bound
    {Ω D : Set E} {v u : E → EReal} (hD : IsOpen D)
    (hu : PlurisubharmonicOn u Ω) (hv : PlurisubharmonicOn v D)
    (hvusc : UpperSemicontinuousOn v (closure D))
    (hvu : ∀ x ∈ Ω ∩ frontier D, v x ≤ u x)
    (hcompact : IsCompact (closure D)) (hclosure : closure D ⊆ Ω) :
    ∃ C : ℝ, ∀ x ∈ closure D, v x ≤ (C : EReal) := by
  have hvtop : ∀ x ∈ closure D, v x ≠ ⊤ := by
    intro x hx
    by_cases hxD : x ∈ D
    · exact (hv x hxD).ne_top
    · have hxfr : x ∈ frontier D := by
        rw [hD.frontier_eq]
        exact ⟨hx, hxD⟩
      exact ne_of_lt ((hvu x ⟨hclosure hx, hxfr⟩).trans_lt
        (lt_top_iff_ne_top.mpr (hu x (hclosure hx)).ne_top))
  rcases (closure D).eq_empty_or_nonempty with hempty | hnonempty
  · refine ⟨0, fun x hx => ?_⟩
    rw [hempty] at hx
    exact False.elim hx
  · obtain ⟨y, hy, hmax⟩ := hvusc.exists_isMaxOn hnonempty hcompact
    obtain ⟨C, hC, _⟩ := EReal.exists_rat_btwn_of_lt
      (lt_top_iff_ne_top.mpr (hvtop y hy))
    exact ⟨C, fun x hx => (hmax hx).trans hC.le⟩

end

end SGPT.Foundations.Analysis.Pending.SingularBoundaryCompetitor
