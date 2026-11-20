import SGPT.Foundations.Analysis.GluingTopology

set_option autoImplicit false

/-! # Genuine boundary upper-limit control for actual extended-real maximum pasting -/

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.ERealBoundaryMaxPastingTopology

variable {X : Type*} [TopologicalSpace X]

/-- The actual boundary upper-limit inequality, tested by every strict extended-real upper bound. -/
def BoundaryDominatedOn (Ω D : Set X) (v u : X → EReal) : Prop :=
  ∀ x ∈ Ω ∩ frontier D, ∀ c : EReal, u x < c → ∀ᶠ y in 𝓝[D] x, v y < c

/-- Actual upper semicontinuity on the patch closure and actual boundary values produce boundary upper limits. -/
theorem boundaryDominatedOn_of_upperSemicontinuousOn_closure
    {Ω D : Set X} {v u : X → EReal}
    (hv : UpperSemicontinuousOn v (closure D))
    (hvu : ∀ x ∈ Ω ∩ frontier D, v x ≤ u x) :
    BoundaryDominatedOn Ω D v u := by
  intro x hx c hc
  exact (hv x (frontier_subset_closure hx.2) c ((hvu x hx).trans_lt hc)).filter_mono
    (nhdsWithin_mono x subset_closure)

/-- Actual boundary upper limits genuinely give upper semicontinuity of the actual pasted maximum. -/
theorem upperSemicontinuousOn_gluedMax
    {Ω D : Set X} {v u : X → EReal} (hD : IsOpen D)
    (hu : UpperSemicontinuousOn u Ω) (hv : UpperSemicontinuousOn v D)
    (hboundary : BoundaryDominatedOn Ω D v u) :
    UpperSemicontinuousOn (gluedMax D v u) Ω := by
  intro x hx c hc
  by_cases hxD : x ∈ D
  · rw [gluedMax_eq_max hxD] at hc
    obtain ⟨hvc, huc⟩ := max_lt_iff.mp hc
    have hvin : ∀ᶠ y in 𝓝 x, y ∈ D → v y < c :=
      eventually_nhdsWithin_iff.mp (hv x hxD c hvc)
    filter_upwards [(hu x hx c huc), hvin.filter_mono nhdsWithin_le_nhds] with y huy hvy
    by_cases hyD : y ∈ D
    · rw [gluedMax_eq_max hyD]
      exact max_lt (hvy hyD) huy
    · simpa [gluedMax, hyD] using huy
  · have huc : u x < c := by simpa [gluedMax, hxD] using hc
    have hvin : ∀ᶠ y in 𝓝 x, y ∈ D → v y < c := by
      by_cases hxcl : x ∈ closure D
      · have hxfr : x ∈ frontier D := by
          rw [hD.frontier_eq]
          exact ⟨hxcl, hxD⟩
        exact eventually_nhdsWithin_iff.mp (hboundary x ⟨hx, hxfr⟩ c huc)
      · filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hxcl] with y hy hyD
        exact False.elim (hy (subset_closure hyD))
    filter_upwards [(hu x hx c huc), hvin.filter_mono nhdsWithin_le_nhds] with y huy hvy
    by_cases hyD : y ∈ D
    · rw [gluedMax_eq_max hyD]
      exact max_lt (hvy hyD) huy
    · simpa [gluedMax, hyD] using huy

omit [TopologicalSpace X] in
/-- Actual maximum pasting retains exclusion of positive infinity, including arbitrary pole sets. -/
theorem gluedMax_ne_top
    {Ω D : Set X} {v u : X → EReal}
    (hu : ∀ x ∈ Ω, u x ≠ ⊤) (hv : ∀ x ∈ D, v x ≠ ⊤) :
    ∀ x ∈ Ω, gluedMax D v u x ≠ ⊤ := by
  intro x hx
  by_cases hxD : x ∈ D
  · rw [gluedMax_eq_max hxD]
    exact ne_of_lt (max_lt (lt_top_iff_ne_top.mpr (hv x hxD))
      (lt_top_iff_ne_top.mpr (hu x hx)))
  · simpa [gluedMax, hxD] using hu x hx

end SGPT.Foundations.Analysis.Pending.ERealBoundaryMaxPastingTopology
