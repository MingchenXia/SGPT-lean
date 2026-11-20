import SGPT.PSH.Basic
import SGPT.Foundations.Analysis.Pending.ERealBoundaryMaxPastingPSH

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH
open Set Filter
open SGPT.Foundations.Analysis
open SGPT.Foundations.Analysis.Pending.ERealBoundaryMaxPastingTopology
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E]

/-- The literal original boundary liminf difference condition produces
actual boundary upper control, including arbitrary original bottom poles. -/
theorem boundaryDominatedOn_of_liminf_difference
    {u v : E → EReal} {Ω D : Set E}
    (hΩ : IsOpen Ω)
    (hu : UpperSemicontinuousOn u Ω)
    (h : ∀ x ∈ Ω ∩ frontier D,
      0 ≤ liminf (fun y => u y - v y) (𝓝[D ∩ {y | v y ≠ ⊥}] x)) :
    BoundaryDominatedOn Ω D v u := by
  intro x hx c hc
  obtain ⟨r, hr, hrc⟩ := EReal.exists_between_coe_real hc
  obtain ⟨s, hrs, hsc⟩ := EReal.exists_between_coe_real hrc
  have hrsR : r < s := EReal.coe_lt_coe_iff.mp hrs
  have hdiff : ∀ᶠ y in 𝓝[D ∩ {y | v y ≠ ⊥}] x,
      ((r - s : ℝ) : EReal) < u y - v y :=
    eventually_lt_of_lt_liminf ((show ((r - s : ℝ) : EReal) < 0 by
      exact_mod_cast sub_neg.mpr hrsR).trans_le (h x hx))
  have hdiff' : ∀ᶠ y in 𝓝 x,
      y ∈ D ∩ {y | v y ≠ ⊥} → ((r - s : ℝ) : EReal) < u y - v y :=
    eventually_nhdsWithin_iff.mp hdiff
  have hur : ∀ᶠ y in 𝓝 x, u y < (r : EReal) := by
    simpa only [nhdsWithin_eq_nhds.mpr (hΩ.mem_nhds hx.1)] using hu x hx.1 (r : EReal) hr
  apply eventually_nhdsWithin_iff.mpr
  filter_upwards [hdiff', hur] with y hdy huy hyD
  by_cases hvbot : v y = ⊥
  · rw [hvbot]
    exact (bot_le : (⊥ : EReal) ≤ u x).trans_lt hc
  · have hlow := hdy ⟨hyD, hvbot⟩
    have hvs : v y < (s : EReal) := by
      by_contra hnot
      have hupper := EReal.sub_le_sub huy.le (le_of_not_gt hnot)
      have hident : (r : EReal) - (s : EReal) = ((r - s : ℝ) : EReal) := by simp
      rw [hident] at hupper
      exact (not_lt_of_ge hupper) hlow
    exact hvs.trans hsc

variable [NormedSpace ℂ E]

/-- Literal original boundary-limsup maximum pasting. The complete main
disc-submean proof is reused, and source nontriviality is inherited from u. -/
theorem pshOn_gluedMax_of_boundary_limsup
    {u v : E → EReal} {Ω D : Set E}
    (hΩ : IsOpen Ω) (hD : IsOpen D)
    (hu : PSHOn u Ω) (hv : PSHOn v D)
    (h : ∀ x ∈ Ω ∩ frontier D, limsup v (𝓝[D] x) ≤ u x) :
    PSHOn (gluedMax D v u) Ω := by
  have hb : BoundaryDominatedOn Ω D v u := fun x hx c hc =>
    eventually_lt_of_limsup_lt ((h x hx).trans_lt hc)
  refine ⟨SGPT.Foundations.Analysis.Pending.ERealBoundaryMaxPastingPSH.discPshOn_gluedMax
    hD (hu.disc.plurisubharmonicOn hΩ) (hv.disc.plurisubharmonicOn hD) hb, ?_⟩
  obtain ⟨z, hz, hzu⟩ := hu.nontrivial
  refine ⟨z, hz, ?_⟩
  have hle : u z ≤ gluedMax D v u z := by
    by_cases hzD : z ∈ D
    · rw [gluedMax_eq_max hzD]
      exact le_max_right _ _
    · simp [gluedMax, hzD]
  exact fun hbot => hzu (le_bot_iff.mp (hbot ▸ hle))

/-- Both original domains and the exact liminf difference hypothesis
produce the original PSH pasted maximum, with no boundary certificate. -/
theorem pshOn_gluedMax_of_boundary_liminf_difference
    {u v : E → EReal} {Ω D : Set E}
    (hΩ : IsOpen Ω) (hD : IsOpen D)
    (hu : PSHOn u Ω) (hv : PSHOn v D)
    (h : ∀ x ∈ Ω ∩ frontier D,
      0 ≤ liminf (fun y => u y - v y) (𝓝[D ∩ {y | v y ≠ ⊥}] x)) :
    PSHOn (gluedMax D v u) Ω := by
  have hb := boundaryDominatedOn_of_liminf_difference hΩ hu.disc.upperSemicontinuousOn h
  exact pshOn_gluedMax_of_boundary_limsup hΩ hD hu hv
    (fun x hx => (limsup_le_iff).mpr (hb x hx))

end SGPT.PSH
