import SGPT.Unibranch.PDThetaForms
import SGPT.Foundations.Analysis.Pending.LogWeightFactorization
import SGPT.Foundations.Analysis.FirstPass.CoordinateDensityGeometry

/-!
# Smooth closed real `(1,1)`-forms are exactly the forms with local `ddᶜ`-potentials

Source `def:unibranch:L105` (Appendix B, SGPT `31e08372`, footnote): "a *smooth closed real
`(1,1)`-form* on `X` is one which, near every point, is the restriction of a smooth closed real
`(1,1)`-form on an open subset of `ℂᴺ` under a local embedding of `X`; equivalently, `θ` has local
smooth `ddᶜ`-potentials."

The first notion is `SGPT.Unibranch.PD.IsLocallyClosedOneOne`. One direction of the
"equivalently" is `IsLocallyClosedOneOne.exists_local_potential` (local `ddᶜ`-lemma). Here we
prove the converse and the equivalence:

* `isLocallyClosedOneOne_of_exists_local_potential`: if near every point `θ` is the restriction
  `θ.RestrictsTo e (smoothDDC g)` of `ddᶜ g` for a smooth `g` on the ambient open set of a local
  embedding, then `θ` is a smooth closed real `(1,1)`-form. Indeed `ddᶜ g = d (dᶜ g)` is smooth
  (`smoothDDC_contDiffOn`), closed (`d ∘ d = 0`, `extDeriv_extDeriv_apply`) and `J`-invariant
  (`MongeAmpere.smoothDDC_isOneOne`, symmetry of the real Hessian).
* `isLocallyClosedOneOne_iff_exists_local_potential`: the equivalence, with potentials on the
  ambient open set of a local embedding.
* `isLocallyClosedOneOne_iff_exists_connected_local_potential`: the same with connected ambient
  open sets, i.e. exactly the potential datum used in the definition of `θ`-psh functions
  (`SourceReducedComplexSpace.IsThetaPSH`).

Lane L105, blueprint `l105.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Topology ContDiff
open SGPT.Foundations.Analysis.FirstPass

namespace SGPT.Unibranch.PD

noncomputable section

variable {X : SourceReducedComplexSpace}

/-- `ddᶜ g = d (dᶜ g)` of a smooth function is closed on the open set where `g` is smooth. -/
theorem extDeriv_smoothDDC_eq_zero {n : ℕ} {U : Set (ComplexModel n)} (hU : IsOpen U)
    {g : ComplexModel n → ℝ} (hg : ContDiffOn ℝ ∞ g U) {z : ComplexModel n} (hz : z ∈ U) :
    extDeriv (smoothDDC g) z = 0 := by
  have hdc : ContDiffAt ℝ ∞ (smoothDc g) z :=
    (smoothDc_contDiffOn hU hg z hz).contDiffAt (hU.mem_nhds hz)
  exact extDeriv_extDeriv_apply hdc
    (by simpa using ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)

/-- Source `def:unibranch:L105` (footnote), converse direction: a form with local smooth
`ddᶜ`-potentials, i.e. near every point the restriction of `ddᶜ g` under a local embedding with
`g` smooth on the ambient open set, is a smooth closed real `(1,1)`-form. -/
theorem isLocallyClosedOneOne_of_exists_local_potential {θ : SpaceForm X 2}
    (h : ∀ x : X.obj.left, ∃ e : LocalEmbedding X, x ∈ range e.toPoint ∧
      ∃ g : ComplexModel e.dim → ℝ, ContDiffOn ℝ ∞ g e.ambient ∧
        θ.RestrictsTo e (smoothDDC g)) :
    IsLocallyClosedOneOne θ := by
  intro x
  obtain ⟨e, hx, g, hg, hr⟩ := h x
  refine ⟨e, hx, smoothDDC g,
    SGPT.Foundations.Analysis.Pending.LogWeightFactorization.smoothDDC_contDiffOn e.ambient.isOpen hg,
    fun z hz => extDeriv_smoothDDC_eq_zero e.ambient.isOpen hg hz, ?_, hr⟩
  intro z hz a b
  exact MongeAmpere.smoothDDC_isOneOne
    ((hg z hz).contDiffAt (e.ambient.isOpen.mem_nhds hz)
      |>.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) a b

/-- Source `def:unibranch:L105` (footnote): a smooth closed real `(1,1)`-form on `X` (near every
point the restriction of a smooth closed real `(1,1)`-form on an open subset of `ℂᴺ` under a local
embedding) is the same as a form with local smooth `ddᶜ`-potentials. -/
theorem isLocallyClosedOneOne_iff_exists_local_potential {θ : SpaceForm X 2} :
    IsLocallyClosedOneOne θ ↔
      ∀ x : X.obj.left, ∃ e : LocalEmbedding X, x ∈ range e.toPoint ∧
        ∃ g : ComplexModel e.dim → ℝ, ContDiffOn ℝ ∞ g e.ambient ∧
          θ.RestrictsTo e (smoothDDC g) := by
  refine ⟨fun h x => ?_, isLocallyClosedOneOne_of_exists_local_potential⟩
  obtain ⟨e, hx, -, g, hg, hr⟩ := h.exists_local_potential x
  exact ⟨e, hx, g, hg, hr⟩

/-- Source `def:unibranch:L105` (footnote), with connected ambient open sets: the potential datum
is then exactly the one of the definition of `θ`-psh functions (`IsThetaPSH`). -/
theorem isLocallyClosedOneOne_iff_exists_connected_local_potential {θ : SpaceForm X 2} :
    IsLocallyClosedOneOne θ ↔
      ∀ x : X.obj.left, ∃ e : LocalEmbedding X, x ∈ range e.toPoint ∧
        IsConnected (e.ambient : Set (ComplexModel e.dim)) ∧
        ∃ g : ComplexModel e.dim → ℝ, ContDiffOn ℝ ∞ g e.ambient ∧
          θ.RestrictsTo e (smoothDDC g) := by
  refine ⟨fun h x => h.exists_local_potential x, fun h => ?_⟩
  refine isLocallyClosedOneOne_of_exists_local_potential fun x => ?_
  obtain ⟨e, hx, -, g, hg, hr⟩ := h x
  exact ⟨e, hx, g, hg, hr⟩

end

end SGPT.Unibranch.PD
