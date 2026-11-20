import SGPT.Unibranch.ComplexSpaceThetaPSH
import SGPT.Foundations.Analysis.Pending.LocalPotentials

/-!
# Smooth closed real `(1,1)`-forms on complex spaces and their local potentials

Source `def:unibranch:L105` and `cor:PSH` (Appendix B): "`θ` is a smooth closed real `(1,1)`-form
on `X`", with the footnote "closed means that locally `θ` is defined by a closed form under a local
embedding". We formalize this reading as `IsLocallyClosedOneOne θ`: near every point, `θ` is the
restriction (`SpaceForm.RestrictsTo`) under a local embedding of ONE smooth ambient real two-form
which is both closed and of type `(1,1)`.

The existing predicates `SpaceForm.IsClosed` and `SpaceForm.IsOneOne` ask for two possibly
different ambient representatives (one closed, one `J`-invariant); `IsLocallyClosedOneOne` implies
both (`IsLocallyClosedOneOne.isClosed`, `.isOneOne`). Its point is the existence of local
`ddᶜ`-potentials (`IsLocallyClosedOneOne.exists_local_potential`), which is exactly the datum used
in the definition of `θ`-psh functions (`SourceReducedComplexSpace.IsThetaPSH`): near every point
there are a local embedding into a ball and a smooth `g` with `θ = (ddᶜ g)|_V`. The proof is the
local `ddᶜ`-lemma on the ambient ball (`LocalPotentials.exists_smooth_local_ddc_potential`) and the
restriction of the local embedding to a smaller ball (`restrictsTo_restrict`).

Lane PD, blueprint `pd.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric TopologicalSpace
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass

namespace SGPT.Unibranch.PD

noncomputable section

variable {X : SourceReducedComplexSpace}

/-- Source `def:unibranch:L105`, `cor:PSH`: `θ` is a smooth closed real `(1,1)`-form on `X`: near
every point it is the restriction, under a local embedding `V ↪ Ω`, of one smooth real two-form on
`Ω` which is closed and of type `(1,1)` (invariant under `J`). -/
def IsLocallyClosedOneOne (θ : SpaceForm X 2) : Prop :=
  ∀ x : X.obj.left, ∃ e : LocalEmbedding X, x ∈ range e.toPoint ∧
    ∃ v : AmbientForm e.dim 2, ContDiffOn ℝ ∞ v e.ambient ∧
      (∀ z ∈ e.ambient, extDeriv v z = 0) ∧
      (∀ z ∈ e.ambient, ∀ a b : ComplexModel e.dim,
        v z ![Complex.I • a, Complex.I • b] = v z ![a, b]) ∧
      θ.RestrictsTo e v

theorem IsLocallyClosedOneOne.isClosed {θ : SpaceForm X 2} (h : IsLocallyClosedOneOne θ) :
    θ.IsClosed := by
  intro x
  obtain ⟨e, hx, v, hv, hcl, -, hr⟩ := h x
  exact ⟨e, hx, v, hv, hcl, hr⟩

theorem IsLocallyClosedOneOne.isOneOne {θ : SpaceForm X 2} (h : IsLocallyClosedOneOne θ) :
    θ.IsOneOne := by
  intro x
  obtain ⟨e, hx, v, hv, -, hJ, hr⟩ := h x
  exact ⟨e, hx, v, hv, hJ, hr⟩

/-- Restriction of a form to a local embedding passes to the restriction of the embedding to a
smaller ambient open set, for any ambient form agreeing with the old one there. -/
theorem restrictsTo_restrict {k : ℕ} {θ : SpaceForm X k} {e : LocalEmbedding X}
    {v : AmbientForm e.dim k} (hv : θ.RestrictsTo e v) (T : Opens (ComplexModel e.dim))
    (hT : T ≤ e.ambient) {w : AmbientForm e.dim k} (hw : EqOn w v T) :
    θ.RestrictsTo (e.restrict T hT) w := by
  intro i W G hG
  have hWT : W ⊆ (T : Set (ComplexModel e.dim)) := hG.2.1
  have hG' : e.IsTransition (θ.chart i) W G := by
    refine ⟨hG.1, fun z hz => hT (hWT hz), hG.2.2.1, hG.2.2.2.1, ?_⟩
    intro y hy
    let y' : e.restrictCarrier T hT := ⟨⟨y.val.val, hWT hy⟩, by
      have hyy : Opens.inclusion hT ⟨y.val.val, hWT hy⟩ = y.val := Subtype.ext rfl
      change Opens.inclusion hT ⟨y.val.val, hWT hy⟩ ∈ e.carrier
      rw [hyy]
      exact y.property⟩
    obtain ⟨z, hz, hzy⟩ := hG.2.2.2.2 y' hy
    refine ⟨z, hz, ?_⟩
    rw [hzy]
    rw [LocalEmbedding.restrict_toPoint]
    rfl
  have hvan := hv i W G hG'
  intro m D h hD hh hmaps z hz
  have hmaps' : ∀ z ∈ D, h z ∈ W ∧ ∃ c : e.carrier, c.val.val = h z := by
    intro z hz
    obtain ⟨hzW, c, hc⟩ := hmaps z hz
    exact ⟨hzW, ⟨⟨Opens.inclusion hT c.val, c.property⟩, hc⟩⟩
  have h0 := hvan m D h hD hh hmaps' z hz
  have hwv : w (h z) = v (h z) := hw (hWT (hmaps z hz).1)
  simp only [pullbackForm, Pi.sub_apply] at h0 ⊢
  rw [hwv]
  exact h0

/-- **Local potentials.** A smooth closed real `(1,1)`-form on a complex space has, near every
point, a local embedding into a ball and a smooth ambient potential `g` with `θ = (ddᶜ g)|_V`. -/
theorem IsLocallyClosedOneOne.exists_local_potential {θ : SpaceForm X 2}
    (h : IsLocallyClosedOneOne θ) (x : X.obj.left) :
    ∃ e : LocalEmbedding X, x ∈ range e.toPoint ∧
      IsConnected (e.ambient : Set (ComplexModel e.dim)) ∧
      ∃ g : ComplexModel e.dim → ℝ, ContDiffOn ℝ ∞ g e.ambient ∧
        θ.RestrictsTo e (smoothDDC g) := by
  obtain ⟨e, ⟨c, rfl⟩, v, hv, hcl, hJ, hr⟩ := h x
  obtain ⟨W, ρ, hcW, hW, hWe, hρ, heq⟩ :=
    SGPT.Foundations.Analysis.Pending.LocalPotentials.exists_smooth_local_ddc_potential
      e.ambient.isOpen v hv hcl (fun z hz a b => hJ z hz a b) c.val.property
  obtain ⟨r, hr0, hrW⟩ := Metric.isOpen_iff.mp hW _ hcW
  let T : Opens (ComplexModel e.dim) := ⟨ball (c : ComplexModel e.dim) r, isOpen_ball⟩
  have hTW : (T : Set (ComplexModel e.dim)) ⊆ W := hrW
  have hT : T ≤ e.ambient := fun z hz => hWe (hTW hz)
  refine ⟨e.restrict T hT, ?_, ?_, ρ, hρ.mono hTW, ?_⟩
  · refine ⟨⟨⟨(c : ComplexModel e.dim), mem_ball_self hr0⟩, ?_⟩, ?_⟩
    · have hcc : Opens.inclusion hT ⟨(c : ComplexModel e.dim), mem_ball_self hr0⟩ = c.val :=
        Subtype.ext rfl
      change Opens.inclusion hT ⟨(c : ComplexModel e.dim), mem_ball_self hr0⟩ ∈ e.carrier
      rw [hcc]
      exact c.property
    · rw [LocalEmbedding.restrict_toPoint]
      rfl
  · exact (convex_ball _ _).isConnected (Metric.nonempty_ball.mpr hr0)
  · exact restrictsTo_restrict hr T hT fun z hz => heq (hTW hz)

end

end SGPT.Unibranch.PD
