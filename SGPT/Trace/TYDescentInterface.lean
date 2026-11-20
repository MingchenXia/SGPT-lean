import SGPT.Trace.P5WireTrace
import SGPT.Unibranch.ComplexSpaceThetaPSH

/-!
# The trace operator on the normalization `Ỹ`: the descent interface

Source: `chapter_trace.tex`, Section "The definition of the trace operator" (the trace of
`φ ∈ QPSH(X)` along an irreducible analytic subset `Y` of a compact connected Kähler manifold `X`
takes values in `QPSH(Ỹ)`, `Ỹ` the normalization of `Y`, a normal compact Kähler space), and
Appendix B (`appendix_unibranch.tex`): `def:unibranch:L105` (`θ`-psh functions on complex spaces),
`cor:PSH` (`π^* : PSH(X, θ) ≅ PSH(Y, π^*θ)` for a proper bimeromorphic `π : Y → X` onto a unibranch
compact Kähler space) and Section `sec:unib_ext` (the theory of the main chapters extends to
unibranch compact Kähler spaces *mutatis mutandis*; `{θ}` is big iff its pullback to one, hence
every, resolution is big).

The resolution-level theory (`SGPT.Trace.Trace2Resolution`, `SGPT.Trace.P5Wire`) proves the
statements of the trace chapter with `Ỹ` replaced by an arbitrary resolution `(V, ι)` of `Y`. This
file sets up the passage to `Ỹ` itself.

* `TildeY Y` packages the normalization `Ỹ` of `Y` as the book uses it: a complex space
  (`SourceReducedComplexSpace`, the book's complex spaces) with its point map `Ỹ → Y ⊆ X`, which
  is injective over the regular locus `Y_reg` of `Y` with dense preimage of `Y_reg` (the
  normalization is an isomorphism over `Y_reg`), the restriction `θ ↦ θ|_Ỹ` of closed real
  `(1,1)`-forms (a closed `(1,1)` `SpaceForm` on `Ỹ`), and one resolution of `Ỹ`.
* `TildeY.Resolution`: a resolution `ν : V → Ỹ` of `Ỹ` by a resolution target `(V, ι)` of `Y`
  (`ι = (Ỹ → X) ∘ ν`). Every resolution of `Y` from a compact Kähler manifold factors through `Ỹ`
  (`V` is normal), and conversely a resolution of `Ỹ` composed with `Ỹ → X` is a resolution of
  `Y`. The lift `ν` is determined by `ι` (`Resolution.lift_unique`), `ν` is surjective
  (`Resolution.surjective`), and two resolutions of `Ỹ` are dominated by a third one
  (`Resolution.exists_common`, from TN goal P5 `P5Wire.exists_common_resolutionTarget`).
* `TildeY.CorPSH N`: **the statement of `cor:PSH` for `ν : V → Ỹ` and the forms `θ|_Ỹ`**: for
  every closed real `(1,1)`-form `θ` on `X`, `ψ ↦ ψ ∘ ν` maps `PSH(Ỹ, θ|_Ỹ)` (`def:unibranch:L105`,
  `SourceReducedComplexSpace.IsThetaPSH`) onto `PSH(V, ν^*(θ|_Ỹ)) = PSH(V, ι^*θ)`; injectivity is
  automatic (`CorPSH.injective`). It is taken as an explicit hypothesis by the transport
  theorems of the `TY*` files.

The *readings* of a function `ψ` on `Ỹ` are the functions `ψ ∘ ν` on the resolutions of `Ỹ`. The
notions which the book defines on `Ỹ` by the same formulas as on manifolds (non-pluripolar
masses, `P`-order, `𝓘`-goodness, `d_S`) are read on resolutions (`sec:unib_ext`: non-pluripolar
products on `Ỹ` are defined as in `chap:npp`, hence are those of a resolution, `Ỹ` and `V` being
isomorphic off nowhere dense analytic sets which carry no non-pluripolar mass); the readings do
not depend on the resolution (common resolutions and the bimeromorphic invariance results).
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology Manifold ENNReal ContDiff

universe u

namespace SGPT.Trace.TY

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
  SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
  SGPT.Trace.Trace2Resolution SGPT.Unibranch

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- **The normalization `Ỹ` of an irreducible analytic subset `Y ⊆ X`, as used by the trace
chapter.** A complex space `space` (reduced, Hausdorff, paracompact, locally embedded:
`SourceReducedComplexSpace`) with a continuous point map `toX : Ỹ → X` with values in `Y`, which is
injective over the regular locus `Y_reg = Y \ singularLocus Y` with dense preimage of `Y_reg`
(the normalization is an isomorphism over the normal, in particular over the regular, locus), the
restriction `restrict θ = θ|_Ỹ` of closed real `(1,1)`-forms on `X` (pull-back along `Ỹ → X`, a
closed `(1,1)` form on `Ỹ` in the sense of `def:unibranch:L105`), and a resolution of `Ỹ` by a
resolution target of `Y` (`thm:res` for `Ỹ`). -/
structure TildeY (Y : ClosedIrreducibleAnalyticSubvariety n X) where
  /-- The complex space `Ỹ`. -/
  space : SourceReducedComplexSpace
  /-- The point map `Ỹ → Y ⊆ X`. -/
  toX : space.obj.left → X
  continuous_toX : Continuous toX
  toX_mem : ∀ y, toX y ∈ Y.carrier
  injOn_regular : InjOn toX (toX ⁻¹' (singularLocus Y)ᶜ)
  dense_regular : Dense (toX ⁻¹' (singularLocus Y)ᶜ)
  /-- `θ ↦ θ|_Ỹ`. -/
  restrict : ClosedRealOneOneForm n X → SpaceForm space 2
  restrict_isClosed : ∀ θ, (restrict θ).IsClosed
  restrict_isOneOne : ∀ θ, (restrict θ).IsOneOne
  /-- `Ỹ` has a resolution by a resolution target of `Y`. -/
  exists_lift : ∃ (R : ResolutionTarget Y) (ν : R.V → space.obj.left), Continuous ν ∧
    ∀ v, toX (ν v) = R.ι v

namespace TildeY

variable {Y : ClosedIrreducibleAnalyticSubvariety n X} (T : TildeY Y)

instance instT2 : T2Space T.space.obj.left := T.space.property.1

/-- The book's `φ|_Ỹ`: the composition of `φ : X → [-∞, ∞)` with `Ỹ → X`. -/
def restrictFun (φ : X → EReal) : T.space.obj.left → EReal := fun y => φ (T.toX y)

/-- **A resolution of `Ỹ`**: a resolution target `(V, ι)` of `Y` (a compact connected Kähler
manifold of dimension `dim Y` with a resolution `ι : V → X` of `Y`) and a continuous lift
`ν : V → Ỹ` of `ι` (`ι = (Ỹ → X) ∘ ν`). -/
structure Resolution where
  /-- The resolution target of `Y`. -/
  R : ResolutionTarget Y
  /-- The map to `Ỹ`. -/
  ν : R.V → T.space.obj.left
  continuous : Continuous ν
  toX_comp : ∀ v, T.toX (ν v) = R.ι v

variable {T}

/-- **The lift of a resolution of `Y` to `Ỹ` is unique.** Two continuous lifts `ν, ν' : V → Ỹ`
of the same resolution `ι : V → X` of `Y` agree: they agree over `Y_reg` (where `Ỹ → X` is
injective), whose preimage is dense in `V`. -/
theorem lift_unique (R : ResolutionTarget Y) {ν ν' : R.V → T.space.obj.left}
    (hν : Continuous ν) (hν' : Continuous ν') (h : ∀ v, T.toX (ν v) = R.ι v)
    (h' : ∀ v, T.toX (ν' v) = R.ι v) : ν = ν' := by
  obtain ⟨B, -, hsing, -, hdense⟩ := R.isResolutionOf.exists_isoLocus
  refine Continuous.ext_on hdense hν hν' ?_
  intro v hv
  have hreg : R.ι v ∉ singularLocus Y := fun hs => hv (hsing hs)
  refine T.injOn_regular ?_ ?_ ((h v).trans (h' v).symm)
  · change T.toX (ν v) ∉ singularLocus Y
    rw [h v]
    exact hreg
  · change T.toX (ν' v) ∉ singularLocus Y
    rw [h' v]
    exact hreg

namespace Resolution

/-- `ν : V → Ỹ` is surjective: its image is compact, hence closed, and contains the dense
preimage of `Y_reg` in `Ỹ`. -/
theorem surjective (N : T.Resolution) : Function.Surjective N.ν := by
  have hclosed : IsClosed (range N.ν) :=
    (isCompact_range N.continuous).isClosed
  have hsub : T.toX ⁻¹' (singularLocus Y)ᶜ ⊆ range N.ν := by
    intro y hy
    have hyY : T.toX y ∈ range N.R.ι := by
      rw [N.R.isResolutionOf.range_eq]
      exact T.toX_mem y
    obtain ⟨v, hv⟩ := hyY
    refine ⟨v, T.injOn_regular ?_ hy ((N.toX_comp v).trans hv)⟩
    change T.toX (N.ν v) ∉ singularLocus Y
    rw [N.toX_comp v, hv]
    exact hy
  have hdense : Dense (range N.ν) := T.dense_regular.mono hsub
  intro y
  have hy : y ∈ range N.ν := by
    rw [hclosed.closure_eq.symm.trans hdense.closure_eq]
    trivial
  exact hy

/-- Restriction along a modification: a resolution of `Ỹ` composed with a modification
`p : V' → V` of resolution targets with `ι' = ι ∘ p` is a resolution of `Ỹ`. -/
def comp (N : T.Resolution) (R' : ResolutionTarget Y) {p : R'.V → N.R.V}
    (hp : IsAnalyticModification (n := Y.dim) p) (hcomm : ∀ w, R'.ι w = N.R.ι (p w)) :
    T.Resolution where
  R := R'
  ν := N.ν ∘ p
  continuous := N.continuous.comp hp.1.continuous
  toX_comp w := (N.toX_comp (p w)).trans (hcomm w).symm

@[simp] theorem comp_ν (N : T.Resolution) (R' : ResolutionTarget Y) {p : R'.V → N.R.V}
    (hp : IsAnalyticModification (n := Y.dim) p) (hcomm : ∀ w, R'.ι w = N.R.ι (p w)) :
    (N.comp R' hp hcomm).ν = N.ν ∘ p := rfl

/-- **Two resolutions of `Ỹ` are dominated by a third one.** For resolutions `N₁`, `N₂` of `Ỹ`
there are a resolution `N₃` and modifications `p_i : V₃ → V_i` with `ι₃ = ι_i ∘ p_i` and
`ν₃ = ν_i ∘ p_i` (TN goal P5, `P5Wire.exists_common_resolutionTarget`, and uniqueness of lifts). -/
theorem exists_common (N₁ N₂ : T.Resolution) :
    ∃ (N₃ : T.Resolution) (p₁ : N₃.R.V → N₁.R.V) (p₂ : N₃.R.V → N₂.R.V),
      IsAnalyticModification (n := Y.dim) p₁ ∧ IsAnalyticModification (n := Y.dim) p₂ ∧
      (∀ w, N₃.R.ι w = N₁.R.ι (p₁ w)) ∧ (∀ w, N₃.R.ι w = N₂.R.ι (p₂ w)) ∧
      N₃.ν = N₁.ν ∘ p₁ ∧ N₃.ν = N₂.ν ∘ p₂ := by
  obtain ⟨R₃, p₁, p₂, hp₁, hp₂, hc₁, hc₂⟩ := P5Wire.exists_common_resolutionTarget N₁.R N₂.R
  refine ⟨N₁.comp R₃ hp₁ hc₁, p₁, p₂, hp₁, hp₂, hc₁, hc₂, rfl, ?_⟩
  exact lift_unique R₃ (N₁.continuous.comp hp₁.1.continuous) (N₂.continuous.comp hp₂.1.continuous)
    (fun w => (N₁.toX_comp (p₁ w)).trans (hc₁ w).symm)
    (fun w => (N₂.toX_comp (p₂ w)).trans (hc₂ w).symm)

/-- The reading of `φ|_Ỹ` on a resolution is the pullback `φ ∘ ι`. -/
@[simp] theorem restrictFun_comp (N : T.Resolution) (φ : X → EReal) :
    T.restrictFun φ ∘ N.ν = φ ∘ N.R.ι := by
  funext v
  simp only [Function.comp_apply, restrictFun, N.toX_comp v]

end Resolution

/-- `Ỹ` has a resolution. -/
theorem nonempty_resolution (T : TildeY Y) : Nonempty T.Resolution := by
  obtain ⟨R, ν, hν, h⟩ := T.exists_lift
  exact ⟨⟨R, ν, hν, h⟩⟩

/-! ### `cor:PSH` for a resolution of `Ỹ` -/

/-- **`cor:PSH` for the resolution `ν : V → Ỹ` and the forms `θ|_Ỹ`.** For every closed real
`(1,1)`-form `θ` on `X`, the pull-back `ψ ↦ ψ ∘ ν` maps `PSH(Ỹ, θ|_Ỹ)` (`def:unibranch:L105`)
into `PSH(V, ν^*(θ|_Ỹ)) = PSH(V, ι^*θ)`, and onto it. (Injectivity is automatic,
`CorPSH.injective`.) This is the book's `cor:PSH` for `π = ν : V → Ỹ` (`Ỹ` normal, hence
unibranch) and the form `θ|_Ỹ`, whose pull-back to `V` is `ι^*θ`. -/
def CorPSH (N : T.Resolution) : Prop :=
  ∀ θ : ClosedRealOneOneForm n X,
    (∀ ψ : T.space.obj.left → EReal, T.space.IsThetaPSH (T.restrict θ) ψ →
      IsThetaPshPotential (ClosedRealOneOneForm.pullback N.R.contMDiff θ).val (ψ ∘ N.ν)) ∧
    (∀ w : N.R.V → EReal,
      IsThetaPshPotential (ClosedRealOneOneForm.pullback N.R.contMDiff θ).val w →
        ∃ ψ : T.space.obj.left → EReal, T.space.IsThetaPSH (T.restrict θ) ψ ∧ ψ ∘ N.ν = w)

/-- **The forward half of `cor:PSH`** for `ν : V → Ỹ` and the forms `θ|_Ỹ`: `ψ ∘ ν` is
`ι^*θ`-psh for every `θ|_Ỹ`-psh `ψ`. -/
def CorPSHForward (N : T.Resolution) : Prop :=
  ∀ (θ : ClosedRealOneOneForm n X) (ψ : T.space.obj.left → EReal),
    T.space.IsThetaPSH (T.restrict θ) ψ →
      IsThetaPshPotential (ClosedRealOneOneForm.pullback N.R.contMDiff θ).val (ψ ∘ N.ν)

theorem CorPSH.forward {N : T.Resolution} (h : T.CorPSH N) : T.CorPSHForward N :=
  fun θ ψ hψ => (h θ).1 ψ hψ

/-- The pull-back along a resolution of `Ỹ` is injective (`ν` is surjective). -/
theorem Resolution.comp_injective (N : T.Resolution) {ψ ψ' : T.space.obj.left → EReal}
    (h : ψ ∘ N.ν = ψ' ∘ N.ν) : ψ = ψ' :=
  N.surjective.injective_comp_right h

/-- The pull-back along a resolution of `Ỹ` reflects the pointwise order. -/
theorem Resolution.le_of_comp_le (N : T.Resolution) {ψ ψ' : T.space.obj.left → EReal}
    (h : ∀ v, ψ (N.ν v) ≤ ψ' (N.ν v)) : ψ ≤ ψ' := by
  intro y
  obtain ⟨v, rfl⟩ := N.surjective y
  exact h v

end TildeY

end SGPT.Trace.TY
