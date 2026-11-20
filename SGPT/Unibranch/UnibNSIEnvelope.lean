import SGPT.Foundations.Analysis.FirstPass.PositiveClasses
import SGPT.Okounkov.IEnvelopeModification
import SGPT.Foundations.Analysis.FirstPass.FormPullbackFunctorial
import SGPT.Foundations.Analysis.Pending.HironakaChowLemma

/-!
# The `𝓘`-envelope through all bimeromorphic models: the smooth case

Source `def:unibranch:L212` (`appendix_unibranch.tex`, §B.3): for an irreducible unibranch
compact Kähler space `X`, a closed real smooth `(1,1)`-form `θ` on `X` and `φ ∈ PSH(X, θ)`,
`P_θ[φ]_𝓘 ∈ PSH(X, θ)` is defined as *the unique element* such that
`π^* P_θ[φ]_𝓘 = P_{π^*θ}[π^*φ]_𝓘` for every proper bimeromorphic morphism `π : Y → X` from a
compact Kähler manifold `Y`; the book adds that this is well defined by `cor:PSH` and
`prop:Ienvelopebimero`.

This file formalizes the defining property (`IsBimeromorphicIEnvelope`) when `X` is a compact
Kähler **manifold** (a connected compact complex manifold is an irreducible unibranch compact
Kähler space), with the project's `𝓘`-envelope `iSingularityEnvelope` on manifolds
(`def:Ienv`), the pull-back of forms `ClosedRealOneOneForm.pullback`, and proper bimeromorphic
morphisms between manifolds `IsAnalyticModification`. It proves the well-definedness asserted by
the book in this case: there is exactly one function with the defining property, and it is the
ordinary `𝓘`-envelope of `def:Ienv` (`isBimeromorphicIEnvelope_iff`,
`existsUnique_isBimeromorphicIEnvelope`). The existence half is `prop:Ienvelopebimero`
(`SGPT.Okounkov.iSingularityEnvelope_modification_pullback`); uniqueness uses `π = id`.

Singular unibranch spaces are not covered: the project has no pull-back of smooth forms on
complex spaces along morphisms, no notion of compact Kähler space, and `cor:PSH` (descent of
`θ`-psh functions through a resolution) is open for singular `X`.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Unibranch.BimeromorphicIEnvelope

open Set
open scoped Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.IEnvelope SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.Pending
  AnalyticModificationLocalDiscrepancy

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- The `𝓘`-envelope only depends on the form up to geometric equality. -/
theorem iSingularityEnvelope_congr {θ η : SmoothRealForm n X 2} (h : θ.GeometricallyEq η)
    (φ : X → EReal) : iSingularityEnvelope θ φ = iSingularityEnvelope η φ := by
  have hc : iSingularityCompetitors θ φ = iSingularityCompetitors η φ := by
    ext u
    simp only [iSingularityCompetitors, thetaPshCompetitors, mem_ofPred_eq,
      h.thetaPshPotential_iff u]
  simp only [iSingularityEnvelope, iSingularitySupremum, hc]

/-- **The defining property of `P_θ[φ]_𝓘` in `def:unibranch:L212`**, on a complex manifold
`X`: `ψ` is `θ`-psh and, for every proper bimeromorphic morphism `π : Y → X` from a compact
Kähler manifold `Y`, `π^*ψ = P_{π^*θ}[π^*φ]_𝓘`. -/
def IsBimeromorphicIEnvelope (θ : ClosedRealOneOneForm n X) (φ ψ : X → EReal) : Prop :=
  IsThetaPshPotential θ.val ψ ∧
    ∀ (Y : Type u) [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
      [IsComplexManifold n Y] [CompactSpace Y], Nonempty (KahlerBackground n Y) →
      ∀ (π : Y → X) (hπ : IsAnalyticModification (n := n) π),
        ψ ∘ π = iSingularityEnvelope (ClosedRealOneOneForm.pullback hπ.1 θ).val (φ ∘ π)

/-- **Well-definedness of `def:unibranch:L212` on a compact Kähler manifold.** For
`φ ∈ PSH(X, θ)`, a function has the defining property of `P_θ[φ]_𝓘` if and only if it is the
`𝓘`-envelope `P_θ[φ]_𝓘` of `def:Ienv`. -/
theorem isBimeromorphicIEnvelope_iff [CompactSpace X] [Nonempty X]
    (hK : Nonempty (KahlerBackground n X)) (θ : ClosedRealOneOneForm n X) {φ : X → EReal}
    (hφ : IsThetaPshPotential θ.val φ) (ψ : X → EReal) :
    IsBimeromorphicIEnvelope θ φ ψ ↔ ψ = iSingularityEnvelope θ.val φ := by
  constructor
  · rintro ⟨-, h⟩
    have hid := h X hK id HironakaChowLemma.isAnalyticModification_id
    rw [ClosedRealOneOneForm.pullback_val,
      iSingularityEnvelope_congr (SmoothRealForm.pullback_id_geometricallyEq θ.val)] at hid
    exact hid
  · rintro rfl
    refine ⟨iSingularityEnvelope_isThetaPshPotential θ.val θ.property.1 θ.property.2
      hφ.1.hasSmoothLocalPotentials φ hφ, ?_⟩
    intro Y _ _ _ _ _ π hπ
    exact (SGPT.Okounkov.iSingularityEnvelope_modification_pullback hπ θ hφ).symm

/-- **`def:unibranch:L212` on a compact Kähler manifold**: for `φ ∈ PSH(X, θ)` there is exactly
one function with the defining property of `P_θ[φ]_𝓘`. -/
theorem existsUnique_isBimeromorphicIEnvelope [CompactSpace X] [Nonempty X]
    (hK : Nonempty (KahlerBackground n X)) (θ : ClosedRealOneOneForm n X) {φ : X → EReal}
    (hφ : IsThetaPshPotential θ.val φ) :
    ∃! ψ : X → EReal, IsBimeromorphicIEnvelope θ φ ψ :=
  ⟨iSingularityEnvelope θ.val φ, (isBimeromorphicIEnvelope_iff hK θ hφ _).mpr rfl,
    fun ψ hψ => (isBimeromorphicIEnvelope_iff hK θ hφ ψ).mp hψ⟩

end SGPT.Unibranch.BimeromorphicIEnvelope
