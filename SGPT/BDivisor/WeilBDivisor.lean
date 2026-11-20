import SGPT.BDivisor.Modification
import SGPT.BDivisor.ClassPushforward

/-!
# Weil and Cartier b-divisors

Source: `chap:bdiv`, `sec:bdivnotion` (`def:bdiv:L38`, `def:bdiv:L116`, `def:nefCar`).

Let `X` be a compact complex manifold of dimension `n > 0`. A **(Weil) b-divisor** over `X` is a
family `(𝔻_π)_π` of real `(1,1)`-classes `𝔻_π ∈ H^{1,1}(Y_π, ℝ)`, indexed by the modifications
`π : Y_π → X`, compatible under push-forward: if `π'` dominates `π` through `g : Y_{π'} → Y_π`,
then `g_* 𝔻_{π'} = 𝔻_π` (`SGPT.BDivisor.classPushforward`, the push-forward of Bott--Chern
classes along `g`, induced by the push-forward of currents). Weil b-divisors form a real vector
space (a submodule of the product of the `H^{1,1}(Y_π, ℝ)`). `𝔻 ≤ 𝔻'` means that every
`𝔻'_π - 𝔻_π` is pseudo-effective; `𝔻` is pseudo-effective if `𝔻 ≥ 0`; the root of `𝔻` is
`𝔻_X`. A **Cartier** b-divisor is a Weil b-divisor with a realization `(π, α_Y)`: for every
`π'` dominating `π`, `𝔻_{π'}` is the pull-back of `α_Y`. It is **nef** if it has a realization
with `α_Y` nef.

Conventions. Modifications are the proper holomorphic bimeromorphic maps from complex manifolds
(`SGPT.BDivisor.Modification`; see that file for the comparison with the book's "locally finite
compositions of blow-ups with smooth centres", which are cofinal by `thm:HironakaChow`). The
classes are the real Bott--Chern classes `RealBottChern` of smooth closed real `(1,1)`-forms;
push-forwards are computed with the coefficient frame `canonicalBasis n` (any frame gives a
current push-forward with the same chart functionals). Pseudo-effectivity is
`ClassPseudoeffectiveViaPotentials` (the class contains a closed positive current `θ + ddᶜφ`,
`def:psefclass`); nefness of a class on a compact manifold is nefness with respect to a Kähler
form (`ClassNefWithRespectTo`), which is independent of the Kähler form on a compact manifold
(`SGPT.BDivisor.classNefWithRespectTo_iff`).
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.BDivisor

open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [CompactSpace X]

namespace Modification

variable (hn : 0 < n)

/-- The push-forward `g_* : H^{1,1}(Y_{π'}, ℝ) → H^{1,1}(Y_π, ℝ)` along the dominating morphism
`g` of `π ≤ π'`. -/
def classPushforwardOfLE {π π' : Modification n X} (h : π ≤ π') :
    RealBottChern n π'.carrier →ₗ[ℝ] RealBottChern n π.carrier :=
  classPushforward (contMDiff_homOfLE h) (CanonicalCurrentFrame.canonicalBasis n) hn

/-- The push-forward along a domination is the push-forward along any holomorphic map over `X`. -/
theorem classPushforwardOfLE_eq {π π' : Modification n X} (h : π ≤ π')
    {g : π'.carrier → π.carrier}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g)
    (hc : π.map ∘ g = π'.map) (α : RealBottChern n π'.carrier) :
    classPushforwardOfLE hn h α =
      classPushforward hg (CanonicalCurrentFrame.canonicalBasis n) hn α := by
  have := homOfLE_eq h hg hc
  subst this
  rfl

theorem classPushforwardOfLE_refl (π : Modification n X) (α : RealBottChern n π.carrier) :
    classPushforwardOfLE hn (le_refl π) α = α := by
  rw [classPushforwardOfLE_eq hn (le_refl π) contMDiff_id rfl]
  exact classPushforward_id _ hn α

/-- Functoriality of the push-forwards along a chain of dominations. -/
theorem classPushforwardOfLE_trans {π π' π'' : Modification n X} (h₁ : π ≤ π') (h₂ : π' ≤ π'')
    (α : RealBottChern n π''.carrier) :
    classPushforwardOfLE hn (h₁.trans h₂) α =
      classPushforwardOfLE hn h₁ (classPushforwardOfLE hn h₂ α) := by
  rw [classPushforwardOfLE_eq hn (h₁.trans h₂)
    ((contMDiff_homOfLE h₁).comp (contMDiff_homOfLE h₂))
    (by rw [← Function.comp_assoc, map_comp_homOfLE, map_comp_homOfLE])]
  exact classPushforward_comp _ hn (contMDiff_homOfLE h₁) (contMDiff_homOfLE h₂) α

end Modification

variable (n X) in
/-- The compatible families of classes, as a real subspace of the product of the
`H^{1,1}(Y_π, ℝ)`. -/
def weilBDivisors (hn : 0 < n) :
    Submodule ℝ ((π : Modification n X) → RealBottChern n π.carrier) where
  carrier := {D | ∀ (π π' : Modification n X) (h : π ≤ π'),
    Modification.classPushforwardOfLE hn h (D π') = D π}
  zero_mem' := by
    intro π π' h
    exact map_zero _
  add_mem' := by
    intro D D' hD hD' π π' h
    change Modification.classPushforwardOfLE hn h (D π' + D' π') = D π + D' π
    rw [map_add, hD π π' h, hD' π π' h]
  smul_mem' := by
    intro c D hD π π' h
    change Modification.classPushforwardOfLE hn h (c • D π') = c • D π
    rw [map_smul, hD π π' h]

variable (n X) in
/-- **Weil b-divisors** over `X` (`def:bdiv:L38`): families `(𝔻_π)_π` of classes
`𝔻_π ∈ H^{1,1}(Y_π, ℝ)` over all modifications `π` of `X`, compatible under push-forward:
`g_* 𝔻_{π'} = 𝔻_π` whenever `π'` dominates `π` through `g`. They form a real vector space. -/
abbrev WeilBDivisor (hn : 0 < n) := ↥(weilBDivisors n X hn)

namespace WeilBDivisor

variable {hn : 0 < n}

/-- The class of a Weil b-divisor on a model. -/
def onModel (D : WeilBDivisor n X hn) (π : Modification n X) : RealBottChern n π.carrier :=
  D.val π

/-- The compatibility under push-forward. -/
theorem pushforward_onModel (D : WeilBDivisor n X hn) {π π' : Modification n X} (h : π ≤ π') :
    Modification.classPushforwardOfLE hn h (D.onModel π') = D.onModel π :=
  D.property π π' h

/-- The **root** `𝔻_X` of a Weil b-divisor: its class on the trivial modification `id : X → X`. -/
def root (D : WeilBDivisor n X hn) : RealBottChern n X :=
  D.onModel Modification.root

/-- `𝔻 ≤ 𝔻'` (`def:bdiv:L38`): `𝔻'_π - 𝔻_π` is pseudo-effective on every model. -/
def LE (D D' : WeilBDivisor n X hn) : Prop :=
  ∀ π : Modification n X, ClassPseudoeffectiveViaPotentials (D'.onModel π - D.onModel π)

/-- A Weil b-divisor is **pseudo-effective** if `𝔻 ≥ 0`. -/
def IsPseudoeffective (D : WeilBDivisor n X hn) : Prop := LE 0 D

theorem isPseudoeffective_iff (D : WeilBDivisor n X hn) :
    D.IsPseudoeffective ↔ ∀ π, ClassPseudoeffectiveViaPotentials (D.onModel π) := by
  unfold IsPseudoeffective LE
  refine forall_congr' fun π => ?_
  have h0 : (0 : WeilBDivisor n X hn).onModel π = 0 := rfl
  rw [h0, sub_zero]

/-- `(π, α)` is a **realization** of `𝔻` (`def:bdiv:L116`): for every `π'` dominating `π`, the
class `𝔻_{π'}` is the pull-back of `α ∈ H^{1,1}(Y_π, ℝ)`. -/
def IsRealization (D : WeilBDivisor n X hn) (π : Modification n X)
    (α : RealBottChern n π.carrier) : Prop :=
  ∀ (π' : Modification n X) (h : π ≤ π'), D.onModel π' = Modification.classPullbackOfLE h α

/-- A **Cartier b-divisor** (`def:bdiv:L116`) is a Weil b-divisor admitting a realization. -/
def IsCartier (D : WeilBDivisor n X hn) : Prop :=
  ∃ (π : Modification n X) (α : RealBottChern n π.carrier), D.IsRealization π α

/-- A realization `(π, α)` is a realization on the model itself: `𝔻_π = α`. -/
theorem IsRealization.onModel_eq {D : WeilBDivisor n X hn} {π : Modification n X}
    {α : RealBottChern n π.carrier} (h : D.IsRealization π α) : D.onModel π = α := by
  rw [h π (le_refl π), Modification.classPullbackOfLE_refl]

/-- A realization stays a realization on every dominating model, with the pulled-back class. -/
theorem IsRealization.pullback {D : WeilBDivisor n X hn} {π : Modification n X}
    {α : RealBottChern n π.carrier} (h : D.IsRealization π α) {π' : Modification n X}
    (hle : π ≤ π') : D.IsRealization π' (Modification.classPullbackOfLE hle α) := by
  intro π'' h'
  rw [h π'' (hle.trans h'), Modification.classPullbackOfLE_trans]

/-- A **nef Cartier b-divisor** (`def:nefCar`): a Cartier b-divisor with a realization
`(π, α_Y)` such that `α_Y` is nef (with respect to a Kähler form on `Y_π`). -/
def IsNefCartier (D : WeilBDivisor n X hn) : Prop :=
  ∃ (π : Modification n X) (α : RealBottChern n π.carrier), D.IsRealization π α ∧
    ∃ κ : KahlerBackground n π.carrier, ClassNefWithRespectTo κ α

/-- The zero b-divisor is Cartier, realized by the zero class on `X` (the definition is not
vacuous). -/
theorem isCartier_zero : (0 : WeilBDivisor n X hn).IsCartier :=
  ⟨Modification.root, 0, fun _ h => (map_zero (Modification.classPullbackOfLE h)).symm⟩

theorem IsNefCartier.isCartier {D : WeilBDivisor n X hn} (h : D.IsNefCartier) : D.IsCartier :=
  let ⟨π, α, hr, _⟩ := h
  ⟨π, α, hr⟩

end WeilBDivisor

/-- On a compact manifold, nefness of a class does not depend on the Kähler form. -/
theorem classNefWithRespectTo_iff {Y : Type u} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y] [CompactSpace Y]
    (κ κ' : KahlerBackground n Y) (α : RealBottChern n Y) :
    ClassNefWithRespectTo κ α ↔ ClassNefWithRespectTo κ' α := by
  have key : ∀ κ₁ κ₂ : KahlerBackground n Y, ClassNefWithRespectTo κ₁ α →
      ClassNefWithRespectTo κ₂ α := by
    intro κ₁ κ₂ h
    have h' := classNef_classPullback (f := (id : Y → Y))
      (contMDiff_id (I := 𝓘(ℂ, ComplexModel n)) (n := ∞)) κ₁ κ₂ h
    rwa [classPullback_id] at h'
  exact ⟨key κ κ', key κ' κ⟩

end SGPT.BDivisor
