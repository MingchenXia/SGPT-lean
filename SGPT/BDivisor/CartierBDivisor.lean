import SGPT.BDivisor.WeilBDivisor
import SGPT.BDivisor.ModificationChangeOfVariables

/-!
# Cartier b-divisors defined by a class on a model

Source: `chap:bdiv`, `def:bdiv:L116` (Cartier b-divisors and their realizations) and
`def:nefCar`.

Let `X` be a compact connected complex manifold of dimension `n > 0`. A Cartier b-divisor is a
Weil b-divisor `𝔻` with a realization `(π, α_Y)`: `𝔻_{π'} = g^* α_Y` for every `π'` dominating `π`
through `g`. The book uses implicitly that **every** pair `(π, α_Y)` is the realization of a
(unique) Cartier b-divisor (e.g. "the Cartier b-divisor realized on `X_i` by `π_i^*H - {E_i}`" in
`ex:volbdivnetstrict`, "`𝔻(ω)` is the Cartier b-divisor realized by `(X, {ω})`" in the proof of
`thm:DT`). This rests on `g_* g^* = id` on classes along modifications
(`SGPT.BDivisor.classPushforward_classPullback`): on an arbitrary model `π'`, choose a model `ρ`
dominating both `π` and `π'` and put `𝔻_{π'} = (ρ → π')_* (ρ → π)^* α_Y`; this does not depend on
`ρ`, and the family is compatible under push-forward.

Main declarations:

* `SGPT.BDivisor.Modification.classPushforwardOfLE_classPullbackOfLE` — `g_* g^* = id` along a
  domination;
* `SGPT.BDivisor.WeilBDivisor.cartierOf π α` — the Cartier b-divisor realized by `(π, α)`, with
  `isRealization_cartierOf`, `isCartier_cartierOf`, and uniqueness
  `IsRealization.eq_cartierOf`;
* `SGPT.BDivisor.WeilBDivisor.root_cartierOf` — its root is `π_* α`;
* `SGPT.BDivisor.WeilBDivisor.cartierBDivisors` — Cartier b-divisors form a real subspace;
* `SGPT.BDivisor.WeilBDivisor.isNefCartier_cartierOf` — a nef class on a model (with a Kähler
  form) defines a nef Cartier b-divisor (`def:nefCar`).
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

/-- **`g_* g^* = id`** along the dominating morphism `g` of `π ≤ π'`. -/
theorem classPushforwardOfLE_classPullbackOfLE {π π' : Modification n X} (h : π ≤ π')
    (α : RealBottChern n π.carrier) :
    classPushforwardOfLE hn h (classPullbackOfLE h α) = α :=
  classPushforward_classPullback (Dominates.isAnalyticModification h) hn α

/-- Push–pull through a model `ρ` dominating `π` and `π'` does not change when `ρ` is replaced by a
model dominating it. -/
theorem pushPull_trans {π π' ρ ρ' : Modification n X} (h : π ≤ ρ) (h' : π' ≤ ρ) (hρ : ρ ≤ ρ')
    (α : RealBottChern n π.carrier) :
    classPushforwardOfLE hn (h'.trans hρ) (classPullbackOfLE (h.trans hρ) α) =
      classPushforwardOfLE hn h' (classPullbackOfLE h α) := by
  rw [classPushforwardOfLE_trans hn h' hρ, classPullbackOfLE_trans h hρ,
    classPushforwardOfLE_classPullbackOfLE hn hρ]

variable [ConnectedSpace X]

/-- Two modifications are dominated by a common one (directedness). -/
theorem exists_le_le (π π' : Modification n X) : ∃ ρ, π ≤ ρ ∧ π' ≤ ρ :=
  (instIsDirected (n := n) (X := X)).directed π π'

/-- Push–pull does not depend on the common model. -/
theorem pushPull_eq {π π' ρ₁ ρ₂ : Modification n X} (h₁ : π ≤ ρ₁) (h₁' : π' ≤ ρ₁)
    (h₂ : π ≤ ρ₂) (h₂' : π' ≤ ρ₂) (α : RealBottChern n π.carrier) :
    classPushforwardOfLE hn h₁' (classPullbackOfLE h₁ α) =
      classPushforwardOfLE hn h₂' (classPullbackOfLE h₂ α) := by
  obtain ⟨ρ, hρ₁, hρ₂⟩ := Modification.exists_le_le ρ₁ ρ₂
  rw [← pushPull_trans hn h₁ h₁' hρ₁, ← pushPull_trans hn h₂ h₂' hρ₂]

/-- The class on `π'` of the Cartier b-divisor realized by `(π, α)`: `(ρ → π')_* (ρ → π)^* α` for a
model `ρ` dominating both. -/
def cartierClass (π : Modification n X) (α : RealBottChern n π.carrier) (π' : Modification n X) :
    RealBottChern n π'.carrier :=
  classPushforwardOfLE hn (exists_le_le π π').choose_spec.2
    (classPullbackOfLE (exists_le_le π π').choose_spec.1 α)

/-- The defining formula holds for every model `ρ` dominating `π` and `π'`. -/
theorem cartierClass_eq {π π' ρ : Modification n X} (h : π ≤ ρ) (h' : π' ≤ ρ)
    (α : RealBottChern n π.carrier) :
    cartierClass hn π α π' = classPushforwardOfLE hn h' (classPullbackOfLE h α) :=
  pushPull_eq hn _ _ h h' α

end Modification

namespace WeilBDivisor

variable {hn : 0 < n} [ConnectedSpace X]

variable (hn) in
/-- **The Cartier b-divisor realized by `(π, α)`** (`def:bdiv:L116`): the Weil b-divisor whose
class on a model `π'` is `(ρ → π')_* (ρ → π)^* α` for any model `ρ` dominating `π` and `π'`. -/
def cartierOf (π : Modification n X) (α : RealBottChern n π.carrier) : WeilBDivisor n X hn :=
  ⟨fun π' => Modification.cartierClass hn π α π', by
    intro π₁ π₂ h
    obtain ⟨ρ, hρ, hρ₂⟩ := Modification.exists_le_le π π₂
    change Modification.classPushforwardOfLE hn h (Modification.cartierClass hn π α π₂) =
      Modification.cartierClass hn π α π₁
    rw [Modification.cartierClass_eq hn hρ hρ₂, Modification.cartierClass_eq hn hρ (h.trans hρ₂),
      Modification.classPushforwardOfLE_trans hn h hρ₂]⟩

theorem cartierOf_onModel {π π' ρ : Modification n X} (α : RealBottChern n π.carrier)
    (h : π ≤ ρ) (h' : π' ≤ ρ) :
    (cartierOf hn π α).onModel π' =
      Modification.classPushforwardOfLE hn h' (Modification.classPullbackOfLE h α) :=
  Modification.cartierClass_eq hn h h' α

/-- `(π, α)` is a realization of `cartierOf π α`. -/
theorem isRealization_cartierOf (π : Modification n X) (α : RealBottChern n π.carrier) :
    (cartierOf hn π α).IsRealization π α := by
  intro π' h
  rw [cartierOf_onModel α h (le_refl π'), Modification.classPushforwardOfLE_refl]

/-- **Every pair `(π, α)` defines a Cartier b-divisor.** -/
theorem isCartier_cartierOf (π : Modification n X) (α : RealBottChern n π.carrier) :
    (cartierOf hn π α).IsCartier :=
  ⟨π, α, isRealization_cartierOf π α⟩

/-- **Uniqueness**: a Weil b-divisor with realization `(π, α)` is `cartierOf π α`. -/
theorem IsRealization.eq_cartierOf {D : WeilBDivisor n X hn} {π : Modification n X}
    {α : RealBottChern n π.carrier} (hD : D.IsRealization π α) : D = cartierOf hn π α := by
  apply Subtype.ext
  funext π'
  obtain ⟨ρ, hρ, hρ'⟩ := Modification.exists_le_le π π'
  change D.onModel π' = (cartierOf hn π α).onModel π'
  rw [cartierOf_onModel α hρ hρ', ← hD ρ hρ, D.pushforward_onModel]

/-- A Weil b-divisor is Cartier iff it is `cartierOf π α` for some `(π, α)`. -/
theorem isCartier_iff (D : WeilBDivisor n X hn) :
    D.IsCartier ↔ ∃ (π : Modification n X) (α : RealBottChern n π.carrier),
      D = cartierOf hn π α := by
  constructor
  · rintro ⟨π, α, hD⟩
    exact ⟨π, α, hD.eq_cartierOf⟩
  · rintro ⟨π, α, rfl⟩
    exact isCartier_cartierOf π α

/-- The root of `cartierOf π α` is the push-forward `π_* α` along `π : Y_π → X`. -/
theorem root_cartierOf (π : Modification n X) (α : RealBottChern n π.carrier) :
    (cartierOf hn π α).root = classPushforward π.contMDiff_map
      (CanonicalCurrentFrame.canonicalBasis n) hn α := by
  rw [root, cartierOf_onModel α (le_refl π) (Modification.root_le π),
    Modification.classPullbackOfLE_refl,
    Modification.classPushforwardOfLE_eq hn (Modification.root_le π) π.contMDiff_map rfl]
  rfl

/-- Realizations of a sum: `(π, α + β)` realizes `cartierOf π α + cartierOf π β`. -/
theorem cartierOf_add (π : Modification n X) (α β : RealBottChern n π.carrier) :
    cartierOf hn π (α + β) = cartierOf hn π α + cartierOf hn π β := by
  symm
  apply IsRealization.eq_cartierOf
  intro π' h
  change (cartierOf hn π α).onModel π' + (cartierOf hn π β).onModel π' = _
  rw [isRealization_cartierOf π α π' h, isRealization_cartierOf π β π' h, map_add]

theorem cartierOf_smul (π : Modification n X) (c : ℝ) (α : RealBottChern n π.carrier) :
    cartierOf hn π (c • α) = c • cartierOf hn π α := by
  symm
  apply IsRealization.eq_cartierOf
  intro π' h
  change c • (cartierOf hn π α).onModel π' = _
  rw [isRealization_cartierOf π α π' h, map_smul]

/-- The Cartier b-divisor realized on a dominating model by the pulled-back class is the same. -/
theorem cartierOf_pullback {π π' : Modification n X} (h : π ≤ π')
    (α : RealBottChern n π.carrier) :
    cartierOf hn π' (Modification.classPullbackOfLE h α) = cartierOf hn π α :=
  ((isRealization_cartierOf π α).pullback h).eq_cartierOf.symm

theorem IsCartier.add {D D' : WeilBDivisor n X hn} (hD : D.IsCartier) (hD' : D'.IsCartier) :
    (D + D').IsCartier := by
  obtain ⟨π, α, rfl⟩ := (isCartier_iff D).mp hD
  obtain ⟨π', α', rfl⟩ := (isCartier_iff D').mp hD'
  obtain ⟨ρ, h, h'⟩ := Modification.exists_le_le π π'
  rw [← cartierOf_pullback h α, ← cartierOf_pullback h' α', ← cartierOf_add]
  exact isCartier_cartierOf _ _

theorem IsCartier.smul {D : WeilBDivisor n X hn} (hD : D.IsCartier) (c : ℝ) :
    (c • D).IsCartier := by
  obtain ⟨π, α, rfl⟩ := (isCartier_iff D).mp hD
  rw [← cartierOf_smul]
  exact isCartier_cartierOf _ _

variable (n X hn) in
/-- Cartier b-divisors form a real subspace of the Weil b-divisors. -/
def cartierBDivisors : Submodule ℝ (WeilBDivisor n X hn) where
  carrier := {D | D.IsCartier}
  zero_mem' := isCartier_zero
  add_mem' := fun hD hD' => hD.add hD'
  smul_mem' := fun c _ hD => hD.smul c

/-- A class on a model that is nef with respect to some Kähler form defines a nef Cartier
b-divisor (`def:nefCar`). -/
theorem isNefCartier_cartierOf (π : Modification n X) (α : RealBottChern n π.carrier)
    (κ : KahlerBackground n π.carrier) (hα : ClassNefWithRespectTo κ α) :
    (cartierOf hn π α).IsNefCartier :=
  ⟨π, α, isRealization_cartierOf π α, κ, hα⟩

/-- `𝔻(ω)`: a Kähler form `ω` on `X` gives the nef Cartier b-divisor realized by `(X, {ω})`. -/
theorem isNefCartier_cartierOf_kahler (κ : KahlerBackground n X) :
    (cartierOf hn Modification.root (RealBottChern.ofRepresentative κ.form)).IsNefCartier :=
  isNefCartier_cartierOf (X := X) Modification.root _ κ
    (classNefWithRespectTo_of_semipositive κ κ.isSemipositive)

end WeilBDivisor

end SGPT.BDivisor
