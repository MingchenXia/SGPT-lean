import SGPT.BDivisor.BlowupModelSystem
import SGPT.BDivisor.CartierBDivisor

/-!
# Weil and Cartier b-divisors over a model system; the book's b-divisors

Source: `chap:bdiv`, `def:bdiv:L38` (Weil b-divisors, order, pseudo-effectivity, root),
`def:bdiv:L116` (Cartier b-divisors and realizations) and `def:nefCar` (nef Cartier b-divisors).

For a model system `S` of the compact manifold `X` (`SGPT.BDivisor.ModelSystem`), a **Weil
b-divisor over `S`** is a family `(𝔻_π)_{π ∈ S}` of classes `𝔻_π ∈ H^{1,1}(Y_π, ℝ)` compatible
under push-forward along dominations (`SGPT.BDivisor.Modification.classPushforwardOfLE`, the class
push-forward induced by the push-forward of currents). With `S = ModelSystem.blowup n X` — the
finite compositions of blow-ups with smooth centres of `def:modif` — these are the book's
b-divisors: `SGPT.BDivisor.BlowupWeilBDivisor n X hn`.

Everything in this file uses only the directed preorder of the models, so it is stated for an
arbitrary model system; the instance relevant for the book is `ModelSystem.blowup`, whose
directedness is TN's `exists_common_isBlowupSequence` (no Chow lemma, no connectedness).

Main declarations (namespace `SGPT.BDivisor.WeilBDivisorOn`):

* `weilBDivisorsOn S hn`, `WeilBDivisorOn S hn` — the real vector space of Weil b-divisors;
* `onModel`, `pushforward_onModel`, `root`, `LE`, `IsPseudoeffective`;
* `IsRealization`, `IsCartier`, and `cartierOf π α`: **every** pair `(π, α)` with `π ∈ S` is the
  realization of a unique Cartier b-divisor (`isRealization_cartierOf`,
  `IsRealization.eq_cartierOf`), because `g_* g^* = id` on `(1,1)`-classes along modifications
  (`Modification.classPushforwardOfLE_classPullbackOfLE`);
* `IsNefCartier` (`def:nefCar`) and, on the book's models of a compact Kähler `X` (which are all
  Kähler), `isNefCartier_blowup_iff`: nefness of the realizing class does not depend on the
  Kähler form, and every blow-up model carries one.
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

namespace ModelSystem

variable {S : ModelSystem n X} (hn : 0 < n)

/-- `g_* g^* = id` along a domination of models of a system. -/
theorem Model.classPushforwardOfLE_classPullbackOfLE {π π' : S.Model} (h : π ≤ π')
    (α : RealBottChern n π.1.carrier) :
    Modification.classPushforwardOfLE hn h (Modification.classPullbackOfLE h α) = α :=
  Modification.classPushforwardOfLE_classPullbackOfLE hn h α

/-- Push–pull through a common model does not depend on the common model. -/
theorem Model.pushPull_eq {π π' ρ₁ ρ₂ : S.Model} (h₁ : π ≤ ρ₁) (h₁' : π' ≤ ρ₁)
    (h₂ : π ≤ ρ₂) (h₂' : π' ≤ ρ₂) (α : RealBottChern n π.1.carrier) :
    Modification.classPushforwardOfLE hn (show π'.1 ≤ ρ₁.1 from h₁')
        (Modification.classPullbackOfLE (show π.1 ≤ ρ₁.1 from h₁) α) =
      Modification.classPushforwardOfLE hn (show π'.1 ≤ ρ₂.1 from h₂')
        (Modification.classPullbackOfLE (show π.1 ≤ ρ₂.1 from h₂) α) := by
  obtain ⟨ρ, hρ₁, hρ₂⟩ := Model.exists_le_le ρ₁ ρ₂
  rw [← Modification.pushPull_trans hn h₁ h₁' hρ₁, ← Modification.pushPull_trans hn h₂ h₂' hρ₂]

/-- The class on `π'` of the Cartier b-divisor realized by `(π, α)`: `(ρ → π')_* (ρ → π)^* α` for a
model `ρ ∈ S` dominating both. -/
def Model.cartierClass (π : S.Model) (α : RealBottChern n π.1.carrier) (π' : S.Model) :
    RealBottChern n π'.1.carrier :=
  Modification.classPushforwardOfLE hn (Model.exists_le_le π π').choose_spec.2
    (Modification.classPullbackOfLE (Model.exists_le_le π π').choose_spec.1 α)

theorem Model.cartierClass_eq {π π' ρ : S.Model} (h : π ≤ ρ) (h' : π' ≤ ρ)
    (α : RealBottChern n π.1.carrier) :
    Model.cartierClass hn π α π' =
      Modification.classPushforwardOfLE hn (show π'.1 ≤ ρ.1 from h')
        (Modification.classPullbackOfLE (show π.1 ≤ ρ.1 from h) α) :=
  Model.pushPull_eq hn (Model.exists_le_le π π').choose_spec.1
    (Model.exists_le_le π π').choose_spec.2 h h' α

end ModelSystem

/-- The compatible families of classes over the models of a system `S`, as a real subspace of the
product of the `H^{1,1}(Y_π, ℝ)`, `π ∈ S`. -/
def weilBDivisorsOn (S : ModelSystem n X) (hn : 0 < n) :
    Submodule ℝ ((π : S.Model) → RealBottChern n π.1.carrier) where
  carrier := {D | ∀ (π π' : S.Model) (h : π ≤ π'),
    Modification.classPushforwardOfLE hn (show π.1 ≤ π'.1 from h) (D π') = D π}
  zero_mem' := by
    intro π π' h
    exact map_zero _
  add_mem' := by
    intro D D' hD hD' π π' h
    change Modification.classPushforwardOfLE hn (show π.1 ≤ π'.1 from h) (D π' + D' π') =
      D π + D' π
    rw [map_add, hD π π' h, hD' π π' h]
  smul_mem' := by
    intro c D hD π π' h
    change Modification.classPushforwardOfLE hn (show π.1 ≤ π'.1 from h) (c • D π') = c • D π
    rw [map_smul, hD π π' h]

/-- **Weil b-divisors over a model system `S`** (`def:bdiv:L38` with index set `S`): families
`(𝔻_π)_{π ∈ S}` of classes `𝔻_π ∈ H^{1,1}(Y_π, ℝ)` with `g_* 𝔻_{π'} = 𝔻_π` whenever `π'`
dominates `π` through `g`. They form a real vector space. -/
abbrev WeilBDivisorOn (S : ModelSystem n X) (hn : 0 < n) := ↥(weilBDivisorsOn S hn)

variable (n X) in
/-- **The book's (Weil) b-divisors** (`def:bdiv:L38`): Weil b-divisors over the finite
compositions of blow-ups with smooth centres of `X` (`def:modif`). -/
abbrev BlowupWeilBDivisor (hn : 0 < n) := WeilBDivisorOn (ModelSystem.blowup n X) hn

namespace WeilBDivisorOn

variable {S : ModelSystem n X} {hn : 0 < n}

/-- The class of a b-divisor on a model. -/
def onModel (D : WeilBDivisorOn S hn) (π : S.Model) : RealBottChern n π.1.carrier :=
  D.val π

@[ext] theorem ext {D D' : WeilBDivisorOn S hn} (h : ∀ π, D.onModel π = D'.onModel π) :
    D = D' :=
  Subtype.ext (funext h)

@[simp] theorem add_onModel (D D' : WeilBDivisorOn S hn) (π : S.Model) :
    (D + D').onModel π = D.onModel π + D'.onModel π := rfl

@[simp] theorem smul_onModel (c : ℝ) (D : WeilBDivisorOn S hn) (π : S.Model) :
    (c • D).onModel π = c • D.onModel π := rfl

@[simp] theorem sub_onModel (D D' : WeilBDivisorOn S hn) (π : S.Model) :
    (D - D').onModel π = D.onModel π - D'.onModel π := rfl

@[simp] theorem zero_onModel (π : S.Model) : (0 : WeilBDivisorOn S hn).onModel π = 0 := rfl

/-- The compatibility under push-forward. -/
theorem pushforward_onModel (D : WeilBDivisorOn S hn) {π π' : S.Model} (h : π ≤ π') :
    Modification.classPushforwardOfLE hn (show π.1 ≤ π'.1 from h) (D.onModel π') =
      D.onModel π :=
  D.property π π' h

/-- The **root** `𝔻_X` of a b-divisor. -/
def root (D : WeilBDivisorOn S hn) : RealBottChern n X :=
  D.onModel ModelSystem.Model.root

/-- `𝔻 ≤ 𝔻'` (`def:bdiv:L38`): `𝔻'_π - 𝔻_π` is pseudo-effective on every model. -/
def LE (D D' : WeilBDivisorOn S hn) : Prop :=
  ∀ π : S.Model, ClassPseudoeffectiveViaPotentials (D'.onModel π - D.onModel π)

/-- A b-divisor is **pseudo-effective** if `𝔻 ≥ 0`. -/
def IsPseudoeffective (D : WeilBDivisorOn S hn) : Prop := LE 0 D

theorem isPseudoeffective_iff (D : WeilBDivisorOn S hn) :
    D.IsPseudoeffective ↔ ∀ π, ClassPseudoeffectiveViaPotentials (D.onModel π) := by
  unfold IsPseudoeffective LE
  refine forall_congr' fun π => ?_
  rw [zero_onModel, sub_zero]

theorem le_iff_isPseudoeffective_sub (D D' : WeilBDivisorOn S hn) :
    D.LE D' ↔ (D' - D).IsPseudoeffective := by
  rw [isPseudoeffective_iff]
  rfl

/-- `(π, α)` is a **realization** of `𝔻` (`def:bdiv:L116`): for every model `π'` dominating `π`,
`𝔻_{π'}` is the pull-back of `α`. -/
def IsRealization (D : WeilBDivisorOn S hn) (π : S.Model) (α : RealBottChern n π.1.carrier) :
    Prop :=
  ∀ (π' : S.Model) (h : π ≤ π'),
    D.onModel π' = Modification.classPullbackOfLE (show π.1 ≤ π'.1 from h) α

/-- A **Cartier b-divisor** (`def:bdiv:L116`): a Weil b-divisor admitting a realization. -/
def IsCartier (D : WeilBDivisorOn S hn) : Prop :=
  ∃ (π : S.Model) (α : RealBottChern n π.1.carrier), D.IsRealization π α

theorem IsRealization.onModel_eq {D : WeilBDivisorOn S hn} {π : S.Model}
    {α : RealBottChern n π.1.carrier} (h : D.IsRealization π α) : D.onModel π = α := by
  rw [h π (le_refl π)]
  exact Modification.classPullbackOfLE_refl π.1 α

/-- Realizations move to dominating models (realizations are not unique). -/
theorem IsRealization.pullback {D : WeilBDivisorOn S hn} {π : S.Model}
    {α : RealBottChern n π.1.carrier} (h : D.IsRealization π α) {π' : S.Model} (hle : π ≤ π') :
    D.IsRealization π' (Modification.classPullbackOfLE (show π.1 ≤ π'.1 from hle) α) := by
  intro π'' h'
  rw [h π'' (hle.trans h')]
  exact Modification.classPullbackOfLE_trans (show π.1 ≤ π'.1 from hle)
    (show π'.1 ≤ π''.1 from h') α

/-- A **nef Cartier b-divisor** (`def:nefCar`): a Cartier b-divisor with a realization `(π, α)`
such that `α` is nef (with respect to a Kähler form on `Y_π`). -/
def IsNefCartier (D : WeilBDivisorOn S hn) : Prop :=
  ∃ (π : S.Model) (α : RealBottChern n π.1.carrier), D.IsRealization π α ∧
    ∃ κ : KahlerBackground n π.1.carrier, ClassNefWithRespectTo κ α

theorem IsNefCartier.isCartier {D : WeilBDivisorOn S hn} (h : D.IsNefCartier) : D.IsCartier :=
  let ⟨π, α, hr, _⟩ := h
  ⟨π, α, hr⟩

variable (hn) in
/-- **The Cartier b-divisor realized by `(π, α)`** (`def:bdiv:L116`): its class on a model `π'` is
`(ρ → π')_* (ρ → π)^* α` for any model `ρ ∈ S` dominating `π` and `π'`. -/
def cartierOf (π : S.Model) (α : RealBottChern n π.1.carrier) : WeilBDivisorOn S hn :=
  ⟨fun π' => ModelSystem.Model.cartierClass hn π α π', by
    intro π₁ π₂ h
    obtain ⟨ρ, hρ, hρ₂⟩ := ModelSystem.Model.exists_le_le π π₂
    change Modification.classPushforwardOfLE hn (show π₁.1 ≤ π₂.1 from h)
        (ModelSystem.Model.cartierClass hn π α π₂) = ModelSystem.Model.cartierClass hn π α π₁
    rw [ModelSystem.Model.cartierClass_eq hn hρ hρ₂,
      ModelSystem.Model.cartierClass_eq hn hρ (h.trans hρ₂),
      Modification.classPushforwardOfLE_trans hn (show π₁.1 ≤ π₂.1 from h)
        (show π₂.1 ≤ ρ.1 from hρ₂)]⟩

theorem cartierOf_onModel {π π' ρ : S.Model} (α : RealBottChern n π.1.carrier)
    (h : π ≤ ρ) (h' : π' ≤ ρ) :
    (cartierOf hn π α).onModel π' =
      Modification.classPushforwardOfLE hn (show π'.1 ≤ ρ.1 from h')
        (Modification.classPullbackOfLE (show π.1 ≤ ρ.1 from h) α) :=
  ModelSystem.Model.cartierClass_eq hn h h' α

/-- `(π, α)` is a realization of `cartierOf π α`. -/
theorem isRealization_cartierOf (π : S.Model) (α : RealBottChern n π.1.carrier) :
    (cartierOf hn π α).IsRealization π α := by
  intro π' h
  rw [cartierOf_onModel α h (le_refl π')]
  exact Modification.classPushforwardOfLE_refl hn π'.1 _

/-- **Every pair `(π, α)` defines a Cartier b-divisor.** -/
theorem isCartier_cartierOf (π : S.Model) (α : RealBottChern n π.1.carrier) :
    (cartierOf hn π α).IsCartier :=
  ⟨π, α, isRealization_cartierOf π α⟩

/-- **Uniqueness**: a b-divisor with realization `(π, α)` is `cartierOf π α`. -/
theorem IsRealization.eq_cartierOf {D : WeilBDivisorOn S hn} {π : S.Model}
    {α : RealBottChern n π.1.carrier} (hD : D.IsRealization π α) : D = cartierOf hn π α := by
  ext π'
  obtain ⟨ρ, hρ, hρ'⟩ := ModelSystem.Model.exists_le_le π π'
  rw [cartierOf_onModel α hρ hρ', ← hD ρ hρ, D.pushforward_onModel hρ']

theorem isCartier_iff (D : WeilBDivisorOn S hn) :
    D.IsCartier ↔ ∃ (π : S.Model) (α : RealBottChern n π.1.carrier), D = cartierOf hn π α := by
  constructor
  · rintro ⟨π, α, hD⟩
    exact ⟨π, α, hD.eq_cartierOf⟩
  · rintro ⟨π, α, rfl⟩
    exact isCartier_cartierOf π α

/-- The root of `cartierOf π α` is `π_* α`. -/
theorem root_cartierOf (π : S.Model) (α : RealBottChern n π.1.carrier) :
    (cartierOf hn π α).root =
      classPushforward π.1.contMDiff_map (CanonicalCurrentFrame.canonicalBasis n) hn α := by
  rw [root, cartierOf_onModel α (le_refl π) (ModelSystem.Model.root_le π),
    Modification.classPullbackOfLE_refl]
  exact Modification.classPushforwardOfLE_eq hn (Modification.root_le π.1) π.1.contMDiff_map rfl α

theorem cartierOf_add (π : S.Model) (α β : RealBottChern n π.1.carrier) :
    cartierOf hn π (α + β) = cartierOf hn π α + cartierOf hn π β := by
  symm
  apply IsRealization.eq_cartierOf
  intro π' h
  rw [add_onModel, isRealization_cartierOf π α π' h, isRealization_cartierOf π β π' h, map_add]

theorem cartierOf_smul (π : S.Model) (c : ℝ) (α : RealBottChern n π.1.carrier) :
    cartierOf hn π (c • α) = c • cartierOf hn π α := by
  symm
  apply IsRealization.eq_cartierOf
  intro π' h
  rw [smul_onModel, isRealization_cartierOf π α π' h, map_smul]

/-- The Cartier b-divisor realized on a dominating model by the pulled-back class is the same. -/
theorem cartierOf_pullback {π π' : S.Model} (h : π ≤ π') (α : RealBottChern n π.1.carrier) :
    cartierOf hn π' (Modification.classPullbackOfLE (show π.1 ≤ π'.1 from h) α) =
      cartierOf hn π α :=
  ((isRealization_cartierOf π α).pullback h).eq_cartierOf.symm

/-- The zero b-divisor is Cartier. -/
theorem isCartier_zero : (0 : WeilBDivisorOn S hn).IsCartier :=
  ⟨ModelSystem.Model.root, 0, fun _ h => (map_zero (Modification.classPullbackOfLE
    (show (ModelSystem.Model.root : S.Model).1 ≤ _ from h))).symm⟩

theorem IsCartier.add {D D' : WeilBDivisorOn S hn} (hD : D.IsCartier) (hD' : D'.IsCartier) :
    (D + D').IsCartier := by
  obtain ⟨π, α, rfl⟩ := (isCartier_iff D).mp hD
  obtain ⟨π', α', rfl⟩ := (isCartier_iff D').mp hD'
  obtain ⟨ρ, h, h'⟩ := ModelSystem.Model.exists_le_le π π'
  rw [← cartierOf_pullback h α, ← cartierOf_pullback h' α', ← cartierOf_add]
  exact isCartier_cartierOf _ _

theorem IsCartier.smul {D : WeilBDivisorOn S hn} (hD : D.IsCartier) (c : ℝ) :
    (c • D).IsCartier := by
  obtain ⟨π, α, rfl⟩ := (isCartier_iff D).mp hD
  rw [← cartierOf_smul]
  exact isCartier_cartierOf _ _

variable (S hn) in
/-- Cartier b-divisors form a real subspace. -/
def cartierBDivisors : Submodule ℝ (WeilBDivisorOn S hn) where
  carrier := {D | D.IsCartier}
  zero_mem' := isCartier_zero
  add_mem' := fun hD hD' => hD.add hD'
  smul_mem' := fun c _ hD => hD.smul c

/-- A class on a model that is nef with respect to some Kähler form defines a nef Cartier
b-divisor. -/
theorem isNefCartier_cartierOf (π : S.Model) (α : RealBottChern n π.1.carrier)
    (κ : KahlerBackground n π.1.carrier) (hα : ClassNefWithRespectTo κ α) :
    (cartierOf hn π α).IsNefCartier :=
  ⟨π, α, isRealization_cartierOf π α, κ, hα⟩

/-- `𝔻(ω)`: a Kähler form `ω` on `X` gives the nef Cartier b-divisor realized by `(X, {ω})`. -/
theorem isNefCartier_cartierOf_kahler (κ : KahlerBackground n X) :
    (cartierOf hn ModelSystem.Model.root
      (S := S) (RealBottChern.ofRepresentative κ.form)).IsNefCartier :=
  isNefCartier_cartierOf (S := S) ModelSystem.Model.root _ κ
    (classNefWithRespectTo_of_semipositive κ κ.isSemipositive)

/-- **Nef Cartier b-divisors over the book's models** (`def:nefCar`). For `X` compact Kähler,
every blow-up model carries a Kähler form, and nefness of a class on it does not depend on the
Kähler form; so a Cartier b-divisor is nef iff it has a realization `(π, α)` with `α` nef with
respect to **every** Kähler form of `Y_π`, and such a realization exists with a Kähler form. -/
theorem isNefCartier_blowup_iff (hK : Nonempty (KahlerBackground n X))
    (D : BlowupWeilBDivisor n X hn) :
    D.IsNefCartier ↔ ∃ (π : (ModelSystem.blowup n X).Model) (α : RealBottChern n π.1.carrier),
      D.IsRealization π α ∧ ∀ κ : KahlerBackground n π.1.carrier, ClassNefWithRespectTo κ α := by
  constructor
  · rintro ⟨π, α, hr, κ, hα⟩
    exact ⟨π, α, hr, fun κ' => (classNefWithRespectTo_iff κ κ' α).mp hα⟩
  · rintro ⟨π, α, hr, hα⟩
    obtain ⟨κ⟩ := ModelSystem.blowup_nonempty_kahlerBackground hK π
    exact ⟨π, α, hr, κ, hα κ⟩

end WeilBDivisorOn

end SGPT.BDivisor
