import SGPT.BDivisor.CartierBDivisor
import SGPT.Foundations.Analysis.Pending.PositiveCurrentPrescribedBottChernRepresentation
import SGPT.Foundations.Analysis.Pending.ThetaPotentialCurrentBottChernClass

/-!
# Pseudo-effectivity under push-forward, and pseudo-effective Cartier b-divisors

For a holomorphic map `g : Z → Y` of compact complex manifolds of dimension `n > 0`, the
push-forward of a pseudo-effective class is pseudo-effective: if `S = θ + ddᶜφ ≥ 0` lies in `β`,
then `g_* S` is a closed positive `(1,1)`-current in `g_* β` (`SGPT.BDivisor.currentPushforward`
preserves closedness, type and positivity, and `{g_* S} = g_*{S}`), and every closed positive
current in a class `{θ'}` is `θ' + ddᶜψ` for a `θ'`-psh potential `ψ`
(`PositiveCurrentPrescribedBottChernRepresentation.exists_theta_representation_of_class_eq`).

Consequences for b-divisors (`def:bdiv:L38`): a Weil b-divisor is pseudo-effective as soon as its
classes on all models dominating one model are; the Cartier b-divisor realized by `(π, α)` is
pseudo-effective iff `α` is; and `𝔻 ≤ 𝔻'` iff `𝔻' - 𝔻` is pseudo-effective.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.BDivisor

open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame
  SGPT.Foundations.Analysis.Pending.CurrentBottChernClass

section Pushforward

variable {m : ℕ} {Z Y : Type*} [TopologicalSpace Z] [ChartedSpace (ComplexModel (m + 1)) Z]
  [IsComplexManifold (m + 1) Z] [CompactSpace Z] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y] [CompactSpace Y]

/-- **The push-forward of a pseudo-effective class is pseudo-effective**, along any holomorphic
map of compact complex manifolds. -/
theorem classPseudoeffective_classPushforward {g : Z → Y}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ g)
    (hn : 0 < m + 1) {β : RealBottChern (m + 1) Z} (hβ : ClassPseudoeffectiveViaPotentials β) :
    ClassPseudoeffectiveViaPotentials (classPushforward hg (canonicalBasis (m + 1)) hn β) := by
  induction β using Quotient.inductionOn with
  | h θ =>
    obtain ⟨u, hu⟩ := hβ
    let S := ThetaPotentialCurrentBottChernClass.thetaClosedCurrent θ u hu
    have hS : bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) S =
        RealBottChern.ofRepresentative θ :=
      ThetaPotentialCurrentBottChernClass.bottChernClass_thetaClosedCurrent θ u hu
    let c := classPushforward hg (canonicalBasis (m + 1)) hn (RealBottChern.ofRepresentative θ)
    obtain ⟨θ', hθ'⟩ : ∃ θ' : ClosedRealOneOneForm (m + 1) Y,
        RealBottChern.ofRepresentative θ' = c := ⟨Quotient.out c, Quotient.out_eq c⟩
    have hpush : bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m)
        (closedCurrentPushforward hg (canonicalBasis (m + 1)) (Nat.succ_pos m) S) =
        RealBottChern.ofRepresentative θ' := by
      rw [hθ', bottChernClass_closedCurrentPushforward, hS]
    have hpos : GlobalPositiveCurrentACRestriction.IsFullPositive
        (closedCurrentPushforward hg (canonicalBasis (m + 1)) (Nat.succ_pos m) S).val :=
      isFullPositive_currentPushforward hg fun e α hα =>
        NaturalThetaPshGeometricCurrent.thetaPotentialCurrent_full_positive θ.val u hu e α hα
    obtain ⟨u', hu', -⟩ :=
      PositiveCurrentPrescribedBottChernRepresentation.exists_theta_representation_of_class_eq
        (closedCurrentPushforward hg (canonicalBasis (m + 1)) (Nat.succ_pos m) S) θ' hpos hpush
    change ClassPseudoeffectiveViaPotentials c
    rw [← hθ']
    exact ⟨u', hu'⟩

end Pushforward

namespace WeilBDivisor

variable {m : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X] [CompactSpace X] [ConnectedSpace X] {hn : 0 < m + 1}

/-- A Weil b-divisor is pseudo-effective as soon as its classes on all models dominating a fixed
model `π₀` are pseudo-effective. -/
theorem isPseudoeffective_of_forall_ge (𝔻 : WeilBDivisor (m + 1) X hn)
    (π₀ : Modification (m + 1) X)
    (h : ∀ π, π₀ ≤ π → ClassPseudoeffectiveViaPotentials (𝔻.onModel π)) :
    𝔻.IsPseudoeffective := by
  rw [isPseudoeffective_iff]
  intro π
  obtain ⟨ρ, h₀, h₁⟩ := Modification.exists_le_le π₀ π
  rw [← 𝔻.pushforward_onModel h₁]
  exact classPseudoeffective_classPushforward _ hn (h ρ h₀)

/-- The Cartier b-divisor realized by `(π, α)` is pseudo-effective iff `α` is. -/
theorem isPseudoeffective_cartierOf_iff (π : Modification (m + 1) X)
    (α : RealBottChern (m + 1) π.carrier) :
    (cartierOf hn π α).IsPseudoeffective ↔ ClassPseudoeffectiveViaPotentials α := by
  constructor
  · intro h
    have h' := (isPseudoeffective_iff _).mp h π
    rwa [(isRealization_cartierOf π α).onModel_eq] at h'
  · intro hα
    apply isPseudoeffective_of_forall_ge _ π
    intro π' h
    rw [isRealization_cartierOf π α π' h]
    exact classPseudoeffective_classPullback (Modification.Dominates.isAnalyticModification h) hα

omit [ConnectedSpace X] in
/-- `𝔻 ≤ 𝔻'` iff `𝔻' - 𝔻` is pseudo-effective (`def:bdiv:L38`). -/
theorem le_iff_isPseudoeffective_sub (𝔻 𝔻' : WeilBDivisor (m + 1) X hn) :
    𝔻.LE 𝔻' ↔ (𝔻' - 𝔻).IsPseudoeffective := by
  rw [isPseudoeffective_iff]
  rfl

/-- Comparison of Cartier b-divisors realized on the same model. -/
theorem cartierOf_le_cartierOf_iff (π : Modification (m + 1) X)
    (α β : RealBottChern (m + 1) π.carrier) :
    (cartierOf hn π α).LE (cartierOf hn π β) ↔ ClassPseudoeffectiveViaPotentials (β - α) := by
  rw [le_iff_isPseudoeffective_sub, sub_eq_add_neg, ← neg_one_smul ℝ (cartierOf hn π α),
    ← cartierOf_smul, ← cartierOf_add, isPseudoeffective_cartierOf_iff, neg_one_smul,
    ← sub_eq_add_neg]

end WeilBDivisor

end SGPT.BDivisor
