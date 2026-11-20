import SGPT.Okounkov.OF2ValCurrRefinement

/-!
# `rmk:valcurr`: independence through a common model with a common lifted flag

Source: chapter *The theory of Okounkov bodies*, `rmk:valcurr`: for a surjective rank `n`
valuation `ν` of `ℂ(X)` and a presentation `ν = ν_{Y•} g` on a resolution `π : Y → X`,
`ν(T) := ν_{Y•}(π^*T) g`; *"this definition does not depend on the choice of `π`, by passing to a
common resolution and applying `prop:cormatrix` and `prop:cormult`."*

This file formalizes that argument for presentations on analytic modifications of the integral
smooth projective complex scheme `X` (`OF2.modificationPresentationValue`): if the two models
`π₁ : X₁ → X(ℂ)`, `π₂ : X₂ → X(ℂ)` are dominated by a common model `Z` (`π₁ p₁ = π₂ p₂`) on
which the two flags have liftings to the **same** smooth flag `W•`, then the two presentations give
the same value `ν(T)` (`modificationPresentationValue_eq_of_common_lifting`).

The proof: on `ρ = π₁ p₁ = π₂ p₂` both presentations become presentations
`ν = (ν_{W•} ∘ ρ^*) (cor(Fᵢ, pᵢ)⁻¹ Gᵢ)` with the same values (refinement invariance,
`OF2.modificationPresentationValue_lifting`, i.e. the algebraic and current `prop:cormatrix` and
`prop:cormult`); the matrix of a presentation of a surjective valuation by a given flag is unique
(`OF2.matrix_eq_of_lexMapValuation_eq`).

What the book uses implicitly and is **not** proved here: that the two lifted flags on a common
model coincide, i.e. that a smooth flag on an analytic modification of `X(ℂ)` is determined by the
equivalence class of the valuation it induces on `ℂ(X)` (proved only on `X` itself,
`SGPT.Okounkov.schemeOriginalFlags_eq_of_lexEquivalent`; on a modification it needs `ℂ(X)` to
separate the points of the model, i.e. the algebraicity of the model).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Okounkov.OF4

open CategoryTheory AlgebraicGeometry Set Filter SGPT.Foundations.Schemes
open SGPT.Okounkov SGPT.Okounkov.AlgebraicValuation SGPT.Okounkov.ValCurr SGPT.Okounkov.OF2
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open GlobalCurrents CanonicalCurrentFrame GlobalPositiveCurrentACRestriction
open NaturalThetaPshGeometricCurrent NaturalThetaPshClosedCurrent
open scoped Matrix

/-- If `ν G` is surjective, so is `ν`. -/
theorem surjective_of_lexMapValuation_surjective {R : Type*} [Ring R] {n : ℕ}
    {v : AddValuation R (WithTop (Lex (Fin n → ℤ)))} {G : Matrix (Fin n) (Fin n) ℤ}
    (hG : IsUnitUpperTriangular G) (h : Function.Surjective (lexMapValuation G hG v)) :
    Function.Surjective v := by
  have hv : lexMapValuation G⁻¹ hG.inv (lexMapValuation G hG v) = v := by
    apply AddValuation.ext
    intro r
    rw [lexMapValuation_apply, lexMapValuation_apply, lexWithTopHom_mul,
      lexWithTopHom_congr hG.mul_inv _ (IsUnitUpperTriangular.one), lexWithTopHom_one]
  rw [← hv]
  exact OF2.lexMapValuation_surjective G⁻¹ hG.inv h

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) {m : ℕ}
  [SmoothOfRelativeDimension (m + 1) f] [IsSeparated f] [QuasiCompact f]

local instance of4ComTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance of4ComCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance of4ComManifold : IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

/-- The induced valuation only depends on the map `ρ`. -/
theorem modificationFlagValuation_congr_map (W : OriginalFlagGeometry.{0} (m + 1))
    {ρ ρ' : W.carrier → SchemeComplexPoint f} (h : ρ = ρ')
    (hρ : IsAnalyticModification (n := m + 1) ρ) (hρ' : IsAnalyticModification (n := m + 1) ρ') :
    modificationFlagValuation f W hρ = modificationFlagValuation f W hρ' := by
  subst h
  rfl

omit [IsIntegral X] in
/-- The value of a presentation only depends on the map `ρ`. -/
theorem modificationPresentationValue_congr_map (W : OriginalFlagGeometry.{0} (m + 1))
    {ρ ρ' : W.carrier → SchemeComplexPoint f} (h : ρ = ρ')
    (hρ : IsAnalyticModification (n := m + 1) ρ) (hρ' : IsAnalyticModification (n := m + 1) ρ')
    (G : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ)
    (θ : ClosedRealOneOneForm (m + 1) (SchemeComplexPoint f)) (u : SchemeComplexPoint f → EReal)
    (hu : IsThetaPshPotential θ.val u) :
    modificationPresentationValue f W hρ G θ u hu =
      modificationPresentationValue f W hρ' G θ u hu := by
  subst h
  rfl

/-- **`rmk:valcurr`: independence through a common model.** Let `ν` be a surjective valuation of
`ℂ(X)` with presentations `ν = (ν_{F₁} ∘ π₁^*) G₁ = (ν_{F₂} ∘ π₂^*) G₂` on two analytic
modifications. If `pᵢ : Z → Xᵢ` lift `Fᵢ` to the same flag `W•` on a common model with
`π₁ p₁ = π₂ p₂`, then the two presentations give the same value `ν(T)` for every closed positive
`(1,1)`-current `T = θ + dd^c u` on `X(ℂ)`. -/
theorem modificationPresentationValue_eq_of_common_lifting
    {F₁ F₂ W : OriginalFlagGeometry.{0} (m + 1)}
    {π₁ : F₁.carrier → SchemeComplexPoint f} (hπ₁ : IsAnalyticModification (n := m + 1) π₁)
    {π₂ : F₂.carrier → SchemeComplexPoint f} (hπ₂ : IsAnalyticModification (n := m + 1) π₂)
    {p₁ : W.carrier → F₁.carrier} (hp₁ : IsFlagLifting F₁ W p₁)
    {p₂ : W.carrier → F₂.carrier} (hp₂ : IsFlagLifting F₂ W p₂)
    (hcomm : π₁ ∘ p₁ = π₂ ∘ p₂)
    (v : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ))))
    (hv : Function.Surjective v)
    {G₁ G₂ : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ} (hG₁ : IsUnitUpperTriangular G₁)
    (hG₂ : IsUnitUpperTriangular G₂)
    (h₁ : v = lexMapValuation G₁ hG₁ (modificationFlagValuation f F₁ hπ₁))
    (h₂ : v = lexMapValuation G₂ hG₂ (modificationFlagValuation f F₂ hπ₂))
    (θ : ClosedRealOneOneForm (m + 1) (SchemeComplexPoint f)) (u : SchemeComplexPoint f → EReal)
    (hu : IsThetaPshPotential θ.val u) :
    modificationPresentationValue f F₁ hπ₁ G₁ θ u hu =
      modificationPresentationValue f F₂ hπ₂ G₂ θ u hu := by
  obtain ⟨hv₁, hval₁⟩ := modificationPresentationValue_lifting f hπ₁ hp₁ v hG₁ h₁ θ u hu
  obtain ⟨hv₂, hval₂⟩ := modificationPresentationValue_lifting f hπ₂ hp₂ v hG₂ h₂ θ u hu
  have hρ₁ := AnalyticModificationComposition.isAnalyticModification_comp hπ₁ hp₁.1
  have hρ₂ := AnalyticModificationComposition.isAnalyticModification_comp hπ₂ hp₂.1
  rw [modificationFlagValuation_congr_map f W hcomm.symm hρ₂ hρ₁] at hv₂
  have hsurj : Function.Surjective (modificationFlagValuation f W hρ₁) :=
    surjective_of_lexMapValuation_surjective _ (hv₁ ▸ hv)
  have hM := OF2.matrix_eq_of_lexMapValuation_eq hsurj _ _ (hv₁.symm.trans hv₂)
  rw [← hval₁, ← hval₂, modificationPresentationValue_congr_map f W hcomm.symm hρ₂ hρ₁, hM]

end SGPT.Okounkov.OF4
