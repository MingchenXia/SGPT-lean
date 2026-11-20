import SGPT.Okounkov.IntrinsicModificationRestriction
import SGPT.Foundations.Analysis.Pending.PrescribedBlowupDomination
import SGPT.Foundations.Analysis.Pending.LocusProperties

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov

open Set
open scoped Manifold ContDiff Topology
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy

/-- Composition preserves the literal original finite smooth-centre predicate. -/
theorem isBlowupSequence_comp
    {n : ℕ} {X Y Z : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]
    {f : Y → X} {g : Z → Y}
    (hf : IsBlowupSequence n X Y f) (hg : IsBlowupSequence n Y Z g) :
    IsBlowupSequence n X Z (f ∘ g) := by
  induction hg with
  | refl => exact hf
  | step g₀ C b _hg₀ hb ih =>
      exact IsBlowupSequence.step (f ∘ g₀) C b ih hb

/-- One original finite branch and one whole analytic modification internally
produce a compact common source and a whole commuting square. -/
theorem exists_commonModification_of_isBlowupSequence
    {n : ℕ} {X Y Z : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]
    [CompactSpace X]
    {π : Y → X} {c : Z → X}
    (hπ : IsBlowupSequence n X Y π) (hc : IsAnalyticModification (n := n) c) :
    ∃ (W : Type u) (_ : TopologicalSpace W) (_ : ChartedSpace (ComplexModel n) W)
      (_ : IsComplexManifold n W) (σ : W → Z) (ℓ : W → Y),
      CompactSpace W ∧ IsBlowupSequence n Z W σ ∧
      IsAnalyticModification (n := n) σ ∧ IsAnalyticModification (n := n) ℓ ∧
      π ∘ ℓ = c ∘ σ := by
  let := AnalyticModificationStrongPullback.compactSpace_of_isAnalyticModification hc
  induction hπ with
  | refl =>
      exact ⟨Z, inferInstance, inferInstance, inferInstance, id, c, inferInstance,
        IsBlowupSequence.refl, isAnalyticModification_of_isBlowupSequence IsBlowupSequence.refl,
        hc, rfl⟩
  | @step Y₀ Y _ _ _ _ _ _ π₀ C b hπ₀ hb ih =>
      obtain ⟨W₀, tW₀, aW₀, mW₀, σ₀, ℓ₀, compactW₀, hσ₀, hσ₀mod, hℓ₀, hsquare₀⟩ := ih
      let := tW₀
      let := aW₀
      let := mW₀
      let := compactW₀
      let := AnalyticModificationStrongPullback.compactSpace_of_isAnalyticModification
        (isAnalyticModification_of_isBlowupSequence hπ₀)
      obtain ⟨W, tW, aW, mW, τ, ℓ, _D, _E, hτ, hτmod, hℓ, hsquare, _hideal, _hSNC, _hsupp⟩ :=
        PrescribedBlowupDomination.exists_domination_of_isBlowupAlong hb hℓ₀
      let := tW
      let := aW
      let := mW
      have hσ : IsBlowupSequence n Z W (σ₀ ∘ τ) :=
        isBlowupSequence_comp hσ₀ hτ.isBlowupSequence
      have hσmod : IsAnalyticModification (n := n) (σ₀ ∘ τ) :=
        AnalyticModificationComposition.isAnalyticModification_comp hσ₀mod hτmod
      have hcompact : CompactSpace W :=
        AnalyticModificationStrongPullback.compactSpace_of_isAnalyticModification hσmod
      refine ⟨W, tW, aW, mW, σ₀ ∘ τ, ℓ, hcompact, hσ, hσmod, hℓ, ?_⟩
      funext w
      calc
        (π₀ ∘ b) (ℓ w) = π₀ (ℓ₀ (τ w)) :=
          congrArg π₀ (congrFun hsquare w)
        _ = (c ∘ (σ₀ ∘ τ)) w := congrFun hsquare₀ (τ w)

/-- A genuine Kähler background on the other source supplies a Kähler
background on the same common source via the produced original finite branch. -/
theorem exists_kahler_commonModification_of_isBlowupSequence
    {n : ℕ} {X Y Z : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]
    [CompactSpace X]
    {π : Y → X} {c : Z → X}
    (hπ : IsBlowupSequence n X Y π) (hc : IsAnalyticModification (n := n) c)
    (hZ : Nonempty (KahlerBackground n Z)) :
    ∃ (W : Type u) (_ : TopologicalSpace W) (_ : ChartedSpace (ComplexModel n) W)
      (_ : IsComplexManifold n W) (σ : W → Z) (ℓ : W → Y),
      CompactSpace W ∧ Nonempty (KahlerBackground n W) ∧ IsBlowupSequence n Z W σ ∧
      IsAnalyticModification (n := n) σ ∧ IsAnalyticModification (n := n) ℓ ∧
      π ∘ ℓ = c ∘ σ := by
  obtain ⟨W, tW, aW, mW, σ, ℓ, _hcompact, hσ, hσmod, hℓ, hsquare⟩ :=
    exists_commonModification_of_isBlowupSequence hπ hc
  let := tW
  let := aW
  let := mW
  let := AnalyticModificationStrongPullback.compactSpace_of_isAnalyticModification hc
  obtain ⟨hcompact, hKahler⟩ := LocusProperties.compactSpace_and_kahler_of_isBlowupSequence
    hZ σ hσ
  exact ⟨W, tW, aW, mW, σ, ℓ, hcompact, hKahler, hσ, hσmod, hℓ, hsquare⟩

end SGPT.Okounkov
