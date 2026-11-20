import SGPT.Projective.OriginalModificationPullbackValues

/-! Literal original pulled coefficient/valuation/body definitions for ALL dimensions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalModification.AllDimensions
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set
open SGPT.Okounkov SGPT.Okounkov.AlgebraicValuation SGPT.AlmostSemigroup SGPT.LineBundle
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves

section Definitions
variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)
local instance : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
variable {Z : Type} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]

/-- Actual original pullback coefficient membership, including dimension0 and original k=0. -/
def IsPullbackMultiplierSection (π : Z → SchemeComplexPoint f) (φ : SchemeComplexPoint f → EReal)
    {L : X.Modules} (k : ℕ) (s : bundlePowerGlobalSections L k) : Prop :=
  k = 0 ∨ ∀ (U : X.Opens) (α : LocalBundleFrame L U) (z : Z),
    schemeComplexPointImage f (π z) ∈ U →
      (multiplierIdeal (n := n) (k : ℝ) (fun w => φ (π w))).mem z
        (fun w => sectionFrameCoefficient f n E α k s (π w))

variable [IsIntegral X] {L : X.Modules} (a : LineBundleAtlas L)
  (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) (c : X)

/-- SAME arbitrary original valuation/centre/atlas on actual original pulled sections. -/
def pullbackValues (π : Z → SchemeComplexPoint f) (φ : SchemeComplexPoint f → EReal) :
    Set ((Fin n → ℤ) × ℤ) :=
  AlgebraicValuation.sectionValueSet v c a
    (fun k s => IsPullbackMultiplierSection f n E π φ k s)

/-- The actual original setBody of the genuine pulled original values, for ANY cone. -/
def pullbackBody (C : AdmissibleCone n) (π : Z → SchemeComplexPoint f)
    (φ : SchemeComplexPoint f → EReal) : Set (EuclideanSpace ℝ (Fin n)) :=
  ValGen.setBody C (pullbackValues f n E a v c π φ)
end Definitions

section Successor
variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) {m : ℕ}
  [SmoothOfRelativeDimension (m+1) f] (E : ClosedProjectiveEmbedding f)
local instance : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance : ChartedSpace (ComplexModel (m+1)) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f (m+1)
variable {Z : Type} [TopologicalSpace Z] [ChartedSpace (ComplexModel (m+1)) Z]
  [IsComplexManifold (m+1) Z] (π : Z → SchemeComplexPoint f) (φ : SchemeComplexPoint f → EReal)

omit [IsComplexManifold (m+1) Z]

/-- Literal original positive-dimensional coefficient membership readback. -/
theorem isPullbackMultiplierSection_succ {L : X.Modules} (k : ℕ)
    (s : bundlePowerGlobalSections L k) :
    IsPullbackMultiplierSection f (m+1) E π φ k s ↔
      OkoTower.IsPullbackMultiplierSection f E m π φ k s := Iff.rfl

variable [IsIntegral X] {L : X.Modules} (a : LineBundleAtlas L)
  (v : AddValuation X.functionField (WithTop (Lex (Fin (m+1) → ℤ)))) (c : X)

/-- Literal SAME arbitrary original valuation value set in successor dimension. -/
theorem pullbackValues_succ : pullbackValues f (m+1) E a v c π φ =
    SGPT.Okounkov.OriginalModification.pullbackValues f E a v c π φ := rfl

/-- Literal original setBody in successor dimension, including its original domain convention. -/
theorem pullbackBody_succ (C : AdmissibleCone (m+1)) :
    pullbackBody f (m+1) E a v c C π φ =
      SGPT.Okounkov.OriginalModification.pullbackBody f E a v c C π φ := rfl
end Successor
end SGPT.Okounkov.OriginalModification.AllDimensions
