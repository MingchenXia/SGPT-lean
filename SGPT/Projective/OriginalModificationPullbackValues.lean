import SGPT.Okounkov.OkoTowerBirinv
import SGPT.Projective.OkounkovOriginalBookPartial

/-! Actual native-modification multiplier values for arbitrary original valuations. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalModification
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set
open SGPT.Okounkov SGPT.Okounkov.AlgebraicValuation SGPT.AlmostSemigroup
open SGPT.LineBundle SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) {m : ℕ}
  [SmoothOfRelativeDimension (m+1) f] (E : ClosedProjectiveEmbedding f)
local instance : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance : ChartedSpace (ComplexModel (m+1)) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f (m+1)
local instance [IsSeparated f] [QuasiCompact f] : IsComplexManifold (m+1) (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f (m+1)
variable {L : X.Modules} (a : LineBundleAtlas L)
  (v : AddValuation X.functionField (WithTop (Lex (Fin (m+1) → ℤ)))) (c : X)
  {Z : Type} [TopologicalSpace Z] [ChartedSpace (ComplexModel (m+1)) Z]
  [IsComplexManifold (m+1) Z]

/-- The SAME arbitrary valuation on sections of the ACTUAL pulled Hermitian line. -/
def pullbackValues (π : Z → SchemeComplexPoint f) (φ : SchemeComplexPoint f → EReal) :
    Set ((Fin (m+1) → ℤ) × ℤ) :=
  AlgebraicValuation.sectionValueSet v c a
    (fun k s => OkoTower.IsPullbackMultiplierSection f E m π φ k s)

/-- The actual pulled multiplier body, using the existing original almost-semigroup reader. -/
def pullbackBody (C : AdmissibleCone (m+1)) (π : Z → SchemeComplexPoint f)
    (φ : SchemeComplexPoint f → EReal) : Set (EuclideanSpace ℝ (Fin (m+1))) :=
  ValGen.setBody C (pullbackValues f E a v c π φ)

/-- Genuine multiplier descent retains the SAME arbitrary valuation and the original sections. -/
theorem pullbackValues_subset {π : Z → SchemeComplexPoint f}
    (hπ : letI := E.isSeparated; letI := E.quasiCompact;
      IsAnalyticModification (n := m+1) π)
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      ManifoldQuasiPlurisubharmonic (n := m+1) φ) :
    pullbackValues f E a v c π φ ⊆ AlgebraicValuation.multiplierSectionSet f (m+1) E v c a φ :=
  AlgebraicValuation.sectionValueSet_mono c a (fun _ _ hs =>
    OkoTower.isMultiplierSection_of_isPullbackMultiplierSection f E hπ hφ hs)

/-- Actual pulled multiplier dimensions equal value-slice cardinalities for the arbitrary valuation. -/
theorem card_slice_pullbackValues [Nonempty (SchemeComplexPoint f)]
    {C : AdmissibleCone (m+1)}
    (hS : sectionSemigroup v c a ≤ latticePoints C.cone)
    (hG : LatticeSlices.generatedGroup (sectionSemigroup v c a) = ⊤)
    {π : Z → SchemeComplexPoint f} (hπc : Continuous π)
    {φ : SchemeComplexPoint f → EReal}
    (hφ : ManifoldQuasiPlurisubharmonic (n := m+1) (fun z => φ (π z))) (k : ℕ) :
    Nat.card (slice (pullbackValues f E a v c π φ) (k : ℤ)) =
      Module.finrank ℂ (OkoTower.pullbackMultiplierSubmodule f E hπc hφ L k) := by
  obtain ⟨Y,hY⟩ := SGPT.Okounkov.OriginalBook.exists_original_smoothFlag_allDimensions f (m+1) E
  rw [pullbackValues, ValGen.slice_sectionValueSet_eq f a c v _ k
    (OkoTower.pullbackMultiplierSubmodule f E hπc hφ L k) (fun _ => Iff.rfl)]
  exact ValGen.card_vectorSet_eq_finrank f E Y hY a c v hS hG k _

end SGPT.Okounkov.OriginalModification
