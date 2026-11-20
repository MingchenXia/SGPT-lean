import SGPT.Projective.OkounkovOriginalIdealProducts
import SGPT.Projective.OriginalSectionUnit

/-! Literal original tensor-left-unit readers and actual original multiplier membership.
Blueprint: okounkov-original-left-unit-multiplier.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalLeftUnitMultiplier
open Set CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Okounkov.AlgebraicValuation
open SGPT.Projective.NumEq.AlgebraicCurveDegree

section Original
variable {X : Scheme.{0}} {M : X.Modules}

private theorem leftUnitHom_inverse (s : bundlePowerGlobalSections M 1) :
    originalSectionUnit ((bundleTensorLeftUnitIso M).hom.val.app (.op ⊤) s)=s :=
  congr($((bundleTensorLeftUnitIso M).hom_inv_id).val.app (.op ⊤) |>.hom s)

private theorem leftUnitHom_coefficients (s : bundlePowerGlobalSections M 1)
    {U : X.Opens} (e : LocalBundleFrame M U) :
    (e.tensorPower 1).coefficients (𝟙 _)
      ((bundleTensorPower M 1).val.map U.leTop.op s) =
    e.coefficients (𝟙 _) (M.val.map U.leTop.op ((bundleTensorLeftUnitIso M).hom.val.app (.op ⊤) s)) := by
  have h := originalSectionUnit_coefficients ((bundleTensorLeftUnitIso M).hom.val.app (.op ⊤) s) e (𝟙 _)
  rw [leftUnitHom_inverse] at h
  exact h

/-- The SAME genuine original unitor preserves EVERY actual original generic coefficient. -/
theorem originalLeftUnitHom_genericCoefficient [IsIntegral X]
    (s : bundlePowerGlobalSections M 1) {U : X.Opens} [Nonempty U] (e : LocalBundleFrame M U) :
    globalSectionToFunctionField e ((bundleTensorLeftUnitIso M).hom.val.app (.op ⊤) s) =
      globalSectionToFunctionField (e.tensorPower 1) s := by
  exact congrArg (X.germToFunctionField U) (leftUnitHom_coefficients s e).symm

end Original

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ) (E : ClosedProjectiveEmbedding f)
  [SmoothOfRelativeDimension n f]
local instance leftUnitMultiplierTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance leftUnitMultiplierCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n

/-- Exact analytic coefficient function equality, not a sheaf identification. -/
theorem originalLeftUnitHom_coefficient {M : X.Modules} (s : bundlePowerGlobalSections M 1)
    {U : X.Opens} (e : LocalBundleFrame M U) :
    sectionFrameCoefficient f n E e 1 s =
      schemeOpenRegularFunction f n E U
        (e.coefficients (𝟙 _) (M.val.map U.leTop.op ((bundleTensorLeftUnitIso M).hom.val.app (.op ⊤) s))) :=
  congrArg (schemeOpenRegularFunction f n E U) (leftUnitHom_coefficients s e)

/-- Literal original multiplier-ideal equivalence through the ACTUAL original left tensor unitor. -/
theorem originalLeftUnitHom_multiplier_iff {M : X.Modules} (s : bundlePowerGlobalSections M 1)
    (φ : SchemeComplexPoint f → EReal) (d : ℝ) :
    IsPlainIdealSection f n E (multiplierIdeal (n:=n) d φ)
      ((bundleTensorLeftUnitIso M).hom.val.app (.op ⊤) s) ↔
    IsIdealSection f n E (multiplierIdeal (n:=n) d φ) 1 s := by
  constructor
  · intro hs U e p hp
    rw [originalLeftUnitHom_coefficient f n E s e]
    exact hs U e p hp
  · intro hs U e p hp
    have h := hs U e p hp
    rw [originalLeftUnitHom_coefficient f n E s e] at h
    exact h

end SGPT.Okounkov.OriginalLeftUnitMultiplier
