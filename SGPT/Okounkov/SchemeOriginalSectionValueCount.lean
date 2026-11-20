import SGPT.Okounkov.SchemeOriginalSectionValuation
import SGPT.Okounkov.SchemeProjectiveSectionSpace

/-!
# Genuine projective sections have dimension-many original full flag values

The actual nonzero section values are identified with the literal native
fraction image values. Genuine projective H0 and the proved native finite-leaf
basis argument internally give finiteness and the exact original dimension.
No finite-dimensionality, adapted-basis, leaf or count certificate is supplied.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Okounkov

open CategoryTheory AlgebraicGeometry Algebra SGPT.Foundations.Schemes Set
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open scoped Topology

variable {X : Scheme} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f]

section Values

variable [IsSeparated f] [QuasiCompact f]

local instance originalSectionCountTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance originalSectionCountCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance originalSectionCountManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n
local instance originalSectionCountComplexAlgebra (p : SchemeComplexPoint f) :
    Algebra ℂ (FractionRing (NativeHolGerm n (SchemeComplexPoint f) p)) :=
  schemeNativeFractionComplexAlgebra f n p

variable (e : ClosedProjectiveEmbedding f) (ω : KahlerBackground n (SchemeComplexPoint f))
  (Y : Fin (n + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)

/-- Literal full values of the ACTUAL nonzero original sections, without chosen representatives. -/
def schemeOriginalFlagSectionValues {L : X.Modules} (a : LineBundleAtlas L) (m : ℕ) :
    Set (WithTop (Lex (Fin n → ℤ))) :=
  {v | ∃ s : bundlePowerGlobalSections L m, s ≠ 0 ∧
    schemeOriginalFlagSectionValue f n e ω Y hY a m s = v}

/-- Actual range preimages identify the WHOLE actual section and native image value sets.
The native and source fraction complex actions are literally the SAME constants/inclusion. -/
theorem schemeOriginalFlagSectionValues_eq_native {L : X.Modules}
    (a : LineBundleAtlas L) (m : ℕ) :
    schemeOriginalFlagSectionValues f n e ω Y hY a m =
      originalFlagGermFractionValues (schemeProjectiveOriginalFlagGeometry f n e ω Y hY)
        (schemeProjectiveOriginalFlagPoint f n e ω Y hY)
        (schemePointPowerSectionSpace f n (schemeProjectiveOriginalFlagPoint f n e ω Y hY).val a m) := by
  let p := (schemeProjectiveOriginalFlagPoint f n e ω Y hY).val
  let := schemeGlobalSectionModule f (bundleTensorPower L m)
  let := schemeFunctionFieldAlgebra f
  ext v
  change (∃ s : bundlePowerGlobalSections L m, s ≠ 0 ∧
      schemeOriginalFlagSectionValue f n e ω Y hY a m s = v) ↔
    ∃ u : schemePointPowerSectionSpace f n p a m, u ≠ 0 ∧
      originalFlagGermFractionValuation (schemeProjectiveOriginalFlagGeometry f n e ω Y hY)
        (schemeProjectiveOriginalFlagPoint f n e ω Y hY) u.val = v
  constructor
  · rintro ⟨s, hs, hv⟩
    refine ⟨⟨schemePointPowerGlobalSectionsGerm f n p a m s, s, rfl⟩, ?_, ?_⟩
    · intro hz
      apply hs
      apply schemePointPowerGlobalSectionsGerm_injective f n p a m
      simpa only [map_zero, Submodule.coe_zero] using congrArg Subtype.val hz
    · exact hv
  · rintro ⟨u, hu, hv⟩
    obtain ⟨s, hs⟩ := u.property
    refine ⟨s, ?_, ?_⟩
    · intro hz
      apply hu
      apply Subtype.ext
      rw [← hs, hz, map_zero]
      rfl
    · change originalFlagGermFractionValuation (schemeProjectiveOriginalFlagGeometry f n e ω Y hY)
        (schemeProjectiveOriginalFlagPoint f n e ω Y hY)
        (schemePointPowerGlobalSectionsGerm f n p a m s) = v
      rw [hs]
      exact hv

end Values

/-- Genuine actual projectivity derives every geometric and H0 finiteness input;
the native proved finite-leaf producer then makes actual section values finite. -/
theorem schemeProjectiveOriginalFlagSectionValues_finite (e : ClosedProjectiveEmbedding f) :
    letI := e.isSeparated
    letI := e.quasiCompact
    letI : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
    letI : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
    letI : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n
    ∀ (ω : KahlerBackground n (SchemeComplexPoint f))
      (Y : Fin (n + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)
      {L : X.Modules} (a : LineBundleAtlas L) (m : ℕ),
      (schemeOriginalFlagSectionValues f n e ω Y hY a m).Finite := by
  let := e.isSeparated
  let := e.quasiCompact
  intro ω Y hY L a m
  let F := schemeProjectiveOriginalFlagGeometry f n e ω Y hY
  let x := schemeProjectiveOriginalFlagPoint f n e ω Y hY
  let := schemeNativeFractionComplexAlgebra f n x.val
  let V := schemePointPowerSectionSpace f n x.val a m
  have hfd : FiniteDimensional ℂ V := schemeProjectivePointPowerSectionSpace_finiteDimensional f n e x.val a m
  rw [schemeOriginalFlagSectionValues_eq_native]
  exact @originalFlagGermFractionValues_finite n F x V hfd

/-- ACTUAL projective section value cardinality is the EXACT original structural dimension.
The actual native basis/count and actual section-image equivalence discharge everything. -/
theorem schemeProjectiveOriginalFlagSectionValues_card_eq_finrank (e : ClosedProjectiveEmbedding f) :
    letI := e.isSeparated
    letI := e.quasiCompact
    letI : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
    letI : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
    letI : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n
    ∀ (ω : KahlerBackground n (SchemeComplexPoint f))
      (Y : Fin (n + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)
      {L : X.Modules} (a : LineBundleAtlas L) (m : ℕ),
      letI := schemeGlobalSectionModule f (bundleTensorPower L m)
      Nat.card (schemeOriginalFlagSectionValues f n e ω Y hY a m) =
        Module.finrank ℂ (bundlePowerGlobalSections L m) := by
  let := e.isSeparated
  let := e.quasiCompact
  intro ω Y hY L a m
  let := schemeGlobalSectionModule f (bundleTensorPower L m)
  let F := schemeProjectiveOriginalFlagGeometry f n e ω Y hY
  let x := schemeProjectiveOriginalFlagPoint f n e ω Y hY
  let := schemeNativeFractionComplexAlgebra f n x.val
  let V := schemePointPowerSectionSpace f n x.val a m
  have hfd : FiniteDimensional ℂ V := schemeProjectivePointPowerSectionSpace_finiteDimensional f n e x.val a m
  rw [schemeOriginalFlagSectionValues_eq_native]
  exact (@originalFlagGermFractionValues_card_eq_finrank n F x V hfd).trans
    (schemePointPowerSectionSpace_finrank f n x.val a m)

end SGPT.Okounkov
