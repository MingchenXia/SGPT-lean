import SGPT.Okounkov.SchemeProjectiveTNKahler
import SGPT.Okounkov.SchemeOriginalSectionValueCount

/-!
# Original projective flag values with the background manufactured internally

The actual source-derived Fubini–Study TN background is inserted literally into
the accepted original geometry, global field, whole-vector and section-count
producers. No background is supplied and no flag or global rank is manufactured.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Okounkov

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open scoped Topology

variable {X : Scheme} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)

local instance fsOriginalPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance fsOriginalPointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n

variable (Y : Fin (n + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)

/-- Actual projectivity supplies the SAME genuine Kähler background internally. -/
def schemeFubiniStudyOriginalFlagGeometry : OriginalFlagGeometry n :=
  schemeProjectiveOriginalFlagGeometry f n E (schemeProjectiveTNKahlerBackground f n E) Y hY

/-- The literal original geometry retains precisely the manufactured background. -/
theorem schemeFubiniStudyOriginalFlagGeometry_background :
    (schemeFubiniStudyOriginalFlagGeometry f n E Y hY).omega =
      schemeProjectiveTNKahlerBackground f n E := rfl

variable [IsIntegral X]

/-- The ACTUAL global field receives its genuine full lex valuation without a background input. -/
def schemeFubiniStudyFunctionFieldValuation :
    AddValuation X.functionField (WithTop (Lex (Fin n → ℤ))) :=
  schemeOriginalFlagFunctionFieldValuation f n E (schemeProjectiveTNKahlerBackground f n E) Y hY

/-- WHOLE original native fraction values read back the SAME actual field embedding. -/
theorem schemeFubiniStudyFunctionFieldValuation_apply (q : X.functionField) :
    letI := E.isSeparated
    letI := E.quasiCompact
    schemeFubiniStudyFunctionFieldValuation f n E Y hY q =
      originalFlagGermFractionValuation (schemeFubiniStudyOriginalFlagGeometry f n E Y hY)
        (schemeProjectiveOriginalFlagPoint f n E (schemeProjectiveTNKahlerBackground f n E) Y hY)
        (schemeNativeFunctionFieldGerm f n
          (schemeProjectiveOriginalFlagPoint f n E (schemeProjectiveTNKahlerBackground f n E) Y hY).val q) := by
  let := E.isSeparated
  let := E.quasiCompact
  rfl

/-- Every coordinate is the accepted actual nonzero original point-frame germ recursion. -/
def schemeFubiniStudySectionVector {L : X.Modules} (a : LineBundleAtlas L)
    (m : ℕ) (s : bundlePowerGlobalSections L m) (hs : s ≠ 0) : Fin n → ℕ := by
  letI := E.isSeparated
  letI := E.quasiCompact
  exact schemeOriginalFlagSectionVector f n E (schemeProjectiveTNKahlerBackground f n E) Y hY a m s hs

/-- Literal insertion of the generated background retains the entire finite natural vector. -/
theorem schemeFubiniStudySectionValue_vector {L : X.Modules} (a : LineBundleAtlas L)
    (m : ℕ) (s : bundlePowerGlobalSections L m) (hs : s ≠ 0) :
    letI := E.isSeparated
    letI := E.quasiCompact
    schemeOriginalFlagSectionValue f n E (schemeProjectiveTNKahlerBackground f n E) Y hY a m s =
      ((toLex (fun i => (schemeFubiniStudySectionVector f n E Y hY a m s hs i : ℤ)) :
        Lex (Fin n → ℤ)) : WithTop (Lex (Fin n → ℤ))) := by
  let := E.isSeparated
  let := E.quasiCompact
  exact schemeOriginalFlagSectionValue_of_ne_zero f n E (schemeProjectiveTNKahlerBackground f n E) Y hY a m s hs

/-- Actual source projective H0 and the genuine finite-leaf producer still supply finiteness. -/
theorem schemeFubiniStudySectionValues_finite {L : X.Modules} (a : LineBundleAtlas L) (m : ℕ) :
    letI := E.isSeparated
    letI := E.quasiCompact
    (schemeOriginalFlagSectionValues f n E (schemeProjectiveTNKahlerBackground f n E) Y hY a m).Finite := by
  let := E.isSeparated
  let := E.quasiCompact
  exact schemeProjectiveOriginalFlagSectionValues_finite f n E (schemeProjectiveTNKahlerBackground f n E) Y hY a m

/-- The actual original structural section dimension is counted with no supplied
background, finite-dimensionality, leaf, adapted basis or count certificate. -/
theorem schemeFubiniStudySectionValues_card_eq_finrank {L : X.Modules} (a : LineBundleAtlas L) (m : ℕ) :
    letI := E.isSeparated
    letI := E.quasiCompact
    letI := schemeGlobalSectionModule f (bundleTensorPower L m)
    Nat.card (schemeOriginalFlagSectionValues f n E (schemeProjectiveTNKahlerBackground f n E) Y hY a m) =
      Module.finrank ℂ (bundlePowerGlobalSections L m) := by
  let := E.isSeparated
  let := E.quasiCompact
  let := schemeGlobalSectionModule f (bundleTensorPower L m)
  exact schemeProjectiveOriginalFlagSectionValues_card_eq_finrank f n E
    (schemeProjectiveTNKahlerBackground f n E) Y hY a m

end SGPT.Okounkov
