import SGPT.Okounkov.OF2ModificationFlagValuation
import SGPT.Okounkov.OFNuOkFirstCoordinate
import SGPT.Projective.OkounkovOriginalPerturbGeometry
import SGPT.Foundations.Analysis.Pending.PluripolarCapacityDichotomy
import SGPT.GAGA.SmoothFlagsScheme
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-!
# `rmk:Abhyankar`, "not necessarily equal", unconditionally

Source: chapter *The theory of Okounkov bodies*, `rmk:Abhyankar`: a valuation with value group
`ℤⁿ_lex` and rational rank `n` is equivalent to, **but not necessarily equal to**, a valuation
induced by an admissible flag on a modification of `X`.

For every smooth flag `Y•` on an integral smooth projective complex scheme `X` of dimension
`n ≥ 1` the flag valuation `ν_{Y•}` is surjective (`surjective_schemeFubiniStudyFunctionFieldValuation`:
`𝒪_X(1)`, with its Fubini–Study metric, gives a big line bundle, and lane OF's
`SGPT.Okounkov.OF.surjective_flagValuation` applies). Hence, for `n ≥ 2`
(`exists_lexEquivalent_ne_flagValuations_fubiniStudy`), `ν_{Y•}` has an equivalent valuation
`ν' = ν_{Y•} G` with value group `ℤⁿ` which is not equal to the valuation of any smooth flag on
`X`, nor to the valuation of `ℂ(X)` induced by any smooth flag on any modification of `X`
(`SGPT.Okounkov.OF2.modificationFlagValuation`), nor to any valuation coordinatewise nonnegative
on some local ring of `X` (a property of all flag valuations, admissible or smooth, on all
modifications). In dimension `n ≤ 1` equivalence is equality
(`SGPT.Okounkov.OF2.eq_of_valuationsLexEquivalent_of_le_one`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Okounkov.OF2

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Okounkov SGPT.Okounkov.AlgebraicValuation SGPT.Okounkov.ValCurr
open SGPT.NAPotential.FSPos
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))

/-- An integral projective complex scheme has a complex point (the point over a closed point). -/
theorem nonempty_schemeComplexPoint (E : ClosedProjectiveEmbedding f) :
    Nonempty (SchemeComplexPoint f) := by
  have := E.quasiCompact
  have := E.locallyOfFiniteType
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨x0⟩ : Nonempty X := inferInstance
  obtain ⟨x, -, hx⟩ := isClosed_univ.exists_closed_singleton ⟨x0, Set.mem_univ _⟩
  exact ⟨⟨pointOfClosedPoint f x hx, pointOfClosedPoint_comp f x hx⟩⟩

section Surjective

variable {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]

local instance of2ExTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance of2ExCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance of2ExManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

/-- The flag valuation `ν_{Y•} : ℂ(X)^× → ℤⁿ` of every smooth flag on an integral smooth
projective complex scheme of dimension `n ≥ 1` is surjective. -/
theorem surjective_schemeFubiniStudyFunctionFieldValuation (E : ClosedProjectiveEmbedding f)
    (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f))
    (hY : letI := E.isSeparated; letI := E.quasiCompact; IsSmoothFlag Y) :
    Function.Surjective (schemeFubiniStudyFunctionFieldValuation f (m + 1) E Y hY) := by
  let := E.isSeparated
  let := E.quasiCompact
  have : Nonempty (SchemeComplexPoint f) :=
    ⟨(schemeProjectiveOriginalFlagPoint f (m + 1) E
      (schemeProjectiveTNKahlerBackground f (m + 1) E) Y hY).val⟩
  have hK := fubiniStudy_curvature_isKahler f (m + 1) E
  let κ : KahlerBackground (m + 1) (SchemeComplexPoint f) :=
    ⟨(fubiniStudyMetric f E (m + 1)).curvature (hyperplaneAtlas E), hK⟩
  have hφ : IsThetaPshPotential ((fubiniStudyMetric f E (m + 1)).curvature (hyperplaneAtlas E)).val
      (fun _ => 0) :=
    PluripolarCapacityDichotomy.isThetaPshPotential_zero κ
  obtain ⟨-, hbig⟩ := OriginalBook.original_positivePerturbation_kahler_and_big f (m + 1) E
    (hyperplaneAtlas E) (fubiniStudyMetric f E (m + 1)) (hyperplaneAtlas E)
    (fubiniStudyMetric f E (m + 1)) hK hφ 1 1 one_pos one_pos
  exact OF.surjective_flagValuation f E Y hY
    (OkoNS.perturbAtlas (hyperplaneAtlas E) (hyperplaneAtlas E) 1 1)
    (OriginalBook.originalPerturbMetric f (m + 1) E (hyperplaneAtlas E)
      (fubiniStudyMetric f E (m + 1)) (hyperplaneAtlas E) (fubiniStudyMetric f E (m + 1)) 1 1)
    hbig

end Surjective

section NotEqual

variable {m : ℕ} [SmoothOfRelativeDimension (m + 2) f]

local instance of2ExNETopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance of2ExNECharts : ChartedSpace (ComplexModel (m + 2)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 2)
local instance of2ExNEManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold (m + 2) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 2)

/-- **`rmk:Abhyankar`, "equivalent, but not necessarily equal".** Let `X` be an integral smooth
projective complex scheme of dimension `n = m + 2 ≥ 2` and `Y•` a smooth flag on `X`. The flag
valuation `ν_{Y•}` has an equivalent valuation `ν' = ν_{Y•} G` (`G = I + N`, `N` strictly upper
triangular integral), with value group `ℤⁿ` (maximal rational rank `n`), such that `ν'` is not
equal to

* any valuation of `ℂ(X)` which is coordinatewise nonnegative on some local ring `𝒪_{X,c}`;
* the valuation of any smooth flag `Z•` on `X`;
* the valuation of `ℂ(X)` induced by any smooth flag on any modification of `X`. -/
theorem exists_lexEquivalent_ne_flagValuations_fubiniStudy (E : ClosedProjectiveEmbedding f)
    (Y : Fin (m + 2 + 1) → Set (SchemeComplexPoint f))
    (hY : letI := E.isSeparated; letI := E.quasiCompact; IsSmoothFlag Y) :
    letI := E.isSeparated
    letI := E.quasiCompact
    ∃ v' : AddValuation X.functionField (WithTop (Lex (Fin (m + 2) → ℤ))),
      ValuationsLexEquivalent (schemeFubiniStudyFunctionFieldValuation f (m + 2) E Y hY) v' ∧
      Function.Surjective v' ∧
      (∀ (μ : AddValuation X.functionField (WithTop (Lex (Fin (m + 2) → ℤ)))) (c : X),
        IsCoordNonnegAt μ c → v' ≠ μ) ∧
      (∀ (omega' : KahlerBackground (m + 2) (SchemeComplexPoint f))
        (Z : Fin (m + 2 + 1) → Set (SchemeComplexPoint f)) (hZ : IsSmoothFlag Z),
        v' ≠ schemeOriginalFlagFunctionFieldValuation f (m + 2) E omega' Z hZ) ∧
      (∀ (F : OriginalFlagGeometry.{0} (m + 2)) {π : F.carrier → SchemeComplexPoint f}
        (hπ : IsAnalyticModification (n := m + 2) π),
        v' ≠ modificationFlagValuation f F hπ) := by
  let := E.isSeparated
  let := E.quasiCompact
  exact exists_lexEquivalent_ne_flagValuations f E (schemeProjectiveTNKahlerBackground f (m + 2) E)
    Y hY (surjective_schemeFubiniStudyFunctionFieldValuation (m := m + 1) f E Y hY)

/-- **`rmk:Abhyankar`, "not necessarily equal", on every `X`.** Every integral smooth projective
complex scheme `X` of dimension `n = m + 2 ≥ 2` carries a valuation `ν' : ℂ(X)^× → ℤⁿ` (value group
`ℤⁿ_lex`, rational rank `n`) which is equivalent to the flag valuation `ν_{Y•}` of a smooth flag on
`X` but is not equal to any valuation coordinatewise nonnegative on a local ring of `X`, to the
valuation of any smooth flag on `X`, nor to the valuation induced by any smooth flag on any
modification of `X`. -/
theorem exists_flag_lexEquivalent_ne_flagValuations (E : ClosedProjectiveEmbedding f) :
    letI := E.isSeparated
    letI := E.quasiCompact
    ∃ (Y : Fin (m + 2 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)
      (v' : AddValuation X.functionField (WithTop (Lex (Fin (m + 2) → ℤ)))),
      ValuationsLexEquivalent (schemeFubiniStudyFunctionFieldValuation f (m + 2) E Y hY) v' ∧
      Function.Surjective v' ∧
      (∀ (μ : AddValuation X.functionField (WithTop (Lex (Fin (m + 2) → ℤ)))) (c : X),
        IsCoordNonnegAt μ c → v' ≠ μ) ∧
      (∀ (omega' : KahlerBackground (m + 2) (SchemeComplexPoint f))
        (Z : Fin (m + 2 + 1) → Set (SchemeComplexPoint f)) (hZ : IsSmoothFlag Z),
        v' ≠ schemeOriginalFlagFunctionFieldValuation f (m + 2) E omega' Z hZ) ∧
      (∀ (F : OriginalFlagGeometry.{0} (m + 2)) {π : F.carrier → SchemeComplexPoint f}
        (hπ : IsAnalyticModification (n := m + 2) π),
        v' ≠ modificationFlagValuation f F hπ) := by
  let := E.isSeparated
  let := E.quasiCompact
  have := nonempty_schemeComplexPoint f E
  obtain ⟨Y, hY⟩ := SGPT.GAGA.SmoothFlags.smoothFlagsExist X f E (m + 1)
  obtain ⟨v', h⟩ := exists_lexEquivalent_ne_flagValuations_fubiniStudy f E Y hY
  exact ⟨Y, hY, v', h⟩

end NotEqual

end SGPT.Okounkov.OF2
