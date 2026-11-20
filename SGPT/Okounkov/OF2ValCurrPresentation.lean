import SGPT.Okounkov.OF2AbhyankarFlagExample
import SGPT.Okounkov.FlagValuationChoiceIndependence
import SGPT.Okounkov.CurrentFlagValuation

/-!
# `rmk:valcurr`: the current value of a presentation on a fixed smooth model

Source: chapter *The theory of Okounkov bodies*, `rmk:valcurr`: for a rank `n` surjective valuation
`ν : ℂ(X)^× → ℤⁿ` and a closed positive `(1,1)`-current `T`, take a resolution `π : Y → X` with a
smooth flag `Y•` on `Y` and `g ∈ Aut(ℤⁿ_lex)` such that `ν = ν_{Y•} g`, and put
`ν(T) := ν_{Y•}(π^*T) g`.

On an integral smooth projective complex scheme `X` (resolution `π = id`), a *presentation* of `ν`
is a smooth flag `Y•` on `X` and a unitriangular `G` with `ν = ν_{Y•} G`; its current value is
`presentationCurrentValue = ν_{Y•}(T) G` (`def:valcurr` for `ν_{Y•}(T)`, the row vector times `G`).

* `matrix_eq_of_lexMapValuation_eq`: for surjective `ν`, `ν G = ν H` forces `G = H`.
* `presentationCurrentValue_eq` (**independence on a fixed model**): two presentations of the same
  surjective `ν` on `X` have the same flag (flag reconstruction from the valuation,
  `SGPT.Okounkov.schemeOriginalFlags_eq_of_lexEquivalent`) and the same matrix, hence give the same
  value `ν(T)` for every closed positive `(1,1)`-current `T`.
* In dimension `1` every surjective `ν` has a presentation on `X` itself with `G = I`
  (`exists_isSmoothFlag_eq_flagValuation_of_curve`).

Independence across *different* models (common resolution, `prop:cormatrix`, `prop:cormult`) and the
existence of presentations in dimension `≥ 2` are not covered here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Okounkov.OF2

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set
open SGPT.Okounkov SGPT.Okounkov.AlgebraicValuation SGPT.Okounkov.ValCurr
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open GlobalCurrents CanonicalCurrentFrame GlobalPositiveCurrentACRestriction
open scoped Matrix

/-- For a surjective valuation, the matrix of an equivalent valuation is unique. -/
theorem matrix_eq_of_lexMapValuation_eq {R : Type*} [Ring R] {n : ℕ}
    {v : AddValuation R (WithTop (Lex (Fin n → ℤ)))} (hv : Function.Surjective v)
    {G H : Matrix (Fin n) (Fin n) ℤ} (hG : IsUnitUpperTriangular G)
    (hH : IsUnitUpperTriangular H)
    (h : lexMapValuation G hG v = lexMapValuation H hH v) : G = H := by
  classical
  ext i j
  obtain ⟨r, hr⟩ := hv ((toLex (Pi.single i (1 : ℤ)) : Lex (Fin n → ℤ)) :
    WithTop (Lex (Fin n → ℤ)))
  have h1 : lexMapValuation G hG v r = lexMapValuation H hH v r := by rw [h]
  rw [lexMapValuation_apply, lexMapValuation_apply, hr, lexWithTopHom_coe,
    lexWithTopHom_coe] at h1
  have h2 := congrArg (fun y : Lex (Fin n → ℤ) => ofLex y j) (WithTop.coe_injective h1)
  simp only [ofLex_toLex] at h2
  simpa [Matrix.vecMul, dotProduct, Pi.single_apply] using h2

section Presentation

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) {m : ℕ}
  [SmoothOfRelativeDimension (m + 1) f] [IsSeparated f] [QuasiCompact f]

local instance of2PresTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance of2PresCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance of2PresManifold : IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

/-- The current value `ν_{Y•}(T) G` of a presentation `ν = ν_{Y•} G` on `X`. -/
def presentationCurrentValue (E : ClosedProjectiveEmbedding f)
    (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f))
    (hY : IsSmoothFlag Y)
    (G : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ)
    (T : GlobalCurrent (m + 1) (SchemeComplexPoint f) (degreeTwo (Nat.succ_pos m)))
    (hc : T.IsClosed (canonicalBasis (m + 1)))
    (h11 : T.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hT : IsFullPositive T) : Fin (m + 1) → ℝ :=
  (fun i => (currentFlagValuation (schemeProjectiveOriginalFlagGeometry f (m + 1) E
      (schemeProjectiveTNKahlerBackground f (m + 1) E) Y hY) T hc h11 hT i : ℝ)) ᵥ*
    (fun i j => (G i j : ℝ))

/-- **`rmk:valcurr`, independence on a fixed smooth model.** Two presentations
`ν = ν_{Y•} G = ν_{Z•} H` of the same surjective valuation on `X` have `Y• = Z•` and `G = H`, hence
the same current value `ν(T)` for every closed positive `(1,1)`-current `T`. -/
theorem presentationCurrentValue_eq (E : ClosedProjectiveEmbedding f)
    (v : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ))))
    (hv : Function.Surjective v)
    (Y Z : Fin (m + 1 + 1) → Set (SchemeComplexPoint f))
    (hY : IsSmoothFlag Y) (hZ : IsSmoothFlag Z)
    {G H : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ} (hG : IsUnitUpperTriangular G)
    (hH : IsUnitUpperTriangular H)
    (h1 : v = lexMapValuation G hG (schemeFubiniStudyFunctionFieldValuation f (m + 1) E Y hY))
    (h2 : v = lexMapValuation H hH (schemeFubiniStudyFunctionFieldValuation f (m + 1) E Z hZ))
    (T : GlobalCurrent (m + 1) (SchemeComplexPoint f) (degreeTwo (Nat.succ_pos m)))
    (hc : T.IsClosed (canonicalBasis (m + 1)))
    (h11 : T.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hT : IsFullPositive T) :
    Y = Z ∧ G = H ∧
      presentationCurrentValue f E Y hY G T hc h11 hT =
        presentationCurrentValue f E Z hZ H T hc h11 hT := by
  have hequiv : ValuationsLexEquivalent
      (schemeFubiniStudyFunctionFieldValuation f (m + 1) E Y hY)
      (schemeFubiniStudyFunctionFieldValuation f (m + 1) E Z hZ) := by
    have hYv : ValuationsLexEquivalent
        (schemeFubiniStudyFunctionFieldValuation f (m + 1) E Y hY) v := ⟨G, hG, h1⟩
    have hZv : ValuationsLexEquivalent
        (schemeFubiniStudyFunctionFieldValuation f (m + 1) E Z hZ) v := ⟨H, hH, h2⟩
    exact valuationsLexEquivalent_equivalence.trans hYv
      (valuationsLexEquivalent_equivalence.symm hZv)
  have hYZ : Y = Z := schemeOriginalFlags_eq_of_lexEquivalent f (m + 1) E
    (schemeProjectiveTNKahlerBackground f (m + 1) E)
    (schemeProjectiveTNKahlerBackground f (m + 1) E)
    Y Z hY hZ hequiv
  subst hYZ
  have hGH : G = H := matrix_eq_of_lexMapValuation_eq
    (surjective_schemeFubiniStudyFunctionFieldValuation f E Y hY) hG hH (h1.symm.trans h2)
  subst hGH
  exact ⟨rfl, rfl, rfl⟩

end Presentation

end SGPT.Okounkov.OF2
