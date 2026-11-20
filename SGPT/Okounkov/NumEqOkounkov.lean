import SGPT.Okounkov.OkoNSAlgebraic
import SGPT.Projective.NumEqCurves

/-!
# Numerical equivalence of line bundles and Okounkov bodies

Lane NUMEQ, blueprint `claude-numeq.tex`.  Source: `prop:Okounonlydepnum` ("The Okounkov body
`Δ_ν(L)` depends only on the numerical class of `L`", chapter *The theory of Okounkov bodies*).

Setting of lane OKO-NS: `X` an integral smooth projective complex scheme of dimension `m + 1`
with a closed projective embedding `E`, a smooth flag `Y•`, and the flag valuation `ν = ν_{Y•}`.

* `LineBundleNumericallyEquivalent a a'` (`L ≡ L'`): the first Chern forms `c₁(L, H)`,
  `c₁(L', H')` of the structural metrics have the same degree along every holomorphic map from a
  compact connected Riemann surface (`SGPT.Projective.NumEq.NumericallyEquivalent`), i.e.
  `L · Γ = L' · Γ` for every curve `Γ ⊆ X`; `lineBundleNumericallyEquivalent_iff` shows that any
  smooth metrics may be used (metric and atlas independence).
* `lineBundleNumericallyEquivalent_of_chernClass_eq`: line bundles with the same real first Chern
  class are numerically equivalent.
* **`lineBundleOkounkovBody_eq_of_numericallyEquivalent_dim_one`** (`prop:Okounonlydepnum`,
  `n = 1`): on a curve, numerically equivalent big line bundles have the same Okounkov body
  (numerical equivalence is cohomological equivalence on a curve,
  `SGPT.Projective.NumEq.ofRepresentative_eq_of_numericallyEquivalent_dim_one`, and the body only
  depends on the real Chern class, `OkoNS.lineBundleOkounkovBody_eq_of_chernClass_eq`).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.NumEq

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Okounkov SGPT.LineBundle SGPT.Projective.NumEq

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
  [IsIntegral X] {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]

local instance numEqTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance numEqCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance numEqManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

/-- **Numerical equivalence of line bundles** `L ≡ L'`: `L · Γ = L' · Γ` for every curve `Γ ⊆ X`,
read as equality of the degrees `∫_C g^* c₁(L, H) = ∫_C g^* c₁(L', H')` along all holomorphic
maps `g` from compact connected Riemann surfaces (the normalizations of the curves of `X`, and
their compositions with finite maps), for the structural metrics `H`, `H'`. -/
def LineBundleNumericallyEquivalent {L L' : X.Modules} (a : LineBundleAtlas L)
    (a' : LineBundleAtlas L') : Prop :=
  letI := E.isSeparated
  letI := E.quasiCompact
  NumericallyEquivalent ((schemeLineBundleMetric f (m + 1) E a).curvature a)
    ((schemeLineBundleMetric f (m + 1) E a').curvature a')

omit [IsIntegral X] in
/-- **Well-definedness**: numerical equivalence may be tested with any smooth metrics. -/
theorem lineBundleNumericallyEquivalent_iff {L L' : X.Modules} (a : LineBundleAtlas L)
    (H : SchemeLineBundleMetric f (m + 1) E L) (a' : LineBundleAtlas L')
    (H' : SchemeLineBundleMetric f (m + 1) E L') :
    letI := E.isSeparated
    letI := E.quasiCompact
    LineBundleNumericallyEquivalent (m := m) f E a a' ↔
      NumericallyEquivalent (H.curvature a) (H'.curvature a') := by
  let := E.isSeparated
  let := E.quasiCompact
  have h1 : NumericallyEquivalent ((schemeLineBundleMetric f (m + 1) E a).curvature a)
      (H.curvature a) :=
    numericallyEquivalent_of_ofRepresentative_eq
      ((schemeLineBundleMetric f (m + 1) E a).chernClass_independent H a a)
  have h2 : NumericallyEquivalent ((schemeLineBundleMetric f (m + 1) E a').curvature a')
      (H'.curvature a') :=
    numericallyEquivalent_of_ofRepresentative_eq
      ((schemeLineBundleMetric f (m + 1) E a').chernClass_independent H' a' a')
  exact ⟨fun h => (h1.symm.trans h).trans h2, fun h => (h1.trans h).trans h2.symm⟩

omit [IsIntegral X] in
/-- Line bundles with the same real first Chern class are numerically equivalent. -/
theorem lineBundleNumericallyEquivalent_of_chernClass_eq {L L' : X.Modules}
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m + 1) E L) (a' : LineBundleAtlas L')
    (H' : SchemeLineBundleMetric f (m + 1) E L')
    (hclass : letI := E.isSeparated; letI := E.quasiCompact;
      H.chernClass a = H'.chernClass a') :
    LineBundleNumericallyEquivalent (m := m) f E a a' := by
  let := E.isSeparated
  let := E.quasiCompact
  exact (lineBundleNumericallyEquivalent_iff f E a H a' H').mpr
    (numericallyEquivalent_of_ofRepresentative_eq hclass)

end SGPT.Okounkov.NumEq

namespace SGPT.Okounkov.NumEq

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Okounkov SGPT.LineBundle SGPT.Projective.NumEq

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
  [IsIntegral X] [SmoothOfRelativeDimension (0 + 1) f]

local instance numEqTopology₁ : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance numEqCharts₁ : ChartedSpace (ComplexModel (0 + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (0 + 1)
local instance numEqManifold₁ [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold (0 + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (0 + 1)

variable (Y : Fin (0 + 1 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)

/-- **Source `prop:Okounonlydepnum`, dimension one**: on a smooth projective curve, numerically
equivalent big line bundles `L ≡ L'` have the same Okounkov body `Δ_ν(L) = Δ_ν(L')`. -/
theorem lineBundleOkounkovBody_eq_of_numericallyEquivalent_dim_one
    [Nonempty (SchemeComplexPoint f)] {L L' : X.Modules} (a : LineBundleAtlas L)
    (a' : LineBundleAtlas L') (hbig : IsBig f L (0 + 1)) (hbig' : IsBig f L' (0 + 1))
    (hnum : LineBundleNumericallyEquivalent (m := 0) f E a a') :
    lineBundleOkounkovBody f (0 + 1) E Y hY a = lineBundleOkounkovBody f (0 + 1) E Y hY a' := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have : ConnectedSpace (SchemeComplexPoint f) := schemeSmoothFlag_connectedSpace f (0 + 1) Y hY
  exact OkoNS.lineBundleOkounkovBody_eq_of_chernClass_eq f E Y hY a
    (schemeLineBundleMetric f (0 + 1) E a) a' (schemeLineBundleMetric f (0 + 1) E a') hbig hbig'
    (ofRepresentative_eq_of_numericallyEquivalent_dim_one
      (schemeProjectiveTNKahlerBackground f (0 + 1) E) hnum)

end SGPT.Okounkov.NumEq
