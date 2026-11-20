import SGPT.LineBundle.AmpleChernComparison
import SGPT.Hodge.SourceCartierMixedAlgebra
import SGPT.GAGA.OkoCloseDXMain

/-!
# The Snapper–Kleiman self-intersection of an ample line bundle is the book's product

Toward the intersection-number item of `rmk:bdiv:L749` (`chapter_bdiv.tex`): Dang–Favre's
intersection numbers of nef Cartier classes on a model are the algebraic (Snapper–Kleiman)
intersection numbers.  On the diagonal and for ample line bundles this is EP-free:

Let `X` be an integral scheme, smooth projective of dimension `m + 1` over `ℂ`, `L` an ample
line bundle with a polarization `P` and `D` any Weil b-divisor over the analytic space `X(ℂ)`
(over the book's blow-up models) which is Cartier, realized on the root model `X(ℂ)` by the
first Chern class `c₁(L)` (`SchemeLineBundleMetric.chernClass`).  Then `D` is nef and its book
self-product (`def:DF_ext`, `nefIntersectionReal`) is the Snapper–Kleiman self-intersection
`(L^{m+1})` (`AmplePolarization.selfIntersection`: the eventual `(m+1)`-st difference of the
Euler characteristics `χ(X, L^{qk})`, i.e. `(m+1)!` times the leading coefficient of the Snapper
polynomial, divided by `q^{m+1}`) — `nefIntersectionReal_eq_selfIntersection`.

Proof: a positive metric on `L` (`exists_positive_metric_of_amplePolarization`) gives a Kähler
representative of `c₁(L)`, so the product is the classical number `∫ c₁(L, h)^{m+1}`
(`nefIntersectionReal_of_common_nef_realization`), which is `(L^{m+1})` by
`AmpleChern.selfIntersection_eq_slotIntegral` (algebraic flag length = Chern integral).

The mixed numbers `(L₁ ⋯ L_{m+1})` (coefficients of `χ(∑ mᵢLᵢ)`) are not covered: their
multilinearity is Snapper's theorem, formalized only on the the earlier envelope formalization side.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.BDivisor.Kleiman

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.NefMixedMass
open SGPT.Okounkov SGPT.Hodge.BDivChain.NativeDraft
  SGPT.Hodge.BDivChain.SourceNefIntersectionDraft SGPT.Hodge.BDivChain.SourceMixedOrderDraft

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
  [IsIntegral X] {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]
  [Nonempty (SchemeComplexPoint f)]

local instance snapperDiagonalTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance snapperDiagonalCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance snapperDiagonalManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)
local instance snapperDiagonalMeasurable : MeasurableSpace (SchemeComplexPoint f) := borel _
local instance snapperDiagonalBorel : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩

/-- **Snapper–Kleiman self-intersection = book product** (diagonal, ample, root model): a Weil
b-divisor over `X(ℂ)` realized on `X(ℂ)` by `c₁(L)`, `L` ample, has book self-product `(L^{m+1})`. -/
theorem nefIntersectionReal_eq_selfIntersection {L : X.Modules} (P : SGPT.LineBundle.AmplePolarization f L)
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m + 1) E L) :
    let := E.isSeparated
    let := E.quasiCompact
    let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    let : ConnectedSpace (SchemeComplexPoint f) :=
      SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E (m + 1)
    ∀ D : WeilFamilyAny (ModelSystem.blowup (m + 1) (SchemeComplexPoint f)),
      IsRealizationAny D ModelSystem.Model.root (H.chernClass a) →
      nefIntersectionReal (fun _ : Fin (m + 1) => D) = P.selfIntersection (m + 1) := by
  let := E.isSeparated
  let := E.quasiCompact
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : ConnectedSpace (SchemeComplexPoint f) :=
    SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E (m + 1)
  dsimp only
  intro D hD
  obtain ⟨K, hK⟩ := SGPT.LineBundle.AmpleChern.exists_positive_metric_of_amplePolarization
    f (m + 1) E P a
  let κ : KahlerBackground (m + 1) (SchemeComplexPoint f) := ⟨K.curvature a, hK⟩
  have hclass : H.chernClass a = RealBottChern.ofRepresentative (K.curvature a) :=
    H.chernClass_independent K a a
  have hr : ∀ _i : Fin (m + 1), IsRealizationAny D ModelSystem.Model.root
      (RealBottChern.ofRepresentative (K.curvature a)) := fun _ => hclass ▸ hD
  have hnef : ∀ _i : Fin (m + 1), NefWithRespectTo κ (K.curvature a) := fun _ =>
    nefWithRespectTo_of_semipositive κ (KahlerBackground.isSemipositive κ)
  have hp := nefIntersectionReal_of_common_nef_realization κ (fun _ => D)
    ModelSystem.Model.root κ (fun _ => K.curvature a) hr hnef
  rw [hp]
  exact (SGPT.LineBundle.AmpleChern.selfIntersection_eq_slotIntegral f E P a K κ).symm

end SGPT.BDivisor.Kleiman
