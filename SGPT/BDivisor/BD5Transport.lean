import SGPT.BDivisor.BD3SnapperNef
import SGPT.Projective.ActualDiffeomorphSlotIntegral

/-!
# the book's product is Dang–Favre's number on every algebraized model

Source: `rmk:bdiv:L749` (chapter_bdiv.tex, line 749).  Lane BD3 identified the book's product
(`def:DF_ext`, `nefIntersectionReal`) with Dang–Favre's Snapper–Kleiman numbers for b-divisors
determined on the ROOT model `X(ℂ)` of an integral smooth projective complex scheme `X`.  Dang–Favre
compute the intersection number of Cartier b-divisors determined on a model `Y` on the algebraic
model `Y`.  Here, for every model `π : Y → X(ℂ)` of the book's blow-up system together with an
algebraization of `Y`, i.e. a smooth projective complex scheme `V` and a biholomorphism
`e : V(ℂ) ≃ Y`, the book's product of b-divisors realized on `Y` by (nef representatives of) the
images of real Cartier classes `vᵢ = ∑_A vᵢ(A) [A]` of `V` is Dang–Favre's (multilinearly extended
Snapper–Kleiman) number of the `vᵢ` on `V`:

* `nefIntersectionReal_eq_originalRealMixedEuler_of_diffeomorph_bd5`.

The proof: the book's product is the classical intersection number on `Y` of any common nef
realization (`nefIntersectionReal_of_common_nef_realization`); a holomorphic diffeomorphism
preserves slot integrals (`slotIntegral_pullback_actualDiffeomorph`), which only depend on the
Bott–Chern classes (`slotIntegral_eq_of_bottChernRel`); on `V(ℂ)` the slot integral of the Chern
forms is the Snapper–Kleiman number (`originalRealMixedEuler_eq_slotIntegral_bd3`, lane BD3).
The existence of the algebraization `(V, e)` for every model is `BD5Algebraization`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Okounkov SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses NefMixedMass
open SGPT.Hodge.BDivChain.NativeDraft SGPT.Hodge.BDivChain.SourceNefIntersectionDraft
open SGPT.Hodge.BDivChain.SourceMixedOrderDraft
open scoped Manifold ContDiff

local instance bd5TransportTopology {Y : Scheme.{0}} (h : Y ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint h) := schemeAnalyticPointTopology h
local instance bd5TransportCharts {Y : Scheme.{0}} (h : Y ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d h] : ChartedSpace (ComplexModel d) (SchemeComplexPoint h) :=
  schemeAnalyticTNChartedSpace h d
local instance bd5TransportManifold {Y : Scheme.{0}} (h : Y ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d h] [IsSeparated h] [QuasiCompact h] :
    IsComplexManifold d (SchemeComplexPoint h) := schemeAnalyticTN_isComplexManifold h d

section Transport

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
  [IsIntegral X] {k : ℕ} [SmoothOfRelativeDimension (k + 1) f]
  [Nonempty (SchemeComplexPoint f)]
  {V : Scheme.{0}} (g : V ⟶ Spec (.of ℂ)) (EV : ClosedProjectiveEmbedding g)
  [SmoothOfRelativeDimension (k + 1) g]

/-- **Book product = Dang–Favre number on every algebraized model (EP-free).**  Let `X` be an
integral scheme, smooth projective of dimension `k + 1` over `ℂ`, and `π : Y → X(ℂ)` a model of
the book's blow-up system.  Let `V` be a smooth projective complex scheme of dimension `k + 1` and
`e : V(ℂ) ≃ Y` a biholomorphism (an algebraization of `Y`).  Let `vᵢ` be real combinations of line
bundles of `V` (real Cartier classes, `θᵢ^V = ∑_A vᵢ(A) c₁(A, K_A)` for any smooth metrics `K_A`),
and `θᵢ` closed real `(1,1)`-forms on `Y`, nef with respect to a Kähler form of `Y`, with
`e^*{θᵢ} = {θᵢ^V}`.  Then for Weil b-divisors `Dᵢ` over `X(ℂ)` realized on `Y` by `{θᵢ}`, the
book's product `(D₀, …, D_k)` is Dang–Favre's number of the classes `vᵢ` on `V`, the real
multilinear extension of the Snapper–Kleiman numbers (for any base line bundle `B`). -/
theorem nefIntersectionReal_eq_originalRealMixedEuler_of_diffeomorph_bd5
    (K : ∀ A : IntrinsicLineBundle V, SchemeLineBundleMetric g (k + 1) EV A.sheaf)
    (B : IntrinsicLineBundle V) (v : Fin (k + 1) → IntrinsicLineBundle V →₀ ℝ) :
    let := E.isSeparated
    let := E.quasiCompact
    let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    let : ConnectedSpace (SchemeComplexPoint f) :=
      SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E (k + 1)
    let := EV.isSeparated
    let := EV.quasiCompact
    ∀ (π : (SGPT.BDivisor.ModelSystem.blowup (k + 1) (SchemeComplexPoint f)).Model)
      (e : SchemeComplexPoint g ≃ₘ⟮𝓘(ℂ, ComplexModel (k + 1)), 𝓘(ℂ, ComplexModel (k + 1))⟯
        π.1.carrier)
      (κ : KahlerBackground (k + 1) π.1.carrier)
      (θ : Fin (k + 1) → ClosedRealOneOneForm (k + 1) π.1.carrier),
      (∀ i, NefWithRespectTo κ (θ i)) →
      (∀ i, RealBottChern.ofRepresentative (ClosedRealOneOneForm.pullback e.contMDiff (θ i)) =
        RealBottChern.ofRepresentative (Finsupp.linearCombination ℝ
          (fun A : IntrinsicLineBundle V => (K A).curvature A.atlas) (v i))) →
      ∀ D : Fin (k + 1) →
          WeilFamilyAny (SGPT.BDivisor.ModelSystem.blowup (k + 1) (SchemeComplexPoint f)),
        (∀ i, IsRealizationAny (D i) π (RealBottChern.ofRepresentative (θ i))) →
        nefIntersectionReal D = originalRealMixedEuler g EV (k + 1) B v := by
  let := E.isSeparated
  let := E.quasiCompact
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : ConnectedSpace (SchemeComplexPoint f) :=
    SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E (k + 1)
  let := EV.isSeparated
  let := EV.quasiCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  let : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  dsimp only
  intro π e κ θ hnef hclass D hD
  have hp := nefIntersectionReal_of_common_nef_realization
    (SGPT.Okounkov.schemeProjectiveTNKahlerBackground f (k + 1) E) D π κ θ hD hnef
  rw [hp]
  let : CompactSpace (SchemeComplexPoint g) := EV.analyticCompact
  let : MeasurableSpace (SchemeComplexPoint g) := borel _
  let : BorelSpace (SchemeComplexPoint g) := ⟨rfl⟩
  let : MeasurableSpace π.1.carrier := borel _
  let : BorelSpace π.1.carrier := ⟨rfl⟩
  let : CompactSpace π.1.carrier := e.toHomeomorph.compactSpace
  -- a Kähler form on `V(ℂ)`: the Fubini–Study form of the projective embedding
  let κV : KahlerBackground (k + 1) (SchemeComplexPoint g) :=
    SGPT.Okounkov.schemeProjectiveTNKahlerBackground g (k + 1) EV
  have h1 : modelSlotIntegral π κ θ = slotIntegral κ θ := rfl
  rw [h1, ← slotIntegral_pullback_actualDiffeomorph e κ κV θ]
  rw [SGPT.Hodge.BDivChain.SourceMixedOrderDraft.slotIntegral_eq_of_bottChernRel κV _
    (fun i => Finsupp.linearCombination ℝ
      (fun A : IntrinsicLineBundle V => (K A).curvature A.atlas) (v i))
    (fun i => (RealBottChern.ofRepresentative_eq_iff _ _).mp (hclass i))]
  exact (originalRealMixedEuler_eq_slotIntegral_bd3 k g EV B K κV v).symm

end Transport

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
