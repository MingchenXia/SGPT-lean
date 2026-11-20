import SGPT.BDivisor.BD7Models
import SGPT.BDivisor.BD7NumericalInverseLimit

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.BDivisor.BD7

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes MeasureTheory
open SGPT.Okounkov SGPT.Okounkov.OF13
open SGPT.BDivisor.DangFavre SGPT.BDivisor.DFAlg
open SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open CanonicalCurrentFrame SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Hodge.BDivChain.NativeDraft SGPT.Hodge.BDivChain.SourceNefIntersectionDraft
open SGPT.Hodge.BDivChain.SourceMixedOrderDraft
open scoped Manifold ContDiff

local instance commonMixedTopology {V : Scheme.{0}} (g : V ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint g) := schemeAnalyticPointTopology g

local instance commonMixedChart {V : Scheme.{0}} (g : V ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n g] :
    ChartedSpace (ComplexModel n) (SchemeComplexPoint g) := schemeAnalyticTNChartedSpace g n

local instance commonMixedManifold {V : Scheme.{0}} (g : V ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n g] [IsSeparated g] [QuasiCompact g] :
    IsComplexManifold n (SchemeComplexPoint g) := schemeAnalyticTN_isComplexManifold g n

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))
    (E : ClosedProjectiveEmbedding f) {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]
    [IsSeparated f] [QuasiCompact f] [CompactSpace (SchemeComplexPoint f)]
    [ConnectedSpace (SchemeComplexPoint f)]

local notation "Sys" => ModelSystem.blowup (m + 1) (SchemeComplexPoint f)

variable (alg : ∀ π : BookBlowupModel (f := f) (d := m + 1),
  BookModelAlgebraization (f := f) (d := m + 1) π)

include E in
/-- On the exact algebraization of the chosen common nef realization, the
original Cartier representatives give the ordinary mixed top degree. The
hypothesis is just equality of numerical incarnations under the Chern map. -/
theorem commonNefRealization_intersection_eq_originalMixedDegree_bd7
    {C : Fin (m + 1) → WeilFamilyAny Sys} (r : CommonNefRealization C)
    (B : IntrinsicLineBundle (alg r.model).A.V)
    (v : Fin (m + 1) → CartierCombinations (alg r.model).A.V)
    (hC : let A := (alg r.model).A
      ∀ i, (bookModelNumericalChern alg r.model
        ((originalIntegralCurveDegreeRelations_bd7 (A.p ≫ f) A.embedding).mkQ (v i))).val =
        (C i).val r.model) :
    r.intersection = originalRealMixedEuler ((alg r.model).A.p ≫ f)
      (alg r.model).A.embedding (m + 1) B v := by
  let A := (alg r.model).A
  let g := A.p ≫ f
  let EG := A.embedding
  let : IsIntegral A.V := A.integral
  let : SmoothOfRelativeDimension (m + 1) g := A.smooth
  let : IsSeparated g := EG.isSeparated
  let : QuasiCompact g := EG.quasiCompact
  let : CompactSpace (SchemeComplexPoint g) := EG.analyticCompact
  let : ConnectedSpace (SchemeComplexPoint g) := smoothProjectiveNativeConnected g (m + 1) EG
  let e := (alg r.model).e
  let K (L : IntrinsicLineBundle A.V) := schemeLineBundleMetric g (m + 1) EG L.atlas
  have hreal (i : Fin (m + 1)) :
      (C i).val r.model = RealBottChern.ofRepresentative (r.form i) := by
    rw [r.realizes i r.model le_rfl, Modification.classPullbackOfLE_refl]
  have hclass (i : Fin (m + 1)) :
      RealBottChern.ofRepresentative (ClosedRealOneOneForm.pullback e.contMDiff (r.form i)) =
        RealBottChern.ofRepresentative (Finsupp.linearCombination ℝ
          (fun L : IntrinsicLineBundle A.V => (K L).curvature L.atlas) (v i)) := by
    let α := RealBottChern.ofRepresentative (r.form i)
    let γ := (integralNumericalEquivNS_bd7 g EG m normalizationProjectiveForCurves_bd7)
      ((originalIntegralCurveDegreeRelations_bd7 g EG).mkQ (v i))
    have hα : α ∈ neronSeveri (m + 1) r.model.1.carrier := by
      change RealBottChern.ofRepresentative (r.form i) ∈ _
      rw [← hreal i, ← hC i]
      exact (bookModelNumericalChern alg r.model
        ((originalIntegralCurveDegreeRelations_bd7 g EG).mkQ (v i))).property
    let β : neronSeveri (m + 1) (SchemeComplexPoint g) :=
      ⟨classPullback e.contMDiff α, classPullback_mem_neronSeveri_diffeomorph e hα⟩
    have hβ : β = γ := by
      apply (neronSeveriDiffeoEquiv e).injective
      apply Subtype.ext
      change classPushforward (isAnalyticModification_of_diffeomorph e).1
        (canonicalBasis (m + 1)) (Nat.succ_pos m) (classPullback e.contMDiff α) =
          (bookModelNumericalChern alg r.model
            ((originalIntegralCurveDegreeRelations_bd7 g EG).mkQ (v i))).val
      rw [hC i, hreal i]
      exact classPushforward_classPullback (isAnalyticModification_of_diffeomorph e)
        (Nat.succ_pos m) α
    rw [← classPullback_ofRepresentative, ofRepresentative_linearCombination g m]
    exact (congrArg Subtype.val hβ).trans
      (numericalChern_mkQ g EG normalizationProjectiveForCurves_bd7 (v i))
  have hEuler := nefIntersectionReal_eq_originalRealMixedEuler_of_diffeomorph_bd5
    f E g EG K B v r.model e r.kahler r.form r.nef hclass C r.realizes
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  let : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  exact (nefIntersectionReal_of_common_nef_realization
    (schemeProjectiveTNKahlerBackground f (m + 1) E) C r.model r.kahler r.form r.realizes r.nef).symm.trans
      hEuler

end SGPT.BDivisor.BD7
