import SGPT.Okounkov.OF14Normal
import SGPT.Unibranch.RIsoAModification
import SGPT.Unibranch.HironakaG1NativeModificationIsoTransport

/-! The OF14 admissible flag lies on an intrinsic smooth-centre modification
whenever the supplied initial resolution is itself such a modification. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace SGPT.Okounkov.OF14

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set
open SGPT.Unibranch SGPT.Unibranch.SourceReducedComplexSpace
open SGPT.Unibranch.OriginalNativeModification SGPT.Unibranch.SmoothCentreModification
open SGPT.Okounkov SGPT.Okounkov.OF9 SGPT.Okounkov.OF5 SGPT.Okounkov.OF6 SGPT.Okounkov.ValCurr
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open scoped Topology Manifold ContDiff

local instance schemePointTopology {A : Scheme.{0}} (g : A ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint g) := schemeAnalyticPointTopology g

local instance schemePointCharts {A : Scheme.{0}} (g : A ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n g] : ChartedSpace (ComplexModel n) (SchemeComplexPoint g) :=
  schemeAnalyticTNChartedSpace g n

local instance schemePointManifold {A : Scheme.{0}} (g : A ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n g] [IsSeparated g] [QuasiCompact g] :
    IsComplexManifold n (SchemeComplexPoint g) := schemeAnalyticTN_isComplexManifold g n

private def wholeModelIsoOfDiffeomorph {n : ℕ} {M N : Type}
    [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    [TopologicalSpace N] [ChartedSpace (ComplexModel n) N] [IsComplexManifold n N]
    (e : M ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ N) :
    wholeModel (n := n) M ≅ wholeModel (n := n) N where
  hom := nativeMorphism e.contMDiff
  inv := nativeMorphism e.symm.contMDiff
  hom_inv_id := by
    apply morphism_eq_of_pointwise_eq
    intro z
    apply Subtype.ext
    exact e.symm_apply_apply z.val
  inv_hom_id := by
    apply morphism_eq_of_pointwise_eq
    intro z
    apply Subtype.ext
    exact e.apply_symm_apply z.val

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))
  [IsSeparated f] [QuasiCompact f] [LocallyOfFiniteType f] {m : ℕ}

/-- Over an initial resolution that is an intrinsic smooth-centre modification, a surjective
valuation is equivalent to the valuation of an admissible flag on a single intrinsic modification
with smooth projective algebraic source. The field pullback is read through the actual tower
projection on meromorphic germs. -/
theorem exists_admissibleFlag_lexEquivalent_of_intrinsic_resolution
    (R : OF12.Resolution f m) (hR : IsModification R.π)
    (ν : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ))))
    (hν : Function.Surjective ν) :
    ∃ (Y : Type) (_ : TopologicalSpace Y) (_ : ChartedSpace (ComplexModel (m + 1)) Y)
      (_ : IsComplexManifold (m + 1) Y) (π : Y → SchemeComplexPoint R.fY)
      (hseq : IsBlowupSequence (m + 1) (SchemeComplexPoint R.fY) Y π)
      (V : Scheme.{0}) (_ : IsIntegral V) (g : V ⟶ Spec (.of ℂ))
      (hsm : SmoothOfRelativeDimension (m + 1) g) (EV : ClosedProjectiveEmbedding g),
      letI := hsm
      letI := EV.isSeparated
      letI := EV.quasiCompact
      ∃ (φ : SchemeComplexPoint g ≃ₘ⟮𝓘(ℂ, ComplexModel (m + 1)), 𝓘(ℂ, ComplexModel (m + 1))⟯ Y)
        (e : R.Y.functionField ≃+* V.functionField)
        (p : OF12.smoothModel g (m + 1) ⟶ UnibAn.analytification f),
        IsModification p ∧
        (∀ v : SchemeComplexPoint g,
          UnibAn.pointMap f (p.hom.left.base ⟨v, mem_univ v⟩) =
            schemeComplexPointMap R.fY f R.ρ R.comp_eq (π (φ v))) ∧
        (∀ (q : R.Y.functionField) (v : SchemeComplexPoint g),
          schemeNativeFunctionFieldGerm g (m + 1) v (e q) =
            fracComap (OF13.isAnalyticModification_of_diffeomorph φ) v
              (ratGerm R.fY (HironakaChowLemma.isAnalyticModification_of_isBlowupSequence hseq)
                (φ v) q)) ∧
        ∃ (Yf : Fin (m + 1 + 1) → Set V) (hY : IsAdmissibleFlag g (m + 1) Yf),
          ValuationsLexEquivalent
            ((admissibleFlagValuation hY).comap (R.φ.trans e).toRingHom) ν := by
  obtain ⟨Y, tY, cY, mY, π, hseq, V, hV, g, hsm, EV, hrest⟩ :=
    exists_admissibleFlag_lexEquivalent_of_resolution f R ν hν
  let := tY
  let := cY
  let := mY
  let := hsm
  let := EV.isSeparated
  let := EV.quasiCompact
  obtain ⟨φ, e, he, Yf, hY, hlex⟩ := hrest
  obtain ⟨q, hq, hqPoint⟩ := RIsoAModification.isModification_of_isBlowupSequence hseq
  let I := wholeModelIsoOfDiffeomorph φ
  let p : OF12.smoothModel g (m + 1) ⟶ UnibAn.analytification f := (I.hom ≫ q) ≫ R.π
  have hp : IsModification p :=
    (HironakaG1NativeModificationIsoTransport.isModification_precomp_iso hq I).comp hR
  refine ⟨Y, tY, cY, mY, π, hseq, V, hV, g, hsm, EV, φ, e, p, hp, ?_, he, Yf, hY, hlex⟩
  intro v
  let a := I.hom.hom.left.base ⟨v, mem_univ v⟩
  let b := q.hom.left.base a
  change UnibAn.pointMap f (R.π.hom.left.base b) = _
  have hb : b.val = π (φ v) := hqPoint a
  exact (R.point_eq b.val).trans (congrArg (schemeComplexPointMap R.fY f R.ρ R.comp_eq) hb)

end SGPT.Okounkov.OF14
