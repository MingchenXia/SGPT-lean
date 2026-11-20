import SGPT.Okounkov.OF12IntrinsicProjectiveStage
import SGPT.Okounkov.OF14IntrinsicModification
import SGPT.Unibranch.AmbientModificationTower
import SGPT.Unibranch.EmbeddedSmoothCentreStep
import SGPT.Unibranch.EmbeddedSmoothTerminalProjective
import SGPT.Unibranch.KS3KahlerResolution
import SGPT.Unibranch.UnibAnNativeProjectiveReducedComparison

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Okounkov.OF14

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set
open SGPT.GAGA.H0S SGPT.Projective
open SGPT.Unibranch SGPT.Unibranch.SourceReducedComplexSpace
open SGPT.Unibranch.OriginalNativeModification SGPT.Unibranch.SmoothCentreModification
open SGPT.Unibranch.AmbientModificationTower
open SGPT.Okounkov.OF5 SGPT.Okounkov.OF6 SGPT.Okounkov.OF9 SGPT.Okounkov.ValCurr
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.BlowupTowers
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open scoped Manifold ContDiff

attribute [local instance] MvPolynomial.gradedAlgebra SGPT.Toric.monomialProjectiveTopology

local instance assemblyPointTopology {B : Scheme.{0}} (g : B ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint g) := schemeAnalyticPointTopology g

local instance assemblyPointCharts {B : Scheme.{0}} (g : B ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n g] : ChartedSpace (ComplexModel n) (SchemeComplexPoint g) :=
  schemeAnalyticTNChartedSpace g n

local instance assemblyPointManifold {B : Scheme.{0}} (g : B ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n g] [IsSeparated g] [QuasiCompact g] :
    IsComplexManifold n (SchemeComplexPoint g) := schemeAnalyticTN_isComplexManifold g n

variable {X : Scheme.{0}} [IsIntegral X] {f : X ⟶ Spec (.of ℂ)}
  [IsSeparated f] [QuasiCompact f] [LocallyOfFiniteType f] {m : ℕ}

/-- Produce a smooth projective algebraic resolution whose actual analytic map
is a finite smooth-centre modification of the original base. -/
theorem exists_intrinsic_resolution_of_normalProjective
    (E : ClosedProjectiveEmbedding f)
    (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hdim : letI := schemeFunctionFieldAlgebra f
      Algebra.trdeg ℂ X.functionField = (m + 1 : ℕ)) :
    ∃ R : OF12.Resolution f m, IsModification R.π ∧ IsIso (R.ρ.stalkMap (genericPoint R.Y)) := by
  let n := E.ambientDimension
  let g := polynomialProjStructureMap ℂ n
  let P := SGPT.NAPotential.AlgPrimes3.ProjectiveGraphProjectivePoint.identityEmbedding n
  let : IsSeparated g := P.isSeparated
  let : QuasiCompact g := P.quasiCompact
  let : LocallyOfFiniteType g := P.locallyOfFiniteType
  let : SmoothOfRelativeDimension n g := inferInstanceAs
    (SmoothOfRelativeDimension n (polynomialProjStructureMap ℂ n))
  let : TopologicalSpace (SchemeComplexPoint g) := schemeAnalyticPointTopology g
  let : ChartedSpace (ComplexModel n) (SchemeComplexPoint g) := schemeAnalyticTNChartedSpace g n
  let : IsComplexManifold n (SchemeComplexPoint g) := schemeAnalyticTN_isComplexManifold g n
  let A : CMfd.{0} n := CMfd.of (SchemeComplexPoint g)
  let : CompactSpace A := P.analyticCompact
  let : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have hcompact : CompactSpace (UnibAn.analytification f).obj.left :=
    (UnibAn.pointHomeomorph f).symm.compactSpace
  obtain ⟨hC, e, -⟩ := UnibAn.exists_projectiveAnalytification_iso_nativeReducedImage f E
  let j : UnibAn.analytification f ⟶ wholeModel (n := n) A :=
    e.hom ≫ OriginalClosedSubspaceFactorization.inclusion hC
      isComplexAnalyticSubset_univ (Set.subset_univ _)
  have hj : IsClosedReducedEmbedding (A := A) j := ⟨_, hC, e, rfl⟩
  have step : AmbientStepBridge n := by
    intro A B C j hj p hp
    exact exists_certified_ambientStep_of_isSmoothCentreStep A j hj p hp
  obtain ⟨Y, p, A', T, j', hp, hres, hj', hcomm, hc, N', Ψ', hΨ'⟩ :=
    exists_resolution_in_projectiveAmbientTower step (isHolomorphicEmbedding_projectivePoint g P n)
      (UnibAn.analytification f) hcompact j hj
  let : CompactSpace A' := hc
  let : CompactSpace (UnibAn.analytification f).obj.left := hcompact
  let : CompactSpace Y.obj.left := hp.source_compact
  let := OF12.connectedSpace_projective_analytification f E
  let : ConnectedSpace Y.obj.left := KS3KahlerResolution.connectedSpace_of_isProperBimeromorphic
    hres.2 (OF12.isUnibranch_analytification_of_normal f hX)
  obtain ⟨d, M, eM, hM, hΦ⟩ :=
    exists_projectivelyEmbedded_nativeManifold_of_smooth_terminal hΨ' hres.1 j' hj'
  let : CompactSpace M := hM
  exact OF12.exists_intrinsic_resolution_of_projective_stage_of_modification E hX (d := d)
    hdim _ hΦ (eM.hom ≫ p)
    (HironakaG1NativeModificationIsoTransport.isModification_precomp_iso hp eM)

/-- The book's finite native modification and admissible flag, with the full
germ pullback identity retained on the same terminal projection. -/
theorem exists_admissibleFlag_lexEquivalent_of_normalProjective
    (E : ClosedProjectiveEmbedding f)
    (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hdim : letI := schemeFunctionFieldAlgebra f
      Algebra.trdeg ℂ X.functionField = (m + 1 : ℕ))
    (ν : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ))))
    (hν : Function.Surjective ν) :
    ∃ (R : OF12.Resolution f m) (_ : IsModification R.π)
      (Y : Type) (_ : TopologicalSpace Y) (_ : ChartedSpace (ComplexModel (m + 1)) Y)
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
  obtain ⟨R, hR, -⟩ := exists_intrinsic_resolution_of_normalProjective E hX hdim
  exact ⟨R, hR, exists_admissibleFlag_lexEquivalent_of_intrinsic_resolution f R hR ν hν⟩

end SGPT.Okounkov.OF14
