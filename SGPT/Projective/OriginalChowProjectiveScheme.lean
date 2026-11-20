import SGPT.Projective.OriginalChowSegreGraph
import SGPT.NAPotential.ProjectiveGraphEmbedding
import SGPT.NAPotential.GraphProjectiveIdealTrace
import SGPT.Foundations.Schemes.SchemeAnalyticSeparation

/-! TRUE original projective homogeneous quotient of the SAME Chow graph
equations and exact entire complex-point graph range. No source smoothness.
Blueprint: original-chow-projective-scheme.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set MvPolynomial
open SGPT.NAPotential.AlgPrimes3 SGPT.NAPotential.GraphProjectiveIdealTrace
open ProjectiveGraphProjectiveHomeomorph ProjectiveGraphAnalyticZero
open SGPT.GAGA.ChowBl SGPT.GAGA.H0S
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
attribute [local instance] MvPolynomial.gradedAlgebra

local instance chowProjectivePNTopology (N : ℕ) :
    TopologicalSpace (SchemeComplexPoint (polynomialProjStructureMap ℂ N)) :=
  schemeAnalyticPointTopology _

variable {N : ℕ} {μ : Type} (P : μ → MvPolynomial (Fin (N+1)) ℂ)
    (m : ℕ) (hP : ∀ k, (P k).IsHomogeneous m)

/-- The literal original span ideal, with homogeneity PROVED from its
actual generators. No radical, saturation or reduced replacement. -/
def originalChowHomogeneousIdeal : HomogeneousIdeal (homogeneousSubmodule (Fin (N+1)) ℂ) :=
  ⟨Ideal.span (range P), Ideal.homogeneous_span _ _ (by
    rintro q ⟨k,rfl⟩
    exact ⟨m,hP k⟩)⟩

/-- Genuine original projective scheme of the SAME homogeneous quotient. -/
def originalChowProjectiveScheme : Scheme :=
  Proj (GradedGraphQuotient.grading (homogeneousSubmodule (Fin (N+1)) ℂ)
    (originalChowHomogeneousIdeal P m hP).toIdeal)

/-- Actual original projective closed immersion, not only a point-set map. -/
def originalChowProjectiveInclusion : originalChowProjectiveScheme P m hP ⟶ polynomialProj ℂ N :=
  GradedGraphQuotient.quotientSchemeMap (homogeneousSubmodule (Fin (N+1)) ℂ)
    (originalChowHomogeneousIdeal P m hP)

instance originalChowProjectiveInclusion_closed : IsClosedImmersion (originalChowProjectiveInclusion P m hP) :=
  GradedGraphQuotient.instIsClosedImmersion_quotientSchemeMap _ _

/-- The genuine original structural map on this SAME whole quotient. -/
def originalChowStructureMap : originalChowProjectiveScheme P m hP ⟶ Spec (.of ℂ) :=
  originalChowProjectiveInclusion P m hP ≫ polynomialProjStructureMap ℂ N

/-- Actual closed projective embedding over the SAME original structural map. -/
def originalChowClosedEmbedding : ClosedProjectiveEmbedding (originalChowStructureMap P m hP) where
  ambientDimension := N
  map := originalChowProjectiveInclusion P m hP
  closedImmersion := inferInstance
  over_base := rfl

/-- The whole original quotient complex-point map into the ACTUAL original
projective manifold, using the proved genuine native/original homeomorphism. -/
def originalChowProjectivePoint (q : SchemeComplexPoint (originalChowStructureMap P m hP)) :
    ComplexProjectiveSpace N :=
  originalProjectiveHomeomorph N (schemeComplexPointMap (originalChowStructureMap P m hP)
    (polynomialProjStructureMap ℂ N) (originalChowProjectiveInclusion P m hP) rfl q)

/-- Exact ENTIRE original scheme complex-point image equals the literal
zeros of the SAME polynomial generators. No smoothness or reducedness input. -/
theorem range_originalChowProjectivePoint :
    range (originalChowProjectivePoint P m hP) =
      {z | ∀ k, MvPolynomial.eval z.rep (P k) = 0} := by
  have hr : range (originalChowProjectivePoint P m hP) =
      idealZeroLocus (originalChowHomogeneousIdeal P m hP).toIdeal := by
    change range ((originalProjectiveHomeomorph N) ∘
      schemeComplexPointMap (originalChowStructureMap P m hP) (polynomialProjStructureMap ℂ N)
        (originalChowProjectiveInclusion P m hP) rfl) = _
    rw [range_comp]
    refine (congrArg (fun S => (originalProjectiveHomeomorph N) '' S)
      (closedImmersionComplexPointMap_range (polynomialProjStructureMap ℂ N)
        (originalChowProjectiveInclusion P m hP))).trans ?_
    change (originalProjectiveHomeomorph N) ''
      {q | schemeComplexPointImage (polynomialProjStructureMap ℂ N) q ∈
        range (GradedGraphQuotient.quotientSchemeMap (homogeneousSubmodule (Fin (N+1)) ℂ)
          (originalChowHomogeneousIdeal P m hP))} = _
    rw [GradedGraphQuotient.range_quotientSchemeMap]
    ext z
    constructor
    · rintro ⟨q,hq,rfl⟩
      exact (originalProjectiveHomeomorph_mem_idealZeroLocus_iff N _ q).mpr hq
    · intro hz
      refine ⟨(originalProjectiveHomeomorph N).symm z,?_,Homeomorph.apply_symm_apply _ _⟩
      exact (inverse_mem_zeroLocus_iff N _ z).mpr hz
  rw [hr]
  ext z
  constructor
  · intro hz k
    exact hz (P k) (Ideal.subset_span ⟨k,rfl⟩)
  · intro hz q hq
    have hle : Ideal.span (range P) ≤ RingHom.ker (MvPolynomial.eval z.rep) := by
      apply Ideal.span_le.mpr
      rintro _ ⟨k,rfl⟩
      exact hz k
    exact hle hq

/-- Actual whole original algebraic graph is PRODUCED from true Chow data.
The FULL analytic cone ideal generators and exact graph-point range retain
the SAME equations used in the genuine original quotient scheme. -/
theorem exists_originalSegreGraph_algebraicScheme
    {n A B : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] [CompactSpace M]
    {Ψ : M → ComplexProjectiveSpace A} {Φ : M → ComplexProjectiveSpace B}
    (hΨ : IsHolomorphicEmbedding (n := n) Ψ) (hΦ : IsHolomorphicEmbedding (n := n) Φ) :
    ∃ (d : ℕ) (ι : Type) (_ : Fintype ι)
      (Q : ι → MvPolynomial (Fin (segreDim A B+1)) ℂ)
      (hQ : ∀ k, (Q k).IsHomogeneous d),
      (coneIdeal (range (fun x => segreMap (Ψ x) (Φ x)))).GeneratedOn
        (SGPT.GAGA.PN.puncture (SGPT.GAGA.PN.ConeSpace (segreDim A B)))
        (fun k => SGPT.GAGA.PN.polyTuple (Q k)) ∧
      range (originalChowProjectivePoint Q d hQ) = range (fun x => segreMap (Ψ x) (Φ x)) := by
  obtain ⟨d,hd⟩ := exists_originalSegreGraph_fullChowIdeal hΨ hΦ
  obtain ⟨ι,hι,Q,hQ,hgen,hzero⟩ := hd d le_rfl
  exact ⟨d,ι,hι,Q,hQ,hgen,(range_originalChowProjectivePoint Q d hQ).trans hzero.symm⟩

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
