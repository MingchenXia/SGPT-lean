import SGPT.BDivisor.BD7IntegralNumericalQuotient
import SGPT.Okounkov.OF14AbhyankarZero
import SGPT.Hodge.SourceNefIntersection

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Okounkov SGPT.BDivisor
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Hodge.BDivChain.NativeDraft SGPT.Hodge.BDivChain.SourceNefIntersectionDraft

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))
    (E : ClosedProjectiveEmbedding f)

private def rankZeroValuation (K : Type*) [Field K] :
    AddValuation K (WithTop (Lex (Fin 0 → ℤ))) := by
  classical
  refine AddValuation.of (fun x => if x = 0 then ⊤ else 0) (by simp) (by simp) ?_ ?_
  · intro x y
    by_cases hx : x = 0
    · simp [hx]
    by_cases hy : y = 0
    · simp [hy]
    by_cases hz : x + y = 0 <;> simp [hx, hy, hz]
  · intro x y
    by_cases hx : x = 0
    · simp [hx]
    by_cases hy : y = 0
    · simp [hy]
    simp [hx, hy, mul_ne_zero hx hy]

include E in
private theorem originalStructure_isIso_of_dim_zero_bd7
    (hdim : let := schemeFunctionFieldAlgebra f; Algebra.trdeg ℂ X.functionField = 0) :
    IsIso f := by
  let : IsSeparated f := E.isSeparated
  let : QuasiCompact f := E.quasiCompact
  let : LocallyOfFiniteType f := E.locallyOfFiniteType
  obtain ⟨_, hf, _⟩ := SGPT.Okounkov.OF14.exists_identity_admissibleFlag_lexEquivalent_dim_zero
    f E hdim (rankZeroValuation X.functionField)
  exact hf

/-- The actual algebraic numerical quotient is zero. Any integral closed
subscheme of the original point scheme is itself the complex point. -/
theorem originalIntegralCurveDegreeRelations_eq_top_of_dim_zero_bd7
    (hdim : let := schemeFunctionFieldAlgebra f; Algebra.trdeg ℂ X.functionField = 0) :
    originalIntegralCurveDegreeRelations_bd7 f E = ⊤ := by
  let : IsIso f := originalStructure_isIso_of_dim_zero_bd7 f E hdim
  apply top_unique
  intro v _
  apply (mem_originalIntegralCurveDegreeRelations_iff_bd7 f E v).2
  intro C _
  have hC : IsClosedImmersion C.structureMap := by
    rw [← C.over_base]
    have : IsClosedImmersion C.inclusion := C.closed
    infer_instance
  have hpoint : Subsingleton (Spec (.of ℂ)) :=
    PrimeSpectrum.subsingleton_iff_isField_of_isReduced.mpr (Field.toIsField ℂ)
  have : Surjective C.structureMap := ⟨fun y =>
    ⟨genericPoint C.source, hpoint.elim _ y⟩⟩
  have : IsIso C.structureMap := isIso_of_isClosedImmersion_of_surjective _
  have : SmoothOfRelativeDimension 0 C.structureMap := inferInstance
  have htr := nativeSmoothFunctionField_trdeg C.structureMap 0
  have h := htr.symm.trans C.dimension
  exact (by norm_num at h : False).elim

theorem originalIntegralCurveDegreeQuotient_subsingleton_of_dim_zero_bd7
    (hdim : let := schemeFunctionFieldAlgebra f; Algebra.trdeg ℂ X.functionField = 0) :
    Subsingleton (OriginalIntegralCurveDegreeQuotient_bd7 f E) := by
  exact Submodule.Quotient.subsingleton_iff.mpr
    (originalIntegralCurveDegreeRelations_eq_top_of_dim_zero_bd7 f E hdim)

/-- The algebra length of the original zero-dimensional integral projective
scheme. This is its ordinary degree over the complex point. -/
def originalEmptyTopDegree_bd7 : ℕ :=
  let φ := (Scheme.ΓSpecIso (.of ℂ)).inv ≫ f.appTop
  let := φ.hom.toAlgebra
  Module.finrank ℂ Γ(X, ⊤)

include E in
theorem originalEmptyTopDegree_eq_one_of_dim_zero_bd7
    (hdim : let := schemeFunctionFieldAlgebra f; Algebra.trdeg ℂ X.functionField = 0) :
    originalEmptyTopDegree_bd7 f = 1 := by
  let : IsIso f := originalStructure_isIso_of_dim_zero_bd7 f E hdim
  let φ := (Scheme.ΓSpecIso (.of ℂ)).inv ≫ f.appTop
  let : Algebra ℂ Γ(X, ⊤) := φ.hom.toAlgebra
  have hφ : IsIso φ := inferInstance
  let e := AlgEquiv.ofBijective (Algebra.ofId ℂ Γ(X, ⊤))
    (ConcreteCategory.bijective_of_isIso φ)
  change Module.finrank ℂ Γ(X, ⊤) = 1
  rw [← e.toLinearEquiv.finrank_eq, Module.finrank_self]

include E in
/-- The ordinary degree of the actual point scheme is the empty analytic
top product. The tuple has no slots, so the analytic value is independent of
the presentation of that point. -/
theorem originalEmptyTopDegree_eq_nefIntersection_of_dim_zero_bd7
    (hdim : let := schemeFunctionFieldAlgebra f; Algebra.trdeg ℂ X.functionField = 0)
    {T : Type} [TopologicalSpace T] [ChartedSpace (ComplexModel 0) T]
    [IsComplexManifold 0 T] [CompactSpace T] [ConnectedSpace T]
    (D : Fin 0 → WeilFamilyAny (ModelSystem.blowup 0 T)) :
    (originalEmptyTopDegree_bd7 f : ℝ) = (nefIntersection D).toReal := by
  rw [originalEmptyTopDegree_eq_one_of_dim_zero_bd7 f E hdim, source_nefIntersection_dim_zero D]
  norm_num

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
