import SGPT.Projective.SourceSimplexCoordinateSections
import SGPT.Projective.SourceHolomorphicSectionPullback

/-! Genuine native coordinate sections of the independent projective O(1). -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Bergman.NativeKodairaPullback
open Bundle Set
open SGPT.Toric SGPT.Toric.F1IntersectionDraft
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.QuantizationDraft
open SGPT.Bergman.AnalyticSectionProducts
open HermitianHolomorphicLineBundle SGPT.Projective
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff BigOperators

/-- Actual original projective coordinate section of the independent native
hyperplane bundle, by genuine holomorphic pullback of the actual Cartier
monomial section. No source bundle/family or chosen H0 model is an input. -/
def sourceProjectiveCoordinateNativeSection (N : ℕ) (i : Fin (N+1)) :
    HolomorphicSections (n := N) (sourceProjectiveHyperplaneBundle N).Fiber :=
  sourceNativeHolomorphicSectionPullback
    (toricNativeHermitianLineBundle (sourceSimplexHyperplaneMetric N))
    (sourceProjectiveSimplexInverseMap N) (sourceSimplexCoordinateNativeSection N i)

/-- Literal native physical coordinate-section value. -/
theorem sourceProjectiveCoordinateNativeSection_apply (N : ℕ) (i : Fin (N+1))
    (p : ComplexProjectiveSpace N) :
    sourceProjectiveCoordinateNativeSection N i p =
      sourceSimplexCoordinateNativeSection N i (sourceProjectiveSimplexInverseMap N p) := rfl

/-- The independent actual projective coordinate sections generate every
actual hyperplane fiber, including target dimension zero. -/
theorem sourceProjectiveCoordinateNativeSection_generating (N : ℕ) :
    ∀ p : ComplexProjectiveSpace N, ∃ i : Fin (N+1),
      sourceProjectiveCoordinateNativeSection N i p ≠ 0 :=
  fun p => sourceSimplexCoordinateNativeSection_generating N (sourceProjectiveSimplexInverseMap N p)

/-- The ACTUAL map of the actual independent O(1) coordinate family is the
identity on the original canonical projective space, at every point. -/
theorem sourceProjectiveCoordinateNativeSection_projectiveMap_identity (N : ℕ)
    (p : ComplexProjectiveSpace N) :
    sourceNativeFiniteSectionProjectiveMap (sourceProjectiveHyperplaneBundle N)
      (sourceProjectiveCoordinateNativeSection N) (sourceProjectiveCoordinateNativeSection_generating N) p = p := by
  change sourceNativeFiniteSectionProjectiveMap
    (nativeHolomorphicPullbackBundle
      (toricNativeHermitianLineBundle (sourceSimplexHyperplaneMetric N)) (sourceProjectiveSimplexInverseMap N))
    (fun i => sourceNativeHolomorphicSectionPullback
      (toricNativeHermitianLineBundle (sourceSimplexHyperplaneMetric N))
      (sourceProjectiveSimplexInverseMap N) (sourceSimplexCoordinateNativeSection N i)) _ p = p
  rw [sourceNativeFiniteFamily_projectiveMap_pullback _ _ _
    (sourceSimplexCoordinateNativeSection_generating N)]
  rw [sourceSimplexCoordinateNativeSection_projectiveMap_eq_simplex]
  exact (simplexProjectiveHomeomorph (simplex_edgeSmooth (N := N))).apply_symm_apply p

/-- The actual native hyperplane section attached to a genuine homogeneous
complex-linear form, expressed in the original actual coordinate sections. -/
def sourceProjectiveNativeLinearFormSection (N : ℕ) (a : Fin (N+1) → ℂ) :
    HolomorphicSections (n := N) (sourceProjectiveHyperplaneBundle N).Fiber :=
  ∑ i, a i • sourceProjectiveCoordinateNativeSection N i

/-- Exact physical fiber evaluation of the original native linear form. -/
theorem sourceProjectiveNativeLinearFormSection_apply (N : ℕ) (a : Fin (N+1) → ℂ)
    (p : ComplexProjectiveSpace N) :
    sourceProjectiveNativeLinearFormSection N a p =
      ∑ i, a i • sourceProjectiveCoordinateNativeSection N i p := by
  let ev : HolomorphicSections (n := N) (sourceProjectiveHyperplaneBundle N).Fiber →ₗ[ℂ]
      (sourceProjectiveHyperplaneBundle N).Fiber p :=
    { toFun t := t p
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  change ev (∑ i, a i • sourceProjectiveCoordinateNativeSection N i) =
    ∑ i, a i • ev (sourceProjectiveCoordinateNativeSection N i)
  simp only [map_sum, map_smul]

end SGPT.Bergman.NativeKodairaPullback
