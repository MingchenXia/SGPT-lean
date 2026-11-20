import SGPT.BDivisor.GMMorphism
import SGPT.Okounkov.OF14Integral
import SGPT.Okounkov.SchemeNativeAnalyticSubset
import SGPT.NAPotential.ProjectiveGraphProjectivePoint
import SGPT.Foundations.Schemes.NativeFanoAlgebraicFiniteness
import SGPT.Projective.OriginalChowProjectiveScheme
import SGPT.Foundations.Schemes.SchemeAnalyticSeparation

/-! The algebraic trace of an ambient analytic subset and the irreducibility of an
integral projective scheme's analytic image. Smoothness of the embedded scheme is unnecessary. -/

set_option autoImplicit false

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace SGPT.Okounkov.OF12

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set
open SGPT.Projective SGPT.GAGA.H0S SGPT.GAGA.ChowBl SGPT.BDivisor.GM SGPT.Okounkov
open SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open SGPT.NAPotential.AlgPrimes3.ProjectiveGraphProjectiveHomeomorph
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open scoped Topology Manifold ContDiff

attribute [local instance] MvPolynomial.gradedAlgebra SGPT.Toric.monomialProjectiveTopology

local instance projectiveTraceTopology (r : ℕ) :
    TopologicalSpace (SchemeComplexPoint (polynomialProjStructureMap ℂ r)) :=
  schemeAnalyticPointTopology _

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} (E : ClosedProjectiveEmbedding f)

/-- The inverse image on complex points of an ambient analytic set is the exact
trace of a Zariski-closed subset of the original projective scheme. -/
theorem exists_closed_trace_of_ambient_analyticSubset
    {C : Set (ComplexProjectiveSpace E.ambientDimension)}
    (hC : IsComplexAnalyticSubset (n := E.ambientDimension) C) :
    ∃ Z : Set X, IsClosed Z ∧ ∀ x : SchemeComplexPoint f,
      schemeComplexPointImage f x ∈ Z ↔ ambientPoint E x ∈ C := by
  obtain ⟨m, hm⟩ := chow hC
  obtain ⟨μ, hμ, P, hP, _hgen, hzero⟩ := hm m le_rfl
  let := hμ
  let ι := originalChowProjectiveInclusion P m hP
  let Z : Set X := E.map ⁻¹' range ι
  have hclosed : IsClosed Z := ι.isClosedEmbedding.isClosed_range.preimage E.map.continuous
  have hrange : range (originalChowProjectivePoint P m hP) = C :=
    (range_originalChowProjectivePoint P m hP).trans hzero.symm
  refine ⟨Z, hclosed, fun x => ?_⟩
  rw [← hrange]
  constructor
  · intro hx
    obtain ⟨q, hq⟩ := exists_closedImmersionComplexPoint
      (polynomialProjStructureMap ℂ E.ambientDimension)
      ι (schemeComplexPointMap f _ E.map E.over_base x) hx
    exact ⟨q, congrArg (originalProjectiveHomeomorph E.ambientDimension) hq⟩
  · rintro ⟨q, hq⟩
    have hp := (originalProjectiveHomeomorph E.ambientDimension).injective hq
    exact ⟨schemeComplexPointImage (originalChowStructureMap P m hP) q,
      congrArg (fun z => z.val default) hp⟩

/-- The ambient projective image of any closed projective scheme is analytic.
Apply the algebraic-trace theorem in the smooth ambient scheme, then identify
the identity embedding's manifold map with the ambient projective readback. -/
theorem isComplexAnalyticSubset_ambientPoint_range :
    IsComplexAnalyticSubset (n := E.ambientDimension) (range (ambientPoint E)) := by
  let n := E.ambientDimension
  let p := polynomialProjStructureMap ℂ n
  let I := SGPT.NAPotential.AlgPrimes3.ProjectiveGraphProjectivePoint.identityEmbedding n
  let : IsSeparated p := I.isSeparated
  let : QuasiCompact p := I.quasiCompact
  let : SmoothOfRelativeDimension n p := inferInstance
  let : ChartedSpace (ComplexModel n) (SchemeComplexPoint p) := schemeAnalyticTNChartedSpace p n
  let : IsComplexManifold n (SchemeComplexPoint p) := schemeAnalyticTN_isComplexManifold p n
  let : CompactSpace (SchemeComplexPoint p) := I.analyticCompact
  have hclosed : IsClosed (range E.map) := E.map.isClosedEmbedding.isClosed_range
  have htrace := schemeNativeAlgebraicTrace_isComplexAnalyticSubset p n (range E.map) hclosed
  have hEmbed := isHolomorphicEmbedding_projectivePoint p I n
  have hread (q : SchemeComplexPoint p) :
      projectivePoint p I n q = originalProjectiveHomeomorph n q := by
    rw [← ambientPoint_eq_projectivePoint I n q]
    change originalProjectiveHomeomorph n (schemeComplexPointMap p p (𝟙 _) I.over_base q) = _
    apply congrArg (originalProjectiveHomeomorph n)
    apply Subtype.ext
    exact Category.comp_id q.val
  have himage : projectivePoint p I n '' schemeNativeAlgebraicTrace p (range E.map) =
      range (ambientPoint E) := by
    ext x
    constructor
    · rintro ⟨q, hq, rfl⟩
      obtain ⟨v', hv⟩ := exists_closedImmersionComplexPoint p E.map q hq
      let v : SchemeComplexPoint f :=
        ⟨v'.val, (congrArg (fun a => v'.val ≫ a) E.over_base).symm.trans v'.property⟩
      have hs : schemeComplexPointMap f p E.map E.over_base v = q :=
        Subtype.ext (congrArg Subtype.val hv)
      exact ⟨v, (congrArg (originalProjectiveHomeomorph n) hs).trans (hread q).symm⟩
    · rintro ⟨v, rfl⟩
      let q := schemeComplexPointMap f p E.map E.over_base v
      exact ⟨q, ⟨schemeComplexPointImage f v, rfl⟩, hread q⟩
  rw [← himage]
  exact isComplexAnalyticSubset_image hEmbed htrace

/-- An integral projective scheme has analytically irreducible image in the
ambient projective manifold. -/
theorem analyticallyIrreducible_ambientPoint_range [IsIntegral X] :
    IsComplexAnalyticallyIrreducible (n := E.ambientDimension) (range (ambientPoint E)) := by
  let : LocallyOfFiniteType f := E.locallyOfFiniteType
  let : Nonempty (SchemeComplexPoint f) := integralFiniteTypeSchemeComplexPoint_nonempty f
  have hDense := OF14.dense_range_schemeComplexPointImage f
  refine ⟨isComplexAnalyticSubset_ambientPoint_range E, Set.range_nonempty _, ?_⟩
  intro B C hB hC hBA hCA hBC
  obtain ⟨Z, hZ, hZtrace⟩ := exists_closed_trace_of_ambient_analyticSubset E hB
  obtain ⟨W, hW, hWtrace⟩ := exists_closed_trace_of_ambient_analyticSubset E hC
  have hCover : range (schemeComplexPointImage f) ⊆ Z ∪ W := by
    rintro _ ⟨x, rfl⟩
    have hx : ambientPoint E x ∈ B ∪ C := hBC ▸ mem_range_self x
    exact hx.elim (fun h => Or.inl ((hZtrace x).mpr h)) (fun h => Or.inr ((hWtrace x).mpr h))
  have hη : genericPoint X ∈ Z ∪ W :=
    closure_minimal hCover (hZ.union hW) (hDense (genericPoint X))
  rcases hη with hη | hη
  · left
    refine Subset.antisymm ?_ hBA
    rintro _ ⟨x, rfl⟩
    exact (hZtrace x).mp (((genericPoint_spec X).specializes (mem_univ (schemeComplexPointImage f x))).mem_closed hZ hη)
  · right
    refine Subset.antisymm ?_ hCA
    rintro _ ⟨x, rfl⟩
    exact (hWtrace x).mp (((genericPoint_spec X).specializes (mem_univ (schemeComplexPointImage f x))).mem_closed hW hη)

end SGPT.Okounkov.OF12
