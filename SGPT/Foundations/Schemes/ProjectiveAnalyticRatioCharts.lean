import SGPT.Foundations.Schemes.PolynomialProjectiveAnalyticCompactness
import SGPT.Foundations.Schemes.ProjectiveRatioDifferential
import Mathlib.Analysis.Analytic.Polynomial

/-! # Actual native projective ratio charts

The proved coordinate-ring dehomogenization identifies actual affine points
with literal complex coordinates. Its actual native open immersion therefore
gives ratio charts in the already defined analytic point topology.
-/

open CategoryTheory AlgebraicGeometry Algebra
open scoped Topology

set_option backward.isDefEq.respectTransparency false

namespace SGPT.Foundations.Schemes

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The inherited affine point evaluator is literally the native Spec preimage. -/
theorem affineSchemePointOfStructure_eval {A : CommRingCat}
    (h : Spec A ⟶ Spec (.of ℂ)) (p : SchemeComplexPoint h) (a : A) :
    letI := affinePointFieldAlgebra h
    affineSchemePointEquivOfStructure h p a = (Spec.preimage p.val).hom a := by
  let := affinePointFieldAlgebra h
  let := affineSchemePointTopologyOfStructure h
  let e := affineSchemePointHomeomorphOfStructure h
  have hp : Spec.map (CommRingCat.ofHom (e p).toRingHom) = p.val := by
    rw [← affineSchemePointHomeomorphOfStructure_symm_val h (e p)]
    exact congrArg Subtype.val (e.symm_apply_apply p)
  rw [← hp, Spec.preimage_map]
  rfl

/-- The actual native projective affine point respects the usual coordinate-ring complex algebra. -/
def polynomialProjRatioAffineUsualPoint (n : ℕ) (i : Fin (n + 1))
    (p : ComplexAffineChartPoint (polynomialProjStructureMap ℂ n)
      (polynomialProjComplexAffineChart n i)) :
    ComplexAlgebraPoint (polynomialProjCoordinateRing ℂ n i) := by
  let pc : SchemeComplexPoint (complexAffineStructureMap (polynomialProjCoordinateRing ℂ n i)) :=
    ⟨p.val, by
      change p.val ≫ affineStructuralMap ℂ (.of (polynomialProjCoordinateRing ℂ n i)) = 𝟙 _
      rw [← polynomialProjCoordinateImmersion_structure]
      exact p.property⟩
  exact affineSchemePoint_toAlgebra (polynomialProjCoordinateRing ℂ n i) pc

/-- Literal actual native affine coordinates are evaluations of the genuine regular ratios. -/
def polynomialProjRatioAffineCoordinates (n : ℕ) (i : Fin (n + 1))
    (p : ComplexAffineChartPoint (polynomialProjStructureMap ℂ n)
      (polynomialProjComplexAffineChart n i)) : Fin n → ℂ :=
  fun a => polynomialProjRatioAffineUsualPoint n i p
    (polynomialProjCoordinateRatio ℂ n i (i.succAbove a))

/-- The literal inverse affine point of a coordinate vector, using the inherited actual structure. -/
def polynomialProjRatioAffineInverse (n : ℕ) (i : Fin (n + 1)) (z : Fin n → ℂ) :
    ComplexAffineChartPoint (polynomialProjStructureMap ℂ n)
      (polynomialProjComplexAffineChart n i) := by
  let := affinePointFieldAlgebra
    ((polynomialProjComplexAffineChart n i).map ≫ polynomialProjStructureMap ℂ n)
  let := affineSchemePointTopologyOfStructure
    ((polynomialProjComplexAffineChart n i).map ≫ polynomialProjStructureMap ℂ n)
  exact (affineSchemePointHomeomorphOfStructure _).symm
    (polynomialProjVectorChartInheritedPoint n i (Fin.insertNth i 1 z))

theorem polynomialProjRatioAffineInverse_val (n : ℕ) (i : Fin (n + 1)) (z : Fin n → ℂ) :
    (polynomialProjRatioAffineInverse n i z).val =
      Spec.map (CommRingCat.ofHom
        (polynomialProjVectorChartAlgebraPoint n i (Fin.insertNth i 1 z)).toRingHom) := by
  let := affinePointFieldAlgebra
    ((polynomialProjComplexAffineChart n i).map ≫ polynomialProjStructureMap ℂ n)
  let := affineSchemePointTopologyOfStructure
    ((polynomialProjComplexAffineChart n i).map ≫ polynomialProjStructureMap ℂ n)
  exact affineSchemePointHomeomorphOfStructure_symm_val _ _

theorem polynomialProjRatioAffineCoordinates_continuous (n : ℕ) (i : Fin (n + 1)) :
    Continuous (polynomialProjRatioAffineCoordinates n i) := by
  let hstr := (polynomialProjComplexAffineChart n i).map ≫ polynomialProjStructureMap ℂ n
  let := affinePointFieldAlgebra hstr
  apply continuous_pi_iff.mpr
  intro a
  have h := (complexPoint_evaluation_continuous (A := (polynomialProjComplexAffineChart n i).ring)
    (polynomialProjCoordinateRatio ℂ n i (i.succAbove a))).comp
      (affineSchemePointHomeomorphOfStructure hstr).continuous
  convert! h using 1
  funext p
  exact (affineSchemePointOfStructure_eval _ p _).symm

theorem polynomialProjRatioAffineInverse_continuous (n : ℕ) (i : Fin (n + 1)) :
    Continuous (polynomialProjRatioAffineInverse n i) := by
  let := affinePointFieldAlgebra
    ((polynomialProjComplexAffineChart n i).map ≫ polynomialProjStructureMap ℂ n)
  let e := affineSchemePointHomeomorphOfStructure
    ((polynomialProjComplexAffineChart n i).map ≫ polynomialProjStructureMap ℂ n)
  apply e.symm.continuous.comp
  apply (continuous_complexPoint_iff _).mpr
  intro a
  change Continuous (fun z : Fin n → ℂ => MvPolynomial.aeval
    (polynomialProjVectorRatios n i (Fin.insertNth i 1 z))
      (polynomialProjCoordinateDehomogenization ℂ n i a))
  have hrat : ∀ z : Fin n → ℂ, polynomialProjVectorRatios n i (Fin.insertNth i 1 z) = z := by
    intro z
    funext a
    simp [polynomialProjVectorRatios]
  simpa only [hrat, MvPolynomial.aeval_eq_eval] using
      complexPolynomial_continuous (polynomialProjCoordinateDehomogenization ℂ n i a)

theorem polynomialProjRatioAffineCoordinates_inverse (n : ℕ) (i : Fin (n + 1)) (z : Fin n → ℂ) :
    polynomialProjRatioAffineCoordinates n i (polynomialProjRatioAffineInverse n i z) = z := by
  funext a
  change (Spec.preimage (polynomialProjRatioAffineInverse n i z).val).hom
    (polynomialProjCoordinateRatio ℂ n i (i.succAbove a)) = _
  rw [polynomialProjRatioAffineInverse_val, Spec.preimage_map]
  change polynomialProjVectorChartAlgebraPoint n i (Fin.insertNth i 1 z)
    (polynomialProjCoordinateRatio ℂ n i (i.succAbove a)) = _
  simpa only [Fin.insertNth_apply_succAbove, Fin.insertNth_apply_same, div_one] using
    polynomialProjVectorChartAlgebraPoint_ratio n i (i.succAbove a) (Fin.insertNth i 1 z)
      (by simp)

theorem polynomialProjRatioAffineInverse_coordinates (n : ℕ) (i : Fin (n + 1))
    (p : ComplexAffineChartPoint (polynomialProjStructureMap ℂ n)
      (polynomialProjComplexAffineChart n i)) :
    polynomialProjRatioAffineInverse n i (polynomialProjRatioAffineCoordinates n i p) = p := by
  apply Subtype.ext
  rw [polynomialProjRatioAffineInverse_val]
  change Spec.map (CommRingCat.ofHom
    (polynomialProjVectorChartAlgebraPoint n i
      (polynomialProjAlgebraPointVector n i (polynomialProjRatioAffineUsualPoint n i p))).toRingHom) = _
  rw [polynomialProjAlgebraPointVector_chartAlgebraPoint]
  exact Spec.map_preimage p.val

/-- A genuine homeomorphism of actual affine native points with literal complex coordinates. -/
def polynomialProjRatioAffineHomeomorph (n : ℕ) (i : Fin (n + 1)) :
    ComplexAffineChartPoint (polynomialProjStructureMap ℂ n)
      (polynomialProjComplexAffineChart n i) ≃ₜ (Fin n → ℂ) where
  toFun := polynomialProjRatioAffineCoordinates n i
  invFun := polynomialProjRatioAffineInverse n i
  left_inv := polynomialProjRatioAffineInverse_coordinates n i
  right_inv := polynomialProjRatioAffineCoordinates_inverse n i
  continuous_toFun := polynomialProjRatioAffineCoordinates_continuous n i
  continuous_invFun := polynomialProjRatioAffineInverse_continuous n i

/-- The actual global native point represented by literal affine ratio coordinates. -/
def polynomialProjRatioPoint (n : ℕ) (i : Fin (n + 1)) (z : Fin n → ℂ) :
    SchemeComplexPoint (polynomialProjStructureMap ℂ n) :=
  complexAffineChartPointMap (polynomialProjStructureMap ℂ n) (polynomialProjComplexAffineChart n i)
    (polynomialProjRatioAffineInverse n i z)

theorem polynomialProjRatioPoint_eq_vector (n : ℕ) (i : Fin (n + 1)) (z : Fin n → ℂ) :
    polynomialProjRatioPoint n i z = polynomialProjVectorChartPoint n i (Fin.insertNth i 1 z) := rfl

theorem polynomialProjRatioPoint_isOpenEmbedding (n : ℕ) (i : Fin (n + 1)) :
    letI := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
    Topology.IsOpenEmbedding (polynomialProjRatioPoint n i) := by
  let := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
  exact (complexAffineChartPointMap_isOpenEmbedding _ (polynomialProjComplexAffineChart n i)).comp
    (polynomialProjRatioAffineHomeomorph n i).symm.isOpenEmbedding

/-- Genuine global native ratio chart, in the actual scheme analytic topology. -/
def polynomialProjRatioChart (n : ℕ) (i : Fin (n + 1)) :
    letI := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
    OpenPartialHomeomorph (SchemeComplexPoint (polynomialProjStructureMap ℂ n)) (Fin n → ℂ) := by
  let := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
  exact ((polynomialProjRatioPoint_isOpenEmbedding n i).toOpenPartialHomeomorph
    (polynomialProjRatioPoint n i)).symm

theorem polynomialProjRatioChart_symm (n : ℕ) (i : Fin (n + 1)) :
    letI := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
    (polynomialProjRatioChart n i).symm = polynomialProjRatioPoint n i := by
  let := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
  exact Topology.IsOpenEmbedding.toOpenPartialHomeomorph_apply
    (polynomialProjRatioPoint n i) (polynomialProjRatioPoint_isOpenEmbedding n i)

theorem polynomialProjRatioChart_target (n : ℕ) (i : Fin (n + 1)) :
    letI := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
    (polynomialProjRatioChart n i).target = Set.univ := rfl

theorem polynomialProjRatioChart_source (n : ℕ) (i : Fin (n + 1)) :
    letI := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
    (polynomialProjRatioChart n i).source = Set.range (polynomialProjRatioPoint n i) := by
  let := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
  exact Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target
    (polynomialProjRatioPoint n i) (polynomialProjRatioPoint_isOpenEmbedding n i)

theorem polynomialProjRatioChart_apply_point (n : ℕ) (i : Fin (n + 1)) (z : Fin n → ℂ) :
    letI := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
    polynomialProjRatioChart n i (polynomialProjRatioPoint n i z) = z := by
  let := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
  exact Topology.IsOpenEmbedding.toOpenPartialHomeomorph_left_inv _ _

/-- Ratio source membership is the actual native open-immersion image condition. -/
theorem polynomialProjRatioChart_mem_source (n : ℕ) (i : Fin (n + 1))
    (p : SchemeComplexPoint (polynomialProjStructureMap ℂ n)) :
    letI := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
    p ∈ (polynomialProjRatioChart n i).source ↔
      schemeComplexPointImage (polynomialProjStructureMap ℂ n) p ∈
        Set.range (polynomialProjCoordinateImmersion ℂ n i) := by
  let := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
  rw [polynomialProjRatioChart_source]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨schemeComplexPointImage
      ((polynomialProjComplexAffineChart n i).map ≫ polynomialProjStructureMap ℂ n)
        (polynomialProjRatioAffineInverse n i z), rfl⟩
  · intro hp
    let q := schemeComplexPointLift (polynomialProjStructureMap ℂ n)
      (polynomialProjCoordinateImmersion ℂ n i) p hp
    refine ⟨polynomialProjRatioAffineCoordinates n i q, ?_⟩
    change complexAffineChartPointMap _ _
      (polynomialProjRatioAffineInverse n i (polynomialProjRatioAffineCoordinates n i q)) = p
    rw [polynomialProjRatioAffineInverse_coordinates]
    apply Subtype.ext
    exact schemeComplexPointLift_fac _ _ p hp

/-- The actual genuine finite ratio-chart sources cover every native projective complex point. -/
theorem polynomialProjRatioChart_sources_cover (n : ℕ)
    (p : SchemeComplexPoint (polynomialProjStructureMap ℂ n)) :
    letI := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
    ∃ i : Fin (n + 1), p ∈ (polynomialProjRatioChart n i).source := by
  let := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
  have hcover : schemeComplexPointImage (polynomialProjStructureMap ℂ n) p ∈
      ⨆ i : Fin (n + 1), (polynomialProjCoordinateImmersion ℂ n i).opensRange := by
    rw [polynomialProjCoordinateImmersion_covers]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hcover
  exact ⟨i, (polynomialProjRatioChart_mem_source n i p).mpr hi⟩

/-- The native projective chart inverse has its literal Spec-map representative. -/
theorem polynomialProjRatioChart_symm_val (n : ℕ) (i : Fin (n + 1)) (z : Fin n → ℂ) :
    letI := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
    ((polynomialProjRatioChart n i).symm z).val =
      Spec.map (CommRingCat.ofHom
        (polynomialProjVectorChartAlgebraPoint n i (Fin.insertNth i 1 z)).toRingHom) ≫
          polynomialProjCoordinateImmersion ℂ n i := by
  let := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
  rw [polynomialProjRatioChart_symm, polynomialProjRatioPoint_eq_vector,
    polynomialProjVectorChartPoint_val]

/-- Actual chart intersection membership is precisely the literal nonzero ratio denominator. -/
theorem polynomialProjRatioChart_inverse_mem_source (n : ℕ) (i j : Fin (n + 1))
    (z : Fin n → ℂ) :
    letI := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
    (polynomialProjRatioChart n i).symm z ∈ (polynomialProjRatioChart n j).source ↔
      projectiveRatioCoordinateVector n i z j ≠ 0 := by
  let := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
  rw [polynomialProjRatioChart_symm, polynomialProjRatioChart_mem_source,
    polynomialProjRatioPoint_eq_vector]
  change schemeComplexPointImage (polynomialProjStructureMap ℂ n)
      (polynomialProjVectorChartPoint n i (Fin.insertNth i 1 z)) ∈
        (polynomialProjCoordinateImmersion ℂ n j).opensRange ↔ _
  change schemeComplexPointImage (polynomialProjStructureMap ℂ n)
      (polynomialProjVectorChartPoint n i (Fin.insertNth i 1 z)) ∈
        (Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) ℂ)
          (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X ℂ j) (by decide)).opensRange ↔ _
  rw [Proj.opensRange_awayι, Proj.mem_basicOpen,
    polynomialProjVectorChartPoint_mem_homogeneous_positive n i (Fin.insertNth i 1 z)
      (by simp) 1 (by decide) (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X ℂ j),
    MvPolynomial.eval_X]
  rfl

/-- Literal quotient coordinates represent the same actual native scheme point on an actual overlap. -/
theorem polynomialProjRatioPoint_transition (n : ℕ) (i j : Fin (n + 1))
    (z : Fin n → ℂ) (hz : projectiveRatioCoordinateVector n i z j ≠ 0) :
    polynomialProjRatioPoint n j (projectiveRatioTransition n i j z) = polynomialProjRatioPoint n i z := by
  rw [polynomialProjRatioPoint_eq_vector, polynomialProjRatioPoint_eq_vector]
  have hpoint : polynomialProjVectorChartPoint n j
      (Fin.insertNth j 1 (projectiveRatioTransition n i j z)) =
        polynomialProjVectorChartPoint n j (Fin.insertNth i 1 z) := by
    have hr : polynomialProjVectorRatios n j (Fin.insertNth j 1 (projectiveRatioTransition n i j z)) =
        polynomialProjVectorRatios n j (Fin.insertNth i 1 z) := by
      funext a
      simp [polynomialProjVectorRatios, projectiveRatioTransition, projectiveRatioCoordinateVector]
    apply Subtype.ext
    rw [polynomialProjVectorChartPoint_val, polynomialProjVectorChartPoint_val]
    unfold polynomialProjVectorChartAlgebraPoint
    rw [hr]
  exact hpoint.trans (polynomialProjVectorChartPoint_eq n i j (Fin.insertNth i 1 z) (by simp) hz).symm

/-- The actual transition of native ratio charts equals the literal quotient-coordinate function. -/
theorem polynomialProjRatioChart_transition_apply (n : ℕ) (i j : Fin (n + 1))
    (z : Fin n → ℂ) (hz : projectiveRatioCoordinateVector n i z j ≠ 0) :
    letI := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
    polynomialProjRatioChart n j ((polynomialProjRatioChart n i).symm z) =
      projectiveRatioTransition n i j z := by
  let := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
  rw [polynomialProjRatioChart_symm, ← polynomialProjRatioPoint_transition n i j z hz,
    polynomialProjRatioChart_apply_point]

/-- All genuine regular elements of the actual ratio chart evaluate polynomially in its coordinates. -/
theorem polynomialProjRatioAffineInverse_eval (n : ℕ) (i : Fin (n + 1))
    (a : (polynomialProjComplexAffineChart n i).ring) (z : Fin n → ℂ) :
    letI := affinePointFieldAlgebra
      ((polynomialProjComplexAffineChart n i).map ≫ polynomialProjStructureMap ℂ n)
    affineSchemePointEquivOfStructure
      ((polynomialProjComplexAffineChart n i).map ≫ polynomialProjStructureMap ℂ n)
      (polynomialProjRatioAffineInverse n i z) a =
        MvPolynomial.eval z (polynomialProjCoordinateDehomogenization ℂ n i a) := by
  let := affinePointFieldAlgebra
    ((polynomialProjComplexAffineChart n i).map ≫ polynomialProjStructureMap ℂ n)
  rw [affineSchemePointOfStructure_eval, polynomialProjRatioAffineInverse_val, Spec.preimage_map]
  change MvPolynomial.eval (polynomialProjVectorRatios n i (Fin.insertNth i 1 z))
    (polynomialProjCoordinateDehomogenization ℂ n i a) = _
  have hrat : polynomialProjVectorRatios n i (Fin.insertNth i 1 z) = z := by
    funext b
    simp [polynomialProjVectorRatios]
  rw [hrat]

/-- Actual inverse evaluation of every actual affine ring element is analytic on the whole target. -/
theorem polynomialProjRatioAffineInverse_eval_analyticOnNhd (n : ℕ) (i : Fin (n + 1))
    (a : (polynomialProjComplexAffineChart n i).ring) :
    letI := affinePointFieldAlgebra
      ((polynomialProjComplexAffineChart n i).map ≫ polynomialProjStructureMap ℂ n)
    AnalyticOnNhd ℂ (fun z => affineSchemePointEquivOfStructure
      ((polynomialProjComplexAffineChart n i).map ≫ polynomialProjStructureMap ℂ n)
        (polynomialProjRatioAffineInverse n i z) a) Set.univ := by
  let := affinePointFieldAlgebra
    ((polynomialProjComplexAffineChart n i).map ≫ polynomialProjStructureMap ℂ n)
  simp only [polynomialProjRatioAffineInverse_eval]
  exact AnalyticOnNhd.eval_mvPolynomial _

/-- The actual native ratio-chart transition on its genuine source. -/
def polynomialProjRatioChartTransition (n : ℕ) (i j : Fin (n + 1)) :
    letI := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
    OpenPartialHomeomorph (Fin n → ℂ) (Fin n → ℂ) := by
  let := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
  exact (polynomialProjRatioChart n i).symm.trans (polynomialProjRatioChart n j)

theorem polynomialProjRatioChartTransition_source (n : ℕ) (i j : Fin (n + 1)) :
    letI := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
    (polynomialProjRatioChartTransition n i j).source =
      {z | projectiveRatioCoordinateVector n i z j ≠ 0} := by
  let := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
  ext z
  change z ∈ (polynomialProjRatioChart n i).target ∧
    (polynomialProjRatioChart n i).symm z ∈ (polynomialProjRatioChart n j).source ↔ _
  simp only [polynomialProjRatioChart_target, Set.mem_univ, true_and,
    polynomialProjRatioChart_inverse_mem_source, Set.mem_ofPred_eq]

/-- The transition of actual native ratio charts is smooth in every complex order. -/
theorem polynomialProjRatioChartTransition_contDiffOn (n : ℕ) (i j : Fin (n + 1))
    (k : WithTop ℕ∞) :
    letI := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
    ContDiffOn ℂ k (polynomialProjRatioChartTransition n i j)
      (polynomialProjRatioChartTransition n i j).source := by
  let := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
  rw [polynomialProjRatioChartTransition_source]
  apply (projectiveRatioTransition_contDiffOn n i j k).congr
  intro z hz
  exact polynomialProjRatioChart_transition_apply n i j z hz

/-- The native real derivative of the actual scheme-derived ratio transition is the literal matrix. -/
theorem polynomialProjRatioChartTransition_real_fderiv (n : ℕ) (i j : Fin (n + 1))
    (z : Fin n → ℂ) (hz : projectiveRatioCoordinateVector n i z j ≠ 0) :
    letI := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
    fderiv ℝ (polynomialProjRatioChartTransition n i j) z =
      (projectiveRatioJacobianCLM n i j (projectiveRatioCoordinateVector n i z)
        (Units.mk0 _ hz)).restrictScalars ℝ := by
  let := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
  have ht : z ∈ (polynomialProjRatioChartTransition n i j).source := by
    rw [polynomialProjRatioChartTransition_source]
    exact hz
  have he : (polynomialProjRatioChartTransition n i j : (Fin n → ℂ) → (Fin n → ℂ)) =ᶠ[𝓝 z]
      projectiveRatioTransition n i j := by
    filter_upwards [(polynomialProjRatioChartTransition n i j).open_source.mem_nhds ht] with w hw
    rw [polynomialProjRatioChartTransition_source] at hw
    exact polynomialProjRatioChart_transition_apply n i j w hw
  rw [he.fderiv_eq]
  exact projectiveRatioTransition_real_fderiv n i j z (Units.mk0 _ hz) rfl

/-- The real coordinate metric is preserved by the actual native projective chart derivative. -/
theorem polynomialProjRatioChartTransition_metric_real_fderiv (n : ℕ) (i j : Fin (n + 1))
    (z v w : Fin n → ℂ) (hz : projectiveRatioCoordinateVector n i z j ≠ 0) :
    letI := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
    projectiveFubiniStudyRealMetric (polynomialProjRatioChartTransition n i j z)
      (fderiv ℝ (polynomialProjRatioChartTransition n i j) z v)
      (fderiv ℝ (polynomialProjRatioChartTransition n i j) z w) =
        projectiveFubiniStudyRealMetric z v w := by
  let := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
  rw [polynomialProjRatioChartTransition_real_fderiv n i j z hz]
  change projectiveFubiniStudyRealMetric
    (polynomialProjRatioChart n j ((polynomialProjRatioChart n i).symm z)) _ _ = _
  rw [polynomialProjRatioChart_transition_apply n i j z hz]
  simpa only [projectiveRatioTransition_real_fderiv n i j z (Units.mk0 _ hz) rfl] using
    projectiveRatioTransition_metric_real_fderiv n i j z v w (Units.mk0 _ hz) rfl

/-- The actual affine point read from a source ratio-chart coordinate vector. -/
def polynomialProjRatioAffineSourcePoint (n : ℕ) (i : Fin (n + 1))
    (p : SchemeComplexPoint (polynomialProjStructureMap ℂ n)) :
    letI := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
    ComplexAffineChartPoint (polynomialProjStructureMap ℂ n) (polynomialProjComplexAffineChart n i) := by
  let := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
  exact polynomialProjRatioAffineInverse n i (polynomialProjRatioChart n i p)

theorem polynomialProjRatioAffineSourcePoint_map (n : ℕ) (i : Fin (n + 1))
    (p : SchemeComplexPoint (polynomialProjStructureMap ℂ n)) :
    letI := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
    p ∈ (polynomialProjRatioChart n i).source →
      complexAffineChartPointMap (polynomialProjStructureMap ℂ n) (polynomialProjComplexAffineChart n i)
        (polynomialProjRatioAffineSourcePoint n i p) = p := by
  let := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
  intro hp
  change polynomialProjRatioPoint n i (polynomialProjRatioChart n i p) = p
  rw [← polynomialProjRatioChart_symm]
  exact (polynomialProjRatioChart n i).left_inv hp

/-- Source chart coordinates are evaluations of the actual native ring ratio generators. -/
theorem polynomialProjRatioAffineSourcePoint_eval (n : ℕ) (i : Fin (n + 1))
    (p : SchemeComplexPoint (polynomialProjStructureMap ℂ n)) (a : Fin n) :
    letI := affinePointFieldAlgebra
      ((polynomialProjComplexAffineChart n i).map ≫ polynomialProjStructureMap ℂ n)
    letI := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
    affineSchemePointEquivOfStructure
      ((polynomialProjComplexAffineChart n i).map ≫ polynomialProjStructureMap ℂ n)
        (polynomialProjRatioAffineSourcePoint n i p)
          (polynomialProjCoordinateRatio ℂ n i (i.succAbove a)) = polynomialProjRatioChart n i p a := by
  let := affinePointFieldAlgebra
    ((polynomialProjComplexAffineChart n i).map ≫ polynomialProjStructureMap ℂ n)
  let := schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)
  change affineSchemePointEquivOfStructure _
    (polynomialProjRatioAffineInverse n i (polynomialProjRatioChart n i p)) _ = _
  rw [polynomialProjRatioAffineInverse_eval, polynomialProjCoordinateDehomogenization_ratio,
    MvPolynomial.eval_X]

end

end SGPT.Foundations.Schemes
