import SGPT.NAPotential.ProjectiveGraphAnalyticZero
import SGPT.NAPotential.AlgPrimes3GraphMap
import SGPT.GAGA.ChowBlLift
import SGPT.GAGA.H0SSchemeEmbedding
import SGPT.Foundations.Schemes.SchemeGenericSections

/-!
# The actual full-relation analytic set in the original projective product

The original projective embedding and actual rational functions manufacture a
nonzero rational Segre vector. All its homogeneous relations define an actual
closed analytic subset of the original `graphAmbient`, using the existing Segre
map and actual projective point map. No analytic graph is assumed as input.

The affine localization identification, graph membership, and graph uniqueness
remain separate obligations; this file does not assert `ProductGraphData`.
Blueprint: `projective-graph-segre.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.NAPotential.AlgPrimes3.ProjectiveGraphSegre

open Set Filter CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.GAGA.ChowBl SGPT.GAGA.H0S SGPT.NAPotential.FSPos
open SGPT.Okounkov ProjectiveGraphRelationCore ProjectiveGraphAnalyticZero
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending HolomorphicIdealSheaves
open scoped Topology Manifold ContDiff
open scoped SGPT.Foundations.Analysis.Pending.ProductComplexManifold

attribute [local instance] MvPolynomial.gradedAlgebra

section SegreHolomorphic

variable {n N s : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]

theorem segreMap_mk {a : Fin (N + 1) → ℂ} {b : Fin (s + 1) → ℂ}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    segreMap (mk a ha) (mk b hb) = mk (segreVec a b) (segreVec_ne_zero ha hb) := by
  calc
    segreMap (mk a ha) (mk b hb) = segreMap (pmk a) (pmk b) := by
      rw [pmk_eq_mk ha, pmk_eq_mk hb]
    _ = pmk (segreVec a b) := segreMap_pmk ha hb
    _ = mk (segreVec a b) (segreVec_ne_zero ha hb) := pmk_eq_mk _

/-- The existing actual Segre map preserves holomorphic maps, proved from local lifts. -/
theorem contMDiffAt_segreMap {F : M → ComplexProjectiveSpace N}
    {G : M → ComplexProjectiveSpace s} {x : M}
    (hF : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ F x)
    (hG : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel s) ∞ G x) :
    ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel (segreDim N s)) ∞
      (fun y => segreMap (F y) (G y)) x := by
  let i := chartIndex (F x)
  let j := chartIndex (G x)
  have hi : F x ∈ (affineChart i).source := mem_affineChart_chartIndex _
  have hj : G x ∈ (affineChart j).source := mem_affineChart_chartIndex _
  have hAi : ContDiff ℂ ∞ (affineLift (N := N) i) :=
    contDiffOn_univ.mp (contDiffOn_of_differentiableOn_complex
      (differentiable_affineLift i).differentiableOn isOpen_univ)
  have hAj : ContDiff ℂ ∞ (affineLift (N := s) j) :=
    contDiffOn_univ.mp (contDiffOn_of_differentiableOn_complex
      (differentiable_affineLift j).differentiableOn isOpen_univ)
  have hLF := hAi.contMDiff.contMDiffAt.comp x ((contMDiffAt_affineChart i hi).comp x hF)
  have hLG := hAj.contMDiff.contMDiffAt.comp x ((contMDiffAt_affineChart j hj).comp x hG)
  have hS : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, Fin (segreDim N s + 1) → ℂ) ∞
      (fun y => segreVec (affineLift i (affineChart i (F y)))
        (affineLift j (affineChart j (G y)))) x := by
    rw [contMDiffAt_pi_space]
    intro k
    exact ((contMDiffAt_pi_space.mp hLF) (segreIdx N s k).1).mul
      ((contMDiffAt_pi_space.mp hLG) (segreIdx N s k).2)
  refine ComplexProjectiveSpace.contMDiffAt_of_lift hS
    (segreVec_ne_zero (affineLift_ne_zero i _) (affineLift_ne_zero j _)) ?_
  filter_upwards [hF.continuousAt.preimage_mem_nhds ((affineChart i).open_source.mem_nhds hi),
    hG.continuousAt.preimage_mem_nhds ((affineChart j).open_source.mem_nhds hj)] with y hyi hyj
  refine ⟨segreVec_ne_zero (affineLift_ne_zero i _) (affineLift_ne_zero j _), ?_⟩
  conv_lhs => rw [eq_mk_affineLift_affineChart i hyi, eq_mk_affineLift_affineChart j hyj]
  exact segreMap_mk _ _

end SegreHolomorphic

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {m s : ℕ}
  [SmoothOfRelativeDimension (m + 1) f] [IsProper f]

local instance segreGraphTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance segreGraphCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance segreGraphManifold : IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

variable (E : ClosedProjectiveEmbedding f)

/-- Holomorphy of the actual original projective point map in the original TN atlas. -/
theorem contMDiff_projectivePoint :
    ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel E.ambientDimension) ∞
      (projectivePoint f E (m + 1)) := by
  let := E.isSeparated
  let := E.quasiCompact
  intro x
  let i := frameIndex f E x
  have hi := mem_coordOpen_frameIndex f E x
  have hF : ContMDiffAt 𝓘(ℂ, ComplexModel (m + 1))
      𝓘(ℂ, Fin (E.ambientDimension + 1) → ℂ) ∞ (homCoords f E (m + 1) i) x := by
    rw [contMDiffAt_pi_space]
    intro k
    exact contMDiffAt_of_eventually_mdifferentiableAt
      (schemeOpenRegularFunction_holomorphicAt f (m + 1) E _ (ratio E i k) x hi)
  refine ComplexProjectiveSpace.contMDiffAt_of_lift hF (homCoords_ne_zero f E (m + 1) i hi) ?_
  filter_upwards [(isOpen_coordOpen_points f E i).mem_nhds hi] with y hy
  exact ⟨homCoords_ne_zero f E (m + 1) i hy, projectivePoint_eq f E (m + 1) i hy⟩

/-- The actual Segre map of the original projective embedding and projective factor. -/
def segreAmbientMap (z : graphAmbient f m s) : ComplexProjectiveSpace (segreDim E.ambientDimension s) :=
  segreMap (projectivePoint f E (m + 1) z.1) z.2

theorem contMDiff_segreAmbientMap :
    ContMDiff 𝓘(ℂ, ComplexModel ((m + 1) + s))
      𝓘(ℂ, ComplexModel (segreDim E.ambientDimension s)) ∞ (segreAmbientMap (m := m) (s := s) E) := by
  intro z
  exact contMDiffAt_segreMap
    ((contMDiff_projectivePoint (m := m) E).contMDiffAt.comp z
      (ProductComplexManifold.contMDiff_fst.contMDiffAt))
    ProductComplexManifold.contMDiff_snd.contMDiffAt

variable [IsIntegral X]

/-- The original hyperplane-atlas coordinate which contains the actual generic point. -/
def genericCoordinateIndex : Fin (E.ambientDimension + 1) :=
  (hyperplaneAtlas E).genericIndex

omit [IsProper f] in
theorem genericCoordinateIndex_mem : genericPoint X ∈ coordOpen E (genericCoordinateIndex E) :=
  (hyperplaneAtlas E).genericIndex_mem

/-- The actual original projective coordinate ratios as actual elements of `K(X)`. -/
def genericCoordinates : Fin (E.ambientDimension + 1) → X.functionField := by
  let U := coordOpen E (genericCoordinateIndex E)
  letI : Nonempty U := ⟨⟨genericPoint X, genericCoordinateIndex_mem E⟩⟩
  exact fun j => X.germToFunctionField U (ratio E (genericCoordinateIndex E) j)

omit [IsProper f] in
@[simp]
theorem genericCoordinates_self : genericCoordinates E (genericCoordinateIndex E) = 1 := by
  simp [genericCoordinates, ratio_self]

/-- The actual original rational Segre vector, built from the original embedding and functions. -/
def rationalSegreCoordinates (b : Fin s → X.functionField) :
    Fin (segreDim E.ambientDimension s + 1) → X.functionField :=
  fun k => genericCoordinates E (segreIdx E.ambientDimension s k).1 *
    (Fin.cons (1 : X.functionField) b : Fin (s + 1) → X.functionField)
      (segreIdx E.ambientDimension s k).2

omit [IsProper f] in
theorem rationalSegreCoordinates_ne_zero (b : Fin s → X.functionField) :
    rationalSegreCoordinates E b ≠ 0 := by
  intro h
  have h0 := congrFun h ((segreIdx E.ambientDimension s).symm (genericCoordinateIndex E, 0))
  simp [rationalSegreCoordinates] at h0

/-- All actual homogeneous relations of the original rational Segre vector, on the original product. -/
def globalRelationGraph (b : Fin s → X.functionField) : Set (graphAmbient f m s) := by
  letI := schemeFunctionFieldAlgebra f
  exact segreAmbientMap (m := m) E ⁻¹' relationZeroLocus (rationalSegreCoordinates E b)

/-- The actual full-relation set in the original ambient product is closed analytic. -/
theorem isComplexAnalyticSubset_globalRelationGraph (b : Fin s → X.functionField) :
    IsComplexAnalyticSubset (n := (m + 1) + s) (globalRelationGraph (m := m) E b) := by
  let := schemeFunctionFieldAlgebra f
  exact AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage
    (contMDiff_segreAmbientMap (m := m) E)
    (isComplexAnalyticSubset_relationZeroLocus (rationalSegreCoordinates E b))

theorem isClosed_globalRelationGraph (b : Fin s → X.functionField) :
    IsClosed (globalRelationGraph (m := m) E b) :=
  (isComplexAnalyticSubset_globalRelationGraph E b).isClosed

/-- Finite actual homogeneous relations cut out exactly this set on the original ambient product. -/
theorem exists_finite_globalRelationEquations (b : Fin s → X.functionField) :
    letI := schemeFunctionFieldAlgebra f
    ∃ F : Finset (MvPolynomial (Fin (segreDim E.ambientDimension s + 1)) ℂ),
      (∀ p ∈ F, ∃ n : ℕ, p.IsHomogeneous n ∧
        MvPolynomial.aeval (rationalSegreCoordinates E b) p = 0) ∧
      ∀ z : graphAmbient f m s, z ∈ globalRelationGraph (m := m) E b ↔
        ∀ p ∈ F, MvPolynomial.eval (segreAmbientMap E z).rep p = 0 := by
  let := schemeFunctionFieldAlgebra f
  obtain ⟨F, hF, hspan⟩ := exists_finite_relations (A := ℂ) (rationalSegreCoordinates E b)
  refine ⟨F, hF, ?_⟩
  intro z
  change (∀ p ∈ (relationCore (A := ℂ) (rationalSegreCoordinates E b)).toIdeal,
    MvPolynomial.eval (segreAmbientMap E z).rep p = 0) ↔ _
  constructor
  · intro hz p hp
    apply hz p
    rw [← hspan]
    exact Ideal.subset_span hp
  · intro hz p hp
    have hle : (relationCore (A := ℂ) (rationalSegreCoordinates E b)).toIdeal ≤
        RingHom.ker (MvPolynomial.eval (segreAmbientMap E z).rep) := by
      rw [← hspan]
      exact Ideal.span_le.mpr hz
    exact hle hp

end SGPT.NAPotential.AlgPrimes3.ProjectiveGraphSegre
