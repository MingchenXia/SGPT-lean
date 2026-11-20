import SGPT.Toric.NativeOriginalEdgeCharts
import SGPT.Foundations.Analysis.FirstPass.ComplexManifold
import Mathlib.Analysis.Analytic.Constructions

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set
open SGPT.Foundations.Analysis.FirstPass
open scoped BigOperators Topology ContDiff
attribute [local instance] monomialProjectiveTopology

variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]

/-- The actual FULL source lattice-point enumeration size is chosen from its
previous genuine existence theorem, not supplied as source geometry. -/
def originalPolytopeFullIndexSize (γ : K → Fin n → ℤ) : ℕ :=
  (exists_latticePolytopeIntegerPoints_enumeration γ).choose

/-- The actual original FULL lattice-point index is manufactured internally. -/
def originalPolytopeFullEnumeration (γ : K → Fin n → ℤ) :
    Fin (originalPolytopeFullIndexSize γ + 1) ≃ latticePolytopeIntegerPoints γ :=
  Classical.choice (exists_latticePolytopeIntegerPoints_enumeration γ).choose_spec

/-- The SAME original full lattice points are the homogeneous exponent family. -/
def originalPolytopeFullExponents (γ : K → Fin n → ℤ) :
    Fin (originalPolytopeFullIndexSize γ + 1) → Fin n → ℤ :=
  latticePolytopeExponentFamily γ (originalPolytopeFullEnumeration γ)

/-- The actual SAME original monomial closure, with its original quotient
subspace topology.  No abstract manifold carrier replaces this type. -/
def originalPolytopeNativeSpace (γ : K → Fin n → ℤ) : Type :=
  monomialProjectiveOrbitClosure (originalPolytopeFullExponents γ)

/-- This is literally the existing original quotient SUBSPACE topology. -/
instance originalPolytopeNativeTopology (γ : K → Fin n → ℤ) :
    TopologicalSpace (originalPolytopeNativeSpace γ) :=
  inferInstanceAs (TopologicalSpace (monomialProjectiveOrbitClosure (originalPolytopeFullExponents γ)))

/-- The internally manufactured index of an ACTUAL original source vertex. -/
def originalPolytopeNativeVertexIndex (γ : K → Fin n → ℤ)
    (v : latticePolytopeVertices γ) : Fin (originalPolytopeFullIndexSize γ + 1) :=
  latticePolytopeVertexIndex γ (originalPolytopeFullEnumeration γ) v

/-- The finite basis is chosen from the ACTUAL original-edge-only producer. -/
def originalPolytopeNativeBasis (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) :
    Module.Basis (Fin n) ℤ (Fin n → ℤ) :=
  (exists_nativeOriginalEdge_chart γ (originalPolytopeFullEnumeration γ) v (hsmooth v)).choose

/-- Actual source neighbors are chosen from the same genuine produced witness. -/
def originalPolytopeNativeNeighborIndex (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) :
    Fin n → Fin (originalPolytopeFullIndexSize γ + 1) :=
  (exists_nativeOriginalEdge_chart γ (originalPolytopeFullEnumeration γ) v (hsmooth v)).choose_spec.choose

/-- The actual original quotient chart is chosen from the SAME source-only
producer, not a supplied atlas or overlap certificate. -/
def originalPolytopeNativePiChart (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) :
    OpenPartialHomeomorph (originalPolytopeNativeSpace γ) (Fin n → ℂ) :=
  (exists_nativeOriginalEdge_chart γ (originalPolytopeFullEnumeration γ) v (hsmooth v)).choose_spec.choose_spec.choose

/-- Every field of these choices is a conclusion of the genuine ORIGINAL
source producer, retaining all representatives and original poles. -/
theorem originalPolytopeNativePiChart_spec (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) :
    (∀ j, originalPolytopeFullExponents γ (originalPolytopeNativeNeighborIndex γ hsmooth v j) -
      v.val = originalPolytopeNativeBasis γ hsmooth v j) ∧
    (originalPolytopeNativePiChart γ hsmooth v).target = Set.univ ∧
    (originalPolytopeNativePiChart γ hsmooth v).source = Subtype.val ⁻¹' Set.range
      (monomialProjectiveRatioPoint (originalPolytopeFullIndexSize γ)
        (originalPolytopeNativeVertexIndex γ v)) ∧
    (∀ z, ((originalPolytopeNativePiChart γ hsmooth v).symm z).val =
      monomialVertexPoint (originalPolytopeNativeBasis γ hsmooth v)
        (originalPolytopeFullExponents γ) (originalPolytopeNativeVertexIndex γ v) z) ∧
    (∀ z, ((originalPolytopeNativePiChart γ hsmooth v).symm z).val ∉ Set.range
      (monomialProjectiveOrbit (originalPolytopeFullExponents γ)) ↔ ∏ j, z j = 0) ∧
    (∀ p, p ∈ (originalPolytopeNativePiChart γ hsmooth v).source → ∀ w hw,
      p.val = Projectivization.mk ℂ w hw →
      w (originalPolytopeNativeVertexIndex γ v) ≠ 0 ∧ ∀ j,
        originalPolytopeNativePiChart γ hsmooth v p j =
          w (originalPolytopeNativeNeighborIndex γ hsmooth v j) /
            w (originalPolytopeNativeVertexIndex γ v)) :=
  (exists_nativeOriginalEdge_chart γ (originalPolytopeFullEnumeration γ) v
    (hsmooth v)).choose_spec.choose_spec.choose_spec

/-- Literal original homogeneous polynomial vector in the manufactured chart. -/
def originalPolytopeNativeVector (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) :
    (Fin n → ℂ) → Fin (originalPolytopeFullIndexSize γ + 1) → ℂ :=
  monomialVertexVector (originalPolytopeNativeBasis γ hsmooth v)
    (originalPolytopeFullExponents γ) (originalPolytopeNativeVertexIndex γ v)

/-- Whole original Pi-chart target, including the literal rank-zero point. -/
theorem originalPolytopeNativePiChart_target (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) :
    (originalPolytopeNativePiChart γ hsmooth v).target = Set.univ :=
  (originalPolytopeNativePiChart_spec γ hsmooth v).2.1

/-- Source is the SAME original homogeneous vertex coordinate open. -/
theorem originalPolytopeNativePiChart_source (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) :
    (originalPolytopeNativePiChart γ hsmooth v).source = Subtype.val ⁻¹' Set.range
      (monomialProjectiveRatioPoint (originalPolytopeFullIndexSize γ)
        (originalPolytopeNativeVertexIndex γ v)) :=
  (originalPolytopeNativePiChart_spec γ hsmooth v).2.2.1

/-- The actual original vertex sources cover this SAME original carrier. -/
theorem originalPolytopeNativePiChart_cover (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (p : originalPolytopeNativeSpace γ) :
    ∃ v, p ∈ (originalPolytopeNativePiChart γ hsmooth v).source := by
  obtain ⟨v, hv⟩ := nativeLatticePolytope_vertex_opens_cover γ
    (originalPolytopeFullEnumeration γ) p.val p.property
  exact ⟨v, by rw [originalPolytopeNativePiChart_source]; exact hv⟩

/-- The actual original homogeneous vector is nonzero on the WHOLE chart. -/
theorem originalPolytopeNativeVector_ne_zero (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) (z : Fin n → ℂ) :
    originalPolytopeNativeVector γ hsmooth v z ≠ 0 :=
  monomialVertexVector_ne_zero _ _ _ z

/-- The actual inverse has this SAME original nonzero homogeneous representative. -/
theorem originalPolytopeNativePiChart_symm_val (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) (z : Fin n → ℂ) :
    ((originalPolytopeNativePiChart γ hsmooth v).symm z).val =
      Projectivization.mk ℂ (originalPolytopeNativeVector γ hsmooth v z)
        (originalPolytopeNativeVector_ne_zero γ hsmooth v z) :=
  (originalPolytopeNativePiChart_spec γ hsmooth v).2.2.2.1 z

/-- EVERY original representative sees the literal vertex-coordinate source. -/
theorem originalPolytopeNativePiChart_mem_source_iff (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (p : originalPolytopeNativeSpace γ)
    (w : Fin (originalPolytopeFullIndexSize γ + 1) → ℂ) (hw : w ≠ 0)
    (hpw : p.val = Projectivization.mk ℂ w hw) :
    p ∈ (originalPolytopeNativePiChart γ hsmooth v).source ↔
      w (originalPolytopeNativeVertexIndex γ v) ≠ 0 := by
  rw [originalPolytopeNativePiChart_source]
  change p.val ∈ Set.range (monomialProjectiveRatioPoint _ _) ↔ _
  rw [hpw]
  exact monomialProjectiveRatioPoint_mem_mk_iff _ _ w hw

/-- Existing genuine analytic finite products/powers apply to the ORIGINAL
literal coordinate polynomial, including the rank-zero product one. -/
theorem analyticAt_originalPolytopeNativeVector_coord (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (i : Fin (originalPolytopeFullIndexSize γ + 1)) (z : Fin n → ℂ) :
    AnalyticAt ℂ (fun u => originalPolytopeNativeVector γ hsmooth v u i) z := by
  change AnalyticAt ℂ (fun u : Fin n → ℂ => ∏ j : Fin n,
    u j ^ monomialVertexExponent (originalPolytopeNativeBasis γ hsmooth v)
      (originalPolytopeFullExponents γ) (originalPolytopeNativeVertexIndex γ v) i j) z
  exact Finset.analyticAt_fun_prod Finset.univ (fun j _ =>
    ((ContinuousLinearMap.proj j : (Fin n → ℂ) →L[ℂ] ℂ).analyticAt z).pow _)

/-- The ACTUAL source/target transition of the manufactured original charts. -/
def originalPolytopeNativePiTransition (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v w : latticePolytopeVertices γ) :
    OpenPartialHomeomorph (Fin n → ℂ) (Fin n → ℂ) :=
  (originalPolytopeNativePiChart γ hsmooth v).symm.trans
    (originalPolytopeNativePiChart γ hsmooth w)

/-- The denominator is nonzero precisely on the ACTUAL original overlap,
proved from the SAME original representative before division. -/
theorem originalPolytopeNativePiTransition_source_iff (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v w : latticePolytopeVertices γ) (z : Fin n → ℂ) :
    z ∈ (originalPolytopeNativePiTransition γ hsmooth v w).source ↔
      originalPolytopeNativeVector γ hsmooth v z (originalPolytopeNativeVertexIndex γ w) ≠ 0 := by
  change (z ∈ (originalPolytopeNativePiChart γ hsmooth v).target ∧
    (originalPolytopeNativePiChart γ hsmooth v).symm z ∈
      (originalPolytopeNativePiChart γ hsmooth w).source) ↔ _
  rw [originalPolytopeNativePiChart_target]
  simp only [Set.mem_univ, true_and]
  exact originalPolytopeNativePiChart_mem_source_iff γ hsmooth w _ _
    (originalPolytopeNativeVector_ne_zero γ hsmooth v z)
    (originalPolytopeNativePiChart_symm_val γ hsmooth v z)

/-- Literal original polynomial ratios give the actual transition ON ITS
ACTUAL SOURCE; no formula is asserted for arbitrary outside-source values. -/
theorem originalPolytopeNativePiTransition_apply (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v w : latticePolytopeVertices γ)
    (z : Fin n → ℂ) (hz : z ∈ (originalPolytopeNativePiTransition γ hsmooth v w).source)
    (j : Fin n) : originalPolytopeNativePiTransition γ hsmooth v w z j =
      originalPolytopeNativeVector γ hsmooth v z (originalPolytopeNativeNeighborIndex γ hsmooth w j) /
        originalPolytopeNativeVector γ hsmooth v z (originalPolytopeNativeVertexIndex γ w) := by
  have h := (originalPolytopeNativePiChart_spec γ hsmooth w).2.2.2.2.2
    ((originalPolytopeNativePiChart γ hsmooth v).symm z) hz.2
    (originalPolytopeNativeVector γ hsmooth v z) (originalPolytopeNativeVector_ne_zero γ hsmooth v z)
    (originalPolytopeNativePiChart_symm_val γ hsmooth v z)
  exact h.2 j

/-- Genuine analytic division with the produced nonzero denominator, followed
by OPEN-source germ congruence, proves analyticity of the ACTUAL transition. -/
theorem analyticOnNhd_originalPolytopeNativePiTransition (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v w : latticePolytopeVertices γ) :
    AnalyticOnNhd ℂ (originalPolytopeNativePiTransition γ hsmooth v w)
      (originalPolytopeNativePiTransition γ hsmooth v w).source := by
  intro z hz
  apply AnalyticAt.pi
  intro j
  have hq := (analyticAt_originalPolytopeNativeVector_coord γ hsmooth v
    (originalPolytopeNativeNeighborIndex γ hsmooth w j) z).div
      (analyticAt_originalPolytopeNativeVector_coord γ hsmooth v
        (originalPolytopeNativeVertexIndex γ w) z)
      ((originalPolytopeNativePiTransition_source_iff γ hsmooth v w z).mp hz)
  apply hq.congr
  filter_upwards [(originalPolytopeNativePiTransition γ hsmooth v w).open_source.mem_nhds hz] with u hu
  exact (originalPolytopeNativePiTransition_apply γ hsmooth v w u hu j).symm

/-- The genuine continuous complex-linear equivalence to the native Euclidean
model.  The Pi norm and the Euclidean norm are not identified definitionally. -/
def originalPolytopeNativeModelEquiv (n : ℕ) : ComplexModel n ≃L[ℂ] (Fin n → ℂ) :=
  EuclideanSpace.equiv (Fin n) ℂ

/-- The original chart transported through this actual linear homeomorphism. -/
def originalPolytopeNativeModelChart (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) :
    OpenPartialHomeomorph (originalPolytopeNativeSpace γ) (ComplexModel n) :=
  (originalPolytopeNativePiChart γ hsmooth v).trans
    (originalPolytopeNativeModelEquiv n).symm.toHomeomorph.toOpenPartialHomeomorph

/-- Linear transport preserves the literal original vertex-coordinate source. -/
theorem originalPolytopeNativeModelChart_source (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) :
    (originalPolytopeNativeModelChart γ hsmooth v).source =
      (originalPolytopeNativePiChart γ hsmooth v).source := by
  simp [originalPolytopeNativeModelChart]

/-- Every original vertex chart has the WHOLE native Euclidean target. -/
theorem originalPolytopeNativeModelChart_target (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) :
    (originalPolytopeNativeModelChart γ hsmooth v).target = Set.univ := by
  simp [originalPolytopeNativeModelChart, originalPolytopeNativePiChart_target]

/-- These are genuine native-model charts on the SAME covering sources. -/
theorem originalPolytopeNativeModelChart_cover (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (p : originalPolytopeNativeSpace γ) :
    ∃ v, p ∈ (originalPolytopeNativeModelChart γ hsmooth v).source := by
  simpa only [originalPolytopeNativeModelChart_source] using
    originalPolytopeNativePiChart_cover γ hsmooth p

/-- The actual native-model overlap, on its genuine open source. -/
def originalPolytopeNativeModelTransition (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v w : latticePolytopeVertices γ) :
    OpenPartialHomeomorph (ComplexModel n) (ComplexModel n) :=
  (originalPolytopeNativeModelChart γ hsmooth v).symm.trans
    (originalPolytopeNativeModelChart γ hsmooth w)

/-- The genuine linear coordinates carry the native overlap into the proved
original rational overlap; no outside-source identity is needed. -/
theorem originalPolytopeNativeModelTransition_source (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v w : latticePolytopeVertices γ) :
    (originalPolytopeNativeModelTransition γ hsmooth v w).source ⊆
      originalPolytopeNativeModelEquiv n ⁻¹'
        (originalPolytopeNativePiTransition γ hsmooth v w).source := by
  intro z hz
  refine ⟨?_, ?_⟩
  · change originalPolytopeNativeModelEquiv n z ∈
      (originalPolytopeNativePiChart γ hsmooth v).target
    rw [originalPolytopeNativePiChart_target]
    exact Set.mem_univ _
  · have h : (originalPolytopeNativeModelChart γ hsmooth v).symm z ∈
        (originalPolytopeNativeModelChart γ hsmooth w).source := hz.2
    rw [originalPolytopeNativeModelChart_source] at h
    exact h

/-- The ACTUAL overlap is conjugation by the genuine linear equivalence. -/
theorem originalPolytopeNativeModelTransition_apply (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v w : latticePolytopeVertices γ)
    (z : ComplexModel n) :
    originalPolytopeNativeModelTransition γ hsmooth v w z =
      (originalPolytopeNativeModelEquiv n).symm
        (originalPolytopeNativePiTransition γ hsmooth v w
          (originalPolytopeNativeModelEquiv n z)) := rfl

/-- Composition with actual continuous linear equivalences proves analyticity
of the genuine native overlap in every dimension, including zero. -/
theorem analyticOnNhd_originalPolytopeNativeModelTransition (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v w : latticePolytopeVertices γ) :
    AnalyticOnNhd ℂ (originalPolytopeNativeModelTransition γ hsmooth v w)
      (originalPolytopeNativeModelTransition γ hsmooth v w).source := by
  intro z hz
  have hp := analyticOnNhd_originalPolytopeNativePiTransition γ hsmooth v w _
    (originalPolytopeNativeModelTransition_source γ hsmooth v w hz)
  exact ((originalPolytopeNativeModelEquiv n).symm.toContinuousLinearMap.analyticAt _).comp
    (hp.comp ((originalPolytopeNativeModelEquiv n).toContinuousLinearMap.analyticAt z))

/-- Genuine analyticity supplies all complex smoothness orders on the actual
open overlap, ready for the existing native manifold constructor. -/
theorem contDiffOn_originalPolytopeNativeModelTransition (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v w : latticePolytopeVertices γ)
    (r : ℕ∞ω) :
    ContDiffOn ℂ r (originalPolytopeNativeModelTransition γ hsmooth v w)
      (originalPolytopeNativeModelTransition γ hsmooth v w).source :=
  (analyticOnNhd_originalPolytopeNativeModelTransition γ hsmooth v w).contDiffOn
    (originalPolytopeNativeModelTransition γ hsmooth v w).open_source.uniqueDiffOn

/-- The same actual overlaps are smooth over the underlying real field. -/
theorem contDiffOn_real_originalPolytopeNativeModelTransition (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v w : latticePolytopeVertices γ)
    (r : ℕ∞ω) :
    ContDiffOn ℝ r (originalPolytopeNativeModelTransition γ hsmooth v w)
      (originalPolytopeNativeModelTransition γ hsmooth v w).source :=
  (contDiffOn_originalPolytopeNativeModelTransition γ hsmooth v w r).restrict_scalars ℝ

end SGPT.Toric
