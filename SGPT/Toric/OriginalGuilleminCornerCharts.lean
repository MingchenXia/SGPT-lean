import SGPT.Toric.NativeOriginalEdgeOrbit
import SGPT.Toric.OriginalVertexHalfspaces

/-!
# Actual charts for the original Guillemin corner basis

The already fixed original halfspace basis supplies the signs and neighbors of
the existing genuine monomial chart constructor. Its charts retain the original
carrier and have actual analytic transitions to the existing native atlas.
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set SGPT.AlmostSemigroup.Counting
open SGPT.Foundations.Analysis.FirstPass
open scoped BigOperators Topology ContDiff Classical
attribute [local instance] monomialProjectiveTopology

variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]

/-- The actual neighbor of the SAME basis used by the original corner weight. -/
def originalGuilleminCornerNeighborIndex (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) :
    Fin n → Fin (originalPolytopeFullIndexSize γ + 1) :=
  fun j => (originalPolytopeFullEnumeration γ).symm
    ⟨v.val + originalVertexHalfspaceBasis γ hsmooth v j,
      (originalVertexHalfspaceBasis_spec γ hsmooth v).2.2 j⟩

private theorem cornerExponent_vertex (γ : K → Fin n → ℤ)
    (v : latticePolytopeVertices γ) :
    originalPolytopeFullExponents γ (originalPolytopeNativeVertexIndex γ v) = v.val :=
  latticePolytopeExponentFamily_vertexIndex γ (originalPolytopeFullEnumeration γ) v

private theorem cornerNeighbor_difference (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) (j : Fin n) :
    originalPolytopeFullExponents γ (originalGuilleminCornerNeighborIndex γ hsmooth v j) -
      originalPolytopeFullExponents γ (originalPolytopeNativeVertexIndex γ v) =
        originalVertexHalfspaceBasis γ hsmooth v j := by
  have h : originalPolytopeFullExponents γ (originalGuilleminCornerNeighborIndex γ hsmooth v j) =
      v.val + originalVertexHalfspaceBasis γ hsmooth v j :=
    congrArg Subtype.val ((originalPolytopeFullEnumeration γ).apply_symm_apply _)
  rw [h, cornerExponent_vertex, add_sub_cancel_left]

private theorem cornerCoefficients_nonneg (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (i : Fin (originalPolytopeFullIndexSize γ + 1)) (j : Fin n) :
    0 ≤ (originalVertexHalfspaceBasis γ hsmooth v).repr
      (originalPolytopeFullExponents γ i -
        originalPolytopeFullExponents γ (originalPolytopeNativeVertexIndex γ v)) j := by
  rw [cornerExponent_vertex]
  exact (originalVertexHalfspaceBasis_spec γ hsmooth v).2.1
    (originalPolytopeFullEnumeration γ i) j

/-- Existing native monomial geometry for the SPECIFIED original corner basis. -/
def originalGuilleminCornerPiChart (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) :
    OpenPartialHomeomorph (originalPolytopeNativeSpace γ) (Fin n → ℂ) :=
  monomialOriginalVertexChart (originalVertexHalfspaceBasis γ hsmooth v)
    (originalPolytopeFullExponents γ) (originalPolytopeNativeVertexIndex γ v)
    (originalGuilleminCornerNeighborIndex γ hsmooth v)
    (cornerCoefficients_nonneg γ hsmooth v) (cornerNeighbor_difference γ hsmooth v)

/-- Original full-target/source, normalized inverse, boundary and EVERY
homogeneous-representative readback are outputs for this fixed basis. -/
theorem originalGuilleminCornerPiChart_spec (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) :
    (∀ j, originalPolytopeFullExponents γ (originalGuilleminCornerNeighborIndex γ hsmooth v j) -
      v.val = originalVertexHalfspaceBasis γ hsmooth v j) ∧
    (originalGuilleminCornerPiChart γ hsmooth v).target = Set.univ ∧
    (originalGuilleminCornerPiChart γ hsmooth v).source =
      (originalPolytopeNativePiChart γ hsmooth v).source ∧
    (∀ z, ((originalGuilleminCornerPiChart γ hsmooth v).symm z).val =
      monomialVertexPoint (originalVertexHalfspaceBasis γ hsmooth v)
        (originalPolytopeFullExponents γ) (originalPolytopeNativeVertexIndex γ v) z) ∧
    (∀ z, ((originalGuilleminCornerPiChart γ hsmooth v).symm z).val ∉
      Set.range (monomialProjectiveOrbit (originalPolytopeFullExponents γ)) ↔ ∏ j, z j = 0) ∧
    (∀ p, p ∈ (originalGuilleminCornerPiChart γ hsmooth v).source → ∀ Z hZ,
      p.val = Projectivization.mk ℂ Z hZ →
      Z (originalPolytopeNativeVertexIndex γ v) ≠ 0 ∧ ∀ j,
        originalGuilleminCornerPiChart γ hsmooth v p j =
          Z (originalGuilleminCornerNeighborIndex γ hsmooth v j) /
            Z (originalPolytopeNativeVertexIndex γ v)) := by
  let B := originalVertexHalfspaceBasis γ hsmooth v
  let β := originalPolytopeFullExponents γ
  let vi := originalPolytopeNativeVertexIndex γ v
  let ν := originalGuilleminCornerNeighborIndex γ hsmooth v
  let hpos := cornerCoefficients_nonneg γ hsmooth v
  let hν := cornerNeighbor_difference γ hsmooth v
  refine ⟨?_, monomialOriginalVertexChart_target B β vi ν hpos hν, ?_,
    monomialOriginalVertexChart_symm_val B β vi ν hpos hν,
    monomialOriginalVertexChart_boundary B β vi ν hpos hν, ?_⟩
  · intro j
    rw [← cornerExponent_vertex γ v]
    exact hν j
  · rw [originalPolytopeNativePiChart_source]
    exact monomialOriginalVertexChart_source B β vi ν hpos hν
  · intro p hp Z hZ hpZ
    exact monomialOriginalVertexChart_ratio B β vi ν hpos hν p hp Z hZ hpZ

/-- The actual corner chart transported through the genuine model equivalence. -/
def originalGuilleminCornerModelChart (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) :
    OpenPartialHomeomorph (originalPolytopeNativeSpace γ) (ComplexModel n) :=
  (originalGuilleminCornerPiChart γ hsmooth v).trans
    (originalPolytopeNativeModelEquiv n).symm.toHomeomorph.toOpenPartialHomeomorph

private theorem cornerModel_source (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) :
    (originalGuilleminCornerModelChart γ hsmooth v).source =
      (originalPolytopeNativeModelChart γ hsmooth v).source := by
  rw [originalPolytopeNativeModelChart_source]
  simpa only [originalGuilleminCornerModelChart, OpenPartialHomeomorph.trans_source,
    Homeomorph.toOpenPartialHomeomorph_source, preimage_univ, inter_univ] using
      (originalGuilleminCornerPiChart_spec γ hsmooth v).2.2.1

private theorem cornerModel_target (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) :
    (originalGuilleminCornerModelChart γ hsmooth v).target = Set.univ := by
  simp [originalGuilleminCornerModelChart, (originalGuilleminCornerPiChart_spec γ hsmooth v).2.1]

/-- Actual overlap from old native vertex w to the specified corner vertex v. -/
def originalGuilleminCornerNativeTransition (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (w v : latticePolytopeVertices γ) :
    OpenPartialHomeomorph (ComplexModel n) (ComplexModel n) :=
  (originalPolytopeNativeModelChart γ hsmooth w).symm.trans
    (originalGuilleminCornerModelChart γ hsmooth v)

/-- Genuine source membership proves the actual denominator nonzero first. -/
theorem originalGuilleminCornerNativeTransition_source_iff (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (w v : latticePolytopeVertices γ)
    (z : ComplexModel n) :
    z ∈ (originalGuilleminCornerNativeTransition γ hsmooth w v).source ↔
      originalPolytopeNativeVector γ hsmooth w (originalPolytopeNativeModelEquiv n z)
        (originalPolytopeNativeVertexIndex γ v) ≠ 0 := by
  change (z ∈ (originalPolytopeNativeModelChart γ hsmooth w).target ∧
    (originalPolytopeNativeModelChart γ hsmooth w).symm z ∈
      (originalGuilleminCornerModelChart γ hsmooth v).source) ↔ _
  rw [originalPolytopeNativeModelChart_target, cornerModel_source,
    originalPolytopeNativeModelChart_source]
  simp only [mem_univ, true_and]
  exact originalPolytopeNativePiChart_mem_source_iff γ hsmooth v _ _
    (originalPolytopeNativeVector_ne_zero γ hsmooth w _)
    (originalPolytopeNativePiChart_symm_val γ hsmooth w _)

/-- Equal original vertex opens give a genuine whole-model inverse pair. -/
theorem originalGuilleminCornerNativeTransition_sameVertex_source_target (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) :
    (originalGuilleminCornerNativeTransition γ hsmooth v v).source = Set.univ ∧
      (originalGuilleminCornerNativeTransition γ hsmooth v v).target = Set.univ := by
  constructor
  · apply Set.eq_univ_iff_forall.mpr
    intro z
    have hz : z ∈ (originalPolytopeNativeModelChart γ hsmooth v).target := by
      rw [originalPolytopeNativeModelChart_target]
      exact Set.mem_univ _
    refine ⟨hz, ?_⟩
    rw [cornerModel_source]
    exact (originalPolytopeNativeModelChart γ hsmooth v).map_target hz
  · apply Set.eq_univ_iff_forall.mpr
    intro z
    have hz : z ∈ (originalGuilleminCornerModelChart γ hsmooth v).target := by
      rw [cornerModel_target]
      exact Set.mem_univ _
    refine ⟨hz, ?_⟩
    change (originalGuilleminCornerModelChart γ hsmooth v).symm z ∈
      (originalPolytopeNativeModelChart γ hsmooth v).source
    rw [← cornerModel_source]
    exact (originalGuilleminCornerModelChart γ hsmooth v).map_target hz

/-- Original-character coordinates in the SAME original Guillemin edge basis. -/
theorem originalGuilleminCornerPiChart_orbit (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (a : Fin n → ℂˣ) (j : Fin n) :
    originalGuilleminCornerPiChart γ hsmooth v (originalPolytopeNativeOrbitMap γ a) j =
      (latticeCharacter (originalVertexHalfspaceBasis γ hsmooth v j) a : ℂ) := by
  have hp : originalPolytopeNativeOrbitMap γ a ∈
      (originalGuilleminCornerPiChart γ hsmooth v).source := by
    rw [(originalGuilleminCornerPiChart_spec γ hsmooth v).2.2.1]
    exact originalPolytopeNativeOrbitMap_mem_chart_source γ hsmooth v a
  have h := (originalGuilleminCornerPiChart_spec γ hsmooth v).2.2.2.2.2 _ hp
    (monomialOrbitVector (originalPolytopeFullExponents γ) a)
    (monomialOrbitVector_ne_zero (originalPolytopeFullExponents γ) a) rfl
  rw [h.2 j]
  change (latticeCharacter _ a : ℂ) / (latticeCharacter _ a : ℂ) = _
  rw [← Units.val_div_eq_div_val, ← originalLatticeCharacter_sub, cornerNeighbor_difference]

private theorem cornerTransition_coordinate (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (w v : latticePolytopeVertices γ)
    (z : ComplexModel n)
    (hz : z ∈ (originalGuilleminCornerNativeTransition γ hsmooth w v).source) (j : Fin n) :
    originalPolytopeNativeModelEquiv n (originalGuilleminCornerNativeTransition γ hsmooth w v z) j =
      originalPolytopeNativeVector γ hsmooth w (originalPolytopeNativeModelEquiv n z)
          (originalGuilleminCornerNeighborIndex γ hsmooth v j) /
        originalPolytopeNativeVector γ hsmooth w (originalPolytopeNativeModelEquiv n z)
          (originalPolytopeNativeVertexIndex γ v) := by
  have hp : (originalPolytopeNativeModelChart γ hsmooth w).symm z ∈
      (originalGuilleminCornerPiChart γ hsmooth v).source := by
    rw [(originalGuilleminCornerPiChart_spec γ hsmooth v).2.2.1]
    have h := hz.2
    rw [cornerModel_source, originalPolytopeNativeModelChart_source] at h
    exact h
  have h := (originalGuilleminCornerPiChart_spec γ hsmooth v).2.2.2.2.2 _ hp
    (originalPolytopeNativeVector γ hsmooth w (originalPolytopeNativeModelEquiv n z))
    (originalPolytopeNativeVector_ne_zero γ hsmooth w _)
    (originalPolytopeNativePiChart_symm_val γ hsmooth w _)
  change originalPolytopeNativeModelEquiv n
    ((originalPolytopeNativeModelEquiv n).symm
      (originalGuilleminCornerPiChart γ hsmooth v
        ((originalPolytopeNativeModelChart γ hsmooth w).symm z))) j = _
  rw [(originalPolytopeNativeModelEquiv n).apply_symm_apply]
  exact h.2 j

/-- Genuine analytic division is restricted to the actual nonzero-denominator
source of this original native-to-corner transition. -/
theorem analyticOnNhd_originalGuilleminCornerNativeTransition (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (w v : latticePolytopeVertices γ) :
    AnalyticOnNhd ℂ (originalGuilleminCornerNativeTransition γ hsmooth w v)
      (originalGuilleminCornerNativeTransition γ hsmooth w v).source := by
  intro z hz
  let F : (Fin n → ℂ) → (Fin n → ℂ) := fun u j =>
    originalPolytopeNativeVector γ hsmooth w u (originalGuilleminCornerNeighborIndex γ hsmooth v j) /
      originalPolytopeNativeVector γ hsmooth w u (originalPolytopeNativeVertexIndex γ v)
  have hF : AnalyticAt ℂ F (originalPolytopeNativeModelEquiv n z) := by
    apply AnalyticAt.pi
    intro j
    exact (analyticAt_originalPolytopeNativeVector_coord γ hsmooth w
      (originalGuilleminCornerNeighborIndex γ hsmooth v j) _).div
      (analyticAt_originalPolytopeNativeVector_coord γ hsmooth w
        (originalPolytopeNativeVertexIndex γ v) _)
      ((originalGuilleminCornerNativeTransition_source_iff γ hsmooth w v z).mp hz)
  have hA := ((originalPolytopeNativeModelEquiv n).symm.toContinuousLinearMap.analyticAt _).comp
    (hF.comp ((originalPolytopeNativeModelEquiv n).toContinuousLinearMap.analyticAt z))
  apply hA.congr
  filter_upwards [(originalGuilleminCornerNativeTransition γ hsmooth w v).open_source.mem_nhds hz]
    with u hu
  apply (originalPolytopeNativeModelEquiv n).injective
  ext j
  change originalPolytopeNativeModelEquiv n
    ((originalPolytopeNativeModelEquiv n).symm (F (originalPolytopeNativeModelEquiv n u))) j = _
  rw [(originalPolytopeNativeModelEquiv n).apply_symm_apply]
  exact (cornerTransition_coordinate γ hsmooth w v u hu j).symm

private theorem analyticAt_cornerVector_coord (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (i : Fin (originalPolytopeFullIndexSize γ + 1)) (z : Fin n → ℂ) :
    AnalyticAt ℂ (fun u => monomialVertexVector (originalVertexHalfspaceBasis γ hsmooth v)
      (originalPolytopeFullExponents γ) (originalPolytopeNativeVertexIndex γ v) u i) z := by
  change AnalyticAt ℂ (fun u : Fin n → ℂ => ∏ j : Fin n,
    u j ^ monomialVertexExponent (originalVertexHalfspaceBasis γ hsmooth v)
      (originalPolytopeFullExponents γ) (originalPolytopeNativeVertexIndex γ v) i j) z
  exact Finset.analyticAt_fun_prod Finset.univ (fun j _ =>
    ((ContinuousLinearMap.proj j : (Fin n → ℂ) →L[ℂ] ℂ).analyticAt z).pow _)

private theorem cornerTransitionInverse_coordinate (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (w v : latticePolytopeVertices γ)
    (z : ComplexModel n)
    (hz : z ∈ (originalGuilleminCornerNativeTransition γ hsmooth w v).target) :
    monomialVertexVector (originalVertexHalfspaceBasis γ hsmooth v) (originalPolytopeFullExponents γ)
      (originalPolytopeNativeVertexIndex γ v) (originalPolytopeNativeModelEquiv n z)
        (originalPolytopeNativeVertexIndex γ w) ≠ 0 ∧ ∀ j,
    originalPolytopeNativeModelEquiv n
        ((originalGuilleminCornerNativeTransition γ hsmooth w v).symm z) j =
      monomialVertexVector (originalVertexHalfspaceBasis γ hsmooth v)
          (originalPolytopeFullExponents γ) (originalPolytopeNativeVertexIndex γ v)
          (originalPolytopeNativeModelEquiv n z) (originalPolytopeNativeNeighborIndex γ hsmooth w j) /
        monomialVertexVector (originalVertexHalfspaceBasis γ hsmooth v)
          (originalPolytopeFullExponents γ) (originalPolytopeNativeVertexIndex γ v)
          (originalPolytopeNativeModelEquiv n z) (originalPolytopeNativeVertexIndex γ w) := by
  have hp : (originalGuilleminCornerModelChart γ hsmooth v).symm z ∈
      (originalPolytopeNativePiChart γ hsmooth w).source := by
    have h := hz.2
    change (originalGuilleminCornerModelChart γ hsmooth v).symm z ∈
      (originalPolytopeNativeModelChart γ hsmooth w).source at h
    rwa [originalPolytopeNativeModelChart_source] at h
  have h := (originalPolytopeNativePiChart_spec γ hsmooth w).2.2.2.2.2 _ hp
    (monomialVertexVector (originalVertexHalfspaceBasis γ hsmooth v)
      (originalPolytopeFullExponents γ) (originalPolytopeNativeVertexIndex γ v)
      (originalPolytopeNativeModelEquiv n z))
    (monomialVertexVector_ne_zero _ _ _ _)
    ((originalGuilleminCornerPiChart_spec γ hsmooth v).2.2.2.1
      (originalPolytopeNativeModelEquiv n z))
  refine ⟨h.1, ?_⟩
  intro j
  change originalPolytopeNativeModelEquiv n
    ((originalPolytopeNativeModelEquiv n).symm
      (originalPolytopeNativePiChart γ hsmooth w
        ((originalGuilleminCornerModelChart γ hsmooth v).symm z))) j = _
  rw [(originalPolytopeNativeModelEquiv n).apply_symm_apply]
  exact h.2 j

/-- The actual inverse is analytic on its actual target, including every
coordinate-zero pattern permitted by the original nonzero vertex denominator. -/
theorem analyticOnNhd_originalGuilleminCornerNativeTransition_symm (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (w v : latticePolytopeVertices γ) :
    AnalyticOnNhd ℂ (originalGuilleminCornerNativeTransition γ hsmooth w v).symm
      (originalGuilleminCornerNativeTransition γ hsmooth w v).target := by
  intro z hz
  let V : (Fin n → ℂ) → Fin (originalPolytopeFullIndexSize γ + 1) → ℂ :=
    monomialVertexVector (originalVertexHalfspaceBasis γ hsmooth v)
      (originalPolytopeFullExponents γ) (originalPolytopeNativeVertexIndex γ v)
  let F : (Fin n → ℂ) → (Fin n → ℂ) := fun u j =>
    V u (originalPolytopeNativeNeighborIndex γ hsmooth w j) /
      V u (originalPolytopeNativeVertexIndex γ w)
  have hF : AnalyticAt ℂ F (originalPolytopeNativeModelEquiv n z) := by
    apply AnalyticAt.pi
    intro j
    exact (analyticAt_cornerVector_coord γ hsmooth v
      (originalPolytopeNativeNeighborIndex γ hsmooth w j) _).div
      (analyticAt_cornerVector_coord γ hsmooth v (originalPolytopeNativeVertexIndex γ w) _)
      (cornerTransitionInverse_coordinate γ hsmooth w v z hz).1
  have hA := ((originalPolytopeNativeModelEquiv n).symm.toContinuousLinearMap.analyticAt _).comp
    (hF.comp ((originalPolytopeNativeModelEquiv n).toContinuousLinearMap.analyticAt z))
  apply hA.congr
  filter_upwards [(originalGuilleminCornerNativeTransition γ hsmooth w v).symm.open_source.mem_nhds hz]
    with u hu
  apply (originalPolytopeNativeModelEquiv n).injective
  ext j
  change originalPolytopeNativeModelEquiv n
    ((originalPolytopeNativeModelEquiv n).symm (F (originalPolytopeNativeModelEquiv n u))) j = _
  rw [(originalPolytopeNativeModelEquiv n).apply_symm_apply]
  exact ((cornerTransitionInverse_coordinate γ hsmooth w v u hu).2 j).symm

end SGPT.Toric
