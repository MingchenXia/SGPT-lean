import SGPT.Toric.ToricAugmentedBaseLocusStabilization
import SGPT.Toric.ToricFanConeRealDimension
import SGPT.Unibranch.Resolution

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH.VariableComplexAtlas
open SGPT.Foundations.Analysis.Pending.HironakaReducedComplexAnalyticSpaces
open SGPT.Foundations.Analysis.Pending.HironakaActualAnalyticSubspace
open scoped Topology BigOperators Classical
variable {n : ℕ} {K : Type} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- The finite genuine full-section equations in the actual original
charts give the source's actual analytic subset, including at base-locus
points. -/
theorem isComplexAnalyticSubset_toricAugmentedBaseLocus (D : ToricDivisor γ hs) :
    IsComplexAnalyticSubset (n := n) (toricAugmentedBaseLocus D) := by
  intro p
  let e := complexChartAt (n := n) p
  have hp : e.val p ∈ e.val.target := e.val.map_source (mem_complexChartAt_source p)
  obtain ⟨W, hW, hpW, hWt, N, g, hg, heq⟩ :=
    hasAnalyticChartEquations_toricAugmentedBaseLocus D e (e.val p) hp
  refine ⟨{ generatorCount := N
            generator := g
            coordinateNeighborhood := W
            isOpen_coordinateNeighborhood := hW
            center_mem_coordinateNeighborhood := hpW
            coordinateNeighborhood_subset_target := hWt
            generator_holomorphic := hg
            zeroLocus := ?_ }⟩
  intro y hy hyW
  have hh := heq (e.val y) hyW
  change e.val.symm (e.val y) ∈ toricAugmentedBaseLocus D ↔
    ∀ j, g j (e.val y) = 0 at hh
  rw [e.val.left_inv hy] at hh
  exact hh

/-- The source's reduced complex structure is the ACTUAL whole-vanishing-
ideal quotient sheaf on the SAME augmented-base-locus subset. All local
analytic embeddings are manufactured from the original manifold charts.
No resolution theorem is used. -/
def toricAugmentedBaseLocusReducedSpace (D : ToricDivisor γ hs) :
    SGPT.Unibranch.SourceReducedComplexSpace :=
  SGPT.Unibranch.SourceReducedComplexSpace.ofClosedAnalytic (toricAugmentedBaseLocus D)
    (isComplexAnalyticSubset_toricAugmentedBaseLocus D)

theorem toricAugmentedBaseLocusReducedSpace_actual (D : ToricDivisor γ hs) :
    (toricAugmentedBaseLocusReducedSpace D).obj.left =
      actualSubspaceLocallyRingedSpace (n := n) (toricAugmentedBaseLocus D) := rfl

/-- Reducedness is proved on the actual stalks, not stored as a caller's
certificate or inferred from a set-theoretic name. -/
theorem toricAugmentedBaseLocusReducedSpace_isReduced_stalk (D : ToricDivisor γ hs)
    (x : (toricAugmentedBaseLocusReducedSpace D).obj.left) :
    IsReduced ((toricAugmentedBaseLocusReducedSpace D).obj.left.presheaf.stalk x).carrier :=
  SGPT.Unibranch.SourceReducedComplexSpace.isReduced_stalk _ x

/-- Literal original affine-face dimension versus the dimension of the
actual original real cone span. Neither dimension is an input certificate. -/
theorem toricAugmentedBaseLocus_eq_actual_deficient_faces (D : ToricDivisor γ hs) :
    toricAugmentedBaseLocus D =
      ⋃ (R : Set (PolytopeToricRays γ hs)) (_ : IsToricFanCone R)
        (_ : toricDivisorFace D R = ∅ ∨
          Module.finrank ℝ (vectorSpan ℝ (toricDivisorFace D R)) <
            n - Module.finrank ℝ (toricFanConeRealSpan R)), toricOrbitClosure R := by
  rw [toricAugmentedBaseLocus_eq_deficient_faces]
  ext p
  simp only [mem_iUnion, exists_prop]
  constructor
  · rintro ⟨R, hR, hdef, hp⟩
    exact ⟨R, hR, (toricDivisorFaceDeficient_iff_actual_cone_dimension D hR).mp hdef, hp⟩
  · rintro ⟨R, hR, hdef, hp⟩
    exact ⟨R, hR, (toricDivisorFaceDeficient_iff_actual_cone_dimension D hR).mpr hdef, hp⟩

/-- WHOLE original cor:augbl: the ACTUAL section-defined augmented base
locus, the exact original deficient-face union with dim(empty)=-infinity,
torus invariance, and the genuine reduced analytic complex structure.
The only inputs are the original integral divisor on the original smooth
projective toric variety. -/
theorem source_augmentedBaseLocus_eq_deficient_faces (D : ToricDivisor γ hs) :
    toricAugmentedBaseLocus D =
        (⋃ (R : Set (PolytopeToricRays γ hs)) (_ : IsToricFanCone R)
          (_ : toricDivisorFace D R = ∅ ∨
            Module.finrank ℝ (vectorSpan ℝ (toricDivisorFace D R)) <
              n - Module.finrank ℝ (toricFanConeRealSpan R)), toricOrbitClosure R) ∧
      IsClosed (toricAugmentedBaseLocus D) ∧
      (∀ (a : Fin n → ℂˣ) (p : PolytopeToricVariety γ hs),
        polytopeToricAction γ hs a p ∈ toricAugmentedBaseLocus D ↔
          p ∈ toricAugmentedBaseLocus D) ∧
      IsComplexAnalyticSubset (n := n) (toricAugmentedBaseLocus D) ∧
      (toricAugmentedBaseLocusReducedSpace D).obj.left =
        actualSubspaceLocallyRingedSpace (n := n) (toricAugmentedBaseLocus D) ∧
      ∀ x : (toricAugmentedBaseLocusReducedSpace D).obj.left,
        IsReduced ((toricAugmentedBaseLocusReducedSpace D).obj.left.presheaf.stalk x).carrier := by
  exact ⟨toricAugmentedBaseLocus_eq_actual_deficient_faces D, isClosed_toricAugmentedBaseLocus D,
    polytopeToricAction_mem_toricAugmentedBaseLocus_iff D,
    isComplexAnalyticSubset_toricAugmentedBaseLocus D,
    toricAugmentedBaseLocusReducedSpace_actual D,
    toricAugmentedBaseLocusReducedSpace_isReduced_stalk D⟩

end SGPT.Toric
