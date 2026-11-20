import SGPT.Toric.ToricFaceFlagHomeomorph
import SGPT.Toric.ToricFaceNativeHolomorphic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set SGPT.AlmostSemigroup.Counting
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open scoped Topology BigOperators Manifold ContDiff Classical
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- The actual source cone codimension is the actual free character rank,
including empty and full cones. Original ray injectivity produces the count. -/
theorem toricFaceDimension_flagSelectedIndices
    (e : Fin n ≃ Fin n) (i : Fin (n + 1)) :
    toricFaceDimension (toricFlagSelectedIndices e i) = n - i.val := by
  have hset : Finset.univ.filter (fun k : Fin n => k ∈ toricFlagSelectedIndices e i) =
      (Finset.univ.filter (fun l : Fin n => l.val < i.val)).map e.toEmbedding := by
    ext k
    simp [toricFlagSelectedIndices]
  have hsel : (Finset.univ.filter (fun k : Fin n => k ∈ toricFlagSelectedIndices e i)).card = i.val := by
    rw [hset, Finset.card_map, Fin.card_filter_val_lt]
    omega
  have hsum := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun k : Fin n => k ∈ toricFlagSelectedIndices e i)
  simp only [Finset.card_univ, Fintype.card_fin] at hsum
  unfold toricFaceDimension
  rw [Fintype.card_subtype]
  omega

/-- The actual inherited original regularity, in the independently produced
free-lattice rank of the face model. -/
theorem toricFaceFlag_regular (v : latticePolytopeVertices γ)
    (e : Fin n ≃ Fin n) (i : Fin (n + 1)) :
    ∀ p ∈ toricFlag hs v e i, RegularAtDim (n := n) (toricFlag hs v e i) p
      (toricFaceDimension (toricFlagSelectedIndices e i)) := by
  rw [toricFaceDimension_flagSelectedIndices e i]
  exact fun p hp => regularAtDim_toricFlag (hs := hs) v e i hp

/-- Actual dimension bound of the genuine inherited stratum. -/
theorem toricFaceFlag_dimension_le
    (e : Fin n ≃ Fin n) (i : Fin (n + 1)) :
    toricFaceDimension (toricFlagSelectedIndices e i) ≤ n := by
  rw [toricFaceDimension_flagSelectedIndices e i]
  exact Nat.sub_le _ _

/-- The SAME original inherited flattening charts, with dimension equality
proved from actual original rays rather than assumed as model data. -/
@[instance_reducible] def toricFaceFlagCharts (v : latticePolytopeVertices γ)
    (e : Fin n ≃ Fin n) (i : Fin (n + 1)) :
    ChartedSpace (ComplexModel (toricFaceDimension (toricFlagSelectedIndices e i))) (toricFlag hs v e i) :=
  SubmanifoldChartedSpace.chartedSpace (toricFaceFlag_dimension_le e i)
    (toricFaceFlag_regular (hs := hs) v e i)

/-- Its genuine original inherited complex structure. -/
theorem toricFaceFlag_isComplexManifold (v : latticePolytopeVertices γ)
    (e : Fin n ≃ Fin n) (i : Fin (n + 1)) :
    letI := toricFaceFlagCharts (hs := hs) v e i
    IsComplexManifold (toricFaceDimension (toricFlagSelectedIndices e i)) (toricFlag hs v e i) :=
  SubmanifoldChartedSpace.isComplexManifold_chartedSpace (toricFaceFlag_dimension_le e i)
    (toricFaceFlag_regular (hs := hs) v e i)

/-- The literal actual inclusion into X is holomorphic in these inherited charts. -/
theorem contMDiff_toricFaceFlag_val (v : latticePolytopeVertices γ)
    (e : Fin n ≃ Fin n) (i : Fin (n + 1)) :
    letI := toricFaceFlagCharts (hs := hs) v e i
    ContMDiff 𝓘(ℂ, ComplexModel (toricFaceDimension (toricFlagSelectedIndices e i))) 𝓘(ℂ, ComplexModel n) ∞
      (Subtype.val : toricFlag hs v e i → PolytopeToricVariety γ hs) :=
  SubmanifoldChartedSpace.contMDiff_val (toricFaceFlag_dimension_le e i)
    (toricFaceFlag_regular (hs := hs) v e i)

/-- The ACTUAL face-model/original-stratum homeomorphism is holomorphic
FORWARD in the two genuine native/inherited atlases. Corestriction uses the
proved whole original image; no target atlas comparison is supplied. -/
theorem contMDiff_toricFaceFlagHomeomorph (v : latticePolytopeVertices γ)
    (e : Fin n ≃ Fin n) (i : Fin (n + 1)) :
    letI := originalPolytopeNativeChartedSpace
      (toricFaceProjectedFamily (hs := hs) v (toricFlagSelectedIndices e i))
      (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v (toricFlagSelectedIndices e i))
    letI := toricFaceFlagCharts (hs := hs) v e i
    ContMDiff 𝓘(ℂ, ComplexModel (toricFaceDimension (toricFlagSelectedIndices e i)))
      𝓘(ℂ, ComplexModel (toricFaceDimension (toricFlagSelectedIndices e i))) ∞
      (toricFaceFlagHomeomorph (hs := hs) v e i) := by
  let := originalPolytopeNativeChartedSpace
    (toricFaceProjectedFamily (hs := hs) v (toricFlagSelectedIndices e i))
    (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v (toricFlagSelectedIndices e i))
  let := originalPolytopeNativeChartedSpace γ hs
  have := originalPolytopeNativeIsComplexManifold
    (toricFaceProjectedFamily (hs := hs) v (toricFlagSelectedIndices e i))
    (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v (toricFlagSelectedIndices e i))
  have := originalPolytopeNativeIsComplexManifold γ hs
  exact SubmanifoldCodRestrict.contMDiff_codRestrict (toricFaceFlag_dimension_le e i)
    (toricFaceFlag_regular (hs := hs) v e i)
    (contMDiff_toricFaceNativeEmbedding (hs := hs) v (toricFlagSelectedIndices e i))
    (fun p => (toricFaceFlagHomeomorph (hs := hs) v e i p).property)

end SGPT.Toric
