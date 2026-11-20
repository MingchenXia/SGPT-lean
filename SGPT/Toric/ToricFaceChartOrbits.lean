import SGPT.Toric.ToricFaceNativeEmbedding
import SGPT.Toric.ToricStratumTorus

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set SGPT.AlmostSemigroup.Counting
open SGPT.Foundations.Analysis.FirstPass
open scoped Topology BigOperators Classical
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- Every actual nonzero native vertex coordinate tuple is produced by a
GENUINE original torus element, via the actual integral character equivalence. -/
theorem latticeCharacter_basis_change_standard
    (b : Module.Basis (Fin n) ℤ (Fin n → ℤ)) (a : Fin n → ℂˣ) (j : Fin n) :
    latticeCharacter (b j) (latticeBasisChangeEquiv b (Pi.basisFun ℤ (Fin n)) a) = a j := by
  have heq := congrArg (fun χ => χ (b j))
    (latticeBasisCharacterEquiv_basisChange b (Pi.basisFun ℤ (Fin n)) a)
  have hb : latticeBasisCharacterEquiv b a (b j) = a j :=
    congrFun ((latticeBasisCharacterEquiv b).symm_apply_apply a) j
  rw [hb] at heq
  simpa only [latticeBasisCharacterEquiv_apply, Pi.basisFun_repr] using heq

/-- The actual diagonal action read back on the WHOLE original chart,
including every original boundary point and all zero coordinates. -/
theorem toricAction_vertexPoint (v : latticePolytopeVertices γ)
    (a : Fin n → ℂˣ) (z : SGPT.Foundations.Analysis.FirstPass.ComplexModel n) :
    polytopeToricAction γ hs a (vertexPoint hs v z) =
      vertexPoint hs v (originalPolytopeNativeModelActionLinear γ hs v a z) := by
  have hp := vertexPoint_mem_source (hs := hs) v z
  have hpa : polytopeToricAction γ hs a (vertexPoint hs v z) ∈
      (originalPolytopeNativeModelChart γ hs v).source := by
    rw [originalPolytopeNativeModelChart_source] at hp ⊢
    exact (originalPolytopeNativeAction_mem_chart_source_iff γ hs v a _).mpr hp
  calc
    polytopeToricAction γ hs a (vertexPoint hs v z) =
      vertexPoint hs v (originalPolytopeNativeModelChart γ hs v
        (polytopeToricAction γ hs a (vertexPoint hs v z))) := (vertexPoint_chart v hpa).symm
    _ = _ := by
      apply congrArg (vertexPoint hs v)
      change originalPolytopeNativeModelChart γ hs v
        (originalPolytopeNativeAction γ a (vertexPoint hs v z)) = _
      rw [originalPolytopeNativeModelChart_action γ hs v a _ hp, chart_vertexPoint]

/-- The same actual whole chart in Pi and Euclidean coordinates. -/
theorem nativePiChart_symm_eq_vertexPoint (v : latticePolytopeVertices γ) (z : Fin n → ℂ) :
    (originalPolytopeNativePiChart γ hs v).symm z = vertexPoint hs v (modelPoint z) := rfl

/-- Actual selected native indices of an arbitrary original flag stage. -/
def toricFlagSelectedIndices (e : Fin n ≃ Fin n) (i : Fin (n + 1)) : Set (Fin n) :=
  e '' {l | (l : ℕ) < i.val}

/-- Its image is the actual original cone-ray set. -/
theorem toricFlagRays_eq_selectedIndices (v : latticePolytopeVertices γ)
    (e : Fin n ≃ Fin n) (i : Fin (n + 1)) :
    toricFlagRays hs v e i = polytopeToricRay γ hs v '' toricFlagSelectedIndices e i := by
  rw [toricFlagSelectedIndices, Set.image_image]
  rfl

/-- The actual base-chart zero pattern is precisely the selected source
indices, by genuine original ray injectivity. -/
theorem mem_flagChartIndices_self_iff_selected (v : latticePolytopeVertices γ)
    (e : Fin n ≃ Fin n) (i : Fin (n + 1)) (k : Fin n) :
    k ∈ flagChartIndices (hs := hs) v e v i ↔ k ∈ toricFlagSelectedIndices e i := by
  rw [mem_flagChartIndices]
  constructor
  · rintro ⟨l, hl, hkl⟩
    exact ⟨l, hl, (polytopeToricRayGenerator_injective hs v hkl).symm⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l, hl, rfl⟩

/-- The actual distinguished orbit point belongs to the actual face-model
image, by the literal homogeneous boundary-orbit identity. -/
theorem toricFlag_basePoint_mem_faceImage (v : latticePolytopeVertices γ)
    (e : Fin n ≃ Fin n) (i : Fin (n + 1)) :
    vertexPoint hs v (flagModelPoint (flagChartIndices (hs := hs) v e v i)) ∈
      Set.range (toricFaceNativeEmbedding (hs := hs) v (toricFlagSelectedIndices e i)) := by
  refine ⟨originalPolytopeNativeOrbitMap
    (toricFaceProjectedFamily (hs := hs) v (toricFlagSelectedIndices e i)) 1, ?_⟩
  rw [toricFaceNativeEmbedding_orbit, nativePiChart_symm_eq_vertexPoint]
  apply congrArg (vertexPoint hs v)
  ext k
  simp only [modelPoint_apply, toricFaceBoundaryCoordinates, flagModelPoint, zeroCoords]
  by_cases hk : k ∈ toricFlagSelectedIndices e i
  · have hk' := (mem_flagChartIndices_self_iff_selected (hs := hs) v e i k).mpr hk
    simp only [dif_pos hk, if_pos hk']
  · have hk' := (mem_flagChartIndices_self_iff_selected (hs := hs) v e i k).not.mpr hk
    simp only [dif_neg hk, if_neg hk', Pi.one_apply, Units.val_one]

/-- Every ACTUAL ambient torus translate of the distinguished orbit point
is in the same actual face-model image. The quotient coordinates are actual
original edge characters, not an assumed action presentation. -/
theorem toricFlag_action_basePoint_mem_faceImage (v : latticePolytopeVertices γ)
    (e : Fin n ≃ Fin n) (i : Fin (n + 1)) (a : Fin n → ℂˣ) :
    polytopeToricAction γ hs a
      (vertexPoint hs v (flagModelPoint (flagChartIndices (hs := hs) v e v i))) ∈
      Set.range (toricFaceNativeEmbedding (hs := hs) v (toricFlagSelectedIndices e i)) := by
  let J := toricFlagSelectedIndices e i
  let q : Fin (toricFaceDimension J) → ℂˣ := fun j =>
    latticeCharacter (originalPolytopeNativeBasis γ hs v
      ((Fintype.equivFin {j : Fin n // j ∉ J}).symm j).val) a
  refine ⟨originalPolytopeNativeOrbitMap (toricFaceProjectedFamily (hs := hs) v J) q, ?_⟩
  rw [toricFaceNativeEmbedding_orbit, nativePiChart_symm_eq_vertexPoint, toricAction_vertexPoint]
  apply congrArg (vertexPoint hs v)
  ext k
  rw [vertexAction_apply]
  simp only [modelPoint_apply, flagModelPoint, zeroCoords]
  by_cases hk : k ∈ J
  · have hk' := (mem_flagChartIndices_self_iff_selected (hs := hs) v e i k).mpr hk
    simp only [if_pos hk', mul_zero]
    exact dif_pos hk
  · have hk' : k ∉ flagChartIndices (hs := hs) v e v i :=
      (mem_flagChartIndices_self_iff_selected v e i k).not.mpr hk
    simp only [if_neg hk', mul_one]
    change (if _hk : k ∈ J then (0 : ℂ) else _) = _
    rw [dif_neg hk]
    change (latticeCharacter (originalPolytopeNativeBasis γ hs v
      ((Fintype.equivFin {j : Fin n // j ∉ J}).symm
        ((Fintype.equivFin {j : Fin n // j ∉ J}) ⟨k, hk⟩)).val) a : ℂ) = _
    rw [Equiv.symm_apply_apply]

/-- In EVERY actual chart containing the source cone, every point with
nonzero free coordinates belongs to the SAME actual face-model image.
The original common distinguished orbit point is proved in production. -/
theorem toricFlag_unitChartPoint_mem_faceImage (v : latticePolytopeVertices γ)
    (e : Fin n ≃ Fin n) (i : Fin (n + 1))
    (w : latticePolytopeVertices γ) (hw : FlagRaysIn (hs := hs) v e w i)
    (z : SGPT.Foundations.Analysis.FirstPass.ComplexModel n) (hz : z ∈ complexTorus n) :
    vertexPoint hs w (zeroCoords (flagChartIndices (hs := hs) v e w i) z) ∈
      Set.range (toricFaceNativeEmbedding (hs := hs) v (toricFlagSelectedIndices e i)) := by
  let t : Fin n → ℂˣ := fun j => Units.mk0 (z j) (hz j)
  let a := latticeBasisChangeEquiv (originalPolytopeNativeBasis γ hs w) (Pi.basisFun ℤ (Fin n)) t
  have hpoint : polytopeToricAction γ hs a
      (vertexPoint hs w (flagModelPoint (flagChartIndices (hs := hs) v e w i))) =
      vertexPoint hs w (zeroCoords (flagChartIndices (hs := hs) v e w i) z) := by
    rw [toricAction_vertexPoint]
    apply congrArg (vertexPoint hs w)
    ext k
    rw [vertexAction_apply, latticeCharacter_basis_change_standard]
    simp only [flagModelPoint, zeroCoords, modelPoint_apply]
    split_ifs <;> simp [t]
  rw [← hpoint, vertexPoint_flagModelPoint v e hw]
  exact toricFlag_action_basePoint_mem_faceImage v e i a

/-- The actual original face-model image is EXACTLY the original orbit
closure, in arbitrary original flag codimension. Density of the genuine free
unit coordinates and actual compactness prove all remaining boundary points. -/
theorem range_toricFaceNativeEmbedding_eq_toricFlag (v : latticePolytopeVertices γ)
    (e : Fin n ≃ Fin n) (i : Fin (n + 1)) :
    Set.range (toricFaceNativeEmbedding (hs := hs) v (toricFlagSelectedIndices e i)) =
      toricFlag hs v e i := by
  apply Set.Subset.antisymm
  · rintro _ ⟨p, rfl⟩
    have hp := toricFaceNativeEmbedding_mem_orbitClosure v (toricFlagSelectedIndices e i) p
    rw [← toricFlagRays_eq_selectedIndices] at hp
    exact hp
  · rw [toricFlag_eq_iUnion]
    intro p hp
    obtain ⟨w, z, rfl⟩ := by
      simpa only [Set.mem_iUnion, Set.mem_range] using hp
    let f := fun z => vertexPoint hs w.val (zeroCoords (flagChartIndices (hs := hs) v e w.val i) z)
    have hf : Continuous f := (continuous_vertexPoint (hs := hs) w.val).comp (continuous_zeroCoords _)
    have hclosed : IsClosed (Set.range (toricFaceNativeEmbedding (hs := hs) v (toricFlagSelectedIndices e i))) :=
      (isCompact_range (continuous_toricFaceNativeEmbedding (hs := hs) v (toricFlagSelectedIndices e i))).isClosed
    have hsubset : f '' complexTorus n ⊆
        Set.range (toricFaceNativeEmbedding (hs := hs) v (toricFlagSelectedIndices e i)) := by
      rintro _ ⟨x, hx, rfl⟩
      exact toricFlag_unitChartPoint_mem_faceImage v e i w.val w.property x hx
    exact (closure_minimal hsubset hclosed) (mem_closure_image hf.continuousAt (dense_complexTorus z))

end SGPT.Toric
