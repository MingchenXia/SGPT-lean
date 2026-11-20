import SGPT.Toric.ToricFaceBoundaryOrbit

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set SGPT.AlmostSemigroup.Counting
open scoped Topology BigOperators Classical
attribute [local instance] monomialProjectiveTopology
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- The actual original dense orbit of the constructed face model maps to
the actual boundary torus point in the SAME ambient vertex chart. -/
theorem toricFaceProjectiveEmbedding_orbit
    (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (a : Fin (toricFaceDimension J) → ℂˣ) :
    toricFaceProjectiveEmbedding (hs := hs) v J
      (monomialProjectiveOrbit (originalPolytopeFullExponents (toricFaceProjectedFamily (hs := hs) v J)) a) =
      ((originalPolytopeNativePiChart γ hs v).symm (toricFaceBoundaryCoordinates J a)).val := by
  rw [originalPolytopeNativePiChart_symm_val]
  change Projectivization.mk ℂ
    (toricFaceHomogeneousZeroExtension (hs := hs) v J
      (monomialOrbitVector (originalPolytopeFullExponents (toricFaceProjectedFamily (hs := hs) v J)) a)) _ = _
  congr 1
  exact (nativeVector_toricFaceBoundary_eq_zeroExtension (hs := hs) v J a).symm

/-- The actual boundary orbit point lies on the SAME original orbit closure,
proved from the original whole-chart coordinate-zero equations. -/
theorem toricFaceBoundaryPoint_mem_orbitClosure
    (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (a : Fin (toricFaceDimension J) → ℂˣ) :
    (originalPolytopeNativePiChart γ hs v).symm (toricFaceBoundaryCoordinates J a) ∈
      toricOrbitClosure (polytopeToricRay γ hs v '' J) := by
  let p := (originalPolytopeNativePiChart γ hs v).symm (toricFaceBoundaryCoordinates J a)
  have hz : toricFaceBoundaryCoordinates J a ∈ (originalPolytopeNativePiChart γ hs v).target := by
    rw [originalPolytopeNativePiChart_target]
    exact mem_univ _
  have hp : p ∈ (originalPolytopeNativeModelChart γ hs v).source := by
    rw [originalPolytopeNativeModelChart_source]
    exact (originalPolytopeNativePiChart γ hs v).map_target hz
  apply (mem_toricOrbitClosure_iff_chart hp).mpr
  rintro ρ ⟨k, hk, rfl⟩
  refine ⟨k, rfl, ?_⟩
  change (originalPolytopeNativeModelEquiv n).symm
    (originalPolytopeNativePiChart γ hs v p) k = 0
  rw [(originalPolytopeNativePiChart γ hs v).right_inv hz]
  exact dif_pos hk

/-- Continuity and the ORIGINAL target dense-orbit closure internally prove
that EVERY actual face-model point maps to the SAME actual ambient toric
variety. No image-membership presentation is assumed. -/
theorem toricFaceProjectiveEmbedding_mem_nativeSpace
    (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (p : originalPolytopeNativeSpace (toricFaceProjectedFamily (hs := hs) v J)) :
    toricFaceProjectiveEmbedding (hs := hs) v J p.val ∈
      monomialProjectiveOrbitClosure (originalPolytopeFullExponents γ) := by
  have hclosed : IsClosed ((toricFaceProjectiveEmbedding (hs := hs) v J) ⁻¹'
      monomialProjectiveOrbitClosure (originalPolytopeFullExponents γ)) :=
    isClosed_closure.preimage (continuous_toricFaceProjectiveEmbedding v J)
  have hsubset : Set.range (monomialProjectiveOrbit
      (originalPolytopeFullExponents (toricFaceProjectedFamily (hs := hs) v J))) ⊆
      (toricFaceProjectiveEmbedding (hs := hs) v J) ⁻¹'
        monomialProjectiveOrbitClosure (originalPolytopeFullExponents γ) := by
    rintro _ ⟨a, rfl⟩
    rw [Set.mem_preimage, toricFaceProjectiveEmbedding_orbit]
    exact ((originalPolytopeNativePiChart γ hs v).symm (toricFaceBoundaryCoordinates J a)).property
  exact closure_minimal hsubset hclosed p.property

/-- The actual linear projective map restricted to the SAME original toric
closures. No abstract face variety carrier replaces either side. -/
def toricFaceNativeEmbedding (v : latticePolytopeVertices γ) (J : Set (Fin n)) :
    originalPolytopeNativeSpace (toricFaceProjectedFamily (hs := hs) v J) →
      originalPolytopeNativeSpace γ :=
  fun p => ⟨toricFaceProjectiveEmbedding (hs := hs) v J p.val,
    toricFaceProjectiveEmbedding_mem_nativeSpace v J p⟩

/-- Genuine continuity in the original subspace quotient topologies. -/
theorem continuous_toricFaceNativeEmbedding (v : latticePolytopeVertices γ) (J : Set (Fin n)) :
    Continuous (toricFaceNativeEmbedding (hs := hs) v J) :=
  ((continuous_toricFaceProjectiveEmbedding (hs := hs) v J).comp continuous_subtype_val).subtype_mk _

/-- The same actual projective injection proves injectivity on the actual
original toric closures. -/
theorem toricFaceNativeEmbedding_injective (v : latticePolytopeVertices γ) (J : Set (Fin n)) :
    Function.Injective (toricFaceNativeEmbedding (hs := hs) v J) := by
  intro p q hpq
  apply Subtype.ext
  exact toricFaceProjectiveEmbedding_injective v J (congrArg Subtype.val hpq)

/-- Exact dense-orbit readback of the same actual closure map. -/
theorem toricFaceNativeEmbedding_orbit
    (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (a : Fin (toricFaceDimension J) → ℂˣ) :
    toricFaceNativeEmbedding (hs := hs) v J
      (originalPolytopeNativeOrbitMap (toricFaceProjectedFamily (hs := hs) v J) a) =
      (originalPolytopeNativePiChart γ hs v).symm (toricFaceBoundaryCoordinates J a) := by
  apply Subtype.ext
  exact toricFaceProjectiveEmbedding_orbit v J a

/-- EVERY actual face-model point belongs to the SAME actual orbit closure.
The original dense-orbit result and genuine closedness derive the inclusion
for ALL boundary points, rather than storing it as a model certificate. -/
theorem toricFaceNativeEmbedding_mem_orbitClosure
    (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (p : originalPolytopeNativeSpace (toricFaceProjectedFamily (hs := hs) v J)) :
    toricFaceNativeEmbedding (hs := hs) v J p ∈
      toricOrbitClosure (polytopeToricRay γ hs v '' J) := by
  have hclosed : IsClosed ((toricFaceNativeEmbedding (hs := hs) v J) ⁻¹'
      toricOrbitClosure (polytopeToricRay γ hs v '' J)) :=
    (isClosed_toricOrbitClosure _).preimage (continuous_toricFaceNativeEmbedding v J)
  have hsubset : Set.range (originalPolytopeNativeOrbitMap (toricFaceProjectedFamily (hs := hs) v J)) ⊆
      (toricFaceNativeEmbedding (hs := hs) v J) ⁻¹' toricOrbitClosure (polytopeToricRay γ hs v '' J) := by
    rintro _ ⟨a, rfl⟩
    rw [Set.mem_preimage, toricFaceNativeEmbedding_orbit]
    exact toricFaceBoundaryPoint_mem_orbitClosure v J a
  have hall : Set.univ ⊆ (toricFaceNativeEmbedding (hs := hs) v J) ⁻¹'
      toricOrbitClosure (polytopeToricRay γ hs v '' J) := by
    rw [← (denseRange_originalPolytopeNativeOrbitMap (toricFaceProjectedFamily (hs := hs) v J)).closure_range]
    exact closure_minimal hsubset hclosed
  exact hall (mem_univ p)

end SGPT.Toric
