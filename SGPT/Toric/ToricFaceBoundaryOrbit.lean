import SGPT.Toric.ToricFaceHomogeneousEmbedding

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set SGPT.AlmostSemigroup.Counting
open scoped Topology BigOperators Classical
attribute [local instance] monomialProjectiveTopology
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- Actual original homogeneous exponents on the face have zero selected
coordinates and EXACTLY the target full exponent on every free coordinate. -/
theorem toricFaceHomogeneous_basisCoordinate (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (i : Fin (originalPolytopeFullIndexSize (toricFaceProjectedFamily (hs := hs) v J) + 1))
    (k : Fin n) :
    (originalPolytopeNativeBasis γ hs v).repr
      (originalPolytopeFullExponents γ (toricFaceHomogeneousIndexEquiv (hs := hs) v J i).val - v.val) k =
      if hk : k ∈ J then 0 else
        originalPolytopeFullExponents (toricFaceProjectedFamily (hs := hs) v J) i
          ((Fintype.equivFin {j : Fin n // j ∉ J}) ⟨k, hk⟩) := by
  rw [toricFaceHomogeneousIndexEquiv_exponent]
  change (originalPolytopeNativeBasis γ hs v).equivFun
    (v.val + (originalPolytopeNativeBasis γ hs v).equivFun.symm _ - v.val) k = _
  rw [add_sub_cancel_left, LinearEquiv.apply_symm_apply]

/-- All actual target full exponents are nonnegative in these actual vertex
coordinates; this follows from the source polytope, not an extra model input. -/
theorem toricFaceFullExponent_nonneg (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (i : Fin (originalPolytopeFullIndexSize (toricFaceProjectedFamily (hs := hs) v J) + 1))
    (j : Fin (toricFaceDimension J)) :
    0 ≤ originalPolytopeFullExponents (toricFaceProjectedFamily (hs := hs) v J) i j := by
  let k := (Fintype.equivFin {j : Fin n // j ∉ J}).symm j
  have h := intPairing_sub_vertex_nonneg hs v k.val
    (originalPolytopeFullExponents_mem (toricFaceHomogeneousIndexEquiv (hs := hs) v J i).val)
  rw [← basis_repr_eq_intPairing, toricFaceHomogeneous_basisCoordinate, dif_neg k.property,
    Equiv.apply_symm_apply] at h
  exact h

/-- Every original homogeneous index outside the actual face has a strictly
positive selected coordinate; actual original lattice nonnegativity rules
out hidden cancellation or negative exponents. -/
theorem exists_selected_positive_coordinate_off_toricFace
    (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (i : Fin (originalPolytopeFullIndexSize γ + 1))
    (hi : integerCast (originalPolytopeFullExponents γ i) ∉ toricNativeVertexFace (hs := hs) v J) :
    ∃ k ∈ J, 0 < (originalPolytopeNativeBasis γ hs v).repr
      (originalPolytopeFullExponents γ i - v.val) k := by
  by_contra hno
  push Not at hno
  apply hi
  refine ⟨originalPolytopeFullExponents_mem i, ?_⟩
  intro k hk
  have hnonneg : 0 ≤ (originalPolytopeNativeBasis γ hs v).repr
      (originalPolytopeFullExponents γ i - v.val) k := by
    rw [basis_repr_eq_intPairing]
    exact intPairing_sub_vertex_nonneg hs v k (originalPolytopeFullExponents_mem i)
  have hzero := le_antisymm (hno k hk) hnonneg
  rw [map_sub, Finsupp.sub_apply] at hzero
  rw [integralRealBasis_repr_integerCast, integralRealBasis_repr_integerCast]
  exact congrArg (fun z : ℤ => (z : ℝ)) (sub_eq_zero.mp hzero)

/-- The ACTUAL boundary torus point in the original vertex chart: selected
ray coordinates0, and literal target unit coordinates on the free factors. -/
def toricFaceBoundaryCoordinates (J : Set (Fin n))
    (a : Fin (toricFaceDimension J) → ℂˣ) : Fin n → ℂ :=
  fun k => if hk : k ∈ J then 0 else
    (a ((Fintype.equivFin {j : Fin n // j ∉ J}) ⟨k, hk⟩) : ℂ)

/-- Every actual original homogeneous coordinate outside the face vanishes
at the actual boundary torus point, with genuine positive Nat exponents. -/
theorem nativeVector_toricFaceBoundary_off_face
    (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (a : Fin (toricFaceDimension J) → ℂˣ)
    (i : Fin (originalPolytopeFullIndexSize γ + 1))
    (hi : integerCast (originalPolytopeFullExponents γ i) ∉ toricNativeVertexFace (hs := hs) v J) :
    originalPolytopeNativeVector γ hs v (toricFaceBoundaryCoordinates J a) i = 0 := by
  obtain ⟨k, hk, hpos⟩ := exists_selected_positive_coordinate_off_toricFace v J i hi
  rw [nativeVector_apply]
  apply Finset.prod_eq_zero (Finset.mem_univ k)
  change (if _hk : k ∈ J then (0 : ℂ) else _) ^ _ = 0
  rw [dif_pos hk]
  apply zero_pow
  have hnat : 0 < ((originalPolytopeNativeBasis γ hs v).repr
      (originalPolytopeFullExponents γ i - v.val) k).toNat := by omega
  rw [basis_repr_eq_intPairing] at hnat
  exact Nat.ne_of_gt hnat

/-- On every actual original face coordinate, the boundary monomial vector
is EXACTLY the target dense-orbit monomial vector, including rank zero. -/
theorem nativeVector_toricFaceBoundary_face
    (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (a : Fin (toricFaceDimension J) → ℂˣ)
    (i : Fin (originalPolytopeFullIndexSize (toricFaceProjectedFamily (hs := hs) v J) + 1)) :
    originalPolytopeNativeVector γ hs v (toricFaceBoundaryCoordinates J a)
      (toricFaceHomogeneousIndexEquiv (hs := hs) v J i).val =
        monomialOrbitVector (originalPolytopeFullExponents (toricFaceProjectedFamily (hs := hs) v J)) a i := by
  rw [nativeVector_apply]
  simp_rw [← basis_repr_eq_intPairing]
  let f : Fin n → ℂ := fun k => toricFaceBoundaryCoordinates J a k ^
    ((originalPolytopeNativeBasis γ hs v).repr
      (originalPolytopeFullExponents γ (toricFaceHomogeneousIndexEquiv (hs := hs) v J i).val - v.val) k).toNat
  change (∏ k, f k) = _
  have hsplit := Fintype.prod_subtype_mul_prod_subtype (fun k : Fin n => k ∈ J) f
  have hzero : (∏ k : {k : Fin n // k ∈ J}, f k.val) = 1 := by
    apply Finset.prod_eq_one
    intro k _
    dsimp only [f]
    rw [toricFaceHomogeneous_basisCoordinate, dif_pos k.property, Int.toNat_zero, pow_zero]
  rw [hzero, one_mul] at hsplit
  rw [← hsplit]
  change (∏ k : {k : Fin n // k ∉ J}, f k.val) =
    ((latticeCharacter (originalPolytopeFullExponents (toricFaceProjectedFamily (hs := hs) v J) i) a : ℂˣ) : ℂ)
  simp only [latticeCharacter, MonoidHom.coe_mk, OneHom.coe_mk, Units.coe_prod, Units.val_zpow_eq_zpow_val]
  apply Fintype.prod_equiv (Fintype.equivFin {j : Fin n // j ∉ J})
  intro k
  dsimp only [f]
  rw [toricFaceHomogeneous_basisCoordinate, dif_neg k.property]
  change (if hk : k.val ∈ J then (0 : ℂ) else _) ^ _ = _
  rw [dif_neg k.property, ← zpow_natCast, Int.toNat_of_nonneg (toricFaceFullExponent_nonneg v J i _)]

/-- The ENTIRE original homogeneous boundary vector is literally the actual
zero extension of the target dense-orbit vector. This proves both original
face coordinates and ALL original off-face coordinates. -/
theorem nativeVector_toricFaceBoundary_eq_zeroExtension
    (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (a : Fin (toricFaceDimension J) → ℂˣ) :
    originalPolytopeNativeVector γ hs v (toricFaceBoundaryCoordinates J a) =
      toricFaceHomogeneousZeroExtension (hs := hs) v J
        (monomialOrbitVector (originalPolytopeFullExponents (toricFaceProjectedFamily (hs := hs) v J)) a) := by
  funext i
  by_cases hi : integerCast (originalPolytopeFullExponents γ i) ∈ toricNativeVertexFace (hs := hs) v J
  · let j := (toricFaceHomogeneousIndexEquiv (hs := hs) v J).symm ⟨i, hi⟩
    have heq : (toricFaceHomogeneousIndexEquiv (hs := hs) v J j).val = i :=
      congrArg Subtype.val ((toricFaceHomogeneousIndexEquiv (hs := hs) v J).apply_symm_apply ⟨i, hi⟩)
    have hread := nativeVector_toricFaceBoundary_face (hs := hs) v J a j
    have hzero := toricFaceHomogeneousZeroExtension_readback (hs := hs) v J
      (monomialOrbitVector (originalPolytopeFullExponents (toricFaceProjectedFamily (hs := hs) v J)) a) j
    rw [heq] at hread hzero
    exact hread.trans hzero.symm
  · rw [nativeVector_toricFaceBoundary_off_face v J a i hi,
      toricFaceHomogeneousZeroExtension_off_face v J _ i hi]

end SGPT.Toric
