import SGPT.Toric.ToricFaceNativeFreeCoordinates

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set SGPT.AlmostSemigroup.Counting
open scoped Topology BigOperators Classical
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- Literal differences of original face vertices project to their actual
target differences in the SAME integral Mσ coordinates. -/
theorem toricFaceCharacterCoordinates_vertex_sub
    (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (w w' : ToricNativeFaceVertex (hs := hs) v J) :
    toricFaceCharacterCoordinates (hs := hs) v J
      ⟨w'.val.val - w.val.val, toricNativeFace_sub_mem_annihilator v J w'.property w.property⟩ =
      (toricFaceVertexEquiv (hs := hs) v J w').val -
        (toricFaceVertexEquiv (hs := hs) v J w).val := by
  let m : toricStratumCharacterLattice (polytopeToricRay γ hs v '' J) :=
    ⟨w'.val.val - w.val.val, toricNativeFace_sub_mem_annihilator v J w'.property w.property⟩
  have h := toricFaceIntegralProjection_add_character v J w.val.val m
  have hsum : w.val.val + m.val = w'.val.val := by dsimp only [m]; abel
  rw [hsum] at h
  change (toricFaceVertexEquiv (hs := hs) v J w').val =
    (toricFaceVertexEquiv (hs := hs) v J w).val + toricFaceCharacterCoordinates v J m at h
  exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using h.symm)

/-- Genuine quotient-fan coherence: two presentations of the SAME target
primitive ray lift to the SAME original ray outside σ. Equal target normals
have the same actual ample-face supporting minimum. The original vertex–facet
incidence and native duality then prove equality of the original lifts. -/
theorem toricFaceNativeRay_lift_independent
    (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (w w' : ToricNativeFaceVertex (hs := hs) v J)
    (k k' : Fin (toricFaceDimension J))
    (hR : polytopeToricRayGenerator (toricFaceProjectedFamily (hs := hs) v J)
        (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J)
        (toricFaceVertexEquiv (hs := hs) v J w) k =
      polytopeToricRayGenerator (toricFaceProjectedFamily (hs := hs) v J)
        (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J)
        (toricFaceVertexEquiv (hs := hs) v J w') k') :
    polytopeToricRay γ hs w.val (toricFaceNativeFreeIndex v J w k) =
      polytopeToricRay γ hs w'.val (toricFaceNativeFreeIndex v J w' k') := by
  let γY := toricFaceProjectedFamily (hs := hs) v J
  let hY := latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J
  let wY := toricFaceVertexEquiv (hs := hs) v J w
  let wY' := toricFaceVertexEquiv (hs := hs) v J w'
  have hz : intPairing (wY'.val - wY.val) (polytopeToricRayGenerator γY hY wY k) = 0 := by
    have hnn := vertex_pairing_rayGenerator_nonneg γY hY wY wY' k
    have hnn' := vertex_pairing_rayGenerator_nonneg γY hY wY' wY k'
    change polytopeToricRayGenerator γY hY wY k = polytopeToricRayGenerator γY hY wY' k' at hR
    rw [← hR] at hnn'
    rw [intPairing_sub] at hnn hnn' ⊢
    omega
  let m : toricStratumCharacterLattice (polytopeToricRay γ hs v '' J) :=
    ⟨w'.val.val - w.val.val, toricNativeFace_sub_mem_annihilator v J w'.property w.property⟩
  have hp : intPairing (w'.val.val - w.val.val)
      (polytopeToricRayGenerator γ hs w.val (toricFaceNativeFreeIndex v J w k)) = 0 := by
    have h := toricFaceNativeRay_pairing v J w k m
    rw [toricFaceCharacterCoordinates_vertex_sub, hz] at h
    exact h.symm
  obtain ⟨l, hl⟩ := exists_rayGenerator_eq_of_pairing_eq_zero hp
  have hlR : polytopeToricRay γ hs w'.val l ∉ polytopeToricRay γ hs v '' J := by
    intro hmem
    have heq : polytopeToricRay γ hs w'.val l =
        polytopeToricRay γ hs w.val (toricFaceNativeFreeIndex v J w k) := Subtype.ext hl
    exact toricFaceNativeFreeIndex_ray_not_mem v J w k (heq ▸ hmem)
  let b : toricStratumCharacterLattice (polytopeToricRay γ hs v '' J) :=
    ⟨originalPolytopeNativeBasis γ hs w'.val l, toricFaceNativeFreePrimitive_annihilator v J w' l hlR⟩
  have h1 := toricFaceNativeRay_pairing v J w k b
  have h2 := toricFaceNativeRay_pairing v J w' k' b
  rw [← hR] at h2
  have heq := h1.symm.trans h2
  change intPairing (originalPolytopeNativeBasis γ hs w'.val l)
    (polytopeToricRayGenerator γ hs w.val (toricFaceNativeFreeIndex v J w k)) =
      intPairing (originalPolytopeNativeBasis γ hs w'.val l)
        (polytopeToricRayGenerator γ hs w'.val (toricFaceNativeFreeIndex v J w' k')) at heq
  rw [← hl, intPairing_basis_rayGenerator, if_pos rfl, intPairing_basis_rayGenerator] at heq
  have heql : l = toricFaceNativeFreeIndex v J w' k' := by
    split_ifs at heq with he
    · exact he
    · omega
  exact Subtype.ext (hl.symm.trans (congrArg (polytopeToricRayGenerator γ hs w'.val) heql))

/-- Every actual target fan ray has an actual original face-vertex/native
presentation; this is derived from the genuine FULL vertex correspondence. -/
theorem exists_toricFaceRay_native_presentation
    (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (ρ : PolytopeToricRays (toricFaceProjectedFamily (hs := hs) v J)
      (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J)) :
    ∃ w : ToricNativeFaceVertex (hs := hs) v J, ∃ k : Fin (toricFaceDimension J),
      polytopeToricRay (toricFaceProjectedFamily (hs := hs) v J)
        (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J)
        (toricFaceVertexEquiv (hs := hs) v J w) k = ρ := by
  obtain ⟨q, k, hk⟩ := ρ.property
  obtain ⟨w, rfl⟩ := (toricFaceVertexEquiv (hs := hs) v J).surjective q
  exact ⟨w, k, Subtype.ext hk⟩

/-- The ACTUAL original ray lift of an actual quotient-model ray. Native
presentation independence above makes this a genuine quotient-fan dictionary. -/
def toricFaceRayLift (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (ρ : PolytopeToricRays (toricFaceProjectedFamily (hs := hs) v J)
      (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J)) :
    PolytopeToricRays γ hs :=
  let h := exists_toricFaceRay_native_presentation (hs := hs) v J ρ
  polytopeToricRay γ hs h.choose.val (toricFaceNativeFreeIndex v J h.choose h.choose_spec.choose)

/-- The produced lift recovers EVERY actual original native presentation,
not only its internally selected presentation. -/
theorem toricFaceRayLift_native (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (w : ToricNativeFaceVertex (hs := hs) v J) (k : Fin (toricFaceDimension J)) :
    toricFaceRayLift (hs := hs) v J
      (polytopeToricRay (toricFaceProjectedFamily (hs := hs) v J)
        (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J)
        (toricFaceVertexEquiv (hs := hs) v J w) k) =
      polytopeToricRay γ hs w.val (toricFaceNativeFreeIndex v J w k) := by
  let ρ := polytopeToricRay (toricFaceProjectedFamily (hs := hs) v J)
    (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J)
    (toricFaceVertexEquiv (hs := hs) v J w) k
  let h := exists_toricFaceRay_native_presentation (hs := hs) v J ρ
  exact toricFaceNativeRay_lift_independent v J h.choose w h.choose_spec.choose k
    (congrArg Subtype.val h.choose_spec.choose_spec)

end SGPT.Toric
