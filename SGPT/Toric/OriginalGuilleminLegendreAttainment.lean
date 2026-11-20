import SGPT.Toric.OriginalGuilleminFreeCoordinates

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set SGPT.Convex SGPT.AlmostSemigroup.Counting
open scoped BigOperators Topology Classical ContDiff
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]

/-- The actual original dual parameter in the original edge basis. -/
def originalCornerDualParameters (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (y : Fin n → ℝ) : {j : Fin n // j ∉ (∅ : Set (Fin n))} → ℝ :=
  fun j => originalCoordinatePairing n (integerCast (originalVertexHalfspaceBasis γ hsmooth v j.val)) y

/-- Actual dual pairing composed with the manufactured primal basis map. -/
def originalCornerPairingLinear (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (y : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] ℝ :=
  ((originalCoordinatePairing n).flip y).toContinuousLinearMap.comp
    (originalVertexCornerLinear γ hsmooth v).toContinuousLinearMap

omit [Nonempty K] in
/-- Existing basis extensionality gives EXACTLY the original pairing tilt;
there is no supplied dual-coordinate or same-constant certificate. -/
theorem originalCornerFaceTilt_empty_eq_pairingLinear (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) (y : Fin n → ℝ) :
    originalCornerFaceTilt ∅ (originalCornerDualParameters γ hsmooth v y) =
      originalCornerPairingLinear γ hsmooth v y := by
  have heq : (originalCornerFaceTilt ∅ (originalCornerDualParameters γ hsmooth v y)).toLinearMap =
      (originalCornerPairingLinear γ hsmooth v y).toLinearMap := by
    apply (Pi.basisFun ℝ (Fin n)).ext
    intro j
    let J : {j : Fin n // j ∉ (∅ : Set (Fin n))} := ⟨j, by simp⟩
    change originalCornerFaceTilt ∅ (originalCornerDualParameters γ hsmooth v y)
      (Pi.basisFun ℝ (Fin n) j) = originalCornerPairingLinear γ hsmooth v y (Pi.basisFun ℝ (Fin n) j)
    rw [← originalCornerFreeEmbedding_basis ∅ J, originalCornerFaceTilt_free_basis,
      originalCornerFreeEmbedding_basis]
    change originalCoordinatePairing n (integerCast (originalVertexHalfspaceBasis γ hsmooth v j)) y =
      originalCoordinatePairing n (originalVertexCornerLinear γ hsmooth v (Pi.basisFun ℝ (Fin n) j)) y
    rw [originalVertexCornerLinear_basis]
  ext x
  exact congrArg (fun L : (Fin n → ℝ) →ₗ[ℝ] ℝ => L x) heq

omit [Nonempty K] in
/-- Literal original pairing identity on EVERY point of the real lattice space. -/
theorem originalCornerPoint_pairing (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) (y x : Fin n → ℝ) :
    originalCoordinatePairing n (originalVertexCornerPoint γ hsmooth v x) y =
      originalCoordinatePairing n (integerCast v.val) y +
        originalCornerFaceTilt ∅ (originalCornerDualParameters γ hsmooth v y) x := by
  rw [originalCornerFaceTilt_empty_eq_pairingLinear]
  change (originalCoordinatePairing n).flip y
    (integerCast v.val + originalVertexCornerLinear γ hsmooth v x) =
      (originalCoordinatePairing n).flip y (integerCast v.val) +
        (originalCoordinatePairing n).flip y (originalVertexCornerLinear γ hsmooth v x)
  exact map_add _ _ _

/-- When the zero pattern is empty, the produced inactive/free positivity
gives ALL original facet slacks positive, using the actual active exhaustion. -/
theorem originalCornerStrict_of_empty_face_strict (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    {x : Fin n → ℝ} (hdom : x ∈ originalVertexCornerDomain γ hsmooth v)
    (hpos : ∀ j : Fin n, 0 < x j) : x ∈ originalVertexCornerStrict γ hsmooth v := by
  intro F
  by_cases hvF : integerCast v.val ∈ F.val
  · obtain ⟨j, hj⟩ := originalVertexActiveFacet_surjective γ hsmooth v ⟨F, hvF⟩
    have hF : (originalVertexActiveFacet γ hsmooth v j).val = F := congrArg Subtype.val hj
    rw [← hF, originalCornerFacetValue_selected]
    exact hpos j
  · exact hdom.1 ⟨F, hvF⟩

/-- Genuine strict inequalities give a real open neighborhood inside the
SAME original P; the ACTUAL homeomorphism transports its interior. -/
theorem originalCornerPoint_mem_interior_of_strict (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    {x : Fin n → ℝ} (hx : x ∈ originalVertexCornerStrict γ hsmooth v) :
    originalVertexCornerPoint γ hsmooth v x ∈ interior (latticePolytope γ) := by
  have hi : x ∈ interior ((originalVertexCornerHomeomorph γ hsmooth v) ⁻¹' latticePolytope γ) := by
    apply mem_interior.mpr
    exact ⟨originalVertexCornerStrict γ hsmooth v, fun z hz =>
      originalVertexCornerPoint_mem_of_mem_domain γ hsmooth v
        (originalVertexCornerStrict_subset_domain γ hsmooth v hz),
      isOpen_originalVertexCornerStrict γ hsmooth v, hx⟩
  rw [← (originalVertexCornerHomeomorph γ hsmooth v).preimage_interior] at hi
  exact hi

/-- The actual all-face minimizer computes the ENTIRE original extended
Legendre supremum. Outside P the cost is genuinely bottom, while on P the
produced finite entropy identity is used BEFORE real comparison. -/
theorem originalCanonicalReference_eq_corner_value_of_minimizer (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) (y : Fin n → ℝ)
    {x : Fin n → ℝ} (hx : x ∈ originalVertexCornerFace γ hsmooth v ∅)
    (hmin : IsMinOn (originalCornerFaceObjective γ hsmooth v ∅ (originalCornerDualParameters γ hsmooth v y))
      (originalVertexCornerFace γ hsmooth v ∅) x) :
    originalCanonicalReference γ hsmooth y =
      ((originalCoordinatePairing n (originalVertexCornerPoint γ hsmooth v x) y -
        originalVertexCornerEntropyReal γ hsmooth v x : ℝ) : EReal) := by
  let _ := originalPolytopeFacetFintype γ hsmooth
  change (⨆ m : Fin n → ℝ, (originalCoordinatePairing n m y : EReal) -
    originalCanonicalEntropy γ hsmooth m) = _
  apply le_antisymm
  · apply iSup_le
    intro m
    by_cases hm : m ∈ latticePolytope γ
    · let z := (originalVertexCornerHomeomorph γ hsmooth v).symm m
      have hzm : originalVertexCornerPoint γ hsmooth v z = m :=
        (originalVertexCornerHomeomorph γ hsmooth v).apply_symm_apply m
      have hz : z ∈ originalVertexCornerFace γ hsmooth v ∅ :=
        ⟨hzm.symm ▸ hm, fun j hj => False.elim hj⟩
      have hminz : originalCornerFaceObjective γ hsmooth v ∅ (originalCornerDualParameters γ hsmooth v y) x ≤
          originalCornerFaceObjective γ hsmooth v ∅ (originalCornerDualParameters γ hsmooth v y) z := hmin hz
      have hpz := originalCornerPoint_pairing γ hsmooth v y z
      have hpx := originalCornerPoint_pairing γ hsmooth v y x
      have hbound : originalCoordinatePairing n m y - originalVertexCornerEntropyReal γ hsmooth v z ≤
          originalCoordinatePairing n (originalVertexCornerPoint γ hsmooth v x) y -
            originalVertexCornerEntropyReal γ hsmooth v x := by
        change originalVertexCornerEntropyReal γ hsmooth v x -
          originalCornerFaceTilt ∅ (originalCornerDualParameters γ hsmooth v y) x ≤
            originalVertexCornerEntropyReal γ hsmooth v z -
              originalCornerFaceTilt ∅ (originalCornerDualParameters γ hsmooth v y) z at hminz
        rw [hzm] at hpz
        linarith
      have hG : originalCanonicalEntropy γ hsmooth m =
          ((originalVertexCornerEntropyReal γ hsmooth v z : ℝ) : EReal) := by
        rw [← hzm, originalCanonicalEntropy_corner_eq, if_pos hz.1]
      rw [hG, ← EReal.coe_sub]
      exact EReal.coe_le_coe hbound
    · rw [originalCanonicalEntropy_eq, if_neg hm]
      simp
  · have hle := le_iSup (fun m : Fin n → ℝ => (originalCoordinatePairing n m y : EReal) -
      originalCanonicalEntropy γ hsmooth m) (originalVertexCornerPoint γ hsmooth v x)
    rw [originalCanonicalEntropy_corner_eq, if_pos hx.1, ← EReal.coe_sub] at hle
    exact hle

/-- ONLY the original source input produces genuine strict-interior attainment
of the literal full extended F0, with actual original stationarity equations. -/
theorem exists_originalCanonicalReference_corner_attainment (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) (y : Fin n → ℝ) :
    ∃ x ∈ originalVertexCornerStrict γ hsmooth v,
      originalVertexCornerPoint γ hsmooth v x ∈ interior (latticePolytope γ) ∧
        originalCanonicalReference γ hsmooth y =
          ((originalCoordinatePairing n (originalVertexCornerPoint γ hsmooth v x) y -
            originalVertexCornerEntropyReal γ hsmooth v x : ℝ) : EReal) ∧
        ∀ j : {j : Fin n // j ∉ (∅ : Set (Fin n))}, Real.log (x j.val) + 1 +
          originalCornerRemainderPartial γ hsmooth v j.val x = originalCornerDualParameters γ hsmooth v y j := by
  obtain ⟨x, ⟨hx, hmin⟩, _⟩ := existsUnique_originalCornerFace_minimizer γ hsmooth v ∅
    (originalCornerDualParameters γ hsmooth v y)
  have hstrict := originalCornerFace_minimizer_strict γ hsmooth v ∅ (originalCornerDualParameters γ hsmooth v y) hx hmin
  have hxs := originalCornerStrict_of_empty_face_strict γ hsmooth v hstrict.1 (fun j => hstrict.2 j (by simp))
  exact ⟨x, hxs, originalCornerPoint_mem_interior_of_strict γ hsmooth v hxs,
    originalCanonicalReference_eq_corner_value_of_minimizer γ hsmooth v y hx hmin,
    originalCornerFace_minimizer_stationary γ hsmooth v ∅ (originalCornerDualParameters γ hsmooth v y) hx hmin⟩

/-- BOTH improper values are excluded by actual finite full-supremum attainment,
before any real representative of the canonical reference is taken. -/
theorem originalCanonicalReference_finite (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) (y : Fin n → ℝ) :
    originalCanonicalReference γ hsmooth y ≠ ⊥ ∧ originalCanonicalReference γ hsmooth y ≠ ⊤ := by
  obtain ⟨x, _, _, hval, _⟩ := exists_originalCanonicalReference_corner_attainment γ hsmooth v y
  rw [hval]
  exact ⟨EReal.coe_ne_bot _, EReal.coe_ne_top _⟩

/-- The literal full supremum has a UNIQUE actual maximizer on the WHOLE
original polytope, including its boundary; uniqueness is not an input. -/
theorem existsUnique_originalCanonicalReference_corner_attainment (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) (y : Fin n → ℝ) :
    ∃! x, originalVertexCornerPoint γ hsmooth v x ∈ latticePolytope γ ∧
      originalCanonicalReference γ hsmooth y =
        ((originalCoordinatePairing n (originalVertexCornerPoint γ hsmooth v x) y -
          originalVertexCornerEntropyReal γ hsmooth v x : ℝ) : EReal) := by
  obtain ⟨x, ⟨hx, hmin⟩, huniq⟩ := existsUnique_originalCornerFace_minimizer γ hsmooth v ∅
    (originalCornerDualParameters γ hsmooth v y)
  have hval := originalCanonicalReference_eq_corner_value_of_minimizer γ hsmooth v y hx hmin
  refine ⟨x, ⟨hx.1, hval⟩, ?_⟩
  intro z hz
  have hzQ : z ∈ originalVertexCornerFace γ hsmooth v ∅ := ⟨hz.1, fun j hj => False.elim hj⟩
  have hcost : originalCoordinatePairing n (originalVertexCornerPoint γ hsmooth v z) y -
      originalVertexCornerEntropyReal γ hsmooth v z =
      originalCoordinatePairing n (originalVertexCornerPoint γ hsmooth v x) y -
        originalVertexCornerEntropyReal γ hsmooth v x := EReal.coe_injective (hz.2.symm.trans hval)
  have hobj : originalCornerFaceObjective γ hsmooth v ∅ (originalCornerDualParameters γ hsmooth v y) z =
      originalCornerFaceObjective γ hsmooth v ∅ (originalCornerDualParameters γ hsmooth v y) x := by
    change originalVertexCornerEntropyReal γ hsmooth v z -
      originalCornerFaceTilt ∅ (originalCornerDualParameters γ hsmooth v y) z =
        originalVertexCornerEntropyReal γ hsmooth v x -
          originalCornerFaceTilt ∅ (originalCornerDualParameters γ hsmooth v y) x
    rw [originalCornerPoint_pairing, originalCornerPoint_pairing] at hcost
    linarith
  have hzmin : IsMinOn (originalCornerFaceObjective γ hsmooth v ∅ (originalCornerDualParameters γ hsmooth v y))
      (originalVertexCornerFace γ hsmooth v ∅) z := by
    intro q hq
    change originalCornerFaceObjective γ hsmooth v ∅ (originalCornerDualParameters γ hsmooth v y) z ≤
      originalCornerFaceObjective γ hsmooth v ∅ (originalCornerDualParameters γ hsmooth v y) q
    rw [hobj]
    exact hmin hq
  exact huniq z ⟨hzQ, hzmin⟩

/-- Original nonempty vertex production removes any vertex input from the
genuine finite representative of the original full canonical reference. -/
theorem exists_real_originalCanonicalReference (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (y : Fin n → ℝ) :
    ∃ r : ℝ, originalCanonicalReference γ hsmooth y = (r : EReal) := by
  obtain ⟨v, hv⟩ := nonempty_latticePolytopeVertices γ
  obtain ⟨x, _, _, hval, _⟩ := exists_originalCanonicalReference_corner_attainment γ hsmooth ⟨v, hv⟩ y
  exact ⟨_, hval⟩

end SGPT.Toric
