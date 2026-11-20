import SGPT.Toric.OriginalPolytopeFacets

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set SGPT.AlmostSemigroup.Counting
open scoped BigOperators Topology
variable {n : ℕ} {K : Type*} [Fintype K]

/-- The literal first nonzero integral element on its positive real normal
ray. This is geometric primitivity, not merely nonvanishing. -/
def IsFirstIntegralNormal (u : (Fin n → ℤ) →ₗ[ℤ] ℤ) : Prop :=
  u ≠ 0 ∧ ∀ (q : (Fin n → ℤ) →ₗ[ℤ] ℤ) (t : ℝ), 0 < t →
    integralRealFunctional q = t • integralRealFunctional u → 1 ≤ t

omit [Fintype K] in
/-- Original integer evaluation gives genuine injectivity of real extension. -/
theorem integralRealFunctional_injective :
    Function.Injective (integralRealFunctional (n := n)) := by
  intro u v huv
  apply LinearMap.ext
  intro m
  have h := congrArg (fun f : (Fin n → ℝ) →L[ℝ] ℝ => f (integerCast m)) huv
  simp only [integralRealFunctional_integerCast] at h
  exact_mod_cast h

/-- The prior genuine first-integer-ray producer gives ACTUAL primitivity. -/
theorem originalVertexHalfspaceNormal_isFirstIntegral (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (ρ : originalVertexHalfspaceIndex γ) :
    IsFirstIntegralNormal (originalVertexHalfspaceNormal γ hsmooth ρ) := by
  refine ⟨originalVertexHalfspaceNormal_ne_zero γ hsmooth ρ, ?_⟩
  intro q t ht hscale
  obtain ⟨k, hk, htk, _⟩ :=
    originalVertexHalfspaceNormal_first_integer_ray γ hsmooth ρ q ht hscale
  rw [htk]
  exact_mod_cast hk

/-- Any actual inward integral normal cutting out the SAME produced face is
a strictly positive multiple of its original normal. All signs and the scale
come from genuine original basis neighbors and actual coordinate readback. -/
theorem originalVertexZeroFace_normal_scale (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (ρ : originalVertexHalfspaceIndex γ)
    (q : (Fin n → ℤ) →ₗ[ℤ] ℤ) (a : ℤ) (hq : q ≠ 0)
    (hinward : ∀ x ∈ latticePolytope γ, 0 ≤ integralRealFunctional q x + (a : ℝ))
    (hzero : {x ∈ latticePolytope γ | integralRealFunctional q x + (a : ℝ) = 0} =
      originalVertexZeroFace γ hsmooth ρ) :
    ∃ t : ℝ, 0 < t ∧
      integralRealFunctional q = t • integralRealFunctional (originalVertexHalfspaceNormal γ hsmooth ρ) ∧
      (a : ℝ) = t * (originalVertexHalfspaceOffset γ hsmooth ρ : ℝ) := by
  let B := originalVertexHalfspaceBasis γ hsmooth ρ.1
  let R := integralRealBasis B
  have hval (m : Fin n → ℤ) (hm : integerCast m ∈ originalVertexZeroFace γ hsmooth ρ) :
      q m + a = 0 := by
    have hx : integerCast m ∈
        {x ∈ latticePolytope γ | integralRealFunctional q x + (a : ℝ) = 0} := by
      rw [hzero]
      exact hm
    have h := hx.2
    rw [integralRealFunctional_integerCast] at h
    exact_mod_cast h
  have hv := hval ρ.1.val (originalVertexZeroFace_vertex_mem γ hsmooth ρ)
  have hother (k : Fin n) (hk : k ≠ ρ.2) : q (B k) = 0 := by
    have h := hval (ρ.1.val + B k) (originalVertexZeroFace_neighbor_mem γ hsmooth ρ hk)
    rw [map_add] at h
    omega
  have hnonneg : 0 ≤ q (B ρ.2) := by
    have h := hinward (integerCast (ρ.1.val + B ρ.2))
      ((originalVertexHalfspaceBasis_spec γ hsmooth ρ.1).2.2 ρ.2)
    rw [integralRealFunctional_integerCast, map_add, Int.cast_add] at h
    have hvcast : (q ρ.1.val : ℝ) + (a : ℝ) = 0 := by exact_mod_cast hv
    exact_mod_cast (by linarith : 0 ≤ (q (B ρ.2) : ℝ))
  have hne : q (B ρ.2) ≠ 0 := by
    intro hz
    apply hq
    apply B.ext
    intro k
    change q (B k) = 0
    by_cases hk : k = ρ.2
    · simpa only [hk] using hz
    · exact hother k hk
  let t : ℝ := q (B ρ.2)
  have ht : 0 < t := by
    dsimp only [t]
    exact_mod_cast (lt_of_le_of_ne hnonneg hne.symm)
  have hlin : (integralRealFunctional q).toLinearMap =
      (t • integralRealFunctional (originalVertexHalfspaceNormal γ hsmooth ρ)).toLinearMap := by
    apply R.ext
    intro k
    change integralRealFunctional q (integralRealBasis B k) =
      t * integralRealFunctional (originalVertexHalfspaceNormal γ hsmooth ρ) (integralRealBasis B k)
    rw [integralRealBasis_apply, integralRealFunctional_integerCast,
      integralRealFunctional_integerCast, originalVertexHalfspaceNormal_basis]
    by_cases hk : k = ρ.2
    · subst k
      simp [t, B]
    · simp [hk, hother k hk]
  have hscale : integralRealFunctional q =
      t • integralRealFunctional (originalVertexHalfspaceNormal γ hsmooth ρ) := by
    ext x
    exact congrArg (fun f : (Fin n → ℝ) →ₗ[ℝ] ℝ => f x) hlin
  refine ⟨t, ht, hscale, ?_⟩
  have hvreal : (q ρ.1.val : ℝ) + (a : ℝ) = 0 := by exact_mod_cast hv
  have href := (originalVertexZeroFace_vertex_mem γ hsmooth ρ).2
  change integralRealFunctional (originalVertexHalfspaceNormal γ hsmooth ρ)
    (integerCast ρ.1.val) + (originalVertexHalfspaceOffset γ hsmooth ρ : ℝ) = 0 at href
  have h := congrArg (fun f : (Fin n → ℝ) →L[ℝ] ℝ => f (integerCast ρ.1.val)) hscale
  simp only [integralRealFunctional_integerCast, smul_apply, smul_eq_mul] at h
  rw [integralRealFunctional_integerCast] at href
  nlinarith

/-- Actual FIRST-integral-point primitivity on both rays forces the positive
scale to be one; nonvanishing alone is never substituted for this property. -/
theorem originalVertexZeroFace_primitive_pair_unique (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (ρ : originalVertexHalfspaceIndex γ)
    (q : (Fin n → ℤ) →ₗ[ℤ] ℤ) (a : ℤ) (hq : IsFirstIntegralNormal q)
    (hinward : ∀ x ∈ latticePolytope γ, 0 ≤ integralRealFunctional q x + (a : ℝ))
    (hzero : {x ∈ latticePolytope γ | integralRealFunctional q x + (a : ℝ) = 0} =
      originalVertexZeroFace γ hsmooth ρ) :
    q = originalVertexHalfspaceNormal γ hsmooth ρ ∧
      a = originalVertexHalfspaceOffset γ hsmooth ρ := by
  obtain ⟨t, ht, hscale, ha⟩ := originalVertexZeroFace_normal_scale γ hsmooth ρ q a hq.1 hinward hzero
  have hge := (originalVertexHalfspaceNormal_isFirstIntegral γ hsmooth ρ).2 q t ht hscale
  have hreverse : integralRealFunctional (originalVertexHalfspaceNormal γ hsmooth ρ) =
      t⁻¹ • integralRealFunctional q := by
    rw [hscale, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
  have hgeinv := hq.2 (originalVertexHalfspaceNormal γ hsmooth ρ) t⁻¹ (inv_pos.mpr ht) hreverse
  have hle : t ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hgeinv ht.le
    simpa only [one_mul, inv_mul_cancel₀ ht.ne'] using h
  have htone := le_antisymm hle hge
  constructor
  · apply integralRealFunctional_injective
    simpa only [htone, one_smul] using hscale
  · have ha' : (a : ℝ) = (originalVertexHalfspaceOffset γ hsmooth ρ : ℝ) := by
      simpa only [htone, one_mul] using ha
    exact_mod_cast ha'

/-- Repeated actual zero facets have EXACTLY the same original primitive
integer normal AND offset, using their produced first-point properties. -/
theorem originalVertexHalfspace_pair_eq_of_zeroFace_eq (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) {ρ σ : originalVertexHalfspaceIndex γ}
    (h : originalVertexZeroFace γ hsmooth ρ = originalVertexZeroFace γ hsmooth σ) :
    originalVertexHalfspaceNormal γ hsmooth ρ = originalVertexHalfspaceNormal γ hsmooth σ ∧
      originalVertexHalfspaceOffset γ hsmooth ρ = originalVertexHalfspaceOffset γ hsmooth σ := by
  exact originalVertexZeroFace_primitive_pair_unique γ hsmooth σ
    (originalVertexHalfspaceNormal γ hsmooth ρ) (originalVertexHalfspaceOffset γ hsmooth ρ)
    (originalVertexHalfspaceNormal_isFirstIntegral γ hsmooth ρ)
    (fun _ hx => latticePolytope_subset_originalVertexHalfspaces γ hsmooth hx ρ) h

/-- A preimage is chosen from the PRODUCED exhaustion of ALL geometric facets. -/
def originalFacetRepresentative [Nonempty K] (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (F : latticePolytopeFacets γ) :
    originalVertexHalfspaceIndex γ :=
  (exists_originalVertexZeroFace_eq γ hsmooth F.property).choose

theorem originalFacetRepresentative_spec [Nonempty K] (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (F : latticePolytopeFacets γ) :
    F.val = originalVertexZeroFace γ hsmooth (originalFacetRepresentative γ hsmooth F) :=
  (exists_originalVertexZeroFace_eq γ hsmooth F.property).choose_spec

/-- The actual primitive normal indexed by ALL DISTINCT original facets. -/
def originalFacetNormal [Nonempty K] (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (F : latticePolytopeFacets γ) :
    (Fin n → ℤ) →ₗ[ℤ] ℤ :=
  originalVertexHalfspaceNormal γ hsmooth (originalFacetRepresentative γ hsmooth F)

/-- The actual integral offset indexed by the SAME geometric facets. -/
def originalFacetOffset [Nonempty K] (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (F : latticePolytopeFacets γ) : ℤ :=
  originalVertexHalfspaceOffset γ hsmooth (originalFacetRepresentative γ hsmooth F)

/-- Primitivity is internally produced for EVERY actual facet. -/
theorem originalFacetNormal_isFirstIntegral [Nonempty K] (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (F : latticePolytopeFacets γ) :
    IsFirstIntegralNormal (originalFacetNormal γ hsmooth F) :=
  originalVertexHalfspaceNormal_isFirstIntegral γ hsmooth _

/-- In particular these actual normals are nonzero. -/
theorem originalFacetNormal_ne_zero [Nonempty K] (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (F : latticePolytopeFacets γ) :
    originalFacetNormal γ hsmooth F ≠ 0 := (originalFacetNormal_isFirstIntegral γ hsmooth F).1

/-- The EXISTING affine facet value vanishes on EXACTLY the geometric facet. -/
theorem originalFacet_zeroSet_eq [Nonempty K] (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (F : latticePolytopeFacets γ) :
    {x ∈ latticePolytope γ | integralFacetValue (originalFacetNormal γ hsmooth)
      (originalFacetOffset γ hsmooth) F x = 0} = F.val :=
  (originalFacetRepresentative_spec γ hsmooth F).symm

/-- The actual selected primitive pair is independent of its raw preimage. -/
theorem originalFacet_pair_eq_of_raw [Nonempty K] (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (F : latticePolytopeFacets γ)
    (ρ : originalVertexHalfspaceIndex γ) (hF : F.val = originalVertexZeroFace γ hsmooth ρ) :
    originalFacetNormal γ hsmooth F = originalVertexHalfspaceNormal γ hsmooth ρ ∧
      originalFacetOffset γ hsmooth F = originalVertexHalfspaceOffset γ hsmooth ρ :=
  originalVertexHalfspace_pair_eq_of_zeroFace_eq γ hsmooth
    ((originalFacetRepresentative_spec γ hsmooth F).symm.trans hF)

/-- Original raw indices read back literally after geometric deduplication. -/
theorem originalFacet_pair_vertexFacet [Nonempty K] (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (ρ : originalVertexHalfspaceIndex γ) :
    originalFacetNormal γ hsmooth (originalVertexFacet γ hsmooth ρ) =
        originalVertexHalfspaceNormal γ hsmooth ρ ∧
      originalFacetOffset γ hsmooth (originalVertexFacet γ hsmooth ρ) =
        originalVertexHalfspaceOffset γ hsmooth ρ :=
  originalFacet_pair_eq_of_raw γ hsmooth _ ρ rfl

/-- Every source point satisfies EVERY true distinct original facet inequality. -/
theorem originalFacetValue_nonneg [Nonempty K] (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (F : latticePolytopeFacets γ)
    {x : Fin n → ℝ} (hx : x ∈ latticePolytope γ) :
    0 ≤ integralFacetValue (originalFacetNormal γ hsmooth) (originalFacetOffset γ hsmooth) F x :=
  latticePolytope_subset_originalVertexHalfspaces γ hsmooth hx (originalFacetRepresentative γ hsmooth F)

/-- The UNIQUE primitive pair for ANY proposed genuine inward first integral
normal on the actual geometric facet; no nonzero-only substitute is used. -/
theorem originalFacet_primitive_pair_unique [Nonempty K] (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (F : latticePolytopeFacets γ)
    (q : (Fin n → ℤ) →ₗ[ℤ] ℤ) (a : ℤ) (hq : IsFirstIntegralNormal q)
    (hinward : ∀ x ∈ latticePolytope γ, 0 ≤ integralRealFunctional q x + (a : ℝ))
    (hzero : {x ∈ latticePolytope γ | integralRealFunctional q x + (a : ℝ) = 0} = F.val) :
    q = originalFacetNormal γ hsmooth F ∧ a = originalFacetOffset γ hsmooth F :=
  originalVertexZeroFace_primitive_pair_unique γ hsmooth _ q a hq hinward
    (hzero.trans (originalFacetRepresentative_spec γ hsmooth F))

/-- ALL DISTINCT ACTUAL original facets give the literal exact source region.
Only original generators and book ALL-edge smoothness are final inputs. -/
theorem latticePolytope_eq_originalFacetRegion [Nonempty K]
    (γ : K → Fin n → ℤ) (hsmooth : latticePolytopeEdgeSmooth γ) :
    latticePolytope γ = integralFacetRegion (originalFacetNormal γ hsmooth)
      (originalFacetOffset γ hsmooth) := by
  apply Set.Subset.antisymm
  · intro x hx F
    exact originalFacetValue_nonneg γ hsmooth F hx
  · intro x hx
    rw [latticePolytope_eq_originalVertexHalfspaces γ hsmooth]
    intro ρ
    have h := hx (originalVertexFacet γ hsmooth ρ)
    have hpair := originalFacet_pair_vertexFacet γ hsmooth ρ
    change 0 ≤ integralFacetValue (originalFacetNormal γ hsmooth)
      (originalFacetOffset γ hsmooth) (originalVertexFacet γ hsmooth ρ) x at h
    simpa only [integralFacetValue, facetValue, hpair.1, hpair.2] using h

end SGPT.Toric
