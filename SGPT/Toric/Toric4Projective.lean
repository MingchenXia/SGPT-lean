import SGPT.Toric.Toric4Okounkov
import SGPT.Projective.Maps

/-!
# `X_{Δ_N} = ℙ^N`

Source `chapter_toric_ample.tex`, `ex:P1toric` and `chapter_toric_big.tex`, `ex:P2`,
`ex:OkounP2`: the toric manifold of the standard simplex is projective space, with the
torus `(t_1, …, t_N) ↦ [1 : t_1 : ⋯ : t_N]`, the torus-invariant prime divisors
`D_{e_k} = {X_k = 0}` and `D_{-(1,…,1)} = {X_0 = 0}`.

The model `X_P` is the closure of the monomial orbit in `ℙ(ℂ^{P ∩ M})`, with homogeneous
coordinates indexed by the (chosen) enumeration of `P ∩ M`.  For `P = Δ_N` we have
`P ∩ M = {0, e_1, …, e_N}` (`simplex_integerPoints`), the orbit closure is all of `ℙ(ℂ^{P∩M})`
(`simplex_mem_orbitClosure`), and reordering the coordinates as `[X_0 : X_{e_1} : ⋯ : X_{e_N}]`
gives

* `simplexProjectiveHomeomorph : X_{Δ_N} ≃ₜ ℙ^N` (S28's `ComplexProjectiveSpace N`);
* `simplexProjectiveHomeomorph_embedding`: the torus `a ↦ [1 : a_1 : ⋯ : a_N]`;
* `simplexProjectiveHomeomorph_image_single`, `…_image_neg`: `D_{e_k} ↦ {X_k = 0}`,
  `D_{-(1,…,1)} ↦ {X_0 = 0}`;
* `contMDiff_simplexProjectiveHomeomorph`, `contMDiff_simplexProjectiveHomeomorph_symm`: both
  directions are holomorphic, i.e. it is a biholomorphism.
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter Topology SGPT.AlmostSemigroup.Counting SGPT.Projective
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped BigOperators Manifold ContDiff
attribute [local instance] monomialProjectiveTopology

/-! ### Homogeneous coordinates of `X_P` -/

section General
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K] {γ : K → Fin n → ℤ}
  (hs : latticePolytopeEdgeSmooth γ)

/-- The point of `ℙ(ℂ^{P ∩ M})` of a point of `X_P`. -/
def polytopeToricProjectivePoint (p : PolytopeToricVariety γ hs) :
    Projectivization ℂ (Fin (originalPolytopeFullIndexSize γ + 1) → ℂ) :=
  (show originalPolytopeNativeSpace γ from p).val

/-- Homogeneous coordinates (a chosen representative) of a point of `X_P`. -/
def polytopeToricHomogeneous (p : PolytopeToricVariety γ hs) :
    Fin (originalPolytopeFullIndexSize γ + 1) → ℂ :=
  (polytopeToricProjectivePoint hs p).rep

theorem polytopeToricHomogeneous_ne_zero (p : PolytopeToricVariety γ hs) :
    polytopeToricHomogeneous hs p ≠ 0 :=
  Projectivization.rep_nonzero _

theorem polytopeToricProjectivePoint_eq_mk (p : PolytopeToricVariety γ hs) :
    polytopeToricProjectivePoint hs p =
      Projectivization.mk ℂ (polytopeToricHomogeneous hs p) (polytopeToricHomogeneous_ne_zero hs p) :=
  (Projectivization.mk_rep _).symm

/-- `p ∈ U_v ↔ X_v(p) ≠ 0`. -/
theorem mem_vertexChart_source_iff (v : latticePolytopeVertices γ) (p : PolytopeToricVariety γ hs) :
    p ∈ (originalPolytopeNativeModelChart γ hs v).source ↔
      polytopeToricHomogeneous hs p (originalPolytopeNativeVertexIndex γ v) ≠ 0 := by
  rw [originalPolytopeNativeModelChart_source]
  exact originalPolytopeNativePiChart_mem_source_iff γ hs v p _
    (polytopeToricHomogeneous_ne_zero hs p) (polytopeToricProjectivePoint_eq_mk hs p)

/-- The vertex chart reads `z_j = X_{v + b_j(v)} / X_v`. -/
theorem vertexChart_apply_eq_div (v : latticePolytopeVertices γ) {p : PolytopeToricVariety γ hs}
    (hp : p ∈ (originalPolytopeNativeModelChart γ hs v).source) (j : Fin n) :
    originalPolytopeNativeModelChart γ hs v p j =
      polytopeToricHomogeneous hs p (originalPolytopeNativeNeighborIndex γ hs v j) /
        polytopeToricHomogeneous hs p (originalPolytopeNativeVertexIndex γ v) := by
  rw [originalPolytopeNativeModelChart_source] at hp
  exact ((originalPolytopeNativePiChart_spec γ hs v).2.2.2.2.2 p hp _
    (polytopeToricHomogeneous_ne_zero hs p) (polytopeToricProjectivePoint_eq_mk hs p)).2 j

theorem vertexChart_apply_eq_zero_iff (v : latticePolytopeVertices γ)
    {p : PolytopeToricVariety γ hs} (hp : p ∈ (originalPolytopeNativeModelChart γ hs v).source)
    (j : Fin n) :
    originalPolytopeNativeModelChart γ hs v p j = 0 ↔
      polytopeToricHomogeneous hs p (originalPolytopeNativeNeighborIndex γ hs v j) = 0 := by
  rw [vertexChart_apply_eq_div hs v hp, div_eq_zero_iff,
    or_iff_left ((mem_vertexChart_source_iff hs v p).mp hp)]

theorem originalPolytopeFullExponents_injective :
    Function.Injective (originalPolytopeFullExponents γ) :=
  Subtype.val_injective.comp (originalPolytopeFullEnumeration γ).injective

end General

/-! ### The lattice points of `Δ_N` -/

section Simplex
variable {N : ℕ}

theorem simplexGenerator_injective : Function.Injective (simplexGenerator N) := by
  intro o o' h
  cases o with
  | none =>
    cases o' with
    | none => rfl
    | some i => have := congrFun h i; simp at this
  | some i =>
    cases o' with
    | none => have := congrFun h i; simp at this
    | some j =>
      have := congrFun h i
      by_cases hij : i = j
      · rw [hij]
      · simp [Ne.symm hij] at this

theorem simplexCoordMap_self (i : Fin N) (x : Fin N → ℤ) :
    simplexCoordMap i x i = -∑ m, x m := by
  simp [simplexCoordMap]

/-- `Δ_N ∩ ℤ^N = {0, e_1, …, e_N}`. -/
theorem simplex_integerPoints :
    latticePolytopeIntegerPoints (simplexGenerator N) = range (simplexGenerator N) := by
  ext m
  constructor
  · intro hm
    have hnn : ∀ k, 0 ≤ m k := by
      intro k
      have := (simplex_isVertexConeBasis none).coord_nonneg hm k
      rw [vertexConeCoord_integerCast] at this
      simpa [simplexBasis] using this
    have hsum : ∑ k, m k ≤ 1 := by
      rcases Nat.eq_zero_or_pos N with hN | hN
      · subst hN; simp
      · set i : Fin N := ⟨0, hN⟩
        have := (simplex_isVertexConeBasis (some i)).coord_nonneg hm i
        rw [vertexConeCoord_integerCast, simplexBasis_some_repr, simplexCoordMap_self] at this
        simp only [simplexGenerator_some, Pi.sub_apply, Finset.sum_sub_distrib,
          Finset.sum_pi_single', Finset.mem_univ, if_true] at this
        have h'' : (0 : ℤ) ≤ -(∑ k, m k - 1) := by exact_mod_cast this
        linarith
    by_cases h0 : ∀ k, m k = 0
    · exact ⟨none, by funext k; simp [h0 k]⟩
    · push Not at h0
      obtain ⟨k, hk⟩ := h0
      have hk1 : 1 ≤ m k := by have := hnn k; omega
      have hle : ∀ l, l ≠ k → m k + m l ≤ 1 := by
        intro l hl
        have hsub : ∑ x ∈ ({k, l} : Finset (Fin N)), m x ≤ ∑ x, m x :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun x _ _ => hnn x
        rw [Finset.sum_pair (Ne.symm hl)] at hsub
        linarith
      refine ⟨some k, ?_⟩
      funext l
      by_cases hl : l = k
      · subst hl
        have : m l ≤ 1 := le_trans (Finset.single_le_sum (fun x _ => hnn x)
          (Finset.mem_univ l)) hsum
        simp only [simplexGenerator_some, Pi.single_eq_same]; omega
      · have := hle l hl
        have := hnn l
        simp only [simplexGenerator_some, Pi.single_eq_of_ne hl]; omega
  · rintro ⟨o, rfl⟩
    exact latticePolytope_integer_generator_mem _ o

/-- Every generator other than `γ_o` is `γ_o + c_k` for the vertex-cone basis `c` at `γ_o`. -/
theorem simplex_generator_eq_vertex_add_basis (o o' : Option (Fin N)) (h : o' ≠ o) :
    ∃ k, simplexGenerator N o' = simplexGenerator N o + simplexBasis o k := by
  cases o with
  | none =>
    cases o' with
    | none => exact absurd rfl h
    | some k => exact ⟨k, by simp [simplexBasis]⟩
  | some i =>
    cases o' with
    | none => exact ⟨i, by rw [simplexBasis_some_apply, if_pos rfl]; simp⟩
    | some k =>
      have hki : k ≠ i := fun hki => h (by rw [hki])
      exact ⟨k, by rw [simplexBasis_some_apply, if_neg hki]; simp⟩

/-- The index of the homogeneous coordinate `X_{γ_o}` in the chosen enumeration of `Δ_N ∩ M`. -/
def simplexCoordIndex (o : Option (Fin N)) :
    Fin (originalPolytopeFullIndexSize (simplexGenerator N) + 1) :=
  (originalPolytopeFullEnumeration (simplexGenerator N)).symm
    ⟨simplexGenerator N o, latticePolytope_integer_generator_mem _ o⟩

theorem fullExponents_simplexCoordIndex (o : Option (Fin N)) :
    originalPolytopeFullExponents (simplexGenerator N) (simplexCoordIndex o) =
      simplexGenerator N o :=
  congrArg Subtype.val ((originalPolytopeFullEnumeration (simplexGenerator N)).apply_symm_apply _)

theorem eq_simplexCoordIndex_iff (i : Fin (originalPolytopeFullIndexSize (simplexGenerator N) + 1))
    (o : Option (Fin N)) :
    i = simplexCoordIndex o ↔
      originalPolytopeFullExponents (simplexGenerator N) i = simplexGenerator N o := by
  constructor
  · rintro rfl; exact fullExponents_simplexCoordIndex o
  · intro h
    apply originalPolytopeFullExponents_injective
    rw [h, fullExponents_simplexCoordIndex]

theorem simplexCoordIndex_bijective : Function.Bijective (simplexCoordIndex (N := N)) := by
  refine ⟨fun o o' h => simplexGenerator_injective ?_, fun i => ?_⟩
  · rw [← fullExponents_simplexCoordIndex o, ← fullExponents_simplexCoordIndex o', h]
  · have hi : ((originalPolytopeFullEnumeration (simplexGenerator N)) i).val ∈
        range (simplexGenerator N) := by
      rw [← simplex_integerPoints]; exact ((originalPolytopeFullEnumeration _) i).property
    obtain ⟨o, ho⟩ := hi
    exact ⟨o, ((eq_simplexCoordIndex_iff i o).mpr ho.symm).symm⟩

/-- The homogeneous coordinates `[X_0 : X_{e_1} : ⋯ : X_{e_N}]` of `ℙ^N` in the enumeration of
`Δ_N ∩ M`: `0 ↦ X_0`, `k + 1 ↦ X_{e_{k+1}}`. -/
def simplexHomogeneousIndex :
    Fin (N + 1) ≃ Fin (originalPolytopeFullIndexSize (simplexGenerator N) + 1) :=
  (finSuccEquiv N).trans (Equiv.ofBijective _ simplexCoordIndex_bijective)

theorem simplexHomogeneousIndex_zero : simplexHomogeneousIndex (N := N) 0 = simplexCoordIndex none := by
  simp [simplexHomogeneousIndex, finSuccEquiv_zero]

theorem simplexHomogeneousIndex_succ (k : Fin N) :
    simplexHomogeneousIndex k.succ = simplexCoordIndex (some k) := by
  simp [simplexHomogeneousIndex, finSuccEquiv_succ]

theorem simplexHomogeneousIndex_apply (i : Fin (N + 1)) :
    simplexHomogeneousIndex i = simplexCoordIndex (finSuccEquiv N i) := rfl

variable (hs : latticePolytopeEdgeSmooth (simplexGenerator N))

theorem simplex_vertexIndex (o : Option (Fin N)) :
    originalPolytopeNativeVertexIndex (simplexGenerator N) (simplexVertex o) = simplexCoordIndex o :=
  (eq_simplexCoordIndex_iff _ o).mpr (fullExponents_vertexIndex _)

/-- Every homogeneous index is the vertex index of `γ_o` or a neighbour index of `γ_o`. -/
theorem simplex_index_eq_vertex_or_neighbor (o : Option (Fin N))
    (i : Fin (originalPolytopeFullIndexSize (simplexGenerator N) + 1)) :
    i = originalPolytopeNativeVertexIndex (simplexGenerator N) (simplexVertex o) ∨
      ∃ j, i = originalPolytopeNativeNeighborIndex (simplexGenerator N) hs (simplexVertex o) j := by
  obtain ⟨o', rfl⟩ := simplexCoordIndex_bijective.2 i
  rw [simplex_vertexIndex]
  by_cases h : o' = o
  · left; rw [h]
  · right
    obtain ⟨k, hk⟩ := simplex_generator_eq_vertex_add_basis o o' h
    obtain ⟨τ, hτ⟩ := exists_perm_originalPolytopeNativeBasis_eq hs (simplexVertex o)
      (simplex_isVertexConeBasis o)
    refine ⟨τ.symm k, ?_⟩
    symm
    rw [eq_simplexCoordIndex_iff, fullExponents_neighborIndex, hτ, Equiv.apply_symm_apply, hk]
    rfl

/-! ### The orbit closure is all of `ℙ(ℂ^{Δ_N ∩ M})` -/

include hs in
/-- Every point of `ℙ(ℂ^{Δ_N ∩ M})` lies on `X_{Δ_N}`. -/
theorem simplex_mem_orbitClosure
    (q : Projectivization ℂ (Fin (originalPolytopeFullIndexSize (simplexGenerator N) + 1) → ℂ)) :
    q ∈ monomialProjectiveOrbitClosure (originalPolytopeFullExponents (simplexGenerator N)) := by
  induction q using Projectivization.ind with
  | h w hw =>
  obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
    by_contra h; push Not at h; exact hw (funext h)
  obtain ⟨o, rfl⟩ := simplexCoordIndex_bijective.2 i
  set v := simplexVertex (N := N) o
  set vi := originalPolytopeNativeVertexIndex (simplexGenerator N) v
  have hvi : vi = simplexCoordIndex o := simplex_vertexIndex o
  set z : Fin N → ℂ := fun j =>
    w (originalPolytopeNativeNeighborIndex (simplexGenerator N) hs v j) / w vi
  set p := (originalPolytopeNativePiChart (simplexGenerator N) hs v).symm z
  have hp := originalPolytopeNativePiChart_symm_val (simplexGenerator N) hs v z
  have hvec : originalPolytopeNativeVector (simplexGenerator N) hs v z = (w vi)⁻¹ • w := by
    have hwvi : w vi ≠ 0 := by rw [hvi]; exact hi
    funext l
    rcases simplex_index_eq_vertex_or_neighbor hs o l with hl | ⟨j, hl⟩
    · rw [hl]
      change monomialVertexVector _ _ _ z vi = _
      rw [monomialVertexVector_vertex, Pi.smul_apply, smul_eq_mul, inv_mul_cancel₀ hwvi]
    · rw [hl]
      change monomialVertexVector _ _ _ z _ = _
      have hν : ∀ j, originalPolytopeFullExponents (simplexGenerator N)
          (originalPolytopeNativeNeighborIndex _ hs v j) -
          originalPolytopeFullExponents (simplexGenerator N) vi =
            originalPolytopeNativeBasis _ hs v j := by
        intro j
        rw [fullExponents_vertexIndex]
        exact (originalPolytopeNativePiChart_spec _ hs v).1 j
      rw [monomialVertexVector_neighbor _ _ _ (originalPolytopeNativeNeighborIndex _ hs v) hν,
        Pi.smul_apply, smul_eq_mul]
      simp only [z]
      rw [div_eq_inv_mul]
  have hq : p.val = Projectivization.mk ℂ w hw := by
    rw [hp]
    apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
    exact ⟨(w vi)⁻¹, hvec.symm⟩
  rw [← hq]
  exact p.property

/-! ### The homeomorphism `X_{Δ_N} ≃ₜ ℙ^N` -/

/-- Reordering the homogeneous coordinates as `(X_0, X_{e_1}, …, X_{e_N})`. -/
def simplexCoordLinear :
    (Fin (originalPolytopeFullIndexSize (simplexGenerator N) + 1) → ℂ) ≃ₗ[ℂ] (Fin (N + 1) → ℂ) :=
  LinearEquiv.funCongrLeft ℂ ℂ simplexHomogeneousIndex

theorem simplexCoordLinear_apply (w : Fin (originalPolytopeFullIndexSize (simplexGenerator N) + 1) → ℂ)
    (i : Fin (N + 1)) : simplexCoordLinear w i = w (simplexHomogeneousIndex i) := rfl

/-- The induced map of projective spaces. -/
def simplexProjectiveMap :
    Projectivization ℂ (Fin (originalPolytopeFullIndexSize (simplexGenerator N) + 1) → ℂ) →
      ComplexProjectiveSpace N :=
  Projectivization.map (simplexCoordLinear (N := N)).toLinearMap simplexCoordLinear.injective

/-- The inverse map of projective spaces. -/
def simplexProjectiveMapInv : ComplexProjectiveSpace N →
    Projectivization ℂ (Fin (originalPolytopeFullIndexSize (simplexGenerator N) + 1) → ℂ) :=
  Projectivization.map (simplexCoordLinear (N := N)).symm.toLinearMap
    simplexCoordLinear.symm.injective

theorem continuous_projectivization_linearEquiv {I J : Type*} (A : (I → ℂ) ≃ₗ[ℂ] (J → ℂ))
    (hA : Continuous A) :
    Continuous (Projectivization.map A.toLinearMap A.injective :
      Projectivization ℂ (I → ℂ) → Projectivization ℂ (J → ℂ)) := by
  have hsub : Continuous (fun v : {v : I → ℂ // v ≠ 0} =>
      (⟨A v.val, by simpa only [map_zero] using A.injective.ne v.property⟩ :
        {v : J → ℂ // v ≠ 0})) := (hA.comp continuous_subtype_val).subtype_mk _
  apply continuous_coinduced_dom.mpr
  exact continuous_quotient_mk'.comp hsub

theorem continuous_simplexProjectiveMap : Continuous (simplexProjectiveMap (N := N)) :=
  continuous_projectivization_linearEquiv _
    (continuous_pi fun i => continuous_apply (simplexHomogeneousIndex i))

theorem continuous_simplexProjectiveMapInv : Continuous (simplexProjectiveMapInv (N := N)) :=
  continuous_projectivization_linearEquiv _
    (continuous_pi fun i => continuous_apply (simplexHomogeneousIndex.symm i))

theorem simplexProjectiveMapInv_map (q) :
    simplexProjectiveMapInv (simplexProjectiveMap (N := N) q) = q := by
  induction q using Projectivization.ind with
  | h w hw =>
    simp only [simplexProjectiveMap, simplexProjectiveMapInv, Projectivization.map_mk]
    congr 1
    simp

theorem simplexProjectiveMap_mapInv (q : ComplexProjectiveSpace N) :
    simplexProjectiveMap (simplexProjectiveMapInv q) = q := by
  induction q using Projectivization.ind with
  | h w hw =>
    simp only [simplexProjectiveMap, simplexProjectiveMapInv, Projectivization.map_mk]
    congr 1
    simp

/-- Source `ex:P1toric`, `ex:P2`: `X_{Δ_N} = ℙ^N`, with homogeneous coordinates
`[X_0 : X_{e_1} : ⋯ : X_{e_N}]`. -/
def simplexProjectiveHomeomorph : PolytopeToricVariety (simplexGenerator N) hs ≃ₜ
    ComplexProjectiveSpace N where
  toFun p := simplexProjectiveMap (polytopeToricProjectivePoint hs p)
  invFun q := show originalPolytopeNativeSpace (simplexGenerator N) from
    ⟨simplexProjectiveMapInv q, simplex_mem_orbitClosure hs _⟩
  left_inv p := by
    apply Subtype.ext
    exact simplexProjectiveMapInv_map _
  right_inv q := simplexProjectiveMap_mapInv q
  continuous_toFun := continuous_simplexProjectiveMap.comp continuous_subtype_val
  continuous_invFun := continuous_simplexProjectiveMapInv.subtype_mk _

theorem simplexProjectiveHomeomorph_apply (p : PolytopeToricVariety (simplexGenerator N) hs) :
    simplexProjectiveHomeomorph hs p =
      ComplexProjectiveSpace.mk (simplexCoordLinear (polytopeToricHomogeneous hs p))
        (by simpa using simplexCoordLinear.injective.ne (polytopeToricHomogeneous_ne_zero hs p)) := by
  change simplexProjectiveMap (polytopeToricProjectivePoint hs p) = _
  rw [polytopeToricProjectivePoint_eq_mk, simplexProjectiveMap, Projectivization.map_mk]
  rfl

/-- `X_i(Φ(p)) = 0` iff the corresponding homogeneous coordinate of `p` vanishes. -/
theorem simplexProjectiveHomeomorph_rep_eq_zero_iff (p : PolytopeToricVariety (simplexGenerator N) hs)
    (i : Fin (N + 1)) :
    (simplexProjectiveHomeomorph hs p).rep i = 0 ↔
      polytopeToricHomogeneous hs p (simplexHomogeneousIndex i) = 0 := by
  obtain ⟨c, hc, hrep⟩ := ComplexProjectiveSpace.rep_smul _ _ (simplexProjectiveHomeomorph_apply hs p)
  rw [hrep, Pi.smul_apply, smul_eq_mul, mul_eq_zero, or_iff_right hc, simplexCoordLinear_apply]

/-- Source `ex:P2`, `ex:P1toric`: the torus `T(ℂ) ⊆ X` is `(a_1, …, a_N) ↦ [1 : a_1 : ⋯ : a_N]`. -/
theorem simplexProjectiveHomeomorph_embedding (a : Fin N → ℂˣ) :
    simplexProjectiveHomeomorph hs (polytopeToricEmbedding (simplexGenerator N) hs a) =
      ComplexProjectiveSpace.mk (Fin.cons 1 fun i => (a i : ℂ))
        (fun h => one_ne_zero (congrFun h 0)) := by
  change simplexProjectiveMap (monomialProjectiveOrbit _ a) = _
  rw [monomialProjectiveOrbit, simplexProjectiveMap, Projectivization.map_mk]
  congr 1
  funext i
  refine Fin.cases ?_ (fun k => ?_) i
  · simp only [LinearEquiv.coe_coe, simplexCoordLinear_apply, simplexHomogeneousIndex_zero,
      monomialOrbitVector, fullExponents_simplexCoordIndex, simplexGenerator_none, Fin.cons_zero]
    simp [latticeCharacter]
  · simp only [LinearEquiv.coe_coe, simplexCoordLinear_apply, simplexHomogeneousIndex_succ,
      monomialOrbitVector, fullExponents_simplexCoordIndex, simplexGenerator_some, Fin.cons_succ]
    simp [latticeCharacter, Pi.single_apply]

/-! ### The divisors `D_ρ` in homogeneous coordinates -/

/-- At the vertex `γ_o`: if `u_j(γ_o) = e_k` then `γ_o + b_j(γ_o) = e_k`, and if
`u_j(γ_o) = -(1,…,1)` then `γ_o + b_j(γ_o) = 0`. -/
theorem simplex_vertex_add_basis_of_ray (o : Option (Fin N)) (j : Fin N) :
    (∀ k, polytopeToricRayGenerator _ hs (simplexVertex o) j = Pi.single k 1 →
      simplexGenerator N o + originalPolytopeNativeBasis _ hs (simplexVertex o) j =
        Pi.single k 1) ∧
    (polytopeToricRayGenerator _ hs (simplexVertex o) j = simplexNegRay N →
      simplexGenerator N o + originalPolytopeNativeBasis _ hs (simplexVertex o) j = 0) := by
  classical
  obtain ⟨τ, hτ⟩ := exists_perm_originalPolytopeNativeBasis_eq hs (simplexVertex o)
    (simplex_isVertexConeBasis o)
  have hr := polytopeToricRayGenerator_eq_vertexConeRay hs (simplexVertex o) hτ j
  rw [hr, hτ j]
  have hsingle : ∀ a b : Fin N, (Pi.single a 1 : Fin N → ℤ) = Pi.single b 1 → a = b := by
    intro a b h
    have := congrFun h a
    by_contra hab
    simp [hab] at this
  cases o with
  | none =>
    rw [simplex_vertexConeRay_none]
    refine ⟨fun k hk => ?_, fun h => absurd h (single_ne_simplexNegRay _)⟩
    rw [hsingle _ _ hk]
    simp [simplexBasis]
  | some i =>
    rw [simplex_vertexConeRay_some, simplexBasis_some_apply]
    by_cases hτi : τ j = i
    · rw [if_pos hτi, if_pos hτi]
      refine ⟨fun k hk => absurd hk.symm (single_ne_simplexNegRay k), fun _ => ?_⟩
      simp
    · rw [if_neg hτi, if_neg hτi]
      refine ⟨fun k hk => ?_, fun h => absurd h (single_ne_simplexNegRay _)⟩
      rw [hsingle _ _ hk]
      simp

theorem simplex_exists_ray_eq (o : Option (Fin N)) {u : Fin N → ℤ}
    (hu : u ∈ range (vertexConeRay (simplexBasis o))) :
    ∃ j, polytopeToricRayGenerator _ hs (simplexVertex o) j = u := by
  rw [← range_polytopeToricRayGenerator_eq hs (simplexVertex o) (simplex_isVertexConeBasis o)] at hu
  exact hu

theorem simplex_neighborIndex_eq (o : Option (Fin N)) (j : Fin N) (o' : Option (Fin N))
    (h : simplexGenerator N o + originalPolytopeNativeBasis _ hs (simplexVertex o) j =
      simplexGenerator N o') :
    originalPolytopeNativeNeighborIndex _ hs (simplexVertex o) j = simplexCoordIndex o' := by
  rw [eq_simplexCoordIndex_iff, fullExponents_neighborIndex]
  exact h

theorem exists_simplexCoordIndex_ne_zero (p : PolytopeToricVariety (simplexGenerator N) hs) :
    ∃ o, polytopeToricHomogeneous hs p (simplexCoordIndex o) ≠ 0 := by
  obtain ⟨i, hi⟩ : ∃ i, polytopeToricHomogeneous hs p i ≠ 0 := by
    by_contra h; push Not at h
    exact polytopeToricHomogeneous_ne_zero hs p (funext h)
  obtain ⟨o, rfl⟩ := simplexCoordIndex_bijective.2 i
  exact ⟨o, hi⟩

/-- Source `ex:P2`, `ex:P1toric`: `D_{e_k} = {X_{e_k} = 0}`. -/
theorem simplex_toricPrimeDivisor_single (k : Fin N)
    (hk : (Pi.single k 1 : Fin N → ℤ) ∈ PolytopeToricRays (simplexGenerator N) hs) :
    toricPrimeDivisor ⟨Pi.single k 1, hk⟩ =
      {p | polytopeToricHomogeneous hs p (simplexCoordIndex (some k)) = 0} := by
  ext p
  constructor
  · rintro ⟨v, j, hvj, hp, hz⟩
    obtain ⟨o, ho⟩ := exists_generator_eq_of_mem_vertices v
    have hv : v = simplexVertex o := Subtype.ext ho.symm
    subst hv
    rw [vertexChart_apply_eq_zero_iff hs _ hp,
      simplex_neighborIndex_eq hs o j (some k) ((simplex_vertex_add_basis_of_ray hs o j).1 k hvj)]
      at hz
    exact hz
  · intro hp
    obtain ⟨o', hi⟩ := exists_simplexCoordIndex_ne_zero hs p
    have ho' : o' ≠ some k := by rintro rfl; exact hi hp
    have hsrc : p ∈ (originalPolytopeNativeModelChart _ hs (simplexVertex o')).source := by
      rw [mem_vertexChart_source_iff, simplex_vertexIndex]; exact hi
    obtain ⟨j, hj⟩ : ∃ j, polytopeToricRayGenerator _ hs (simplexVertex o') j = Pi.single k 1 := by
      apply simplex_exists_ray_eq
      cases o' with
      | none => exact ⟨k, simplex_vertexConeRay_none k⟩
      | some i =>
        have hki : k ≠ i := fun h => ho' (by rw [h])
        exact ⟨k, by rw [simplex_vertexConeRay_some, if_neg hki]⟩
    refine ⟨simplexVertex o', j, hj, hsrc, ?_⟩
    rw [vertexChart_apply_eq_zero_iff hs _ hsrc,
      simplex_neighborIndex_eq hs o' j (some k) ((simplex_vertex_add_basis_of_ray hs o' j).1 k hj)]
    exact hp

/-- Source `ex:P2`, `ex:P1toric`: `D_{-(1,…,1)} = {X_0 = 0}`. -/
theorem simplex_toricPrimeDivisor_neg
    (h : simplexNegRay N ∈ PolytopeToricRays (simplexGenerator N) hs) :
    toricPrimeDivisor ⟨simplexNegRay N, h⟩ =
      {p | polytopeToricHomogeneous hs p (simplexCoordIndex none) = 0} := by
  ext p
  constructor
  · rintro ⟨v, j, hvj, hp, hz⟩
    obtain ⟨o, ho⟩ := exists_generator_eq_of_mem_vertices v
    have hv : v = simplexVertex o := Subtype.ext ho.symm
    subst hv
    rw [vertexChart_apply_eq_zero_iff hs _ hp,
      simplex_neighborIndex_eq hs o j none ((simplex_vertex_add_basis_of_ray hs o j).2 hvj)] at hz
    exact hz
  · intro hp
    obtain ⟨o', hi⟩ := exists_simplexCoordIndex_ne_zero hs p
    cases o' with
    | none => exact absurd hp hi
    | some i =>
      have hsrc : p ∈ (originalPolytopeNativeModelChart _ hs (simplexVertex (some i))).source := by
        rw [mem_vertexChart_source_iff, simplex_vertexIndex]; exact hi
      obtain ⟨j, hj⟩ : ∃ j, polytopeToricRayGenerator _ hs (simplexVertex (some i)) j =
          simplexNegRay N :=
        simplex_exists_ray_eq hs (some i) ⟨i, by rw [simplex_vertexConeRay_some, if_pos rfl]; rfl⟩
      refine ⟨simplexVertex (some i), j, hj, hsrc, ?_⟩
      rw [vertexChart_apply_eq_zero_iff hs _ hsrc,
        simplex_neighborIndex_eq hs (some i) j none ((simplex_vertex_add_basis_of_ray hs _ j).2 hj)]
      exact hp

/-- Source `ex:P2`, `ex:P1toric`: under `X_{Δ_N} ≅ ℙ^N`, `D_{e_k} = {X_k = 0}`. -/
theorem simplexProjectiveHomeomorph_image_single (k : Fin N)
    (hk : (Pi.single k 1 : Fin N → ℤ) ∈ PolytopeToricRays (simplexGenerator N) hs) :
    simplexProjectiveHomeomorph hs '' toricPrimeDivisor ⟨Pi.single k 1, hk⟩ =
      {q | q.rep k.succ = 0} := by
  rw [simplex_toricPrimeDivisor_single]
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    change _ = 0
    rw [simplexProjectiveHomeomorph_rep_eq_zero_iff, simplexHomogeneousIndex_succ]
    exact hp
  · intro hq
    refine ⟨(simplexProjectiveHomeomorph hs).symm q, ?_,
      (simplexProjectiveHomeomorph hs).apply_symm_apply q⟩
    have := (simplexProjectiveHomeomorph_rep_eq_zero_iff hs
      ((simplexProjectiveHomeomorph hs).symm q) k.succ).mp
      (by rw [(simplexProjectiveHomeomorph hs).apply_symm_apply]; exact hq)
    rwa [simplexHomogeneousIndex_succ] at this

/-- Source `ex:P2`, `ex:P1toric`: under `X_{Δ_N} ≅ ℙ^N`, `D_{-(1,…,1)} = {X_0 = 0}`. -/
theorem simplexProjectiveHomeomorph_image_neg
    (h : simplexNegRay N ∈ PolytopeToricRays (simplexGenerator N) hs) :
    simplexProjectiveHomeomorph hs '' toricPrimeDivisor ⟨simplexNegRay N, h⟩ =
      {q | q.rep 0 = 0} := by
  rw [simplex_toricPrimeDivisor_neg]
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    change _ = 0
    rw [simplexProjectiveHomeomorph_rep_eq_zero_iff, simplexHomogeneousIndex_zero]
    exact hp
  · intro hq
    refine ⟨(simplexProjectiveHomeomorph hs).symm q, ?_,
      (simplexProjectiveHomeomorph hs).apply_symm_apply q⟩
    have := (simplexProjectiveHomeomorph_rep_eq_zero_iff hs
      ((simplexProjectiveHomeomorph hs).symm q) 0).mp
      (by rw [(simplexProjectiveHomeomorph hs).apply_symm_apply]; exact hq)
    rwa [simplexHomogeneousIndex_zero] at this

/-! ### Holomorphy -/

theorem contDiff_simplexChartLift (v : latticePolytopeVertices (simplexGenerator N)) :
    ContDiff ℂ ∞ (fun z : ComplexModel N => simplexCoordLinear
      (originalPolytopeNativeVector _ hs v (originalPolytopeNativeModelEquiv N z))) := by
  have hvec : ContDiff ℂ ∞ (originalPolytopeNativeVector (simplexGenerator N) hs v) :=
    contDiff_pi.mpr fun i => contDiff_iff_contDiffAt.mpr fun z =>
      (analyticAt_originalPolytopeNativeVector_coord _ hs v i z).contDiffAt
  have hL : ContDiff ℂ ∞ (simplexCoordLinear (N := N)) :=
    (LinearMap.toContinuousLinearMap (simplexCoordLinear (N := N)).toLinearMap).contDiff
  exact hL.comp (hvec.comp (originalPolytopeNativeModelEquiv N).contDiff)

/-- The identification `X_{Δ_N} → ℙ^N` is holomorphic. -/
theorem contMDiff_simplexProjectiveHomeomorph :
    ContMDiff 𝓘(ℂ, ComplexModel N) 𝓘(ℂ, ComplexModel N) ∞ (simplexProjectiveHomeomorph hs) := by
  intro x
  obtain ⟨v, hv⟩ := originalPolytopeNativeModelChart_cover (simplexGenerator N) hs x
  set c : OpenPartialHomeomorph (PolytopeToricVariety (simplexGenerator N) hs) (ComplexModel N) :=
    originalPolytopeNativeModelChart (simplexGenerator N) hs v
  set G := fun z : ComplexModel N => simplexCoordLinear
    (originalPolytopeNativeVector _ hs v (originalPolytopeNativeModelEquiv N z))
  have hc : ContMDiffAt 𝓘(ℂ, ComplexModel N) 𝓘(ℂ, ComplexModel N) ∞ c x :=
    contMDiffAt_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := 𝓘(ℂ, ComplexModel N)) (n := ∞)
        (vertexChart_mem_atlas v)) hv
  have hF : ContMDiffAt 𝓘(ℂ, ComplexModel N) 𝓘(ℂ, Fin (N + 1) → ℂ) ∞ (fun y => G (c y)) x :=
    (contDiff_simplexChartLift hs v).contMDiff.contMDiffAt.comp x hc
  have hG0 : ∀ z, G z ≠ 0 := fun z h =>
    originalPolytopeNativeVector_ne_zero _ hs v (originalPolytopeNativeModelEquiv N z)
      (simplexCoordLinear.injective (h.trans (map_zero _).symm))
  refine ComplexProjectiveSpace.contMDiffAt_of_lift hF (hG0 _) ?_
  filter_upwards [c.open_source.mem_nhds hv] with y hy
  refine ⟨hG0 _, ?_⟩
  have hy' : y ∈ (originalPolytopeNativePiChart _ hs v).source := by
    rwa [originalPolytopeNativeModelChart_source] at hy
  have hval : polytopeToricProjectivePoint hs y =
      Projectivization.mk ℂ (originalPolytopeNativeVector _ hs v
        (originalPolytopeNativeModelEquiv N (c y)))
        (originalPolytopeNativeVector_ne_zero _ hs v _) := by
    have h1 := originalPolytopeNativePiChart_symm_val _ hs v
      (originalPolytopeNativePiChart _ hs v y)
    rw [(originalPolytopeNativePiChart _ hs v).left_inv hy'] at h1
    change (show originalPolytopeNativeSpace _ from y).val = _
    rw [h1]
    congr 2
  change simplexProjectiveMap (polytopeToricProjectivePoint hs y) = _
  rw [hval, simplexProjectiveMap, Projectivization.map_mk]
  rfl

/-- The identification `ℙ^N → X_{Δ_N}` is holomorphic. -/
theorem contMDiff_simplexProjectiveHomeomorph_symm :
    ContMDiff 𝓘(ℂ, ComplexModel N) 𝓘(ℂ, ComplexModel N) ∞ (simplexProjectiveHomeomorph hs).symm := by
  intro q
  set i := q.chartIndex
  have hq : q ∈ (ComplexProjectiveSpace.affineChart i).source :=
    ComplexProjectiveSpace.mem_affineChart_chartIndex q
  set o := finSuccEquiv N i
  set v := simplexVertex (N := N) o
  set σ := simplexHomogeneousIndex (N := N)
  have hσi : σ i = originalPolytopeNativeVertexIndex _ v := by
    rw [simplex_vertexIndex]; rfl
  have hne : ∀ j, σ.symm (originalPolytopeNativeNeighborIndex _ hs v j) ≠ i := by
    intro j h
    have h1 : originalPolytopeNativeNeighborIndex _ hs v j = originalPolytopeNativeVertexIndex _ v := by
      rw [← hσi, ← h, Equiv.apply_symm_apply]
    have h2 := congrArg (originalPolytopeFullExponents (simplexGenerator N)) h1
    rw [fullExponents_neighborIndex, fullExponents_vertexIndex] at h2
    exact (originalPolytopeNativeBasis _ hs v).ne_zero j (by simpa using h2)
  choose kj hkj using fun j => Fin.exists_succAbove_eq (hne j)
  set A : ComplexModel N → ComplexModel N :=
    fun z => (originalPolytopeNativeModelEquiv N).symm (fun j => z (kj j))
  have hA : ContDiff ℂ ∞ A := by
    have : ContDiff ℂ ∞ (fun z : ComplexModel N => (fun j => z (kj j) : Fin N → ℂ)) :=
      contDiff_pi.mpr fun j => (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) (kj j)).contDiff.comp
        (originalPolytopeNativeModelEquiv N).contDiff
    exact (originalPolytopeNativeModelEquiv N).symm.contDiff.comp this
  set c : OpenPartialHomeomorph (PolytopeToricVariety (simplexGenerator N) hs) (ComplexModel N) :=
    originalPolytopeNativeModelChart (simplexGenerator N) hs v
  have hcsymm : ContMDiffOn 𝓘(ℂ, ComplexModel N) 𝓘(ℂ, ComplexModel N) ∞ c.symm c.target :=
    contMDiffOn_symm_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := 𝓘(ℂ, ComplexModel N)) (n := ∞)
        (vertexChart_mem_atlas v))
  have hctarget : c.target = univ := originalPolytopeNativeModelChart_target _ hs v
  have hΨ : ContMDiffAt 𝓘(ℂ, ComplexModel N) 𝓘(ℂ, ComplexModel N) ∞
      (fun q' => c.symm (A (ComplexProjectiveSpace.affineChart i q'))) q := by
    have h1 : ContMDiffAt 𝓘(ℂ, ComplexModel N) 𝓘(ℂ, ComplexModel N) ∞ c.symm
        (A (ComplexProjectiveSpace.affineChart i q)) :=
      hcsymm.contMDiffAt (by rw [hctarget]; exact Filter.univ_mem)
    exact h1.comp q ((hA.contMDiff.contMDiffAt).comp q
      (ComplexProjectiveSpace.contMDiffAt_affineChart i hq))
  refine hΨ.congr_of_eventuallyEq ?_
  filter_upwards [(ComplexProjectiveSpace.affineChart i).open_source.mem_nhds hq] with q' hq'
  apply (simplexProjectiveHomeomorph hs).injective
  rw [Homeomorph.apply_symm_apply]
  symm
  have hq'i : q'.rep i ≠ 0 := (ComplexProjectiveSpace.mem_affineChart_source_iff i q').mp hq'
  set ζ := A (ComplexProjectiveSpace.affineChart i q')
  have hpt : polytopeToricProjectivePoint hs (c.symm ζ) =
      Projectivization.mk ℂ (originalPolytopeNativeVector _ hs v (originalPolytopeNativeModelEquiv N ζ))
        (originalPolytopeNativeVector_ne_zero _ hs v _) :=
    originalPolytopeNativePiChart_symm_val _ hs v _
  change simplexProjectiveMap (polytopeToricProjectivePoint hs (c.symm ζ)) = q'
  rw [hpt, simplexProjectiveMap, Projectivization.map_mk]
  conv_rhs => rw [← ComplexProjectiveSpace.mk_rep q']
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  refine ⟨(q'.rep i)⁻¹, ?_⟩
  funext l
  simp only [LinearEquiv.coe_coe, simplexCoordLinear_apply, Pi.smul_apply, smul_eq_mul]
  rcases simplex_index_eq_vertex_or_neighbor hs o (σ l) with hl | ⟨j, hl⟩
  · have hli : l = i := by
      apply σ.injective; rw [hl, hσi]
    rw [hl]
    change _ = monomialVertexVector _ _ _ _ _
    rw [monomialVertexVector_vertex, hli, inv_mul_cancel₀ hq'i]
  · rw [hl]
    have hν : ∀ j, originalPolytopeFullExponents (simplexGenerator N)
        (originalPolytopeNativeNeighborIndex _ hs v j) -
        originalPolytopeFullExponents (simplexGenerator N) (originalPolytopeNativeVertexIndex _ v) =
          originalPolytopeNativeBasis _ hs v j := by
      intro j
      rw [fullExponents_vertexIndex]
      exact (originalPolytopeNativePiChart_spec _ hs v).1 j
    change _ = monomialVertexVector _ _ _ _ _
    rw [monomialVertexVector_neighbor _ _ _ (originalPolytopeNativeNeighborIndex _ hs v) hν]
    have hlj : l = i.succAbove (kj j) := by
      rw [hkj j, ← hl, Equiv.symm_apply_apply]
    have haff : ComplexProjectiveSpace.affineChart i q' =
        ComplexProjectiveSpace.affineRatio i q'.rep := by
      conv_lhs => rw [← ComplexProjectiveSpace.mk_rep q']
      exact ComplexProjectiveSpace.affineChart_mk i _ hq'i
    simp only [ζ, A, ContinuousLinearEquiv.apply_symm_apply]
    rw [haff, ComplexProjectiveSpace.affineRatio_apply, hlj, div_eq_inv_mul]

end Simplex

end SGPT.Toric
