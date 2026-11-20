import SGPT.Toric.Toric4Delzant

/-!
# The standard simplex `Δ_N` as a Delzant polytope

Source `chapter_toric_ample.tex`, `ex:P1toric` (`N = 1`, `P = [0,1]`) and
`chapter_toric_big.tex`, `ex:P2` (`N = 2`).

`Δ_N = conv(0, e_1, …, e_N) ⊆ ℝ^N` (`simplexGenerator`).  At the vertex `0` the standard basis is
a vertex-cone basis; at the vertex `e_i` the basis `e_j - e_i` (`j ≠ i`), `-e_i` is
(`simplexBasis`); its coordinate map `x ↦ x - (x_i + ∑_m x_m) e_i` is an involution of `ℤ^N`.
Hence (by `latticePolytopeEdgeSmooth_of_vertexCones`)

* `simplex_edgeSmooth`: `Δ_N` is a Delzant lattice polytope, so `X_{Δ_N}` is defined;
* `simplex_vertices`: its vertices are `0, e_1, …, e_N`;
* `simplex_rays`: `Σ(1) = {e_1, …, e_N, -(1, …, 1)}`;
* `simplex_rayGenerator_zero`, `simplex_rayGenerator_single`: the rays of the maximal cones
  `σ_0 = cone(e_1, …, e_N)` and `σ_{e_i} = cone(e_j (j ≠ i), -(1,…,1))`;
* `simplexHyperplaneDivisor`, `simplexHyperplaneDivisor_eq_ample`: the divisor
  `D = D_{-(1,…,1)}` is the divisor `D_P` of the polytope;
* `toricDivisorPolytope_simplexHyperplaneDivisor`:
  `P_D = {m : m_k ≥ 0, ∑ m_k ≤ 1}`;
* `toricCartierDatum_simplexHyperplaneDivisor`: `m_{σ_v} = v`.
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set SGPT.AlmostSemigroup.Counting
open scoped BigOperators

variable {N : ℕ}

/-- The vertices `0, e_1, …, e_N` of the standard simplex `Δ_N`. -/
def simplexGenerator (N : ℕ) : Option (Fin N) → Fin N → ℤ
  | none => 0
  | some i => Pi.single i 1

@[simp] theorem simplexGenerator_none : simplexGenerator N none = 0 := rfl
@[simp] theorem simplexGenerator_some (i : Fin N) :
    simplexGenerator N (some i) = Pi.single i 1 := rfl

/-- The coordinate map at the vertex `e_i`: `x ↦ x - (x_i + ∑_m x_m) e_i`. -/
def simplexCoordMap (i : Fin N) (x : Fin N → ℤ) : Fin N → ℤ :=
  fun l => x l - if l = i then x i + ∑ m, x m else 0

theorem simplexCoordMap_involutive (i : Fin N) : Function.Involutive (simplexCoordMap i) := by
  intro x
  have hsum : ∑ m, simplexCoordMap i x m = -x i := by
    simp only [simplexCoordMap, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
    ring
  funext l
  by_cases hl : l = i
  · subst hl
    show simplexCoordMap l x l -
      (if l = l then simplexCoordMap l x l + ∑ m, simplexCoordMap l x m else 0) = x l
    rw [if_pos rfl, hsum]
    ring
  · show simplexCoordMap i x l - (if l = i then _ else 0) = x l
    rw [if_neg hl]
    simp [simplexCoordMap, hl]

/-- The coordinate map at `e_i` as a lattice automorphism. -/
def simplexCoordEquiv (i : Fin N) : (Fin N → ℤ) ≃ₗ[ℤ] (Fin N → ℤ) where
  toFun := simplexCoordMap i
  invFun := simplexCoordMap i
  map_add' x y := by
    funext l
    simp only [simplexCoordMap, Pi.add_apply, Finset.sum_add_distrib]
    split_ifs <;> ring
  map_smul' c x := by
    funext l
    simp only [simplexCoordMap, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← Finset.mul_sum]
    split_ifs <;> ring
  left_inv := simplexCoordMap_involutive i
  right_inv := simplexCoordMap_involutive i

theorem simplexCoordEquiv_apply (i : Fin N) (x : Fin N → ℤ) :
    simplexCoordEquiv i x = simplexCoordMap i x := rfl

/-- The vertex-cone bases of `Δ_N`: the standard basis at `0` and
`(e_j - e_i)_{j ≠ i}, -e_i` at `e_i`. -/
def simplexBasis : Option (Fin N) → Module.Basis (Fin N) ℤ (Fin N → ℤ)
  | none => Pi.basisFun ℤ (Fin N)
  | some i => Module.Basis.ofEquivFun (simplexCoordEquiv i)

theorem simplexCoordMap_single (i j : Fin N) :
    simplexCoordMap i (Pi.single j 1) =
      if j = i then -Pi.single i 1 else Pi.single j 1 - Pi.single i 1 := by
  funext l
  by_cases hji : j = i
  · subst hji
    by_cases hl : l = j
    · subst hl; simp [simplexCoordMap]
    · simp [simplexCoordMap, hl]
  · rw [if_neg hji]
    by_cases hl : l = i
    · subst hl; simp [simplexCoordMap, Ne.symm hji]
    · simp [simplexCoordMap, hl]

theorem simplexBasis_some_apply (i j : Fin N) :
    simplexBasis (some i) j = if j = i then -Pi.single i 1 else Pi.single j 1 - Pi.single i 1 := by
  classical
  simp only [simplexBasis, Module.Basis.coe_ofEquivFun]
  exact simplexCoordMap_single i j

theorem simplexBasis_some_repr (i : Fin N) (x : Fin N → ℤ) (k : Fin N) :
    (simplexBasis (some i)).repr x k = simplexCoordMap i x k := by
  simp only [simplexBasis, Module.Basis.ofEquivFun_repr_apply, simplexCoordEquiv_apply]

theorem simplex_generator_mem (o : Option (Fin N)) :
    integerCast (simplexGenerator N o) ∈ latticePolytope (simplexGenerator N) :=
  latticePolytope_generator_mem _ o

/-- The vertex-cone bases of `Δ_N`. -/
theorem simplex_isVertexConeBasis (o : Option (Fin N)) :
    IsVertexConeBasis (simplexGenerator N) (simplexGenerator N o) (simplexBasis o) := by
  classical
  cases o with
  | none =>
    refine ⟨simplex_generator_mem none, fun j => ?_, fun k j => ?_⟩
    · have : simplexGenerator N none + simplexBasis none j = simplexGenerator N (some j) := by
        simp [simplexBasis]
      rw [this]; exact simplex_generator_mem _
    · simp only [simplexBasis, Pi.basisFun_repr, simplexGenerator_none, sub_zero]
      cases k with
      | none => simp
      | some i => simp only [simplexGenerator_some]; by_cases h : j = i <;> simp [h]
  | some i =>
    refine ⟨simplex_generator_mem (some i), fun j => ?_, fun k j => ?_⟩
    · rw [simplexBasis_some_apply]
      by_cases hji : j = i
      · rw [if_pos hji]
        have : simplexGenerator N (some i) + -Pi.single i 1 = simplexGenerator N none := by simp
        rw [this]; exact simplex_generator_mem _
      · rw [if_neg hji]
        have : simplexGenerator N (some i) + (Pi.single j 1 - Pi.single i 1) =
            simplexGenerator N (some j) := by simp
        rw [this]; exact simplex_generator_mem _
    · rw [simplexBasis_some_repr]
      have hlin : simplexCoordMap i (simplexGenerator N k - simplexGenerator N (some i)) =
          simplexCoordMap i (simplexGenerator N k) - simplexCoordMap i (Pi.single i 1) :=
        (simplexCoordEquiv i).map_sub _ _
      rw [hlin, simplexCoordMap_single, if_pos rfl]
      cases k with
      | none =>
        have h0 : simplexCoordMap i (0 : Fin N → ℤ) = 0 := (simplexCoordEquiv i).map_zero
        simp only [simplexGenerator_none, h0]
        by_cases h : j = i <;> simp [h]
      | some l =>
        simp only [simplexGenerator_some, simplexCoordMap_single]
        by_cases hli : l = i
        · subst hli; simp
        · rw [if_neg hli]
          by_cases h : j = i
          · subst h; simp [hli]
          · by_cases h' : j = l <;> simp [Pi.single_apply, h, h']

/-- Source `ex:P1toric`, `ex:P2`: the standard simplex is a Delzant lattice polytope. -/
theorem simplex_edgeSmooth : latticePolytopeEdgeSmooth (simplexGenerator N) :=
  latticePolytopeEdgeSmooth_of_vertexCones simplexBasis simplex_isVertexConeBasis

/-- The vertices of `Δ_N` are `0, e_1, …, e_N`. -/
theorem simplex_vertices :
    latticePolytopeVertices (simplexGenerator N) = range (simplexGenerator N) := by
  ext m
  constructor
  · intro hm
    obtain ⟨k, hk⟩ := exists_generator_eq_of_mem_vertices (⟨m, hm⟩ : latticePolytopeVertices _)
    exact ⟨k, hk⟩
  · rintro ⟨k, rfl⟩
    exact (simplex_isVertexConeBasis k).mem_vertices

theorem simplex_vertexConeRay_none (k : Fin N) :
    vertexConeRay (simplexBasis none) k = Pi.single k 1 := by
  funext l
  simp only [vertexConeRay, simplexBasis, Pi.basisFun_repr]
  by_cases h : l = k
  · subst h; simp
  · simp [h, Ne.symm h]

theorem simplex_vertexConeRay_some (i k : Fin N) :
    vertexConeRay (simplexBasis (some i)) k = if k = i then (fun _ => -1) else Pi.single k 1 := by
  funext l
  simp only [vertexConeRay, simplexBasis_some_repr, simplexCoordMap_single]
  by_cases hk : k = i
  · subst hk
    by_cases hl : l = k <;> simp [hl]
  · rw [if_neg hk]
    by_cases hl : l = i
    · subst hl; simp [hk, Ne.symm hk]
    · by_cases hlk : l = k
      · subst hlk; simp [hl]
      · simp [hl, hlk, Ne.symm hlk, hk]

variable (hs : latticePolytopeEdgeSmooth (simplexGenerator N))

/-- Source `ex:P1toric`, `ex:P2`: `Σ(1) = {e_1, …, e_N, -(1, …, 1)}`. -/
theorem simplex_rays [NeZero N] :
    PolytopeToricRays (simplexGenerator N) hs =
      range (fun k : Fin N => (Pi.single k 1 : Fin N → ℤ)) ∪ {fun _ => -1} := by
  rw [polytopeToricRays_eq_of_vertexCones hs simplexBasis simplex_isVertexConeBasis]
  ext u
  simp only [mem_ofPred_eq, mem_union, mem_range, mem_singleton_iff]
  constructor
  · rintro ⟨k, j, rfl⟩
    cases k with
    | none => left; exact ⟨j, (simplex_vertexConeRay_none j).symm⟩
    | some i =>
      rw [simplex_vertexConeRay_some]
      split_ifs
      · right; rfl
      · left; exact ⟨j, rfl⟩
  · rintro (⟨j, rfl⟩ | rfl)
    · exact ⟨none, j, simplex_vertexConeRay_none j⟩
    · refine ⟨some 0, 0, ?_⟩
      rw [simplex_vertexConeRay_some, if_pos rfl]

/-- The vertex `γ_o` of `Δ_N` as an element of the vertex set. -/
def simplexVertex (o : Option (Fin N)) : latticePolytopeVertices (simplexGenerator N) :=
  ⟨simplexGenerator N o, (simplex_isVertexConeBasis o).mem_vertices⟩

/-- The rays of the maximal cone `σ_0`: up to the (chosen) order, `e_1, …, e_N`. -/
theorem simplex_rayGenerator_zero :
    range (polytopeToricRayGenerator (simplexGenerator N) hs (simplexVertex none)) =
      range (fun k : Fin N => (Pi.single k 1 : Fin N → ℤ)) := by
  rw [range_polytopeToricRayGenerator_eq hs (simplexVertex none) (simplex_isVertexConeBasis none)]
  congr 1
  funext k
  exact simplex_vertexConeRay_none k

/-- The rays of the maximal cone `σ_{e_i}`: `e_j` (`j ≠ i`) and `-(1, …, 1)`. -/
theorem simplex_rayGenerator_single (i : Fin N) :
    range (polytopeToricRayGenerator (simplexGenerator N) hs (simplexVertex (some i))) =
      (fun k : Fin N => if k = i then (fun _ => -1) else (Pi.single k 1 : Fin N → ℤ)) '' univ := by
  rw [range_polytopeToricRayGenerator_eq hs (simplexVertex (some i))
    (simplex_isVertexConeBasis (some i)), image_univ]
  congr 1
  funext k
  exact simplex_vertexConeRay_some i k

/-! ### The hyperplane divisor `D = D_{-(1,…,1)}` -/

/-- The all-`(-1)` ray `-(1, …, 1)`. -/
def simplexNegRay (N : ℕ) : Fin N → ℤ := fun _ => -1

/-- Source `ex:P2`, `ex:P1toric`: the divisor `D = D_{-(1,…,1)}`
(`a_{-(1,…,1)} = 1`, `a_{e_k} = 0`). -/
def simplexHyperplaneDivisor : ToricDivisor (simplexGenerator N) hs :=
  fun ρ => if ρ.val = simplexNegRay N then 1 else 0

theorem single_ne_simplexNegRay (k : Fin N) : (Pi.single k 1 : Fin N → ℤ) ≠ simplexNegRay N := by
  intro h
  have := congrFun h k
  simp [simplexNegRay] at this

theorem mem_simplex_rays [NeZero N] (ρ : PolytopeToricRays (simplexGenerator N) hs) :
    (∃ k, ρ.val = Pi.single k 1) ∨ ρ.val = simplexNegRay N := by
  have h : ρ.val ∈ range (fun k : Fin N => (Pi.single k 1 : Fin N → ℤ)) ∪ {fun _ => -1} := by
    rw [← simplex_rays hs]; exact ρ.property
  rcases h with ⟨k, hk⟩ | h
  · exact Or.inl ⟨k, hk.symm⟩
  · exact Or.inr h

/-- Source `ex:P2`: `P_D = {m : m_k ≥ 0, ∑_k m_k ≤ 1}`. -/
theorem toricDivisorPolytope_simplexHyperplaneDivisor [NeZero N] :
    toricDivisorPolytope (simplexHyperplaneDivisor hs) =
      {m : EuclideanSpace ℝ (Fin N) | (∀ k, 0 ≤ m k) ∧ ∑ k, m k ≤ 1} := by
  ext m
  simp only [toricDivisorPolytope, mem_ofPred_eq]
  constructor
  · intro h
    refine ⟨fun k => ?_, ?_⟩
    · have hk := h ⟨Pi.single k 1, by rw [simplex_rays]; exact Or.inl ⟨k, rfl⟩⟩
      simp only [simplexHyperplaneDivisor, single_ne_simplexNegRay, if_false, Int.cast_zero,
        neg_zero, latticeFunctional_apply] at hk
      simpa [Pi.single_apply] using hk
    · have hk := h ⟨simplexNegRay N, by rw [simplex_rays]; exact Or.inr rfl⟩
      simp only [simplexHyperplaneDivisor, if_true, Int.cast_one, latticeFunctional_apply,
        simplexNegRay] at hk
      simp only [Int.cast_neg, Int.cast_one, neg_one_mul, Finset.sum_neg_distrib] at hk
      linarith
  · rintro ⟨h0, h1⟩ ρ
    rcases mem_simplex_rays hs ρ with ⟨k, hk⟩ | hk
    · simp only [simplexHyperplaneDivisor, hk, single_ne_simplexNegRay, if_false, Int.cast_zero,
        neg_zero, latticeFunctional_apply]
      simpa [Pi.single_apply] using h0 k
    · simp only [simplexHyperplaneDivisor, hk, if_true, Int.cast_one, latticeFunctional_apply,
        simplexNegRay, Int.cast_neg, neg_one_mul, Finset.sum_neg_distrib]
      linarith

/-- Source `ex:P2`: the Cartier datum of `D` on the maximal cone `σ_v` is the vertex `v`
(`m_{σ_0} = 0`, `m_{σ_{e_i}} = e_i`). -/
theorem toricCartierDatum_simplexHyperplaneDivisor (o : Option (Fin N)) :
    toricCartierDatum (simplexHyperplaneDivisor hs) (simplexVertex o) = simplexGenerator N o := by
  classical
  apply toricCartierDatum_eq_of_vertexCone hs _ _ (simplex_isVertexConeBasis o)
  intro k
  cases o with
  | none =>
    simp only [simplexHyperplaneDivisor, simplex_vertexConeRay_none, single_ne_simplexNegRay,
      if_false, simplexGenerator_none]
    simp [intPairing]
  | some i =>
    simp only [simplexHyperplaneDivisor, simplex_vertexConeRay_some]
    by_cases hk : k = i
    · subst hk
      rw [if_pos rfl, if_pos (show (fun _ : Fin N => (-1 : ℤ)) = simplexNegRay N from rfl)]
      simp [intPairing]
    · simp only [if_neg hk, single_ne_simplexNegRay, if_false, simplexGenerator_some]
      simp [intPairing, Pi.single_apply, hk]

/-- Source `ex:P2` ("`L = O(D)` is ample"): `D` is the divisor `D_P` of the polytope, whose
line bundle carries the Guillemin metric with Kähler curvature `ω`. -/
theorem simplexHyperplaneDivisor_eq_ample :
    simplexHyperplaneDivisor hs = polytopeToricAmpleDivisor (simplexGenerator N) hs := by
  funext ρ
  obtain ⟨v, j, hvj⟩ := ρ.property
  obtain ⟨o, ho⟩ := exists_generator_eq_of_mem_vertices v
  have hv : v = simplexVertex o := Subtype.ext ho.symm
  subst hv
  have hρ : ρ = polytopeToricRay (simplexGenerator N) hs (simplexVertex o) j := Subtype.ext hvj.symm
  have h1 := toricCartierDatum_pairing (simplexHyperplaneDivisor hs) (simplexVertex o) j
  have h2 := toricCartierDatum_pairing (polytopeToricAmpleDivisor (simplexGenerator N) hs)
    (simplexVertex o) j
  rw [toricCartierDatum_simplexHyperplaneDivisor] at h1
  rw [toricCartierDatum_ampleDivisor] at h2
  rw [hρ]
  change intPairing (simplexGenerator N o) _ = _ at h1
  change intPairing (simplexGenerator N o) _ = _ at h2
  linarith

end SGPT.Toric
