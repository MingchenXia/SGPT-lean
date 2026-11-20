import SGPT.Toric.Toric4Projective

/-!
# The examples `ex:P1toric` and `ex:P2`

Source `chapter_toric_ample.tex`, `ex:P1toric` (`P = [0,1]`, `X = ℙ¹`) and
`chapter_toric_big.tex`, `ex:P2` (`P = Δ_2`, `X = ℙ²`).

* `isToricFanCone_iff_of_vertexCones`: for a polytope all of whose generators carry vertex-cone
  bases, the cones `τ ∈ Σ` are exactly the cones spanned by subsets of the dual bases;
* `P1toric_*`: the facet presentation of `[0,1]`, the fan `Σ = {(-∞,0], {0}, [0,∞)}`,
  `X_{[0,1]} ≅ ℙ¹` (biholomorphic), `D_{[0,∞)} = [0]`, `D_{(-∞,0]} = [∞]`, `D = [∞]`;
* `P2_*`: the fan of `ℙ²` (three rays, three maximal cones, the zero cone and nothing else),
  `D_{σ_i}` in homogeneous coordinates, `D = D_{σ_4}`, `P_D`, the Cartier data, the faces
  `Q_σ`, and `D = D_P` (the ample divisor of the polytope).
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set SGPT.AlmostSemigroup.Counting SGPT.Projective
open scoped BigOperators Manifold ContDiff

/-! ### Cones of `Σ` from vertex-cone bases -/

section Cones
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K] {γ : K → Fin n → ℤ}
  (hs : latticePolytopeEdgeSmooth γ)

/-- The cones `τ ∈ Σ` (recorded by their rays `τ(1)`) are the cones spanned by subsets of the
dual bases of the vertex-cone bases. -/
theorem isToricFanCone_iff_of_vertexCones (B : K → Module.Basis (Fin n) ℤ (Fin n → ℤ))
    (hB : ∀ k, IsVertexConeBasis γ (γ k) (B k)) (R : Set (PolytopeToricRays γ hs)) :
    IsToricFanCone R ↔
      ∃ (k : K) (S : Set (Fin n)), ∀ ρ, ρ ∈ R ↔ ∃ j ∈ S, vertexConeRay (B k) j = ρ.val := by
  constructor
  · rintro ⟨v, J, rfl⟩
    obtain ⟨k, hk⟩ := exists_generator_eq_of_mem_vertices v
    have h : IsVertexConeBasis γ v.val (B k) := hk ▸ hB k
    obtain ⟨τ, hτ⟩ := exists_perm_originalPolytopeNativeBasis_eq hs v h
    refine ⟨k, τ '' J, fun ρ => ?_⟩
    simp only [mem_image]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨τ j, ⟨j, hj, rfl⟩, (polytopeToricRayGenerator_eq_vertexConeRay hs v hτ j).symm⟩
    · rintro ⟨_, ⟨j, hj, rfl⟩, hρ⟩
      exact ⟨j, hj, Subtype.ext ((polytopeToricRayGenerator_eq_vertexConeRay hs v hτ j).trans hρ)⟩
  · rintro ⟨k, S, hS⟩
    set v : latticePolytopeVertices γ := ⟨γ k, (hB k).mem_vertices⟩
    obtain ⟨τ, hτ⟩ := exists_perm_originalPolytopeNativeBasis_eq hs v (hB k)
    refine ⟨v, τ ⁻¹' S, ?_⟩
    ext ρ
    rw [hS ρ]
    simp only [mem_image, mem_preimage]
    constructor
    · rintro ⟨j, hj, hρ⟩
      refine ⟨τ.symm j, by rwa [Equiv.apply_symm_apply], Subtype.ext ?_⟩
      change polytopeToricRayGenerator γ hs v (τ.symm j) = ρ.val
      rw [polytopeToricRayGenerator_eq_vertexConeRay hs v hτ, Equiv.apply_symm_apply, hρ]
    · rintro ⟨j, hj, rfl⟩
      exact ⟨τ j, hj, (polytopeToricRayGenerator_eq_vertexConeRay hs v hτ j).symm⟩

end Cones

theorem set_fin_one (S : Set (Fin 1)) : S = ∅ ∨ S = univ := by
  by_cases h : (0 : Fin 1) ∈ S
  · right; ext i; fin_cases i; simpa using h
  · left; ext i; fin_cases i; simpa using h

theorem set_fin_two (S : Set (Fin 2)) : S = ∅ ∨ S = {0} ∨ S = {1} ∨ S = univ := by
  by_cases h0 : (0 : Fin 2) ∈ S <;> by_cases h1 : (1 : Fin 2) ∈ S
  · right; right; right; ext i; fin_cases i <;> simpa
  · right; left; ext i; fin_cases i <;> simpa
  · right; right; left; ext i; fin_cases i <;> simpa
  · left; ext i; fin_cases i <;> simpa

theorem range_fin_two_eq {α : Type*} (f : Fin 2 → α) : range f = {f 0, f 1} := by
  ext a
  simp only [mem_range, mem_insert_iff, mem_singleton_iff, Fin.exists_fin_two]
  constructor
  · rintro (h | h)
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  · rintro (h | h)
    · exact Or.inl h.symm
    · exact Or.inr h.symm

/-- The point `[e_i] ∈ ℙ^N` is cut out by the vanishing of the other coordinates. -/
theorem ComplexProjectiveSpace.eq_mk_single_iff {N : ℕ} (i : Fin (N + 1))
    (q : ComplexProjectiveSpace N) :
    (∀ j, j ≠ i → q.rep j = 0) ↔
      q = ComplexProjectiveSpace.mk (Pi.single i (1 : ℂ)) (fun h => by simpa using congrFun h i) := by
  constructor
  · intro h
    have hi : q.rep i ≠ 0 := by
      intro h0
      apply q.rep_ne_zero
      funext j
      by_cases hj : j = i
      · rw [hj, h0]; rfl
      · exact h j hj
    conv_lhs => rw [← ComplexProjectiveSpace.mk_rep q]
    apply (ComplexProjectiveSpace.mk_eq_mk_iff _ _).mpr
    refine ⟨q.rep i, ?_⟩
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj, h j hj]
  · rintro rfl j hj
    obtain ⟨c, -, hc⟩ := ComplexProjectiveSpace.rep_smul _ _ rfl
    rw [hc]
    simp [hj]

/-- In dimension two the toric flag is `Y_1 = D_{ρ_1}` and `Y_2 = V(cone(ρ_1, ρ_2))`. -/
theorem toricFlag_two {K : Type*} [Fintype K] [Nonempty K] {γ : K → Fin 2 → ℤ}
    (hs : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) (e : Fin 2 ≃ Fin 2) :
    toricFlag hs v e 1 = toricPrimeDivisor (polytopeToricRay γ hs v (e 0)) ∧
    toricFlag hs v e 2 =
      toricOrbitClosure {polytopeToricRay γ hs v (e 0), polytopeToricRay γ hs v (e 1)} := by
  constructor
  · ext p
    simp only [toricFlag, toricOrbitClosure, toricFlagRays, mem_iInter, mem_image, mem_ofPred_eq]
    constructor
    · intro hp
      exact hp _ ⟨0, by simp, rfl⟩
    · rintro hp ρ ⟨l, hl, rfl⟩
      have hl0 : l = 0 := by ext; simp at hl ⊢; omega
      subst hl0
      exact hp
  · ext p
    simp only [toricFlag, toricOrbitClosure, toricFlagRays, mem_iInter, mem_image, mem_ofPred_eq,
      mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro hp ρ (rfl | rfl)
      · exact hp _ ⟨0, by simp, rfl⟩
      · exact hp _ ⟨1, by simp, rfl⟩
    · rintro hp ρ ⟨l, -, rfl⟩
      fin_cases l
      · exact hp _ (Or.inl rfl)
      · exact hp _ (Or.inr rfl)

/-! ### Sections of `O(D)` on `X_{Δ_N}` -/

section SimplexSections
variable {N : ℕ}

/-- The lattice points with `m_k ≥ 0` and `∑ m_k ≤ 1` are `0, e_1, …, e_N`. -/
theorem mem_range_simplexGenerator_iff (m : Fin N → ℤ) :
    m ∈ range (simplexGenerator N) ↔ (∀ k, 0 ≤ m k) ∧ ∑ k, m k ≤ 1 := by
  constructor
  · rintro ⟨o, rfl⟩
    cases o with
    | none => simp
    | some i =>
      refine ⟨fun k => ?_, ?_⟩
      · by_cases h : k = i
        · subst h; simp
        · simp [h]
      · simp
  · rintro ⟨hnn, hsum⟩
    by_cases h0 : ∀ k, m k = 0
    · exact ⟨none, by funext k; simp [h0 k]⟩
    · push Not at h0
      obtain ⟨k, hk⟩ := h0
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
        have := hnn l
        simp only [simplexGenerator_some, Pi.single_eq_same]; omega
      · have := hle l hl
        have := hnn l
        have := hnn k
        simp only [simplexGenerator_some, Pi.single_eq_of_ne hl]; omega

variable (hs : latticePolytopeEdgeSmooth (simplexGenerator N))

/-- `M ∩ P_D = {0, e_1, …, e_N}` for `D = D_{-(1,…,1)}`. -/
theorem simplex_toricLatticePoints [NeZero N] :
    toricLatticePoints (simplexHyperplaneDivisor hs) = range (simplexGenerator N) := by
  ext m
  rw [mem_range_simplexGenerator_iff]
  change latticeVector m ∈ toricDivisorPolytope (simplexHyperplaneDivisor hs) ↔ _
  rw [toricDivisorPolytope_simplexHyperplaneDivisor]
  simp only [mem_ofPred_eq, latticeVector_apply]
  constructor
  · rintro ⟨h0, h1⟩
    exact ⟨fun k => by exact_mod_cast h0 k, by exact_mod_cast h1⟩
  · rintro ⟨h0, h1⟩
    exact ⟨fun k => by exact_mod_cast h0 k, by exact_mod_cast h1⟩

/-- `H⁰(X, O(D)) = span{χ^0, χ^{e_1}, …, χ^{e_N}}` has dimension `N + 1`, and
`χ^{e_k}(a) = a_k = X_k / X_0` at the point `[1 : a_1 : ⋯ : a_N]` of the torus: the sections of
`O(D) = O(\{X_0 = 0\})` are the linear forms `X_0, …, X_N` divided by `X_0`. -/
theorem simplex_sections [NeZero N] :
    Module.finrank ℂ (toricSections (simplexHyperplaneDivisor hs)) = N + 1 ∧
    toricSections (simplexHyperplaneDivisor hs) = Submodule.span ℂ
      (range fun o : Option (Fin N) => fun a => (latticeCharacter (simplexGenerator N o) a : ℂ)) ∧
    ∀ (k : Fin N) (a : Fin N → ℂˣ),
      (latticeCharacter (simplexGenerator N (some k)) a : ℂ) = a k := by
  refine ⟨?_, ?_, fun k a => ?_⟩
  · rw [finrank_toricSections, simplex_toricLatticePoints, ← image_univ,
      Set.ncard_image_of_injective _ simplexGenerator_injective, ncard_univ]
    simp
  · rw [toricSections_eq_span]
    congr 1
    ext g
    simp only [mem_range]
    constructor
    · rintro ⟨⟨m, hm⟩, rfl⟩
      rw [simplex_toricLatticePoints] at hm
      obtain ⟨o, rfl⟩ := hm
      exact ⟨o, rfl⟩
    · rintro ⟨o, rfl⟩
      exact ⟨⟨simplexGenerator N o, by rw [simplex_toricLatticePoints]; exact ⟨o, rfl⟩⟩, rfl⟩
  · simp [latticeCharacter, Pi.single_apply]

end SimplexSections

/-! ### `ex:P1toric` -/

section P1
variable (hs : latticePolytopeEdgeSmooth (simplexGenerator 1))

/-- Source `ex:P1toric`: `P = conv(0, 1) = [0, 1]`. -/
theorem P1toric_polytope :
    toricDivisorPolytope (simplexHyperplaneDivisor hs) = {m | 0 ≤ m 0 ∧ m 0 ≤ 1} := by
  rw [toricDivisorPolytope_simplexHyperplaneDivisor (N := 1) hs]
  ext m
  simp [Fin.forall_fin_one]

/-- Source `ex:P1toric`: the facet presentation `P = {⟨m, 1⟩ ≥ 0, ⟨m, -1⟩ ≥ -1}`:
`Σ(1) = {1, -1}` (`u_{\{0\}} = 1`, `u_{\{1\}} = -1`), with `a_{\{0\}} = 0`, `a_{\{1\}} = 1`, and
`D = D_P`. -/
theorem P1toric_facets :
    PolytopeToricRays (simplexGenerator 1) hs = {Pi.single 0 1, simplexNegRay 1} ∧
    simplexHyperplaneDivisor hs = polytopeToricAmpleDivisor (simplexGenerator 1) hs ∧
    toricDivisorPolytope (polytopeToricAmpleDivisor (simplexGenerator 1) hs) =
      polytopeToricMomentPolytope (simplexGenerator 1) := by
  refine ⟨?_, simplexHyperplaneDivisor_eq_ample hs, toricDivisorPolytope_ampleDivisor _ hs⟩
  rw [simplex_rays]
  ext u
  simp only [mem_union, mem_range, mem_singleton_iff, mem_insert_iff, Fin.exists_fin_one]
  constructor
  · rintro (h | h)
    · exact Or.inl h.symm
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl h.symm
    · exact Or.inr h

/-- Source `ex:P1toric`: the normal fan is `Σ = {(-∞, 0], {0}, [0, ∞)}`: the cones are the zero
cone, the ray `[0, ∞)` of `1` and the ray `(-∞, 0]` of `-1`. -/
theorem P1toric_fan (R : Set (PolytopeToricRays (simplexGenerator 1) hs)) :
    IsToricFanCone R ↔ R = ∅ ∨ (∀ ρ, ρ ∈ R ↔ ρ.val = Pi.single 0 1) ∨
      (∀ ρ, ρ ∈ R ↔ ρ.val = simplexNegRay 1) := by
  rw [isToricFanCone_iff_of_vertexCones hs simplexBasis simplex_isVertexConeBasis]
  have hr0 := simplex_vertexConeRay_none (N := 1) 0
  have hr1 : vertexConeRay (simplexBasis (some (0 : Fin 1))) 0 = simplexNegRay 1 := by
    rw [simplex_vertexConeRay_some, if_pos rfl]; rfl
  constructor
  · rintro ⟨k, S, hS⟩
    rcases set_fin_one S with rfl | rfl
    · left; ext ρ; simp [hS ρ]
    · right
      cases k with
      | none => left; intro ρ; rw [hS ρ]; simp [Fin.exists_fin_one, hr0, eq_comm]
      | some i =>
        right; intro ρ; rw [hS ρ]
        have : i = 0 := Subsingleton.elim _ _
        subst this
        simp [Fin.exists_fin_one, hr1, eq_comm]
  · rintro (rfl | h | h)
    · exact ⟨none, ∅, fun ρ => by simp⟩
    · exact ⟨none, univ, fun ρ => by rw [h ρ]; simp [Fin.exists_fin_one, hr0, eq_comm]⟩
    · exact ⟨some 0, univ, fun ρ => by rw [h ρ]; simp [Fin.exists_fin_one, hr1, eq_comm]⟩

/-- Source `ex:P1toric`: `X = ℙ¹` (biholomorphically), with torus `t ↦ [1 : t]`,
`D_{[0,∞)} = [0] = [1 : 0]` and `D_{(-∞,0]} = [∞] = [0 : 1]`; hence `D = D_{(-∞,0]} = [∞]`. -/
theorem P1toric_projectiveLine
    (h0 : (Pi.single 0 1 : Fin 1 → ℤ) ∈ PolytopeToricRays (simplexGenerator 1) hs)
    (h1 : simplexNegRay 1 ∈ PolytopeToricRays (simplexGenerator 1) hs) :
    (ContMDiff 𝓘(ℂ, SGPT.Foundations.Analysis.FirstPass.ComplexModel 1)
        𝓘(ℂ, SGPT.Foundations.Analysis.FirstPass.ComplexModel 1) ∞ (simplexProjectiveHomeomorph hs) ∧
      ContMDiff 𝓘(ℂ, SGPT.Foundations.Analysis.FirstPass.ComplexModel 1)
        𝓘(ℂ, SGPT.Foundations.Analysis.FirstPass.ComplexModel 1) ∞
        (simplexProjectiveHomeomorph hs).symm) ∧
    (∀ a : Fin 1 → ℂˣ, simplexProjectiveHomeomorph hs (polytopeToricEmbedding _ hs a) =
      ComplexProjectiveSpace.mk ![1, (a 0 : ℂ)] (fun h => one_ne_zero (congrFun h 0))) ∧
    simplexProjectiveHomeomorph hs '' toricPrimeDivisor ⟨Pi.single 0 1, h0⟩ =
      {ComplexProjectiveSpace.mk ![1, 0] (fun h => one_ne_zero (congrFun h 0))} ∧
    simplexProjectiveHomeomorph hs '' toricPrimeDivisor ⟨simplexNegRay 1, h1⟩ =
      {ComplexProjectiveSpace.mk ![0, 1] (fun h => one_ne_zero (congrFun h 1))} := by
  refine ⟨⟨contMDiff_simplexProjectiveHomeomorph hs,
    contMDiff_simplexProjectiveHomeomorph_symm hs⟩, fun a => ?_, ?_, ?_⟩
  · rw [simplexProjectiveHomeomorph_embedding]
    congr 1
    funext i; fin_cases i <;> rfl
  · rw [simplexProjectiveHomeomorph_image_single]
    ext q
    have := ComplexProjectiveSpace.eq_mk_single_iff (N := 1) 0 q
    have hs1 : (Pi.single (0 : Fin 2) (1 : ℂ)) = ![1, 0] := by
      funext i; fin_cases i <;> rfl
    simp only [hs1, ne_eq] at this
    simp only [mem_ofPred_eq, mem_singleton_iff, ← this]
    simp
  · rw [simplexProjectiveHomeomorph_image_neg]
    ext q
    have := ComplexProjectiveSpace.eq_mk_single_iff (N := 1) 1 q
    have hs1 : (Pi.single (1 : Fin 2) (1 : ℂ)) = ![0, 1] := by
      funext i; fin_cases i <;> rfl
    simp only [hs1, ne_eq] at this
    simp only [mem_ofPred_eq, mem_singleton_iff, ← this]
    simp

end P1

/-! ### `ex:P2` -/

section P2
variable (hs : latticePolytopeEdgeSmooth (simplexGenerator 2))

/-- The rays `u_{σ_4} = (-1,-1)`, `u_{σ_5} = (1,0)`, `u_{σ_6} = (0,1)` of `ℙ²`. -/
def P2ray4 : Fin 2 → ℤ := simplexNegRay 2
def P2ray5 : Fin 2 → ℤ := Pi.single 0 1
def P2ray6 : Fin 2 → ℤ := Pi.single 1 1

theorem P2ray_values : P2ray4 = ![-1, -1] ∧ P2ray5 = ![1, 0] ∧ P2ray6 = ![0, 1] := by
  refine ⟨?_, ?_, ?_⟩ <;> funext i <;> fin_cases i <;> rfl

/-- Source `ex:P2`: `Σ(1) = {σ_4, σ_5, σ_6}`. -/
theorem P2_rays : PolytopeToricRays (simplexGenerator 2) hs = {P2ray4, P2ray5, P2ray6} := by
  rw [simplex_rays]
  ext u
  simp only [mem_union, mem_range, mem_singleton_iff, mem_insert_iff, Fin.exists_fin_two,
    P2ray4, P2ray5, P2ray6]
  constructor
  · rintro ((h | h) | h)
    · right; left; exact h.symm
    · right; right; exact h.symm
    · left; exact h
  · rintro (h | h | h)
    · right; exact h
    · left; left; exact h.symm
    · left; right; exact h.symm

theorem P2_vertexConeRays :
    (vertexConeRay (simplexBasis (none : Option (Fin 2))) 0 = P2ray5 ∧
      vertexConeRay (simplexBasis (none : Option (Fin 2))) 1 = P2ray6) ∧
    (vertexConeRay (simplexBasis (some (0 : Fin 2))) 0 = P2ray4 ∧
      vertexConeRay (simplexBasis (some (0 : Fin 2))) 1 = P2ray6) ∧
    (vertexConeRay (simplexBasis (some (1 : Fin 2))) 0 = P2ray5 ∧
      vertexConeRay (simplexBasis (some (1 : Fin 2))) 1 = P2ray4) := by
  refine ⟨⟨simplex_vertexConeRay_none 0, simplex_vertexConeRay_none 1⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    rw [simplex_vertexConeRay_some] <;> rfl

/-- Source `ex:P2`: the maximal cones `σ_1 = cone(σ_5, σ_6)` (vertex `0`),
`σ_2 = cone(σ_6, σ_4)` (vertex `(1,0)`) and `σ_3 = cone(σ_4, σ_5)` (vertex `(0,1)`). -/
theorem P2_maximalCones :
    range (polytopeToricRayGenerator _ hs (simplexVertex none)) = {P2ray5, P2ray6} ∧
    range (polytopeToricRayGenerator _ hs (simplexVertex (some 0))) = {P2ray4, P2ray6} ∧
    range (polytopeToricRayGenerator _ hs (simplexVertex (some 1))) = {P2ray5, P2ray4} := by
  obtain ⟨⟨h00, h01⟩, ⟨h10, h11⟩, ⟨h20, h21⟩⟩ := P2_vertexConeRays
  refine ⟨?_, ?_, ?_⟩
  · rw [range_vertexCone_two hs _ (simplex_isVertexConeBasis none), h00, h01]
  · rw [range_vertexCone_two hs _ (simplex_isVertexConeBasis (some 0)), h10, h11]
  · rw [range_vertexCone_two hs _ (simplex_isVertexConeBasis (some 1)), h20, h21]

/-- Source `ex:P2`: `Σ` consists of the zero cone `σ_0`, the three rays `σ_4, σ_5, σ_6` and
the three two-dimensional cones `σ_1 = cone(σ_5,σ_6)`, `σ_2 = cone(σ_6,σ_4)`,
`σ_3 = cone(σ_4,σ_5)` (a cone is recorded by the set of the generators of its rays). -/
theorem P2_fan (R : Set (PolytopeToricRays (simplexGenerator 2) hs)) :
    IsToricFanCone R ↔ Subtype.val '' R ∈ ({∅, {P2ray4}, {P2ray5}, {P2ray6}, {P2ray5, P2ray6},
      {P2ray4, P2ray6}, {P2ray5, P2ray4}} : Set (Set (Fin 2 → ℤ))) := by
  rw [isToricFanCone_iff_of_vertexCones hs simplexBasis simplex_isVertexConeBasis]
  obtain ⟨⟨h00, h01⟩, ⟨h10, h11⟩, ⟨h20, h21⟩⟩ := P2_vertexConeRays
  have hval : ∀ (k : Option (Fin 2)) (S : Set (Fin 2)),
      (∀ ρ, ρ ∈ R ↔ ∃ j ∈ S, vertexConeRay (simplexBasis k) j = ρ.val) →
        Subtype.val '' R = vertexConeRay (simplexBasis k) '' S := by
    intro k S hS
    ext u
    constructor
    · rintro ⟨ρ, hρ, rfl⟩
      obtain ⟨j, hj, h⟩ := (hS ρ).mp hρ
      exact ⟨j, hj, h⟩
    · rintro ⟨j, hj, rfl⟩
      have hmem : vertexConeRay (simplexBasis k) j ∈ PolytopeToricRays (simplexGenerator 2) hs :=
        vertexConeRay_mem_polytopeToricRays hs ⟨_, (simplex_isVertexConeBasis k).mem_vertices⟩
          (simplex_isVertexConeBasis k) j
      exact ⟨⟨_, hmem⟩, (hS _).mpr ⟨j, hj, rfl⟩, rfl⟩
  have hinj : ∀ T : Set (Fin 2 → ℤ), T ⊆ PolytopeToricRays (simplexGenerator 2) hs →
      Subtype.val '' R = T → ∀ ρ, ρ ∈ R ↔ ρ.val ∈ T := by
    intro T _ hT ρ
    rw [← hT]
    exact ⟨fun h => ⟨ρ, h, rfl⟩, fun ⟨ρ', h', he⟩ => Subtype.ext he ▸ h'⟩
  have hsub : ∀ {T : Set (Fin 2 → ℤ)}, T ⊆ {P2ray4, P2ray5, P2ray6} →
      T ⊆ PolytopeToricRays (simplexGenerator 2) hs := by
    intro T hT; rw [P2_rays]; exact hT
  constructor
  · rintro ⟨k, S, hS⟩
    rw [hval k S hS]
    simp only [mem_insert_iff, mem_singleton_iff]
    rcases set_fin_two S with rfl | rfl | rfl | rfl <;> rcases k with _ | ⟨i⟩ <;>
      try fin_cases i
    all_goals
      simp [image_empty, image_singleton, image_univ, range_fin_two_eq, h00, h01, h10, h11,
        h20, h21]
  · intro hR
    simp only [mem_insert_iff, mem_singleton_iff] at hR
    have key : ∀ (k : Option (Fin 2)) (S : Set (Fin 2)),
        Subtype.val '' R = vertexConeRay (simplexBasis k) '' S →
          ∃ (k : Option (Fin 2)) (S : Set (Fin 2)), ∀ ρ, ρ ∈ R ↔
            ∃ j ∈ S, vertexConeRay (simplexBasis k) j = ρ.val := by
      intro k S h
      refine ⟨k, S, fun ρ => ?_⟩
      have := hinj _ (by rw [← h]; rintro _ ⟨ρ', -, rfl⟩; exact ρ'.property) h ρ
      rw [this]; simp
    rcases hR with h | h | h | h | h | h | h
    · exact key none ∅ (by rw [h, image_empty])
    · exact key (some 0) {0} (by rw [h, image_singleton, h10])
    · exact key none {0} (by rw [h, image_singleton, h00])
    · exact key none {1} (by rw [h, image_singleton, h01])
    · exact key none univ (by rw [h, image_univ, range_fin_two_eq, h00, h01])
    · exact key (some 0) univ (by rw [h, image_univ, range_fin_two_eq, h10, h11])
    · exact key (some 1) univ (by rw [h, image_univ, range_fin_two_eq, h20, h21])

/-- The rays `σ_4, σ_5, σ_6` as elements of `Σ(1)`. -/
def P2rho4 : PolytopeToricRays (simplexGenerator 2) hs := ⟨P2ray4, by rw [P2_rays]; simp⟩
def P2rho5 : PolytopeToricRays (simplexGenerator 2) hs := ⟨P2ray5, by rw [P2_rays]; simp⟩
def P2rho6 : PolytopeToricRays (simplexGenerator 2) hs := ⟨P2ray6, by rw [P2_rays]; simp⟩

theorem P2_mem_divisor_iff (q : ComplexProjectiveSpace 2) :
    ((simplexProjectiveHomeomorph hs).symm q ∈ toricPrimeDivisor (P2rho4 hs) ↔ q.rep 0 = 0) ∧
    ((simplexProjectiveHomeomorph hs).symm q ∈ toricPrimeDivisor (P2rho5 hs) ↔ q.rep 1 = 0) ∧
    ((simplexProjectiveHomeomorph hs).symm q ∈ toricPrimeDivisor (P2rho6 hs) ↔ q.rep 2 = 0) := by
  have h4 := simplexProjectiveHomeomorph_image_neg hs (P2rho4 hs).property
  have h5 := simplexProjectiveHomeomorph_image_single hs 0 (P2rho5 hs).property
  have h6 := simplexProjectiveHomeomorph_image_single hs 1 (P2rho6 hs).property
  rw [Homeomorph.image_eq_preimage_symm] at h4 h5 h6
  refine ⟨?_, ?_, ?_⟩
  · exact Iff.of_eq (congrArg (q ∈ ·) h4)
  · exact Iff.of_eq (congrArg (q ∈ ·) h5)
  · exact Iff.of_eq (congrArg (q ∈ ·) h6)

/-- Source `ex:P2`: the orbit–cone correspondence in homogeneous coordinates of `ℙ²`:
`D_{σ_4} = {[0 : X_1 : X_2]}`, `D_{σ_5} = {[X_0 : 0 : X_2]}`, `D_{σ_6} = {[X_0 : X_1 : 0]}`,
`D_{σ_1} = {[1 : 0 : 0]}`, `D_{σ_2} = {[0 : 1 : 0]}`, `D_{σ_3} = {[0 : 0 : 1]}`,
`D_{σ_0} = ℙ²` (here `D_σ = V(σ) = ⋂_{ρ ∈ σ(1)} D_ρ`). -/
theorem P2_orbitClosures :
    simplexProjectiveHomeomorph hs '' toricPrimeDivisor (P2rho4 hs) = {q | q.rep 0 = 0} ∧
    simplexProjectiveHomeomorph hs '' toricPrimeDivisor (P2rho5 hs) = {q | q.rep 1 = 0} ∧
    simplexProjectiveHomeomorph hs '' toricPrimeDivisor (P2rho6 hs) = {q | q.rep 2 = 0} ∧
    simplexProjectiveHomeomorph hs '' toricOrbitClosure {P2rho5 hs, P2rho6 hs} =
      {ComplexProjectiveSpace.mk ![1, 0, 0] (fun h => one_ne_zero (congrFun h 0))} ∧
    simplexProjectiveHomeomorph hs '' toricOrbitClosure {P2rho6 hs, P2rho4 hs} =
      {ComplexProjectiveSpace.mk ![0, 1, 0] (fun h => one_ne_zero (congrFun h 1))} ∧
    simplexProjectiveHomeomorph hs '' toricOrbitClosure {P2rho4 hs, P2rho5 hs} =
      {ComplexProjectiveSpace.mk ![0, 0, 1] (fun h => one_ne_zero (congrFun h 2))} ∧
    toricOrbitClosure (∅ : Set (PolytopeToricRays (simplexGenerator 2) hs)) = univ := by
  have hpt : ∀ (i : Fin 3) (w : Fin 3 → ℂ) (hw : w ≠ 0), Pi.single i (1 : ℂ) = w →
      {q : ComplexProjectiveSpace 2 | ∀ j, j ≠ i → q.rep j = 0} =
        {ComplexProjectiveSpace.mk w hw} := by
    rintro i w hw rfl
    ext q
    exact ComplexProjectiveSpace.eq_mk_single_iff i q
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext q; rw [Homeomorph.image_eq_preimage_symm]; exact (P2_mem_divisor_iff hs q).1
  · ext q; rw [Homeomorph.image_eq_preimage_symm]; exact (P2_mem_divisor_iff hs q).2.1
  · ext q; rw [Homeomorph.image_eq_preimage_symm]; exact (P2_mem_divisor_iff hs q).2.2
  · rw [← hpt 0 _ _ (by funext i; fin_cases i <;> rfl), Homeomorph.image_eq_preimage_symm]
    ext q
    simp only [mem_preimage, toricOrbitClosure, mem_iInter, mem_insert_iff, mem_singleton_iff,
      forall_eq_or_imp, forall_eq, mem_ofPred_eq, (P2_mem_divisor_iff hs q).2.1,
      (P2_mem_divisor_iff hs q).2.2, Fin.forall_fin_succ, Fin.isValue]
    simp
  · rw [← hpt 1 _ _ (by funext i; fin_cases i <;> rfl), Homeomorph.image_eq_preimage_symm]
    ext q
    simp only [mem_preimage, toricOrbitClosure, mem_iInter, mem_insert_iff, mem_singleton_iff,
      forall_eq_or_imp, forall_eq, mem_ofPred_eq, (P2_mem_divisor_iff hs q).1,
      (P2_mem_divisor_iff hs q).2.2, Fin.forall_fin_succ, Fin.isValue]
    simp
    tauto
  · rw [← hpt 2 _ _ (by funext i; fin_cases i <;> rfl), Homeomorph.image_eq_preimage_symm]
    ext q
    simp only [mem_preimage, toricOrbitClosure, mem_iInter, mem_insert_iff, mem_singleton_iff,
      forall_eq_or_imp, forall_eq, mem_ofPred_eq, (P2_mem_divisor_iff hs q).1,
      (P2_mem_divisor_iff hs q).2.1, Fin.forall_fin_succ, Fin.isValue]
    simp
  · ext p; simp [toricOrbitClosure]

/-- Source `ex:P2`: `D = D_{σ_4}`, i.e. `a_{σ_5} = a_{σ_6} = 0`, `a_{σ_4} = 1`, and
`P_D = {m : m_1 + m_2 ≤ 1, m_1 ≥ 0, m_2 ≥ 0}`. -/
theorem P2_divisor :
    simplexHyperplaneDivisor hs (P2rho4 hs) = 1 ∧ simplexHyperplaneDivisor hs (P2rho5 hs) = 0 ∧
    simplexHyperplaneDivisor hs (P2rho6 hs) = 0 ∧
    toricDivisorPolytope (simplexHyperplaneDivisor hs) =
      {m | m 0 + m 1 ≤ 1 ∧ 0 ≤ m 0 ∧ 0 ≤ m 1} := by
  refine ⟨by simp [simplexHyperplaneDivisor, P2rho4, P2ray4],
    by simp [simplexHyperplaneDivisor, P2rho5, P2ray5, single_ne_simplexNegRay],
    by simp [simplexHyperplaneDivisor, P2rho6, P2ray6, single_ne_simplexNegRay], ?_⟩
  rw [toricDivisorPolytope_simplexHyperplaneDivisor (N := 2) hs]
  ext m
  simp only [mem_ofPred_eq, Fin.forall_fin_two, Fin.sum_univ_two]
  tauto

/-- Source `ex:P2`: the Cartier data `m_{σ_1} = (0,0)`, `m_{σ_2} = (1,0)`, `m_{σ_3} = (0,1)`. -/
theorem P2_cartierData :
    toricCartierDatum (simplexHyperplaneDivisor hs) (simplexVertex none) = ![0, 0] ∧
    toricCartierDatum (simplexHyperplaneDivisor hs) (simplexVertex (some 0)) = ![1, 0] ∧
    toricCartierDatum (simplexHyperplaneDivisor hs) (simplexVertex (some 1)) = ![0, 1] := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · rw [toricCartierDatum_simplexHyperplaneDivisor]
    funext i; fin_cases i <;> rfl

/-- Source `ex:P2` ("`L = O_X(D) = O_{ℙ²}(1)`; hence `L` is ample"): `D = D_P` is the divisor of
the polytope, its line bundle carries the Guillemin metric whose curvature `ω` is a Kähler form,
and under `X ≅ ℙ²` the divisor `D = D_{σ_4}` is the hyperplane `{X_0 = 0}` (so
`O(D) = O(H) = O_{ℙ²}(1)`). -/
theorem P2_lineBundle :
    simplexHyperplaneDivisor hs = polytopeToricAmpleDivisor (simplexGenerator 2) hs ∧
    (guilleminBigToricMetric (simplexGenerator 2) hs).form = polytopeToricKahlerForm _ hs ∧
    (polytopeToricKahlerForm (simplexGenerator 2) hs).val.IsKahler ∧
    simplexProjectiveHomeomorph hs '' toricPrimeDivisor (P2rho4 hs) = {q | q.rep 0 = 0} :=
  ⟨simplexHyperplaneDivisor_eq_ample hs, rfl, (polytopeToricKahlerBackground _ hs).2,
    (P2_orbitClosures hs).1⟩

/-- Source `ex:P2`: the faces `Q_σ` of `P_D`: `Q_{σ_1} = {(0,0)}`, `Q_{σ_2} = {(1,0)}`,
`Q_{σ_3} = {(0,1)}`, `Q_{σ_4} = {m ≥ 0, m_1 + m_2 = 1}`, `Q_{σ_5} = {0} × [0,1]`,
`Q_{σ_6} = [0,1] × {0}`, `Q_{σ_0} = P_D`. -/
theorem P2_faces :
    toricDivisorFace (simplexHyperplaneDivisor hs) {P2rho5 hs, P2rho6 hs} =
      {latticeVector ![0, 0]} ∧
    toricDivisorFace (simplexHyperplaneDivisor hs) {P2rho6 hs, P2rho4 hs} =
      {latticeVector ![1, 0]} ∧
    toricDivisorFace (simplexHyperplaneDivisor hs) {P2rho4 hs, P2rho5 hs} =
      {latticeVector ![0, 1]} ∧
    toricDivisorFace (simplexHyperplaneDivisor hs) {P2rho4 hs} =
      {m | 0 ≤ m 0 ∧ 0 ≤ m 1 ∧ m 0 + m 1 = 1} ∧
    toricDivisorFace (simplexHyperplaneDivisor hs) {P2rho5 hs} =
      {m | m 0 = 0 ∧ 0 ≤ m 1 ∧ m 1 ≤ 1} ∧
    toricDivisorFace (simplexHyperplaneDivisor hs) {P2rho6 hs} =
      {m | 0 ≤ m 0 ∧ m 0 ≤ 1 ∧ m 1 = 0} ∧
    toricDivisorFace (simplexHyperplaneDivisor hs) ∅ = toricDivisorPolytope (simplexHyperplaneDivisor hs) := by
  obtain ⟨h4, h5, h6, hP⟩ := P2_divisor hs
  have hl4 : ∀ m : EuclideanSpace ℝ (Fin 2), latticeFunctional (P2rho4 hs).val m = -m 0 - m 1 := by
    intro m; simp [P2rho4, P2ray4, simplexNegRay, latticeFunctional_two]; ring
  have hl5 : ∀ m : EuclideanSpace ℝ (Fin 2), latticeFunctional (P2rho5 hs).val m = m 0 := by
    intro m; simp [P2rho5, P2ray5, latticeFunctional_two]
  have hl6 : ∀ m : EuclideanSpace ℝ (Fin 2), latticeFunctional (P2rho6 hs).val m = m 1 := by
    intro m; simp [P2rho6, P2ray6, latticeFunctional_two]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, toricDivisorFace_empty _⟩
  all_goals
    ext m
    simp only [toricDivisorFace, hP, mem_insert_iff, mem_singleton_iff, forall_eq_or_imp,
      forall_eq, mem_ofPred_eq, hl4, hl5, hl6, h4, h5, h6, eq_latticeVector_iff_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Int.cast_zero, Int.cast_one, neg_zero]
    constructor <;> intro h <;> casesm* _ ∧ _ <;> (repeat' constructor) <;> linarith

/-- The flag of `ex:OkounP2` (reference cone `σ_1`, `ρ_1 = σ_5`, `ρ_2 = σ_6`) exists. -/
theorem P2_exists_flagOrder :
    ∃ e : Fin 2 ≃ Fin 2,
      polytopeToricRayGenerator _ hs (simplexVertex none) (e 0) = P2ray5 ∧
      polytopeToricRayGenerator _ hs (simplexVertex none) (e 1) = P2ray6 := by
  obtain ⟨e, he⟩ := simplex_exists_flagOrder (N := 2) hs
  exact ⟨e, he 0, he 1⟩

/-- Source `ex:OkounP2`: for the reference cone `σ_1` and `ρ_1 = σ_5`, `ρ_2 = σ_6`:
`Y_1 = {[X_0 : 0 : X_2]}`, `Y_2 = {[X_0 : 0 : 0]} = {[1 : 0 : 0]}`, `Φ(m_1, m_2) = (m_1, m_2)`
and `Δ_{Y•}(O_{ℙ²}(1)) = P_D`. -/
theorem P2_okounkov (e : Fin 2 ≃ Fin 2)
    (he0 : polytopeToricRayGenerator _ hs (simplexVertex none) (e 0) = P2ray5)
    (he1 : polytopeToricRayGenerator _ hs (simplexVertex none) (e 1) = P2ray6) :
    simplexProjectiveHomeomorph hs '' toricFlag hs (simplexVertex none) e 1 = {q | q.rep 1 = 0} ∧
    simplexProjectiveHomeomorph hs '' toricFlag hs (simplexVertex none) e 2 =
      {ComplexProjectiveSpace.mk ![1, 0, 0] (fun h => one_ne_zero (congrFun h 0))} ∧
    (∀ m, toricFlagLatticeMap hs (simplexVertex none) e (simplexHyperplaneDivisor hs) m = m) ∧
    toricOkounkovBody (simplexVertex none) e (simplexHyperplaneDivisor hs) =
      EuclideanSpace.equiv (Fin 2) ℝ '' toricDivisorPolytope (simplexHyperplaneDivisor hs) := by
  have he : ∀ l, polytopeToricRayGenerator _ hs (simplexVertex none) (e l) = Pi.single l 1 := by
    intro l; fin_cases l
    · exact he0
    · exact he1
  obtain ⟨hΦ, hΔ, -⟩ := simplex_okounkovBody hs e he
  have h0 : polytopeToricRay _ hs (simplexVertex none) (e 0) = P2rho5 hs := Subtype.ext he0
  have h1 : polytopeToricRay _ hs (simplexVertex none) (e 1) = P2rho6 hs := Subtype.ext he1
  obtain ⟨hY1, hY2⟩ := toricFlag_two hs (simplexVertex none) e
  obtain ⟨-, h5, -, h56, -⟩ := P2_orbitClosures hs
  refine ⟨?_, ?_, hΦ, hΔ⟩
  · rw [hY1, h0, h5]
  · rw [hY2, h0, h1, h56]

end P2

end SGPT.Toric
