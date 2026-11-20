import SGPT.Toric.BigToric2Orbits

/-!
# Concrete Delzant polytopes: the vertex-cone criterion

Source `chapter_toric_ample.tex`, `sec:toricsetup` (the smoothness footnote: for every vertex
`v` of `P` the vectors `w_E - v`, `w_E` the first lattice point on the edge `E ∋ v`, form a
basis of `M`; `CLS11`, Definition 2.4.2) and the examples of `chapter_toric_big.tex`.

The toric manifold `X_P = PolytopeToricVariety γ hs` needs the Delzant hypothesis
`hs : latticePolytopeEdgeSmooth γ`, phrased with the *actual* edges of `P = conv(γ)` (extreme
segments at a vertex).  To produce it for explicit polytopes we prove a criterion that only
involves a lattice basis at each vertex and finitely many inequalities:

`IsVertexConeBasis γ v c`: `v ∈ P`, `v + c_j ∈ P` for all `j`, and every generator `γ_k`
lies in the cone `v + ℝ_{≥0} c_1 + ⋯ + ℝ_{≥0} c_n` (`c.repr (γ_k - v) ≥ 0`).

Under this hypothesis
* `IsVertexConeBasis.mem_vertices`: `v` is a vertex of `P`;
* `IsVertexConeBasis.exists_edge_eq`, `IsVertexConeBasis.edgeEquiv`: the edges of `P` at `v`
  are exactly the `n` segments `E_j = P ∩ {x : (x - v)_k = 0, k ≠ j}` (coordinates in the
  basis `c`), each `E_j` being a nondegenerate extreme segment containing `v + c_j`;
* `IsVertexConeBasis.latticePolytopeEdgeSmoothAt`: `P` is smooth at `v`;
* `latticePolytopeEdgeSmooth_of_vertexCones`: if every generator carries a vertex-cone basis,
  `P` is a Delzant polytope.

The basis `originalPolytopeNativeBasis γ hs v` of the vertex chart is defined by choice.  It is
characterised (`exists_perm_originalPolytopeNativeBasis_eq`): for any vertex-cone basis `c` at
`v` there is a permutation `τ` with `b_j(v) = c_{τ j}`, hence the rays of the maximal cone `σ_v`
are the dual basis of `c` (`polytopeToricRayGenerator_eq_vertexConeRay`) and
`Σ(1) = ⋃_k (dual basis of c_k)` (`polytopeToricRays_eq_of_vertexCones`).
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set SGPT.AlmostSemigroup.Counting
open scoped BigOperators

variable {n : ℕ} {K : Type*}

theorem integerCast_sub_toric4 (x y : Fin n → ℤ) :
    integerCast (x - y) = integerCast x - integerCast y := by
  ext i; simp [integerCast]

theorem integerCast_add_toric4 (x y : Fin n → ℤ) :
    integerCast (x + y) = integerCast x + integerCast y := by
  ext i; simp [integerCast]

/-! ### Real coordinates at a vertex -/

/-- The real affine coordinates of `x` at the lattice point `v` in the lattice basis `c`:
`x - v = ∑_k (vertexConeCoord v c x k) c_k`. -/
def vertexConeCoord (v : Fin n → ℤ) (c : Module.Basis (Fin n) ℤ (Fin n → ℤ))
    (x : Fin n → ℝ) (k : Fin n) : ℝ :=
  (integralRealBasis c).repr (x - integerCast v) k

variable (v : Fin n → ℤ) (c : Module.Basis (Fin n) ℤ (Fin n → ℤ))

theorem vertexConeCoord_integerCast (m : Fin n → ℤ) (k : Fin n) :
    vertexConeCoord v c (integerCast m) k = (c.repr (m - v) k : ℝ) := by
  rw [vertexConeCoord, ← integerCast_sub_toric4, integralRealBasis_repr_integerCast]

theorem vertexConeCoord_vertex (k : Fin n) : vertexConeCoord v c (integerCast v) k = 0 := by
  rw [vertexConeCoord_integerCast, sub_self, map_zero, Finsupp.zero_apply, Int.cast_zero]

theorem vertexConeCoord_affine {x y : Fin n → ℝ} {a b : ℝ} (hab : a + b = 1) (k : Fin n) :
    vertexConeCoord v c (a • x + b • y) k =
      a * vertexConeCoord v c x k + b * vertexConeCoord v c y k := by
  have h1 : a • x + b • y - integerCast v =
      a • (x - integerCast v) + b • (y - integerCast v) := by
    obtain rfl : b = 1 - a := by linarith
    module
  simp only [vertexConeCoord, h1, map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply,
    smul_eq_mul]

theorem continuous_vertexConeCoord (k : Fin n) : Continuous fun x => vertexConeCoord v c x k :=
  (continuous_apply k).comp
    ((integralRealBasis c).equivFunL.continuous.comp (continuous_id.sub continuous_const))

/-- `x = v + ∑_k x_k c_k` in the coordinates at `v`. -/
theorem vertexConeCoord_expand (x : Fin n → ℝ) :
    x = integerCast v + ∑ k, vertexConeCoord v c x k • integerCast (c k) := by
  have h := (integralRealBasis c).sum_repr (x - integerCast v)
  simp only [integralRealBasis_apply] at h
  unfold vertexConeCoord
  rw [h]
  abel

theorem vertexConeCoord_vertex_add_sum (s : Fin n → ℝ) (k : Fin n) :
    vertexConeCoord v c (integerCast v + ∑ l, s l • integerCast (c l)) k = s k := by
  unfold vertexConeCoord
  rw [add_sub_cancel_left]
  simp_rw [← integralRealBasis_apply]
  rw [Module.Basis.repr_sum_self]

/-- Points with the same coordinates at `v` coincide. -/
theorem eq_of_vertexConeCoord_eq {x y : Fin n → ℝ}
    (h : ∀ k, vertexConeCoord v c x k = vertexConeCoord v c y k) : x = y := by
  rw [vertexConeCoord_expand v c x, vertexConeCoord_expand v c y]
  simp only [h]

/-! ### Vertex-cone bases -/

/-- A *vertex-cone basis* of `P = conv(γ)` at the lattice point `v`: `v ∈ P`, `v + c_j ∈ P`
for every `j`, and every generator `γ_k` lies in `v + ∑_j ℝ_{≥0} c_j`. -/
structure IsVertexConeBasis (γ : K → Fin n → ℤ) (v : Fin n → ℤ)
    (c : Module.Basis (Fin n) ℤ (Fin n → ℤ)) : Prop where
  vertex_mem : integerCast v ∈ latticePolytope γ
  add_mem : ∀ j, integerCast (v + c j) ∈ latticePolytope γ
  cone : ∀ k j, 0 ≤ c.repr (γ k - v) j

/-- The face of `P` through `v` along the `j`-th basis direction:
`E_j = {x ∈ P : (x - v)_k = 0 for k ≠ j}`. -/
def vertexConeEdge (γ : K → Fin n → ℤ) (j : Fin n) : Set (Fin n → ℝ) :=
  {x | x ∈ latticePolytope γ ∧ ∀ k, k ≠ j → vertexConeCoord v c x k = 0}

/-- The dual basis vector `u_k ∈ N` of `c`: `⟨c_j, u_k⟩ = δ_{jk}`. -/
def vertexConeRay (k : Fin n) : Fin n → ℤ := fun l => c.repr (Pi.single l 1) k

theorem intPairing_vertexConeRay (m : Fin n → ℤ) (k : Fin n) :
    intPairing m (vertexConeRay c k) = c.repr m k := by
  conv_rhs => rw [← Finset.univ_sum_single m]
  have hs : (∑ l, (Pi.single l (m l) : Fin n → ℤ)) = ∑ l, m l • (Pi.single l 1 : Fin n → ℤ) := by
    refine Finset.sum_congr rfl fun l _ => ?_
    ext i
    by_cases hi : i = l
    · subst hi; simp
    · simp [hi]
  rw [hs]
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
    smul_eq_mul, intPairing, vertexConeRay]

variable {v c}

section EdgeFaces

theorem vertexConeCoord_add_self (v : Fin n → ℤ) (c : Module.Basis (Fin n) ℤ (Fin n → ℤ)) (j : Fin n) :
    vertexConeCoord v c (integerCast (v + c j)) j = 1 := by
  rw [vertexConeCoord_integerCast, add_sub_cancel_left, c.repr_self,
    Finsupp.single_apply, if_pos rfl, Int.cast_one]

theorem convex_vertexConeEdge (γ : K → Fin n → ℤ) (j : Fin n) : Convex ℝ (vertexConeEdge v c γ j) := by
  rintro x ⟨hx, hx0⟩ y ⟨hy, hy0⟩ a b ha hb hab
  refine ⟨convex_latticePolytope γ hx hy ha hb hab, fun k hk => ?_⟩
  rw [vertexConeCoord_affine v c hab, hx0 k hk, hy0 k hk]
  ring

/-- A point of `E_j` is `v + x_j c_j`. -/
theorem eq_of_mem_vertexConeEdge {γ : K → Fin n → ℤ} {j : Fin n} {x : Fin n → ℝ} (hx : x ∈ vertexConeEdge v c γ j) :
    x = integerCast v + vertexConeCoord v c x j • integerCast (c j) := by
  conv_lhs => rw [vertexConeCoord_expand v c x]
  congr 1
  rw [Finset.sum_eq_single j]
  · intro k _ hk
    rw [hx.2 k hk, zero_smul]
  · intro hj; exact absurd (Finset.mem_univ j) hj

theorem isCompact_vertexConeEdge [Fintype K] (γ : K → Fin n → ℤ) (j : Fin n) : IsCompact (vertexConeEdge v c γ j) := by
  have heq : vertexConeEdge v c γ j = latticePolytope γ ∩
      ⋂ k ∈ ({j}ᶜ : Set (Fin n)), {x | vertexConeCoord v c x k = 0} := by
    ext x
    simp [vertexConeEdge]
  rw [heq]
  exact (isCompact_latticePolytope γ).inter_right
    (isClosed_biInter fun k _ => isClosed_eq (continuous_vertexConeCoord v c k) continuous_const)

end EdgeFaces

namespace IsVertexConeBasis

variable {γ : K → Fin n → ℤ} (h : IsVertexConeBasis γ v c)
include h

/-- `P ⊆ v + cone(c)`: all coordinates at `v` are nonnegative on `P`. -/
theorem coord_nonneg {x : Fin n → ℝ} (hx : x ∈ latticePolytope γ) (k : Fin n) :
    0 ≤ vertexConeCoord v c x k := by
  have hconv : Convex ℝ {y : Fin n → ℝ | ∀ k, 0 ≤ vertexConeCoord v c y k} := by
    intro y hy z hz a b ha hb hab
    simp only [mem_ofPred_eq] at hy hz ⊢
    intro k
    rw [vertexConeCoord_affine v c hab]
    exact add_nonneg (mul_nonneg ha (hy k)) (mul_nonneg hb (hz k))
  have hsub : range (fun k => integerCast (γ k)) ⊆
      {y : Fin n → ℝ | ∀ k, 0 ≤ vertexConeCoord v c y k} := by
    rintro _ ⟨i, rfl⟩ k
    rw [vertexConeCoord_integerCast]
    exact_mod_cast h.cone i k
  exact convexHull_min hsub hconv hx k

/-- The lattice simplex `conv(v, v + c_1, …, v + c_n)` lies in `P`. -/
theorem vertex_add_sum_mem (s : Fin n → ℝ) (hs0 : ∀ k, 0 ≤ s k) (hs1 : ∑ k, s k ≤ 1) :
    integerCast v + ∑ k, s k • integerCast (c k) ∈ latticePolytope γ := by
  have hmem := (convex_latticePolytope γ).sum_mem (t := Finset.univ)
    (w := fun o : Option (Fin n) => o.elim (1 - ∑ k, s k) s)
    (z := fun o : Option (Fin n) => o.elim (integerCast v) (fun k => integerCast (v + c k)))
    (by
      rintro (_ | k) _
      · simp only [Option.elim]; linarith
      · exact hs0 k)
    (by rw [Fintype.sum_option]; simp)
    (by
      rintro (_ | k) _
      · exact h.vertex_mem
      · exact h.add_mem k)
  rw [Fintype.sum_option] at hmem
  simp only [Option.elim] at hmem
  convert hmem using 1
  simp only [integerCast_add_toric4, smul_add, Finset.sum_add_distrib, ← Finset.sum_smul,
    sub_smul, one_smul]
  abel

/-- `v` is an extreme point of `P`. -/
theorem mem_extremePoints :
    integerCast v ∈ (latticePolytope γ).extremePoints ℝ := by
  refine _root_.mem_extremePoints.mpr ⟨h.vertex_mem, fun x hx y hy hv => ?_⟩
  obtain ⟨a, b, ha, hb, hab, hxy⟩ := hv
  have hzero : ∀ k, vertexConeCoord v c x k = 0 ∧ vertexConeCoord v c y k = 0 := by
    intro k
    have h0 := vertexConeCoord_vertex v c k
    rw [← hxy, vertexConeCoord_affine v c hab] at h0
    have h1 := h.coord_nonneg hx k
    have h2 := h.coord_nonneg hy k
    constructor <;> nlinarith [mul_nonneg ha.le h1, mul_nonneg hb.le h2]
  exact ⟨eq_of_vertexConeCoord_eq v c fun k => by rw [(hzero k).1, vertexConeCoord_vertex],
    eq_of_vertexConeCoord_eq v c fun k => by rw [(hzero k).2, vertexConeCoord_vertex]⟩

/-- `v` is a vertex of `P`. -/
theorem mem_vertices : v ∈ latticePolytopeVertices γ :=
  ⟨h.vertex_mem, h.mem_extremePoints⟩

theorem vertex_mem_edge (j : Fin n) : integerCast v ∈ vertexConeEdge v c γ j :=
  ⟨h.vertex_mem, fun k _ => vertexConeCoord_vertex v c k⟩

theorem add_mem_edge (j : Fin n) : integerCast (v + c j) ∈ vertexConeEdge v c γ j := by
  refine ⟨h.add_mem j, fun k hk => ?_⟩
  rw [vertexConeCoord_integerCast, add_sub_cancel_left, c.repr_self,
    Finsupp.single_apply, if_neg (Ne.symm hk), Int.cast_zero]

theorem isExtreme_edge (j : Fin n) :
    IsExtreme ℝ (latticePolytope γ) (vertexConeEdge v c γ j) := by
  refine ⟨fun _ hx => hx.1, ?_⟩
  intro x hx y hy z hz hzseg
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hzseg
  have hzero : ∀ k, k ≠ j → vertexConeCoord v c x k = 0 ∧ vertexConeCoord v c y k = 0 := by
    intro k hk
    have h0 := hz.2 k hk
    rw [vertexConeCoord_affine v c hab] at h0
    have h1 := h.coord_nonneg hx k
    have h2 := h.coord_nonneg hy k
    constructor <;> nlinarith [mul_nonneg ha.le h1, mul_nonneg hb.le h2]
  exact ⟨hx, fun k hk => (hzero k hk).1⟩

variable [Fintype K]

/-- `E_j` is a nondegenerate segment `[v, w_j]` with `w_j = v + L c_j`, `L ≥ 1`. -/
theorem exists_edge_eq_segment (j : Fin n) :
    ∃ w, w ∈ vertexConeEdge v c γ j ∧ 1 ≤ vertexConeCoord v c w j ∧
      vertexConeEdge v c γ j = segment ℝ (integerCast v) w := by
  obtain ⟨w, hwE, hwmax⟩ := (isCompact_vertexConeEdge γ j).exists_isMaxOn ⟨_, h.vertex_mem_edge j⟩
    (continuous_vertexConeCoord v c j).continuousOn
  set L := vertexConeCoord v c w j
  have hL1 : 1 ≤ L := by
    have := isMaxOn_iff.mp hwmax _ (h.add_mem_edge j)
    rw [vertexConeCoord_add_self v c j] at this
    exact this
  have hL : 0 < L := by linarith
  refine ⟨w, hwE, hL1, Subset.antisymm ?_ ((convex_vertexConeEdge γ j).segment_subset (h.vertex_mem_edge j) hwE)⟩
  intro x hx
  have hxnn := h.coord_nonneg hx.1 j
  have hxle : vertexConeCoord v c x j ≤ L := hwmax hx
  rw [segment_eq_image']
  refine ⟨vertexConeCoord v c x j / L, ⟨div_nonneg hxnn hL.le, (div_le_one hL).mpr hxle⟩, ?_⟩
  have hw' : w - integerCast v = L • integerCast (c j) := by
    rw [sub_eq_iff_eq_add']; exact eq_of_mem_vertexConeEdge hwE
  dsimp only
  rw [hw', smul_smul, div_mul_cancel₀ _ hL.ne']
  exact (eq_of_mem_vertexConeEdge hx).symm

/-- `E_j` is an edge of `P` at `v`. -/
theorem isOriginalPolytopeEdgeAt_edge (j : Fin n) :
    IsOriginalPolytopeEdgeAt (latticePolytope γ) (integerCast v) (vertexConeEdge v c γ j) := by
  obtain ⟨w, hwE, hw1, heq⟩ := h.exists_edge_eq_segment j
  refine ⟨w, ?_, heq, h.isExtreme_edge j⟩
  rintro rfl
  rw [vertexConeCoord_vertex] at hw1
  linarith

/-- The edge `E_j` as an element of the edge type of `P` at `v`. -/
def edge (j : Fin n) : latticePolytopeEdgesAt γ v :=
  ⟨vertexConeEdge v c γ j, h.isOriginalPolytopeEdgeAt_edge j⟩

theorem edge_injective : Function.Injective h.edge := by
  intro j k hjk
  by_contra hne
  have hmem := h.add_mem_edge j
  have hval : vertexConeEdge v c γ j = vertexConeEdge v c γ k := congrArg Subtype.val hjk
  rw [hval] at hmem
  have := hmem.2 j hne
  rw [vertexConeCoord_add_self v c j] at this
  exact one_ne_zero this

/-- Every edge of `P` at `v` is one of the `E_j`. -/
theorem exists_edge_eq (E : latticePolytopeEdgesAt γ v) : ∃ j, h.edge j = E := by
  classical
  obtain ⟨w, hwv, hE, hext⟩ := E.property
  have hwE : w ∈ E.val := by rw [hE]; exact right_mem_segment ℝ _ w
  have hwP : w ∈ latticePolytope γ := hext.1 hwE
  set t : Fin n → ℝ := fun k => vertexConeCoord v c w k with ht_def
  have ht0 : ∀ k, 0 ≤ t k := fun k => h.coord_nonneg hwP k
  -- some coordinate of `w - v` is positive
  obtain ⟨j, hj⟩ : ∃ j, 0 < t j := by
    by_contra hall
    push Not at hall
    apply hwv
    apply eq_of_vertexConeCoord_eq v c
    intro k
    rw [vertexConeCoord_vertex]
    exact le_antisymm (hall k) (ht0 k)
  -- all other coordinates vanish
  have hother : ∀ l, l ≠ j → t l = 0 := by
    intro l hl
    by_contra htl
    have htl' : 0 < t l := lt_of_le_of_ne (ht0 l) (Ne.symm htl)
    set S := ∑ k, t k
    have hS : 0 ≤ S := Finset.sum_nonneg fun k _ => ht0 k
    have htjS : t j ≤ S := Finset.single_le_sum (fun k _ => ht0 k) (Finset.mem_univ j)
    set ε : ℝ := 1 / (2 * (S + 1))
    have hε : 0 < ε := by positivity
    have hε2 : 2 * ε * S ≤ 1 := by
      have : 2 * ε * S = S / (S + 1) := by
        simp only [ε]; field_simp
      rw [this, div_le_one (by linarith)]; linarith
    have hε1 : ε ≤ 1 := by
      have : ε ≤ 1 / 2 := by
        simp only [ε]
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
      linarith
    set s1 : Fin n → ℝ := Pi.single j (2 * ε * t j)
    set s2 : Fin n → ℝ := fun k => if k = j then 0 else 2 * ε * t k
    have hs1 : ∀ k, 0 ≤ s1 k := by
      intro k; by_cases hk : k = j
      · subst hk; simp only [s1, Pi.single_eq_same]; positivity
      · simp only [s1, Pi.single_eq_of_ne hk, le_refl]
    have hs2 : ∀ k, 0 ≤ s2 k := by
      intro k; simp only [s2]; split_ifs
      · exact le_refl 0
      · have := ht0 k; positivity
    have hsum1 : ∑ k, s1 k ≤ 1 := by
      simp only [s1, Finset.sum_pi_single', Finset.mem_univ, if_true]
      nlinarith
    have hsum2 : ∑ k, s2 k ≤ 1 := by
      have : ∑ k, s2 k ≤ ∑ k, 2 * ε * t k :=
        Finset.sum_le_sum fun k _ => by
          simp only [s2]; split_ifs
          · have := ht0 k; positivity
          · exact le_refl _
      rw [← Finset.mul_sum] at this
      linarith
    set q1 := integerCast v + ∑ k, s1 k • integerCast (c k)
    set q2 := integerCast v + ∑ k, s2 k • integerCast (c k)
    have hq1 : q1 ∈ latticePolytope γ := h.vertex_add_sum_mem s1 hs1 hsum1
    have hq2 : q2 ∈ latticePolytope γ := h.vertex_add_sum_mem s2 hs2 hsum2
    set p := integerCast v + ε • (w - integerCast v)
    have hpE : p ∈ E.val := by
      rw [hE, segment_eq_image']
      exact ⟨ε, ⟨hε.le, hε1⟩, rfl⟩
    have hpseg : p ∈ openSegment ℝ q1 q2 := by
      refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
      apply eq_of_vertexConeCoord_eq v c
      intro k
      rw [vertexConeCoord_affine v c (by norm_num), vertexConeCoord_vertex_add_sum,
        vertexConeCoord_vertex_add_sum]
      have hp : p = (1 - ε) • integerCast v + ε • w := by simp only [p]; module
      rw [hp, vertexConeCoord_affine v c (by ring), vertexConeCoord_vertex]
      by_cases hk : k = j
      · subst hk; simp only [s1, s2, Pi.single_eq_same, if_true]; ring
      · simp only [s1, s2, Pi.single_eq_of_ne hk, if_neg hk]; ring
    have hq1E : q1 ∈ E.val := hext.2 hq1 hq2 hpE hpseg
    rw [hE, segment_eq_image'] at hq1E
    obtain ⟨θ, ⟨hθ0, hθ1⟩, hθ⟩ := hq1E
    have hθ' : integerCast v + θ • (w - integerCast v) = (1 - θ) • integerCast v + θ • w := by
      module
    have hcoord : ∀ k, θ * t k = s1 k := by
      intro k
      have := congrArg (fun x => vertexConeCoord v c x k) hθ
      simp only at this
      rw [hθ', vertexConeCoord_affine v c (by ring), vertexConeCoord_vertex,
        vertexConeCoord_vertex_add_sum] at this
      simpa using this
    have hl0 := hcoord l
    simp only [s1, Pi.single_eq_of_ne hl] at hl0
    have hθz : θ = 0 := by
      rcases mul_eq_zero.mp hl0 with h0 | h0
      · exact h0
      · exact absurd h0 htl
    have hj0 := hcoord j
    simp only [s1, Pi.single_eq_same, hθz, zero_mul] at hj0
    have : 0 < 2 * ε * t j := by positivity
    linarith
  -- `w ∈ E_j`
  have hwEj : w ∈ vertexConeEdge v c γ j := ⟨hwP, fun k hk => hother k hk⟩
  refine ⟨j, Subtype.ext ?_⟩
  change vertexConeEdge v c γ j = E.val
  obtain ⟨wj, hwjE, hwj1, hEj⟩ := h.exists_edge_eq_segment j
  apply Subset.antisymm
  · by_cases hww : w = wj
    · rw [hEj, hE, hww]
    · have hwopen : w ∈ openSegment ℝ (integerCast v) wj := by
        refine mem_openSegment_of_ne_left_right (Ne.symm hwv) (Ne.symm hww) ?_
        rw [← hEj]; exact hwEj
      have hwjE' : wj ∈ E.val :=
        hext.2 hwjE.1 h.vertex_mem hwE (by rw [openSegment_symm]; exact hwopen)
      rw [hEj]
      exact (E.property.convex).segment_subset (E.property.vertex_mem) hwjE'
  · rw [hE]
    exact (convex_vertexConeEdge γ j).segment_subset (h.vertex_mem_edge j) hwEj

/-- The edges of `P` at `v` are indexed by `Fin n`, `j ↦ E_j`. -/
def edgeEquiv : Fin n ≃ latticePolytopeEdgesAt γ v :=
  Equiv.ofBijective h.edge ⟨h.edge_injective, fun E => h.exists_edge_eq E⟩

theorem edgeEquiv_apply (j : Fin n) : h.edgeEquiv j = h.edge j := rfl

/-- The vertex-cone criterion: `P` is smooth (Delzant) at `v`, the edge basis being `c`. -/
theorem latticePolytopeEdgeSmoothAt : latticePolytopeEdgeSmoothAt γ v := by
  refine ⟨c.reindex h.edgeEquiv, fun E => ?_⟩
  rw [Module.Basis.reindex_apply]
  obtain ⟨j, rfl⟩ := h.edgeEquiv.surjective E
  rw [Equiv.symm_apply_apply]
  exact h.add_mem_edge j

end IsVertexConeBasis

variable [Fintype K]

omit [Fintype K] in
/-- Every vertex of `conv(γ)` is a generator. -/
theorem exists_generator_eq_of_mem_vertices {γ : K → Fin n → ℤ}
    (v : latticePolytopeVertices γ) : ∃ k, γ k = v.val := by
  obtain ⟨k, hk⟩ := latticePolytope_extremePoints_subset_generators γ v.property.2
  exact ⟨k, integerCast_injective hk⟩

/-- The vertex-cone criterion for a whole polytope: if every generator `γ_k` carries a
vertex-cone basis, then `conv(γ)` is a Delzant lattice polytope. -/
theorem latticePolytopeEdgeSmooth_of_vertexCones {γ : K → Fin n → ℤ}
    (B : K → Module.Basis (Fin n) ℤ (Fin n → ℤ)) (hB : ∀ k, IsVertexConeBasis γ (γ k) (B k)) :
    latticePolytopeEdgeSmooth γ := by
  intro v
  obtain ⟨k, hk⟩ := exists_generator_eq_of_mem_vertices v
  rw [← hk]
  exact (hB k).latticePolytopeEdgeSmoothAt

/-! ### The chosen edge bases and the rays -/

variable [Nonempty K] {γ : K → Fin n → ℤ} (hs : latticePolytopeEdgeSmooth γ)

/-- The chart basis `b(v) = originalPolytopeNativeBasis γ hs v` (defined by choice) is a
permutation of any vertex-cone basis `c` at `v`. -/
theorem exists_perm_originalPolytopeNativeBasis_eq (v : latticePolytopeVertices γ)
    (h : IsVertexConeBasis γ v.val c) :
    ∃ τ : Equiv.Perm (Fin n), ∀ j, originalPolytopeNativeBasis γ hs v j = c (τ j) := by
  classical
  set b := originalPolytopeNativeBasis γ hs v
  -- the coordinates of `b_j` in `c` are nonnegative
  have hA : ∀ j k, 0 ≤ c.repr (b j) k := by
    intro j k
    have hx := h.coord_nonneg (vertex_add_basis_mem hs v j) k
    rw [vertexConeCoord_integerCast, add_sub_cancel_left] at hx
    exact_mod_cast hx
  -- the coordinates of `c_k` in `b` are nonnegative
  have hB : ∀ k l, 0 ≤ b.repr (c k) l := by
    intro k l
    have hm : v.val + c k ∈ latticePolytopeIntegerPoints γ := h.add_mem k
    have := intPairing_sub_vertex_nonneg hs v l hm
    rw [add_sub_cancel_left] at this
    rw [basis_repr_eq_intPairing hs v]
    exact this
  -- `ψ_l(b_j) = ∑_k φ_k(b_j) ψ_l(c_k)`
  have hexp : ∀ j l, b.repr (b j) l = ∑ k, c.repr (b j) k * b.repr (c k) l := by
    intro j l
    conv_lhs => rw [← c.sum_repr (b j)]
    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
      smul_eq_mul]
  have hfun : ∀ j, ∃ k, b j = c k := by
    intro j
    obtain ⟨k0, hk0⟩ : ∃ k0, c.repr (b j) k0 ≠ 0 := by
      by_contra hall
      push Not at hall
      apply b.ne_zero j
      rw [c.ext_elem_iff]
      intro k
      rw [hall k, map_zero, Finsupp.zero_apply]
    have hk0pos : 1 ≤ c.repr (b j) k0 := by
      have := hA j k0; omega
    have hnn : ∀ l, ∀ k ∈ Finset.univ, 0 ≤ c.repr (b j) k * b.repr (c k) l :=
      fun l k _ => mul_nonneg (hA j k) (hB k l)
    have hperp : ∀ l, l ≠ j → b.repr (c k0) l = 0 := by
      intro l hl
      have h0 := hexp j l
      rw [b.repr_self, Finsupp.single_apply, if_neg (Ne.symm hl)] at h0
      have := (Finset.sum_eq_zero_iff_of_nonneg (hnn l)).mp h0.symm k0 (Finset.mem_univ k0)
      rcases mul_eq_zero.mp this with h1 | h1
      · exact absurd h1 hk0
      · exact h1
    have hck0 : c k0 = b.repr (c k0) j • b j := by
      conv_lhs => rw [← b.sum_repr (c k0)]
      rw [Finset.sum_eq_single j]
      · intro l _ hl; rw [hperp l hl, zero_smul]
      · intro hj; exact absurd (Finset.mem_univ j) hj
    have hcoef_ne : b.repr (c k0) j ≠ 0 := by
      intro h0
      apply c.ne_zero k0
      rw [hck0, h0, zero_smul]
    have hcoef1 : 1 ≤ b.repr (c k0) j := by have := hB k0 j; omega
    have hle : c.repr (b j) k0 * b.repr (c k0) j ≤ 1 := by
      have h1 := hexp j j
      rw [b.repr_self, Finsupp.single_apply, if_pos rfl] at h1
      rw [h1]
      exact Finset.single_le_sum (hnn j) (Finset.mem_univ k0)
    have hone : b.repr (c k0) j = 1 := by nlinarith
    refine ⟨k0, ?_⟩
    rw [hck0, hone, one_smul]
  choose f hf using hfun
  have hinj : Function.Injective f := by
    intro i j hij
    apply b.injective
    rw [hf i, hf j, hij]
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), fun j => hf j⟩

/-- If `b(v)_j = c_{τ j}` then the ray `u_j(v)` of `σ_v` is the dual vector `u_{τ j}` of `c`. -/
theorem polytopeToricRayGenerator_eq_vertexConeRay (v : latticePolytopeVertices γ)
    {τ : Equiv.Perm (Fin n)} (hτ : ∀ j, originalPolytopeNativeBasis γ hs v j = c (τ j))
    (j : Fin n) : polytopeToricRayGenerator γ hs v j = vertexConeRay c (τ j) := by
  have hb : originalPolytopeNativeBasis γ hs v = c.reindex τ.symm := by
    apply Module.Basis.eq_of_apply_eq
    intro i
    rw [Module.Basis.reindex_apply, Equiv.symm_symm, hτ i]
  funext l
  simp only [polytopeToricRayGenerator, vertexConeRay, hb, Module.Basis.repr_reindex_apply,
    Equiv.symm_symm]

/-- The rays of the maximal cone `σ_v` are the dual basis of a vertex-cone basis at `v`. -/
theorem range_polytopeToricRayGenerator_eq (v : latticePolytopeVertices γ)
    (h : IsVertexConeBasis γ v.val c) :
    range (polytopeToricRayGenerator γ hs v) = range (vertexConeRay c) := by
  obtain ⟨τ, hτ⟩ := exists_perm_originalPolytopeNativeBasis_eq hs v h
  ext u
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨τ j, (polytopeToricRayGenerator_eq_vertexConeRay hs v hτ j).symm⟩
  · rintro ⟨k, rfl⟩
    refine ⟨τ.symm k, ?_⟩
    rw [polytopeToricRayGenerator_eq_vertexConeRay hs v hτ, Equiv.apply_symm_apply]

/-- `Σ(1)` for a polytope all of whose generators carry vertex-cone bases `B k`:
the union of the dual bases of the `B k`. -/
theorem polytopeToricRays_eq_of_vertexCones (B : K → Module.Basis (Fin n) ℤ (Fin n → ℤ))
    (hB : ∀ k, IsVertexConeBasis γ (γ k) (B k)) :
    PolytopeToricRays γ hs = {u | ∃ k j, vertexConeRay (B k) j = u} := by
  ext u
  constructor
  · rintro ⟨v, j, rfl⟩
    obtain ⟨k, hk⟩ := exists_generator_eq_of_mem_vertices v
    have h : IsVertexConeBasis γ v.val (B k) := hk ▸ hB k
    have hr := range_polytopeToricRayGenerator_eq hs v h
    obtain ⟨j', hj'⟩ : polytopeToricRayGenerator γ hs v j ∈ range (vertexConeRay (B k)) := by
      rw [← hr]; exact ⟨j, rfl⟩
    exact ⟨k, j', hj'⟩
  · rintro ⟨k, j, rfl⟩
    let v : latticePolytopeVertices γ := ⟨γ k, (hB k).mem_vertices⟩
    have hr := range_polytopeToricRayGenerator_eq hs v (hB k)
    obtain ⟨j', hj'⟩ : vertexConeRay (B k) j ∈ range (polytopeToricRayGenerator γ hs v) := by
      rw [hr]; exact ⟨j, rfl⟩
    exact ⟨v, j', hj'⟩

/-- The dual vectors of a vertex-cone basis at a vertex are rays of `Σ`. -/
theorem vertexConeRay_mem_polytopeToricRays (v : latticePolytopeVertices γ)
    (h : IsVertexConeBasis γ v.val c) (k : Fin n) :
    vertexConeRay c k ∈ PolytopeToricRays γ hs := by
  have hr := range_polytopeToricRayGenerator_eq hs v h
  obtain ⟨j, hj⟩ : vertexConeRay c k ∈ range (polytopeToricRayGenerator γ hs v) := by
    rw [hr]; exact ⟨k, rfl⟩
  exact ⟨v, j, hj⟩

/-- Computing a Cartier datum: if `⟨m, u⟩ = -a_u` for the dual vectors `u` of a vertex-cone
basis at `v`, then `m = m_{σ_v}`. -/
theorem toricCartierDatum_eq_of_vertexCone (D : ToricDivisor γ hs) (v : latticePolytopeVertices γ)
    (h : IsVertexConeBasis γ v.val c) {m : Fin n → ℤ}
    (hm : ∀ k, intPairing m (vertexConeRay c k) =
      -D ⟨vertexConeRay c k, vertexConeRay_mem_polytopeToricRays hs v h k⟩) :
    toricCartierDatum D v = m := by
  obtain ⟨τ, hτ⟩ := exists_perm_originalPolytopeNativeBasis_eq hs v h
  symm
  apply toricCartierDatum_unique
  intro j
  have hj := polytopeToricRayGenerator_eq_vertexConeRay hs v hτ j
  have hρ : polytopeToricRay γ hs v j =
      ⟨vertexConeRay c (τ j), vertexConeRay_mem_polytopeToricRays hs v h (τ j)⟩ :=
    Subtype.ext hj
  rw [hρ, hj]
  exact hm (τ j)

variable {hs}

/-- Source `eq:Qsigma`: the face `Q_τ = {m ∈ P_D : ⟨m, u_ρ⟩ = -a_ρ ∀ ρ ∈ τ(1)}` of `P_D`
attached to the cone with rays `R = τ(1)` (the same set as in `toricStableBaseLocus_eq_faces`
and `sourceGenericLelong_toricOrbitClosure_eq_zero_tfae`). -/
def toricDivisorFace (D : ToricDivisor γ hs) (R : Set (PolytopeToricRays γ hs)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x ∈ toricDivisorPolytope D | ∀ ρ ∈ R, latticeFunctional ρ.val x = -(D ρ : ℝ)}

theorem toricDivisorFace_empty (D : ToricDivisor γ hs) :
    toricDivisorFace D ∅ = toricDivisorPolytope D := by
  ext x; simp [toricDivisorFace]

end SGPT.Toric
