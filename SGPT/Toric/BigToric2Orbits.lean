import SGPT.Toric.BigToric2Sections

/-!
# Torus-invariant prime divisors and orbit closures of `X_Σ`

Source `chapter_toric_big.tex`, section `sec:toricsetup2`: the torus-invariant prime divisors
`D_ρ` (`ρ ∈ Σ(1)`), the cones `τ ∈ Σ` and the toric subvarieties
`V(τ) = ⋂_{ρ ∈ τ(1)} D_ρ` (the orbit closures, recalled after `prop:baseloc`).

In the model `X = PolytopeToricVariety γ hs` (see `BigToricDivisor`), the cones of the
normal fan `Σ` are the faces of the maximal cones `σ_v`, i.e. the cones spanned by subsets of
the rays `u_j(v)` of one vertex `v`; a cone is recorded by its set of rays `τ(1)`
(`IsToricFanCone`).  In the vertex chart `U_v ≅ ℂ^n` with coordinates `z_j = χ^{b_j(v)}`,
the divisor of the ray `u_j(v)` is the coordinate hyperplane `{z_j = 0}`; `D_ρ` is the union of
these hyperplanes over the charts in which `ρ` is a ray (`toricPrimeDivisor`).

## Main results

* `intPairing_sub_vertex_nonneg`: `⟨m - v, u_j(v)⟩ ≥ 0` for every lattice point `m` of `P`;
* `exists_rayGenerator_eq_of_pairing_eq_zero`: if the vertex `v` lies on the facet of `P` with
  inner normal `u_j(w)`, then `u_j(w)` is a ray of `σ_v` (vertex–facet incidence);
* `mem_toricPrimeDivisor_iff`: in every vertex chart `U_v`, `D_ρ ∩ U_v = ∅` unless `ρ` is a ray
  of `σ_v`, and `D_{u_i(v)} ∩ U_v = {z_i = 0}` (orbit–cone correspondence in the charts);
* `isToricFanCone_orbitRays`, `mem_toricOrbitClosure_iff`: the rays `ρ` with `p ∈ D_ρ` span a
  cone `τ_p` of `Σ`, and `p ∈ V(τ) ↔ τ(1) ⊆ τ_p(1)`;
* `isClosed_toricPrimeDivisor`, `isClosed_toricOrbitClosure`, `toricOrbitClosure_action`:
  `D_ρ` and `V(τ)` are closed and `T(ℂ)`-invariant;
* `hasAnalyticChartEquations_toricOrbitClosure`: `V(τ)` is cut out by holomorphic equations in
  every chart.
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter SGPT.AlmostSemigroup.Counting
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.PSH.VariableComplexAtlas
open scoped Topology BigOperators

variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-! ### Pairings -/

theorem intPairing_add (a b u : Fin n → ℤ) :
    intPairing (a + b) u = intPairing a u + intPairing b u := by
  simp only [intPairing, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem intPairing_add_right (m u u' : Fin n → ℤ) :
    intPairing m (u + u') = intPairing m u + intPairing m u' := by
  simp only [intPairing, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem intPairing_smul (c : ℤ) (a u : Fin n → ℤ) :
    intPairing (c • a) u = c * intPairing a u := by
  simp only [intPairing, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem intPairing_smul_right (c : ℤ) (m u : Fin n → ℤ) :
    intPairing m (c • u) = c * intPairing m u := by
  simp only [intPairing, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem intPairing_sum_right {ι : Type*} (S : Finset ι) (m : Fin n → ℤ) (u : ι → Fin n → ℤ) :
    intPairing m (∑ i ∈ S, u i) = ∑ i ∈ S, intPairing m (u i) := by
  simp only [intPairing, Finset.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem intPairing_sum_left {ι : Type*} (S : Finset ι) (m : ι → Fin n → ℤ) (u : Fin n → ℤ) :
    intPairing (∑ i ∈ S, m i) u = ∑ i ∈ S, intPairing (m i) u := by
  rw [intPairing_comm, intPairing_sum_right]
  exact Finset.sum_congr rfl fun i _ => intPairing_comm _ _

variable (hs) in
/-- `x = ∑_i ⟨x, u_i(v)⟩ b_i(v)` paired with `u`: `⟨x, u⟩ = ∑_i ⟨x, u_i(v)⟩ ⟨b_i(v), u⟩`. -/
theorem intPairing_expand (v : latticePolytopeVertices γ) (x u : Fin n → ℤ) :
    intPairing x u = ∑ i, intPairing x (polytopeToricRayGenerator γ hs v i) *
      intPairing (originalPolytopeNativeBasis γ hs v i) u := by
  conv_lhs => rw [← (originalPolytopeNativeBasis γ hs v).sum_repr x]
  rw [intPairing_sum_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [intPairing_smul, basis_repr_eq_intPairing hs v x i]

variable (hs) in
/-- Dual expansion in `N`: `y = ∑_k ⟨b_k(v), y⟩ u_k(v)`. -/
theorem eq_sum_intPairing_basis_smul_rayGenerator (v : latticePolytopeVertices γ)
    (y : Fin n → ℤ) :
    y = ∑ k, intPairing (originalPolytopeNativeBasis γ hs v k) y •
      polytopeToricRayGenerator γ hs v k := by
  funext l
  have h := intPairing_expand hs v (Pi.single l 1) y
  have hl : intPairing (Pi.single l (1 : ℤ)) y = y l := by
    simp [intPairing, Pi.single_apply]
  have hl' : ∀ k, intPairing (Pi.single l (1 : ℤ)) (polytopeToricRayGenerator γ hs v k) =
      polytopeToricRayGenerator γ hs v k l := by
    intro k; simp [intPairing, Pi.single_apply]
  rw [hl] at h
  rw [h, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hl', Pi.smul_apply, smul_eq_mul, mul_comm]

/-! ### The vertex cones of `P` -/

variable (hs) in
/-- Every point `x` of `P` satisfies `⟨x - v, u_j(v)⟩ ≥ 0` (the cone of `P` at the vertex `v`
is spanned by its edges). -/
theorem pairing_rayGenerator_nonneg_of_mem (v : latticePolytopeVertices γ) (j : Fin n)
    {x : Fin n → ℝ} (hx : x ∈ latticePolytope γ) :
    (intPairing v.val (polytopeToricRayGenerator γ hs v j) : ℝ) ≤
      ∑ k, x k * (polytopeToricRayGenerator γ hs v j k : ℝ) := by
  set u := polytopeToricRayGenerator γ hs v j
  let f : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun y => ∑ k, y k * (u k : ℝ)
      map_add' := fun y z => by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun c y => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring }
  rw [← convexHull_latticePolytopeVertices γ] at hx
  apply convexHull_min (t := {y | (intPairing v.val u : ℝ) ≤ f y}) ?_
    (convex_halfSpace_ge f.isLinear _) hx
  rintro _ ⟨w, hw, rfl⟩
  have h := vertex_pairing_rayGenerator_nonneg γ hs v ⟨w, hw⟩ j
  rw [intPairing_sub] at h
  change (intPairing v.val u : ℝ) ≤ ∑ k, (w k : ℝ) * (u k : ℝ)
  have : (∑ k, (w k : ℝ) * (u k : ℝ)) = (intPairing w u : ℝ) := by
    simp [intPairing]
  rw [this]
  exact_mod_cast (show intPairing v.val u ≤ intPairing w u by linarith)

variable (hs) in
/-- `⟨m - v, u_j(v)⟩ ≥ 0` for every lattice point `m` of `P`. -/
theorem intPairing_sub_vertex_nonneg (v : latticePolytopeVertices γ) (j : Fin n)
    {m : Fin n → ℤ} (hm : m ∈ latticePolytopeIntegerPoints γ) :
    0 ≤ intPairing (m - v.val) (polytopeToricRayGenerator γ hs v j) := by
  have h := pairing_rayGenerator_nonneg_of_mem hs v j hm
  have : (∑ k, integerCast m k * (polytopeToricRayGenerator γ hs v j k : ℝ)) =
      (intPairing m (polytopeToricRayGenerator γ hs v j) : ℝ) := by
    simp [intPairing, integerCast]
  rw [this] at h
  rw [intPairing_sub]
  have h' : intPairing v.val (polytopeToricRayGenerator γ hs v j) ≤
      intPairing m (polytopeToricRayGenerator γ hs v j) := by exact_mod_cast h
  linarith

variable (hs) in
theorem vertex_add_basis_mem_integerPoints (v : latticePolytopeVertices γ) (j : Fin n) :
    v.val + originalPolytopeNativeBasis γ hs v j ∈ latticePolytopeIntegerPoints γ :=
  vertex_add_basis_mem hs v j

/-- Vertex–facet incidence: if the vertex `v` lies on the facet `{⟨·, u_j(w)⟩ = ⟨w, u_j(w)⟩}` of
`P`, then `u_j(w)` is one of the rays `u_i(v)` of the maximal cone `σ_v`. -/
theorem exists_rayGenerator_eq_of_pairing_eq_zero {v w : latticePolytopeVertices γ} {j : Fin n}
    (h : intPairing (v.val - w.val) (polytopeToricRayGenerator γ hs w j) = 0) :
    ∃ i, polytopeToricRayGenerator γ hs v i = polytopeToricRayGenerator γ hs w j := by
  set ρ := polytopeToricRayGenerator γ hs w j
  set c : Fin n → ℤ := fun i => intPairing (originalPolytopeNativeBasis γ hs v i) ρ
  have hc : ∀ i, 0 ≤ c i := by
    intro i
    have h1 := intPairing_sub_vertex_nonneg hs w j (vertex_add_basis_mem_integerPoints hs v i)
    have h2 : v.val + originalPolytopeNativeBasis γ hs v i - w.val =
        (v.val - w.val) + originalPolytopeNativeBasis γ hs v i := by abel
    rw [h2, intPairing_add, h, zero_add] at h1
    exact h1
  -- the pairings of the edges `b_k(w)` (`k ≠ j`) with the rays `u_i(v)`, `c_i > 0`, vanish
  have hperp : ∀ i, 0 < c i → ∀ k, k ≠ j →
      intPairing (originalPolytopeNativeBasis γ hs w k) (polytopeToricRayGenerator γ hs v i) = 0 := by
    intro i hci k hk
    have hzero_of : ∀ x : Fin n → ℤ, x ∈ latticePolytopeIntegerPoints γ →
        intPairing (x - w.val) ρ = 0 →
        intPairing (x - v.val) (polytopeToricRayGenerator γ hs v i) = 0 := by
      intro x hx hxρ
      have hexp := intPairing_expand hs v (x - v.val) ρ
      have hval : intPairing (x - v.val) ρ = 0 := by
        have : x - v.val = (x - w.val) - (v.val - w.val) := by abel
        rw [this, intPairing_sub, hxρ, h, sub_zero]
      rw [hval] at hexp
      have hnn : ∀ l ∈ Finset.univ, 0 ≤ intPairing (x - v.val) (polytopeToricRayGenerator γ hs v l) *
          intPairing (originalPolytopeNativeBasis γ hs v l) ρ :=
        fun l _ => mul_nonneg (intPairing_sub_vertex_nonneg hs v l hx) (hc l)
      have hall := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hexp.symm i (Finset.mem_univ i)
      rcases mul_eq_zero.mp hall with h0 | h0
      · exact h0
      · exact absurd h0 (ne_of_gt hci)
    have hk1 := hzero_of _ (vertex_add_basis_mem_integerPoints hs w k) (by
      rw [add_sub_cancel_left]
      rw [intPairing_basis_rayGenerator, if_neg hk])
    have hw1 := hzero_of _ (w.property.1) (by rw [sub_self]; simp [intPairing])
    have : originalPolytopeNativeBasis γ hs w k =
        (w.val + originalPolytopeNativeBasis γ hs w k - v.val) - (w.val - v.val) := by abel
    rw [this, intPairing_sub, hk1, hw1, sub_zero]
  -- some `c_i` is positive
  have hpos : ∃ i, 0 < c i := by
    by_contra hcon
    push Not at hcon
    have hzero : ∀ i, c i = 0 := fun i => le_antisymm (hcon i) (hc i)
    have hρ := eq_sum_intPairing_basis_smul_rayGenerator hs v ρ
    have : ρ = 0 := by
      rw [hρ]
      simp only [c] at hzero
      simp [hzero]
    have h1 := intPairing_basis_rayGenerator γ hs w j j
    rw [if_pos rfl] at h1
    change intPairing _ ρ = 1 at h1
    rw [this] at h1
    simp [intPairing] at h1
  obtain ⟨i, hci⟩ := hpos
  refine ⟨i, ?_⟩
  -- `u_i(v) = t ρ` with `t = ⟨b_j(w), u_i(v)⟩`
  set t := intPairing (originalPolytopeNativeBasis γ hs w j) (polytopeToricRayGenerator γ hs v i)
  have hut : polytopeToricRayGenerator γ hs v i = t • ρ := by
    conv_lhs => rw [eq_sum_intPairing_basis_smul_rayGenerator hs w
      (polytopeToricRayGenerator γ hs v i)]
    rw [Finset.sum_eq_single j]
    · intro k _ hk
      rw [hperp i hci k hk, zero_smul]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  have h1 : intPairing (originalPolytopeNativeBasis γ hs v i)
      (polytopeToricRayGenerator γ hs v i) = 1 := by
    rw [intPairing_basis_rayGenerator, if_pos rfl]
  rw [hut, intPairing_smul_right] at h1
  have ht : t = 1 := by
    have hc1 : (1 : ℤ) ≤ c i := hci
    have : t * c i = 1 := h1
    nlinarith
  rw [hut, ht, one_smul]

/-! ### Homogeneous coordinates in a vertex chart -/

variable (hs) in
/-- The homogeneous coordinate `X_m` of the point `z` of the chart `U_w` is the monomial
`∏_k z_k^{⟨m - w, u_k(w)⟩}`. -/
theorem nativeVector_apply (w : latticePolytopeVertices γ) (z : Fin n → ℂ)
    (i : Fin (originalPolytopeFullIndexSize γ + 1)) :
    originalPolytopeNativeVector γ hs w z i = ∏ k, z k ^
      (intPairing (originalPolytopeFullExponents γ i - w.val)
        (polytopeToricRayGenerator γ hs w k)).toNat := by
  change ∏ k : Fin n, z k ^ monomialVertexExponent (originalPolytopeNativeBasis γ hs w)
    (originalPolytopeFullExponents γ) (originalPolytopeNativeVertexIndex γ w) i k = _
  refine Finset.prod_congr rfl fun k _ => ?_
  unfold monomialVertexExponent
  have hv := latticePolytopeExponentFamily_vertexIndex γ (originalPolytopeFullEnumeration γ) w
  change originalPolytopeFullExponents γ (originalPolytopeNativeVertexIndex γ w) = w.val at hv
  rw [hv, basis_repr_eq_intPairing hs w]

theorem fullExponents_vertexIndex (v : latticePolytopeVertices γ) :
    originalPolytopeFullExponents γ (originalPolytopeNativeVertexIndex γ v) = v.val :=
  latticePolytopeExponentFamily_vertexIndex γ (originalPolytopeFullEnumeration γ) v

variable (hs) in
theorem fullExponents_neighborIndex (v : latticePolytopeVertices γ) (j : Fin n) :
    originalPolytopeFullExponents γ (originalPolytopeNativeNeighborIndex γ hs v j) =
      v.val + originalPolytopeNativeBasis γ hs v j := by
  have h := (originalPolytopeNativePiChart_spec γ hs v).1 j
  rw [← h]; abel

variable (hs) in
/-- The vertex chart at `w` reads the point `(PiChart w)⁻¹ z` of `U_v` as the ratio of
homogeneous coordinates. -/
theorem piChart_symm_mem_source_iff (v w : latticePolytopeVertices γ) (z : Fin n → ℂ) :
    (originalPolytopeNativePiChart γ hs w).symm z ∈ (originalPolytopeNativePiChart γ hs v).source ↔
      originalPolytopeNativeVector γ hs w z (originalPolytopeNativeVertexIndex γ v) ≠ 0 :=
  originalPolytopeNativePiChart_mem_source_iff γ hs v _ _
    (originalPolytopeNativeVector_ne_zero γ hs w z) (originalPolytopeNativePiChart_symm_val γ hs w z)

variable (hs) in
theorem piChart_piChart_symm (v w : latticePolytopeVertices γ) (z : Fin n → ℂ)
    (hz : (originalPolytopeNativePiChart γ hs w).symm z ∈ (originalPolytopeNativePiChart γ hs v).source)
    (i : Fin n) :
    originalPolytopeNativePiChart γ hs v ((originalPolytopeNativePiChart γ hs w).symm z) i =
      originalPolytopeNativeVector γ hs w z (originalPolytopeNativeNeighborIndex γ hs v i) /
        originalPolytopeNativeVector γ hs w z (originalPolytopeNativeVertexIndex γ v) :=
  ((originalPolytopeNativePiChart_spec γ hs v).2.2.2.2.2 _ hz _
    (originalPolytopeNativeVector_ne_zero γ hs w z) (originalPolytopeNativePiChart_symm_val γ hs w z)).2 i

variable (hs) in
/-- Orbit–cone correspondence in the charts: if `p ∈ U_v ∩ U_w` lies on the coordinate
hyperplane `{z_j = 0}` of `U_w`, then `u_j(w)` is a ray `u_i(v)` of `σ_v` and `p` lies on the
coordinate hyperplane `{z_i = 0}` of `U_v`. -/
theorem exists_chart_coord_eq_zero {v w : latticePolytopeVertices γ} {p : PolytopeToricVariety γ hs}
    (hv : p ∈ (originalPolytopeNativeModelChart γ hs v).source)
    (hw : p ∈ (originalPolytopeNativeModelChart γ hs w).source) {j : Fin n}
    (hj : originalPolytopeNativeModelChart γ hs w p j = 0) :
    ∃ i, polytopeToricRayGenerator γ hs v i = polytopeToricRayGenerator γ hs w j ∧
      originalPolytopeNativeModelChart γ hs v p i = 0 := by
  rw [originalPolytopeNativeModelChart_source] at hv hw
  set z := originalPolytopeNativePiChart γ hs w p
  have hpz : (originalPolytopeNativePiChart γ hs w).symm z = p :=
    (originalPolytopeNativePiChart γ hs w).left_inv hw
  have hzj : z j = 0 := hj
  have hsrc : (originalPolytopeNativePiChart γ hs w).symm z ∈
      (originalPolytopeNativePiChart γ hs v).source := by rw [hpz]; exact hv
  have hX := (piChart_symm_mem_source_iff hs v w z).mp hsrc
  rw [nativeVector_apply hs w, fullExponents_vertexIndex] at hX
  have hfac := (Finset.prod_ne_zero_iff.mp hX) j (Finset.mem_univ j)
  rw [hzj] at hfac
  have hexp0 : (intPairing (v.val - w.val) (polytopeToricRayGenerator γ hs w j)).toNat = 0 := by
    by_contra hne
    exact hfac (zero_pow hne)
  have hnn := intPairing_sub_vertex_nonneg hs w j v.property.1
  have hpair : intPairing (v.val - w.val) (polytopeToricRayGenerator γ hs w j) = 0 := by
    have := Int.toNat_eq_zero.mp hexp0
    omega
  obtain ⟨i, hi⟩ := exists_rayGenerator_eq_of_pairing_eq_zero hpair
  refine ⟨i, hi, ?_⟩
  change originalPolytopeNativePiChart γ hs v p i = 0
  rw [← hpz, piChart_piChart_symm hs v w z hsrc i]
  apply div_eq_zero_iff.mpr
  left
  rw [nativeVector_apply hs w, fullExponents_neighborIndex hs]
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  rw [hzj]
  apply zero_pow
  have : v.val + originalPolytopeNativeBasis γ hs v i - w.val =
      (v.val - w.val) + originalPolytopeNativeBasis γ hs v i := by abel
  rw [this, intPairing_add, hpair, zero_add, ← hi, intPairing_basis_rayGenerator, if_pos rfl]
  decide

/-! ### Toric divisors and orbit closures -/

/-- Source `sec:toricsetup2`: the torus-invariant prime divisor `D_ρ` of the ray `ρ ∈ Σ(1)`:
in each vertex chart `U_v` in which `ρ = u_j(v)` is a ray of `σ_v`, the coordinate hyperplane
`{z_j = 0}`. -/
def toricPrimeDivisor (ρ : PolytopeToricRays γ hs) : Set (PolytopeToricVariety γ hs) :=
  {p | ∃ v j, polytopeToricRayGenerator γ hs v j = ρ.val ∧
    p ∈ (originalPolytopeNativeModelChart γ hs v).source ∧
    originalPolytopeNativeModelChart γ hs v p j = 0}

/-- In the chart `U_v`, `D_ρ ∩ U_v` is the hyperplane `{z_i = 0}` if `ρ = u_i(v)`, and empty
if `ρ` is not a ray of `σ_v`. -/
theorem mem_toricPrimeDivisor_iff {v : latticePolytopeVertices γ} {p : PolytopeToricVariety γ hs}
    (hv : p ∈ (originalPolytopeNativeModelChart γ hs v).source) (ρ : PolytopeToricRays γ hs) :
    p ∈ toricPrimeDivisor ρ ↔ ∃ i, polytopeToricRayGenerator γ hs v i = ρ.val ∧
      originalPolytopeNativeModelChart γ hs v p i = 0 := by
  constructor
  · rintro ⟨w, j, hwj, hw, hj⟩
    obtain ⟨i, hi, hzi⟩ := exists_chart_coord_eq_zero hs hv hw hj
    exact ⟨i, hi.trans hwj, hzi⟩
  · rintro ⟨i, hi, hzi⟩
    exact ⟨v, i, hi, hv, hzi⟩

/-- Source `sec:toricsetup2`: a cone `τ ∈ Σ`, recorded by its set of rays `τ(1)`: a face of a
maximal cone `σ_v`, spanned by the rays `u_j(v)`, `j ∈ J`. -/
def IsToricFanCone (R : Set (PolytopeToricRays γ hs)) : Prop :=
  ∃ (v : latticePolytopeVertices γ) (J : Set (Fin n)), R = polytopeToricRay γ hs v '' J

/-- Source `prop:baseloc` (after the statement): the toric subvariety
`V(τ) = ⋂_{ρ ∈ τ(1)} D_ρ` of the cone with rays `R = τ(1)`. -/
def toricOrbitClosure (R : Set (PolytopeToricRays γ hs)) : Set (PolytopeToricVariety γ hs) :=
  ⋂ ρ ∈ R, toricPrimeDivisor ρ

/-- The rays `ρ` with `p ∈ D_ρ`: the cone `τ_p` of the orbit of `p`. -/
def orbitRays (p : PolytopeToricVariety γ hs) : Set (PolytopeToricRays γ hs) :=
  {ρ | p ∈ toricPrimeDivisor ρ}

theorem mem_toricOrbitClosure_iff {R : Set (PolytopeToricRays γ hs)}
    {p : PolytopeToricVariety γ hs} : p ∈ toricOrbitClosure R ↔ R ⊆ orbitRays p := by
  simp only [toricOrbitClosure, mem_iInter]
  rfl

/-- In a chart `U_v ∋ p`, the rays of the orbit cone `τ_p` are the rays `u_j(v)` of the
vanishing coordinates of `p`; in particular `τ_p` is a cone of `Σ`. -/
theorem orbitRays_eq {v : latticePolytopeVertices γ} {p : PolytopeToricVariety γ hs}
    (hv : p ∈ (originalPolytopeNativeModelChart γ hs v).source) :
    orbitRays p = polytopeToricRay γ hs v '' {j | originalPolytopeNativeModelChart γ hs v p j = 0} := by
  ext ρ
  simp only [orbitRays, mem_ofPred_eq, mem_image]
  rw [mem_toricPrimeDivisor_iff hv]
  constructor
  · rintro ⟨i, hi, hzi⟩
    exact ⟨i, hzi, Subtype.ext hi⟩
  · rintro ⟨i, hzi, rfl⟩
    exact ⟨i, rfl, hzi⟩

theorem isToricFanCone_orbitRays (p : PolytopeToricVariety γ hs) : IsToricFanCone (orbitRays p) := by
  obtain ⟨v, hv⟩ := originalPolytopeNativeModelChart_cover γ hs p
  exact ⟨v, _, orbitRays_eq hv⟩

theorem mem_toricOrbitClosure_orbitRays (p : PolytopeToricVariety γ hs) :
    p ∈ toricOrbitClosure (orbitRays p) := mem_toricOrbitClosure_iff.mpr le_rfl

/-- `V(τ) ∩ U_v` is the coordinate subspace `{z_i = 0 : u_i(v) ∈ τ(1)}`, empty unless
`τ(1) ⊆ σ_v(1)`. -/
theorem mem_toricOrbitClosure_iff_chart {R : Set (PolytopeToricRays γ hs)}
    {v : latticePolytopeVertices γ} {p : PolytopeToricVariety γ hs}
    (hv : p ∈ (originalPolytopeNativeModelChart γ hs v).source) :
    p ∈ toricOrbitClosure R ↔ ∀ ρ ∈ R, ∃ i, polytopeToricRayGenerator γ hs v i = ρ.val ∧
      originalPolytopeNativeModelChart γ hs v p i = 0 := by
  simp only [toricOrbitClosure, mem_iInter]
  exact forall₂_congr fun ρ _ => mem_toricPrimeDivisor_iff hv ρ

/-! ### Topology and torus invariance -/

theorem isClosed_toricPrimeDivisor (ρ : PolytopeToricRays γ hs) :
    IsClosed (toricPrimeDivisor ρ) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro p hp
  obtain ⟨v, hv⟩ := originalPolytopeNativeModelChart_cover γ hs p
  set e := originalPolytopeNativeModelChart γ hs v
  let U : Set (PolytopeToricVariety γ hs) := e.source ∩ e ⁻¹'
    {z | ∀ i, polytopeToricRayGenerator γ hs v i = ρ.val → z i ≠ 0}
  refine ⟨U, ?_, ?_, ?_⟩
  · rintro q ⟨hq, hqz⟩ hqD
    obtain ⟨i, hi, hzi⟩ := (mem_toricPrimeDivisor_iff hq ρ).mp hqD
    exact hqz i hi hzi
  · apply e.isOpen_inter_preimage
    have : {z : ComplexModel n | ∀ i, polytopeToricRayGenerator γ hs v i = ρ.val → z i ≠ 0} =
        ⋂ i ∈ {i | polytopeToricRayGenerator γ hs v i = ρ.val}, {z | z i ≠ 0} := by
      ext z; simp
    rw [this]
    exact (Set.toFinite _).isOpen_biInter fun i _ =>
      isOpen_ne_fun (EuclideanSpace.proj (𝕜 := ℂ) i).continuous continuous_const
  · refine ⟨hv, fun i hi hzi => hp ?_⟩
    exact (mem_toricPrimeDivisor_iff hv ρ).mpr ⟨i, hi, hzi⟩

theorem isClosed_toricOrbitClosure (R : Set (PolytopeToricRays γ hs)) :
    IsClosed (toricOrbitClosure R) :=
  isClosed_biInter fun ρ _ => isClosed_toricPrimeDivisor ρ

/-- `D_ρ` is invariant under the torus `T(ℂ)`. -/
theorem polytopeToricAction_mem_toricPrimeDivisor_iff (a : Fin n → ℂˣ)
    (ρ : PolytopeToricRays γ hs) (p : PolytopeToricVariety γ hs) :
    polytopeToricAction γ hs a p ∈ toricPrimeDivisor ρ ↔ p ∈ toricPrimeDivisor ρ := by
  obtain ⟨v, hv⟩ := originalPolytopeNativeModelChart_cover γ hs p
  have hva : polytopeToricAction γ hs a p ∈ (originalPolytopeNativeModelChart γ hs v).source := by
    rw [originalPolytopeNativeModelChart_source] at hv ⊢
    exact (originalPolytopeNativeAction_mem_chart_source_iff γ hs v a p).mpr hv
  rw [mem_toricPrimeDivisor_iff hva, mem_toricPrimeDivisor_iff hv]
  have hcoord : ∀ i, originalPolytopeNativeModelChart γ hs v (polytopeToricAction γ hs a p) i =
      (latticeCharacter (originalPolytopeNativeBasis γ hs v i) a : ℂ) *
        originalPolytopeNativeModelChart γ hs v p i := by
    intro i
    rw [originalPolytopeNativeModelChart_source] at hv
    exact originalPolytopeNativePiChart_action γ hs v a p hv i
  simp only [hcoord, mul_eq_zero, Units.ne_zero, false_or]

/-- Source `prop:baseloc`: `V(τ)` is torus invariant. -/
theorem polytopeToricAction_mem_toricOrbitClosure_iff (a : Fin n → ℂˣ)
    (R : Set (PolytopeToricRays γ hs)) (p : PolytopeToricVariety γ hs) :
    polytopeToricAction γ hs a p ∈ toricOrbitClosure R ↔ p ∈ toricOrbitClosure R := by
  simp only [toricOrbitClosure, mem_iInter]
  exact forall₂_congr fun ρ _ => polytopeToricAction_mem_toricPrimeDivisor_iff a ρ p

/-- Source `prop:baseloc`: `V(τ)` is an analytic subset: in every chart of `X` it is cut out by
coordinate functions. -/
theorem hasAnalyticChartEquations_toricOrbitClosure (R : Set (PolytopeToricRays γ hs)) :
    (ofFixedModel n (PolytopeToricVariety γ hs)).HasAnalyticChartEquations
      (toricOrbitClosure R) := by
  classical
  intro e z _
  obtain ⟨v, hve⟩ := originalPolytopeNativeComplexChart_exhaustive γ hs e
  subst hve
  have hsrc : ∀ y : ComplexModel n, (originalPolytopeNativeModelChart γ hs v).symm y ∈
      (originalPolytopeNativeModelChart γ hs v).source := fun y =>
    (originalPolytopeNativeModelChart γ hs v).map_target
      (by rw [originalPolytopeNativeModelChart_target]; exact mem_univ y)
  have hright : ∀ y : ComplexModel n, originalPolytopeNativeModelChart γ hs v
      ((originalPolytopeNativeModelChart γ hs v).symm y) = y := fun y =>
    (originalPolytopeNativeModelChart γ hs v).right_inv
      (by rw [originalPolytopeNativeModelChart_target]; exact mem_univ y)
  refine ⟨univ, isOpen_univ, mem_univ z, (polytopeToric_chart_target γ hs _).symm.subset, ?_⟩
  by_cases hR : ∀ ρ ∈ R, ∃ i, polytopeToricRayGenerator γ hs v i = ρ.val
  · -- the coordinates `z_i` with `u_i(v) ∈ R`
    refine ⟨n, fun i y => if polytopeToricRay γ hs v i ∈ R then y i else 0, ?_, ?_⟩
    · intro i
      by_cases hi : polytopeToricRay γ hs v i ∈ R
      · simp only [hi, if_true]
        exact (EuclideanSpace.proj (𝕜 := ℂ) i).differentiable.differentiableOn
      · simp only [hi, if_false]
        exact differentiableOn_const 0
    · intro y _
      refine Iff.trans (mem_toricOrbitClosure_iff_chart
        (p := (originalPolytopeNativeModelChart γ hs v).symm y) (hsrc y)) ?_
      constructor
      · intro h i
        dsimp only
        split_ifs with hi
        · obtain ⟨i', hi', hzi'⟩ := h _ hi
          have : i' = i := by
            by_contra hne
            have h1 := intPairing_basis_rayGenerator γ hs v i' i'
            have h2 := intPairing_basis_rayGenerator γ hs v i' i
            rw [if_pos rfl] at h1
            rw [if_neg hne] at h2
            change intPairing _ (polytopeToricRayGenerator γ hs v i) = 0 at h2
            rw [show polytopeToricRayGenerator γ hs v i = polytopeToricRayGenerator γ hs v i'
              from hi'.symm] at h2
            omega
          rw [← this]
          have hy := hright y
          rw [hy] at hzi'
          exact hzi'
        · rfl
      · intro h ρ hρ
        obtain ⟨i, hi⟩ := hR ρ hρ
        refine ⟨i, hi, ?_⟩
        have hiR : polytopeToricRay γ hs v i ∈ R := by
          have : polytopeToricRay γ hs v i = ρ := Subtype.ext hi
          rw [this]; exact hρ
        have := h i
        dsimp only at this
        rw [if_pos hiR] at this
        have hy := hright y
        rw [hy]
        exact this
  · -- `V(τ) ∩ U_v = ∅`
    push Not at hR
    obtain ⟨ρ, hρ, hnot⟩ := hR
    refine ⟨1, fun _ _ => 1, fun _ => differentiableOn_const 1, ?_⟩
    intro y _
    refine Iff.trans (mem_toricOrbitClosure_iff_chart
      (p := (originalPolytopeNativeModelChart γ hs v).symm y) (hsrc y)) ?_
    simp only [one_ne_zero, forall_const, iff_false, not_forall]
    exact ⟨ρ, hρ, fun ⟨i, hi, _⟩ => hnot i hi⟩

end SGPT.Toric
