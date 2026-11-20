import SGPT.Toric.PolytopeToricCorrespondence

/-!
# Torus-invariant divisors on a smooth projective toric manifold

Source `chapter_toric_big.tex`, section `sec:toricsetup2`.  The smooth projective toric
variety `X = X_Σ` is modelled, as in `PolytopeToricVariety`, by the toric manifold of a
Delzant lattice polytope `P = conv(γ)` whose normal fan is `Σ` (every smooth projective
toric variety is of this form, `Σ` being the normal fan of the polytope of any ample
torus-invariant divisor).  The vertex `v` of `P` corresponds to the maximal cone `σ_v` of
`Σ`; with the edge basis `b_1(v), …, b_n(v)` of `P` at `v` (the coordinates of the vertex
chart are the characters `χ^{b_j(v)}`), the cone `σ_v` is spanned by the dual basis

* `u_j(v) = polytopeToricRayGenerator γ hs v j`, `⟨b_i(v), u_j(v)⟩ = δ_{ij}`,

the primitive inward normals of the facets of `P` through `v`.  The set of rays is
`Σ(1) = {u_j(v)}` (`PolytopeToricRays`).

## Main definitions

* `ToricDivisor γ hs`: a torus-invariant integral divisor `D = ∑_ρ a_ρ D_ρ`, i.e. the
  coefficient function `ρ ↦ a_ρ` on `Σ(1)`;
* `toricDivisorPolytope D`: the polytope `P_D = {m : ⟨m, u_ρ⟩ ≥ -a_ρ ∀ ρ}` of `eq:bigPrep`;
* `toricCartierDatum D v`: the Cartier datum `m_σ ∈ M` of `D` on the maximal cone
  `σ = σ_v`, characterised by `⟨m_σ, u_ρ⟩ = -a_ρ` for `ρ ∈ σ(1)`.

## Main results

* `toricCartierDatum_pairing`, `toricCartierDatum_unique`: the Cartier datum on a maximal
  cone exists and is unique;
* `toricDivisorPolytope_sub_cartier_nonneg`: `eq:mmsigpos`;
* `exists_vertex_mem_negCone`: completeness of the normal fan (`N_ℝ = ⋃_v (-σ_v)`);
* `inner_le_latticeFunctional_cartier`: on `-σ_v`, every `m ∈ P_D` satisfies
  `⟨m, x⟩ ≤ ⟨m_v, x⟩` (the support function of `P_D` is below the piecewise linear
  function `x ↦ ⟨m_v, x⟩` on `-σ_v`);
* `isCompact_toricDivisorPolytope`, `convex_toricDivisorPolytope`;
* `singularityLE_support_of_vertexBounds`: a finite convex function with
  `F ≤ ⟨m_v, ·⟩ + C` on every `-σ_v` satisfies `F ≼ Supp_{P_D}`.
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter SGPT.PSH SGPT.Convex SGPT.AlmostSemigroup.Counting
open scoped Topology BigOperators

variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable (γ : K → Fin n → ℤ) (hs : latticePolytopeEdgeSmooth γ)

/-! ### Ray generators -/

/-- The integral pairing `⟨m, u⟩ = ∑_k m_k u_k` of `M = ℤ^n` and `N = ℤ^n`. -/
def intPairing (m u : Fin n → ℤ) : ℤ := ∑ k, m k * u k

/-- The ray generator `u_j(v)` of the maximal cone `σ_v`: the `j`-th vector of the dual
basis of the edge basis `b(v)` of `P` at `v`. -/
def polytopeToricRayGenerator (v : latticePolytopeVertices γ) (j : Fin n) : Fin n → ℤ :=
  fun k => (originalPolytopeNativeBasis γ hs v).repr (Pi.single k 1) j

/-- Duality `⟨b_i(v), u_j(v)⟩ = δ_{ij}`. -/
theorem intPairing_basis_rayGenerator (v : latticePolytopeVertices γ) (i j : Fin n) :
    intPairing (originalPolytopeNativeBasis γ hs v i) (polytopeToricRayGenerator γ hs v j) =
      if i = j then 1 else 0 := by
  set b := originalPolytopeNativeBasis γ hs v
  have hsum : b i = ∑ k, b i k • (Pi.single k (1 : ℤ) : Fin n → ℤ) := by
    conv_lhs => rw [← Finset.univ_sum_single (b i)]
    refine Finset.sum_congr rfl fun k _ => ?_
    ext l
    by_cases hl : l = k
    · subst hl; simp
    · simp [hl]
  have h := congrArg (fun y => b.repr y j) hsum
  simp only [b.repr_self, map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.smul_apply, smul_eq_mul] at h
  rw [Finsupp.single_apply] at h
  unfold intPairing polytopeToricRayGenerator
  rw [← h]

/-- The set `Σ(1)` of ray generators of the normal fan. -/
def PolytopeToricRays : Set (Fin n → ℤ) :=
  {u | ∃ v j, polytopeToricRayGenerator γ hs v j = u}

theorem finite_polytopeToricRays : (PolytopeToricRays γ hs).Finite := by
  have hv := finite_latticePolytopeVertices γ
  let _ := hv.fintype
  have : PolytopeToricRays γ hs =
      range (fun p : latticePolytopeVertices γ × Fin n => polytopeToricRayGenerator γ hs p.1 p.2) := by
    ext u
    simp [PolytopeToricRays, eq_comm]
  rw [this]
  exact finite_range _

/-- The ray `u_j(v) ∈ Σ(1)`. -/
def polytopeToricRay (v : latticePolytopeVertices γ) (j : Fin n) : PolytopeToricRays γ hs :=
  ⟨polytopeToricRayGenerator γ hs v j, v, j, rfl⟩

/-! ### Divisors, polytopes and Cartier data -/

/-- Source `sec:toricsetup2`: a torus-invariant integral divisor `D = ∑_{ρ ∈ Σ(1)} a_ρ D_ρ`,
recorded by its coefficient function `ρ ↦ a_ρ`. -/
abbrev ToricDivisor := PolytopeToricRays γ hs → ℤ

variable {γ hs}

/-- Source `eq:bigPrep`: the polytope `P_D = {m ∈ M_ℝ : ⟨m, u_ρ⟩ ≥ -a_ρ ∀ ρ ∈ Σ(1)}`. -/
def toricDivisorPolytope (D : ToricDivisor γ hs) : Set (EuclideanSpace ℝ (Fin n)) :=
  {m | ∀ ρ : PolytopeToricRays γ hs, -(D ρ : ℝ) ≤ latticeFunctional ρ.val m}

/-- Source `sec:toricsetup2`: the Cartier datum `m_σ ∈ M` of `D` on the maximal cone
`σ = σ_v`, `m_σ = -∑_j a_{u_j(v)} b_j(v)`. -/
def toricCartierDatum (D : ToricDivisor γ hs) (v : latticePolytopeVertices γ) : Fin n → ℤ :=
  ∑ j, (-D (polytopeToricRay γ hs v j)) • originalPolytopeNativeBasis γ hs v j

/-- Source `sec:toricsetup2`: `⟨m_σ, u_ρ⟩ = -a_ρ` for every ray `ρ` of `σ = σ_v`. -/
theorem toricCartierDatum_pairing (D : ToricDivisor γ hs) (v : latticePolytopeVertices γ)
    (j : Fin n) :
    intPairing (toricCartierDatum D v) (polytopeToricRayGenerator γ hs v j) =
      -D (polytopeToricRay γ hs v j) := by
  unfold toricCartierDatum
  have hlin (c : Fin n → ℤ) (x : Fin n → Fin n → ℤ) :
      intPairing (∑ i, c i • x i) (polytopeToricRayGenerator γ hs v j) =
        ∑ i, c i * intPairing (x i) (polytopeToricRayGenerator γ hs v j) := by
    simp only [intPairing, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
  rw [hlin]
  simp only [intPairing_basis_rayGenerator, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

/-- The ray generators of a maximal cone form a basis of `N` (the dual basis of the
edge basis), so the pairings with them determine an element of `M`. -/
theorem eq_of_intPairing_rayGenerator_eq (v : latticePolytopeVertices γ) {m m' : Fin n → ℤ}
    (h : ∀ j, intPairing m (polytopeToricRayGenerator γ hs v j) =
      intPairing m' (polytopeToricRayGenerator γ hs v j)) : m = m' := by
  have hrepr (x : Fin n → ℤ) (j : Fin n) :
      (originalPolytopeNativeBasis γ hs v).repr x j =
        intPairing x (polytopeToricRayGenerator γ hs v j) := by
    conv_lhs => rw [← Finset.univ_sum_single x]
    have hs' : (∑ k, (Pi.single k (x k) : Fin n → ℤ)) =
        ∑ k, x k • (Pi.single k (1 : ℤ) : Fin n → ℤ) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      ext l
      by_cases hl : l = k
      · subst hl; simp
      · simp [hl]
    rw [hs']
    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
      smul_eq_mul, intPairing, polytopeToricRayGenerator]
  apply (originalPolytopeNativeBasis γ hs v).repr.injective
  ext j
  rw [hrepr, hrepr, h j]

/-- Source `sec:toricsetup2`: for an `n`-dimensional cone the Cartier datum is uniquely
determined by `⟨m_σ, u_ρ⟩ = -a_ρ` (`ρ ∈ σ(1)`). -/
theorem toricCartierDatum_unique (D : ToricDivisor γ hs) (v : latticePolytopeVertices γ)
    {m : Fin n → ℤ} (hm : ∀ j, intPairing m (polytopeToricRayGenerator γ hs v j) =
      -D (polytopeToricRay γ hs v j)) : m = toricCartierDatum D v :=
  eq_of_intPairing_rayGenerator_eq v fun j => by rw [hm j, toricCartierDatum_pairing]

/-! ### Real pairings -/

/-- The real vector of an integral vector. -/
def latticeVector (u : Fin n → ℤ) : EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm (integerCast u)

@[simp] theorem latticeVector_apply (u : Fin n → ℤ) (k : Fin n) :
    latticeVector u k = (u k : ℝ) := rfl

theorem latticeFunctional_latticeVector (m u : Fin n → ℤ) :
    latticeFunctional m (latticeVector u) = (intPairing m u : ℝ) := by
  simp [latticeFunctional_apply, intPairing]

theorem inner_latticeVector (u : Fin n → ℤ) (m : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (latticeVector u) m = latticeFunctional u m := by
  simp only [PiLp.inner_apply, latticeVector_apply, latticeFunctional_apply,
    RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

variable (hs) in
/-- The pairing of `⟨m, ·⟩` with `∑_j y_j u_j(v)`. -/
theorem latticeFunctional_logInverse (v : latticePolytopeVertices γ) (m : Fin n → ℤ)
    (y : EuclideanSpace ℝ (Fin n)) :
    latticeFunctional m (latticeBasisLogInverse (originalPolytopeNativeBasis γ hs v) y) =
      ∑ j, y j * (intPairing m (polytopeToricRayGenerator γ hs v j) : ℝ) := by
  simp only [latticeFunctional_apply, latticeBasisLogInverse_apply, intPairing,
    polytopeToricRayGenerator, Int.cast_sum, Int.cast_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

variable (hs) in
/-- The real coordinates `x = ∑_j ⟨b_j(v), x⟩ u_j(v)` of the dual basis. -/
theorem latticeFunctional_eq_sum_basis (v : latticePolytopeVertices γ) (m : Fin n → ℤ)
    (x : EuclideanSpace ℝ (Fin n)) :
    latticeFunctional m x = ∑ j, latticeFunctional (originalPolytopeNativeBasis γ hs v j) x *
      (intPairing m (polytopeToricRayGenerator γ hs v j) : ℝ) := by
  conv_lhs => rw [← latticeBasisLogInverse_logMap (originalPolytopeNativeBasis γ hs v) x]
  rw [latticeFunctional_logInverse hs]
  rfl

variable (hs) in
/-- The same expansion for the real pairing `⟨m, x⟩` with `m ∈ M_ℝ`. -/
theorem inner_eq_sum_basis (v : latticePolytopeVertices γ) (m x : EuclideanSpace ℝ (Fin n)) :
    inner ℝ m x = ∑ j, latticeFunctional (originalPolytopeNativeBasis γ hs v j) x *
      latticeFunctional (polytopeToricRayGenerator γ hs v j) m := by
  have key : ∀ y : EuclideanSpace ℝ (Fin n),
      inner ℝ m (latticeBasisLogInverse (originalPolytopeNativeBasis γ hs v) y) =
        ∑ j, y j * latticeFunctional (polytopeToricRayGenerator γ hs v j) m := by
    intro y
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, latticeFunctional_apply,
      latticeBasisLogInverse_apply, polytopeToricRayGenerator, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  conv_lhs => rw [← latticeBasisLogInverse_logMap (originalPolytopeNativeBasis γ hs v) x]
  rw [key]
  rfl

variable (hs) in
/-- The negative of the maximal cone `σ_v`: `-σ_v = {x : ⟨b_j(v), x⟩ ≤ 0 ∀ j}`. -/
def polytopeToricNegCone (v : latticePolytopeVertices γ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ j, latticeFunctional (originalPolytopeNativeBasis γ hs v j) x ≤ 0}

/-- Source `eq:mmsigpos`: `⟨m - m_σ, u_ρ⟩ ≥ 0` for `m ∈ P_D`, `σ = σ_v`, `ρ ∈ σ(1)`. -/
theorem toricDivisorPolytope_sub_cartier_nonneg (D : ToricDivisor γ hs)
    (v : latticePolytopeVertices γ) {m : EuclideanSpace ℝ (Fin n)}
    (hm : m ∈ toricDivisorPolytope D) (j : Fin n) :
    0 ≤ latticeFunctional (polytopeToricRayGenerator γ hs v j) m -
      latticeFunctional (polytopeToricRayGenerator γ hs v j) (latticeVector (toricCartierDatum D v)) := by
  have h := hm (polytopeToricRay γ hs v j)
  rw [latticeFunctional_latticeVector]
  have hc := toricCartierDatum_pairing D v j
  have hsym : intPairing (polytopeToricRayGenerator γ hs v j) (toricCartierDatum D v) =
      intPairing (toricCartierDatum D v) (polytopeToricRayGenerator γ hs v j) := by
    unfold intPairing; exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [hsym, hc]
  change -(D (polytopeToricRay γ hs v j) : ℝ) ≤
    latticeFunctional (polytopeToricRayGenerator γ hs v j) m at h
  push_cast
  linarith

/-- On `-σ_v`, the linear function `⟨m_v, ·⟩` dominates `⟨m, ·⟩` for every `m ∈ P_D`. -/
theorem inner_le_latticeFunctional_cartier (D : ToricDivisor γ hs)
    (v : latticePolytopeVertices γ) {m x : EuclideanSpace ℝ (Fin n)}
    (hm : m ∈ toricDivisorPolytope D) (hx : x ∈ polytopeToricNegCone hs v) :
    inner ℝ m x ≤ latticeFunctional (toricCartierDatum D v) x := by
  rw [inner_eq_sum_basis hs v, latticeFunctional_eq_sum_basis hs v]
  apply Finset.sum_le_sum
  intro j _
  rw [toricCartierDatum_pairing]
  have h := hm (polytopeToricRay γ hs v j)
  change -(D (polytopeToricRay γ hs v j) : ℝ) ≤
    latticeFunctional (polytopeToricRayGenerator γ hs v j) m at h
  have hxj := hx j
  push_cast
  nlinarith

/-! ### Completeness of the normal fan -/

theorem originalPolytopeFullExponents_mem (i : Fin (originalPolytopeFullIndexSize γ + 1)) :
    originalPolytopeFullExponents γ i ∈ latticePolytopeIntegerPoints γ :=
  ((originalPolytopeFullEnumeration γ) i).property

variable (hs) in
/-- `v + b_j(v)` is a lattice point of `P`. -/
theorem vertex_add_basis_mem (v : latticePolytopeVertices γ) (j : Fin n) :
    integerCast (v.val + originalPolytopeNativeBasis γ hs v j) ∈ latticePolytope γ := by
  have h := (originalPolytopeNativePiChart_spec γ hs v).1 j
  have hmem := originalPolytopeFullExponents_mem (originalPolytopeNativeNeighborIndex γ hs v j)
  rw [← h, add_sub_cancel]
  exact hmem

/-- Completeness of the normal fan: every `x ∈ N_ℝ` lies in some `-σ_v` (take a vertex
maximizing `⟨·, x⟩` on `P`). -/
theorem exists_vertex_mem_negCone (x : EuclideanSpace ℝ (Fin n)) :
    ∃ v : latticePolytopeVertices γ, x ∈ polytopeToricNegCone hs v := by
  let f : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun y => ∑ k, y k * x k
      map_add' := fun y z => by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun c y => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring }
  obtain ⟨v, hv, hmax⟩ := Set.exists_max_image (latticePolytopeVertices γ)
    (fun m => f (integerCast m)) (finite_latticePolytopeVertices γ)
    (nonempty_latticePolytopeVertices γ)
  have hP : ∀ y ∈ latticePolytope γ, f y ≤ f (integerCast v) := by
    intro y hy
    rw [← convexHull_latticePolytopeVertices γ] at hy
    apply convexHull_min (t := {z | f z ≤ f (integerCast v)}) ?_ ?_ hy
    · rintro z ⟨w, hw, rfl⟩
      exact hmax w hw
    · exact convex_halfSpace_le f.isLinear _
  refine ⟨⟨v, hv⟩, fun j => ?_⟩
  have h := hP _ (vertex_add_basis_mem hs ⟨v, hv⟩ j)
  have hcast : integerCast (v + originalPolytopeNativeBasis γ hs ⟨v, hv⟩ j) =
      integerCast v + integerCast (originalPolytopeNativeBasis γ hs ⟨v, hv⟩ j) := by
    ext i; simp [integerCast]
  rw [hcast, map_add] at h
  have h' : f (integerCast (originalPolytopeNativeBasis γ hs ⟨v, hv⟩ j)) ≤ 0 := by linarith
  simpa [f, integerCast, latticeFunctional_apply, mul_comm] using h'

/-! ### Geometry of `P_D` -/

theorem convex_toricDivisorPolytope (D : ToricDivisor γ hs) :
    Convex ℝ (toricDivisorPolytope D) := by
  have : toricDivisorPolytope D =
      ⋂ ρ : PolytopeToricRays γ hs, {m | -(D ρ : ℝ) ≤ latticeFunctional ρ.val m} := by
    ext m; simp [toricDivisorPolytope]
  rw [this]
  exact convex_iInter fun ρ => convex_halfSpace_ge (latticeFunctional ρ.val).isLinear _

theorem isClosed_toricDivisorPolytope (D : ToricDivisor γ hs) :
    IsClosed (toricDivisorPolytope D) := by
  have : toricDivisorPolytope D =
      ⋂ ρ : PolytopeToricRays γ hs, {m | -(D ρ : ℝ) ≤ latticeFunctional ρ.val m} := by
    ext m; simp [toricDivisorPolytope]
  rw [this]
  exact isClosed_iInter fun ρ =>
    isClosed_le continuous_const (LinearMap.continuous_of_finiteDimensional _)

/-- Points of `P_D` are bounded by the Cartier data (completeness of the fan). -/
theorem inner_le_max_cartier (D : ToricDivisor γ hs) {m : EuclideanSpace ℝ (Fin n)}
    (hm : m ∈ toricDivisorPolytope D) (x : EuclideanSpace ℝ (Fin n)) :
    ∃ v : latticePolytopeVertices γ, inner ℝ m x ≤ latticeFunctional (toricCartierDatum D v) x := by
  obtain ⟨v, hv⟩ := exists_vertex_mem_negCone (γ := γ) (hs := hs) x
  exact ⟨v, inner_le_latticeFunctional_cartier D v hm hv⟩

theorem isCompact_toricDivisorPolytope (D : ToricDivisor γ hs) :
    IsCompact (toricDivisorPolytope D) := by
  have hv := finite_latticePolytopeVertices γ
  let _ := hv.fintype
  let C : ℝ := ∑ v : latticePolytopeVertices γ, ∑ k, |((toricCartierDatum D v k : ℤ) : ℝ)|
  have hcoord : ∀ m ∈ toricDivisorPolytope D, ∀ k, |m k| ≤ C := by
    intro m hm k
    have hbound : ∀ v : latticePolytopeVertices γ, |((toricCartierDatum D v k : ℤ) : ℝ)| ≤ C := by
      intro v
      have h1 : |((toricCartierDatum D v k : ℤ) : ℝ)| ≤
          ∑ l, |((toricCartierDatum D v l : ℤ) : ℝ)| :=
        Finset.single_le_sum (f := fun l => |((toricCartierDatum D v l : ℤ) : ℝ)|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ k)
      exact h1.trans (Finset.single_le_sum
        (f := fun v : latticePolytopeVertices γ => ∑ l, |((toricCartierDatum D v l : ℤ) : ℝ)|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ v))
    have hpos := inner_le_max_cartier D hm (EuclideanSpace.single k 1)
    have hneg := inner_le_max_cartier D hm (-EuclideanSpace.single k 1)
    obtain ⟨v, hv⟩ := hpos
    obtain ⟨w, hw⟩ := hneg
    simp only [inner_neg_right, map_neg, EuclideanSpace.inner_single_right, one_mul,
      conj_trivial, latticeFunctional_apply, PiLp.single_apply] at hv hw
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hv hw
    rw [abs_le]
    constructor
    · have := hbound w
      rw [abs_le] at this
      linarith
    · have := hbound v
      rw [abs_le] at this
      linarith
  have hsub : (EuclideanSpace.equiv (Fin n) ℝ) '' toricDivisorPolytope D ⊆
      Set.Icc (fun _ => -C) (fun _ => C) := by
    rintro _ ⟨m, hm, rfl⟩
    refine ⟨fun k => ?_, fun k => ?_⟩
    · exact (abs_le.mp (hcoord m hm k)).1
    · exact (abs_le.mp (hcoord m hm k)).2
  have hcomp : IsCompact ((EuclideanSpace.equiv (Fin n) ℝ) '' toricDivisorPolytope D) :=
    isCompact_Icc.of_isClosed_subset
      ((EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph.isClosedMap _
        (isClosed_toricDivisorPolytope D)) hsub
  have h := hcomp.image (EuclideanSpace.equiv (Fin n) ℝ).symm.continuous
  rwa [← Set.image_comp, show ((EuclideanSpace.equiv (Fin n) ℝ).symm ∘
    (EuclideanSpace.equiv (Fin n) ℝ)) = id from
      funext fun x => (EuclideanSpace.equiv (Fin n) ℝ).symm_apply_apply x, Set.image_id] at h

/-! ### Support growth from vertex-cone bounds -/

/-- The Legendre transform of a finite convex function with `F ≤ ⟨m_v, ·⟩ + C` on every
`-σ_v` is `+∞` off `P_D`. -/
theorem conjugate_eq_top_of_vertexBounds (D : ToricDivisor γ hs)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hb : ∀ v : latticePolytopeVertices γ, ∃ C : ℝ, ∀ x ∈ polytopeToricNegCone hs v,
      f x ≤ latticeFunctional (toricCartierDatum D v) x + C)
    {m : EuclideanSpace ℝ (Fin n)} (hm : m ∉ toricDivisorPolytope D) :
    conjugate (innerₗ (EuclideanSpace ℝ (Fin n))) (fun x => (f x : EReal)) m = ⊤ := by
  simp only [toricDivisorPolytope, mem_ofPred_eq, not_forall, not_le] at hm
  obtain ⟨ρ, hρ⟩ := hm
  obtain ⟨v, j, hvj⟩ := ρ.property
  have hρeq : ρ = polytopeToricRay γ hs v j := Subtype.ext hvj.symm
  subst hρeq
  obtain ⟨C, hC⟩ := hb v
  set u := polytopeToricRayGenerator γ hs v j
  set δ : ℝ := -(D (polytopeToricRay γ hs v j) : ℝ) - latticeFunctional u m
  have hδ : 0 < δ := by
    change latticeFunctional u m < -(D (polytopeToricRay γ hs v j) : ℝ) at hρ
    simp only [δ]; linarith
  have hall : ∀ r : ℝ, (r : EReal) ≤
      conjugate (innerₗ (EuclideanSpace ℝ (Fin n))) (fun x => (f x : EReal)) m := by
    intro r
    obtain ⟨t, ht⟩ : ∃ t : ℝ, 0 ≤ t ∧ r + C ≤ t * δ := by
      refine ⟨max 0 ((r + C) / δ), le_max_left _ _, ?_⟩
      calc r + C = (r + C) / δ * δ := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hδ.le
    let x : EuclideanSpace ℝ (Fin n) := (-t) • latticeVector u
    have hx : x ∈ polytopeToricNegCone hs v := by
      intro i
      simp only [x, map_smul, smul_eq_mul, latticeFunctional_latticeVector, u,
        intPairing_basis_rayGenerator]
      split_ifs <;> simp [ht.1]
    have hfx := hC x hx
    have hlin : latticeFunctional (toricCartierDatum D v) x =
        t * (D (polytopeToricRay γ hs v j) : ℝ) := by
      have hsym : intPairing (toricCartierDatum D v) u = -D (polytopeToricRay γ hs v j) :=
        toricCartierDatum_pairing D v j
      simp only [x, map_smul, smul_eq_mul, latticeFunctional_latticeVector, hsym]
      push_cast; ring
    have hin : (innerₗ (EuclideanSpace ℝ (Fin n))) x m = -t * latticeFunctional u m := by
      simp only [x, innerₗ_apply_apply, inner_smul_left, conj_trivial, inner_latticeVector]
    calc (r : EReal) ≤ (((innerₗ (EuclideanSpace ℝ (Fin n))) x m - f x : ℝ) : EReal) := by
          apply EReal.coe_le_coe_iff.mpr
          rw [hin]
          have : f x ≤ t * (D (polytopeToricRay γ hs v j) : ℝ) + C := hlin ▸ hfx
          simp only [δ] at ht
          nlinarith [ht.2]
      _ = ((innerₗ (EuclideanSpace ℝ (Fin n))) x m : EReal) - (f x : EReal) := EReal.coe_sub _ _
      _ ≤ _ := le_iSup (fun y => ((innerₗ (EuclideanSpace ℝ (Fin n))) y m : EReal) -
          (f y : EReal)) x
  apply EReal.eq_top_iff_forall_lt _ |>.mpr
  intro r
  exact (EReal.coe_lt_coe_iff.mpr (lt_add_one r)).trans_le (hall (r + 1))

/-- A finite convex function with `F ≤ ⟨m_v, ·⟩ + C` on every `-σ_v` has support growth:
`F ≤ Supp_{P_D} + F(0)`. -/
theorem le_support_of_vertexBounds (D : ToricDivisor γ hs)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ConvexOn ℝ univ f)
    (hb : ∀ v : latticePolytopeVertices γ, ∃ C : ℝ, ∀ x ∈ polytopeToricNegCone hs v,
      f x ≤ latticeFunctional (toricCartierDatum D v) x + C)
    (x : EuclideanSpace ℝ (Fin n)) :
    (f x : EReal) ≤ support (innerₗ (EuclideanSpace ℝ (Fin n))).flip (toricDivisorPolytope D) x +
      (f 0 : EReal) := by
  set B := innerₗ (EuclideanSpace ℝ (Fin n))
  set g := conjugate B (fun y => (f y : EReal))
  have hproper := isProper_coe_of_convexOn hf
  have hclosed : IsClosedConvex (fun y => (f y : EReal)) :=
    isClosedConvex_of_isProper_full_domain hproper (by ext y; simp [effectiveDomain])
  have hbi : conjugate B.flip g = fun y => (f y : EReal) :=
    (biconjugate_eq_convexClosure_of_isContPerfPair B hproper.1).trans
      (convexClosure_eq_self_of_isClosedConvex hclosed)
  have hlow : ∀ m, (-(f 0) : EReal) ≤ g m := by
    intro m
    have h := le_iSup (fun y => ((B y m : ℝ) : EReal) - (f y : EReal)) 0
    simpa [g, conjugate, B] using h
  rw [← congrFun hbi x]
  apply iSup_le
  intro m
  by_cases hm : m ∈ toricDivisorPolytope D
  · have h1 : ((B.flip m x : ℝ) : EReal) ≤
        support (innerₗ (EuclideanSpace ℝ (Fin n))).flip (toricDivisorPolytope D) x :=
      le_iSup (fun y : toricDivisorPolytope D => ((B.flip y x : ℝ) : EReal)) ⟨m, hm⟩
    have h2 : ((B.flip m x : ℝ) : EReal) - g m ≤ ((B.flip m x : ℝ) : EReal) + (f 0 : EReal) := by
      have := hlow m
      rw [sub_eq_add_neg]
      apply add_le_add le_rfl
      rw [← EReal.coe_neg] at this
      have h' := EReal.neg_le_neg_iff.mpr this
      simpa using h'
    exact h2.trans (add_le_add h1 le_rfl)
  · have htop : g m = ⊤ := conjugate_eq_top_of_vertexBounds D hb hm
    rw [htop]
    simp

/-- `F ≼ Supp_{P_D}` for a finite convex function bounded by `⟨m_v, ·⟩ + C` on `-σ_v`. -/
theorem singularityLE_support_of_vertexBounds (D : ToricDivisor γ hs)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ConvexOn ℝ univ f)
    (hb : ∀ v : latticePolytopeVertices γ, ∃ C : ℝ, ∀ x ∈ polytopeToricNegCone hs v,
      f x ≤ latticeFunctional (toricCartierDatum D v) x + C) :
    SGPT.PSH.SingularityLE (fun x => (f x : EReal))
      (support (innerₗ (EuclideanSpace ℝ (Fin n))).flip (toricDivisorPolytope D)) :=
  (SGPT.PSH.singularityLE_iff_exists_real _ _).mpr ⟨f 0, le_support_of_vertexBounds D hf hb⟩

/-- Conversely, the support function of `P_D` is bounded by `⟨m_v, ·⟩` on `-σ_v`. -/
theorem support_le_latticeFunctional_cartier (D : ToricDivisor γ hs)
    (v : latticePolytopeVertices γ) {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ polytopeToricNegCone hs v) :
    support (innerₗ (EuclideanSpace ℝ (Fin n))).flip (toricDivisorPolytope D) x ≤
      (latticeFunctional (toricCartierDatum D v) x : EReal) := by
  apply iSup_le
  intro m
  apply EReal.coe_le_coe_iff.mpr
  change inner ℝ x m.val ≤ _
  rw [real_inner_comm]
  exact inner_le_latticeFunctional_cartier D v m.property hx

end SGPT.Toric
