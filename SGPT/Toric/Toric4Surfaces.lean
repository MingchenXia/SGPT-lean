import SGPT.Toric.Toric4Simplex

/-!
# The toric surfaces `Bl₀ℙ²` and `𝔽₂` as Delzant polytope models

Source `chapter_toric_big.tex`, `ex:P2bl1pt`, `ex:F1big_non_nef`, `ex:F2_non_lattice_polytope`.

The model `X_P = PolytopeToricVariety γ hs` is the toric manifold of the normal fan of a Delzant
polytope `P`.  We realise the fans of the examples as normal fans of explicit polytopes:

* `blowupGenerator`: `P' = conv{(1,0), (2,0), (0,2), (0,1)}`, with normal fan
  `Σ(1) = {(1,0), (0,1), (-1,-1), (1,1)}`: the fan of `ℙ²` with the cone `σ_1 = cone(e_1, e_2)`
  subdivided by the ray `σ_7 = ℝ_{≥0}(1,1)` (the fan of `Bl₀ℙ²`, figure `fig:polyP2b1p`);
* `hirzebruchGenerator`: `P'' = conv{(0,0), (1,0), (3,1), (0,1)}`, with normal fan
  `Σ(1) = {(1,0), (0,1), (-1,2), (0,-1)}` (the fan of the Hirzebruch surface `𝔽₂`).

For each we prove the Delzant property with explicit vertex-cone bases (`lattice2Basis`),
compute `Σ(1)` and the rays of every maximal cone, and compute the polytopes `P_D`, Cartier
data and faces `Q_σ` of the divisors of the examples.
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set SGPT.AlmostSemigroup.Counting
open scoped BigOperators

/-! ### Lattice bases of `ℤ²` -/

/-- The coordinates in the lattice basis `c_0 = (a, b)`, `c_1 = (c, d)` of `ℤ²` (`ad - bc = 1`). -/
def lattice2Equiv (a b c d : ℤ) (hdet : a * d - b * c = 1) : (Fin 2 → ℤ) ≃ₗ[ℤ] (Fin 2 → ℤ) where
  toFun x := ![d * x 0 - c * x 1, -b * x 0 + a * x 1]
  invFun y := ![a * y 0 + c * y 1, b * y 0 + d * y 1]
  map_add' x y := by funext k; fin_cases k <;> simp <;> ring
  map_smul' r x := by funext k; fin_cases k <;> simp <;> ring
  left_inv x := by
    funext k; fin_cases k
    · simp; linear_combination x 0 * hdet
    · simp; linear_combination x 1 * hdet
  right_inv y := by
    funext k; fin_cases k
    · simp; linear_combination y 0 * hdet
    · simp; linear_combination y 1 * hdet

/-- The lattice basis `c_0 = (a, b)`, `c_1 = (c, d)` of `ℤ²` (`ad - bc = 1`). -/
def lattice2Basis (a b c d : ℤ) (hdet : a * d - b * c = 1) : Module.Basis (Fin 2) ℤ (Fin 2 → ℤ) :=
  Module.Basis.ofEquivFun (lattice2Equiv a b c d hdet)

section Lattice2
variable (a b c d : ℤ) (hdet : a * d - b * c = 1)

theorem lattice2Basis_repr (x : Fin 2 → ℤ) (k : Fin 2) :
    (lattice2Basis a b c d hdet).repr x k = ![d * x 0 - c * x 1, -b * x 0 + a * x 1] k := by
  simp only [lattice2Basis, Module.Basis.ofEquivFun_repr_apply]
  rfl

theorem lattice2Basis_apply_zero : lattice2Basis a b c d hdet 0 = ![a, b] := by
  classical
  simp only [lattice2Basis, Module.Basis.coe_ofEquivFun]
  funext k; fin_cases k <;> simp [lattice2Equiv]

theorem lattice2Basis_apply_one : lattice2Basis a b c d hdet 1 = ![c, d] := by
  classical
  simp only [lattice2Basis, Module.Basis.coe_ofEquivFun]
  funext k; fin_cases k <;> simp [lattice2Equiv]

/-- The dual basis of `(a, b), (c, d)`: `u_0 = (d, -c)`, `u_1 = (-b, a)`. -/
theorem vertexConeRay_lattice2Basis_zero : vertexConeRay (lattice2Basis a b c d hdet) 0 = ![d, -c] := by
  funext l; fin_cases l <;> simp [vertexConeRay, lattice2Basis_repr]

theorem vertexConeRay_lattice2Basis_one : vertexConeRay (lattice2Basis a b c d hdet) 1 = ![-b, a] := by
  funext l; fin_cases l <;> simp [vertexConeRay, lattice2Basis_repr]

end Lattice2

/-- A lattice point on the segment between two generators lies in `conv(γ)`. -/
theorem integerCast_mem_latticePolytope_of_combo {n : ℕ} {K : Type*} (γ : K → Fin n → ℤ)
    (i j : K) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (x : Fin n → ℤ)
    (hx : integerCast x = (1 - θ) • integerCast (γ i) + θ • integerCast (γ j)) :
    integerCast x ∈ latticePolytope γ := by
  rw [hx]
  exact convex_latticePolytope γ (latticePolytope_generator_mem γ i)
    (latticePolytope_generator_mem γ j) (by linarith) hθ0 (by ring)

/-- Rewriting `∀ ρ ∈ Σ(1)` through an explicit description of `Σ(1)`. -/
theorem forall_polytopeToricRays_iff {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
    {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ} {S : Set (Fin n → ℤ)}
    (hS : PolytopeToricRays γ hs = S) (p : PolytopeToricRays γ hs → Prop) :
    (∀ ρ, p ρ) ↔ ∀ u (hu : u ∈ S), p ⟨u, hS ▸ hu⟩ := by
  constructor
  · intro h u hu; exact h _
  · intro h ρ
    have := h ρ.val (hS ▸ ρ.property)
    exact this

/-- In dimension two the maximal cone `σ_v` has the two rays of the dual basis. -/
theorem range_vertexCone_two {K : Type*} [Fintype K] [Nonempty K] {γ : K → Fin 2 → ℤ}
    (hs : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    {c : Module.Basis (Fin 2) ℤ (Fin 2 → ℤ)} (h : IsVertexConeBasis γ v.val c) :
    range (polytopeToricRayGenerator γ hs v) = {vertexConeRay c 0, vertexConeRay c 1} := by
  rw [range_polytopeToricRayGenerator_eq hs v h]
  ext u
  simp only [mem_range, mem_insert_iff, mem_singleton_iff, Fin.exists_fin_two]
  constructor
  · rintro (h0 | h1)
    · exact Or.inl h0.symm
    · exact Or.inr h1.symm
  · rintro (h0 | h1)
    · exact Or.inl h0.symm
    · exact Or.inr h1.symm

/-! ### Divisors given by coefficient functions -/

section Generic
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K] {γ : K → Fin n → ℤ}
  {hs : latticePolytopeEdgeSmooth γ}

/-- The divisor `∑_ρ a(u_ρ) D_ρ` of a coefficient function `a` on `N`. -/
def toricDivisorOfCoeff (hs : latticePolytopeEdgeSmooth γ) (a : (Fin n → ℤ) → ℤ) :
    ToricDivisor γ hs :=
  fun ρ => a ρ.val

/-- The rays of `Σ` lying in a set `T ⊆ N` (the rays `τ(1)` of a cone `τ`). -/
def toricRaysIn (hs : latticePolytopeEdgeSmooth γ) (T : Set (Fin n → ℤ)) :
    Set (PolytopeToricRays γ hs) :=
  {ρ | ρ.val ∈ T}

theorem toricDivisorPolytope_ofCoeff {S : Set (Fin n → ℤ)} (hS : PolytopeToricRays γ hs = S)
    (a : (Fin n → ℤ) → ℤ) :
    toricDivisorPolytope (toricDivisorOfCoeff hs a) =
      {m | ∀ u ∈ S, -(a u : ℝ) ≤ latticeFunctional u m} := by
  ext m
  simp only [toricDivisorPolytope, toricDivisorOfCoeff, mem_ofPred_eq]
  constructor
  · intro h u hu; exact h ⟨u, hS ▸ hu⟩
  · intro h ρ; exact h ρ.val (hS ▸ ρ.property)

theorem toricDivisorFace_ofCoeff (a : (Fin n → ℤ) → ℤ) (T : Set (Fin n → ℤ))
    (hT : T ⊆ PolytopeToricRays γ hs) :
    toricDivisorFace (toricDivisorOfCoeff hs a) (toricRaysIn hs T) =
      {m ∈ toricDivisorPolytope (toricDivisorOfCoeff hs a) |
        ∀ u ∈ T, latticeFunctional u m = -(a u : ℝ)} := by
  ext m
  simp only [toricDivisorFace, toricRaysIn, toricDivisorOfCoeff, mem_ofPred_eq]
  constructor
  · rintro ⟨hm, h⟩; exact ⟨hm, fun u hu => h ⟨u, hT hu⟩ hu⟩
  · rintro ⟨hm, h⟩; exact ⟨hm, fun ρ hρ => h ρ.val hρ⟩

theorem toricCartierDatum_ofCoeff (a : (Fin n → ℤ) → ℤ) (v : latticePolytopeVertices γ)
    {c : Module.Basis (Fin n) ℤ (Fin n → ℤ)} (h : IsVertexConeBasis γ v.val c) {m : Fin n → ℤ}
    (hm : ∀ k, intPairing m (vertexConeRay c k) = -a (vertexConeRay c k)) :
    toricCartierDatum (toricDivisorOfCoeff hs a) v = m :=
  toricCartierDatum_eq_of_vertexCone hs _ v h fun k => hm k

end Generic

theorem eq_latticeVector_iff_two (m : EuclideanSpace ℝ (Fin 2)) (u : Fin 2 → ℤ) :
    m = latticeVector u ↔ m 0 = u 0 ∧ m 1 = u 1 := by
  constructor
  · rintro rfl; simp
  · rintro ⟨h0, h1⟩
    ext i; fin_cases i <;> simp [h0, h1]

theorem latticeFunctional_two (u : Fin 2 → ℤ) (m : EuclideanSpace ℝ (Fin 2)) :
    latticeFunctional u m = u 0 * m 0 + u 1 * m 1 := by
  simp [latticeFunctional_apply, Fin.sum_univ_two]

/-! ### The polytope `P'` of `Bl₀ℙ²` -/

/-- The vertices `(1,0), (2,0), (0,2), (0,1)` of `P'`. -/
def blowupGenerator : Fin 4 → Fin 2 → ℤ := ![![1, 0], ![2, 0], ![0, 2], ![0, 1]]

/-- Vertex-cone bases of `P'`: at `(1,0)`: `(1,0), (-1,1)`; at `(2,0)`: `(-1,1), (-1,0)`;
at `(0,2)`: `(0,-1), (1,-1)`; at `(0,1)`: `(1,-1), (0,1)`. -/
def blowupBasis : Fin 4 → Module.Basis (Fin 2) ℤ (Fin 2 → ℤ) :=
  ![lattice2Basis 1 0 (-1) 1 (by norm_num), lattice2Basis (-1) 1 (-1) 0 (by norm_num),
    lattice2Basis 0 (-1) 1 (-1) (by norm_num), lattice2Basis 1 (-1) 0 1 (by norm_num)]

theorem blowup_isVertexConeBasis (k : Fin 4) :
    IsVertexConeBasis blowupGenerator (blowupGenerator k) (blowupBasis k) := by
  have hgen := latticePolytope_generator_mem blowupGenerator
  have h11 : integerCast (![1, 1] : Fin 2 → ℤ) ∈ latticePolytope blowupGenerator :=
    integerCast_mem_latticePolytope_of_combo blowupGenerator 1 2 (1 / 2) (by norm_num)
      (by norm_num) _ (by funext i; fin_cases i <;> (simp [integerCast, blowupGenerator]; try norm_num))
  refine ⟨hgen k, fun j => ?_, fun k' j => ?_⟩
  · fin_cases k <;> fin_cases j <;>
      simp only [blowupBasis, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val,
        lattice2Basis_apply_zero, lattice2Basis_apply_one]
    · convert hgen 1 using 2; funext i; fin_cases i <;> simp [blowupGenerator]
    · convert hgen 3 using 2; funext i; fin_cases i <;> simp [blowupGenerator]
    · convert h11 using 2; funext i; fin_cases i <;> simp [blowupGenerator]
    · convert hgen 0 using 2; funext i; fin_cases i <;> simp [blowupGenerator]
    · convert hgen 3 using 2; funext i; fin_cases i <;> simp [blowupGenerator]
    · convert h11 using 2; funext i; fin_cases i <;> simp [blowupGenerator]
    · convert hgen 0 using 2; funext i; fin_cases i <;> simp [blowupGenerator]
    · convert hgen 2 using 2; funext i; fin_cases i <;> simp [blowupGenerator]
  · fin_cases k <;> fin_cases k' <;> fin_cases j <;>
      simp [blowupBasis, lattice2Basis_repr, blowupGenerator]

/-- Source `ex:P2bl1pt`: `P'` is a Delzant lattice polytope. -/
theorem blowup_edgeSmooth : latticePolytopeEdgeSmooth blowupGenerator :=
  latticePolytopeEdgeSmooth_of_vertexCones blowupBasis blowup_isVertexConeBasis

/-- The vertex `γ_k` of `P'`. -/
def blowupVertex (k : Fin 4) : latticePolytopeVertices blowupGenerator :=
  ⟨blowupGenerator k, (blowup_isVertexConeBasis k).mem_vertices⟩

variable (hs : latticePolytopeEdgeSmooth blowupGenerator)

/-- The rays `u_ρ`: `σ_4 = (-1,-1)`, `σ_5 = (1,0)`, `σ_6 = (0,1)`, `σ_7 = (1,1)`. -/
def blowupRay4 : Fin 2 → ℤ := ![-1, -1]
def blowupRay5 : Fin 2 → ℤ := ![1, 0]
def blowupRay6 : Fin 2 → ℤ := ![0, 1]
def blowupRay7 : Fin 2 → ℤ := ![1, 1]

/-- The rays of the maximal cones of `P'` at its vertices, in the order of `blowupBasis`. -/
theorem blowup_vertexConeRays :
    (vertexConeRay (blowupBasis 0) 0 = blowupRay7 ∧ vertexConeRay (blowupBasis 0) 1 = blowupRay6) ∧
    (vertexConeRay (blowupBasis 1) 0 = blowupRay6 ∧ vertexConeRay (blowupBasis 1) 1 = blowupRay4) ∧
    (vertexConeRay (blowupBasis 2) 0 = blowupRay4 ∧ vertexConeRay (blowupBasis 2) 1 = blowupRay5) ∧
    (vertexConeRay (blowupBasis 3) 0 = blowupRay5 ∧ vertexConeRay (blowupBasis 3) 1 = blowupRay7) := by
  simp only [blowupBasis, Matrix.cons_val, vertexConeRay_lattice2Basis_zero,
    vertexConeRay_lattice2Basis_one, blowupRay4, blowupRay5, blowupRay6, blowupRay7]
  norm_num

/-- Source `ex:P2bl1pt`: `Σ(1) = {σ_4, σ_5, σ_6, σ_7}`. -/
theorem blowup_rays :
    PolytopeToricRays blowupGenerator hs = {blowupRay4, blowupRay5, blowupRay6, blowupRay7} := by
  rw [polytopeToricRays_eq_of_vertexCones hs blowupBasis blowup_isVertexConeBasis]
  obtain ⟨⟨h00, h01⟩, ⟨h10, h11⟩, ⟨h20, h21⟩, ⟨h30, h31⟩⟩ := blowup_vertexConeRays
  ext u
  simp only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨k, j, rfl⟩
    fin_cases k <;> fin_cases j <;> simp [h00, h01, h10, h11, h20, h21, h30, h31]
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨1, 1, h11⟩
    · exact ⟨2, 1, h21⟩
    · exact ⟨0, 1, h01⟩
    · exact ⟨0, 0, h00⟩

/-- Source `ex:P2bl1pt`: the maximal cones.  `σ_1'' = cone(σ_7, σ_6)` (vertex `(1,0)`),
`σ_2 = cone(σ_6, σ_4)` (vertex `(2,0)`), `σ_3 = cone(σ_4, σ_5)` (vertex `(0,2)`) and
`σ_1' = cone(σ_5, σ_7)` (vertex `(0,1)`): the cones of `ℙ²` with `σ_1` subdivided by `σ_7`. -/
theorem blowup_maximalCones :
    range (polytopeToricRayGenerator blowupGenerator hs (blowupVertex 0)) = {blowupRay7, blowupRay6} ∧
    range (polytopeToricRayGenerator blowupGenerator hs (blowupVertex 1)) = {blowupRay6, blowupRay4} ∧
    range (polytopeToricRayGenerator blowupGenerator hs (blowupVertex 2)) = {blowupRay4, blowupRay5} ∧
    range (polytopeToricRayGenerator blowupGenerator hs (blowupVertex 3)) = {blowupRay5, blowupRay7} := by
  obtain ⟨⟨h00, h01⟩, ⟨h10, h11⟩, ⟨h20, h21⟩, ⟨h30, h31⟩⟩ := blowup_vertexConeRays
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [range_vertexCone_two hs (blowupVertex 0) (blowup_isVertexConeBasis 0), h00, h01]
  · rw [range_vertexCone_two hs (blowupVertex 1) (blowup_isVertexConeBasis 1), h10, h11]
  · rw [range_vertexCone_two hs (blowupVertex 2) (blowup_isVertexConeBasis 2), h20, h21]
  · rw [range_vertexCone_two hs (blowupVertex 3) (blowup_isVertexConeBasis 3), h30, h31]

/-! ### The divisors of `ex:P2bl1pt` and `ex:F1big_non_nef` -/

/-- Source `ex:P2bl1pt`: `D = D_{σ_4}` on `Bl₀ℙ²`. -/
def blowupHyperplaneDivisor : ToricDivisor blowupGenerator hs :=
  toricDivisorOfCoeff hs fun u => if u = blowupRay4 then 1 else 0

/-- Source `ex:F1big_non_nef`: `D = 2D_{σ_4} + D_{σ_7} = 2H + E`. -/
def blowupNonNefDivisor : ToricDivisor blowupGenerator hs :=
  toricDivisorOfCoeff hs fun u => if u = blowupRay4 then 2 else if u = blowupRay7 then 1 else 0

theorem blowup_toricDivisorPolytope (a : (Fin 2 → ℤ) → ℤ) :
    toricDivisorPolytope (toricDivisorOfCoeff hs a) =
      {m | -(a blowupRay4 : ℝ) ≤ -m 0 - m 1 ∧ -(a blowupRay5 : ℝ) ≤ m 0 ∧
        -(a blowupRay6 : ℝ) ≤ m 1 ∧ -(a blowupRay7 : ℝ) ≤ m 0 + m 1} := by
  rw [toricDivisorPolytope_ofCoeff (blowup_rays hs)]
  ext m
  simp only [mem_insert_iff, mem_singleton_iff, forall_eq_or_imp, forall_eq, mem_ofPred_eq,
    latticeFunctional_two, blowupRay4, blowupRay5, blowupRay6, blowupRay7,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor
  · rintro ⟨h4, h5, h6, h7⟩
    push_cast at h4 h5 h6 h7
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨h4, h5, h6, h7⟩
    refine ⟨?_, ?_, ?_, ?_⟩ <;> push_cast <;> linarith

/-- Source `ex:P2bl1pt`: `P_D` is the triangle of `ex:P2`. -/
theorem toricDivisorPolytope_blowupHyperplaneDivisor :
    toricDivisorPolytope (blowupHyperplaneDivisor hs) =
      {m | 0 ≤ m 0 ∧ 0 ≤ m 1 ∧ m 0 + m 1 ≤ 1} := by
  rw [blowupHyperplaneDivisor, blowup_toricDivisorPolytope]
  ext m
  simp only [mem_ofPred_eq, blowupRay4, blowupRay5, blowupRay6, blowupRay7]
  norm_num
  constructor
  · rintro ⟨h4, h5, h6, -⟩; exact ⟨h5, h6, by linarith⟩
  · rintro ⟨h5, h6, h4⟩; exact ⟨by linarith, h5, h6, by linarith⟩

/-- Source `ex:F1big_non_nef`: the four inequalities defining `P_D` for `D = 2H + E`, i.e.
`m_1 ≥ 0, m_2 ≥ 0, m_1 + m_2 ≤ 2, m_1 + m_2 ≥ -1`. -/
theorem toricDivisorPolytope_blowupNonNefDivisor_ineq :
    toricDivisorPolytope (blowupNonNefDivisor hs) =
      {m | 0 ≤ m 0 ∧ 0 ≤ m 1 ∧ m 0 + m 1 ≤ 2 ∧ -1 ≤ m 0 + m 1} := by
  rw [blowupNonNefDivisor, blowup_toricDivisorPolytope]
  ext m
  simp only [mem_ofPred_eq, blowupRay4, blowupRay5, blowupRay6, blowupRay7]
  norm_num
  constructor
  · rintro ⟨h4, h5, h6, h7⟩; exact ⟨h5, h6, by linarith, by linarith⟩
  · rintro ⟨h5, h6, h4, h7⟩; exact ⟨by linarith, h5, h6, by linarith⟩

/-- Source `ex:F1big_non_nef`: the inequality of the exceptional ray `σ_7` is redundant, and
`P_D = {m_1 ≥ 0, m_2 ≥ 0, m_1 + m_2 ≤ 2}`. -/
theorem toricDivisorPolytope_blowupNonNefDivisor :
    toricDivisorPolytope (blowupNonNefDivisor hs) =
      {m | 0 ≤ m 0 ∧ 0 ≤ m 1 ∧ m 0 + m 1 ≤ 2} ∧
    ∀ m : EuclideanSpace ℝ (Fin 2), 0 ≤ m 0 → 0 ≤ m 1 → -1 ≤ m 0 + m 1 := by
  refine ⟨?_, fun m h0 h1 => by linarith⟩
  rw [toricDivisorPolytope_blowupNonNefDivisor_ineq]
  ext m
  simp only [mem_ofPred_eq]
  constructor
  · rintro ⟨h0, h1, h2, -⟩; exact ⟨h0, h1, h2⟩
  · rintro ⟨h0, h1, h2⟩; exact ⟨h0, h1, h2, by linarith⟩

/-- Source `ex:P2bl1pt`: the Cartier data of `D = D_{σ_4}`:
`m_{σ_1''} = m_{σ_1'} = (0,0)`, `m_{σ_2} = (1,0)`, `m_{σ_3} = (0,1)`. -/
theorem toricCartierDatum_blowupHyperplaneDivisor :
    toricCartierDatum (blowupHyperplaneDivisor hs) (blowupVertex 0) = ![0, 0] ∧
    toricCartierDatum (blowupHyperplaneDivisor hs) (blowupVertex 3) = ![0, 0] ∧
    toricCartierDatum (blowupHyperplaneDivisor hs) (blowupVertex 1) = ![1, 0] ∧
    toricCartierDatum (blowupHyperplaneDivisor hs) (blowupVertex 2) = ![0, 1] := by
  obtain ⟨⟨h00, h01⟩, ⟨h10, h11⟩, ⟨h20, h21⟩, ⟨h30, h31⟩⟩ := blowup_vertexConeRays
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply toricCartierDatum_ofCoeff _ (blowupVertex 0) (blowup_isVertexConeBasis 0)
    intro k
    fin_cases k <;> simp [h00, h01, blowupRay4, blowupRay6, blowupRay7, intPairing]
  · apply toricCartierDatum_ofCoeff _ (blowupVertex 3) (blowup_isVertexConeBasis 3)
    intro k
    fin_cases k <;> simp [h30, h31, blowupRay4, blowupRay5, blowupRay7, intPairing]
  · apply toricCartierDatum_ofCoeff _ (blowupVertex 1) (blowup_isVertexConeBasis 1)
    intro k
    fin_cases k <;> simp [h10, h11, blowupRay4, blowupRay6, intPairing]
  · apply toricCartierDatum_ofCoeff _ (blowupVertex 2) (blowup_isVertexConeBasis 2)
    intro k
    fin_cases k <;> simp [h20, h21, blowupRay4, blowupRay5, intPairing]

/-- The rays `τ(1)` of the cones of `ex:P2bl1pt` lie in `Σ(1)`. -/
theorem blowup_raysIn_subset {T : Set (Fin 2 → ℤ)}
    (hT : T ⊆ {blowupRay4, blowupRay5, blowupRay6, blowupRay7}) :
    T ⊆ PolytopeToricRays blowupGenerator hs := by
  rw [blowup_rays hs]; exact hT

/-- Source `ex:P2bl1pt`: the faces `Q_σ` of `P_D`, `D = D_{σ_4}`:
`Q_{σ_1'} = Q_{σ_1''} = Q_{σ_7} = {(0,0)}`, `Q_{σ_2} = {(1,0)}`, `Q_{σ_3} = {(0,1)}`,
`Q_{σ_4} = {m ≥ 0, m_1 + m_2 = 1}`, `Q_{σ_5} = {0} × [0,1]`, `Q_{σ_6} = [0,1] × {0}`,
`Q_{σ_0} = P_D`. -/
theorem toricDivisorFace_blowupHyperplaneDivisor :
    toricDivisorFace (blowupHyperplaneDivisor hs) (toricRaysIn hs {blowupRay5, blowupRay7}) =
      {latticeVector ![0, 0]} ∧
    toricDivisorFace (blowupHyperplaneDivisor hs) (toricRaysIn hs {blowupRay7, blowupRay6}) =
      {latticeVector ![0, 0]} ∧
    toricDivisorFace (blowupHyperplaneDivisor hs) (toricRaysIn hs {blowupRay7}) =
      {latticeVector ![0, 0]} ∧
    toricDivisorFace (blowupHyperplaneDivisor hs) (toricRaysIn hs {blowupRay6, blowupRay4}) =
      {latticeVector ![1, 0]} ∧
    toricDivisorFace (blowupHyperplaneDivisor hs) (toricRaysIn hs {blowupRay4, blowupRay5}) =
      {latticeVector ![0, 1]} ∧
    toricDivisorFace (blowupHyperplaneDivisor hs) (toricRaysIn hs {blowupRay4}) =
      {m | 0 ≤ m 0 ∧ 0 ≤ m 1 ∧ m 0 + m 1 = 1} ∧
    toricDivisorFace (blowupHyperplaneDivisor hs) (toricRaysIn hs {blowupRay5}) =
      {m | m 0 = 0 ∧ 0 ≤ m 1 ∧ m 1 ≤ 1} ∧
    toricDivisorFace (blowupHyperplaneDivisor hs) (toricRaysIn hs {blowupRay6}) =
      {m | 0 ≤ m 0 ∧ m 0 ≤ 1 ∧ m 1 = 0} ∧
    toricDivisorFace (blowupHyperplaneDivisor hs) ∅ = toricDivisorPolytope (blowupHyperplaneDivisor hs) := by
  have hsub : ∀ {T : Set (Fin 2 → ℤ)}, T ⊆ {blowupRay4, blowupRay5, blowupRay6, blowupRay7} →
      toricDivisorFace (blowupHyperplaneDivisor hs) (toricRaysIn hs T) =
        {m ∈ {m : EuclideanSpace ℝ (Fin 2) | 0 ≤ m 0 ∧ 0 ≤ m 1 ∧ m 0 + m 1 ≤ 1} |
          ∀ u ∈ T, latticeFunctional u m = -((if u = blowupRay4 then 1 else 0 : ℤ) : ℝ)} := by
    intro T hT
    rw [blowupHyperplaneDivisor, toricDivisorFace_ofCoeff _ _ (blowup_raysIn_subset hs hT),
      ← blowupHyperplaneDivisor, toricDivisorPolytope_blowupHyperplaneDivisor]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, toricDivisorFace_empty _⟩
  all_goals
    rw [hsub (by intro u hu; simp only [mem_insert_iff, mem_singleton_iff] at hu ⊢; tauto)]
    ext m
    simp only [mem_insert_iff, mem_singleton_iff, forall_eq_or_imp, forall_eq, mem_ofPred_eq,
      latticeFunctional_two, eq_latticeVector_iff_two, blowupRay4, blowupRay5, blowupRay6,
      blowupRay7]
    norm_num
  all_goals first
    | (constructor
       · rintro ⟨⟨h0, h1, h2⟩, h3, h4⟩; constructor <;> linarith
       · rintro ⟨h0, h1⟩; refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩ <;> linarith)
    | (constructor
       · rintro ⟨⟨h0, h1, h2⟩, h3⟩; constructor <;> linarith
       · rintro ⟨h0, h1⟩; refine ⟨⟨?_, ?_, ?_⟩, ?_⟩ <;> linarith)
    | (constructor
       · rintro ⟨⟨h0, h1, h2⟩, h3⟩; refine ⟨?_, ?_, ?_⟩ <;> linarith
       · rintro ⟨h0, h1, h2⟩; refine ⟨⟨?_, ?_, ?_⟩, ?_⟩ <;> linarith)

/-! ### The polytope `P''` of `𝔽₂` -/

/-- The vertices `(0,0), (1,0), (3,1), (0,1)` of `P''`. -/
def hirzebruchGenerator : Fin 4 → Fin 2 → ℤ := ![![0, 0], ![1, 0], ![3, 1], ![0, 1]]

/-- Vertex-cone bases of `P''`: at `(0,0)`: `(1,0), (0,1)`; at `(1,0)`: `(2,1), (-1,0)`;
at `(3,1)`: `(-1,0), (-2,-1)`; at `(0,1)`: `(0,-1), (1,0)`. -/
def hirzebruchBasis : Fin 4 → Module.Basis (Fin 2) ℤ (Fin 2 → ℤ) :=
  ![lattice2Basis 1 0 0 1 (by norm_num), lattice2Basis 2 1 (-1) 0 (by norm_num),
    lattice2Basis (-1) 0 (-2) (-1) (by norm_num), lattice2Basis 0 (-1) 1 0 (by norm_num)]

theorem hirzebruch_isVertexConeBasis (k : Fin 4) :
    IsVertexConeBasis hirzebruchGenerator (hirzebruchGenerator k) (hirzebruchBasis k) := by
  have hgen := latticePolytope_generator_mem hirzebruchGenerator
  have h21 : integerCast (![2, 1] : Fin 2 → ℤ) ∈ latticePolytope hirzebruchGenerator :=
    integerCast_mem_latticePolytope_of_combo hirzebruchGenerator 3 2 (2 / 3) (by norm_num)
      (by norm_num) _ (by funext i; fin_cases i <;> simp [integerCast, hirzebruchGenerator])
  have h11 : integerCast (![1, 1] : Fin 2 → ℤ) ∈ latticePolytope hirzebruchGenerator :=
    integerCast_mem_latticePolytope_of_combo hirzebruchGenerator 3 2 (1 / 3) (by norm_num)
      (by norm_num) _ (by funext i; fin_cases i <;> simp [integerCast, hirzebruchGenerator])
  refine ⟨hgen k, fun j => ?_, fun k' j => ?_⟩
  · fin_cases k <;> fin_cases j <;>
      simp only [hirzebruchBasis, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val,
        lattice2Basis_apply_zero, lattice2Basis_apply_one]
    · convert hgen 1 using 2; funext i; fin_cases i <;> simp [hirzebruchGenerator]
    · convert hgen 3 using 2; funext i; fin_cases i <;> simp [hirzebruchGenerator]
    · convert hgen 2 using 2; funext i; fin_cases i <;> simp [hirzebruchGenerator]
    · convert hgen 0 using 2; funext i; fin_cases i <;> simp [hirzebruchGenerator]
    · convert h21 using 2; funext i; fin_cases i <;> simp [hirzebruchGenerator]
    · convert hgen 1 using 2; funext i; fin_cases i <;> simp [hirzebruchGenerator]
    · convert hgen 0 using 2; funext i; fin_cases i <;> simp [hirzebruchGenerator]
    · convert h11 using 2; funext i; fin_cases i <;> simp [hirzebruchGenerator]
  · fin_cases k <;> fin_cases k' <;> fin_cases j <;>
      simp [hirzebruchBasis, lattice2Basis_repr, hirzebruchGenerator]

/-- Source `ex:F2_non_lattice_polytope`: `P''` is a Delzant lattice polytope. -/
theorem hirzebruch_edgeSmooth : latticePolytopeEdgeSmooth hirzebruchGenerator :=
  latticePolytopeEdgeSmooth_of_vertexCones hirzebruchBasis hirzebruch_isVertexConeBasis

/-- The vertex `γ_k` of `P''`. -/
def hirzebruchVertex (k : Fin 4) : latticePolytopeVertices hirzebruchGenerator :=
  ⟨hirzebruchGenerator k, (hirzebruch_isVertexConeBasis k).mem_vertices⟩

/-- The rays `u_{ρ_1} = (1,0)`, `u_{ρ_2} = (0,1)`, `u_{ρ_3} = (-1,2)`, `u_{ρ_4} = (0,-1)`. -/
def hirzebruchRay1 : Fin 2 → ℤ := ![1, 0]
def hirzebruchRay2 : Fin 2 → ℤ := ![0, 1]
def hirzebruchRay3 : Fin 2 → ℤ := ![-1, 2]
def hirzebruchRay4 : Fin 2 → ℤ := ![0, -1]

theorem hirzebruch_vertexConeRays :
    (vertexConeRay (hirzebruchBasis 0) 0 = hirzebruchRay1 ∧
      vertexConeRay (hirzebruchBasis 0) 1 = hirzebruchRay2) ∧
    (vertexConeRay (hirzebruchBasis 1) 0 = hirzebruchRay2 ∧
      vertexConeRay (hirzebruchBasis 1) 1 = hirzebruchRay3) ∧
    (vertexConeRay (hirzebruchBasis 2) 0 = hirzebruchRay3 ∧
      vertexConeRay (hirzebruchBasis 2) 1 = hirzebruchRay4) ∧
    (vertexConeRay (hirzebruchBasis 3) 0 = hirzebruchRay4 ∧
      vertexConeRay (hirzebruchBasis 3) 1 = hirzebruchRay1) := by
  simp only [hirzebruchBasis, Matrix.cons_val, vertexConeRay_lattice2Basis_zero,
    vertexConeRay_lattice2Basis_one, hirzebruchRay1, hirzebruchRay2, hirzebruchRay3,
    hirzebruchRay4]
  norm_num

variable (hs' : latticePolytopeEdgeSmooth hirzebruchGenerator)

/-- Source `ex:F2_non_lattice_polytope`: `Σ(1) = {ρ_1, ρ_2, ρ_3, ρ_4}`. -/
theorem hirzebruch_rays :
    PolytopeToricRays hirzebruchGenerator hs' =
      {hirzebruchRay1, hirzebruchRay2, hirzebruchRay3, hirzebruchRay4} := by
  rw [polytopeToricRays_eq_of_vertexCones hs' hirzebruchBasis hirzebruch_isVertexConeBasis]
  obtain ⟨⟨h00, h01⟩, ⟨h10, h11⟩, ⟨h20, h21⟩, ⟨h30, h31⟩⟩ := hirzebruch_vertexConeRays
  ext u
  simp only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨k, j, rfl⟩
    fin_cases k <;> fin_cases j <;> simp [h00, h01, h10, h11, h20, h21, h30, h31]
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, 0, h00⟩
    · exact ⟨0, 1, h01⟩
    · exact ⟨1, 1, h11⟩
    · exact ⟨2, 1, h21⟩

/-- Source `ex:F2_non_lattice_polytope`: the maximal cones are spanned by consecutive rays in
the cyclic order `ρ_1, ρ_2, ρ_3, ρ_4`. -/
theorem hirzebruch_maximalCones :
    range (polytopeToricRayGenerator hirzebruchGenerator hs' (hirzebruchVertex 0)) =
      {hirzebruchRay1, hirzebruchRay2} ∧
    range (polytopeToricRayGenerator hirzebruchGenerator hs' (hirzebruchVertex 1)) =
      {hirzebruchRay2, hirzebruchRay3} ∧
    range (polytopeToricRayGenerator hirzebruchGenerator hs' (hirzebruchVertex 2)) =
      {hirzebruchRay3, hirzebruchRay4} ∧
    range (polytopeToricRayGenerator hirzebruchGenerator hs' (hirzebruchVertex 3)) =
      {hirzebruchRay4, hirzebruchRay1} := by
  obtain ⟨⟨h00, h01⟩, ⟨h10, h11⟩, ⟨h20, h21⟩, ⟨h30, h31⟩⟩ := hirzebruch_vertexConeRays
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [range_vertexCone_two hs' (hirzebruchVertex 0) (hirzebruch_isVertexConeBasis 0), h00, h01]
  · rw [range_vertexCone_two hs' (hirzebruchVertex 1) (hirzebruch_isVertexConeBasis 1), h10, h11]
  · rw [range_vertexCone_two hs' (hirzebruchVertex 2) (hirzebruch_isVertexConeBasis 2), h20, h21]
  · rw [range_vertexCone_two hs' (hirzebruchVertex 3) (hirzebruch_isVertexConeBasis 3), h30, h31]

/-- Source `ex:F2_non_lattice_polytope`: `D = -D_{ρ_3} + 2 D_{ρ_4}`. -/
def hirzebruchDivisor : ToricDivisor hirzebruchGenerator hs' :=
  toricDivisorOfCoeff hs' fun u =>
    if u = hirzebruchRay3 then -1 else if u = hirzebruchRay4 then 2 else 0

/-- Source `ex:F2_non_lattice_polytope`:
`P_D = {m : m_1 ≥ 0, (m_1 + 1)/2 ≤ m_2 ≤ 2}`. -/
theorem toricDivisorPolytope_hirzebruchDivisor :
    toricDivisorPolytope (hirzebruchDivisor hs') =
      {m | 0 ≤ m 0 ∧ (m 0 + 1) / 2 ≤ m 1 ∧ m 1 ≤ 2} := by
  rw [hirzebruchDivisor, toricDivisorPolytope_ofCoeff (hirzebruch_rays hs')]
  ext m
  simp only [mem_insert_iff, mem_singleton_iff, forall_eq_or_imp, forall_eq, mem_ofPred_eq,
    latticeFunctional_two, hirzebruchRay1, hirzebruchRay2, hirzebruchRay3, hirzebruchRay4,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num
  intro h1
  constructor
  · rintro ⟨h2, h3, h4⟩
    exact ⟨by linarith, h4⟩
  · rintro ⟨h3, h4⟩
    exact ⟨by linarith, by linarith, h4⟩

/-- The vertex `(0, 1/2)` of `P_D` is an extreme point of `P_D`. -/
theorem hirzebruch_extremePoint :
    (EuclideanSpace.equiv (Fin 2) ℝ).symm ![0, 1 / 2] ∈
      (toricDivisorPolytope (hirzebruchDivisor hs')).extremePoints ℝ := by
  rw [toricDivisorPolytope_hirzebruchDivisor]
  refine _root_.mem_extremePoints.mpr ⟨by simp; norm_num, ?_⟩
  rintro x ⟨hx0, hx1, -⟩ y ⟨hy0, hy1, -⟩ ⟨a, b, ha, hb, hab, hxy⟩
  have h0 := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 0) hxy
  have h1 := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 1) hxy
  simp at h0 h1
  have hx0' : x 0 = 0 := by nlinarith [mul_nonneg ha.le hx0, mul_nonneg hb.le hy0]
  have hy0' : y 0 = 0 := by nlinarith [mul_nonneg ha.le hx0, mul_nonneg hb.le hy0]
  rw [hx0'] at hx1; rw [hy0'] at hy1
  have hx1' : x 1 = 1 / 2 := by nlinarith
  have hy1' : y 1 = 1 / 2 := by nlinarith
  constructor
  · ext i; fin_cases i <;> simp [hx0', hx1']
  · ext i; fin_cases i <;> simp [hy0', hy1']

/-- Source `ex:F2_non_lattice_polytope`: `P_D` is not a lattice polytope: it is not the convex
hull of any set of lattice points (its vertex `(0, 1/2)` is not a lattice point). -/
theorem hirzebruch_not_latticePolytope :
    ¬ ∃ S : Set (Fin 2 → ℤ),
      toricDivisorPolytope (hirzebruchDivisor hs') = convexHull ℝ (latticeVector '' S) := by
  rintro ⟨S, hS⟩
  have hp := hirzebruch_extremePoint hs'
  rw [hS] at hp
  obtain ⟨m, -, hm⟩ := extremePoints_convexHull_subset hp
  have h1 := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 1) hm
  simp only [latticeVector_apply] at h1
  have : (m 1 : ℝ) = 1 / 2 := by simpa using h1
  have hlt : (0 : ℝ) < m 1 := by rw [this]; norm_num
  have hlt' : (m 1 : ℝ) < 1 := by rw [this]; norm_num
  have h0 : (0 : ℤ) < m 1 := by exact_mod_cast hlt
  have h1' : m 1 < (1 : ℤ) := by exact_mod_cast hlt'
  omega

end SGPT.Toric
