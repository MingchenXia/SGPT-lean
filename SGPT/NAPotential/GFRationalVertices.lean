import SGPT.Convex.CutSimplexVertices
import Mathlib.Data.NNRat.Defs

/-! # Rational vertices of the ORIGINAL cut simplex have one actual integer denominator
Blueprint: `gf-rational-hull.tex`. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.NAPotential.BJ.GfIm.RationalHull

open Set SGPT.Convex.CutSimplex
open scoped Classical
variable {ι : Type} [Fintype ι]

/-- The actual rational coordinates of each original vertex, in the original vertex order. -/
def rationalVertexVector (τ : ι → ℚ) (s : ℚ) :
    VertexIndex (fun i => (τ i : ℝ)) (s : ℝ) → (ι → ℚ)
  | Sum.inl i => fun k => if k = i.val then 1 else 0
  | Sum.inr p => fun k =>
      (s - τ p.val.2) / (τ p.val.1 - τ p.val.2) * (if k = p.val.1 then 1 else 0) +
      (τ p.val.1 - s) / (τ p.val.1 - τ p.val.2) * (if k = p.val.2 then 1 else 0)

omit [Fintype ι] in
/-- These actual rational coefficients are the ORIGINAL real simplex vertex coordinates. -/
theorem rationalVertexVector_cast (τ : ι → ℚ) (s : ℚ)
    (v : VertexIndex (fun i => (τ i : ℝ)) (s : ℝ)) (k : ι) :
    (rationalVertexVector τ s v k : ℝ) = vertexVector (fun i => (τ i : ℝ)) (s : ℝ) v k := by
  classical
  cases v with
  | inl i =>
    simp only [rationalVertexVector, vertexVector, basis]
    split_ifs <;> norm_num
  | inr p =>
    simp only [rationalVertexVector, vertexVector, pairWeights, basis, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_sub]
    split_ifs <;> norm_num

/-- Actual vertex feasibility gives actual nonnegative rational coordinates. -/
theorem rationalVertexVector_nonneg (τ : ι → ℚ) (s : ℚ)
    (v : VertexIndex (fun i => (τ i : ℝ)) (s : ℝ)) (k : ι) :
    0 ≤ rationalVertexVector τ s v k := by
  have h := (mem_cut_iff _ _ _).mp (vertexVector_isExtreme (fun i => (τ i : ℝ)) (s : ℝ) v).1
  have hk := h.1 k
  rw [← rationalVertexVector_cast] at hk
  exact_mod_cast hk

/-- The ORIGINAL rational vertex coordinates have total mass one. -/
theorem sum_rationalVertexVector (τ : ι → ℚ) (s : ℚ)
    (v : VertexIndex (fun i => (τ i : ℝ)) (s : ℝ)) :
    ∑ k, rationalVertexVector τ s v k = 1 := by
  have h := (mem_cut_iff _ _ _).mp (vertexVector_isExtreme (fun i => (τ i : ℝ)) (s : ℝ) v).1
  have hs := h.2.1
  simp_rw [← rationalVertexVector_cast] at hs
  exact_mod_cast hs


/-- The finite family of actual nonnegative rational coordinates manufactures one positive common integer multiplier. -/
theorem exists_common_integer_multiples {κ : Type} [Fintype κ] (q : κ → ℚ≥0) :
    ∃ Q : ℕ, 0 < Q ∧ ∃ a : κ → ℕ, ∀ i, (Q : ℚ≥0) * q i = a i := by
  classical
  let Q := ∏ i, (q i).den
  have hQ : 0 < Q := Finset.prod_pos (fun i _ => (q i).den_pos)
  have hd (i : κ) : (q i).den ∣ Q := Finset.dvd_prod_of_mem (fun i => (q i).den) (Finset.mem_univ i)
  choose c hc using hd
  refine ⟨Q, hQ, fun i => c i * (q i).num, fun i => ?_⟩
  rw [hc i]
  push_cast
  calc
    ((q i).den : ℚ≥0) * c i * q i = (c i : ℚ≥0) * ((q i).den * q i) := by ring
    _ = (c i : ℚ≥0) * (q i).num := by rw [NNRat.den_mul_eq_num]

/-- **All ORIGINAL vertices at a rational original parameter have one actual integer tensor degree**. -/
theorem exists_integer_vertexWeights (τ : ι → ℚ) (s : ℚ) :
    ∃ Q : ℕ, 0 < Q ∧ ∃ a : VertexIndex (fun i => (τ i : ℝ)) (s : ℝ) → ι → ℕ,
      (∀ v, ∑ i, a v i = Q) ∧
      ∀ v i, vertexVector (fun i => (τ i : ℝ)) (s : ℝ) v i = (a v i : ℝ) / Q := by
  classical
  let V := VertexIndex (fun i => (τ i : ℝ)) (s : ℝ)
  let : Fintype V := Fintype.ofFinite V
  let q : V × ι → ℚ≥0 := fun vi =>
    ⟨rationalVertexVector τ s vi.1 vi.2, rationalVertexVector_nonneg τ s vi.1 vi.2⟩
  obtain ⟨Q, hQ, a, ha⟩ := exists_common_integer_multiples q
  have hmul (v : V) (i : ι) :
      (Q : ℝ) * vertexVector (fun i => (τ i : ℝ)) (s : ℝ) v i = (a (v, i) : ℝ) := by
    have h := congrArg (fun z : ℚ≥0 => (z : ℚ)) (ha (v, i))
    change (Q : ℚ) * rationalVertexVector τ s v i = (a (v, i) : ℚ) at h
    have hreal : (Q : ℝ) * (rationalVertexVector τ s v i : ℝ) = (a (v, i) : ℝ) := by exact_mod_cast h
    rw [rationalVertexVector_cast] at hreal
    exact hreal
  refine ⟨Q, hQ, fun v i => a (v, i), ?_, ?_⟩
  · intro v
    have hmass := ((mem_cut_iff _ _ _).mp (vertexVector_isExtreme (fun i => (τ i : ℝ)) (s : ℝ) v).1).2.1
    have hs : ∑ i, (a (v, i) : ℝ) = (Q : ℝ) := by
      simp_rw [← hmul v]
      rw [← Finset.mul_sum, hmass, mul_one]
    exact_mod_cast hs
  · intro v i
    apply (eq_div_iff (by exact_mod_cast hQ.ne' : (Q : ℝ) ≠ 0)).mpr
    exact (mul_comm _ _).trans (hmul v i)


/-- The same denominator producer for ORIGINAL real node data whose rationality is a primitive source hypothesis. -/
theorem exists_integer_vertexWeights_real (τ : ι → ℝ) (hτ : ∀ i, ∃ q : ℚ, τ i = q) (s : ℚ) :
    ∃ Q : ℕ, 0 < Q ∧ ∃ a : VertexIndex τ (s : ℝ) → ι → ℕ,
      (∀ v, ∑ i, a v i = Q) ∧ ∀ v i, vertexVector τ (s : ℝ) v i = (a v i : ℝ) / Q := by
  choose τq hτq using hτ
  have he : τ = fun i => (τq i : ℝ) := funext hτq
  rw [he]
  exact exists_integer_vertexWeights τq s

end SGPT.NAPotential.BJ.GfIm.RationalHull
