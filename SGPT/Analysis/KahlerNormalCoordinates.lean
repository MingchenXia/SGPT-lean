import SGPT.Foundations.Analysis.Pending.CoordinateDensityHermitian
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.Calculus.FDeriv.ContinuousAlternatingMap

/-!
# Kähler normal coordinates

Lane TOS-C11 (`claude-tos-c11`, node `tos-c11:normal-coordinates`).  Source: Xia, *Foundations of
pluripotential theory*, `lem:kahler-normal-coordinates-uniform` (chapter q10, section
`sec:penalized-kahler-envelopes`), used in the Aubin–Yau trace estimate
(`lem:kahler-trace-laplacian`) and in the real Hessian estimate of Tosatti and Chu–Zhou
(`lem:penalized-real-hessian`) behind SGPT `thm:Tos_C11`.

Let `a` be a smooth field of real two-forms on an open set of `ℂⁿ` (the chart coefficient
`ComplexModel n → CoordinateRealTwoForm n` of a form of the library), of type `(1,1)`, strictly
positive and closed.  At a point `z₀` we produce holomorphic coordinates
`z = Φ(w) = z₀ + A (w - ½ c(w, w))` — `A` a `ℂ`-linear map, `c` a symmetric `ℂ`-bilinear map —
in which the pulled-back form `Φ^*a` equals the flat form `ω₀ = π⁻¹ Im⟪·,·⟫` at `0` (coefficient
matrix the identity, `normalizedHermitianMatrix (Φ^*a)(0) = 1`, the normalization
`ω = (i/2π) Σ hᵢⱼ dzᵢ ∧ dz̄ⱼ` of FPT) and has vanishing differential at `0`.

* `flatForm n` — `ω₀ = π⁻¹ Im⟪u, v⟫`, with `normalizedHermitianMatrix (flatForm n) = 1`.
* `pullbackField Φ a w = (a (Φ w))(DΦ(w) ·, DΦ(w) ·)` — the pullback of a form field.
* `normalQuad β` — the quadratic coefficient `c` built from the derivative `β = D(A^*a)(0)` of
  the linearly normalized form: `⟪v, c(p, u)⟫ = π ∂_p H(u, v)`, where `H` is the Hermitian entry
  of the form and `∂_p = ½(D_p - i D_{ip})`.  It is `ℂ`-bilinear, and **symmetric** because the
  form is closed (`normalQuad_symm`).
* `exists_normalizing_linear` — a strictly positive `(1,1)`-form is `ω₀` in suitable linear
  coordinates (Cholesky/`C⋆`-square root from `exists_linearMap_eq_standard_comp`).
* `kahlerNormal_pullback_zero`, `kahlerNormal_hasFDerivAt_zero` — **normal coordinates**: for
  every `ℂ`-linear `A` with `A^*a(z₀) = ω₀`, the map `Φ = normalCoord z₀ A c` satisfies
  `(Φ^*a)(0) = ω₀` and `D(Φ^*a)(0) = 0`.  Since every such `A` is allowed, the property persists
  under composition with unitary maps (`A ↦ A ∘ Q`), as in FPT.
* `exists_kahlerNormalCoordinates` — the existence statement of FPT's lemma.
* Uniformity (`kahlerNormal_uniform`): on a compact subset `K` of the domain, `‖A‖`, `‖c‖` and
  the derivatives of every fixed order of `Φ^*a` at `0` are bounded independently of `z₀ ∈ K`
  and of the normalizing `A`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped Topology ContDiff InnerProductSpace

namespace SGPT.Analysis.KahlerNormal

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere

variable {n : ℕ}

/-! ### Two-form algebra -/

section TwoForm

variable (α : CoordinateRealTwoForm n)

theorem twoForm_swap (u v : ComplexModel n) : α ![v, u] = -α ![u, v] := by
  simpa using α.map_swap ![u, v] (i := 0) (j := 1) (by decide)

theorem twoForm_add_left (u u' v : ComplexModel n) :
    α ![u + u', v] = α ![u, v] + α ![u', v] :=
  α.toMultilinearMap.cons_add ![v] u u'

theorem twoForm_smul_left (r : ℝ) (u v : ComplexModel n) :
    α ![r • u, v] = r * α ![u, v] :=
  α.toMultilinearMap.cons_smul ![v] r u

theorem twoForm_add_right (u v v' : ComplexModel n) :
    α ![u, v + v'] = α ![u, v] + α ![u, v'] := by
  rw [twoForm_swap α (v + v') u, twoForm_add_left, twoForm_swap α u v, twoForm_swap α u v']
  ring

theorem twoForm_smul_right (r : ℝ) (u v : ComplexModel n) :
    α ![u, r • v] = r * α ![u, v] := by
  rw [twoForm_swap α (r • v) u, twoForm_smul_left, twoForm_swap α u v]
  ring

theorem twoForm_neg_left (u v : ComplexModel n) : α ![-u, v] = -α ![u, v] := by
  simpa using twoForm_smul_left α (-1) u v

theorem twoForm_neg_right (u v : ComplexModel n) : α ![u, -v] = -α ![u, v] := by
  simpa using twoForm_smul_right α (-1) u v

variable {α}

theorem twoForm_I_left (hα : IsOneOne α) (u v : ComplexModel n) :
    α ![Complex.I • u, v] = -α ![u, Complex.I • v] := by
  rw [← hα u (Complex.I • v), smul_smul, Complex.I_mul_I, neg_one_smul, twoForm_neg_right,
    neg_neg]

/-- A real two-form is recovered from its Hermitian entry: `α(u, v) = -Im H_α(u, v)`. -/
theorem twoForm_eq_neg_im_hermitianEntry (u v : ComplexModel n) :
    α ![u, v] = -(hermitianEntry α u v).im := by
  simp [hermitianEntry]

end TwoForm

/-! ### The flat form -/

/-- The flat Kähler form `ω₀ = π⁻¹ Im⟪u, v⟫` on `ℂⁿ`, i.e. `ω₀ = (i/2π) Σ dzⱼ ∧ dz̄ⱼ`: its
coefficient matrix in the normalization `ω = (i/2π) Σ hⱼₖ dzⱼ ∧ dz̄ₖ` is the identity
(`normalizedHermitianMatrix_flatForm`). -/
def flatForm (n : ℕ) : CoordinateRealTwoForm n := Real.pi⁻¹ • standardHermitianTwoForm n

@[simp] theorem flatForm_apply (u v : ComplexModel n) :
    flatForm n ![u, v] = Real.pi⁻¹ * (inner ℂ u v).im := by
  simp [flatForm]

theorem flatForm_isOneOne (n : ℕ) : IsOneOne (flatForm n) := by
  intro u v
  simp [flatForm_apply, inner_smul_left, inner_smul_right]

theorem flatForm_apply_I_smul_self (u : ComplexModel n) :
    flatForm n ![u, Complex.I • u] = Real.pi⁻¹ * ‖u‖ ^ 2 := by
  simp only [flatForm, ContinuousAlternatingMap.smul_apply, standardHermitianTwoForm_apply_I_smul_self,
    smul_eq_mul]

theorem flatForm_isStrictlyPositive (n : ℕ) : IsStrictlyPositive (flatForm n) := by
  intro u hu
  rw [flatForm_apply_I_smul_self]
  have : 0 < ‖u‖ := norm_pos_iff.mpr hu
  positivity

theorem hermitianEntry_flatForm (u v : ComplexModel n) :
    hermitianEntry (flatForm n) u v = (Real.pi⁻¹ : ℂ) * inner ℂ v u := by
  have h := inner_conj_symm (𝕜 := ℂ) u v
  have hre : (inner ℂ v u).re = (inner ℂ u v).re := by
    conv_rhs => rw [← h]
    rw [Complex.conj_re]
  have him : (inner ℂ v u).im = -(inner ℂ u v).im := by
    conv_rhs => rw [← h]
    rw [Complex.conj_im, neg_neg]
  apply Complex.ext
  · simp only [hermitianEntry, flatForm_apply, inner_smul_right]
    simp [hre]
  · simp only [hermitianEntry, flatForm_apply]
    simp [him]

/-- The coefficient matrix of `ω₀` is the identity. -/
theorem normalizedHermitianMatrix_flatForm (n : ℕ) :
    normalizedHermitianMatrix (flatForm n) = 1 := by
  ext j k
  rw [normalizedHermitianMatrix_apply', hermitianEntry_flatForm]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [← mul_assoc, ← Complex.ofReal_inv, ← Complex.ofReal_mul, mul_inv_cancel₀ Real.pi_ne_zero,
    Complex.ofReal_one, one_mul]
  simp [coordinateVector, Matrix.one_apply, EuclideanSpace.inner_single_left, eq_comm]

/-! ### Complex scalars and coordinate expansions -/

theorem complex_smul_eq_re_im (c : ℂ) (w : ComplexModel n) :
    c • w = c.re • w + c.im • (Complex.I • w) := by
  conv_lhs => rw [← Complex.re_add_im c]
  rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]

theorem eq_sum_coordinateVector (v : ComplexModel n) :
    v = ∑ j, v j • coordinateVector j := by
  ext q
  simp [coordinateVector, Pi.single_apply, mul_ite]

theorem inner_coordinateVector_right (v : ComplexModel n) (j : Fin n) :
    inner ℂ v (coordinateVector j) = (starRingEnd ℂ) (v j) := by
  simp [coordinateVector, EuclideanSpace.inner_single_right]

/-! ### The quadratic coefficient -/

section Quad

variable (β : ComplexModel n →L[ℝ] CoordinateRealTwoForm n)

/-- The `(1,0)`-derivative `∂_p H(u, v) = ½ (H_{β p}(u, v) - i H_{β (i p)}(u, v))` of the Hermitian
entry `H` of a form whose real derivative at the point is `β`. -/
def dHol (p u v : ComplexModel n) : ℂ :=
  (1 / 2 : ℂ) * (hermitianEntry (β p) u v - Complex.I * hermitianEntry (β (Complex.I • p)) u v)

theorem dHol_re (p u v : ComplexModel n) :
    (dHol β p u v).re = (β p ![u, Complex.I • v] - β (Complex.I • p) ![u, v]) / 2 := by
  simp [dHol, hermitianEntry]
  ring

theorem dHol_im (p u v : ComplexModel n) :
    (dHol β p u v).im = -(β p ![u, v] + β (Complex.I • p) ![u, Complex.I • v]) / 2 := by
  simp [dHol, hermitianEntry]
  ring

theorem dHol_add_left (p p' u v : ComplexModel n) :
    dHol β (p + p') u v = dHol β p u v + dHol β p' u v := by
  apply Complex.ext <;> simp only [dHol_re, dHol_im, Complex.add_re, Complex.add_im, smul_add,
    map_add, ContinuousAlternatingMap.add_apply] <;> ring

theorem dHol_smul_left (r : ℝ) (p u v : ComplexModel n) :
    dHol β (r • p) u v = r * dHol β p u v := by
  apply Complex.ext <;> simp only [dHol_re, dHol_im, Complex.re_ofReal_mul, Complex.im_ofReal_mul,
    smul_comm Complex.I r, map_smul, ContinuousAlternatingMap.smul_apply, smul_eq_mul] <;> ring

theorem dHol_I_smul_left (p u v : ComplexModel n) :
    dHol β (Complex.I • p) u v = Complex.I * dHol β p u v := by
  have hII : Complex.I • Complex.I • p = -p := by rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  apply Complex.ext <;>
    simp only [dHol_re, dHol_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, hII,
      map_neg, ContinuousAlternatingMap.neg_apply] <;> ring

theorem dHol_complex_smul_left (c : ℂ) (p u v : ComplexModel n) :
    dHol β (c • p) u v = c * dHol β p u v := by
  rw [complex_smul_eq_re_im, dHol_add_left, dHol_smul_left, dHol_smul_left, dHol_I_smul_left]
  conv_rhs => rw [← Complex.re_add_im c]
  ring

theorem dHol_add_mid (p u u' v : ComplexModel n) :
    dHol β p (u + u') v = dHol β p u v + dHol β p u' v := by
  apply Complex.ext <;> simp only [dHol_re, dHol_im, Complex.add_re, Complex.add_im,
    twoForm_add_left] <;> ring

theorem dHol_smul_mid (r : ℝ) (p u v : ComplexModel n) :
    dHol β p (r • u) v = r * dHol β p u v := by
  apply Complex.ext <;> simp only [dHol_re, dHol_im, Complex.re_ofReal_mul, Complex.im_ofReal_mul,
    twoForm_smul_left] <;> ring

theorem dHol_I_smul_mid (h11 : ∀ q, IsOneOne (β q)) (p u v : ComplexModel n) :
    dHol β p (Complex.I • u) v = Complex.I * dHol β p u v := by
  have hII : Complex.I • Complex.I • v = -v := by rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  have h1 := twoForm_I_left (h11 p) u (Complex.I • v)
  have h2 := twoForm_I_left (h11 p) u v
  have h3 := twoForm_I_left (h11 (Complex.I • p)) u (Complex.I • v)
  have h4 := twoForm_I_left (h11 (Complex.I • p)) u v
  rw [hII, twoForm_neg_right] at h1 h3
  apply Complex.ext <;>
    simp only [dHol_re, dHol_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      h1, h2, h3, h4] <;> ring

theorem dHol_complex_smul_mid (h11 : ∀ q, IsOneOne (β q)) (c : ℂ) (p u v : ComplexModel n) :
    dHol β p (c • u) v = c * dHol β p u v := by
  rw [complex_smul_eq_re_im, dHol_add_mid, dHol_smul_mid, dHol_smul_mid, dHol_I_smul_mid β h11]
  conv_rhs => rw [← Complex.re_add_im c]
  ring

theorem dHol_add_right (p u v v' : ComplexModel n) :
    dHol β p u (v + v') = dHol β p u v + dHol β p u v' := by
  simp only [dHol, hermitianEntry_add_right]
  ring

theorem dHol_smul_right (c : ℂ) (p u v : ComplexModel n) :
    dHol β p u (c • v) = (starRingEnd ℂ) c * dHol β p u v := by
  simp only [dHol, hermitianEntry_smul_right]
  ring

theorem dHol_zero_right (p u : ComplexModel n) : dHol β p u 0 = 0 := by
  simpa using dHol_smul_right β 0 p u 0

theorem dHol_sum_right (p u : ComplexModel n) (c : Fin n → ℂ) :
    dHol β p u (∑ j, c j • coordinateVector j) =
      ∑ j, (starRingEnd ℂ) (c j) * dHol β p u (coordinateVector j) := by
  induction (Finset.univ : Finset (Fin n)) using Finset.induction with
  | empty => simp [dHol_zero_right]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, dHol_add_right, dHol_smul_right, ih, Finset.sum_insert ha]

/-- **Symmetry from closedness.**  If every `β q` is of type `(1,1)` and `β` satisfies the cocycle
identity `β_x(y, z) - β_y(x, z) + β_z(x, y) = 0` of a closed form, then `∂_p H(u, v)` is symmetric
in `p` and `u`. -/
theorem dHol_symm (h11 : ∀ q, IsOneOne (β q))
    (hcl : ∀ x y z : ComplexModel n, β x ![y, z] - β y ![x, z] + β z ![x, y] = 0)
    (p u v : ComplexModel n) : dHol β p u v = dHol β u p v := by
  -- type `(1,1)` consequences
  have a1 : β u ![Complex.I • p, Complex.I • v] = β u ![p, v] := h11 u p v
  have a2 : β p ![Complex.I • u, Complex.I • v] = β p ![u, v] := h11 p u v
  have b1 : β (Complex.I • v) ![Complex.I • u, p] = β (Complex.I • v) ![Complex.I • p, u] := by
    rw [twoForm_I_left (h11 (Complex.I • v)), twoForm_swap (β (Complex.I • v)) u (Complex.I • p)]
  have b2 : β v ![Complex.I • u, p] = β v ![Complex.I • p, u] := by
    rw [twoForm_I_left (h11 v), twoForm_swap (β v) u (Complex.I • p)]
  have c1 : β u ![Complex.I • p, v] = -β u ![p, Complex.I • v] := twoForm_I_left (h11 u) p v
  have c2 : β p ![Complex.I • u, v] = -β p ![u, Complex.I • v] := twoForm_I_left (h11 p) u v
  -- closedness instances
  have k1 := hcl p u v
  have k2 := hcl (Complex.I • p) u (Complex.I • v)
  have k3 := hcl (Complex.I • u) p (Complex.I • v)
  have k4 := hcl p u (Complex.I • v)
  have k5 := hcl (Complex.I • p) u v
  have k6 := hcl (Complex.I • u) p v
  apply Complex.ext
  · rw [dHol_re, dHol_re]
    linarith
  · rw [dHol_im, dHol_im]
    linarith

/-- The vector `c(p, u) = π Σⱼ ∂_p H(u, eⱼ) eⱼ`, characterized by `⟪v, c(p, u)⟫ = π ∂_p H(u, v)`. -/
def quadFun (p u : ComplexModel n) : ComplexModel n :=
  ∑ j, ((Real.pi : ℂ) * dHol β p u (coordinateVector j)) • coordinateVector j

theorem inner_quadFun (p u v : ComplexModel n) :
    inner ℂ v (quadFun β p u) = (Real.pi : ℂ) * dHol β p u v := by
  rw [quadFun, inner_sum]
  conv_rhs => rw [eq_sum_coordinateVector v, dHol_sum_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_smul_right, inner_coordinateVector_right]
  ring

theorem quadFun_symm (h11 : ∀ q, IsOneOne (β q))
    (hcl : ∀ x y z : ComplexModel n, β x ![y, z] - β y ![x, z] + β z ![x, y] = 0)
    (p u : ComplexModel n) : quadFun β p u = quadFun β u p := by
  simp only [quadFun, dHol_symm β h11 hcl p u]

/-- **The first-order identity**: `β p (u, v) = ω₀(c(p, u), v) + ω₀(u, c(p, v))`. -/
theorem apply_eq_flatForm_quadFun (h11 : ∀ q, IsOneOne (β q)) (p u v : ComplexModel n) :
    β p ![u, v] = flatForm n ![quadFun β p u, v] + flatForm n ![u, quadFun β p v] := by
  have hc : inner ℂ (quadFun β p u) v = (starRingEnd ℂ) ((Real.pi : ℂ) * dHol β p u v) := by
    rw [← inner_quadFun, inner_conj_symm]
  rw [flatForm_apply, flatForm_apply, hc, inner_quadFun, Complex.conj_im, Complex.im_ofReal_mul,
    Complex.im_ofReal_mul, dHol_im, dHol_im]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have e1 : β (Complex.I • p) ![v, Complex.I • u] = β (Complex.I • p) ![u, Complex.I • v] := by
    have := h11 (Complex.I • p) v (Complex.I • u)
    rw [smul_smul, Complex.I_mul_I, neg_one_smul, twoForm_neg_right] at this
    rw [← this, twoForm_swap (β (Complex.I • p)) (Complex.I • v) u]
  have e2 : β p ![v, u] = -β p ![u, v] := twoForm_swap (β p) u v
  field_simp
  rw [e1, e2]
  ring

theorem quadFun_add_left (p p' u : ComplexModel n) :
    quadFun β (p + p') u = quadFun β p u + quadFun β p' u := by
  simp only [quadFun, dHol_add_left, mul_add, add_smul, Finset.sum_add_distrib]

theorem quadFun_smul_left (c : ℂ) (p u : ComplexModel n) :
    quadFun β (c • p) u = c • quadFun β p u := by
  simp only [quadFun, dHol_complex_smul_left, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring_nf

theorem quadFun_add_mid (p u u' : ComplexModel n) :
    quadFun β p (u + u') = quadFun β p u + quadFun β p u' := by
  simp only [quadFun, dHol_add_mid, mul_add, add_smul, Finset.sum_add_distrib]

theorem quadFun_smul_mid (h11 : ∀ q, IsOneOne (β q)) (c : ℂ) (p u : ComplexModel n) :
    quadFun β p (c • u) = c • quadFun β p u := by
  simp only [quadFun, dHol_complex_smul_mid β h11, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring_nf

/-- `c` as a `ℂ`-bilinear map (requires `β q` of type `(1,1)` for linearity in `u`). -/
def normalQuadₗ (h11 : ∀ q, IsOneOne (β q)) :
    ComplexModel n →ₗ[ℂ] ComplexModel n →ₗ[ℂ] ComplexModel n :=
  LinearMap.mk₂ ℂ (quadFun β) (quadFun_add_left β) (quadFun_smul_left β) (quadFun_add_mid β)
    (quadFun_smul_mid β h11)

/-- **The quadratic coefficient** `c` of Kähler normal coordinates, a continuous `ℂ`-bilinear map
with `⟪v, c(p, u)⟫ = π ∂_p H(u, v)`. -/
def normalQuad (h11 : ∀ q, IsOneOne (β q)) :
    ComplexModel n →L[ℂ] ComplexModel n →L[ℂ] ComplexModel n :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap :
      (ComplexModel n →ₗ[ℂ] ComplexModel n) ≃ₗ[ℂ] (ComplexModel n →L[ℂ] ComplexModel n)).toLinearMap
      ∘ₗ normalQuadₗ β h11)

@[simp] theorem normalQuad_apply (h11 : ∀ q, IsOneOne (β q)) (p u : ComplexModel n) :
    normalQuad β h11 p u = quadFun β p u := rfl

/-- **`c` is symmetric** when the form is closed. -/
theorem normalQuad_symm (h11 : ∀ q, IsOneOne (β q))
    (hcl : ∀ x y z : ComplexModel n, β x ![y, z] - β y ![x, z] + β z ![x, y] = 0)
    (p u : ComplexModel n) : normalQuad β h11 p u = normalQuad β h11 u p :=
  quadFun_symm β h11 hcl p u

end Quad

/-! ### Linear normalization -/

/-- **Linear normal form.**  A strictly positive real `(1,1)`-form is the flat form `ω₀` in
suitable `ℂ`-linear coordinates: `α(Au, Av) = ω₀(u, v)`. -/
theorem exists_normalizing_linear {α : CoordinateRealTwoForm n} (h11 : IsOneOne α)
    (hpos : IsStrictlyPositive α) :
    ∃ A : ComplexModel n ≃L[ℂ] ComplexModel n, ∀ u v, α ![A u, A v] = flatForm n ![u, v] := by
  have hsemi : PositiveClasses.CoefficientSemipositive α := by
    intro v
    by_cases hv : v = 0
    · subst v
      rw [α.map_coord_zero (0 : Fin 2) rfl]
    · exact (hpos v hv).le
  obtain ⟨S, hS⟩ := exists_linearMap_eq_standard_comp h11 hsemi
  have hdet := det_ne_zero_of_standard_comp_strictlyPositive hS hpos
  set Se : ComplexModel n ≃ₗ[ℂ] ComplexModel n := LinearMap.equivOfDetNeZero S hdet
  have hSe : ∀ x, Se x = S x := fun x => rfl
  set r : ℝ := (Real.sqrt Real.pi)⁻¹
  have hr0 : r ≠ 0 := inv_ne_zero (Real.sqrt_ne_zero'.mpr Real.pi_pos)
  have hr2 : r * r = Real.pi⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt Real.pi_pos.le]
  have hrc : ((r : ℂ)) ≠ 0 := by exact_mod_cast hr0
  set A : ComplexModel n ≃L[ℂ] ComplexModel n :=
    (Se.symm.trans (LinearEquiv.smulOfUnit (Units.mk0 (r : ℂ) hrc))).toContinuousLinearEquiv
  have hA : ∀ x, S (A x) = (r : ℂ) • x := by
    intro x
    change S ((r : ℂ) • Se.symm x) = _
    rw [map_smul, ← hSe, LinearEquiv.apply_symm_apply]
  refine ⟨A, fun u v => ?_⟩
  rw [hS, hA, hA, flatForm_apply, inner_smul_left, inner_smul_right, Complex.conj_ofReal,
    ← mul_assoc, ← Complex.ofReal_mul, Complex.im_ofReal_mul, hr2]

/-! ### Fields of forms: type `(1,1)` and closedness of the derivative -/

theorem twoForm_apply_eq_vec (α : CoordinateRealTwoForm n) (m : Fin 2 → ComplexModel n) :
    α m = α ![m 0, m 1] := by
  congr 1
  funext i
  fin_cases i <;> rfl

theorem fderivCompContinuousLinearMap_apply_two (α : CoordinateRealTwoForm n)
    (g dg : ComplexModel n →L[ℝ] ComplexModel n) (u v : ComplexModel n) :
    α.fderivCompContinuousLinearMap g dg ![u, v] = α ![dg u, g v] + α ![g u, dg v] := by
  rw [ContinuousAlternatingMap.fderivCompContinuousLinearMap_apply, Fin.sum_univ_two]
  congr 1 <;> (congr 1; funext j; fin_cases j <;> simp [Function.update])

theorem compContinuousLinearMap_apply_two (α : CoordinateRealTwoForm n)
    (L : ComplexModel n →L[ℝ] ComplexModel n) (u v : ComplexModel n) :
    α.compContinuousLinearMap L ![u, v] = α ![L u, L v] := by
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- The derivative of a field of `(1,1)`-forms is of type `(1,1)` in every direction. -/
theorem isOneOne_fderiv {a : ComplexModel n → CoordinateRealTwoForm n} {z₀ : ComplexModel n}
    (ha : DifferentiableAt ℝ a z₀) (h11 : ∀ᶠ z in 𝓝 z₀, IsOneOne (a z)) (q : ComplexModel n) :
    IsOneOne (fderiv ℝ a z₀ q) := by
  intro u v
  have heq : (fun y => a y ![Complex.I • u, Complex.I • v]) =ᶠ[𝓝 z₀] (fun y => a y ![u, v]) :=
    h11.mono fun z hz => hz u v
  rw [← fderiv_continuousAlternatingMap_apply_const_apply ha,
    ← fderiv_continuousAlternatingMap_apply_const_apply ha, heq.fderiv_eq]

/-- The derivative of a closed field of two-forms satisfies the cocycle identity
`Da(x)(y, z) - Da(y)(x, z) + Da(z)(x, y) = 0` (this is `da = 0`). -/
theorem cocycle_fderiv {a : ComplexModel n → CoordinateRealTwoForm n} {z₀ : ComplexModel n}
    (ha : DifferentiableAt ℝ a z₀) (hcl : extDeriv a z₀ = 0) (x y z : ComplexModel n) :
    fderiv ℝ a z₀ x ![y, z] - fderiv ℝ a z₀ y ![x, z] + fderiv ℝ a z₀ z ![x, y] = 0 := by
  have h := congrArg (fun F => F ![x, y, z]) hcl
  simp only [_root_.extDeriv_apply ha, ContinuousAlternatingMap.coe_zero, Pi.zero_apply,
    Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
    fderiv_continuousAlternatingMap_apply_const_apply ha] at h
  have r0 : Fin.removeNth 0 ![x, y, z] = ![y, z] := by
    funext i; fin_cases i <;> rfl
  have r1 : Fin.removeNth (Fin.succ 0) ![x, y, z] = ![x, z] := by
    funext i; fin_cases i <;> rfl
  have r2 : Fin.removeNth (Fin.succ (Fin.succ 0)) ![x, y, z] = ![x, y] := by
    funext i; fin_cases i <;> rfl
  simp only [r0, r1, r2] at h
  simp at h
  linarith

/-- The derivative at `0` of the linearly normalized field `w ↦ a(z₀ + A w)(A ·, A ·)`:
`β q = Da(z₀)(A q)(A ·, A ·)`. -/
def normalizedDeriv (a : ComplexModel n → CoordinateRealTwoForm n) (z₀ : ComplexModel n)
    (A : ComplexModel n →L[ℂ] ComplexModel n) : ComplexModel n →L[ℝ] CoordinateRealTwoForm n :=
  ContinuousAlternatingMap.compContinuousLinearMapCLM (A.restrictScalars ℝ) ∘L fderiv ℝ a z₀ ∘L
    A.restrictScalars ℝ

theorem normalizedDeriv_apply (a : ComplexModel n → CoordinateRealTwoForm n) (z₀ : ComplexModel n)
    (A : ComplexModel n →L[ℂ] ComplexModel n) (q u v : ComplexModel n) :
    normalizedDeriv a z₀ A q ![u, v] = fderiv ℝ a z₀ (A q) ![A u, A v] := by
  simp only [normalizedDeriv, ContinuousLinearMap.comp_apply,
    ContinuousAlternatingMap.compContinuousLinearMapCLM_apply, compContinuousLinearMap_apply_two,
    ContinuousLinearMap.coe_restrictScalars']

theorem normalizedDeriv_isOneOne {a : ComplexModel n → CoordinateRealTwoForm n}
    {z₀ : ComplexModel n} (ha : DifferentiableAt ℝ a z₀) (h11 : ∀ᶠ z in 𝓝 z₀, IsOneOne (a z))
    (A : ComplexModel n →L[ℂ] ComplexModel n) (q : ComplexModel n) :
    IsOneOne (normalizedDeriv a z₀ A q) := by
  intro u v
  rw [normalizedDeriv_apply, normalizedDeriv_apply, map_smul, map_smul]
  exact isOneOne_fderiv ha h11 (A q) (A u) (A v)

theorem normalizedDeriv_cocycle {a : ComplexModel n → CoordinateRealTwoForm n}
    {z₀ : ComplexModel n} (ha : DifferentiableAt ℝ a z₀) (hcl : extDeriv a z₀ = 0)
    (A : ComplexModel n →L[ℂ] ComplexModel n) (x y z : ComplexModel n) :
    normalizedDeriv a z₀ A x ![y, z] - normalizedDeriv a z₀ A y ![x, z] +
      normalizedDeriv a z₀ A z ![x, y] = 0 := by
  simp only [normalizedDeriv_apply]
  exact cocycle_fderiv ha hcl (A x) (A y) (A z)

/-! ### The coordinate map -/

/-- The pullback `Φ^*a` of a field of real two-forms along a map `Φ`:
`(Φ^*a)(w)(u, v) = a(Φ w)(DΦ(w) u, DΦ(w) v)`. -/
def pullbackField (Φ : ComplexModel n → ComplexModel n)
    (a : ComplexModel n → CoordinateRealTwoForm n) (w : ComplexModel n) : CoordinateRealTwoForm n :=
  (a (Φ w)).compContinuousLinearMap (fderiv ℝ Φ w)

/-- The quadratic coordinate map `Φ(w) = z₀ + A (w - ½ c(w, w))`. -/
def normalCoord (z₀ : ComplexModel n) (A : ComplexModel n →L[ℂ] ComplexModel n)
    (c : ComplexModel n →L[ℂ] ComplexModel n →L[ℂ] ComplexModel n) (w : ComplexModel n) :
    ComplexModel n :=
  z₀ + A (w - (1 / 2 : ℂ) • c w w)

variable (z₀ : ComplexModel n) (A : ComplexModel n →L[ℂ] ComplexModel n)
  (c : ComplexModel n →L[ℂ] ComplexModel n →L[ℂ] ComplexModel n)

@[simp] theorem normalCoord_zero : normalCoord z₀ A c 0 = z₀ := by
  simp [normalCoord]

/-- `Φ` is holomorphic, with strict derivative `DΦ(w) = A ∘ (id - c(w, ·))` for symmetric `c`. -/
theorem hasStrictFDerivAt_normalCoord (hc : ∀ p u, c p u = c u p) (w : ComplexModel n) :
    HasStrictFDerivAt (normalCoord z₀ A c) (A ∘L (ContinuousLinearMap.id ℂ _ - c w)) w := by
  have hq : HasStrictFDerivAt (fun w => c w w)
      (c.precompR (ComplexModel n) w (ContinuousLinearMap.id ℂ _) +
        c.precompL (ComplexModel n) (ContinuousLinearMap.id ℂ _) w) w :=
    c.hasStrictFDerivAt_of_bilinear (hasStrictFDerivAt_id w) (hasStrictFDerivAt_id w)
  have h1 := (hasStrictFDerivAt_id w).sub (hq.const_smul (1 / 2 : ℂ))
  have h2 : HasStrictFDerivAt (normalCoord z₀ A c) (A ∘L (ContinuousLinearMap.id ℂ _ -
      (1 / 2 : ℂ) • (c.precompR (ComplexModel n) w (ContinuousLinearMap.id ℂ _) +
        c.precompL (ComplexModel n) (ContinuousLinearMap.id ℂ _) w))) w :=
    (A.hasStrictFDerivAt.comp w h1).const_add z₀
  refine h2.congr_fderiv (ContinuousLinearMap.ext fun h => ?_)
  simp only [ContinuousLinearMap.comp_apply, _root_.sub_apply,
    ContinuousLinearMap.id_apply, _root_.add_apply, _root_.smul_apply,
    ContinuousLinearMap.precompR_apply, ContinuousLinearMap.precompL_apply,
    ContinuousLinearMap.compL_apply]
  rw [hc h w]
  congr 1
  rw [← two_smul ℂ (c w h), smul_smul]
  norm_num

theorem hasFDerivAt_normalCoord (hc : ∀ p u, c p u = c u p) (w : ComplexModel n) :
    HasFDerivAt (normalCoord z₀ A c) (A ∘L (ContinuousLinearMap.id ℂ _ - c w)) w :=
  (hasStrictFDerivAt_normalCoord z₀ A c hc w).hasFDerivAt

/-- **`Φ` is a biholomorphism near `0`** when `A` is invertible: it restricts to an open partial
homeomorphism, holomorphic on its source, whose source contains `0` and whose inverse is
holomorphic on its target (a neighbourhood of `Φ(0) = z₀`). -/
theorem exists_biholomorphic_normalCoord (A : ComplexModel n ≃L[ℂ] ComplexModel n)
    (hc : ∀ p u, c p u = c u p) :
    ∃ Ψ : OpenPartialHomeomorph (ComplexModel n) (ComplexModel n),
      ⇑Ψ = normalCoord z₀ (A : ComplexModel n →L[ℂ] ComplexModel n) c ∧ 0 ∈ Ψ.source ∧
      (∀ w ∈ Ψ.source, DifferentiableAt ℂ Ψ w) ∧ ∀ z ∈ Ψ.target, DifferentiableAt ℂ Ψ.symm z := by
  set A' := (A : ComplexModel n →L[ℂ] ComplexModel n)
  have hc0 : A' ∘L (ContinuousLinearMap.id ℂ _ - c 0) = A' := by
    refine ContinuousLinearMap.ext fun u => ?_
    simp
  have hf : HasStrictFDerivAt (normalCoord z₀ A' c) A' 0 := by
    have := hasStrictFDerivAt_normalCoord z₀ A' c hc 0
    rwa [hc0] at this
  set Ψ₀ := hf.toOpenPartialHomeomorph (normalCoord z₀ A' c)
  set D : ComplexModel n → (ComplexModel n →L[ℂ] ComplexModel n) :=
    fun w => A' ∘L (ContinuousLinearMap.id ℂ _ - c w)
  have hDc : Continuous D := continuous_const.clm_comp (continuous_const.sub c.continuous)
  set V := D ⁻¹' range ((↑) : (ComplexModel n ≃L[ℂ] ComplexModel n) → _)
  have hV : IsOpen V := ContinuousLinearEquiv.isOpen.preimage hDc
  refine ⟨Ψ₀.restrOpen V hV, ?_, ?_, ?_, ?_⟩
  · rw [OpenPartialHomeomorph.coe_restrOpen]
    exact HasStrictFDerivAt.toOpenPartialHomeomorph_coe hf
  · rw [OpenPartialHomeomorph.restrOpen_source]
    refine ⟨HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source hf, A, ?_⟩
    simp only [D, hc0]; rfl
  · intro w _
    rw [OpenPartialHomeomorph.coe_restrOpen, HasStrictFDerivAt.toOpenPartialHomeomorph_coe]
    exact (hasFDerivAt_normalCoord z₀ A' c hc w).differentiableAt
  · intro z hz
    set Ψ := Ψ₀.restrOpen V hV
    have hs : Ψ.symm z ∈ Ψ.source := Ψ.map_target hz
    rw [OpenPartialHomeomorph.restrOpen_source] at hs
    obtain ⟨e, he⟩ := hs.2
    have hΨ : ⇑Ψ = normalCoord z₀ A' c := by
      rw [OpenPartialHomeomorph.coe_restrOpen]
      exact HasStrictFDerivAt.toOpenPartialHomeomorph_coe hf
    have hd : HasFDerivAt Ψ (e : ComplexModel n →L[ℂ] ComplexModel n) (Ψ.symm z) := by
      rw [hΨ, he]
      exact hasFDerivAt_normalCoord z₀ A' c hc _
    exact (Ψ.hasFDerivAt_symm hz hd).differentiableAt

theorem fderiv_normalCoord (hc : ∀ p u, c p u = c u p) (w : ComplexModel n) :
    fderiv ℝ (normalCoord z₀ A c) w =
      (A ∘L (ContinuousLinearMap.id ℂ _ - c w)).restrictScalars ℝ :=
  ((hasFDerivAt_normalCoord z₀ A c hc w).restrictScalars ℝ).fderiv

/-- The (constant) second derivative `p ↦ -A ∘ c(p, ·)` of `Φ`. -/
def normalCoordSecond : ComplexModel n →L[ℝ] (ComplexModel n →L[ℝ] ComplexModel n) :=
  ContinuousLinearMap.restrictScalarsL ℂ (ComplexModel n) (ComplexModel n) ℝ ℝ ∘L
    ((ContinuousLinearMap.compL ℂ (ComplexModel n) (ComplexModel n) (ComplexModel n) A ∘L c).restrictScalars ℝ)

theorem normalCoordSecond_apply (p u : ComplexModel n) :
    normalCoordSecond A c p u = A (c p u) := rfl

theorem hasFDerivAt_fderiv_normalCoord (hc : ∀ p u, c p u = c u p) (w : ComplexModel n) :
    HasFDerivAt (fderiv ℝ (normalCoord z₀ A c)) (-normalCoordSecond A c) w := by
  have hfun : fderiv ℝ (normalCoord z₀ A c) =
      fun w => A.restrictScalars ℝ - normalCoordSecond A c w := by
    funext w
    rw [fderiv_normalCoord z₀ A c hc]
    refine ContinuousLinearMap.ext fun u => ?_
    simp [normalCoordSecond_apply]
  rw [hfun]
  have := (hasFDerivAt_const (A.restrictScalars ℝ) w).sub (normalCoordSecond A c).hasFDerivAt
  rw [zero_sub] at this
  exact this

/-! ### Normal coordinates -/

/-- **Kähler normal coordinates (first order).**  Let `a` be a field of real two-forms near `z₀`,
differentiable at `z₀`, of type `(1,1)` near `z₀` and closed at `z₀`, and let `A` be `ℂ`-linear with
`a(z₀)(A ·, A ·) = ω₀`.  For the symmetric `c` of `normalQuad`, the pullback along
`Φ = normalCoord z₀ A c` is `ω₀` at `0` and has vanishing derivative at `0`. -/
theorem kahlerNormal_of_normalizing {a : ComplexModel n → CoordinateRealTwoForm n}
    (ha : DifferentiableAt ℝ a z₀) (h11 : ∀ᶠ z in 𝓝 z₀, IsOneOne (a z))
    (hcl : extDeriv a z₀ = 0) (hA : ∀ u v, a z₀ ![A u, A v] = flatForm n ![u, v])
    (hc : ∀ p u v, inner ℂ v (c p u) = (Real.pi : ℂ) * dHol (normalizedDeriv a z₀ A) p u v) :
    (∀ p u, c p u = c u p) ∧ pullbackField (normalCoord z₀ A c) a 0 = flatForm n ∧
      HasFDerivAt (pullbackField (normalCoord z₀ A c) a) (0 : ComplexModel n →L[ℝ] _) 0 := by
  set β := normalizedDeriv a z₀ A
  have hβ11 := normalizedDeriv_isOneOne ha h11 A
  have hβcl := normalizedDeriv_cocycle ha hcl A
  -- `c` agrees with `normalQuad β`
  have hcq : ∀ p u, c p u = normalQuad β hβ11 p u := by
    intro p u
    refine ext_inner_left ℂ fun v => ?_
    rw [hc, normalQuad_apply, inner_quadFun]
  have hsymm : ∀ p u, c p u = c u p := by
    intro p u
    rw [hcq, hcq, normalQuad_symm β hβ11 hβcl]
  have hid : (A ∘L (ContinuousLinearMap.id ℂ _ - c 0)).restrictScalars ℝ = A.restrictScalars ℝ := by
    refine ContinuousLinearMap.ext fun u => ?_
    simp
  have hD0 : fderiv ℝ (normalCoord z₀ A c) 0 = A.restrictScalars ℝ := by
    rw [fderiv_normalCoord z₀ A c hsymm, hid]
  refine ⟨hsymm, ?_, ?_⟩
  · ext m
    rw [twoForm_apply_eq_vec, pullbackField, normalCoord_zero, hD0, compContinuousLinearMap_apply_two]
    exact hA _ _
  · have hΦ : HasFDerivAt (normalCoord z₀ A c) (A.restrictScalars ℝ) 0 := by
      have := (hasFDerivAt_normalCoord z₀ A c hsymm 0).restrictScalars ℝ
      rwa [hid] at this
    have hf : HasFDerivAt (fun w => a (normalCoord z₀ A c w))
        (fderiv ℝ a z₀ ∘L A.restrictScalars ℝ) 0 := by
      have ha' : HasFDerivAt a (fderiv ℝ a z₀) (normalCoord z₀ A c 0) := by
        rw [normalCoord_zero]; exact ha.hasFDerivAt
      exact ha'.comp 0 hΦ
    have hg := hasFDerivAt_fderiv_normalCoord z₀ A c hsymm 0
    have H := hf.continuousAlternatingMapCompContinuousLinearMap hg
    refine H.congr_fderiv ?_
    rw [normalCoord_zero, hD0]
    refine ContinuousLinearMap.ext fun p => ?_
    ext m
    have hm : m = ![m 0, m 1] := by funext i; fin_cases i <;> rfl
    rw [hm]
    generalize m 0 = u
    generalize m 1 = v
    simp only [_root_.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.compContinuousLinearMapCLM_apply,
      compContinuousLinearMap_apply_two, fderivCompContinuousLinearMap_apply_two,
      _root_.neg_apply, normalCoordSecond_apply, ContinuousLinearMap.coe_restrictScalars',
      _root_.zero_apply, ContinuousAlternatingMap.coe_zero, Pi.zero_apply,
      twoForm_neg_left, twoForm_neg_right, hA]
    have key := apply_eq_flatForm_quadFun β hβ11 p u v
    rw [normalizedDeriv_apply] at key
    rw [hcq, hcq, normalQuad_apply, normalQuad_apply, key]
    ring

/-- **Existence of Kähler normal coordinates** (FPT `lem:kahler-normal-coordinates-uniform`, first
part).  Let `a` be a differentiable field of real two-forms on an open set `U ⊆ ℂⁿ`, of type `(1,1)`,
strictly positive and closed.  For every `z₀ ∈ U` there are a `ℂ`-linear isomorphism `A` and a
symmetric `ℂ`-bilinear `c` such that `Φ(w) = z₀ + A(w - ½ c(w, w))` is a biholomorphism from a
neighbourhood of `0` onto a neighbourhood of `z₀`, and the coefficient matrix of `Φ^*a` is the
identity at `0` with vanishing differential there. -/
theorem exists_kahlerNormalCoordinates {U : Set (ComplexModel n)} (hU : IsOpen U)
    {a : ComplexModel n → CoordinateRealTwoForm n} (ha : DifferentiableOn ℝ a U)
    (h11 : ∀ z ∈ U, IsOneOne (a z)) (hpos : ∀ z ∈ U, IsStrictlyPositive (a z))
    (hcl : ∀ z ∈ U, extDeriv a z = 0) {z₀ : ComplexModel n} (hz₀ : z₀ ∈ U) :
    ∃ (A : ComplexModel n ≃L[ℂ] ComplexModel n)
      (c : ComplexModel n →L[ℂ] ComplexModel n →L[ℂ] ComplexModel n)
      (Ψ : OpenPartialHomeomorph (ComplexModel n) (ComplexModel n)),
      (∀ p u, c p u = c u p) ∧
      ⇑Ψ = normalCoord z₀ (A : ComplexModel n →L[ℂ] ComplexModel n) c ∧ 0 ∈ Ψ.source ∧
      Ψ 0 = z₀ ∧ (∀ w ∈ Ψ.source, DifferentiableAt ℂ Ψ w) ∧
      (∀ z ∈ Ψ.target, DifferentiableAt ℂ Ψ.symm z) ∧
      pullbackField (normalCoord z₀ (A : ComplexModel n →L[ℂ] ComplexModel n) c) a 0 = flatForm n ∧
      normalizedHermitianMatrix
        (pullbackField (normalCoord z₀ (A : ComplexModel n →L[ℂ] ComplexModel n) c) a 0) = 1 ∧
      HasFDerivAt (pullbackField (normalCoord z₀ (A : ComplexModel n →L[ℂ] ComplexModel n) c) a)
        (0 : ComplexModel n →L[ℝ] CoordinateRealTwoForm n) 0 := by
  have hU0 : U ∈ 𝓝 z₀ := hU.mem_nhds hz₀
  have ha0 : DifferentiableAt ℝ a z₀ := ha.differentiableAt hU0
  have h11ev : ∀ᶠ z in 𝓝 z₀, IsOneOne (a z) := Filter.mem_of_superset hU0 fun z hz => h11 z hz
  obtain ⟨A, hA⟩ := exists_normalizing_linear (h11 z₀ hz₀) (hpos z₀ hz₀)
  set A' := (A : ComplexModel n →L[ℂ] ComplexModel n)
  set β := normalizedDeriv a z₀ A'
  have hβ11 := normalizedDeriv_isOneOne ha0 h11ev A'
  set c := normalQuad β hβ11
  have hc : ∀ p u v, inner ℂ v (c p u) = (Real.pi : ℂ) * dHol β p u v := fun p u v =>
    inner_quadFun β p u v
  obtain ⟨hsymm, h0, hd⟩ := kahlerNormal_of_normalizing z₀ A' c ha0 h11ev (hcl z₀ hz₀) hA hc
  obtain ⟨Ψ, hΨ, h0s, hΨd, hΨs⟩ := exists_biholomorphic_normalCoord z₀ c A hsymm
  refine ⟨A, c, Ψ, hsymm, hΨ, h0s, ?_, hΨd, hΨs, h0, ?_, hd⟩
  · rw [hΨ, normalCoord_zero]
  · rw [h0, normalizedHermitianMatrix_flatForm]

/-- The flat form is invariant under unitary maps; hence normalizing maps can be composed with
unitary maps (`kahlerNormal_of_normalizing` then applies to `A ∘ Q`). -/
theorem flatForm_unitary (Q : ComplexModel n →ₗᵢ[ℂ] ComplexModel n) (u v : ComplexModel n) :
    flatForm n ![Q u, Q v] = flatForm n ![u, v] := by
  rw [flatForm_apply, flatForm_apply, LinearIsometry.inner_map_map]

end SGPT.Analysis.KahlerNormal
