import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Hermitian forms on complex lines and their tensor products

Source: chapter *Plurisubharmonic functions*, section *Plurisubharmonic metrics on line bundles*:
`def:pshfunctions:L1743` (Hermitian forms and the singular Hermitian form on a
`1`-dimensional complex linear space) and `def:1dimlinspacehermten` (tensor product of two
maps `V_i → [0,∞]`, each a Hermitian form or the singular Hermitian form).

A Hermitian form is a map `h : V × V → ℂ`, `ℂ`-linear in the second variable and conjugate
linear in the first, with `h(v,v) ∈ ℝ_{>0}` for `v ≠ 0`; here it is a Mathlib sesquilinear map
`V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ` with that positivity. It is identified with its quadratic form
`v ↦ |v|_h² = h(v,v)` (`HermitianForm.normSq`): this identification is injective
(`HermitianForm.ext_normSq`, by polarization). The singular Hermitian form sends `0` to `0` and
every other vector to `∞`.

Main declarations:

* `SGPT.PSH.HermitianForm`, `SGPT.PSH.HermitianForm.normSq`, `SGPT.PSH.HermitianForm.norm`,
  `SGPT.PSH.singularHermitianForm` — `def:pshfunctions:L1743`;
* `SGPT.PSH.HermitianForm.tensor` — the usual tensor product of two Hermitian forms on complex
  lines, characterized by `(h₁ ⊗ h₂)(v₁ ⊗ v₂) = h₁(v₁) h₂(v₂)`
  (`HermitianForm.normSq_tensor_tmul`, `HermitianForm.existsUnique_tensor`);
* `SGPT.PSH.IsHermitianOrSingular`, `SGPT.PSH.lineFormTensor` — `def:1dimlinspacehermten`, with
  `lineFormTensor_tmul` (the defining formula on pure tensors, also in the singular cases) and
  `IsHermitianOrSingular.lineFormTensor` (the tensor product is again of the same kind).
-/

set_option autoImplicit false

noncomputable section

open scoped TensorProduct ComplexConjugate ENNReal
open Module

namespace SGPT.PSH

/-- `def:pshfunctions:L1743`. A *Hermitian form* on a complex linear space `V`: a map
`h : V × V → ℂ` which is `ℂ`-linear in the second variable and conjugate linear in the first,
such that `h(v,v)` is a positive real number for every `v ≠ 0`. The book uses it for
`1`-dimensional `V`. -/
structure HermitianForm (V : Type*) [AddCommGroup V] [Module ℂ V] where
  /-- The sesquilinear map `h`, conjugate linear in the first variable. -/
  toSesq : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ
  /-- `h(v,v) ∈ ℝ_{>0}` for `v ≠ 0`. -/
  pos' : ∀ v : V, v ≠ 0 → ∃ r : ℝ, 0 < r ∧ toSesq v v = (r : ℂ)

/-- `def:pshfunctions:L1743`. The *singular Hermitian form* on `V`: the map `V → {0, ∞}`
sending `0` to `0` and every other element to `∞`. -/
def singularHermitianForm (V : Type*) [AddCommGroup V] : V → ℝ≥0∞ := by
  classical
  exact fun v => if v = 0 then 0 else ⊤

namespace HermitianForm

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (h : HermitianForm V)

/-- The quadratic form `|v|_h² = h(v,v)` with which `h` is identified. -/
def normSq (v : V) : ℝ := (h.toSesq v v).re

/-- `|v|_h = √(|v|_h²)`. -/
def norm (v : V) : ℝ := Real.sqrt (h.normSq v)

theorem toSesq_self (v : V) : h.toSesq v v = (h.normSq v : ℂ) := by
  by_cases hv : v = 0
  · subst hv
    simp [normSq]
  · obtain ⟨r, _, hr⟩ := h.pos' v hv
    simp [normSq, hr]

theorem normSq_pos {v : V} (hv : v ≠ 0) : 0 < h.normSq v := by
  obtain ⟨r, hr, hr'⟩ := h.pos' v hv
  simpa [normSq, hr'] using hr

@[simp] theorem normSq_zero : h.normSq 0 = 0 := by
  simp [normSq]

theorem normSq_nonneg (v : V) : 0 ≤ h.normSq v := by
  by_cases hv : v = 0
  · simp [hv]
  · exact (h.normSq_pos hv).le

theorem normSq_eq_zero_iff (v : V) : h.normSq v = 0 ↔ v = 0 :=
  ⟨fun h0 => by_contra fun hv => (h.normSq_pos hv).ne' h0, fun hv => by simp [hv]⟩

theorem norm_sq (v : V) : h.norm v ^ 2 = h.normSq v :=
  Real.sq_sqrt (h.normSq_nonneg v)

theorem normSq_smul (c : ℂ) (v : V) : h.normSq (c • v) = ‖c‖ ^ 2 * h.normSq v := by
  have : h.toSesq (c • v) (c • v) = conj c * c * h.toSesq v v := by
    simp only [LinearMap.map_smulₛₗ₂, map_smul, smul_eq_mul]
    ring
  have h2 : (h.normSq (c • v) : ℂ) = ((‖c‖ ^ 2 * h.normSq v : ℝ) : ℂ) := by
    rw [← toSesq_self, this, toSesq_self, Complex.conj_mul']
    push_cast
    ring
  exact_mod_cast h2

/-- Polarization: a sesquilinear map is determined by its values on the diagonal. -/
theorem polarization (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (x y : V) :
    4 * B x y = B (x + y) (x + y) - B (x - y) (x - y) - Complex.I * B (x + Complex.I • y)
      (x + Complex.I • y) + Complex.I * B (x - Complex.I • y) (x - Complex.I • y) := by
  simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.map_smulₛₗ₂, map_smul, smul_eq_mul, Complex.conj_I]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The identification of a Hermitian form with its quadratic form `v ↦ |v|_h²` is injective. -/
theorem ext_normSq {h h' : HermitianForm V} (hq : h.normSq = h'.normSq) : h = h' := by
  have hs : h.toSesq = h'.toSesq := by
    apply LinearMap.ext₂
    intro x y
    have h1 := polarization h.toSesq x y
    have h2 := polarization h'.toSesq x y
    simp only [toSesq_self, hq] at h1 h2
    have : (4 : ℂ) * h.toSesq x y = 4 * h'.toSesq x y := by rw [h1, h2]
    exact mul_left_cancel₀ (by norm_num) this
  cases h
  cases h'
  simp only [mk.injEq]
  exact hs

/-- A Hermitian form, viewed as the map `V → [0, ∞]`, `v ↦ |v|_h²`. -/
def toENNReal (v : V) : ℝ≥0∞ := ENNReal.ofReal (h.normSq v)

theorem toENNReal_injective : Function.Injective (toENNReal (V := V)) := by
  intro h h' heq
  apply ext_normSq
  funext v
  have := congrFun heq v
  simp only [toENNReal] at this
  exact (ENNReal.ofReal_eq_ofReal_iff (h.normSq_nonneg v) (h'.normSq_nonneg v)).mp this

theorem toENNReal_ne_top (v : V) : h.toENNReal v ≠ ⊤ := ENNReal.ofReal_ne_top

/-! ### Complex lines -/

section Line

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- On a complex line every vector is a multiple of a fixed nonzero vector. -/
theorem exists_smul_eq_of_finrank_eq_one (hV : finrank ℂ V = 1) {e : V} (he : e ≠ 0) (w : V) :
    ∃ c : ℂ, c • e = w :=
  (finrank_eq_one_iff_of_nonzero' e he).mp hV w

end Line

/-! ### The tensor product of two Hermitian forms -/

section Tensor

variable {V₁ V₂ : Type*} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]

/-- The sesquilinear map `(x₁ ⊗ x₂, y₁ ⊗ y₂) ↦ h₁(x₁,y₁) h₂(x₂,y₂)` on `V₁ ⊗ V₂`. -/
def tensorSesq (h₁ : V₁ →ₗ⋆[ℂ] V₁ →ₗ[ℂ] ℂ) (h₂ : V₂ →ₗ⋆[ℂ] V₂ →ₗ[ℂ] ℂ) :
    V₁ ⊗[ℂ] V₂ →ₗ⋆[ℂ] V₁ ⊗[ℂ] V₂ →ₗ[ℂ] ℂ :=
  TensorProduct.lift
    { toFun := fun x₁ =>
        { toFun := fun x₂ => TensorProduct.lift ((LinearMap.mul ℂ ℂ).compl₁₂ (h₁ x₁) (h₂ x₂))
          map_add' := by
            intro a b
            apply TensorProduct.ext'
            intro y₁ y₂
            simp [mul_add]
          map_smul' := by
            intro c a
            apply TensorProduct.ext'
            intro y₁ y₂
            simp [mul_left_comm] }
      map_add' := by
        intro a b
        ext x₂ y₁ y₂
        simp
      map_smul' := by
        intro c a
        ext x₂ y₁ y₂
        simp [mul_assoc] }

@[simp] theorem tensorSesq_tmul (h₁ : V₁ →ₗ⋆[ℂ] V₁ →ₗ[ℂ] ℂ) (h₂ : V₂ →ₗ⋆[ℂ] V₂ →ₗ[ℂ] ℂ)
    (x₁ y₁ : V₁) (x₂ y₂ : V₂) :
    tensorSesq h₁ h₂ (x₁ ⊗ₜ x₂) (y₁ ⊗ₜ y₂) = h₁ x₁ y₁ * h₂ x₂ y₂ := by
  simp [tensorSesq]

/-- On complex lines the tensor product of two Hermitian forms is a Hermitian form. -/
theorem tensorSesq_pos (hV₁ : finrank ℂ V₁ = 1) (hV₂ : finrank ℂ V₂ = 1)
    (h₁ : HermitianForm V₁) (h₂ : HermitianForm V₂) (w : V₁ ⊗[ℂ] V₂) (hw : w ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ tensorSesq h₁.toSesq h₂.toSesq w w = (r : ℂ) := by
  have : FiniteDimensional ℂ V₁ := Module.finite_of_finrank_eq_succ hV₁
  have : FiniteDimensional ℂ V₂ := Module.finite_of_finrank_eq_succ hV₂
  obtain ⟨e₁, he₁⟩ := (finrank_pos_iff_exists_ne_zero (R := ℂ) (M := V₁)).mp (by omega)
  obtain ⟨e₂, he₂⟩ := (finrank_pos_iff_exists_ne_zero (R := ℂ) (M := V₂)).mp (by omega)
  have hW : finrank ℂ (V₁ ⊗[ℂ] V₂) = 1 := by
    rw [Module.finrank_tensorProduct, hV₁, hV₂]
  have hval : tensorSesq h₁.toSesq h₂.toSesq (e₁ ⊗ₜ e₂) (e₁ ⊗ₜ e₂) =
      ((h₁.normSq e₁ * h₂.normSq e₂ : ℝ) : ℂ) := by
    rw [tensorSesq_tmul, toSesq_self, toSesq_self]
    push_cast
    ring
  have hr : 0 < h₁.normSq e₁ * h₂.normSq e₂ := mul_pos (h₁.normSq_pos he₁) (h₂.normSq_pos he₂)
  have he : e₁ ⊗ₜ[ℂ] e₂ ≠ 0 := by
    intro h0
    simp only [h0, map_zero] at hval
    exact hr.ne' (by exact_mod_cast hval.symm)
  obtain ⟨c, rfl⟩ := exists_smul_eq_of_finrank_eq_one hW he w
  have hc : c ≠ 0 := by
    rintro rfl
    exact hw (zero_smul _ _)
  refine ⟨‖c‖ ^ 2 * (h₁.normSq e₁ * h₂.normSq e₂), mul_pos (by positivity) hr, ?_⟩
  rw [LinearMap.map_smulₛₗ₂, map_smul, hval]
  simp only [smul_eq_mul]
  rw [← mul_assoc, Complex.conj_mul']
  push_cast
  ring

/-- The usual tensor product `h₁ ⊗ h₂` of Hermitian forms on complex lines `V₁`, `V₂`: the
Hermitian form on `V₁ ⊗ V₂` with `h₁ ⊗ h₂ (x₁ ⊗ x₂, y₁ ⊗ y₂) = h₁(x₁,y₁) h₂(x₂,y₂)`. -/
def tensor (hV₁ : finrank ℂ V₁ = 1) (hV₂ : finrank ℂ V₂ = 1)
    (h₁ : HermitianForm V₁) (h₂ : HermitianForm V₂) : HermitianForm (V₁ ⊗[ℂ] V₂) where
  toSesq := tensorSesq h₁.toSesq h₂.toSesq
  pos' := tensorSesq_pos hV₁ hV₂ h₁ h₂

/-- The defining formula of `def:1dimlinspacehermten`, item 2:
`(h₁ ⊗ h₂)(v₁ ⊗ v₂) = h₁(v₁) h₂(v₂)` for the quadratic forms. -/
theorem normSq_tensor_tmul (hV₁ : finrank ℂ V₁ = 1) (hV₂ : finrank ℂ V₂ = 1)
    (h₁ : HermitianForm V₁) (h₂ : HermitianForm V₂) (v₁ : V₁) (v₂ : V₂) :
    (tensor hV₁ hV₂ h₁ h₂).normSq (v₁ ⊗ₜ v₂) = h₁.normSq v₁ * h₂.normSq v₂ := by
  have : ((tensor hV₁ hV₂ h₁ h₂).normSq (v₁ ⊗ₜ v₂) : ℂ) =
      ((h₁.normSq v₁ * h₂.normSq v₂ : ℝ) : ℂ) := by
    rw [← toSesq_self]
    change tensorSesq h₁.toSesq h₂.toSesq (v₁ ⊗ₜ v₂) (v₁ ⊗ₜ v₂) = _
    rw [tensorSesq_tmul, toSesq_self, toSesq_self]
    push_cast
    ring
  exact_mod_cast this

/-- Well-definedness of the tensor product: it is the unique Hermitian form on `V₁ ⊗ V₂` with
`(h₁ ⊗ h₂)(v₁ ⊗ v₂) = h₁(v₁) h₂(v₂)` for all `v₁, v₂`. -/
theorem existsUnique_tensor (hV₁ : finrank ℂ V₁ = 1) (hV₂ : finrank ℂ V₂ = 1)
    (h₁ : HermitianForm V₁) (h₂ : HermitianForm V₂) :
    ∃! H : HermitianForm (V₁ ⊗[ℂ] V₂),
      ∀ v₁ v₂, H.normSq (v₁ ⊗ₜ v₂) = h₁.normSq v₁ * h₂.normSq v₂ := by
  refine ⟨tensor hV₁ hV₂ h₁ h₂, normSq_tensor_tmul hV₁ hV₂ h₁ h₂, ?_⟩
  intro H hH
  have : FiniteDimensional ℂ V₁ := Module.finite_of_finrank_eq_succ hV₁
  have : FiniteDimensional ℂ V₂ := Module.finite_of_finrank_eq_succ hV₂
  obtain ⟨e₁, he₁⟩ := (finrank_pos_iff_exists_ne_zero (R := ℂ) (M := V₁)).mp (by omega)
  obtain ⟨e₂, he₂⟩ := (finrank_pos_iff_exists_ne_zero (R := ℂ) (M := V₂)).mp (by omega)
  apply ext_normSq
  funext w
  -- every vector of `V₁ ⊗ V₂` is a pure tensor `v₁ ⊗ e₂`
  have hspan : ∀ w : V₁ ⊗[ℂ] V₂, ∃ v₁ : V₁, v₁ ⊗ₜ e₂ = w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => exact ⟨0, TensorProduct.zero_tmul _ _⟩
    | tmul x y =>
      obtain ⟨c, rfl⟩ := exists_smul_eq_of_finrank_eq_one hV₂ he₂ y
      exact ⟨c • x, by rw [TensorProduct.smul_tmul]⟩
    | add x y hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, TensorProduct.add_tmul _ _ _⟩
  obtain ⟨v₁, rfl⟩ := hspan w
  rw [hH, normSq_tensor_tmul]

end Tensor

end HermitianForm

/-- A map `V → [0, ∞]` that is either (the quadratic form of) a Hermitian form or the singular
Hermitian form, the inputs of `def:1dimlinspacehermten`. -/
def IsHermitianOrSingular {V : Type*} [AddCommGroup V] [Module ℂ V] (q : V → ℝ≥0∞) : Prop :=
  (∃ h : HermitianForm V, q = h.toENNReal) ∨ q = singularHermitianForm V

/-- On a nonzero space the two kinds of maps are distinct. -/
theorem HermitianForm.toENNReal_ne_singular {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Nontrivial V] (h : HermitianForm V) : h.toENNReal ≠ singularHermitianForm V := by
  classical
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  intro heq
  have := congrFun heq v
  simp only [singularHermitianForm, hv, if_false] at this
  exact h.toENNReal_ne_top v this

open Classical in
/-- `def:1dimlinspacehermten`. The tensor product `h₁ ⊗ h₂ : V₁ ⊗ V₂ → [0, ∞]` of two maps
`hᵢ : Vᵢ → [0, ∞]`, each a Hermitian form or the singular Hermitian form on the complex line
`Vᵢ`: if either is singular, `h₁ ⊗ h₂` is the singular Hermitian form; otherwise it is the usual
tensor product of Hermitian forms. -/
def lineFormTensor {V₁ V₂ : Type*} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂]
    [Module ℂ V₂] (hV₁ : finrank ℂ V₁ = 1) (hV₂ : finrank ℂ V₂ = 1)
    (q₁ : V₁ → ℝ≥0∞) (q₂ : V₂ → ℝ≥0∞) : V₁ ⊗[ℂ] V₂ → ℝ≥0∞ :=
  if h : (∃ h₁ : HermitianForm V₁, q₁ = h₁.toENNReal) ∧ (∃ h₂ : HermitianForm V₂, q₂ = h₂.toENNReal)
  then (HermitianForm.tensor hV₁ hV₂ h.1.choose h.2.choose).toENNReal
  else singularHermitianForm (V₁ ⊗[ℂ] V₂)

section LineFormTensor

variable {V₁ V₂ : Type*} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
  (hV₁ : finrank ℂ V₁ = 1) (hV₂ : finrank ℂ V₂ = 1)

include hV₁ in
theorem nontrivial_of_finrank_eq_one' : Nontrivial V₁ := by
  have : FiniteDimensional ℂ V₁ := Module.finite_of_finrank_eq_succ hV₁
  exact Module.nontrivial_of_finrank_pos (R := ℂ) (by omega)

/-- Item 2: for two Hermitian forms, `h₁ ⊗ h₂` is the usual tensor product. -/
theorem lineFormTensor_hermitian (h₁ : HermitianForm V₁) (h₂ : HermitianForm V₂) :
    lineFormTensor hV₁ hV₂ h₁.toENNReal h₂.toENNReal =
      (HermitianForm.tensor hV₁ hV₂ h₁ h₂).toENNReal := by
  classical
  have hex : (∃ h : HermitianForm V₁, h₁.toENNReal = h.toENNReal) ∧
      (∃ h : HermitianForm V₂, h₂.toENNReal = h.toENNReal) := ⟨⟨h₁, rfl⟩, ⟨h₂, rfl⟩⟩
  unfold lineFormTensor
  rw [dif_pos hex]
  have e₁ := HermitianForm.toENNReal_injective hex.1.choose_spec
  have e₂ := HermitianForm.toENNReal_injective hex.2.choose_spec
  rw [← e₁, ← e₂]

/-- Item 1: if the first map is singular, so is the tensor product. -/
theorem lineFormTensor_singular_left (q₂ : V₂ → ℝ≥0∞) :
    lineFormTensor hV₁ hV₂ (singularHermitianForm V₁) q₂ =
      singularHermitianForm (V₁ ⊗[ℂ] V₂) := by
  classical
  have := nontrivial_of_finrank_eq_one' hV₁
  unfold lineFormTensor
  rw [dif_neg]
  rintro ⟨⟨h, hh⟩, _⟩
  exact h.toENNReal_ne_singular hh.symm

/-- Item 1: if the second map is singular, so is the tensor product. -/
theorem lineFormTensor_singular_right (q₁ : V₁ → ℝ≥0∞) :
    lineFormTensor hV₁ hV₂ q₁ (singularHermitianForm V₂) =
      singularHermitianForm (V₁ ⊗[ℂ] V₂) := by
  classical
  have := nontrivial_of_finrank_eq_one' hV₂
  unfold lineFormTensor
  rw [dif_neg]
  rintro ⟨_, ⟨h, hh⟩⟩
  exact h.toENNReal_ne_singular hh.symm

/-- The tensor product of two Hermitian-or-singular forms is again a Hermitian form or the
singular Hermitian form (well-definedness of `def:1dimlinspacehermten`). -/
theorem IsHermitianOrSingular.lineFormTensor {q₁ : V₁ → ℝ≥0∞} {q₂ : V₂ → ℝ≥0∞}
    (h₁ : IsHermitianOrSingular q₁) (h₂ : IsHermitianOrSingular q₂) :
    IsHermitianOrSingular (lineFormTensor hV₁ hV₂ q₁ q₂) := by
  rcases h₁ with ⟨h₁, rfl⟩ | rfl
  · rcases h₂ with ⟨h₂, rfl⟩ | rfl
    · exact Or.inl ⟨_, lineFormTensor_hermitian hV₁ hV₂ h₁ h₂⟩
    · exact Or.inr (lineFormTensor_singular_right hV₁ hV₂ _)
  · exact Or.inr (lineFormTensor_singular_left hV₁ hV₂ _)

omit hV₁ hV₂ in
/-- A pure tensor of nonzero vectors is nonzero. -/
theorem tmul_ne_zero_of_ne_zero {v₁ : V₁} {v₂ : V₂} (h₁ : v₁ ≠ 0) (h₂ : v₂ ≠ 0) :
    v₁ ⊗ₜ[ℂ] v₂ ≠ 0 := by
  obtain ⟨f₁, hf₁⟩ := Module.Projective.exists_dual_ne_zero ℂ h₁
  obtain ⟨f₂, hf₂⟩ := Module.Projective.exists_dual_ne_zero ℂ h₂
  intro h0
  have := congrArg (TensorProduct.lift ((LinearMap.mul ℂ ℂ).compl₁₂ f₁ f₂)) h0
  simp only [TensorProduct.lift.tmul, LinearMap.compl₁₂_apply, LinearMap.mul_apply',
    map_zero] at this
  exact mul_ne_zero hf₁ hf₂ this

omit hV₁ hV₂ in
theorem singularHermitianForm_tmul (v₁ : V₁) (v₂ : V₂) :
    singularHermitianForm (V₁ ⊗[ℂ] V₂) (v₁ ⊗ₜ v₂) =
      singularHermitianForm V₁ v₁ * singularHermitianForm V₂ v₂ := by
  classical
  by_cases h₁ : v₁ = 0
  · simp [singularHermitianForm, h₁]
  · by_cases h₂ : v₂ = 0
    · simp [singularHermitianForm, h₂]
    · simp [singularHermitianForm, h₁, h₂, tmul_ne_zero_of_ne_zero h₁ h₂]

theorem IsHermitianOrSingular.apply_zero {V : Type*} [AddCommGroup V] [Module ℂ V]
    {q : V → ℝ≥0∞} (hq : IsHermitianOrSingular q) : q 0 = 0 := by
  classical
  rcases hq with ⟨h, rfl⟩ | rfl
  · simp [HermitianForm.toENNReal]
  · simp [singularHermitianForm]

theorem IsHermitianOrSingular.apply_ne_zero {V : Type*} [AddCommGroup V] [Module ℂ V]
    {q : V → ℝ≥0∞} (hq : IsHermitianOrSingular q) {v : V} (hv : v ≠ 0) : q v ≠ 0 := by
  classical
  rcases hq with ⟨h, rfl⟩ | rfl
  · simpa [HermitianForm.toENNReal] using h.normSq_pos hv
  · simp [singularHermitianForm, hv]

/-- The formula `(h₁ ⊗ h₂)(v₁ ⊗ v₂) = h₁(v₁) h₂(v₂)` holds in `[0, ∞]` in all four cases
(with `0 · ∞ = 0`). -/
theorem lineFormTensor_tmul {q₁ : V₁ → ℝ≥0∞} {q₂ : V₂ → ℝ≥0∞}
    (h₁ : IsHermitianOrSingular q₁) (h₂ : IsHermitianOrSingular q₂) (v₁ : V₁) (v₂ : V₂) :
    lineFormTensor hV₁ hV₂ q₁ q₂ (v₁ ⊗ₜ v₂) = q₁ v₁ * q₂ v₂ := by
  classical
  -- the singular cases: both sides vanish iff `v₁ = 0` or `v₂ = 0`, and are `∞` otherwise
  have hsing : ∀ (_ : q₁ = singularHermitianForm V₁ ∨ q₂ = singularHermitianForm V₂),
      singularHermitianForm (V₁ ⊗[ℂ] V₂) (v₁ ⊗ₜ v₂) = q₁ v₁ * q₂ v₂ := by
    intro hs
    by_cases hv₁ : v₁ = 0
    · simp [singularHermitianForm, hv₁, h₁.apply_zero]
    · by_cases hv₂ : v₂ = 0
      · simp [singularHermitianForm, hv₂, h₂.apply_zero]
      · have hl : singularHermitianForm (V₁ ⊗[ℂ] V₂) (v₁ ⊗ₜ v₂) = ⊤ := by
          simp [singularHermitianForm, tmul_ne_zero_of_ne_zero hv₁ hv₂]
        rw [hl]
        rcases hs with rfl | rfl
        · have : singularHermitianForm V₁ v₁ = ⊤ := by simp [singularHermitianForm, hv₁]
          rw [this, ENNReal.top_mul (h₂.apply_ne_zero hv₂)]
        · have : singularHermitianForm V₂ v₂ = ⊤ := by simp [singularHermitianForm, hv₂]
          rw [this, ENNReal.mul_top (h₁.apply_ne_zero hv₁)]
  rcases h₁ with ⟨k₁, rfl⟩ | rfl
  · rcases h₂ with ⟨k₂, rfl⟩ | rfl
    · rw [lineFormTensor_hermitian, HermitianForm.toENNReal, HermitianForm.normSq_tensor_tmul,
        HermitianForm.toENNReal, HermitianForm.toENNReal,
        ENNReal.ofReal_mul (k₁.normSq_nonneg v₁)]
    · rw [lineFormTensor_singular_right]
      exact hsing (Or.inr rfl)
  · rw [lineFormTensor_singular_left]
    exact hsing (Or.inl rfl)

end LineFormTensor

end SGPT.PSH
