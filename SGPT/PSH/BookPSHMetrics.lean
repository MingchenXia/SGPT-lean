import SGPT.PSH.BookLineBundleMetrics
import SGPT.Foundations.Analysis.Pending.NaturalThetaPshGeometricCurrent

/-!
# Plurisubharmonic metrics on line bundles (`def:pshfunctions:L1836`, `def:tensorprodpshmetric`)

Source: chapter *Plurisubharmonic functions*, section *Plurisubharmonic metrics on line bundles*.

* `def:pshfunctions:L1836`: a psh metric `h` on `L` is a family `(h_x)` of Hermitian or singular
  Hermitian forms on the fibres such that there are a Hermitian metric `h₀` and
  `φ ∈ PSH(X, c₁(L,h₀))` with `|v|²_{h_x} = |v|²_{h₀,x} e^{-φ(x)}` for `v ≠ 0` (and `0` for
  `v = 0`); its Chern current is `c₁(L,h) = c₁(L,h₀) + ddᶜφ`. Here `c₁(L,h₀)` is the genuine
  first Chern form `firstChernForm h₀` of `def:Hermmetric`, `PSH(X,θ)` is the existing
  `IsThetaPshPotential`, and the Chern current is the existing global current `θ + ddᶜφ`
  (`thetaPotentialCurrent`, in positive dimension; there are no degree-two currents in dimension
  zero).
* `def:tensorprodpshmetric`: `(h₁ ⊗ h₂)_x = h_{1,x} ⊗ h_{2,x}` fibrewise, with the tensor product
  of `def:1dimlinspacehermten` on the complex lines `L_{1,x} ⊗ L_{2,x}`.

We also prove that the twisted family `h₀ e^{-φ}` automatically consists of Hermitian or singular
forms (`isHermitianOrSingular_twistedForm`), and that `φ` is recovered from the metric
(`twistedForm_injective`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Set Filter Bundle
open scoped Topology Manifold ContDiff ENNReal TensorProduct

namespace SGPT.PSH.LineBundleMetric

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]
  {L : X → Type*} [∀ x, AddCommGroup (L x)] [∀ x, Module ℂ (L x)] [∀ x, TopologicalSpace (L x)]
  [TopologicalSpace (TotalSpace ℂ L)] [FiberBundle ℂ L] [VectorBundle ℂ ℂ L]
  [ContMDiffVectorBundle ∞ ℂ L 𝓘(ℂ, ComplexModel n)]

/-- The family `h₀ e^{-φ}`: `|v|² = |v|²_{h₀,x} e^{-φ(x)}` for `v ≠ 0` and `0` for `v = 0`. -/
def twistedForm (h₀ : HermitianMetric (n := n) L) (φ : X → EReal) (x : X) (v : L x) : ℝ≥0∞ := by
  classical
  exact if v = 0 then 0 else ENNReal.ofReal ((h₀.form x).normSq v) * EReal.exp (-φ x)

/-- `h = h₀ e^{-φ}` with `φ ∈ PSH(X, c₁(L,h₀))`. -/
structure IsPSHMetricWith (q : (x : X) → L x → ℝ≥0∞) (h₀ : HermitianMetric (n := n) L)
    (φ : X → EReal) : Prop where
  thetaPsh : IsThetaPshPotential (firstChernForm h₀).val φ
  eq_twisted : ∀ x v, q x v = twistedForm h₀ φ x v

variable (L) in
/-- `def:pshfunctions:L1836`. A (singular) plurisubharmonic metric on `L`: every `h_x` is a
Hermitian form or the singular Hermitian form on `L_x`, and `h = h₀ e^{-φ}` for some Hermitian
metric `h₀` and some `φ ∈ PSH(X, c₁(L,h₀))`. -/
structure IsPSHMetric (q : (x : X) → L x → ℝ≥0∞) : Prop where
  fiber : ∀ x, IsHermitianOrSingular (q x)
  twist : ∃ (h₀ : HermitianMetric (n := n) L) (φ : X → EReal), IsPSHMetricWith q h₀ φ

variable (L) in
/-- `PSH(L)`, the set of plurisubharmonic metrics on `L`. -/
def pshMetrics : Set ((x : X) → L x → ℝ≥0∞) := {q | IsPSHMetric (n := n) L q}

/-- A positive real multiple of a Hermitian form. -/
def _root_.SGPT.PSH.HermitianForm.posSMul {V : Type*} [AddCommGroup V] [Module ℂ V]
    (h : HermitianForm V) {c : ℝ} (hc : 0 < c) : HermitianForm V where
  toSesq := (c : ℂ) • h.toSesq
  pos' := by
    intro v hv
    obtain ⟨r, hr, hrv⟩ := h.pos' v hv
    refine ⟨c * r, mul_pos hc hr, ?_⟩
    simp [hrv]

theorem _root_.SGPT.PSH.HermitianForm.normSq_posSMul {V : Type*} [AddCommGroup V] [Module ℂ V]
    (h : HermitianForm V) {c : ℝ} (hc : 0 < c) (v : V) :
    (h.posSMul hc).normSq v = c * h.normSq v := by
  simp [HermitianForm.normSq, HermitianForm.posSMul]

/-- Item 1 of `def:pshfunctions:L1836` follows from item 2: at a point where `φ` is finite the
form `h₀ e^{-φ}` is Hermitian, at a pole it is the singular Hermitian form. -/
theorem isHermitianOrSingular_twistedForm (h₀ : HermitianMetric (n := n) L) {φ : X → EReal}
    (hφ : ∀ x, φ x ≠ ⊤) (x : X) : IsHermitianOrSingular (twistedForm h₀ φ x) := by
  classical
  by_cases hbot : φ x = ⊥
  · right
    funext v
    by_cases hv : v = 0
    · simp [twistedForm, singularHermitianForm, hv]
    · have hpos : ENNReal.ofReal ((h₀.form x).normSq v) ≠ 0 := by
        simpa using (h₀.form x).normSq_pos hv
      simp only [twistedForm, singularHermitianForm, hv, if_false, hbot]
      rw [show -(⊥ : EReal) = ⊤ from rfl, EReal.exp_top, ENNReal.mul_top hpos]
  · left
    set a : ℝ := (φ x).toReal
    have ha : φ x = (a : EReal) := (EReal.coe_toReal (hφ x) hbot).symm
    refine ⟨(h₀.form x).posSMul (Real.exp_pos (-a)), ?_⟩
    funext v
    by_cases hv : v = 0
    · simp [twistedForm, hv, HermitianForm.toENNReal]
    · simp only [twistedForm, hv, if_false, HermitianForm.toENNReal,
        HermitianForm.normSq_posSMul, ha]
      rw [← EReal.coe_neg, EReal.exp_coe, ← ENNReal.ofReal_mul ((h₀.form x).normSq_nonneg v),
        mul_comm]

/-- The potential `φ` of `h = h₀ e^{-φ}` is determined by `h` and `h₀`. -/
theorem twistedForm_injective (h₀ : HermitianMetric (n := n) L) {φ ψ : X → EReal}
    (heq : twistedForm h₀ φ = twistedForm h₀ ψ) : φ = ψ := by
  classical
  funext x
  obtain ⟨v, hv⟩ : ∃ v : L x, v ≠ 0 := by
    have : Nontrivial (L x) := Module.nontrivial_of_finrank_eq_succ (finrank_fiber x)
    exact exists_ne 0
  have h1 := congrFun (congrFun heq x) v
  simp only [twistedForm, hv, if_false] at h1
  have hpos : ENNReal.ofReal ((h₀.form x).normSq v) ≠ 0 := by
    simpa using (h₀.form x).normSq_pos hv
  have h2 := (ENNReal.mul_right_inj hpos ENNReal.ofReal_ne_top).mp h1
  have h3 := EReal.exp_strictMono.injective h2
  exact neg_injective h3

/-- A psh metric is a psh metric with respect to the reference data of its twist. -/
theorem IsPSHMetric.of_with {q : (x : X) → L x → ℝ≥0∞} {h₀ : HermitianMetric (n := n) L}
    {φ : X → EReal} (h : IsPSHMetricWith q h₀ φ) : IsPSHMetric (n := n) L q := by
  refine ⟨fun x => ?_, ⟨h₀, φ, h⟩⟩
  have hq : q x = twistedForm h₀ φ x := funext (h.eq_twisted x)
  rw [hq]
  exact isHermitianOrSingular_twistedForm h₀
    (fun y => h.thetaPsh.1.quasiPlurisubharmonic.ne_top y) x

/-- The Chern current `ddᶜh = c₁(L,h) = c₁(L,h₀) + ddᶜφ` of a psh metric presented as
`h = h₀ e^{-φ}` (positive dimension `m + 1`): the global current `θ + ddᶜφ` with
`θ = c₁(L,h₀)`. -/
def chernCurrent {m : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y]
    [IsComplexManifold (m + 1) Y]
    {E : Y → Type*} [∀ y, AddCommGroup (E y)] [∀ y, Module ℂ (E y)]
    [∀ y, TopologicalSpace (E y)] [TopologicalSpace (TotalSpace ℂ E)] [FiberBundle ℂ E]
    [VectorBundle ℂ ℂ E] [ContMDiffVectorBundle ∞ ℂ E 𝓘(ℂ, ComplexModel (m + 1))]
    (h₀ : HermitianMetric (n := m + 1) E) (φ : Y → EReal)
    (hφ : IsThetaPshPotential (firstChernForm h₀).val φ) :
    GlobalCurrent (m + 1) Y (degreeTwo (Nat.succ_pos m)) :=
  Pending.NaturalThetaPshGeometricCurrent.thetaPotentialCurrent (firstChernForm h₀).val φ hφ

/-! ### Tensor products -/

variable {L₁ L₂ : X → Type*} [∀ x, AddCommGroup (L₁ x)] [∀ x, Module ℂ (L₁ x)]
  [∀ x, TopologicalSpace (L₁ x)] [TopologicalSpace (TotalSpace ℂ L₁)] [FiberBundle ℂ L₁]
  [VectorBundle ℂ ℂ L₁] [ContMDiffVectorBundle ∞ ℂ L₁ 𝓘(ℂ, ComplexModel n)]
  [∀ x, AddCommGroup (L₂ x)] [∀ x, Module ℂ (L₂ x)]
  [∀ x, TopologicalSpace (L₂ x)] [TopologicalSpace (TotalSpace ℂ L₂)] [FiberBundle ℂ L₂]
  [VectorBundle ℂ ℂ L₂] [ContMDiffVectorBundle ∞ ℂ L₂ 𝓘(ℂ, ComplexModel n)]

/-- `def:tensorprodpshmetric`. The tensor product `h₁ ⊗ h₂` of psh metrics on `L₁` and `L₂`:
fibrewise `(h₁ ⊗ h₂)_x = h_{1,x} ⊗ h_{2,x}` on `(L₁ ⊗ L₂)_x = L_{1,x} ⊗ L_{2,x}`, in the sense of
`def:1dimlinspacehermten`. -/
def tensorMetric (h₁ : (x : X) → L₁ x → ℝ≥0∞) (h₂ : (x : X) → L₂ x → ℝ≥0∞) (x : X) :
    L₁ x ⊗[ℂ] L₂ x → ℝ≥0∞ :=
  lineFormTensor (finrank_fiber (L := L₁) x) (finrank_fiber (L := L₂) x)
    (h₁ x) (h₂ x)

/-- The fibrewise tensor product of psh metrics consists of Hermitian or singular forms and
satisfies `(h₁ ⊗ h₂)(v₁ ⊗ v₂) = h₁(v₁) h₂(v₂)`. -/
theorem tensorMetric_tmul {h₁ : (x : X) → L₁ x → ℝ≥0∞} {h₂ : (x : X) → L₂ x → ℝ≥0∞}
    (hh₁ : IsPSHMetric (n := n) L₁ h₁) (hh₂ : IsPSHMetric (n := n) L₂ h₂) (x : X)
    (v₁ : L₁ x) (v₂ : L₂ x) :
    IsHermitianOrSingular (tensorMetric h₁ h₂ x) ∧
      tensorMetric h₁ h₂ x (v₁ ⊗ₜ v₂) = h₁ x v₁ * h₂ x v₂ :=
  ⟨(hh₁.fiber x).lineFormTensor _ _ (hh₂.fiber x),
    lineFormTensor_tmul _ _ (hh₁.fiber x) (hh₂.fiber x) v₁ v₂⟩

end SGPT.PSH.LineBundleMetric
