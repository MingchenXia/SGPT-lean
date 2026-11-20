import SGPT.Foundations.Analysis.Pending.NaturalHermitianWeakLaplacian
import Mathlib.Analysis.InnerProductSpace.LaxMilgram

set_option autoImplicit false

/-! # Genuine original weak resolvents at every positive real shift
All six entire mathematical proofs precede SOURCE. The actual shift
factor is internally coercive on the original Hilbert space; its native
Lax--Milgram equivalence produces the bounded inverse. No coercivity,
inverse, onto, compactness or Green certificate is a caller input.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.NaturalHermitianPositiveShiftResolvent

open FirstPass FirstPass.PositiveClasses NaturalHermitianFormL2
  NaturalHermitianGraphEnergy NaturalHermitianWeakResolvent
  NaturalHermitianWeakLaplacian

variable {n q : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- The literal shift factor, on the original Hilbert norm. -/
def positiveShiftFactor (w : KahlerBackground n M) (q : ℕ) (t : ℝ) :
    HilbertFormL2 w.form.val w.isKahler.1 q →L[ℝ]
      HilbertFormL2 w.form.val w.isKahler.1 q :=
  ContinuousLinearMap.id ℝ _ + (t - 1) • shiftedWeakResolvent w q

/-- Actual bounded bilinear form of the internally constructed factor. -/
def positiveShiftBilinear (w : KahlerBackground n M) (q : ℕ) (t : ℝ) :
    HilbertFormL2 w.form.val w.isKahler.1 q →L[ℝ]
      HilbertFormL2 w.form.val w.isKahler.1 q →L[ℝ] ℝ :=
  (innerSL ℝ).comp (positiveShiftFactor w q t)

theorem positiveShiftFactor_apply (w : KahlerBackground n M) (t : ℝ)
    (f : HilbertFormL2 w.form.val w.isKahler.1 q) :
    positiveShiftFactor w q t f = f + (t - 1) • shiftedWeakResolvent w q f := rfl

theorem positiveShiftBilinear_apply (w : KahlerBackground n M) (t : ℝ)
    (f g : HilbertFormL2 w.form.val w.isKahler.1 q) :
    positiveShiftBilinear w q t f g = inner ℝ (positiveShiftFactor w q t f) g := rfl

theorem positiveShiftFactor_inner_self (w : KahlerBackground n M) (t : ℝ)
    (f : HilbertFormL2 w.form.val w.isKahler.1 q) :
    inner ℝ (positiveShiftFactor w q t f) f =
      ‖f‖ ^ 2 + (t - 1) * inner ℝ (shiftedWeakResolvent w q f) f := by
  exact (inner_add_left (𝕜 := ℝ) f ((t - 1) • shiftedWeakResolvent w q f) f).trans
    (congrArg₂ (fun a b : ℝ => a + b) (real_inner_self_eq_norm_sq f)
      (real_inner_smul_left (shiftedWeakResolvent w q f) f (t - 1)))

/-- Coercivity of the actual factor is derived from genuine original positivity and contraction. -/
theorem positiveShiftFactor_coercive_bound (w : KahlerBackground n M) (t : ℝ)
    (f : HilbertFormL2 w.form.val w.isKahler.1 q) :
    min 1 t * ‖f‖ ^ 2 ≤ inner ℝ (positiveShiftFactor w q t f) f := by
  have h0 := shiftedWeakResolvent_nonneg w f
  have h1 : inner ℝ (shiftedWeakResolvent w q f) f ≤ ‖f‖ ^ 2 := by
    calc
      inner ℝ (shiftedWeakResolvent w q f) f ≤ ‖shiftedWeakResolvent w q f‖ * ‖f‖ :=
        real_inner_le_norm (shiftedWeakResolvent w q f) f
      _ ≤ ‖f‖ * ‖f‖ := mul_le_mul_of_nonneg_right (shiftedWeakResolvent_norm_le w f)
        (norm_nonneg f)
      _ = ‖f‖ ^ 2 := (pow_two ‖f‖).symm
  rw [positiveShiftFactor_inner_self]
  by_cases ht : 1 ≤ t
  · rw [min_eq_left ht]
    have hterm := mul_nonneg (sub_nonneg.mpr ht) h0
    nlinarith
  · rw [min_eq_right (le_of_not_ge ht)]
    have hterm := mul_le_mul_of_nonpos_left h1 (sub_nonpos.mpr (le_of_not_ge ht))
    nlinarith

/-- The native coercivity premise is produced internally, with an explicit positive constant. -/
theorem positiveShiftBilinear_isCoercive (w : KahlerBackground n M) (q : ℕ)
    (t : ℝ) (ht : 0 < t) : IsCoercive (positiveShiftBilinear w q t) := by
  refine ⟨min 1 t, lt_min zero_lt_one ht, ?_⟩
  intro f
  simpa only [positiveShiftBilinear_apply, pow_two, mul_assoc] using
    positiveShiftFactor_coercive_bound w t f

/-- Genuine native Lax--Milgram equivalence of the original factor. -/
def positiveShiftFactorEquiv (w : KahlerBackground n M) (q : ℕ)
    (t : ℝ) (ht : 0 < t) :
    HilbertFormL2 w.form.val w.isKahler.1 q ≃L[ℝ]
      HilbertFormL2 w.form.val w.isKahler.1 q :=
  (positiveShiftBilinear_isCoercive w q t ht).continuousLinearEquivOfBilin

theorem positiveShiftFactorEquiv_apply (w : KahlerBackground n M)
    (t : ℝ) (ht : 0 < t) (f : HilbertFormL2 w.form.val w.isKahler.1 q) :
    positiveShiftFactorEquiv w q t ht f = positiveShiftFactor w q t f := by
  apply ext_inner_right ℝ
  intro g
  exact IsCoercive.continuousLinearEquivOfBilin_apply
    (positiveShiftBilinear_isCoercive w q t ht) f g

theorem positiveShiftFactor_bijective (w : KahlerBackground n M) (q : ℕ)
    (t : ℝ) (ht : 0 < t) : Function.Bijective (positiveShiftFactor w q t) := by
  have heq : (positiveShiftFactor w q t :
      HilbertFormL2 w.form.val w.isKahler.1 q → HilbertFormL2 w.form.val w.isKahler.1 q) =
      positiveShiftFactorEquiv w q t ht :=
    (funext (positiveShiftFactorEquiv_apply w t ht)).symm
  rw [heq]
  exact (positiveShiftFactorEquiv w q t ht).bijective

theorem positiveShiftFactor_inverse_apply (w : KahlerBackground n M)
    (t : ℝ) (ht : 0 < t) (f : HilbertFormL2 w.form.val w.isKahler.1 q) :
    positiveShiftFactor w q t ((positiveShiftFactorEquiv w q t ht).symm f) = f :=
  (positiveShiftFactorEquiv_apply w t ht _).symm.trans
    ((positiveShiftFactorEquiv w q t ht).apply_symm_apply f)

theorem positiveShiftFactor_lower_norm (w : KahlerBackground n M)
    (t : ℝ) (f : HilbertFormL2 w.form.val w.isKahler.1 q) :
    min 1 t * ‖f‖ ≤ ‖positiveShiftFactor w q t f‖ := by
  by_cases hf : ‖f‖ = 0
  · simp [hf]
  · have hp : 0 < ‖f‖ := lt_of_le_of_ne (norm_nonneg f) (Ne.symm hf)
    apply (mul_le_mul_iff_left₀ hp).mp
    calc
      (min 1 t * ‖f‖) * ‖f‖ = min 1 t * ‖f‖ ^ 2 := by ring
      _ ≤ inner ℝ (positiveShiftFactor w q t f) f := positiveShiftFactor_coercive_bound w t f
      _ ≤ ‖positiveShiftFactor w q t f‖ * ‖f‖ :=
        real_inner_le_norm (positiveShiftFactor w q t f) f

theorem positiveShiftFactor_inverse_norm_le (w : KahlerBackground n M)
    (t : ℝ) (ht : 0 < t) (f : HilbertFormL2 w.form.val w.isKahler.1 q) :
    ‖(positiveShiftFactorEquiv w q t ht).symm f‖ ≤ (min 1 t)⁻¹ * ‖f‖ := by
  have hc : 0 < min 1 t := lt_min zero_lt_one ht
  have hb := positiveShiftFactor_lower_norm w t ((positiveShiftFactorEquiv w q t ht).symm f)
  rw [positiveShiftFactor_inverse_apply] at hb
  calc
    ‖(positiveShiftFactorEquiv w q t ht).symm f‖ ≤ ‖f‖ / min 1 t :=
      (le_div_iff₀ hc).mpr (by nlinarith)
    _ = (min 1 t)⁻¹ * ‖f‖ := by rw [div_eq_mul_inv, mul_comm]

local instance (w : KahlerBackground n M) (q : ℕ) : NormedAddCommGroup (GraphEnergy w q) :=
  Submodule.normedAddCommGroup (graphEnergySubmodule w q)

local instance (w : KahlerBackground n M) (q : ℕ) : InnerProductSpace ℝ (GraphEnergy w q) :=
  Submodule.innerProductSpace (graphEnergySubmodule w q)

local instance (w : KahlerBackground n M) (q : ℕ) : CompleteSpace (GraphEnergy w q) :=
  graphEnergy_complete w q

/-- Actual bounded inverse at every positive shift. -/
def positiveShiftResolvent (w : KahlerBackground n M) (q : ℕ) (t : ℝ) (ht : 0 < t) :
    HilbertFormL2 w.form.val w.isKahler.1 q →L[ℝ]
      HilbertFormL2 w.form.val w.isKahler.1 q :=
  (shiftedWeakResolvent w q).comp (positiveShiftFactorEquiv w q t ht).symm.toContinuousLinearMap

/-- The corresponding genuine solution in the original complete graph space. -/
def positiveShiftEnergySolution (w : KahlerBackground n M) (q : ℕ) (t : ℝ) (ht : 0 < t) :
    HilbertFormL2 w.form.val w.isKahler.1 q →L[ℝ] GraphEnergy w q :=
  (energySolution w q).comp (positiveShiftFactorEquiv w q t ht).symm.toContinuousLinearMap

/-- Actual algebraic lift to the original range domain. -/
def positiveShiftDomainLift (w : KahlerBackground n M) (q : ℕ) (t : ℝ) (ht : 0 < t) :
    HilbertFormL2 w.form.val w.isKahler.1 q →ₗ[ℝ] weakDomain w q :=
  (resolventRangeEquiv w q).toLinearMap.comp (positiveShiftFactorEquiv w q t ht).symm.toLinearMap

theorem positiveShiftDomainLift_val (w : KahlerBackground n M) (t : ℝ) (ht : 0 < t)
    (f : HilbertFormL2 w.form.val w.isKahler.1 q) :
    (positiveShiftDomainLift w q t ht f).val = positiveShiftResolvent w q t ht f := rfl

theorem positiveShiftEnergySolution_inclusion (w : KahlerBackground n M)
    (t : ℝ) (ht : 0 < t) (f : HilbertFormL2 w.form.val w.isKahler.1 q) :
    energyInclusion w q (positiveShiftEnergySolution w q t ht f) =
      positiveShiftResolvent w q t ht f := rfl

theorem weakLaplacian_positiveShiftDomainLift (w : KahlerBackground n M)
    (t : ℝ) (ht : 0 < t) (f : HilbertFormL2 w.form.val w.isKahler.1 q) :
    weakLaplacian w q (positiveShiftDomainLift w q t ht f) =
      f - t • positiveShiftResolvent w q t ht f := by
  let b := (positiveShiftFactorEquiv w q t ht).symm f
  change weakLaplacian w q (resolventRangeEquiv w q b) = f - t • shiftedWeakResolvent w q b
  rw [weakLaplacian_resolvent, ← positiveShiftFactor_inverse_apply w t ht f,
    positiveShiftFactor_apply, sub_smul, one_smul]
  abel

theorem positiveShift_pair_mem_weakGraph (w : KahlerBackground n M)
    (t : ℝ) (ht : 0 < t) (f : HilbertFormL2 w.form.val w.isKahler.1 q) :
    (positiveShiftResolvent w q t ht f, f - t • positiveShiftResolvent w q t ht f) ∈
      weakGraph w q := by
  exact (mem_weakGraph_iff_domain w _ _).mpr
    ⟨positiveShiftDomainLift w q t ht f, rfl, weakLaplacian_positiveShiftDomainLift w t ht f⟩

/-- Literal t times the native inclusion plus the original range-domain operator. -/
def positiveShiftWeakLaplacian (w : KahlerBackground n M) (q : ℕ) (t : ℝ) :
    weakDomain w q →ₗ[ℝ] HilbertFormL2 w.form.val w.isKahler.1 q :=
  t • (weakDomain w q).subtype + weakLaplacian w q

theorem positiveShiftWeakLaplacian_factor (w : KahlerBackground n M)
    (t : ℝ) (a : weakDomain w q) :
    positiveShiftWeakLaplacian w q t a =
      positiveShiftFactor w q t ((resolventRangeEquiv w q).symm a) := by
  let b := (resolventRangeEquiv w q).symm a
  have hb : shiftedWeakResolvent w q b = a.val := resolventRangeEquiv_symm_apply w a
  change t • a.val + (b - a.val) = positiveShiftFactor w q t b
  rw [positiveShiftFactor_apply, hb, sub_smul, one_smul]
  abel

/-- Actual onto and injectivity for every positive shift, with no caller range certificate. -/
theorem positiveShiftWeakLaplacian_bijective (w : KahlerBackground n M) (q : ℕ)
    (t : ℝ) (ht : 0 < t) : Function.Bijective (positiveShiftWeakLaplacian w q t) := by
  have heq : (positiveShiftWeakLaplacian w q t : weakDomain w q →
      HilbertFormL2 w.form.val w.isKahler.1 q) =
      (positiveShiftFactor w q t) ∘ (resolventRangeEquiv w q).symm :=
    funext (positiveShiftWeakLaplacian_factor w t)
  rw [heq]
  exact (positiveShiftFactor_bijective w q t ht).comp (resolventRangeEquiv w q).symm.bijective

theorem positiveShiftWeakLaplacian_lift (w : KahlerBackground n M)
    (t : ℝ) (ht : 0 < t) (f : HilbertFormL2 w.form.val w.isKahler.1 q) :
    positiveShiftWeakLaplacian w q t (positiveShiftDomainLift w q t ht f) = f := by
  change t • positiveShiftResolvent w q t ht f +
    weakLaplacian w q (positiveShiftDomainLift w q t ht f) = f
  rw [weakLaplacian_positiveShiftDomainLift, add_sub_cancel]

theorem positiveShiftDomainLift_inverse (w : KahlerBackground n M)
    (t : ℝ) (ht : 0 < t) (a : weakDomain w q) :
    positiveShiftDomainLift w q t ht (positiveShiftWeakLaplacian w q t a) = a := by
  apply (positiveShiftWeakLaplacian_bijective w q t ht).1
  exact positiveShiftWeakLaplacian_lift w t ht _

theorem existsUnique_positiveShift_weakLaplacian_solution (w : KahlerBackground n M)
    (t : ℝ) (ht : 0 < t) (f : HilbertFormL2 w.form.val w.isKahler.1 q) :
    ∃! a : weakDomain w q, positiveShiftWeakLaplacian w q t a = f := by
  refine ⟨positiveShiftDomainLift w q t ht f, positiveShiftWeakLaplacian_lift w t ht f, ?_⟩
  intro a ha
  exact (positiveShiftWeakLaplacian_bijective w q t ht).1
    (ha.trans (positiveShiftWeakLaplacian_lift w t ht f).symm)

/-- Whole original three-coordinate weak equation at every positive shift. -/
theorem positiveShiftEnergySolution_weak_equation (w : KahlerBackground n M)
    (t : ℝ) (ht : 0 < t) (f : HilbertFormL2 w.form.val w.isKahler.1 q) (v : GraphEnergy w q) :
    t * inner ℝ (energyInclusion w q (positiveShiftEnergySolution w q t ht f))
        (energyInclusion w q v) +
      inner ℝ (energyDerivative w q (positiveShiftEnergySolution w q t ht f))
        (energyDerivative w q v) +
      inner ℝ (energyCoderivative w q (positiveShiftEnergySolution w q t ht f))
        (energyCoderivative w q v) = inner ℝ f (energyInclusion w q v) := by
  let b := (positiveShiftFactorEquiv w q t ht).symm f
  have he := energySolution_weak_equation w b v
  change inner ℝ (shiftedWeakResolvent w q b) (energyInclusion w q v) +
    inner ℝ (energyDerivative w q (energySolution w q b)) (energyDerivative w q v) +
    inner ℝ (energyCoderivative w q (energySolution w q b)) (energyCoderivative w q v) =
    inner ℝ b (energyInclusion w q v) at he
  have hf := congrArg (fun a => inner ℝ a (energyInclusion w q v))
    (positiveShiftFactor_inverse_apply w t ht f)
  rw [positiveShiftFactor_apply] at hf
  change inner ℝ (b + (t - 1) • shiftedWeakResolvent w q b) (energyInclusion w q v) =
    inner ℝ f (energyInclusion w q v) at hf
  have hadd := inner_add_left (𝕜 := ℝ) b ((t - 1) • shiftedWeakResolvent w q b)
    (energyInclusion w q v)
  have hsmul := real_inner_smul_left (shiftedWeakResolvent w q b) (energyInclusion w q v) (t - 1)
  change t * inner ℝ (shiftedWeakResolvent w q b) (energyInclusion w q v) +
    inner ℝ (energyDerivative w q (energySolution w q b)) (energyDerivative w q v) +
    inner ℝ (energyCoderivative w q (energySolution w q b)) (energyCoderivative w q v) = _
  nlinarith

theorem existsUnique_positiveShift_weak_solution (w : KahlerBackground n M)
    (t : ℝ) (ht : 0 < t) (f : HilbertFormL2 w.form.val w.isKahler.1 q) :
    ∃! u : GraphEnergy w q, ∀ v : GraphEnergy w q,
      t * inner ℝ (energyInclusion w q u) (energyInclusion w q v) +
        inner ℝ (energyDerivative w q u) (energyDerivative w q v) +
        inner ℝ (energyCoderivative w q u) (energyCoderivative w q v) =
        inner ℝ f (energyInclusion w q v) := by
  refine ⟨positiveShiftEnergySolution w q t ht f,
    positiveShiftEnergySolution_weak_equation w t ht f, ?_⟩
  intro u hu
  let x : HilbertFormL2 w.form.val w.isKahler.1 q := energyInclusion w q u
  have hg : (x, f - t • x) ∈ weakGraph w q := by
    apply (mem_weakGraph_iff_weak_equation (q := q) w x _).mpr
    refine ⟨u, rfl, ?_⟩
    intro v
    have he := hu v
    change t * inner ℝ x (energyInclusion w q v) +
      inner ℝ (energyDerivative w q u) (energyDerivative w q v) +
      inner ℝ (energyCoderivative w q u) (energyCoderivative w q v) =
      inner ℝ f (energyInclusion w q v) at he
    have hs := inner_sub_left (𝕜 := ℝ) f (t • x) (energyInclusion w q v)
    have hm := real_inner_smul_left x (energyInclusion w q v) t
    nlinarith
  obtain ⟨a, ha, hy⟩ := (mem_weakGraph_iff_domain (q := q) w x _).mp hg
  have hsolve : positiveShiftWeakLaplacian w q t a = f := by
    change t • a.val + weakLaplacian w q a = f
    rw [ha, hy, add_sub_cancel]
  have heq : a = positiveShiftDomainLift w q t ht f :=
    (positiveShiftWeakLaplacian_bijective w q t ht).1
      (hsolve.trans (positiveShiftWeakLaplacian_lift w t ht f).symm)
  apply energyInclusion_injective w q
  exact ha.symm.trans ((congrArg Subtype.val heq).trans
    (positiveShiftEnergySolution_inclusion w t ht f).symm)

/-- Literal original energy, with the coefficient of the zeroth coordinate equal to the shift. -/
theorem positiveShiftEnergy_identity (w : KahlerBackground n M)
    (t : ℝ) (ht : 0 < t) (f : HilbertFormL2 w.form.val w.isKahler.1 q) :
    t * ‖positiveShiftResolvent w q t ht f‖ ^ 2 +
      ‖energyDerivative w q (positiveShiftEnergySolution w q t ht f)‖ ^ 2 +
      ‖energyCoderivative w q (positiveShiftEnergySolution w q t ht f)‖ ^ 2 =
      inner ℝ f (positiveShiftResolvent w q t ht f) := by
  have he := positiveShiftEnergySolution_weak_equation w t ht f
    (positiveShiftEnergySolution w q t ht f)
  rw [positiveShiftEnergySolution_inclusion] at he
  have hI := real_inner_self_eq_norm_sq (positiveShiftResolvent w q t ht f)
  have hD := real_inner_self_eq_norm_sq
    (energyDerivative w q (positiveShiftEnergySolution w q t ht f))
  have hC := real_inner_self_eq_norm_sq
    (energyCoderivative w q (positiveShiftEnergySolution w q t ht f))
  exact (congrArg₂ (fun a b : ℝ => a + b)
    (congrArg₂ (fun a b : ℝ => a + b) (congrArg (fun a => t * a) hI.symm) hD.symm)
      hC.symm).trans he

/-- True Hilbert symmetry follows from the actual original operator-domain symmetry. -/
theorem positiveShiftResolvent_inner_symm (w : KahlerBackground n M)
    (t : ℝ) (ht : 0 < t) (f g : HilbertFormL2 w.form.val w.isKahler.1 q) :
    inner ℝ (positiveShiftResolvent w q t ht f) g =
      inner ℝ f (positiveShiftResolvent w q t ht g) := by
  let x := positiveShiftResolvent w q t ht f
  let z := positiveShiftResolvent w q t ht g
  let a := positiveShiftDomainLift w q t ht f
  let b := positiveShiftDomainLift w q t ht g
  have hf : t • x + weakLaplacian w q a = f := positiveShiftWeakLaplacian_lift w t ht f
  have hg : t • z + weakLaplacian w q b = g := positiveShiftWeakLaplacian_lift w t ht g
  have hs : inner ℝ (weakLaplacian w q a) z = inner ℝ x (weakLaplacian w q b) :=
    weakLaplacian_inner_symm w a b
  calc
    inner ℝ x g = inner ℝ x (t • z + weakLaplacian w q b) :=
      congrArg (fun y => inner ℝ x y) hg.symm
    _ = t * inner ℝ x z + inner ℝ x (weakLaplacian w q b) :=
      (inner_add_right (𝕜 := ℝ) x (t • z) (weakLaplacian w q b)).trans
        (congrArg (fun v => v + inner ℝ x (weakLaplacian w q b))
          (real_inner_smul_right x z t))
    _ = t * inner ℝ x z + inner ℝ (weakLaplacian w q a) z :=
      congrArg (fun v => t * inner ℝ x z + v) hs.symm
    _ = inner ℝ (t • x + weakLaplacian w q a) z :=
      ((inner_add_left (𝕜 := ℝ) (t • x) (weakLaplacian w q a) z).trans
        (congrArg (fun v => v + inner ℝ (weakLaplacian w q a) z)
          (real_inner_smul_left x z t))).symm
    _ = inner ℝ f z := congrArg (fun y => inner ℝ y z) hf

private theorem adjoint_eq_of_inner_symm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (T : E →L[ℝ] E)
    (h : ∀ x y : E, inner ℝ (T x) y = inner ℝ x (T y)) :
    ContinuousLinearMap.adjoint T = T :=
  ((ContinuousLinearMap.eq_adjoint_iff T T).mpr h).symm

theorem positiveShiftResolvent_adjoint (w : KahlerBackground n M) (q : ℕ)
    (t : ℝ) (ht : 0 < t) :
    ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := HilbertFormL2 w.form.val w.isKahler.1 q)
      (F := HilbertFormL2 w.form.val w.isKahler.1 q) (positiveShiftResolvent w q t ht) =
      positiveShiftResolvent w q t ht :=
  adjoint_eq_of_inner_symm (E := HilbertFormL2 w.form.val w.isKahler.1 q)
    (positiveShiftResolvent w q t ht) (positiveShiftResolvent_inner_symm (q := q) w t ht)

theorem positiveShiftResolvent_nonneg (w : KahlerBackground n M)
    (t : ℝ) (ht : 0 < t) (f : HilbertFormL2 w.form.val w.isKahler.1 q) :
    0 ≤ inner ℝ (positiveShiftResolvent w q t ht f) f := by
  have he := positiveShiftEnergy_identity w t ht f
  have hD := sq_nonneg ‖energyDerivative w q (positiveShiftEnergySolution w q t ht f)‖
  have hC := sq_nonneg ‖energyCoderivative w q (positiveShiftEnergySolution w q t ht f)‖
  have hI := mul_nonneg ht.le (sq_nonneg ‖positiveShiftResolvent w q t ht f‖)
  have hc := real_inner_comm f (positiveShiftResolvent w q t ht f)
  linarith

/-- Sharp pointwise bound of the actual inverse at a positive shift. -/
theorem positiveShiftResolvent_norm_le (w : KahlerBackground n M)
    (t : ℝ) (ht : 0 < t) (f : HilbertFormL2 w.form.val w.isKahler.1 q) :
    ‖positiveShiftResolvent w q t ht f‖ ≤ t⁻¹ * ‖f‖ := by
  let x := positiveShiftResolvent w q t ht f
  have he := positiveShiftEnergy_identity w t ht f
  have hD := sq_nonneg ‖energyDerivative w q (positiveShiftEnergySolution w q t ht f)‖
  have hC := sq_nonneg ‖energyCoderivative w q (positiveShiftEnergySolution w q t ht f)‖
  have hs := real_inner_le_norm f x
  have hl : t * ‖x‖ ^ 2 ≤ ‖f‖ * ‖x‖ := by linarith
  by_cases hx : ‖x‖ = 0
  · exact (le_of_eq hx).trans (mul_nonneg (inv_nonneg.mpr ht.le) (norm_nonneg f))
  · have hp : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg x) (Ne.symm hx)
    have hb : t * ‖x‖ ≤ ‖f‖ := (mul_le_mul_iff_left₀ hp).mp (by nlinarith only [hl])
    calc
      ‖x‖ ≤ ‖f‖ / t := (le_div_iff₀ ht).mpr (by simpa only [mul_comm] using hb)
      _ = t⁻¹ * ‖f‖ := by rw [div_eq_mul_inv, mul_comm]

theorem positiveShiftResolvent_opNorm_le (w : KahlerBackground n M) (q : ℕ)
    (t : ℝ) (ht : 0 < t) : ‖positiveShiftResolvent w q t ht‖ ≤ t⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr ht.le)
  exact positiveShiftResolvent_norm_le w t ht

theorem positiveShiftResolvent_of_domain (w : KahlerBackground n M)
    (t : ℝ) (ht : 0 < t) (a : weakDomain w q) :
    positiveShiftResolvent w q t ht (positiveShiftWeakLaplacian w q t a) = a.val :=
  congrArg Subtype.val (positiveShiftDomainLift_inverse w t ht a)

/-- Literal unit-shift readback of the already original Riesz resolvent. -/
theorem positiveShiftResolvent_one (w : KahlerBackground n M) (q : ℕ) :
    positiveShiftResolvent w q 1 zero_lt_one = shiftedWeakResolvent w q := by
  apply ContinuousLinearMap.ext
  intro f
  let b : HilbertFormL2 w.form.val w.isKahler.1 q :=
    (positiveShiftFactorEquiv w q 1 zero_lt_one).symm f
  have hf : positiveShiftFactor w q 1 b = f :=
    positiveShiftFactor_inverse_apply w 1 zero_lt_one f
  have hb : positiveShiftFactor w q 1 b = b := by
    rw [positiveShiftFactor_apply, sub_self, zero_smul, add_zero]
  exact congrArg (shiftedWeakResolvent w q) (hb.symm.trans hf)

/-- Entire genuine resolvent identity, including equal positive shifts. -/
theorem positiveShiftResolvent_identity (w : KahlerBackground n M) (q : ℕ)
    (t s : ℝ) (ht : 0 < t) (hs : 0 < s) :
    positiveShiftResolvent w q t ht - positiveShiftResolvent w q s hs =
      (s - t) • (positiveShiftResolvent w q t ht).comp (positiveShiftResolvent w q s hs) := by
  apply ContinuousLinearMap.ext
  intro f
  let a := positiveShiftDomainLift w q s hs f
  let x := positiveShiftResolvent w q s hs f
  have ha : weakLaplacian w q a = f - s • x := weakLaplacian_positiveShiftDomainLift w s hs f
  have hb : positiveShiftWeakLaplacian w q t a = f + (t - s) • x := by
    change t • x + weakLaplacian w q a = _
    rw [ha, sub_smul]
    abel
  have hi := positiveShiftResolvent_of_domain w t ht a
  rw [hb, map_add, map_smul] at hi
  change positiveShiftResolvent w q t ht f +
    (t - s) • positiveShiftResolvent w q t ht x = x at hi
  change positiveShiftResolvent w q t ht f - x =
    (s - t) • positiveShiftResolvent w q t ht x
  have heq : positiveShiftResolvent w q t ht f =
      x - (t - s) • positiveShiftResolvent w q t ht x := eq_sub_iff_add_eq.mpr hi
  calc
    positiveShiftResolvent w q t ht f - x =
        (x - (t - s) • positiveShiftResolvent w q t ht x) - x :=
      congrArg (fun z => z - x) heq
    _ = -((t - s) • positiveShiftResolvent w q t ht x) := by abel
    _ = (s - t) • positiveShiftResolvent w q t ht x := by rw [← neg_smul, neg_sub]

end SGPT.Foundations.Analysis.Pending.NaturalHermitianPositiveShiftResolvent
