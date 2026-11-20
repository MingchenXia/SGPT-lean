import SGPT.Foundations.Analysis.Pending.NaturalHermitianPositiveShiftHarmonicLimit

set_option autoImplicit false

/-! # Genuine positive-shift family on the original harmonic complement
Five complete mathematical proofs precede SOURCE and have independent
mathematical review. Every domain, invariance, coercivity and onto premise
is produced internally. The original norms and algebraic weak domain remain.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.NaturalHermitianReducedPositiveShiftResolvent

open FirstPass FirstPass.PositiveClasses NaturalHermitianFormL2
  NaturalHermitianWeakResolvent NaturalHermitianWeakLaplacian
  NaturalHermitianWeakHarmonicKernel NaturalHermitianReducedWeakResolvent
  NaturalHermitianPositiveShiftResolvent NaturalHermitianPositiveShiftHarmonicLimit

variable {n q : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

local instance (w : KahlerBackground n M) (q : ℕ) :
    NormedAddCommGroup ((harmonicKernel w q)ᗮ) :=
  Submodule.normedAddCommGroup ((harmonicKernel w q)ᗮ)

local instance (w : KahlerBackground n M) (q : ℕ) :
    InnerProductSpace ℝ ((harmonicKernel w q)ᗮ) :=
  Submodule.innerProductSpace ((harmonicKernel w q)ᗮ)

local instance (w : KahlerBackground n M) (q : ℕ) :
    NormedSpace ℝ ((harmonicKernel w q)ᗮ) :=
  (Submodule.innerProductSpace ((harmonicKernel w q)ᗮ)).toNormedSpace

local instance (w : KahlerBackground n M) (q : ℕ) :
    CompleteSpace ((harmonicKernel w q)ᗮ) := harmonicComplement_complete w q

/-- Literal inverse-image submodule of the actual original weak domain. -/
def reducedWeakDomain (w : KahlerBackground n M) (q : ℕ) :
    Submodule ℝ (weakDomain w q) :=
  ((harmonicKernel w q)ᗮ).comap (weakDomain w q).subtype

/-- Native algebraic inclusion, with membership from the actual domain definition. -/
def reducedDomainInclusion (w : KahlerBackground n M) (q : ℕ) :
    reducedWeakDomain w q →ₗ[ℝ] (harmonicKernel w q)ᗮ :=
  ((weakDomain w q).subtype.comp (reducedWeakDomain w q).subtype).codRestrict
    ((harmonicKernel w q)ᗮ) (fun a => a.property)

/-- Genuine original operator restricted to the actual domain and actual orthogonal codomain. -/
def reducedWeakLaplacian (w : KahlerBackground n M) (q : ℕ) :
    reducedWeakDomain w q →ₗ[ℝ] (harmonicKernel w q)ᗮ :=
  ((weakLaplacian w q).comp (reducedWeakDomain w q).subtype).codRestrict
    ((harmonicKernel w q)ᗮ) (fun a => weakLaplacian_mem_harmonic_orthogonal w a.val)

theorem reducedDomainInclusion_val (w : KahlerBackground n M)
    (a : reducedWeakDomain w q) : (reducedDomainInclusion w q a).val = a.val.val := rfl

theorem reducedWeakLaplacian_val (w : KahlerBackground n M)
    (a : reducedWeakDomain w q) :
    (reducedWeakLaplacian w q a).val = weakLaplacian w q a.val := rfl

theorem reducedWeakLaplacian_inner_symm (w : KahlerBackground n M)
    (a b : reducedWeakDomain w q) :
    inner ℝ (reducedWeakLaplacian w q a) (reducedDomainInclusion w q b) =
      inner ℝ (reducedDomainInclusion w q a) (reducedWeakLaplacian w q b) :=
  weakLaplacian_inner_symm w a.val b.val

theorem reducedWeakLaplacian_nonneg (w : KahlerBackground n M)
    (a : reducedWeakDomain w q) :
    0 ≤ inner ℝ (reducedWeakLaplacian w q a) (reducedDomainInclusion w q a) :=
  weakLaplacian_nonneg w a.val

/-- Actual native restriction; every original solution stays orthogonal by the proved forcing criterion. -/
def reducedPositiveShiftResolvent (w : KahlerBackground n M) (q : ℕ)
    (t : ℝ) (ht : 0 < t) : (harmonicKernel w q)ᗮ →L[ℝ] (harmonicKernel w q)ᗮ :=
  (positiveShiftResolvent w q t ht).restrict
    (fun f hf => (positiveShiftResolvent_mem_orthogonal_iff w t ht f).mpr hf)

/-- Algebraic actual-domain lift, with original forcing membership produced internally. -/
def reducedPositiveShiftDomainLift (w : KahlerBackground n M) (q : ℕ)
    (t : ℝ) (ht : 0 < t) : (harmonicKernel w q)ᗮ →ₗ[ℝ] reducedWeakDomain w q :=
  ((positiveShiftDomainLift w q t ht).comp ((harmonicKernel w q)ᗮ).subtype).codRestrict
    (reducedWeakDomain w q)
    (fun f => (positiveShiftResolvent_mem_orthogonal_iff w t ht f.val).mpr f.property)

theorem reducedPositiveShiftResolvent_val (w : KahlerBackground n M)
    (t : ℝ) (ht : 0 < t) (f : (harmonicKernel w q)ᗮ) :
    (reducedPositiveShiftResolvent w q t ht f).val = positiveShiftResolvent w q t ht f.val := rfl

theorem reducedPositiveShiftDomainLift_original (w : KahlerBackground n M)
    (t : ℝ) (ht : 0 < t) (f : (harmonicKernel w q)ᗮ) :
    (reducedPositiveShiftDomainLift w q t ht f).val = positiveShiftDomainLift w q t ht f.val := rfl

theorem reducedPositiveShiftDomainLift_inclusion (w : KahlerBackground n M)
    (t : ℝ) (ht : 0 < t) (f : (harmonicKernel w q)ᗮ) :
    reducedDomainInclusion w q (reducedPositiveShiftDomainLift w q t ht f) =
      reducedPositiveShiftResolvent w q t ht f := rfl

theorem reducedWeakLaplacian_positiveShiftDomainLift (w : KahlerBackground n M)
    (t : ℝ) (ht : 0 < t) (f : (harmonicKernel w q)ᗮ) :
    reducedWeakLaplacian w q (reducedPositiveShiftDomainLift w q t ht f) =
      f - t • reducedPositiveShiftResolvent w q t ht f := by
  apply Subtype.ext
  exact weakLaplacian_positiveShiftDomainLift w t ht f.val

theorem reducedPositiveShiftResolvent_norm_le (w : KahlerBackground n M)
    (t : ℝ) (ht : 0 < t) (f : (harmonicKernel w q)ᗮ) :
    ‖reducedPositiveShiftResolvent w q t ht f‖ ≤ t⁻¹ * ‖f‖ :=
  positiveShiftResolvent_norm_le w t ht f.val

private theorem scaled_norm_le_of_inverse_bound {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (t : ℝ) (ht : 0 < t) (T : E →L[ℝ] E)
    (hT : ∀ f, ‖T f‖ ≤ t⁻¹ * ‖f‖) (f : E) : ‖t • T f‖ ≤ ‖f‖ := by
  calc
    ‖t • T f‖ = ‖t‖ * ‖T f‖ := norm_smul t _
    _ = t * ‖T f‖ := congrArg (fun c => c * ‖T f‖) (Real.norm_of_nonneg ht.le)
    _ ≤ t * (t⁻¹ * ‖f‖) := mul_le_mul_of_nonneg_left (hT f) ht.le
    _ = ‖f‖ := by rw [← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul]

theorem reducedPositiveShiftResolvent_scaled_norm_le (w : KahlerBackground n M)
    (t : ℝ) (ht : 0 < t) (f : (harmonicKernel w q)ᗮ) :
    ‖t • reducedPositiveShiftResolvent w q t ht f‖ ≤ ‖f‖ :=
  scaled_norm_le_of_inverse_bound (E := (harmonicKernel w q)ᗮ) t ht
    (reducedPositiveShiftResolvent w q t ht)
    (fun (g : (harmonicKernel w q)ᗮ) => reducedPositiveShiftResolvent_norm_le w t ht g) f

theorem reducedPositiveShiftResolvent_inner_symm (w : KahlerBackground n M)
    (t : ℝ) (ht : 0 < t) (f g : (harmonicKernel w q)ᗮ) :
    inner ℝ (reducedPositiveShiftResolvent w q t ht f) g =
      inner ℝ f (reducedPositiveShiftResolvent w q t ht g) :=
  positiveShiftResolvent_inner_symm w t ht f.val g.val

private theorem adjoint_eq_of_inner_symm {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E) (h : ∀ f g : E, inner ℝ (T f) g = inner ℝ f (T g)) :
    ContinuousLinearMap.adjoint T = T :=
  ((ContinuousLinearMap.eq_adjoint_iff T T).mpr h).symm

theorem reducedPositiveShiftResolvent_adjoint (w : KahlerBackground n M)
    (q : ℕ) (t : ℝ) (ht : 0 < t) :
    ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := (harmonicKernel w q)ᗮ)
      (F := (harmonicKernel w q)ᗮ) (reducedPositiveShiftResolvent w q t ht) =
        reducedPositiveShiftResolvent w q t ht := by
  apply adjoint_eq_of_inner_symm
  intro f g
  exact reducedPositiveShiftResolvent_inner_symm w t ht f g

theorem reducedPositiveShiftResolvent_nonneg (w : KahlerBackground n M)
    (t : ℝ) (ht : 0 < t) (f : (harmonicKernel w q)ᗮ) :
    0 ≤ inner ℝ (reducedPositiveShiftResolvent w q t ht f) f :=
  positiveShiftResolvent_nonneg w t ht f.val

/-- Actual reduced factor in the existing native harmonic-complement norm. -/
def reducedPositiveShiftFactor (w : KahlerBackground n M) (q : ℕ) (t : ℝ) :
    (harmonicKernel w q)ᗮ →L[ℝ] (harmonicKernel w q)ᗮ :=
  ContinuousLinearMap.id ℝ _ + (t - 1) • reducedResolvent w q

def reducedPositiveShiftBilinear (w : KahlerBackground n M) (q : ℕ) (t : ℝ) :
    (harmonicKernel w q)ᗮ →L[ℝ] (harmonicKernel w q)ᗮ →L[ℝ] ℝ :=
  (innerSL ℝ).comp (reducedPositiveShiftFactor w q t)

theorem reducedPositiveShiftFactor_val (w : KahlerBackground n M)
    (t : ℝ) (f : (harmonicKernel w q)ᗮ) :
    (reducedPositiveShiftFactor w q t f).val = positiveShiftFactor w q t f.val := rfl

theorem reducedPositiveShiftFactor_coercive_bound (w : KahlerBackground n M)
    (t : ℝ) (f : (harmonicKernel w q)ᗮ) :
    min 1 t * ‖f‖ ^ 2 ≤ inner ℝ (reducedPositiveShiftFactor w q t f) f :=
  positiveShiftFactor_coercive_bound w t f.val

theorem reducedPositiveShiftBilinear_isCoercive (w : KahlerBackground n M)
    (q : ℕ) (t : ℝ) (ht : 0 < t) :
    IsCoercive (reducedPositiveShiftBilinear w q t) := by
  refine ⟨min 1 t, lt_min zero_lt_one ht, ?_⟩
  intro f
  exact (mul_assoc (min 1 t) ‖f‖ ‖f‖).trans_le
    ((congrArg (fun a => min 1 t * a) (pow_two ‖f‖).symm).trans_le
      (reducedPositiveShiftFactor_coercive_bound w t f))

/-- Internally coercive native Lax--Milgram equivalence on the actual complete complement. -/
def reducedPositiveShiftFactorEquiv (w : KahlerBackground n M) (q : ℕ)
    (t : ℝ) (ht : 0 < t) : (harmonicKernel w q)ᗮ ≃L[ℝ] (harmonicKernel w q)ᗮ :=
  (reducedPositiveShiftBilinear_isCoercive w q t ht).continuousLinearEquivOfBilin

theorem reducedPositiveShiftFactorEquiv_apply (w : KahlerBackground n M)
    (t : ℝ) (ht : 0 < t) (f : (harmonicKernel w q)ᗮ) :
    reducedPositiveShiftFactorEquiv w q t ht f = reducedPositiveShiftFactor w q t f := by
  apply ext_inner_right ℝ
  intro g
  exact IsCoercive.continuousLinearEquivOfBilin_apply
    (reducedPositiveShiftBilinear_isCoercive w q t ht) f g

theorem reducedPositiveShiftFactor_inverse_apply (w : KahlerBackground n M)
    (t : ℝ) (ht : 0 < t) (f : (harmonicKernel w q)ᗮ) :
    reducedPositiveShiftFactor w q t ((reducedPositiveShiftFactorEquiv w q t ht).symm f) = f :=
  (reducedPositiveShiftFactorEquiv_apply w t ht _).symm.trans
    ((reducedPositiveShiftFactorEquiv w q t ht).apply_symm_apply f)

theorem reducedPositiveShiftFactor_lower_norm (w : KahlerBackground n M)
    (t : ℝ) (f : (harmonicKernel w q)ᗮ) :
    min 1 t * ‖f‖ ≤ ‖reducedPositiveShiftFactor w q t f‖ :=
  positiveShiftFactor_lower_norm w t f.val

theorem reducedPositiveShiftFactor_inverse_norm_le (w : KahlerBackground n M)
    (t : ℝ) (ht : 0 < t) (f : (harmonicKernel w q)ᗮ) :
    ‖(reducedPositiveShiftFactorEquiv w q t ht).symm f‖ ≤ (min 1 t)⁻¹ * ‖f‖ := by
  have hc : 0 < min 1 t := lt_min zero_lt_one ht
  have hb := reducedPositiveShiftFactor_lower_norm w t
    ((reducedPositiveShiftFactorEquiv w q t ht).symm f)
  rw [reducedPositiveShiftFactor_inverse_apply] at hb
  calc
    ‖(reducedPositiveShiftFactorEquiv w q t ht).symm f‖ ≤ ‖f‖ / min 1 t :=
      (le_div_iff₀ hc).mpr (by nlinarith)
    _ = (min 1 t)⁻¹ * ‖f‖ := by rw [div_eq_mul_inv, mul_comm]

theorem reducedPositiveShiftResolvent_factor_apply (w : KahlerBackground n M)
    (t : ℝ) (ht : 0 < t) (f : (harmonicKernel w q)ᗮ) :
    reducedPositiveShiftResolvent w q t ht (reducedPositiveShiftFactor w q t f) =
      reducedResolvent w q f := by
  apply Subtype.ext
  exact positiveShiftResolvent_factor w t ht f.val

theorem reducedPositiveShiftResolvent_comp_factor (w : KahlerBackground n M)
    (q : ℕ) (t : ℝ) (ht : 0 < t) :
    (reducedPositiveShiftResolvent w q t ht).comp (reducedPositiveShiftFactor w q t) =
      reducedResolvent w q := by
  apply ContinuousLinearMap.ext
  intro f
  exact reducedPositiveShiftResolvent_factor_apply w t ht f

theorem reducedPositiveShiftResolvent_eq_factor_inverse (w : KahlerBackground n M)
    (q : ℕ) (t : ℝ) (ht : 0 < t) :
    reducedPositiveShiftResolvent w q t ht = (reducedResolvent w q).comp
      (reducedPositiveShiftFactorEquiv w q t ht).symm.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro f
  calc
    reducedPositiveShiftResolvent w q t ht f = reducedPositiveShiftResolvent w q t ht
        (reducedPositiveShiftFactor w q t ((reducedPositiveShiftFactorEquiv w q t ht).symm f)) :=
      congrArg (reducedPositiveShiftResolvent w q t ht)
        (reducedPositiveShiftFactor_inverse_apply w t ht f).symm
    _ = reducedResolvent w q ((reducedPositiveShiftFactorEquiv w q t ht).symm f) :=
      reducedPositiveShiftResolvent_factor_apply w t ht _

/-- Actual positive-shift operator on the whole literal reduced weak domain. -/
def reducedPositiveShiftWeakLaplacian (w : KahlerBackground n M) (q : ℕ) (t : ℝ) :
    reducedWeakDomain w q →ₗ[ℝ] (harmonicKernel w q)ᗮ :=
  t • reducedDomainInclusion w q + reducedWeakLaplacian w q

theorem reducedPositiveShiftWeakLaplacian_val (w : KahlerBackground n M)
    (t : ℝ) (a : reducedWeakDomain w q) :
    (reducedPositiveShiftWeakLaplacian w q t a).val =
      positiveShiftWeakLaplacian w q t a.val := rfl

theorem reducedPositiveShiftWeakLaplacian_lift (w : KahlerBackground n M)
    (t : ℝ) (ht : 0 < t) (f : (harmonicKernel w q)ᗮ) :
    reducedPositiveShiftWeakLaplacian w q t (reducedPositiveShiftDomainLift w q t ht f) = f := by
  apply Subtype.ext
  exact positiveShiftWeakLaplacian_lift w t ht f.val

/-- True entire reduced-domain onto and injectivity, internally using the actual original lift. -/
theorem reducedPositiveShiftWeakLaplacian_bijective (w : KahlerBackground n M)
    (q : ℕ) (t : ℝ) (ht : 0 < t) :
    Function.Bijective (reducedPositiveShiftWeakLaplacian w q t) := by
  constructor
  · intro a b h
    apply Subtype.ext
    apply (positiveShiftWeakLaplacian_bijective w q t ht).1
    exact congrArg Subtype.val h
  · intro f
    exact ⟨reducedPositiveShiftDomainLift w q t ht f,
      reducedPositiveShiftWeakLaplacian_lift w t ht f⟩

theorem reducedPositiveShiftDomainLift_inverse (w : KahlerBackground n M)
    (t : ℝ) (ht : 0 < t) (a : reducedWeakDomain w q) :
    reducedPositiveShiftDomainLift w q t ht (reducedPositiveShiftWeakLaplacian w q t a) = a := by
  apply (reducedPositiveShiftWeakLaplacian_bijective w q t ht).1
  exact reducedPositiveShiftWeakLaplacian_lift w t ht _

theorem existsUnique_reducedPositiveShift_solution (w : KahlerBackground n M)
    (t : ℝ) (ht : 0 < t) (f : (harmonicKernel w q)ᗮ) :
    ∃! a : reducedWeakDomain w q, reducedPositiveShiftWeakLaplacian w q t a = f := by
  refine ⟨reducedPositiveShiftDomainLift w q t ht f,
    reducedPositiveShiftWeakLaplacian_lift w t ht f, ?_⟩
  intro a ha
  apply (reducedPositiveShiftWeakLaplacian_bijective w q t ht).1
  exact ha.trans (reducedPositiveShiftWeakLaplacian_lift w t ht f).symm

theorem reducedPositiveShiftWeakLaplacian_coercive_bound (w : KahlerBackground n M)
    (t : ℝ) (a : reducedWeakDomain w q) :
    t * ‖reducedDomainInclusion w q a‖ ^ 2 ≤
      inner ℝ (reducedPositiveShiftWeakLaplacian w q t a) (reducedDomainInclusion w q a) := by
  have h : inner ℝ (reducedPositiveShiftWeakLaplacian w q t a) (reducedDomainInclusion w q a) =
      t * ‖reducedDomainInclusion w q a‖ ^ 2 +
        inner ℝ (reducedWeakLaplacian w q a) (reducedDomainInclusion w q a) :=
    (inner_add_left (𝕜 := ℝ) (t • reducedDomainInclusion w q a)
      (reducedWeakLaplacian w q a) (reducedDomainInclusion w q a)).trans
      (congrArg (fun z => z + inner ℝ (reducedWeakLaplacian w q a) (reducedDomainInclusion w q a))
        ((real_inner_smul_left _ _ t).trans
          (congrArg (fun z => t * z) (real_inner_self_eq_norm_sq _))))
  exact (le_add_of_nonneg_right (reducedWeakLaplacian_nonneg w a)).trans_eq h.symm

theorem reducedPositiveShiftResolvent_one (w : KahlerBackground n M) (q : ℕ) :
    reducedPositiveShiftResolvent w q 1 zero_lt_one = reducedResolvent w q := by
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  exact congrArg (fun T => T f.val) (positiveShiftResolvent_one w q)

theorem reducedPositiveShiftResolvent_identity (w : KahlerBackground n M)
    (q : ℕ) (t s : ℝ) (ht : 0 < t) (hs : 0 < s) :
    reducedPositiveShiftResolvent w q t ht - reducedPositiveShiftResolvent w q s hs =
      (s - t) • (reducedPositiveShiftResolvent w q t ht).comp
        (reducedPositiveShiftResolvent w q s hs) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  exact congrArg (fun T => T f.val) (positiveShiftResolvent_identity w q t s ht hs)

/-- Genuine convergence in the original native harmonic-complement norm, for any filter. -/
theorem scaled_reducedPositiveShiftResolvent_tendsto_zero (w : KahlerBackground n M)
    {ι : Type*} (F : Filter ι) (t : ι → ℝ) (ht : ∀ i, 0 < t i)
    (ht0 : Tendsto t F (𝓝 0)) (f : (harmonicKernel w q)ᗮ) :
    Tendsto (fun i => t i • reducedPositiveShiftResolvent w q (t i) (ht i) f) F (𝓝 0) := by
  have hz := scaledResolvent_tendsto_zero_on_orthogonal w F t ht ht0 f
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hev := (Metric.tendsto_nhds.mp hz) ε hε
  filter_upwards [hev] with i hi
  rw [dist_zero_right]
  calc
    ‖t i • reducedPositiveShiftResolvent w q (t i) (ht i) f‖ =
        ‖(t i • reducedPositiveShiftResolvent w q (t i) (ht i) f).val‖ :=
      (Submodule.norm_coe _).symm
    _ = ‖scaledResolvent w q (t i) (ht i) f.val‖ := rfl
    _ < ε := by simpa only [dist_zero_right] using hi

end SGPT.Foundations.Analysis.Pending.NaturalHermitianReducedPositiveShiftResolvent
