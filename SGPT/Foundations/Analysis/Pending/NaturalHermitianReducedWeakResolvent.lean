import SGPT.Foundations.Analysis.Pending.NaturalHermitianWeakHarmonicKernel

set_option autoImplicit false

/-! # Actual shifted resolvent and defect on the genuine harmonic orthogonal complement
Four complete mathematical proofs precede SOURCE. All complement, invariance,
completeness, injectivity and range density are produced internally from the
actual original Hilbert resolvent. No compactness, closed range, onto or
Green certificate is supplied.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.NaturalHermitianReducedWeakResolvent

open FirstPass FirstPass.PositiveClasses NaturalHermitianFormL2
  NaturalHermitianWeakResolvent NaturalHermitianWeakHarmonicKernel

variable {n q : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

theorem harmonicComplement_isClosed (w : KahlerBackground n M) (q : ℕ) :
    IsClosed ((harmonicKernel w q)ᗮ : Set (HilbertFormL2 w.form.val w.isKahler.1 q)) :=
  (harmonicKernel w q).isClosed_orthogonal

theorem harmonicComplement_complete (w : KahlerBackground n M) (q : ℕ) :
    CompleteSpace ((harmonicKernel w q)ᗮ) := inferInstance

local instance (w : KahlerBackground n M) (q : ℕ) :
    NormedAddCommGroup ((harmonicKernel w q)ᗮ) :=
  Submodule.normedAddCommGroup ((harmonicKernel w q)ᗮ)

local instance (w : KahlerBackground n M) (q : ℕ) :
    InnerProductSpace ℝ ((harmonicKernel w q)ᗮ) :=
  Submodule.innerProductSpace ((harmonicKernel w q)ᗮ)

local instance (w : KahlerBackground n M) (q : ℕ) :
    CompleteSpace ((harmonicKernel w q)ᗮ) := harmonicComplement_complete w q

/-- Genuine native restriction, with original resolvent invariance produced internally. -/
def reducedResolvent (w : KahlerBackground n M) (q : ℕ) :
    (harmonicKernel w q)ᗮ →L[ℝ] (harmonicKernel w q)ᗮ :=
  (shiftedWeakResolvent w q).restrict
    (fun f hf => resolvent_mem_harmonic_orthogonal w f hf)

theorem reducedResolvent_coe (w : KahlerBackground n M) (f : (harmonicKernel w q)ᗮ) :
    (reducedResolvent w q f).val = shiftedWeakResolvent w q f.val := rfl

theorem reducedResolvent_norm_le (w : KahlerBackground n M) (f : (harmonicKernel w q)ᗮ) :
    ‖reducedResolvent w q f‖ ≤ ‖f‖ := shiftedWeakResolvent_norm_le w f.val

theorem reducedResolvent_opNorm_le_one (w : KahlerBackground n M) (q : ℕ) :
    ‖reducedResolvent w q‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  exact (reducedResolvent_norm_le w f).trans_eq (one_mul ‖f‖).symm

theorem reducedResolvent_inner_symm (w : KahlerBackground n M)
    (f g : (harmonicKernel w q)ᗮ) :
    inner ℝ (reducedResolvent w q f) g = inner ℝ f (reducedResolvent w q g) :=
  shiftedWeakResolvent_inner_symm w f.val g.val

private theorem adjoint_eq_of_inner_symm {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E) (h : ∀ f g : E, inner ℝ (T f) g = inner ℝ f (T g)) :
    ContinuousLinearMap.adjoint T = T :=
  ((ContinuousLinearMap.eq_adjoint_iff T T).mpr h).symm

theorem reducedResolvent_adjoint (w : KahlerBackground n M) (q : ℕ) :
    ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := (harmonicKernel w q)ᗮ)
      (F := (harmonicKernel w q)ᗮ) (reducedResolvent w q) = reducedResolvent w q := by
  exact adjoint_eq_of_inner_symm (E := (harmonicKernel w q)ᗮ) (reducedResolvent w q)
    (fun (f g : (harmonicKernel w q)ᗮ) => reducedResolvent_inner_symm (q := q) w f g)

theorem reducedResolvent_nonneg (w : KahlerBackground n M) (f : (harmonicKernel w q)ᗮ) :
    0 ≤ inner ℝ (reducedResolvent w q f) f := shiftedWeakResolvent_nonneg w f.val

theorem reducedResolvent_injective (w : KahlerBackground n M) (q : ℕ) :
    Function.Injective (reducedResolvent w q) := by
  intro f g h
  exact Subtype.ext (shiftedWeakResolvent_injective w q (congrArg Subtype.val h))

theorem reducedResolvent_ker (w : KahlerBackground n M) (q : ℕ) :
    (reducedResolvent w q).ker = ⊥ :=
  LinearMap.ker_eq_bot.mpr (reducedResolvent_injective w q)

private theorem denseRange_of_injective_self_adjoint {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E) (hi : Function.Injective T)
    (ha : ContinuousLinearMap.adjoint T = T) : DenseRange T := by
  have hk : T.ker = ⊥ := LinearMap.ker_eq_bot.mpr hi
  have ho : T.kerᗮ = T.range.topologicalClosure := by
    have h := T.orthogonal_ker
    rw [ha] at h
    exact h
  change Dense (T.range : Set E)
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  calc
    T.range.topologicalClosure = T.kerᗮ := ho.symm
    _ = (⊥ : Submodule ℝ E)ᗮ := congrArg Submodule.orthogonal hk
    _ = ⊤ := Submodule.bot_orthogonal_eq_top

/-- True range density, retaining the native topological closure rather than asserting closed range. -/
theorem reducedResolvent_denseRange (w : KahlerBackground n M) (q : ℕ) :
    DenseRange (reducedResolvent w q) :=
  denseRange_of_injective_self_adjoint (E := (harmonicKernel w q)ᗮ) (reducedResolvent w q)
    (reducedResolvent_injective w q) (reducedResolvent_adjoint w q)

/-- Literal identity minus the actual reduced original resolvent. -/
def reducedDefect (w : KahlerBackground n M) (q : ℕ) :
    (harmonicKernel w q)ᗮ →L[ℝ] (harmonicKernel w q)ᗮ :=
  ContinuousLinearMap.id ℝ _ - reducedResolvent w q

theorem reducedDefect_coe (w : KahlerBackground n M) (f : (harmonicKernel w q)ᗮ) :
    (reducedDefect w q f).val = f.val - shiftedWeakResolvent w q f.val := rfl

theorem reducedDefect_inner_symm (w : KahlerBackground n M)
    (f g : (harmonicKernel w q)ᗮ) :
    inner ℝ (reducedDefect w q f) g = inner ℝ f (reducedDefect w q g) := by
  exact (inner_sub_left (𝕜 := ℝ) f (reducedResolvent w q f) g).trans
    ((congrArg (fun t => inner ℝ f g - t) (reducedResolvent_inner_symm w f g)).trans
      (inner_sub_right (𝕜 := ℝ) f g (reducedResolvent w q g)).symm)

theorem reducedDefect_adjoint (w : KahlerBackground n M) (q : ℕ) :
    ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := (harmonicKernel w q)ᗮ)
      (F := (harmonicKernel w q)ᗮ) (reducedDefect w q) = reducedDefect w q := by
  exact adjoint_eq_of_inner_symm (E := (harmonicKernel w q)ᗮ) (reducedDefect w q)
    (fun (f g : (harmonicKernel w q)ᗮ) => reducedDefect_inner_symm (q := q) w f g)

theorem reducedDefect_nonneg (w : KahlerBackground n M) (f : (harmonicKernel w q)ᗮ) :
    0 ≤ inner ℝ (reducedDefect w q f) f := by
  have hbound : inner ℝ (reducedResolvent w q f) f ≤ ‖f‖ ^ 2 :=
    ((real_inner_le_norm (reducedResolvent w q f) f).trans
      (mul_le_mul_of_nonneg_right (reducedResolvent_norm_le w f) (norm_nonneg f))).trans_eq
        (pow_two ‖f‖).symm
  have heq : inner ℝ (reducedDefect w q f) f = ‖f‖ ^ 2 -
      inner ℝ (reducedResolvent w q f) f :=
    (inner_sub_left (𝕜 := ℝ) f (reducedResolvent w q f) f).trans
      (congrArg (fun t => t - inner ℝ (reducedResolvent w q f) f)
        (real_inner_self_eq_norm_sq f))
  exact (sub_nonneg.mpr hbound).trans_eq heq.symm

/-- A genuine reduced fixed vector lies internally in both original K and its orthogonal complement. -/
theorem reducedResolvent_eq_self_iff (w : KahlerBackground n M) (f : (harmonicKernel w q)ᗮ) :
    reducedResolvent w q f = f ↔ f = 0 := by
  constructor
  · intro h
    have hh : shiftedWeakResolvent w q f.val = f.val := congrArg Subtype.val h
    have hk : f.val ∈ harmonicKernel w q := (mem_harmonicKernel_iff w f.val).mpr hh
    exact Subtype.ext ((inner_self_eq_zero (𝕜 := ℝ)).mp (f.property f.val hk))
  · rintro rfl
    exact map_zero _

theorem reducedDefect_eq_zero_iff (w : KahlerBackground n M) (f : (harmonicKernel w q)ᗮ) :
    reducedDefect w q f = 0 ↔ f = 0 := by
  constructor
  · intro h
    change f - reducedResolvent w q f = 0 at h
    exact (reducedResolvent_eq_self_iff w f).mp (sub_eq_zero.mp h).symm
  · rintro rfl
    exact map_zero _

theorem reducedDefect_injective (w : KahlerBackground n M) (q : ℕ) :
    Function.Injective (reducedDefect w q) := by
  intro f g h
  apply sub_eq_zero.mp
  apply (reducedDefect_eq_zero_iff w (f - g)).mp
  exact (map_sub (reducedDefect w q) f g).trans
    ((congrArg (fun t => t - reducedDefect w q g) h).trans (sub_self _))

theorem reducedDefect_ker (w : KahlerBackground n M) (q : ℕ) :
    (reducedDefect w q).ker = ⊥ := LinearMap.ker_eq_bot.mpr (reducedDefect_injective w q)

/-- Dense actual defect range; no spectral gap, bounded inverse or onto assertion is supplied. -/
theorem reducedDefect_denseRange (w : KahlerBackground n M) (q : ℕ) :
    DenseRange (reducedDefect w q) :=
  denseRange_of_injective_self_adjoint (E := (harmonicKernel w q)ᗮ) (reducedDefect w q)
    (reducedDefect_injective w q) (reducedDefect_adjoint w q)

end SGPT.Foundations.Analysis.Pending.NaturalHermitianReducedWeakResolvent
