import SGPT.Foundations.Analysis.Pending.NaturalHermitianGraphEnergy
import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option autoImplicit false

/-! # A genuine Riesz shifted weak resolvent of the original joint graph
All six complete mathematical proofs precede this SOURCE. The native
adjoint is constructed from the actual complete graph-energy space;
no caller closed-operator, solution or compactness certificate is used.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.NaturalHermitianWeakResolvent

open FirstPass FirstPass.PositiveClasses NaturalHermitianFormL2
  NaturalHermitianGraphEnergy NaturalHermitianCodifferential

variable {n q : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

local instance (w : KahlerBackground n M) (q : ℕ) : NormedAddCommGroup (GraphEnergy w q) :=
  Submodule.normedAddCommGroup (graphEnergySubmodule w q)

local instance (w : KahlerBackground n M) (q : ℕ) : InnerProductSpace ℝ (GraphEnergy w q) :=
  Submodule.innerProductSpace (graphEnergySubmodule w q)

local instance (w : KahlerBackground n M) (q : ℕ) : CompleteSpace (GraphEnergy w q) :=
  graphEnergy_complete w q



/-- The actual native inverse Riesz construction on the internally complete original graph. -/
def energySolution (w : KahlerBackground n M) (q : ℕ) :
    HilbertFormL2 w.form.val w.isKahler.1 q →L[ℝ] GraphEnergy w q :=
  ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := GraphEnergy w q)
    (F := HilbertFormL2 w.form.val w.isKahler.1 q) (energyInclusion w q)

/-- The genuine shifted weak resolvent, defined from the actual graph solution. -/
def shiftedWeakResolvent (w : KahlerBackground n M) (q : ℕ) :
    HilbertFormL2 w.form.val w.isKahler.1 q →L[ℝ] HilbertFormL2 w.form.val w.isKahler.1 q :=
  (energyInclusion w q).comp (energySolution w q)

/-- Literal Riesz readback, with no supplied variational solution. -/
theorem energySolution_inner (w : KahlerBackground n M)
    (f : HilbertFormL2 w.form.val w.isKahler.1 q) (v : GraphEnergy w q) :
    inner ℝ (energySolution w q f) v = inner ℝ f (energyInclusion w q v) :=
  ContinuousLinearMap.adjoint_inner_left (𝕜 := ℝ) (E := GraphEnergy w q)
    (F := HilbertFormL2 w.form.val w.isKahler.1 q) (energyInclusion w q) v f

/-- The entire actual three-coordinate weak equation holds on the genuine graph domain. -/
theorem energySolution_weak_equation (w : KahlerBackground n M)
    (f : HilbertFormL2 w.form.val w.isKahler.1 q) (v : GraphEnergy w q) :
    inner ℝ (energyInclusion w q (energySolution w q f)) (energyInclusion w q v) +
      inner ℝ (energyDerivative w q (energySolution w q f)) (energyDerivative w q v) +
      inner ℝ (energyCoderivative w q (energySolution w q f)) (energyCoderivative w q v) =
      inner ℝ f (energyInclusion w q v) :=
  (energy_inner w (energySolution w q f) v).symm.trans (energySolution_inner w f v)

/-- True unique existence on the internally constructed actual domain, for every original Hilbert datum. -/
theorem existsUnique_weak_solution (w : KahlerBackground n M)
    (f : HilbertFormL2 w.form.val w.isKahler.1 q) :
    ∃! u : GraphEnergy w q, ∀ v : GraphEnergy w q,
      inner ℝ (energyInclusion w q u) (energyInclusion w q v) +
        inner ℝ (energyDerivative w q u) (energyDerivative w q v) +
        inner ℝ (energyCoderivative w q u) (energyCoderivative w q v) =
        inner ℝ f (energyInclusion w q v) := by
  refine ⟨energySolution w q f, energySolution_weak_equation w f, ?_⟩
  intro u hu
  apply ext_inner_right ℝ
  intro v
  exact (energy_inner w u v).trans ((hu v).trans (energySolution_inner w f v).symm)

private theorem energyInclusion_opNorm_le_one (w : KahlerBackground n M) (q : ℕ) :
    ‖energyInclusion w q‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  exact (energyProjection_norm_le w v .base).trans_eq (one_mul ‖v‖).symm

/-- The genuine Riesz solution is a contraction in the actual full graph norm. -/
theorem energySolution_opNorm_le_one (w : KahlerBackground n M) (q : ℕ) :
    ‖energySolution w q‖ ≤ 1 := by
  have hn : ‖energySolution w q‖ = ‖energyInclusion w q‖ :=
    (ContinuousLinearMap.adjoint :
      (GraphEnergy w q →L[ℝ] HilbertFormL2 w.form.val w.isKahler.1 q) ≃ₗᵢ⋆[ℝ]
        (HilbertFormL2 w.form.val w.isKahler.1 q →L[ℝ] GraphEnergy w q)).norm_map _
  exact hn.le.trans (energyInclusion_opNorm_le_one w q)

/-- The actual shifted weak resolvent is a contraction in the original Hilbert norm. -/
theorem shiftedWeakResolvent_opNorm_le_one (w : KahlerBackground n M) (q : ℕ) :
    ‖shiftedWeakResolvent w q‖ ≤ 1 := by
  calc
    ‖shiftedWeakResolvent w q‖ ≤ ‖energyInclusion w q‖ * ‖energySolution w q‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 := mul_le_mul (energyInclusion_opNorm_le_one w q)
      (energySolution_opNorm_le_one w q) (energySolution w q).opNorm_nonneg zero_le_one
    _ = 1 := one_mul 1

theorem energySolution_norm_le (w : KahlerBackground n M)
    (f : HilbertFormL2 w.form.val w.isKahler.1 q) : ‖energySolution w q f‖ ≤ ‖f‖ :=
  (energySolution w q).le_opNorm f |>.trans
    ((mul_le_mul_of_nonneg_right (energySolution_opNorm_le_one w q) (norm_nonneg f)).trans_eq
      (one_mul ‖f‖))

theorem shiftedWeakResolvent_norm_le (w : KahlerBackground n M)
    (f : HilbertFormL2 w.form.val w.isKahler.1 q) : ‖shiftedWeakResolvent w q f‖ ≤ ‖f‖ :=
  (shiftedWeakResolvent w q).le_opNorm f |>.trans
    ((mul_le_mul_of_nonneg_right (shiftedWeakResolvent_opNorm_le_one w q) (norm_nonneg f)).trans_eq
      (one_mul ‖f‖))

theorem energySolution_coordinate_norm_le (w : KahlerBackground n M)
    (f : HilbertFormL2 w.form.val w.isKahler.1 q) (i : GraphSlot) :
    ‖energyProjection w q i (energySolution w q f)‖ ≤ ‖f‖ :=
  (energyProjection_norm_le w (energySolution w q f) i).trans (energySolution_norm_le w f)

/-- The constructed shifted weak resolvent is genuinely self-adjoint. -/
theorem shiftedWeakResolvent_adjoint (w : KahlerBackground n M) (q : ℕ) :
    ContinuousLinearMap.adjoint (shiftedWeakResolvent w q) = shiftedWeakResolvent w q := by
  let I : GraphEnergy w q →L[ℝ] HilbertFormL2 w.form.val w.isKahler.1 q := energyInclusion w q
  change ContinuousLinearMap.adjoint (I.comp (ContinuousLinearMap.adjoint I)) =
    I.comp (ContinuousLinearMap.adjoint I)
  have hcomp := ContinuousLinearMap.adjoint_comp (𝕜 := ℝ)
    (E := HilbertFormL2 w.form.val w.isKahler.1 q) (F := GraphEnergy w q)
    (G := HilbertFormL2 w.form.val w.isKahler.1 q) I (ContinuousLinearMap.adjoint I)
  have hinv := ContinuousLinearMap.adjoint_adjoint (𝕜 := ℝ)
    (E := GraphEnergy w q) (F := HilbertFormL2 w.form.val w.isKahler.1 q) I
  exact hcomp.trans (congrArg (fun T : GraphEnergy w q →L[ℝ]
    HilbertFormL2 w.form.val w.isKahler.1 q => T.comp (ContinuousLinearMap.adjoint I)) hinv)

/-- The entire original Hilbert symmetry, not a supplied spectral property. -/
theorem shiftedWeakResolvent_inner_symm (w : KahlerBackground n M)
    (f g : HilbertFormL2 w.form.val w.isKahler.1 q) :
    inner ℝ (shiftedWeakResolvent w q f) g = inner ℝ f (shiftedWeakResolvent w q g) := by
  have hadj := ContinuousLinearMap.adjoint_inner_right (shiftedWeakResolvent w q) f g
  rw [shiftedWeakResolvent_adjoint] at hadj
  exact hadj.symm

/-- Actual positivity reads back the full constructed graph energy. -/
theorem shiftedWeakResolvent_inner_self (w : KahlerBackground n M)
    (f : HilbertFormL2 w.form.val w.isKahler.1 q) :
    inner ℝ (shiftedWeakResolvent w q f) f = ‖energySolution w q f‖ ^ 2 := by
  calc
    inner ℝ (shiftedWeakResolvent w q f) f = inner ℝ f (shiftedWeakResolvent w q f) :=
      real_inner_comm f (shiftedWeakResolvent w q f)
    _ = inner ℝ (energySolution w q f) (energySolution w q f) :=
      (energySolution_inner w f (energySolution w q f)).symm
    _ = ‖energySolution w q f‖ ^ 2 := real_inner_self_eq_norm_sq _

theorem shiftedWeakResolvent_nonneg (w : KahlerBackground n M)
    (f : HilbertFormL2 w.form.val w.isKahler.1 q) :
    0 ≤ inner ℝ (shiftedWeakResolvent w q f) f := by
  rw [shiftedWeakResolvent_inner_self]
  exact sq_nonneg _

private theorem energySolution_eq_zero_imp (w : KahlerBackground n M)
    (f : HilbertFormL2 w.form.val w.isKahler.1 q) (hf : energySolution w q f = 0) : f = 0 := by
  let H := HilbertFormL2 w.form.val w.isKahler.1 q
  have hcont : Continuous (fun y : H => inner ℝ f y) :=
    (continuous_const : Continuous (fun _ : H => f)).inner (𝕜 := ℝ)
      (continuous_id : Continuous (fun y : H => y))
  have horth : ∀ y : H, inner ℝ f y = 0 := by
    intro y
    exact (energyInclusion_denseRange w q).induction_on
      (p := fun z => inner ℝ f z = 0) y (isClosed_eq hcont continuous_const)
      (fun v => by
        have hadj := energySolution_inner w f v
        rw [hf] at hadj
        have hz : inner ℝ (0 : GraphEnergy w q) v = 0 := inner_zero_left v
        exact hadj.symm.trans hz
        )
  exact (inner_self_eq_zero (𝕜 := ℝ)).mp (horth f)

/-- Injectivity follows from actual graph inclusion density and genuine Riesz identities. -/
theorem energySolution_injective (w : KahlerBackground n M) (q : ℕ) :
    Function.Injective (energySolution w q) := by
  intro f g h
  apply sub_eq_zero.mp
  apply energySolution_eq_zero_imp w
  rw [map_sub, h, sub_self]

/-- True injectivity of the actual shifted resolvent uses genuine joint closability. -/
theorem shiftedWeakResolvent_injective (w : KahlerBackground n M) (q : ℕ) :
    Function.Injective (shiftedWeakResolvent w q) :=
  (energyInclusion_injective w q).comp (energySolution_injective w q)

/-- Actual range density; closed range or a bounded inverse is not inferred. -/
theorem shiftedWeakResolvent_denseRange (w : KahlerBackground n M) (q : ℕ) :
    DenseRange (shiftedWeakResolvent w q) := by
  let R := shiftedWeakResolvent w q
  have hk : R.ker = ⊥ := LinearMap.ker_eq_bot.mpr (shiftedWeakResolvent_injective w q)
  have ho : R.kerᗮ = R.range.topologicalClosure := by
    have h := R.orthogonal_ker
    rw [shiftedWeakResolvent_adjoint] at h
    exact h
  change Dense (R.range : Set (HilbertFormL2 w.form.val w.isKahler.1 q))
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  calc
    R.range.topologicalClosure = R.kerᗮ := ho.symm
    _ = (⊥ : Submodule ℝ (HilbertFormL2 w.form.val w.isKahler.1 q))ᗮ :=
      congrArg Submodule.orthogonal hk
    _ = ⊤ := Submodule.bot_orthogonal_eq_top

/-- Literal genuine original smooth tests of the constructed shifted weak equation. -/
theorem shiftedWeakResolvent_original_smooth_tests (w : KahlerBackground n M)
    (f : HilbertFormL2 w.form.val w.isKahler.1 q) (β : SmoothRealForm n M q) :
    inner ℝ (shiftedWeakResolvent w q f) (toHilbertFormL2 w.form.val w.isKahler.1 β) +
      inner ℝ (energyDerivative w q (energySolution w q f))
        (toHilbertFormL2 w.form.val w.isKahler.1 β.exteriorDerivative) +
      inner ℝ (energyCoderivative w q (energySolution w q f))
        (toHilbertFormL2 w.form.val w.isKahler.1
          (coderivativeForm w.form.val w.isKahler.1 q β)) =
      inner ℝ f (toHilbertFormL2 w.form.val w.isKahler.1 β) :=
  energySolution_weak_equation w f (smoothEnergyLinear w q β)

end SGPT.Foundations.Analysis.Pending.NaturalHermitianWeakResolvent
