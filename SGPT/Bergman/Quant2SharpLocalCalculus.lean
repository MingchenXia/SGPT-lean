import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import SGPT.Foundations.Analysis.LeviForm
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Complex
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Quant2SharpLocalCalculus

Local calculus for the sharp Bergman upper bound: Haar measure on the complex model, Hermitian Hessians, small Taylor remainders, quadratic holomorphic gauges, rescaling limits and Jacobians.

Support for source `prop:smooth_weak_conv` (sharp upper bound `τ ≤ θ^n_{P_{θ,X}[φ]_I(v)}` for every
weak cluster point `τ` of the Bergman measures). Ported verbatim (modulo module names) from the
previous team's drafts under `wip/RESUME-20261109/KODAIRA-TRANSPORT/` and re-checked.
-/

-- Ported from `wip/RESUME-20261109/KODAIRA-TRANSPORT/ORIGINAL-SMOOTH-WEAK-CONV01/sources/SourceSharpComplexModelHaar.lean`.
section
set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.SharpLocalUpper
open Module MeasureTheory MeasureTheory.Measure Set WithLp
/-- The ACTUAL complex Euclidean chart volume agrees with the existing
product complex volume under its actual coordinate map. The proof uses the
real orthonormal one/i basis, not a chosen Haar normalization hypothesis.
This includes dimension zero. -/
theorem sourceSharp_complexModel_ofLp_measurePreserving (n : ℕ) :
    MeasurePreserving (@WithLp.ofLp 2 (Fin n → ℂ)) := by
  classical
  let b := Pi.basis (fun _ : Fin n => Complex.basisOneI)
  let B := Pi.orthonormalBasis (fun _ : Fin n => Complex.orthonormalBasisOneI)
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℂ)
  have hpar : (b.parallelepiped : Set (Fin n → ℂ)) =
      Set.univ.pi (fun _ : Fin n => (Complex.basisOneI.parallelepiped : Set ℂ)) := by
    change _root_.parallelepiped b =
      Set.univ.pi (fun _ : Fin n => _root_.parallelepiped Complex.basisOneI)
    simp_rw [parallelepiped_basis_eq]
    ext z
    simp [b, Pi.basis_repr]
    constructor
    · intro h i
      exact ⟨by simpa using h ⟨i, 0⟩, by simpa using h ⟨i, 1⟩⟩
    · intro h ⟨i, j⟩
      fin_cases j
      · simpa using (h i).1
      · simpa using (h i).2
  have hcomplex : (volume : Measure ℂ) Complex.basisOneI.parallelepiped = 1 := by
    change volume (_root_.parallelepiped Complex.basisOneI) = 1
    simpa only [← Complex.toBasis_orthonormalBasisOneI, OrthonormalBasis.coe_toBasis] using
      Complex.orthonormalBasisOneI.volume_parallelepiped
  have hb : b.addHaar = (volume : Measure (Fin n → ℂ)) := by
    apply (Basis.addHaar_eq_iff b volume).mpr
    rw [hpar, volume_pi_pi]
    simp only [hcomplex, Finset.prod_const_one]
  have hmapbasis : B.toBasis.map e.toLinearEquiv = b := by
    rw [show B.toBasis = b.map e.symm.toLinearEquiv from Pi.orthonormalBasis.toBasis _]
    apply DFunLike.ext
    intro j
    change e (e.symm (b j)) = b j
    exact e.apply_symm_apply (b j)
  have hm : Measure.map e (volume : Measure (EuclideanSpace ℂ (Fin n))) = volume := by
    rw [← B.addHaar_eq_volume, Basis.map_addHaar, hmapbasis, hb]
  change MeasurePreserving e
  exact ⟨e.continuous.measurable, hm⟩
end SGPT.Bergman.SharpLocalUpper
end
end

-- Ported from `wip/RESUME-20261109/KODAIRA-TRANSPORT/NEW-SHARP/REVISION-02/sources/SourceSharpHermitianHessian.lean`.
section
/-! New mathematical lineage implementing the reviewed quadratic normal form.
The inputs are arbitrary total real derivative maps. Symmetry and smoothness
are not assumptions of this algebraic construction. -/
set_option autoImplicit false
noncomputable section

namespace SGPT.Bergman.SharpLocalUpper

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

/-- The Levi-normalized Hermitian diagonal, for any real bilinear map. -/
def hermitianHessianQuadratic (B : E →L[ℝ] E →L[ℝ] ℝ) (z : E) : ℝ :=
  (B z z + B (Complex.I • z) (Complex.I • z)) / 4

/-- Complex-linear projection of a continuous real-linear map into a complex
normed space. The factor is deliberately omitted for later normalization. -/
private def complexLinearProjection {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]
    (C : E →L[ℝ] F) : E →L[ℂ] F := by
  let J : E →L[ℝ] E :=
    ((Complex.I : ℂ) • ContinuousLinearMap.id ℂ E).restrictScalars ℝ
  let A : E →L[ℝ] F := C - Complex.I • C.comp J
  have hI (x : E) : A (Complex.I • x) = Complex.I • A x := by
    simp only [A, J, _root_.sub_apply, _root_.smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearMap.id_apply,
      smul_smul, Complex.I_mul_I, neg_one_smul, map_neg, smul_sub, smul_neg]
    abel
  refine
    { toFun := A
      map_add' := A.map_add
      map_smul' := ?_
      cont := A.continuous }
  intro c x
  have hR (t : ℝ) (y : E) : A ((t : ℂ) • y) = (t : ℂ) • A y := by
    change A (algebraMap ℝ ℂ t • y) = algebraMap ℝ ℂ t • A y
    simp only [IsScalarTower.algebraMap_smul, A.map_smul]
  rw [← Complex.re_add_im c]
  simp only [add_smul, mul_smul, A.map_add, hR, hI, RingHom.id_apply]

/-- The complex bilinear part of a real Hessian. -/
def sourceHessianComplexBilinear (B : E →L[ℝ] E →L[ℝ] ℝ) : E →L[ℂ] E →L[ℂ] ℂ :=
  (1 / 4 : ℂ) • complexLinearProjection
    ((StrongDual.extendRCLikeL (𝕜 := ℂ) (F := E)).toContinuousLinearMap.comp B)

/-- The entire holomorphic quadratic part of the actual real Hessian. -/
def sourceHessianHolomorphicQuadratic (B : E →L[ℝ] E →L[ℝ] ℝ) (z : E) : ℂ :=
  sourceHessianComplexBilinear B z z

theorem sourceHessianComplexBilinear_apply
    (B : E →L[ℝ] E →L[ℝ] ℝ) (z w : E) :
    sourceHessianComplexBilinear B z w =
      ((B z w : ℂ) - (B (Complex.I • z) (Complex.I • w) : ℂ) -
        Complex.I * (B z (Complex.I • w) : ℂ) -
        Complex.I * (B (Complex.I • z) w : ℂ)) / 4 := by
  simp only [sourceHessianComplexBilinear, complexLinearProjection,
    _root_.smul_apply, ContinuousLinearMap.coe_mk',
    LinearMap.coe_mk, AddHom.coe_mk, _root_.sub_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    StrongDual.extendRCLikeL_apply, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.id_apply,
    StrongDual.extendRCLike_apply, smul_eq_mul,
    RCLike.I_to_complex]
  ring_nf
  simp [Complex.I_sq]
  ring

theorem sourceHessianHolomorphicQuadratic_differentiable
    (B : E →L[ℝ] E →L[ℝ] ℝ) :
    Differentiable ℂ (sourceHessianHolomorphicQuadratic B) :=
  (sourceHessianComplexBilinear B).differentiable.clm_apply differentiable_id

theorem sourceHessianHolomorphicQuadratic_re
    (B : E →L[ℝ] E →L[ℝ] ℝ) (z : E) :
    (sourceHessianHolomorphicQuadratic B z).re + hermitianHessianQuadratic B z =
      B z z / 2 := by
  rw [sourceHessianHolomorphicQuadratic, sourceHessianComplexBilinear_apply]
  simp only [hermitianHessianQuadratic, Complex.div_ofNat_re, Complex.sub_re,
    Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im, zero_mul, one_mul, sub_zero]
  ring

omit [IsScalarTower ℝ ℂ E] in
@[simp] theorem hermitianHessianQuadratic_zero (B : E →L[ℝ] E →L[ℝ] ℝ) :
    hermitianHessianQuadratic B 0 = 0 := by simp [hermitianHessianQuadratic]

theorem hermitianHessianQuadratic_real_smul
    (B : E →L[ℝ] E →L[ℝ] ℝ) (t : ℝ) (z : E) :
    hermitianHessianQuadratic B (t • z) = t ^ 2 * hermitianHessianQuadratic B z := by
  simp only [hermitianHessianQuadratic, smul_comm Complex.I t, map_smul,
    _root_.smul_apply, smul_eq_mul]
  ring

end SGPT.Bergman.SharpLocalUpper
end
end

-- Ported from `wip/RESUME-20261109/KODAIRA-TRANSPORT/NEW-SHARP/REVISION-02/sources/SourceActualSmallTaylorRemainder.lean`.
section
/-! The actual second-order residual of an arbitrary real function. The
definition uses total derivatives; only the small-residual theorem uses C². -/
set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.SharpLocalUpper
open Set Filter Metric
open scoped Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def sourceActualTaylorResidual (p : E → ℝ) (a z : E) : ℝ :=
  p z - p a - fderiv ℝ p a (z - a) -
    fderiv ℝ (fderiv ℝ p) a (z - a) (z - a) / 2

@[simp] theorem sourceActualTaylorResidual_center (p : E → ℝ) (a : E) :
    sourceActualTaylorResidual p a a = 0 := by simp [sourceActualTaylorResidual]

set_option backward.isDefEq.respectTransparency false in
/-- Continuity of the actual second derivative manufactures an arbitrarily
small quadratic residual on a closed ball inside the original open domain. -/
theorem sourceActual_smallTaylorResidual {U : Set E} (hU : IsOpen U)
    {p : E → ℝ} (hp : ContDiffOn ℝ 2 p U) {a : E} (ha : a ∈ U)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ closedBall a r ⊆ U ∧
      ∀ z ∈ closedBall a r,
        |sourceActualTaylorResidual p a z| ≤ ε * ‖z - a‖ ^ 2 := by
  let B := fderiv ℝ (fderiv ℝ p) a
  have hD : ContDiffOn ℝ 1 (fderiv ℝ p) U :=
    hp.fderiv_of_isOpen hU (by norm_num)
  have hDD : ContinuousAt (fderiv ℝ (fderiv ℝ p)) a :=
    (hD.continuousOn_fderiv_of_isOpen hU (by norm_num)).continuousAt (hU.mem_nhds ha)
  have hnorm : ContinuousAt (fun y => ‖fderiv ℝ (fderiv ℝ p) y - B‖) a :=
    (show Continuous (fun A : E →L[ℝ] E →L[ℝ] ℝ => ‖A‖) from
      @continuous_norm (E →L[ℝ] E →L[ℝ] ℝ) inferInstance).continuousAt.comp
        (hDD.sub continuousAt_const)
  have hzero : ‖fderiv ℝ (fderiv ℝ p) a - B‖ = 0 := by
    dsimp only [B]
    rw [sub_self]
    exact @norm_zero (E →L[ℝ] E →L[ℝ] ℝ) inferInstance
  have hbound : ∀ᶠ y in 𝓝 a, ‖fderiv ℝ (fderiv ℝ p) y - B‖ < ε :=
    hnorm.eventually (gt_mem_nhds (by
      change ‖fderiv ℝ (fderiv ℝ p) a - B‖ < ε
      rw [hzero]
      exact hε))
  have hnear : ∀ᶠ y in 𝓝 a, y ∈ U ∧ ‖fderiv ℝ (fderiv ℝ p) y - B‖ < ε := by
    filter_upwards [hU.mem_nhds ha, hbound] with y hy hby
    exact ⟨hy, hby⟩
  obtain ⟨r₀, hr₀, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let r := r₀ / 2
  have hr : 0 < r := by dsimp [r]; linarith
  have hb (y : E) (hy : y ∈ closedBall a r) :
      y ∈ U ∧ ‖fderiv ℝ (fderiv ℝ p) y - B‖ ≤ ε := by
    have hlt : y ∈ ball a r₀ := by
      apply mem_ball.mpr
      apply lt_of_le_of_lt (mem_closedBall.mp hy)
      dsimp [r]
      linarith
    exact ⟨(hball hlt).1, (hball hlt).2.le⟩
  have hd (y : E) (hy : y ∈ U) : DifferentiableAt ℝ p y :=
    (hp.differentiableOn (by norm_num) y hy).differentiableAt (hU.mem_nhds hy)
  have hdd (y : E) (hy : y ∈ U) : DifferentiableAt ℝ (fderiv ℝ p) y :=
    (hD.differentiableOn (by norm_num) y hy).differentiableAt (hU.mem_nhds hy)
  have hsym (v w : E) : B v w = B w v :=
    (hp.contDiffAt (hU.mem_nhds ha)).isSymmSndFDerivAt (by norm_num) v w
  have hlin (y : E) (hy : y ∈ closedBall a r) :
      ‖fderiv ℝ p y - fderiv ℝ p a - B (y - a)‖ ≤ ε * ‖y - a‖ :=
    (convex_closedBall a r).norm_image_sub_le_of_norm_fderiv_le'
      (fun w hw => hdd w (hb w hw).1) (fun w hw => (hb w hw).2)
      (mem_closedBall_self hr.le) hy
  let g : E → ℝ := fun y => p y - B (y - a) (y - a) / 2
  have hg (y : E) (hy : y ∈ U) :
      HasFDerivAt g (fderiv ℝ p y - B (y - a)) y := by
    have hquad : HasFDerivAt (fun w => B (w - a) (w - a) / 2) (B (y - a)) y := by
      let T : E →L[ℝ] ℝ := B.precompR E (y - a) (ContinuousLinearMap.id ℝ E) +
        B.precompL E (ContinuousLinearMap.id ℝ E) (y - a)
      have hq : HasFDerivAt (fun w => B (w - a) (w - a)) T y :=
        B.hasFDerivAt_of_bilinear
          ((hasFDerivAt_id y).sub_const a) ((hasFDerivAt_id y).sub_const a)
      have hT : (1 / 2 : ℝ) • T = B (y - a) := by
        ext v
        simp only [T, _root_.smul_apply, _root_.add_apply,
          ContinuousLinearMap.precompR_apply, ContinuousLinearMap.precompL_apply,
          ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.id_apply, smul_eq_mul]
        rw [hsym]
        ring
      have hh := hq.const_smul (1 / 2 : ℝ)
      rw [hT] at hh
      have hfun : (fun w => B (w - a) (w - a) / 2) =
          (1 / 2 : ℝ) • (fun w => B (w - a) (w - a)) := by
        funext w
        change B (w - a) (w - a) / 2 = (1 / 2 : ℝ) * B (w - a) (w - a)
        ring
      rw [hfun]
      exact hh
    exact (hd y hy).hasFDerivAt.sub hquad
  refine ⟨r, hr, fun z hz => (hb z hz).1, fun z hz => ?_⟩
  have hseg : segment ℝ a z ⊆ closedBall a r :=
    (convex_closedBall a r).segment_subset (mem_closedBall_self hr.le) hz
  have hbound (y : E) (hy : y ∈ segment ℝ a z) :
      ‖fderiv ℝ g y - fderiv ℝ p a‖ ≤ ε * ‖z - a‖ := by
    rw [(hg y (hb y (hseg hy)).1).fderiv]
    have h := hlin y (hseg hy)
    have heq : fderiv ℝ p y - B (y - a) - fderiv ℝ p a =
        fderiv ℝ p y - fderiv ℝ p a - B (y - a) := by abel
    rw [heq]
    exact h.trans (mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hy) hε.le)
  have hm := (convex_segment a z).norm_image_sub_le_of_norm_fderiv_le'
    (fun y hy => (hg y (hb y (hseg hy)).1).differentiableAt) hbound
    (left_mem_segment ℝ a z) (right_mem_segment ℝ a z)
  have heq : ∀ z : E, p z - B (z - a) (z - a) / 2 - p a - fderiv ℝ p a (z - a) =
      sourceActualTaylorResidual p a z := by
    intro z
    dsimp [sourceActualTaylorResidual, B]
    ring
  simpa only [g, sub_self, map_zero, zero_div, sub_zero, heq,
    Real.norm_eq_abs, sourceActualTaylorResidual, pow_two, mul_assoc,
    sub_sub_sub_comm] using hm


/-- Open-ball form consumed by the unchanged fixed-radius peak producer. -/
theorem sourceActualTaylorResidual_small {U : Set E} (hU : IsOpen U)
    {p : E → ℝ} (hp : ContDiffOn ℝ 2 p U) {a : E} (ha : a ∈ U)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ z : E, ‖z - a‖ < r →
      z ∈ U ∧ |sourceActualTaylorResidual p a z| ≤ ε * ‖z - a‖ ^ 2 := by
  obtain ⟨r, hr, hUball, hsmall⟩ := sourceActual_smallTaylorResidual hU hp ha hε
  refine ⟨r, hr, fun z hz => ?_⟩
  have hmem : z ∈ closedBall a r := mem_closedBall_iff_norm.mpr hz.le
  exact ⟨hUball hmem, hsmall z hmem⟩

end SGPT.Bergman.SharpLocalUpper
end
end

-- Ported from `wip/RESUME-20261109/KODAIRA-TRANSPORT/NEW-SHARP/REVISION-02/sources/SourceActualQuadraticGauge.lean`.
section
/-! Exact quadratic gauge for arbitrary physical functions. All smoothness
assumptions belong to the Taylor-limit branch, not to these identities. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.SharpLocalUpper
open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

def sourceQuadraticGauge (p q : E → ℝ) (a : E) (k : ℝ)
    (F : E → ℂ) (z : E) : ℂ :=
  F z * Complex.exp (((k : ℂ) * ((p a : ℂ) +
    StrongDual.extendRCLike (𝕜 := ℂ) (fderiv ℝ p a) (z - a) +
    sourceHessianHolomorphicQuadratic (fderiv ℝ (fderiv ℝ p) a) (z - a)) +
    (q a : ℂ)) / 2)

theorem sourceQuadraticGauge_differentiableOn
    (p q : E → ℝ) (a : E) (k : ℝ) {F : E → ℂ} {U : Set E}
    (hF : DifferentiableOn ℂ F U) :
    DifferentiableOn ℂ (sourceQuadraticGauge p q a k F) U := by
  apply hF.mul
  apply Complex.differentiable_exp.comp_differentiableOn
  have hlin := (StrongDual.extendRCLike (𝕜 := ℂ) (fderiv ℝ p a)).differentiable.comp
    (differentiable_id.sub_const a)
  have hquad := (sourceHessianHolomorphicQuadratic_differentiable
    (fderiv ℝ (fderiv ℝ p) a)).comp (differentiable_id.sub_const a)
  simp only [div_eq_mul_inv]
  exact (((hlin.const_add (p a : ℂ)).add hquad).const_mul (k : ℂ) |>.add_const
    (q a : ℂ) |>.mul_const (2 : ℂ)⁻¹).differentiableOn

theorem sourceQuadraticGauge_norm_sq (p q : E → ℝ) (a : E) (k : ℝ)
    (F : E → ℂ) (z : E) :
    ‖sourceQuadraticGauge p q a k F z‖ ^ 2 =
      ‖F z‖ ^ 2 * Real.exp ((k : ℝ) * (p a + fderiv ℝ p a (z - a) +
        (sourceHessianHolomorphicQuadratic (fderiv ℝ (fderiv ℝ p) a) (z - a)).re) +
        q a) := by
  rw [sourceQuadraticGauge, norm_mul, mul_pow, Complex.norm_exp, ← Real.exp_nat_mul]
  congr 1
  congr 1
  simp only [Complex.div_ofNat_re, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  have hr : (StrongDual.extendRCLike (𝕜 := ℂ) (fderiv ℝ p a) (z - a)).re =
      fderiv ℝ p a (z - a) := by simp [StrongDual.extendRCLike_apply]
  rw [hr]
  ring

/-- Exact weighted density at every point, including section zeros and k=0. -/
theorem sourceQuadraticGauge_physicalDensity (p q : E → ℝ) (a : E) (k : ℝ)
    (F : E → ℂ) (z : E) :
    ‖F z‖ ^ 2 * Real.exp ((k : ℝ) * p z + q z) =
      ‖sourceQuadraticGauge p q a k F z‖ ^ 2 *
        Real.exp ((k : ℝ) *
          (hermitianHessianQuadratic (fderiv ℝ (fderiv ℝ p) a) (z - a) +
            sourceActualTaylorResidual p a z) + q z - q a) := by
  rw [sourceQuadraticGauge_norm_sq, mul_assoc, ← Real.exp_add]
  congr 1
  congr 1
  have h := sourceHessianHolomorphicQuadratic_re (fderiv ℝ (fderiv ℝ p) a) (z - a)
  dsimp only [sourceActualTaylorResidual]
  linear_combination -(k : ℝ) * h

/-- The same physical density is recovered at the original center. -/
theorem sourceQuadraticGauge_center (p q : E → ℝ) (a : E) (k : ℝ) (F : E → ℂ) :
    ‖sourceQuadraticGauge p q a k F a‖ ^ 2 =
      ‖F a‖ ^ 2 * Real.exp ((k : ℝ) * p a + q a) := by
  simp [sourceQuadraticGauge_norm_sq, sourceHessianHolomorphicQuadratic]

end SGPT.Bergman.SharpLocalUpper
end
end

-- Ported from `wip/RESUME-20261109/KODAIRA-TRANSPORT/NEW-SHARP/REVISION-02/sources/SourceActualRescalingLimit.lean`.
section
/-! Uniform rescaling of the same physical exponent on every fixed ball. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.SharpLocalUpper
open Set Filter Metric
open scoped Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

def sourceRescaleRadius (k : ℕ) : ℝ := (Real.sqrt (k : ℝ))⁻¹

def sourceRescaledPhysicalExponent (p q : E → ℝ) (a : E) (k : ℕ) (z : E) : ℝ :=
  let w := a + sourceRescaleRadius k • z
  (k : ℝ) * (hermitianHessianQuadratic (fderiv ℝ (fderiv ℝ p) a) (w - a) +
    sourceActualTaylorResidual p a w) + q w - q a

theorem sourceRescaleRadius_nonneg (k : ℕ) : 0 ≤ sourceRescaleRadius k :=
  inv_nonneg.mpr (Real.sqrt_nonneg _)

theorem sourceRescaleRadius_tendsto : Tendsto sourceRescaleRadius atTop (𝓝 0) := by
  have h : Tendsto (fun k : ℕ => (k : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_nhds_zero_nat
  change Tendsto (fun k : ℕ => (Real.sqrt (k : ℝ))⁻¹) atTop (𝓝 0)
  simpa only [Real.sqrt_zero, Real.sqrt_inv, sourceRescaleRadius] using h.sqrt

theorem sourceRescaleRadius_sq {k : ℕ} (hk : 0 < k) :
    (k : ℝ) * sourceRescaleRadius k ^ 2 = 1 := by
  rw [sourceRescaleRadius, inv_pow, Real.sq_sqrt (Nat.cast_nonneg k)]
  exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hk))

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in
private theorem rescaledPoint_norm_le (a : E) {R : ℝ} {z : E}
    (hz : z ∈ closedBall (0 : E) R) (k : ℕ) :
    ‖a + sourceRescaleRadius k • z - a‖ ≤ sourceRescaleRadius k * R := by
  rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (sourceRescaleRadius_nonneg k)]
  exact mul_le_mul_of_nonneg_left (by simpa only [mem_closedBall, dist_zero_right] using hz)
    (sourceRescaleRadius_nonneg k)

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in
private theorem rescaledPoints_eventually {U : Set E} (hU : IsOpen U)
    {a : E} (ha : a ∈ U) {R : ℝ} :
    ∀ᶠ k : ℕ in atTop, ∀ z ∈ closedBall (0 : E) R,
      a + sourceRescaleRadius k • z ∈ U := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds ha)
  have ht : Tendsto (fun k => sourceRescaleRadius k * R) atTop (𝓝 0) := by
    simpa only [zero_mul] using sourceRescaleRadius_tendsto.mul_const R
  filter_upwards [ht.eventually (gt_mem_nhds hr)] with k hk z hz
  apply hball
  rw [mem_ball, dist_eq_norm]
  exact (rescaledPoint_norm_le a hz k).trans_lt hk

/-- The same physical exponent converges uniformly to the actual Hermitian
Hessian diagonal, with all rescaled points eventually in the original domain. -/
theorem sourceActual_rescaled_exponent_uniform {U : Set E} (hU : IsOpen U)
    {p : E → ℝ} (hp : ContDiffOn ℝ 2 p U) {a : E} (ha : a ∈ U)
    {q : E → ℝ} (hq : ContinuousAt q a) {R : ℝ} (hR : 0 ≤ R) :
    TendstoUniformlyOn (sourceRescaledPhysicalExponent p q a)
      (hermitianHessianQuadratic (fderiv ℝ (fderiv ℝ p) a)) atTop (closedBall 0 R) ∧
      ∀ᶠ k : ℕ in atTop, ∀ z ∈ closedBall (0 : E) R,
        a + sourceRescaleRadius k • z ∈ U := by
  refine ⟨Metric.tendstoUniformlyOn_iff.mpr ?_, rescaledPoints_eventually hU ha⟩
  intro η hη
  let ε := η / (2 * (R ^ 2 + 1))
  have hden : 0 < R ^ 2 + 1 := by positivity
  have hε : 0 < ε := div_pos hη (mul_pos (by norm_num) hden)
  have hratio : ε * (R ^ 2 + 1) = η / 2 := by
    dsimp only [ε]
    field_simp [ne_of_gt hden]
  have hεsmall : ε * R ^ 2 < η / 2 := by nlinarith
  obtain ⟨r, hr, hball, hsmall⟩ := sourceActual_smallTaylorResidual hU hp ha hε
  obtain ⟨t, ht, hqt⟩ := Metric.continuousAt_iff.mp hq (η / 2) (by positivity)
  have hlim : Tendsto (fun k => sourceRescaleRadius k * R) atTop (𝓝 0) := by
    simpa only [zero_mul] using sourceRescaleRadius_tendsto.mul_const R
  have hrt : 0 < min r t := lt_min hr ht
  filter_upwards [hlim.eventually (gt_mem_nhds hrt), eventually_ge_atTop 1] with k hk hk1 z hz
  let w := a + sourceRescaleRadius k • z
  have hw : ‖w - a‖ < min r t := (rescaledPoint_norm_le a hz k).trans_lt hk
  have hwr : w ∈ closedBall a r :=
    mem_closedBall.mpr (by rw [dist_eq_norm]; exact (hw.trans_le (min_le_left _ _)).le)
  have hwq : |q w - q a| < η / 2 := by
    simpa only [Real.dist_eq] using hqt (by
      rw [dist_eq_norm]
      exact hw.trans_le (min_le_right _ _))
  have hscale := sourceRescaleRadius_sq (lt_of_lt_of_le (by decide : 0 < 1) hk1)
  have hn : ‖w - a‖ ^ 2 = sourceRescaleRadius k ^ 2 * ‖z‖ ^ 2 := by
    simp only [w, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (sourceRescaleRadius_nonneg k), mul_pow]
  have hzR : ‖z‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hz
  have hT : |(k : ℝ) * sourceActualTaylorResidual p a w| ≤ ε * R ^ 2 := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg k)]
    calc
      (k : ℝ) * |sourceActualTaylorResidual p a w| ≤ (k : ℝ) * (ε * ‖w - a‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (hsmall w hwr) (Nat.cast_nonneg k)
      _ = ε * ((k : ℝ) * sourceRescaleRadius k ^ 2) * ‖z‖ ^ 2 := by rw [hn]; ring
      _ = ε * ‖z‖ ^ 2 := by rw [hscale]; ring
      _ ≤ ε * R ^ 2 := mul_le_mul_of_nonneg_left
        (sq_le_sq₀ (norm_nonneg z) hR |>.mpr hzR) hε.le
  have heq : sourceRescaledPhysicalExponent p q a k z -
        hermitianHessianQuadratic (fderiv ℝ (fderiv ℝ p) a) z =
      (k : ℝ) * sourceActualTaylorResidual p a w + q w - q a := by
    dsimp only [sourceRescaledPhysicalExponent]
    rw [add_sub_cancel_left, hermitianHessianQuadratic_real_smul]
    dsimp only [w]
    linear_combination
      (hermitianHessianQuadratic (fderiv ℝ (fderiv ℝ p) a) z) * hscale
  rw [dist_comm, Real.dist_eq, heq]
  have hadd := abs_add_le ((k : ℝ) * sourceActualTaylorResidual p a w) (q w - q a)
  have halg : (k : ℝ) * sourceActualTaylorResidual p a w + q w - q a =
      (k : ℝ) * sourceActualTaylorResidual p a w + (q w - q a) := by ring
  rw [halg]
  exact hadd.trans_lt (by linarith)

end SGPT.Bergman.SharpLocalUpper
end
end

-- Ported from `wip/RESUME-20261109/KODAIRA-TRANSPORT/ORIGINAL-SMOOTH-WEAK-CONV01/sources/SourceSharpRescaleJacobian.lean`.
section
set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.SharpLocalUpper
open Complex Module WithLp
/-- The actual real determinant of the SAME complex linear map is its
complex determinant norm square. No separate Jacobian certificate is supplied. -/
theorem sourceSharp_real_det_eq_complex_normSq {n : ℕ}
    (A : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) :
    LinearMap.det (A.restrictScalars ℝ) = Complex.normSq (LinearMap.det A) := by
  rw [LinearMap.det_restrictScalars, Algebra.norm_complex_eq]
  rfl

/-- Exact true rescaling Jacobian in real dimension2n, manufactured from the
accepted SAME diagonalizer determinant and original k^(-1/2) radius. -/
theorem sourceSharp_rescaled_real_det {n k : ℕ}
    (S : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n))
    (hS : Complex.normSq (LinearMap.det S) = 1) :
    LinearMap.det ((((sourceRescaleRadius k : ℝ) : ℂ) • S).restrictScalars ℝ) =
      ((k : ℝ) ^ n)⁻¹ := by
  rw [sourceSharp_real_det_eq_complex_normSq, LinearMap.det_smul,
    map_mul, map_pow, hS, mul_one]
  have hr : sourceRescaleRadius k ^ 2 = (k : ℝ)⁻¹ := by
    rw [sourceRescaleRadius, inv_pow, Real.sq_sqrt (Nat.cast_nonneg k)]
  simp only [finrank_euclideanSpace_fin, Complex.normSq_ofReal]
  rw [← pow_two, hr, inv_pow]
end SGPT.Bergman.SharpLocalUpper
end
end

-- Ported from `wip/RESUME-20261109/KODAIRA-TRANSPORT/ORIGINAL-SMOOTH-WEAK-CONV01/sources/SourceSharpRescaledImageIntegral.lean`.
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Bergman.SharpLocalUpper
open Complex Module WithLp Set MeasureTheory
open scoped ENNReal
/-- Exact image integral for the SAME original real k^(-1/2) rescaling and
actual determinant-one spectral map. The true real Jacobian k^(-n) is
manufactured; no measure-change equality or Jacobian field is a premise. -/
theorem sourceSharp_rescaled_image_lintegral {n k : ℕ} (hk : 0 < k)
    (a : EuclideanSpace ℂ (Fin n))
    (S : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n))
    (hS : Complex.normSq (LinearMap.det S) = 1)
    (K : Set (EuclideanSpace ℂ (Fin n))) (hK : MeasurableSet K)
    (g : EuclideanSpace ℂ (Fin n) → ℝ≥0∞) :
    (∫⁻ y in (fun z => a + sourceRescaleRadius k • S z) '' K, g y) =
      ∫⁻ z in K, ENNReal.ofReal (((k : ℝ) ^ n)⁻¹) *
        g (a + sourceRescaleRadius k • S z) := by
  let A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    (((sourceRescaleRadius k : ℝ) : ℂ) • S).toContinuousLinearMap
  let B := A.restrictScalars ℝ
  have hdet : B.det = ((k : ℝ) ^ n)⁻¹ := sourceSharp_rescaled_real_det S hS
  have hdetpos : 0 < B.det := by rw [hdet]; positivity
  have hker : LinearMap.ker B.toLinearMap = ⊥ := by
    by_contra h
    have hz : B.det = 0 := LinearMap.det_eq_zero_iff_ker_ne_bot.mpr h
    exact (ne_of_gt hdetpos) hz
  have hinj : Function.Injective B := LinearMap.ker_eq_bot.mp hker
  let f := fun z : EuclideanSpace ℂ (Fin n) => a + B z
  have hread : f = (fun z => a + sourceRescaleRadius k • S z) := by
    funext z
    change a + (sourceRescaleRadius k : ℂ) • S z = _
    rw [Complex.coe_smul]
  have hd (z : EuclideanSpace ℂ (Fin n)) : HasFDerivAt f B z :=
    B.hasFDerivAt.const_add a
  have hi : Function.Injective f := by
    intro x y h
    exact hinj (add_left_cancel h)
  have h := lintegral_image_eq_lintegral_abs_det_fderiv_mul
    (volume : Measure (EuclideanSpace ℂ (Fin n))) hK
    (fun z _ => (hd z).hasFDerivWithinAt) hi.injOn g
  have hkp : 0 < ((k : ℝ) ^ n)⁻¹ := by positivity
  simpa only [hread, hdet, abs_of_pos hkp] using h
end SGPT.Bergman.SharpLocalUpper
end
end
