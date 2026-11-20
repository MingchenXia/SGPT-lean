import SGPT.Foundations.Analysis.Pending.ExplicitRadialCurrentACApproximation
import SGPT.Foundations.Analysis.Pending.LocalPositiveCurrentSmoothACApproximation
import SGPT.Foundations.Analysis.Pending.ActualDistributionTwoFormDdc
import SGPT.Foundations.Analysis.Pending.LocalCurrents

set_option autoImplicit false

/-! Full differential calibration of the SAME explicit inner-product radial kernel.
The full mathematical statements and ENTIRE proofs precede this source.
The buffer and index are internally chosen before ALL signed distributions.
This is neither a global class regularization nor a finite mass assertion. -/

noncomputable section
open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ContDiff Distributions BigOperators

namespace SGPT.Foundations.Analysis.Pending.ExplicitRadialScalarDdcCalibration
open FirstPass FirstPass.MongeAmpere StronglyPositiveForms LocalProductCurrents
  LocalCurrentSemicontinuity LocalCurrentDensityMatrix LocalCurrentLebesgue
  LocalCurrentDeterminant TopDegreeDensity ExplicitRadialCurrentACApproximation HolomorphicPullback
  LocalBedfordTaylorProducts ScalarLeviPositiveCurrent LocalCurrentPullbackDdc
  ActualDistributionTwoFormReading ActualDistributionTwoFormDdc
  _root_.SGPT.Foundations.Analysis.LocalCurrents

attribute [local instance] addCommGroupFormSpan

variable {m : ℕ} {U : Opens (ComplexModel (m + 1))}

private def radialBumpTest (U : Opens (ComplexModel (m+1))) (R : ℝ) (hR : 0 < R)
    (k : ℕ) (z : ComplexModel (m+1))
    (h : closedBall z (shrinkingBump (E := ComplexModel (m+1)) R hR k).rOut ⊆ U) : 𝓓(U,ℝ) where
  toFun y := explicitRadialKernel R hR k (z-y)
  contDiff' := (explicitRadialKernel_contDiff R hR k).comp (contDiff_const.sub contDiff_id)
  hasCompactSupport' := by
    apply (isCompact_closedBall z (shrinkingBump (E := ComplexModel (m+1)) R hR k).rOut).of_isClosed_subset
      (isClosed_tsupport _)
    rw [show (fun y => explicitRadialKernel R hR k (z-y)) =
        (fun y => explicitRadialKernel R hR k (y-z)) by
      funext y
      rw [← neg_sub y z,explicitRadialKernel_neg]]
    exact tsupport_explicitRadialKernel_translate_subset R hR k z
  tsupport_subset' := by
    rw [show (fun y => explicitRadialKernel R hR k (z-y)) =
        (fun y => explicitRadialKernel R hR k (y-z)) by
      funext y
      rw [← neg_sub y z,explicitRadialKernel_neg]]
    exact (tsupport_explicitRadialKernel_translate_subset R hR k z).trans h

/-- Evaluation of the SAME genuine explicit radial test, with the zero test
when its supporting ball is not contained in the original domain. -/
def radialMollifiedScalar (D : 𝓓'(U,ℝ)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : ComplexModel (m+1)) : ℝ := by
  classical
  exact if h : closedBall z (shrinkingBump (E := ComplexModel (m+1)) R hR k).rOut ⊆ U then
    D (radialBumpTest U R hR k z h) else 0

private theorem cutoff_hessian_mixed
    (D : 𝓓'(U,ℝ)) (χ : 𝓓(U,ℝ)) (κ : ComplexModel (m+1) → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (K : Compacts (ComplexModel (m+1)))
    (hχK : tsupport χ ⊆ K) (hKU : (K : Set (ComplexModel (m+1))) ⊆ U)
    (z v w : ComplexModel (m+1))
    (hcut : ∀ y ∈ tsupport (fun q => κ (q-z)), χ y = 1) :
    realHessian (distributionCutoffTranslatedPairing D χ κ hκ K hχK hKU) z v w =
      D (dTest w (dTest v (TestFunction.ofSupportedIn hKU
        (cutoffTranslatedKernelSupportedIn χ κ hκ K hχK z)))) := by
  let F := distributionCutoffTranslatedPairing D χ κ hκ K hχK hKU
  let φ := TestFunction.ofSupportedIn hKU
    (cutoffTranslatedKernelSupportedIn χ κ hκ K hχK z)
  have hself (a : ComplexModel (m+1)) :
      realHessian F z a a = D (dTest a (dTest a φ)) := by
    rw [realHessian_distributionCutoffTranslatedPairing_self]
    exact distributionCutoffTranslatedPairing_realHessian_eq_lineDeriv
      D χ κ hκ K hχK hKU z a hcut
  have hF : ContDiffAt ℝ 2 F z :=
    (distributionCutoffTranslatedPairing_contDiff D χ κ hκ K hχK hKU).contDiffAt.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hs : realHessian F z w v = realHessian F z v w := by
    simpa only [realHessian_eq_fderiv] using
      hF.isSymmSndFDerivAt (by norm_num) w v
  have hc : D (dTest v (dTest w φ)) = D (dTest w (dTest v φ)) := by
    have h := congrArg (fun Q : 𝓓'(U,ℝ) => Q φ)
      (LocalCurrents.distribution_derivatives_commute U D v w)
    simpa only [Distribution.lineDerivCLM_apply,neg_neg] using h.symm
  have hsum := hself (v+w)
  have hv := hself v
  have hw := hself w
  simp only [realHessian_eq_fderiv,map_add,_root_.add_apply,
    dTest,TestFunction.lineDerivCLM_add,map_add] at hsum
  simp only [← realHessian_eq_fderiv] at hsum
  change realHessian F z v v + realHessian F z w v +
      (realHessian F z v w + realHessian F z w w) =
    D (dTest v (dTest v φ)) + D (dTest w (dTest v φ)) +
      (D (dTest v (dTest w φ)) + D (dTest w (dTest w φ))) at hsum
  rw [hs,hc] at hsum
  linarith

private theorem cutoff_tested_ddc
    (D : 𝓓'(U,ℝ)) (χ : 𝓓(U,ℝ)) (κ : ComplexModel (m+1) → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (K : Compacts (ComplexModel (m+1)))
    (hχK : tsupport χ ⊆ K) (hKU : (K : Set (ComplexModel (m+1))) ⊆ U)
    (z : ComplexModel (m+1))
    (hcut : ∀ y ∈ tsupport (fun q => κ (q-z)), χ y = 1) :
    testedTwoForm (ddC D) (TestFunction.ofSupportedIn hKU
      (cutoffTranslatedKernelSupportedIn χ κ hκ K hχK z)) =
      smoothDDC (distributionCutoffTranslatedPairing D χ κ hκ K hχK hKU) z := by
  ext v
  have hv : v = ![v 0,v 1] := by ext i; fin_cases i <;> rfl
  rw [hv,testedTwoForm_apply,ddC_apply,
    FirstPass.smoothDDC_apply_eq_realHessian
      ((distributionCutoffTranslatedPairing_contDiff D χ κ hκ K hχK hKU).contDiffAt.of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))]
  simp only [_root_.smul_apply,_root_.sub_apply,smul_eq_mul,
    Distribution.lineDerivCLM_apply,neg_neg]
  rw [cutoff_hessian_mixed D χ κ hκ K hχK hKU z (v 1) (Complex.I • v 0) hcut,
    cutoff_hessian_mixed D χ κ hκ K hχK hKU z (v 0) (Complex.I • v 1) hcut]
  ring

private theorem radial_form_tested_ddc
    (D : 𝓓'(U,ℝ)) (R : ℝ) (hR : 0 < R) (k : ℕ) (z : ComplexModel (m+1))
    (hzU : closedBall z (shrinkingBump (E := ComplexModel (m+1)) R hR k).rOut ⊆ U) :
    radialMollifiedForm (ddc (scalarTopCurrent D)) R hR k z =
      testedTwoForm (ddC D) (radialBumpTest U R hR k z hzU) := by
  classical
  let T := ddc (scalarTopCurrent D)
  let φ := radialBumpTest U R hR k z hzU
  have hform : radialMollifiedForm T R hR k z =
      ∑ i, T (formBasis (m+1) m i) φ • dualForm m i := by
    change (∑ i, T (formBasis (m+1) m i)
      (if h : closedBall z (shrinkingBump (E := ComplexModel (m+1)) R hR k).rOut ⊆ U then
        radialBumpTest U R hR k z h else 0) • dualForm m i) = _
    rw [dif_pos hzU]
  have h11 : FirstPass.IsOneOne (radialMollifiedForm T R hR k z) := by
    rw [hform]
    exact isOneOne_sum _ fun i _ => isOneOne_smul (isOneOne_dualForm i) _
  have h11' : FirstPass.IsOneOne (testedTwoForm (ddC D) φ) := by
    intro a b
    rw [testedTwoForm_apply,testedTwoForm_apply]
    exact congrArg (fun Q : 𝓓'(U,ℝ) => Q φ) (LocalCurrents.ddC_isOneOne D a b)
  apply eq_of_forall_topDensity_eq h11 h11'
  intro γ
  change formDensity (radialMollifiedForm T R hR k z) γ = formDensity (testedTwoForm (ddC D) φ) γ
  rw [← complementaryRead_apply,complementaryRead_ddC]
  change formDensity (radialMollifiedForm T R hR k z) γ = T γ φ
  rw [hform,formDensity_apply,← wedgeDensity_apply,map_sum]
  simp only [map_smul,wedgeDensity_apply,topDensity_dualForm,smul_eq_mul]
  have he := congrArg (fun δ : formSpan (m+1) m => T δ φ)
    ((formBasis (m+1) m).sum_repr γ)
  simp only [map_sum,map_smul,_root_.sum_apply,_root_.smul_apply,smul_eq_mul] at he
  rw [← he]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

/-- The original open domain internally supplies one buffer and threshold
before ALL signed scalar distributions, calibrating every actual coefficient
of the SAME actual radial mollified differential with the scalar convolution. -/
theorem exists_buffered_radial_scalar_ddc_calibration
    {x : ComplexModel (m+1)} (hx : x ∈ U) (R : ℝ) (hR : 0 < R) :
    ∃ (V : Opens (ComplexModel (m+1))) (_ : V ≤ U), x ∈ V ∧
      ∃ N : ℕ, ∀ (D : 𝓓'(U,ℝ)) (k : ℕ), N ≤ k →
        ContDiffOn ℝ (⊤ : ℕ∞) (radialMollifiedScalar D R hR k) V ∧
          ∀ z ∈ V, radialMollifiedForm (ddc (scalarTopCurrent D)) R hR k z =
            smoothDDC (radialMollifiedScalar D R hR k) z := by
  classical
  obtain ⟨δ,hδ,hδU⟩ := Metric.isOpen_iff.mp U.isOpen x hx
  let V : Opens (ComplexModel (m+1)) := ⟨ball x (δ/4),isOpen_ball⟩
  let ρ : ContDiffBump x := ⟨δ/2,3*δ/4,by positivity,by linarith⟩
  let K : Compacts (ComplexModel (m+1)) :=
    ⟨closedBall x (3*δ/4),isCompact_closedBall _ _⟩
  have hKU : (K : Set (ComplexModel (m+1))) ⊆ U :=
    (closedBall_subset_ball (by linarith : 3*δ/4 < δ)).trans hδU
  let χ : 𝓓(U,ℝ) := ⟨ρ,ρ.contDiff,ρ.hasCompactSupport,by
    change tsupport (ρ : ComplexModel (m+1) → ℝ) ⊆ U
    rw [ρ.tsupport_eq]
    exact hKU⟩
  have hχK : tsupport χ ⊆ K := by
    change tsupport (ρ : ComplexModel (m+1) → ℝ) ⊆ closedBall x (3*δ/4)
    rw [ρ.tsupport_eq]
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    ((tendsto_order.1 (tendsto_shrinkingBump_rOut (E := ComplexModel (m+1)) R hR)).2
      (δ/4) (by positivity))
  have hVU : V ≤ U := (ball_subset_ball (by linarith : δ/4 ≤ δ)).trans hδU
  refine ⟨V,hVU,by exact mem_ball_self (by positivity),N,?_⟩
  intro D k hk
  let κ := explicitRadialKernel (n := m+1) R hR k
  let F := distributionCutoffTranslatedPairing D χ κ (explicitRadialKernel_contDiff R hR k) K hχK hKU
  have hF : ContDiff ℝ (⊤ : ℕ∞) F :=
    distributionCutoffTranslatedPairing_contDiff D χ κ (explicitRadialKernel_contDiff R hR k) K hχK hKU
  have hbuffer (z : ComplexModel (m+1)) (hz : z ∈ V) :
      closedBall z (shrinkingBump (E := ComplexModel (m+1)) R hR k).rOut ⊆ closedBall x (δ/2) := by
    intro y hy
    have hyz := mem_closedBall.mp hy
    have hzx := mem_ball.mp hz
    apply mem_closedBall.mpr
    calc dist y x ≤ dist y z + dist z x := dist_triangle y z x
      _ ≤ (shrinkingBump (E := ComplexModel (m+1)) R hR k).rOut + δ/4 :=
        add_le_add hyz hzx.le
      _ ≤ δ/4 + δ/4 := add_le_add (hN k hk).le le_rfl
      _ = δ/2 := by ring
  have hzU (z : ComplexModel (m+1)) (hz : z ∈ V) :
      closedBall z (shrinkingBump (E := ComplexModel (m+1)) R hR k).rOut ⊆ U :=
    (hbuffer z hz).trans ((closedBall_subset_ball (by linarith : δ/2 < δ)).trans hδU)
  have hkernel (z y : ComplexModel (m+1)) :
      κ (y-z) = explicitRadialKernel R hR k (z-y) := by
    dsimp [κ]
    rw [← neg_sub z y,explicitRadialKernel_neg]
  have hcut (z : ComplexModel (m+1)) (hz : z ∈ V) :
      ∀ y ∈ tsupport (fun q => κ (q-z)), χ y = 1 := by
    intro y hy
    exact ρ.one_of_mem_closedBall
      (hbuffer z hz (tsupport_explicitRadialKernel_translate_subset R hR k z hy))
  have htest (z : ComplexModel (m+1)) (hz : z ∈ V) :
      radialBumpTest U R hR k z (hzU z hz) = TestFunction.ofSupportedIn hKU
        (cutoffTranslatedKernelSupportedIn χ κ (explicitRadialKernel_contDiff R hR k) K hχK z) := by
    ext y
    change explicitRadialKernel R hR k (z-y) = χ y * κ (y-z)
    rw [hkernel]
    by_cases hy : explicitRadialKernel R hR k (z-y) = 0
    · simp only [hy,mul_zero]
    · rw [show χ y = 1 from (hcut z hz) y (subset_tsupport _ (by
        change κ (y-z) ≠ 0
        rw [hkernel]
        exact hy)),one_mul]
  have heq : Set.EqOn (radialMollifiedScalar D R hR k) F V := by
    intro z hz
    unfold radialMollifiedScalar
    rw [dif_pos (hzU z hz),htest z hz]
    rfl
  refine ⟨hF.contDiffOn.congr heq,?_⟩
  intro z hz
  rw [radial_form_tested_ddc D R hR k z (hzU z hz),htest z hz,
    cutoff_tested_ddc D χ κ (explicitRadialKernel_contDiff R hR k) K hχK hKU z (hcut z hz)]
  exact FirstPass.smoothDDC_congr (Filter.EventuallyEq.symm
    (heq.eventuallyEq_of_mem (V.isOpen.mem_nhds hz)))

end SGPT.Foundations.Analysis.Pending.ExplicitRadialScalarDdcCalibration
