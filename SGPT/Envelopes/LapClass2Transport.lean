import SGPT.Envelopes.LapClass2Normal

/-!
# Transport of the metric Laplacian to Kähler normal coordinates

Lane LAP-CLASS2 (`claude-lap-class2`, node `lap-class2:transport`).  Let `Φ = normalCoord z₀ L c` be
the quadratic normal coordinate map, with `‖L‖ ≤ C0`, `‖L⁻¹‖ ≤ N0`, `‖c‖ ≤ C0` and a radius `r₀`
with `C0 r₀ ≤ 1/4`, `C0² r₀ N0 ≤ 1/4` (`exists_uniform_normal_data`).  On `B(0, r₀)`:

* `Φ` approximates `L` (`approximatesLinearOn_normalCoord`), hence restricts to an open partial
  homeomorphism `normalPH` from `B(0, r₀)` onto its image, with smooth inverse
  (`contDiffAt_normalPH_symm`), and `|det DΦ|` is bounded above and below
  (`abs_det_fderiv_normalCoord_le`, `le_abs_det_fderiv_normalCoord`);
* a test function `ψ` with compact support in `B(0, r₀)` is the pull-back of the test function
  `φ = ψ ∘ Φ⁻¹` (`normalPushTest`, `contDiff_normalPushTest`, `normalPushTest_comp`);
* **transport of the pairing** (`integral_normalPushTest_eq`): for any `g`, `V`,
  `∫ g V Re tr(H⁻¹ ∂∂̄φ) dz = ∫ g(Φ) |det DΦ| V(Φ) Re tr(h̃⁻¹ ∂∂̄ψ) dζ`, `H` the coefficient
  matrix of a field `a` of `(1,1)`-forms and `h̃` that of `Φ^*a` (change of variables and the
  holomorphic chain rule `complexHessian_comp_normalCoord`, as in LAP-CLASS's
  `laplacian_normalCoord`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal

namespace SGPT.Envelopes.LapClass

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.HolomorphicMixedDensity
open SGPT.Analysis.KahlerNormal

variable {n : ℕ}

section Local

variable (z₀ : ComplexModel n) (L : ComplexModel n ≃L[ℂ] ComplexModel n)
  {c : ComplexModel n →L[ℂ] ComplexModel n →L[ℂ] ComplexModel n} (hsymm : ∀ p u, c p u = c u p)
  {r₀ C0 N0 : ℝ}

/-- The normal coordinate map as a function. -/
abbrev nc : ComplexModel n → ComplexModel n :=
  normalCoord z₀ (L : ComplexModel n →L[ℂ] ComplexModel n) c

include hsymm in
/-- `Φ(w) - Φ(w') - L(w - w') = -½ L c(w - w', w + w')`. -/
theorem normalCoord_sub_sub (w w' : ComplexModel n) :
    nc z₀ L (c := c) w - nc z₀ L (c := c) w' - (L : ComplexModel n →L[ℂ] ComplexModel n) (w - w') =
      -((1 / 2 : ℂ) • (L : ComplexModel n →L[ℂ] ComplexModel n) (c (w - w') (w + w'))) := by
  have h : c (w - w') (w + w') = c w w - c w' w' := by
    rw [map_sub, sub_apply, map_add, map_add, hsymm w' w]
    abel
  rw [h]
  simp only [nc, normalCoord, map_sub, map_smul, smul_sub]
  abel

include hsymm in
/-- **`Φ` approximates `L` on `B(0, r₀)`**, with constant `C0² r₀`. -/
theorem approximatesLinearOn_normalCoord (hC0 : 0 ≤ C0) (hr₀ : 0 ≤ r₀)
    (hL : ‖(L : ComplexModel n →L[ℂ] ComplexModel n)‖ ≤ C0)
    (hc : ∀ p x, ‖c p x‖ ≤ C0 * ‖p‖ * ‖x‖) :
    ApproximatesLinearOn (nc z₀ L (c := c)) (L : ComplexModel n →L[ℂ] ComplexModel n)
      (ball 0 r₀) ⟨C0 * C0 * r₀, by positivity⟩ := by
  intro w hw w' hw'
  rw [normalCoord_sub_sub z₀ L hsymm, norm_neg, norm_smul]
  rw [mem_ball, dist_zero_right] at hw hw'
  have h1 : ‖w + w'‖ ≤ 2 * r₀ := (norm_add_le _ _).trans (by linarith)
  have h2 : ‖(L : ComplexModel n →L[ℂ] ComplexModel n) (c (w - w') (w + w'))‖ ≤
      C0 * (C0 * ‖w - w'‖ * ‖w + w'‖) :=
    ((L : ComplexModel n →L[ℂ] ComplexModel n).le_opNorm _).trans
      (mul_le_mul hL (hc _ _) (norm_nonneg _) hC0)
  have h3 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [h3]
  change 1 / 2 * ‖(L : ComplexModel n →L[ℂ] ComplexModel n) (c (w - w') (w + w'))‖ ≤
    C0 * C0 * r₀ * ‖w - w'‖
  have h4 : C0 * ‖w - w'‖ * ‖w + w'‖ ≤ C0 * ‖w - w'‖ * (2 * r₀) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left h4 hC0, norm_nonneg (w - w')]

/-- The approximation constant is below `‖L⁻¹‖⁻¹` (or the space is trivial). -/
theorem normalCoord_const_lt (hN0 : 0 < N0) (hLinv : ∀ y, ‖L.symm y‖ ≤ N0 * ‖y‖)
    (hr : C0 * C0 * r₀ * N0 ≤ 1 / 4) (hC0 : 0 ≤ C0) (hr₀ : 0 ≤ r₀) :
    Subsingleton (ComplexModel n) ∨ (⟨C0 * C0 * r₀, by positivity⟩ : ℝ≥0) <
      ‖((L.symm : ComplexModel n ≃L[ℂ] ComplexModel n) : ComplexModel n →L[ℂ] ComplexModel n)‖₊⁻¹ := by
  by_cases hsub : Subsingleton (ComplexModel n)
  · exact Or.inl hsub
  right
  have hLs : ‖((L.symm : ComplexModel n ≃L[ℂ] ComplexModel n) :
      ComplexModel n →L[ℂ] ComplexModel n)‖ ≤ N0 :=
    ContinuousLinearMap.opNorm_le_bound _ hN0.le fun y => by simpa using hLinv y
  have hpos : 0 < ‖((L.symm : ComplexModel n ≃L[ℂ] ComplexModel n) :
      ComplexModel n →L[ℂ] ComplexModel n)‖ := by
    refine lt_of_le_of_ne (norm_nonneg _) fun h0 => hsub ⟨fun y y' => ?_⟩
    have hz : ((L.symm : ComplexModel n ≃L[ℂ] ComplexModel n) :
        ComplexModel n →L[ℂ] ComplexModel n) = 0 := norm_eq_zero.mp h0.symm
    have hy : ∀ y : ComplexModel n, y = 0 := fun y => by
      have := congrArg (fun T : ComplexModel n →L[ℂ] ComplexModel n => L (T y)) hz
      simpa using this
    rw [hy y, hy y']
  refine NNReal.coe_lt_coe.mp ?_
  simp only [NNReal.coe_inv, coe_nnnorm]
  calc C0 * C0 * r₀ < 1 / N0 := by
        rw [lt_div_iff₀ hN0]; linarith
    _ ≤ _ := by rw [one_div]; exact inv_anti₀ hpos hLs

end Local

/-! ### Normal balls -/

/-- **A normal ball**: the data of Kähler normal coordinates `Φ = normalCoord z₀ L c` on
`B(0, r₀)` with the quantitative bounds of `exists_uniform_normal_data`. -/
structure NormalBall (n : ℕ) where
  /-- The centre. -/
  z₀ : ComplexModel n
  /-- The linear part. -/
  L : ComplexModel n ≃L[ℂ] ComplexModel n
  /-- The quadratic part. -/
  c : ComplexModel n →L[ℂ] ComplexModel n →L[ℂ] ComplexModel n
  /-- The radius. -/
  r₀ : ℝ
  /-- A bound for `L` and `c`. -/
  C0 : ℝ
  /-- A bound for `L⁻¹`. -/
  N0 : ℝ
  symm : ∀ p u, c p u = c u p
  r₀_pos : 0 < r₀
  C0_nonneg : 0 ≤ C0
  N0_pos : 0 < N0
  norm_L : ‖(L : ComplexModel n →L[ℂ] ComplexModel n)‖ ≤ C0
  norm_Linv : ∀ y, ‖L.symm y‖ ≤ N0 * ‖y‖
  norm_c : ∀ p x, ‖c p x‖ ≤ C0 * ‖p‖ * ‖x‖
  small : C0 * r₀ ≤ 1 / 4
  small' : C0 * C0 * r₀ * N0 ≤ 1 / 4

namespace NormalBall

variable (B : NormalBall n)

/-- The coordinate map. -/
abbrev Φ : ComplexModel n → ComplexModel n :=
  normalCoord B.z₀ (B.L : ComplexModel n →L[ℂ] ComplexModel n) B.c

theorem approx : ApproximatesLinearOn B.Φ (B.L : ComplexModel n →L[ℂ] ComplexModel n)
    (ball 0 B.r₀) ⟨B.C0 * B.C0 * B.r₀, by have := B.C0_nonneg; have := B.r₀_pos; positivity⟩ :=
  approximatesLinearOn_normalCoord B.z₀ B.L B.symm B.C0_nonneg B.r₀_pos.le B.norm_L B.norm_c

theorem const_lt : Subsingleton (ComplexModel n) ∨
    (⟨B.C0 * B.C0 * B.r₀, by have := B.C0_nonneg; have := B.r₀_pos; positivity⟩ : ℝ≥0) <
      ‖((B.L.symm : ComplexModel n ≃L[ℂ] ComplexModel n) :
        ComplexModel n →L[ℂ] ComplexModel n)‖₊⁻¹ :=
  normalCoord_const_lt B.L B.N0_pos B.norm_Linv B.small' B.C0_nonneg B.r₀_pos.le

/-- The coordinate map on `B(0, r₀)` as an open partial homeomorphism. -/
def ph : OpenPartialHomeomorph (ComplexModel n) (ComplexModel n) :=
  B.approx.toOpenPartialHomeomorph B.Φ (ball 0 B.r₀) B.const_lt isOpen_ball

@[simp] theorem ph_coe : ⇑B.ph = B.Φ := rfl

@[simp] theorem ph_source : B.ph.source = ball 0 B.r₀ := rfl

theorem ph_target : B.ph.target = B.Φ '' ball 0 B.r₀ := rfl

theorem injOn : InjOn B.Φ (ball 0 B.r₀) := B.approx.injOn B.const_lt

/-- `Φ(B̄(0, ρ)) ⊇ B̄(z₀, 3ρ/(4N0))` for `ρ < r₀`. -/
theorem closedBall_subset_image {ρ : ℝ} (hρ : 0 ≤ ρ) (hρr : ρ < B.r₀) :
    closedBall B.z₀ (3 / (4 * B.N0) * ρ) ⊆ B.Φ '' closedBall 0 ρ := by
  by_cases hsub0 : Subsingleton (ComplexModel n)
  · intro z _
    refine ⟨0, mem_closedBall_self hρ, ?_⟩
    exact Subsingleton.elim _ _
  have hsub : closedBall (0 : ComplexModel n) ρ ⊆ ball 0 B.r₀ := closedBall_subset_ball hρr
  have h := B.approx.surjOn_closedBall_of_nonlinearRightInverse
    (B.L : ComplexModel n ≃L[ℂ] ComplexModel n).toNonlinearRightInverse hρ hsub
  have hΦ0 : B.Φ 0 = B.z₀ := normalCoord_zero _ _ _
  rw [hΦ0] at h
  refine Subset.trans (closedBall_subset_closedBall ?_) h
  have hN : (B.L.toNonlinearRightInverse.nnnorm : ℝ) ≤ B.N0 := by
    change ‖((B.L.symm : ComplexModel n ≃L[ℂ] ComplexModel n) :
      ComplexModel n →L[ℂ] ComplexModel n)‖ ≤ B.N0
    exact ContinuousLinearMap.opNorm_le_bound _ B.N0_pos.le fun y => by simpa using B.norm_Linv y
  have hC : B.C0 * B.C0 * B.r₀ ≤ 1 / (4 * B.N0) := by
    rw [le_div_iff₀ (by have := B.N0_pos; positivity)]
    linarith [B.small']
  refine mul_le_mul_of_nonneg_right ?_ hρ
  change 3 / (4 * B.N0) ≤ (B.L.toNonlinearRightInverse.nnnorm : ℝ)⁻¹ - B.C0 * B.C0 * B.r₀
  have hpos : 0 < (B.L.toNonlinearRightInverse.nnnorm : ℝ) := by
    change 0 < ‖((B.L.symm : ComplexModel n ≃L[ℂ] ComplexModel n) :
      ComplexModel n →L[ℂ] ComplexModel n)‖
    refine lt_of_le_of_ne (norm_nonneg _) fun h0 => hsub0 ⟨fun y y' => ?_⟩
    have hz : ((B.L.symm : ComplexModel n ≃L[ℂ] ComplexModel n) :
        ComplexModel n →L[ℂ] ComplexModel n) = 0 := norm_eq_zero.mp h0.symm
    have hy : ∀ y : ComplexModel n, y = 0 := fun y => by
      have := congrArg (fun T : ComplexModel n →L[ℂ] ComplexModel n => B.L (T y)) hz
      simpa using this
    rw [hy y, hy y']
  have h1 : 1 / B.N0 ≤ (B.L.toNonlinearRightInverse.nnnorm : ℝ)⁻¹ := by
    rw [one_div]; exact inv_anti₀ hpos hN
  have h2 : 3 / (4 * B.N0) = 1 / B.N0 - 1 / (4 * B.N0) := by
    field_simp; ring
  linarith

/-- `‖Φ(w) - z₀‖ ≤ (5/4) C0 ‖w‖` for `w ∈ B(0, r₀)`. -/
theorem norm_Φ_sub_le {w : ComplexModel n} (hw : w ∈ ball (0 : ComplexModel n) B.r₀) :
    ‖B.Φ w - B.z₀‖ ≤ 5 / 4 * B.C0 * ‖w‖ := by
  rw [mem_ball, dist_zero_right] at hw
  have hcw : ‖B.c w w‖ ≤ B.C0 * ‖w‖ * ‖w‖ := B.norm_c w w
  have hCw : B.C0 * ‖w‖ ≤ 1 / 4 :=
    (mul_le_mul_of_nonneg_left hw.le B.C0_nonneg).trans B.small
  have hin : ‖w - (1 / 2 : ℂ) • B.c w w‖ ≤ 5 / 4 * ‖w‖ := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul]
    have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [this]
    nlinarith [norm_nonneg w]
  simp only [Φ, normalCoord, add_sub_cancel_left]
  calc ‖(B.L : ComplexModel n →L[ℂ] ComplexModel n) (w - (1 / 2 : ℂ) • B.c w w)‖
      ≤ B.C0 * (5 / 4 * ‖w‖) :=
        ((B.L : ComplexModel n →L[ℂ] ComplexModel n).le_opNorm _).trans
          (mul_le_mul B.norm_L hin (norm_nonneg _) B.C0_nonneg)
    _ = 5 / 4 * B.C0 * ‖w‖ := by ring

/-- The derivative `DΦ(w) = L ∘ (1 - c(w, ·))` is bounded below on `B(0, r₀)`. -/
theorem norm_normalLinear_ge {w : ComplexModel n} (hw : w ∈ ball (0 : ComplexModel n) B.r₀)
    (v : ComplexModel n) :
    3 / (4 * B.N0) * ‖v‖ ≤ ‖normalLinear (B.L : ComplexModel n →L[ℂ] ComplexModel n) B.c w v‖ := by
  rw [normalLinear_apply]
  rw [mem_ball, dist_zero_right] at hw
  have hN := B.N0_pos
  have h1 : ‖v - B.c w v‖ ≤ B.N0 * ‖(B.L : ComplexModel n →L[ℂ] ComplexModel n) (v - B.c w v)‖ := by
    have := B.norm_Linv ((B.L : ComplexModel n →L[ℂ] ComplexModel n) (v - B.c w v))
    simpa using this
  have h2 : 3 / 4 * ‖v‖ ≤ ‖v - B.c w v‖ := by
    have hcw : ‖B.c w v‖ ≤ B.C0 * ‖w‖ * ‖v‖ := B.norm_c w v
    have hCw : B.C0 * ‖w‖ ≤ 1 / 4 :=
      (mul_le_mul_of_nonneg_left hw.le B.C0_nonneg).trans B.small
    have := norm_sub_norm_le v (B.c w v)
    nlinarith [norm_nonneg v]
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith [norm_nonneg ((B.L : ComplexModel n →L[ℂ] ComplexModel n) (v - B.c w v))]

theorem injective_normalLinear {w : ComplexModel n} (hw : w ∈ ball (0 : ComplexModel n) B.r₀) :
    Function.Injective (normalLinear (B.L : ComplexModel n →L[ℂ] ComplexModel n) B.c w) := by
  refine (injective_iff_map_eq_zero _).mpr fun v hv => ?_
  have h := B.norm_normalLinear_ge hw v
  rw [hv, norm_zero] at h
  have hN := B.N0_pos
  have : 0 < 3 / (4 * B.N0) := by positivity
  exact norm_le_zero_iff.mp (by nlinarith [norm_nonneg v])

/-- `DΦ(w)` as a continuous linear equivalence. -/
def derivEquiv {w : ComplexModel n} (hw : w ∈ ball (0 : ComplexModel n) B.r₀) :
    ComplexModel n ≃L[ℂ] ComplexModel n :=
  (LinearEquiv.ofBijective (normalLinear (B.L : ComplexModel n →L[ℂ] ComplexModel n) B.c w)
    ⟨B.injective_normalLinear hw,
      LinearMap.injective_iff_surjective.mp (B.injective_normalLinear hw)⟩).toContinuousLinearEquiv

theorem derivEquiv_coe {w : ComplexModel n} (hw : w ∈ ball (0 : ComplexModel n) B.r₀) :
    ((B.derivEquiv hw : ComplexModel n ≃L[ℂ] ComplexModel n) : ComplexModel n →L[ℂ] ComplexModel n) =
      (B.L : ComplexModel n →L[ℂ] ComplexModel n) ∘L (ContinuousLinearMap.id ℂ _ - B.c w) := by
  ext v
  rfl

theorem isUnit_det_jacobian {w : ComplexModel n} (hw : w ∈ ball (0 : ComplexModel n) B.r₀) :
    IsUnit (jacobianMatrix B.Φ w).det := by
  rw [← standardMatrix_normalLinear B.z₀ _ B.symm, det_standardMatrix]
  have h : normalLinear (B.L : ComplexModel n →L[ℂ] ComplexModel n) B.c w =
      ((B.derivEquiv hw).toLinearEquiv : ComplexModel n →ₗ[ℂ] ComplexModel n) := by
    ext v; rfl
  rw [h]
  exact LinearEquiv.isUnit_det' _

/-- **The inverse of `Φ` is smooth.** -/
theorem contDiffAt_symm {z : ComplexModel n} (hz : z ∈ B.ph.target) :
    ContDiffAt ℝ ∞ B.ph.symm z := by
  have hs : B.ph.symm z ∈ ball (0 : ComplexModel n) B.r₀ := B.ph.map_target hz
  have hD : HasFDerivAt B.ph
      (((B.derivEquiv hs : ComplexModel n ≃L[ℂ] ComplexModel n) :
        ComplexModel n →L[ℂ] ComplexModel n)) (B.ph.symm z) := by
    rw [derivEquiv_coe, ph_coe]
    exact hasFDerivAt_normalCoord _ _ _ B.symm _
  have hC : ContDiffAt ℂ ∞ B.ph (B.ph.symm z) :=
    (contDiff_normalCoord B.z₀ _ B.c).contDiffAt
  exact (B.ph.contDiffAt_symm hz hD hC).restrict_scalars ℝ

/-! #### Pushing test functions forward -/

open Classical in
/-- The push-forward `φ = ψ ∘ Φ⁻¹` of a test function supported in `B(0, r₀)`. -/
def pushTest (ψ : ComplexModel n → ℝ) (z : ComplexModel n) : ℝ :=
  if z ∈ B.ph.target then ψ (B.ph.symm z) else 0

theorem pushTest_comp (ψ : ComplexModel n → ℝ) {w : ComplexModel n}
    (hw : w ∈ ball (0 : ComplexModel n) B.r₀) : B.pushTest ψ (B.Φ w) = ψ w := by
  have hwt : B.Φ w ∈ B.ph.target := B.ph.map_source hw
  rw [pushTest, if_pos hwt]
  congr 1
  exact B.ph.left_inv hw

theorem pushTest_eq_zero {ψ : ComplexModel n → ℝ} {z : ComplexModel n}
    (hz : z ∉ B.Φ '' tsupport ψ) : B.pushTest ψ z = 0 := by
  classical
  by_cases ht : z ∈ B.ph.target
  · rw [pushTest, if_pos ht]
    refine image_eq_zero_of_notMem_tsupport fun h => hz ⟨B.ph.symm z, h, ?_⟩
    exact B.ph.right_inv ht
  · rw [pushTest, if_neg ht]

theorem isCompact_image_tsupport {ψ : ComplexModel n → ℝ} (hψc : HasCompactSupport ψ) :
    IsCompact (B.Φ '' tsupport ψ) :=
  hψc.isCompact.image (contDiff_normalCoord B.z₀ _ B.c).continuous

theorem tsupport_pushTest_subset {ψ : ComplexModel n → ℝ} (hψc : HasCompactSupport ψ) :
    tsupport (B.pushTest ψ) ⊆ B.Φ '' tsupport ψ :=
  closure_minimal (fun _ hz => by_contra fun h => hz (B.pushTest_eq_zero h))
    (B.isCompact_image_tsupport hψc).isClosed

theorem contDiff_pushTest {ψ : ComplexModel n → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) (hψt : tsupport ψ ⊆ ball 0 B.r₀) :
    ContDiff ℝ ∞ (B.pushTest ψ) := by
  classical
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases ht : z ∈ B.ph.target
  · refine (hψ.contDiffAt.comp z (B.contDiffAt_symm ht)).congr_of_eventuallyEq ?_
    filter_upwards [B.ph.open_target.mem_nhds ht] with y hy
    simp [pushTest, if_pos hy]
  · have hzK : z ∉ B.Φ '' tsupport ψ := fun ⟨w, hw, hwz⟩ =>
      ht (hwz ▸ B.ph.map_source (hψt hw))
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [(B.isCompact_image_tsupport hψc).isClosed.isOpen_compl.mem_nhds hzK] with y hy
    exact B.pushTest_eq_zero hy

theorem hasCompactSupport_pushTest {ψ : ComplexModel n → ℝ} (hψc : HasCompactSupport ψ) :
    HasCompactSupport (B.pushTest ψ) :=
  (B.isCompact_image_tsupport hψc).of_isClosed_subset (isClosed_tsupport _)
    (B.tsupport_pushTest_subset hψc)

end NormalBall

/-! ### Determinant bounds -/

theorem volume_ball_one_pos_lt_top :
    0 < volume (ball (0 : ComplexModel n) 1) ∧ volume (ball (0 : ComplexModel n) 1) < ⊤ :=
  ⟨measure_ball_pos volume _ one_pos, measure_ball_lt_top⟩

/-- `|det T| ≤ A^d` if `‖T v‖ ≤ A ‖v‖`. -/
theorem abs_det_le_of_norm_le (T : ComplexModel n →L[ℝ] ComplexModel n) {A : ℝ} (hA : 0 ≤ A)
    (hT : ∀ v, ‖T v‖ ≤ A * ‖v‖) :
    |LinearMap.det (T : ComplexModel n →ₗ[ℝ] ComplexModel n)| ≤
      A ^ Module.finrank ℝ (ComplexModel n) := by
  have hsub : T '' closedBall 0 1 ⊆ closedBall 0 A := by
    rintro _ ⟨v, hv, rfl⟩
    rw [mem_closedBall, dist_zero_right] at hv ⊢
    exact (hT v).trans (by nlinarith [norm_nonneg v])
  have h := measure_mono (μ := (volume : Measure (ComplexModel n))) hsub
  rw [Measure.addHaar_image_continuousLinearMap, Measure.addHaar_closedBall volume _ zero_le_one,
    Measure.addHaar_closedBall volume _ hA, one_pow, ENNReal.ofReal_one, one_mul,
    ← mul_one (volume (ball (0 : ComplexModel n) 1))] at h
  obtain ⟨h0, htop⟩ := volume_ball_one_pos_lt_top (n := n)
  rw [mul_one] at h
  have h' := (ENNReal.mul_le_mul_iff_left h0.ne' htop.ne).mp h
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h'

/-- `m^d ≤ |det T|` if `m ‖v‖ ≤ ‖T v‖`, `m > 0`. -/
theorem le_abs_det_of_le_norm (T : ComplexModel n →L[ℝ] ComplexModel n) {m : ℝ} (hm : 0 < m)
    (hT : ∀ v, m * ‖v‖ ≤ ‖T v‖) :
    m ^ Module.finrank ℝ (ComplexModel n) ≤
      |LinearMap.det (T : ComplexModel n →ₗ[ℝ] ComplexModel n)| := by
  have hinj : Function.Injective (T : ComplexModel n →ₗ[ℝ] ComplexModel n) := by
    refine (injective_iff_map_eq_zero _).mpr fun v hv => ?_
    have h := hT v
    change m * ‖v‖ ≤ ‖T v‖ at h
    rw [show T v = 0 from hv, norm_zero] at h
    exact norm_le_zero_iff.mp (by nlinarith [norm_nonneg v])
  have hsurj := LinearMap.injective_iff_surjective.mp hinj
  have hsub : closedBall 0 m ⊆ T '' closedBall 0 1 := by
    intro y hy
    obtain ⟨v, rfl⟩ := hsurj y
    refine ⟨v, ?_, rfl⟩
    rw [mem_closedBall, dist_zero_right] at hy ⊢
    have h := hT v
    change ‖T v‖ ≤ m at hy
    nlinarith [norm_nonneg v]
  have h := measure_mono (μ := (volume : Measure (ComplexModel n))) hsub
  rw [Measure.addHaar_image_continuousLinearMap, Measure.addHaar_closedBall volume _ zero_le_one,
    Measure.addHaar_closedBall volume _ hm.le, one_pow, ENNReal.ofReal_one, one_mul] at h
  obtain ⟨h0, htop⟩ := volume_ball_one_pos_lt_top (n := n)
  have h' := (ENNReal.mul_le_mul_iff_left h0.ne' htop.ne).mp h
  exact (ENNReal.ofReal_le_ofReal_iff (abs_nonneg _)).mp h'

namespace NormalBall

variable (B : NormalBall n)

theorem contDiff_Φ : ContDiff ℝ ∞ B.Φ :=
  (contDiff_normalCoord B.z₀ _ B.c).restrict_scalars ℝ

theorem fderiv_Φ_apply (w v : ComplexModel n) :
    fderiv ℝ B.Φ w v = normalLinear (B.L : ComplexModel n →L[ℂ] ComplexModel n) B.c w v :=
  fderiv_normalCoord_apply B.z₀ _ B.symm w v

/-- Upper bound of the Jacobian determinant. -/
theorem abs_det_fderiv_le {w : ComplexModel n} (hw : w ∈ ball (0 : ComplexModel n) B.r₀) :
    |LinearMap.det (fderiv ℝ B.Φ w : ComplexModel n →ₗ[ℝ] ComplexModel n)| ≤
      (5 / 4 * B.C0) ^ Module.finrank ℝ (ComplexModel n) := by
  refine abs_det_le_of_norm_le _ (by have := B.C0_nonneg; positivity) fun v => ?_
  rw [fderiv_Φ_apply, normalLinear_apply]
  rw [mem_ball, dist_zero_right] at hw
  have hcw : ‖B.c w v‖ ≤ B.C0 * ‖w‖ * ‖v‖ := B.norm_c w v
  have hCw : B.C0 * ‖w‖ ≤ 1 / 4 :=
    (mul_le_mul_of_nonneg_left hw.le B.C0_nonneg).trans B.small
  have hin : ‖v - B.c w v‖ ≤ 5 / 4 * ‖v‖ := by
    refine (norm_sub_le _ _).trans ?_
    nlinarith [norm_nonneg v]
  calc ‖(B.L : ComplexModel n →L[ℂ] ComplexModel n) (v - B.c w v)‖ ≤ B.C0 * (5 / 4 * ‖v‖) :=
        ((B.L : ComplexModel n →L[ℂ] ComplexModel n).le_opNorm _).trans
          (mul_le_mul B.norm_L hin (norm_nonneg _) B.C0_nonneg)
    _ = 5 / 4 * B.C0 * ‖v‖ := by ring

/-- Lower bound of the Jacobian determinant. -/
theorem le_abs_det_fderiv {w : ComplexModel n} (hw : w ∈ ball (0 : ComplexModel n) B.r₀) :
    (3 / (4 * B.N0)) ^ Module.finrank ℝ (ComplexModel n) ≤
      |LinearMap.det (fderiv ℝ B.Φ w : ComplexModel n →ₗ[ℝ] ComplexModel n)| := by
  refine le_abs_det_of_le_norm _ (by have := B.N0_pos; positivity) fun v => ?_
  rw [fderiv_Φ_apply]
  exact B.norm_normalLinear_ge hw v

theorem continuous_abs_det_fderiv :
    Continuous fun w => |LinearMap.det (fderiv ℝ B.Φ w : ComplexModel n →ₗ[ℝ] ComplexModel n)| :=
  (ContinuousLinearMap.continuous_det.comp (B.contDiff_Φ.continuous_fderiv (by simp))).abs

/-! #### The pairing in normal coordinates -/

/-- **The congruence identity**: `Re tr(H(Φw)⁻¹ ∂∂̄φ(Φw)) = Re tr(h̃(w)⁻¹ ∂∂̄ψ(w))`. -/
theorem trace_pushTest (a : ComplexModel n → CoordinateRealTwoForm n) {ψ : ComplexModel n → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (hψt : tsupport ψ ⊆ ball 0 B.r₀)
    {w : ComplexModel n} (hw : w ∈ ball (0 : ComplexModel n) B.r₀) (h11 : IsOneOne (a (B.Φ w))) :
    ((normalizedHermitianMatrix (a (B.Φ w)))⁻¹ * complexHessian (B.pushTest ψ) (B.Φ w)).trace =
      ((normalizedHermitianMatrix (pullbackField B.Φ a w))⁻¹ * complexHessian ψ w).trace := by
  have hφ := B.contDiff_pushTest hψ hψc hψt
  have hφ2 : ContDiffOn ℝ 2 (B.pushTest ψ) univ :=
    (hφ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffOn
  have hev : (fun x => B.pushTest ψ (B.Φ x)) =ᶠ[𝓝 w] ψ := by
    filter_upwards [isOpen_ball.mem_nhds hw] with x hx
    exact B.pushTest_comp ψ hx
  rw [← KahlerLaplacianChart.complexHessian_congr' hev,
    complexHessian_comp_normalCoord B.z₀ _ isOpen_univ hφ2 (mem_univ _),
    pullbackField_eq_compLinearMap B.z₀ _ B.symm, normalizedHermitianMatrix_compLinearMap h11,
    standardMatrix_normalLinear B.z₀ _ B.symm,
    KahlerLaplacianChart.trace_inv_mul_congr (B.isUnit_det_jacobian hw)]

/-- **Transport of the pairing to normal coordinates** (change of variables `z = Φ(w)`). -/
theorem integral_pushTest_eq (a : ComplexModel n → CoordinateRealTwoForm n)
    (h11 : ∀ w ∈ ball (0 : ComplexModel n) B.r₀, IsOneOne (a (B.Φ w)))
    {ψ : ComplexModel n → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψt : tsupport ψ ⊆ ball 0 B.r₀) (g V : ComplexModel n → ℝ) :
    ∫ z, g z * (V z * ((normalizedHermitianMatrix (a z))⁻¹ *
        complexHessian (B.pushTest ψ) z).trace.re) =
      ∫ w, g (B.Φ w) * (|LinearMap.det (fderiv ℝ B.Φ w : ComplexModel n →ₗ[ℝ] ComplexModel n)| *
        V (B.Φ w) * ((normalizedHermitianMatrix (pullbackField B.Φ a w))⁻¹ *
          complexHessian ψ w).trace.re) := by
  have hderiv : ∀ x ∈ ball (0 : ComplexModel n) B.r₀,
      HasFDerivWithinAt B.Φ (fderiv ℝ B.Φ x) (ball 0 B.r₀) x := fun x _ =>
    ((B.contDiff_Φ.differentiable (by simp)) x).hasFDerivAt.hasFDerivWithinAt
  -- the left side lives on `Φ(B(0, r₀))`
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := B.Φ '' ball 0 B.r₀) fun z hz => by
    have hz' : z ∉ tsupport (B.pushTest ψ) := fun h =>
      hz (image_mono hψt (B.tsupport_pushTest_subset hψc h))
    rw [MixedHessian.complexHessian_eq_zero_of_notMem_tsupport hz']
    simp]
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume measurableSet_ball hderiv B.injOn]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := ball (0 : ComplexModel n) B.r₀)
    (f := fun w => g (B.Φ w) * (|LinearMap.det (fderiv ℝ B.Φ w : ComplexModel n →ₗ[ℝ]
      ComplexModel n)| * V (B.Φ w) * ((normalizedHermitianMatrix (pullbackField B.Φ a w))⁻¹ *
        complexHessian ψ w).trace.re)) fun w hw => by
    have hw' : w ∉ tsupport ψ := fun h => hw (hψt h)
    rw [MixedHessian.complexHessian_eq_zero_of_notMem_tsupport hw']
    simp]
  refine setIntegral_congr_fun measurableSet_ball fun w hw => ?_
  simp only [smul_eq_mul]
  rw [trace_pushTest B a hψ hψc hψt hw (h11 w hw), ContinuousLinearMap.det]
  ring

/-- **Transport of the mass**: `∫ V |φ| dz = ∫ |det DΦ| V(Φ) |ψ| dw`. -/
theorem integral_abs_pushTest_eq {ψ : ComplexModel n → ℝ} (hψt : tsupport ψ ⊆ ball 0 B.r₀)
    (V : ComplexModel n → ℝ) :
    ∫ z, V z * |B.pushTest ψ z| =
      ∫ w, |LinearMap.det (fderiv ℝ B.Φ w : ComplexModel n →ₗ[ℝ] ComplexModel n)| *
        V (B.Φ w) * |ψ w| := by
  have hderiv : ∀ x ∈ ball (0 : ComplexModel n) B.r₀,
      HasFDerivWithinAt B.Φ (fderiv ℝ B.Φ x) (ball 0 B.r₀) x := fun x _ =>
    ((B.contDiff_Φ.differentiable (by simp)) x).hasFDerivAt.hasFDerivWithinAt
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := B.Φ '' ball 0 B.r₀) fun z hz => by
    have hz' : z ∉ B.Φ '' tsupport ψ := fun h => hz (image_mono hψt h)
    rw [B.pushTest_eq_zero hz', abs_zero, mul_zero]]
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume measurableSet_ball hderiv B.injOn]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := ball (0 : ComplexModel n) B.r₀)
    (f := fun w => |LinearMap.det (fderiv ℝ B.Φ w : ComplexModel n →ₗ[ℝ] ComplexModel n)| *
        V (B.Φ w) * |ψ w|) fun w hw => by
    have hw' : w ∉ tsupport ψ := fun h => hw (hψt h)
    rw [image_eq_zero_of_notMem_tsupport hw', abs_zero, mul_zero]]
  refine setIntegral_congr_fun measurableSet_ball fun w hw => ?_
  simp only [smul_eq_mul]
  rw [B.pushTest_comp ψ hw, ContinuousLinearMap.det]
  ring

end NormalBall

end SGPT.Envelopes.LapClass
