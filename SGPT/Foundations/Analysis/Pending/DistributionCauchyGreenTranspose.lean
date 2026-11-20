import SGPT.Foundations.Analysis.Pending.DolbeaultLemma
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.Calculus.ContDiff.Bounds

set_option autoImplicit false

noncomputable section
open Set Filter MeasureTheory TopologicalSpace Complex Metric
open scoped ContDiff Distributions Topology
namespace SGPT.Foundations.Analysis.Pending.DistributionCauchyGreenTranspose


open SGPT.Foundations.Analysis.Pending.CauchyGreen

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] {Ω U : Opens E} {v : E}

omit [FiniteDimensional ℂ E] in
private theorem cauchyGreen_add {f g : E → ℂ}
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hg : Continuous g) (hgc : HasCompactSupport g) (hv : v ≠ 0) :
    cauchyGreen v (f + g) = cauchyGreen v f + cauchyGreen v g := by
  funext y
  simp only [cauchyGreen, Pi.add_apply, smul_add,
    integral_add (integrable_inv_smul_comp hf hfc hv y)
      (integrable_inv_smul_comp hg hgc hv y), mul_add]

omit [FiniteDimensional ℂ E] in
private theorem cauchyGreen_smul (f : E → ℂ) (c : ℂ) :
    cauchyGreen v (c • f) = c • cauchyGreen v f := by
  funext y
  simp only [cauchyGreen, Pi.smul_apply, smul_eq_mul]
  simp_rw [mul_left_comm _ c, integral_const_mul]
  ring

private def jetEvaluationCLM {n : ℕ} (q : Fin n → E) :
    (E [×n]→L[ℝ] ℂ) →L[ℝ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => f q
      map_add' := fun f g => by simp
      map_smul' := fun c f => by simp }
    (∏ i, ‖q i‖) (fun f => by simpa [mul_comm] using f.le_opNorm q)

private theorem iteratedFDeriv_cauchyGreen_apply
    {f : E → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hc : HasCompactSupport f) (hv : v ≠ 0)
    (n : ℕ) (y : E) (q : Fin n → E) :
    iteratedFDeriv ℝ n (cauchyGreen v f) y q =
      (Real.pi : ℂ)⁻¹ * ∫ w : ℂ, w⁻¹ * iteratedFDeriv ℝ n f (y - w • v) q := by
  induction n generalizing y with
  | zero => simp only [iteratedFDeriv_zero_apply, cauchyGreen, smul_eq_mul]
  | succ n ih =>
    let t := Fin.tail q
    let g : E → ℂ := fun z => iteratedFDeriv ℝ n f z t
    have hg : ContDiff ℝ (⊤ : ℕ∞) g :=
      (jetEvaluationCLM t).contDiff.comp
        (hf.iteratedFDeriv_right (m := (⊤ : ℕ∞)) (i := n)
          (by exact WithTop.coe_le_coe.mpr le_top))
    have hgc : HasCompactSupport g :=
      (hc.iteratedFDeriv (𝕜 := ℝ) n).mono fun z hz h => hz (by simp [g, h])
    have hh := (contDiff_cauchyGreen hf hc hv).differentiable_iteratedFDeriv
      (m := n) (by exact WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n))
    rw [(hh y).iteratedFDeriv_succ_apply_left']
    have heq : (fun z => iteratedFDeriv ℝ n (cauchyGreen v f) z t) =
        cauchyGreen v g := funext fun z => ih z t
    rw [heq, fderiv_cauchyGreen_apply (hg.of_le (by simp)) hgc hv, cauchyGreen]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with w
    rw [smul_eq_mul]
    congr 1
    exact ((hf.differentiable_iteratedFDeriv (m := n)
      (by exact WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n)) (y - w • v)).iteratedFDeriv_succ_apply_left'
        (m := q)).symm

private theorem exists_uniform_jet_bound (K L : Compacts E) (hv : v ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : ContDiffMapSupportedIn E ℂ ⊤ K) (n : ℕ) (y : E),
      y ∈ L → ‖iteratedFDeriv ℝ n (cauchyGreen v f) y‖ ≤
        C * ContDiffMapSupportedIn.seminorm ℂ E ℂ ⊤ K n f := by
  obtain ⟨M, hM⟩ := K.isCompact.isBounded.subset_closedBall (0 : E)
  obtain ⟨N, hN⟩ := L.isCompact.isBounded.subset_closedBall (0 : E)
  have hvp : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let R : ℝ := (|M| + |N|) / ‖v‖ + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hout (y : E) (hy : y ∈ L) (w : ℂ) (hw : w ∉ ball 0 R) : y - w • v ∉ K := by
    intro hmem
    have h1 := hM hmem
    have h2 := hN hy
    rw [mem_closedBall, dist_zero_right] at h1 h2
    rw [mem_ball, dist_zero_right, not_lt] at hw
    have htri : ‖w‖ * ‖v‖ ≤ ‖y - w • v‖ + ‖y‖ := by
      have ht := norm_le_norm_add_norm_sub' (w • v) y
      simpa only [norm_smul, norm_sub_rev, add_comm] using ht
    have hb := mul_le_mul_of_nonneg_right hw hvp.le
    dsimp [R] at hb
    rw [add_mul, div_mul_cancel₀ _ hvp.ne'] at hb
    linarith [le_abs_self M, le_abs_self N]
  let C := ‖(Real.pi : ℂ)⁻¹‖ * ∫ w in ball (0 : ℂ) R, ‖w‖⁻¹
  have hJ : IntegrableOn (fun w : ℂ => ‖w‖⁻¹) (ball 0 R) := by
    have hi := integrable_indicator_inv_norm 1 R
    simpa only [one_mul, integrable_indicator_iff measurableSet_ball] using hi
  have hC : 0 ≤ C := mul_nonneg (norm_nonneg _) (integral_nonneg fun _ => inv_nonneg.mpr (norm_nonneg _))
  refine ⟨C, hC, fun f n y hy => ?_⟩
  let P := ContDiffMapSupportedIn.seminorm ℂ E ℂ ⊤ K n f
  have hP : 0 ≤ P := apply_nonneg _ _
  apply ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg hC hP)
  intro q
  rw [iteratedFDeriv_cauchyGreen_apply f.contDiff f.hasCompactSupport hv]
  have hz (w : ℂ) (hw : w ∉ ball 0 R) : iteratedFDeriv ℝ n f (y - w • v) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    exact fun h => hout y hy w hw
      ((tsupport_iteratedFDeriv_subset n).trans f.tsupport_subset h)
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := ball (0 : ℂ) R) (fun w hw => by rw [hz w hw]; simp), norm_mul]
  calc
    ‖(Real.pi : ℂ)⁻¹‖ * ‖∫ w in ball (0 : ℂ) R,
        w⁻¹ * iteratedFDeriv ℝ n f (y - w • v) q‖ ≤
      ‖(Real.pi : ℂ)⁻¹‖ * ∫ w in ball (0 : ℂ) R, ‖w‖⁻¹ * (P * ∏ i, ‖q i‖) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply norm_integral_le_of_norm_le (hJ.mul_const _)
      filter_upwards [] with w
      rw [norm_mul, norm_inv]
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (norm_nonneg _))
      exact ((iteratedFDeriv ℝ n f (y - w • v)).le_opNorm q).trans
        (mul_le_mul_of_nonneg_right
          (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℂ)
          (Finset.prod_nonneg fun _ _ => norm_nonneg _))
    _ = C * P * ∏ i, ‖q i‖ := by rw [integral_mul_const]; ring

private def cutoffSupportedIn (χ : 𝓓(Ω, ℂ)) (hv : v ≠ 0) (φ : 𝓓(U, ℂ)) :
    ContDiffMapSupportedIn E ℂ ⊤ ⟨tsupport χ, χ.hasCompactSupport⟩ :=
  .of_support_subset (χ.contDiff.mul (contDiff_cauchyGreen φ.contDiff φ.hasCompactSupport hv))
    (subset_closure.trans tsupport_mul_subset_left)

private def cutoffFixedSupportCLM (χ : 𝓓(Ω, ℂ)) (hv : v ≠ 0)
    (K : Compacts E) :
    ContDiffMapSupportedIn E ℂ ⊤ K →L[ℂ]
      ContDiffMapSupportedIn E ℂ ⊤ ⟨tsupport χ, χ.hasCompactSupport⟩ := by
  let L : Compacts E := ⟨tsupport χ, χ.hasCompactSupport⟩
  let C := Classical.choose (exists_uniform_jet_bound K L hv)
  have hC : 0 ≤ C := (Classical.choose_spec (exists_uniform_jet_bound K L hv)).1
  have hbound := (Classical.choose_spec (exists_uniform_jet_bound K L hv)).2
  refine ContDiffMapSupportedIn.mkCLM ℂ (fun f y => χ y * cauchyGreen v f y)
    (fun f g y => ?_) (fun c f y => ?_)
    (fun f => χ.contDiff.mul (contDiff_cauchyGreen f.contDiff f.hasCompactSupport hv))
    (fun f y hy => ?_) (fun n _ => ?_)
  · rw [FunLike.coe_add, cauchyGreen_add f.continuous f.hasCompactSupport g.continuous g.hasCompactSupport hv]
    simp only [Pi.add_apply, mul_add]
  · rw [FunLike.coe_smul, cauchyGreen_smul]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  · change χ y * cauchyGreen v f y = 0
    rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
  · have hcont : Continuous fun y : E => (Finset.range (n+1)).sup'
        Finset.nonempty_range_add_one (fun i => ‖iteratedFDeriv ℝ i χ y‖) :=
      Continuous.finset_sup'_apply Finset.nonempty_range_add_one fun i _ =>
        (χ.contDiff.continuous_iteratedFDeriv (by exact WithTop.coe_le_coe.mpr le_top)).norm
    obtain ⟨B, hB⟩ := L.isCompact.exists_bound_of_continuousOn hcont.continuousOn
    have hb (i : ℕ) (hi : i ≤ n) (y : E) (hy : y ∈ L) :
        ‖iteratedFDeriv ℝ i χ y‖ ≤ |B| :=
      (Finset.le_sup' _ (Finset.mem_range_succ_iff.mpr hi)).trans
        ((Real.le_norm_self _).trans ((hB y hy).trans (Real.le_norm_self B)))
    refine ⟨Finset.Iic n, 2^n * |B| * C, by positivity, fun f y hy => ?_⟩
    let P := ((Finset.Iic n).sup fun j =>
      ContDiffMapSupportedIn.seminorm ℂ E ℂ ⊤ K j) f
    have hp : 0 ≤ P := apply_nonneg _ _
    calc
      ‖iteratedFDeriv ℝ n (fun z => χ z * cauchyGreen v f z) y‖ ≤
        ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ y‖ *
          ‖iteratedFDeriv ℝ (n-i) (cauchyGreen v f) y‖ :=
        norm_iteratedFDeriv_mul_le χ.contDiff
          (contDiff_cauchyGreen f.contDiff f.hasCompactSupport hv) y
          (by exact WithTop.coe_le_coe.mpr le_top)
      _ ≤ ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) * |B| * (C * P) := by
        apply Finset.sum_le_sum
        intro i hi
        gcongr
        · exact hb i (Finset.mem_range_succ_iff.mp hi) y hy
        · exact (hbound f (n-i) y hy).trans (mul_le_mul_of_nonneg_left
            (Seminorm.le_finset_sup_apply (Finset.mem_Iic.mpr (Nat.sub_le n i))) hC)
      _ = 2^n * |B| * C * P := by
        simp_rw [← mul_assoc, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
        push_cast
        ring

/-- The original cutoff Cauchy--Green operator, with continuity proved on
all actual fixed-support test spaces before taking their LF limit. -/
def cutoffTestCLM (χ : 𝓓(Ω, ℂ)) (hv : v ≠ 0) :
    𝓓(U, ℂ) →L[ℂ] 𝓓(Ω, ℂ) :=
  TestFunction.limitCLM ℂ
    (fun φ => TestFunction.ofSupportedIn χ.tsupport_subset (cutoffSupportedIn χ hv φ))
    (fun K _ => (TestFunction.ofSupportedInCLM ℂ χ.tsupport_subset).comp
      (cutoffFixedSupportCLM χ hv K)) (fun _ _ _ => by ext; rfl)

@[simp] theorem cutoffTestCLM_apply (χ : 𝓓(Ω, ℂ)) (hv : v ≠ 0)
    (φ : 𝓓(U, ℂ)) (y : E) : cutoffTestCLM χ hv φ y = χ y * cauchyGreen v φ y := rfl

/-- The actual complex-linear test derivative in the direction v. -/
def dbarTestCLM (v : E) : 𝓓(U, ℂ) →L[ℂ] 𝓓(U, ℂ) :=
  (TestFunction.postcompCLM (ContinuousLinearMap.mul ℂ ℂ (2:ℂ)⁻¹)).comp
    (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) (F := ℂ) (Ω := U) ℂ v +
      (TestFunction.postcompCLM (ContinuousLinearMap.mul ℂ ℂ (I : ℂ))).comp
        (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) (F := ℂ) (Ω := U) ℂ ((I : ℂ) • v)))

omit [FiniteDimensional ℂ E] in
private theorem dbarTestCLM_apply (φ : 𝓓(U, ℂ)) (y : E) :
    dbarTestCLM v φ y = dbarDir v φ y := by
  change (2:ℂ)⁻¹ *
    ((TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℂ v φ) y +
      I * (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℂ (I • v) φ) y) = _
  simp only [TestFunction.lineDerivCLM_apply, le_top, ↓reduceIte]
  rw [(φ.contDiff.differentiable (by simp) y).lineDeriv_eq_fderiv,
    (φ.contDiff.differentiable (by simp) y).lineDeriv_eq_fderiv]
  simp only [dbarDir]
  ring

omit [FiniteDimensional ℂ E] in
private theorem cauchyGreen_dbar_eq (φ : 𝓓(U, ℂ)) (hv : v ≠ 0) (y : E) :
    cauchyGreen v (dbarTestCLM v φ) y = φ y := by
  have hc : ContDiff ℝ 1 φ := φ.contDiff.of_le (by simp)
  have hcomm := dbarDir_cauchyGreen_comm hc φ.hasCompactSupport hv v y
  have hi := dbarDir_cauchyGreen hc φ.hasCompactSupport hv y
  have heq : (dbarTestCLM v φ : E → ℂ) = dbarDir v φ := funext (dbarTestCLM_apply φ)
  rw [heq, ← hcomm, hi]

/-- Arbitrary local complex distributions receive an actual one-direction
Wirtinger solution, with the smaller domain and cutoff produced internally. -/
theorem exists_local_wirtinger_solution (T : 𝓓(Ω, ℂ) →L[ℂ] ℂ)
    (hv : v ≠ 0) (x : E) (hx : x ∈ Ω) :
    ∃ (U : Opens E) (_hU : U ≤ Ω) (S : 𝓓(U, ℂ) →L[ℂ] ℂ), x ∈ U ∧
      -(S.comp (dbarTestCLM v)) = T.comp (TestFunction.monoCLM ℂ) := by
  classical
  obtain ⟨δ, hδ, hδΩ⟩ := Metric.isOpen_iff.mp Ω.isOpen x hx
  let ρ : ContDiffBump x := ⟨δ/4, δ/2, by positivity, by linarith⟩
  let L : Compacts E := ⟨closedBall x (δ/2), isCompact_closedBall _ _⟩
  have hLΩ : (L:Set E) ⊆ Ω := fun z hz => hδΩ (by
    change z ∈ closedBall x (δ/2) at hz
    rw [mem_closedBall] at hz
    rw [mem_ball]
    linarith)
  let χ : 𝓓(Ω, ℂ) := TestFunction.ofSupportedIn hLΩ
    (ContDiffMapSupportedIn.of_support_subset (Complex.ofRealCLM.contDiff.comp ρ.contDiff)
      (by
        intro z hz
        have hzρ : z ∈ tsupport ρ := subset_tsupport ρ (by simpa using hz)
        change z ∈ closedBall x (δ/2)
        simpa [ρ.tsupport_eq, ρ] using hzρ))
  let U : Opens E := ⟨ball x (δ/4), isOpen_ball⟩
  have hU : U ≤ Ω := fun z hz => hδΩ (by
    change z ∈ ball x (δ/4) at hz
    rw [mem_ball] at hz ⊢
    linarith)
  let H : 𝓓(U, ℂ) →L[ℂ] 𝓓(Ω, ℂ) := cutoffTestCLM χ hv
  refine ⟨U, hU, -(T.comp H), mem_ball_self (by positivity), ?_⟩
  ext φ
  change -(-(T (H (dbarTestCLM v φ)))) = T (TestFunction.monoCLM ℂ φ)
  rw [neg_neg]
  congr 1
  ext y
  rw [cutoffTestCLM_apply, cauchyGreen_dbar_eq φ hv]
  by_cases hy : y ∈ U
  · have hρ : ρ y = 1 := ρ.one_of_mem_closedBall (ball_subset_closedBall hy)
    change (ρ y : ℂ) * φ y = _
    rw [hρ]
    simp [TestFunction.monoCLM_apply, hU]
  · have hφ : φ y = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hy (φ.tsupport_subset h))
    simp [hφ, TestFunction.monoCLM_apply, hU]

end SGPT.Foundations.Analysis.Pending.DistributionCauchyGreenTranspose
