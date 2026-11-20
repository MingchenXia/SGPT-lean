import SGPT.Okounkov.TranscendentalSkodaSurjective
import SGPT.Foundations.Analysis.Pending.HormanderAPriori
import SGPT.Foundations.Analysis.Pending.HormanderPairingBound

/-!
# Skoda's theorem: the adjoint of `∂̄` and the kernel bundle

Blueprint `claude-tok-skoda`, node `skoda:adjoint-kernel` (part (1)), the first step of the proof
of `skoda:twisted-hormander`.

For a tuple `G` holomorphic near `x` and a `ℂ^R`-valued `(0,1)`-form `α` (rows `α i`, scalar
`(0,1)`-forms) with values in the kernel bundle `S = ker G` near `x`, the weighted formal adjoint
`T* α = -e^{-ψ₀} ∑ⱼ δⱼ αⱼ` of TN (`Hormander.tstarForm`, applied to each row) satisfies

`G · T* α = e^{-ψ₀} ∑ᵢⱼ ∂ⱼGᵢ αᵢⱼ` (`sum_mul_tstarForm_of_eventually_inKernel`),

and splitting a vector `a ∈ ℂ^R` into its `S`-component `kernelProj G x a = a - (G·a) Ḡ/|G|²` and
the normal component gives `|a|² = |P_S a|² + |G·a|²/|G|²` (`norm_sq_eq_kernelProj_add`).
Hence `|T* α|² e^{-w₁} = |P_S T* α|² e^{-w₁} + B(α) e^{-w₃}` with `w₁ = w₃ - 2ψ₀`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.TranscendentalSkoda

open Filter MeasureTheory Set SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.CauchyGreen SGPT.Foundations.Analysis.Pending.Hormander
open SGPT.Foundations.Analysis.Pending.Hormander.Density
open scoped Topology ComplexConjugate ContDiff ENNReal InnerProductSpace

variable {n R : ℕ}

/-! ### The orthogonal projection onto the kernel bundle -/

/-- The orthogonal projection `P_S a = a - (G · a) Ḡ / |G|²` onto `S_x = ker G(x)`. -/
def kernelProj (G : Fin R → ComplexModel n → ℂ) (x : ComplexModel n) (a : Fin R → ℂ) :
    Fin R → ℂ :=
  fun i => a i - (∑ k, G k x * a k) * conj (G i x) * (((generatorNormSq G x)⁻¹ : ℝ) : ℂ)

theorem sum_mul_kernelProj (G : Fin R → ComplexModel n → ℂ) {x : ComplexModel n}
    (hS : 0 < generatorNormSq G x) (a : Fin R → ℂ) :
    ∑ i, G i x * kernelProj G x a i = 0 := by
  have hsum : ∑ i, G i x * (conj (G i x) * (((generatorNormSq G x)⁻¹ : ℝ) : ℂ)) = 1 := by
    have h := sum_mul_skodaLift (D := {x}) (G := G) (fun z hz => by rw [hz]; exact hS)
      (fun _ => (1 : ℂ)) (mem_singleton x)
    simpa [skodaLift] using h
  simp only [kernelProj, mul_sub, Finset.sum_sub_distrib]
  rw [sub_eq_zero]
  calc ∑ i, G i x * a i = (∑ k, G k x * a k) *
        ∑ i, G i x * (conj (G i x) * (((generatorNormSq G x)⁻¹ : ℝ) : ℂ)) := by
        rw [hsum, mul_one]
    _ = _ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring

/-- **Pythagoras for the kernel bundle**: `|a|² = |P_S a|² + |G · a|² / |G|²`. -/
theorem norm_sq_eq_kernelProj_add (G : Fin R → ComplexModel n → ℂ) {x : ComplexModel n}
    (hS : 0 < generatorNormSq G x) (a : Fin R → ℂ) :
    ∑ i, ‖a i‖ ^ 2 =
      ∑ i, ‖kernelProj G x a i‖ ^ 2 + ‖∑ k, G k x * a k‖ ^ 2 / generatorNormSq G x := by
  set Gb : EuclideanSpace ℂ (Fin R) := WithLp.toLp 2 (fun i => conj (G i x)) with hGb
  set av : EuclideanSpace ℂ (Fin R) := WithLp.toLp 2 a with hav
  have hGbS : ‖Gb‖ ^ 2 = generatorNormSq G x := by
    rw [EuclideanSpace.norm_sq_eq, generatorNormSq]
    simp [hGb]
  have hGb0 : Gb ≠ 0 := by
    intro h; rw [h, norm_zero] at hGbS; linarith [hGbS ▸ hS]
  have hinner : ⟪Gb, av⟫_ℂ = ∑ k, G k x * a k := by
    rw [PiLp.inner_apply]
    exact Finset.sum_congr rfl fun k _ => by simp [hGb, hav, RCLike.inner_apply, mul_comm]
  have hproj : ∀ i, kernelProj G x a i =
      (av - ((∑ k, G k x * a k) / ((generatorNormSq G x : ℝ) : ℂ)) • Gb) i := by
    intro i
    simp only [kernelProj, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    have h1 : av.ofLp i = a i := rfl
    have h2 : Gb.ofLp i = conj (G i x) := rfl
    rw [h1, h2, div_eq_mul_inv, ← Complex.ofReal_inv]
    ring
  have h := norm_sq_sub_proj Gb av hGb0
  rw [hinner, hGbS, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at h
  simp_rw [hproj]
  have hav' : ∀ i, av.ofLp i = a i := fun i => rfl
  simp_rw [hav'] at h
  linarith

/-! ### `G · T* α` for kernel-valued forms -/

theorem dDir_finset_sum {ι : Type*} (s : Finset ι) {F : ι → ComplexModel n → ℂ}
    {x v : ComplexModel n} (hF : ∀ i ∈ s, DifferentiableAt ℝ (F i) x) :
    dDir v (fun y => ∑ i ∈ s, F i y) x = ∑ i ∈ s, dDir v (F i) x := by
  simp only [dDir, fderiv_fun_sum hF, _root_.sum_apply, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib, Finset.sum_div]

/-- **The adjoint and the kernel bundle** (`skoda:adjoint-kernel` (1)): if `α` takes values in
`ker G` near `x`, then `G · T* α = e^{-ψ₀} ∑ᵢⱼ ∂ⱼGᵢ αᵢⱼ` at `x`. -/
theorem sum_mul_tstarForm_of_eventually_inKernel {G : Fin R → ComplexModel n → ℂ}
    (w₂ ψ₀ : ComplexModel n → ℝ) {α : Fin R → Fin n → ComplexModel n → ℂ} {x : ComplexModel n}
    (hG : ∀ i, DifferentiableAt ℂ (G i) x) (hα : ∀ i j, DifferentiableAt ℝ (α i j) x)
    (hker : ∀ᶠ y in 𝓝 x, InKernel G y fun i j => α i j y) :
    ∑ i, G i x * tstarForm w₂ ψ₀ (α i) x =
      ((Real.exp (-ψ₀ x) : ℝ) : ℂ) * kernelPairing G x fun i j => α i j x := by
  have hker0 : ∀ j, ∑ i, G i x * α i j x = 0 := hker.self_of_nhds
  -- `∑ᵢ Gᵢ ∂ⱼ αᵢⱼ = - ∑ᵢ ∂ⱼGᵢ αᵢⱼ`
  have hd : ∀ j, ∑ i, G i x * dDir (coordVec j) (α i j) x =
      -∑ i, dDir (coordVec j) (G i) x * α i j x := by
    intro j
    have hzero : (fun y => ∑ i, G i y * α i j y) =ᶠ[𝓝 x] fun _ => (0 : ℂ) := by
      filter_upwards [hker] with y hy
      exact hy j
    have h0 : dDir (coordVec j) (fun y => ∑ i, G i y * α i j y) x = 0 := by
      rw [SGPT.Foundations.Analysis.Pending.Hormander.Density.dDir_congr_of_eventuallyEq hzero]
      simp [dDir]
    have hGR : ∀ i, DifferentiableAt ℝ (G i) x := fun i => (hG i).restrictScalars ℝ
    rw [dDir_finset_sum (F := fun i y => G i y * α i j y) _ fun i _ => (hGR i).mul (hα i j)] at h0
    rw [Finset.sum_congr rfl fun i _ => dDir_mul (hGR i) (hα i j)] at h0
    rw [Finset.sum_add_distrib] at h0
    linear_combination h0
  simp only [tstarForm, deltaDir]
  set e : ℂ := ((Real.exp (-ψ₀ x) : ℝ) : ℂ)
  set c : Fin n → ℂ := fun j => dDir (coordVec j) (fun y => ((w₂ y : ℝ) : ℂ)) x with hc
  calc ∑ i, G i x * (-e * ∑ j, (dDir (coordVec j) (α i j) x -
        dDir (coordVec j) (fun y => ((w₂ y : ℝ) : ℂ)) x * α i j x))
      = -e * ∑ j, ((∑ i, G i x * dDir (coordVec j) (α i j) x) - c j * ∑ i, G i x * α i j x) := by
        rw [Finset.mul_sum]
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← Finset.sum_sub_distrib, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by simp only [hc]; ring
    _ = e * ∑ j, ∑ i, dDir (coordVec j) (G i) x * α i j x := by
        simp_rw [hd, hker0, mul_zero, sub_zero, Finset.sum_neg_distrib]
        ring
    _ = e * kernelPairing G x fun i j => α i j x := by
        rw [kernelPairing, Finset.sum_comm]

/-! ### The a priori estimate in the kernel bundle -/

/-- A nonnegative function integrable for `e^{-w} dλ|_D` gives `F e^{-w}` integrable on `D`. -/
theorem integrable_mul_exp_of_integrable_weightedVolume {D : Set (ComplexModel n)}
    (hD : IsOpen D) {w : ComplexModel n → ℝ} (hw : ContinuousOn w D) {F : ComplexModel n → ℝ}
    (hF : Integrable F (weightedVolume D w)) :
    Integrable (fun x => F x * Real.exp (-w x)) (volume.restrict D) := by
  rw [weightedVolume_eq_withDensity_weightDensity hD, integrable_withDensity_iff
    (measurable_weightDensity hD hw) (Eventually.of_forall fun x => weightDensity_lt_top x)] at hF
  refine hF.congr ?_
  filter_upwards [ae_restrict_mem hD.measurableSet] with x hx
  simp [weightDensity, hx, (Real.exp_pos _).le]

/-- **The a priori estimate in the kernel bundle** (Step 1 of `skoda:twisted-hormander`): for a
test form `α` with values in `ker G`, summing TN's scalar a priori estimate over the rows and
splitting `T* α` into its `S`-part and its normal part,
`∫ (L_Φ(α) - (1 + t) B(α)) e^{-w₃} ≤ (1 + t) ‖P_S T* α‖²_{w₁} + ∑ᵢ ‖∂̄ αᵢ‖²_{w₃}`. -/
theorem kernel_apriori_on {D : Set (ComplexModel n)} (hD : IsOpen D)
    {Φ χ ψ₀ : ComplexModel n → ℝ} (hΦ : ContDiffOn ℝ ∞ Φ D) (hχ : ContDiffOn ℝ ∞ χ D)
    (hψ : ContDiffOn ℝ ∞ ψ₀ D) {t : ℝ} (ht : 0 < t)
    (hLevi : ∀ x ∈ D, ∀ ξ, (1 + 1 / t) * n * ‖fderiv ℝ ψ₀ x‖ ^ 2 * ‖ξ‖ ^ 2 ≤ leviForm χ x ξ)
    {G : Fin R → ComplexModel n → ℂ} (hG : ∀ i, DifferentiableOn ℂ (G i) D)
    (hpos : ∀ z ∈ D, 0 < generatorNormSq G z)
    {α : Fin R → Fin n → ComplexModel n → ℂ} (hα : ∀ i, α i ∈ testForms D)
    (hker : ∀ x ∈ D, InKernel G x fun i j => α i j x) :
    IntegrableOn (fun x => (vectorLevi Φ x (fun i j => α i j x) -
        (1 + t) * secondFundamental G x (fun i j => α i j x)) * Real.exp (-(Φ x + χ x))) D ∧
    ∫ x in D, (vectorLevi Φ x (fun i j => α i j x) -
        (1 + t) * secondFundamental G x (fun i j => α i j x)) * Real.exp (-(Φ x + χ x)) ≤
      (1 + t) * ∫ x, (∑ i, ‖kernelProj G x
          (fun i => tstarForm (fun y => Φ y + χ y - ψ₀ y) ψ₀ (α i) x) i‖ ^ 2)
          ∂(weightedVolume D fun x => Φ x + χ x - 2 * ψ₀ x) +
        ∑ i, ∫ x, (∑ p, ‖dbarForm (α i) p x‖ ^ 2) * Real.exp (-(Φ x + χ x)) := by
  set w₂ : ComplexModel n → ℝ := fun y => Φ y + χ y - ψ₀ y with hw₂def
  set w₁ : ComplexModel n → ℝ := fun x => Φ x + χ x - 2 * ψ₀ x with hw₁def
  set μ₁ := weightedVolume D w₁ with hμ₁
  set T : Fin R → ComplexModel n → ℂ := fun i => tstarForm w₂ ψ₀ (α i) with hT
  set B : ComplexModel n → ℝ := fun x => secondFundamental G x fun i j => α i j x with hB
  set P : ComplexModel n → ℝ := fun x => ∑ i, ‖kernelProj G x (fun i => T i x) i‖ ^ 2 with hP
  set e₃ : ComplexModel n → ℝ := fun x => Real.exp (-(Φ x + χ x)) with he₃
  have hw₂s : ContDiffOn ℝ ∞ w₂ D := (hΦ.add hχ).sub hψ
  have hw₁c : ContinuousOn w₁ D :=
    (hΦ.continuousOn.add hχ.continuousOn).sub (continuousOn_const.mul hψ.continuousOn)
  have hap := fun i => apriori_on hD hΦ hχ hψ ht hLevi (hα i)
  -- the rows
  have hTm : ∀ i, MemLp (T i) 2 μ₁ := fun i =>
    memLp_tstarForm hD hw₁c hw₂s hψ.continuousOn (hα i)
  have hTint : ∀ i, Integrable (fun x => ‖T i x‖ ^ 2) μ₁ := fun i =>
    (memLp_two_iff_integrable_sq_norm (hTm i).1).mp (hTm i)
  have hf₁ : Integrable (fun x => ∑ i, ‖T i x‖ ^ 2) μ₁ :=
    integrable_finsetSum Finset.univ fun i _ => hTint i
  -- the pointwise identity on `D`
  have hpt : ∀ x ∈ D, ∑ i, ‖T i x‖ ^ 2 = P x + Real.exp (-(2 * ψ₀ x)) * B x := by
    intro x hx
    have hS := hpos x hx
    rw [norm_sq_eq_kernelProj_add G hS]
    have hGx : ∀ i, DifferentiableAt ℂ (G i) x := fun i => (hG i).differentiableAt (hD.mem_nhds hx)
    have hαx : ∀ i j, DifferentiableAt ℝ (α i j) x := fun i j =>
      ((hα i j).1.differentiable (by simp)) x
    have hkerx : ∀ᶠ y in 𝓝 x, InKernel G y fun i j => α i j y :=
      Filter.eventually_of_mem (hD.mem_nhds hx) hker
    rw [show (∑ k, G k x * T k x) = _ from
      sum_mul_tstarForm_of_eventually_inKernel w₂ ψ₀ hGx hαx hkerx]
    simp only [hP, hB, secondFundamental]
    congr 1
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, mul_pow,
      ← Real.exp_nat_mul]
    push_cast
    ring_nf
  -- measurability of the `S`-part
  have hGc : ∀ i, ContinuousOn (G i) D := fun i => (hG i).continuousOn
  have hTc : ∀ i, Continuous (T i) := fun i =>
    continuous_tstarForm hD hw₂s hψ.continuousOn (hα i)
  have hSc : ContinuousOn (generatorNormSq G) D := (contDiffOn_generatorNormSq hD hG).continuousOn
  have hPc : ContinuousOn P D := by
    simp only [hP, kernelProj]
    refine continuousOn_finsetSum _ fun i _ => ?_
    refine (ContinuousOn.pow (ContinuousOn.norm ?_) 2)
    refine (hTc i).continuousOn.sub (((continuousOn_finsetSum _ fun k _ =>
      (hGc k).mul (hTc k).continuousOn).mul ((Complex.continuous_conj.comp_continuousOn
        (hGc i)))).mul ?_)
    exact Complex.continuous_ofReal.comp_continuousOn (hSc.inv₀ fun x hx => (hpos x hx).ne')
  have hPm : AEStronglyMeasurable P μ₁ :=
    (aestronglyMeasurable_weightedVolume_iff hD hw₁c).mpr
      (hPc.aestronglyMeasurable hD.measurableSet)
  have hDμ₁ : ∀ᵐ x ∂μ₁, x ∈ D := by
    rw [hμ₁, weightedVolume]
    exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hD.measurableSet)
  have hP0 : ∀ x, 0 ≤ P x := fun x => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hf₂ : Integrable P μ₁ := by
    refine hf₁.mono' hPm ?_
    filter_upwards [hDμ₁] with x hx
    rw [Real.norm_of_nonneg (hP0 x), hpt x hx]
    have hB0 : 0 ≤ B x := div_nonneg (sq_nonneg _) (generatorNormSq_nonneg G x)
    nlinarith [mul_nonneg (Real.exp_pos (-(2 * ψ₀ x))).le hB0]
  have hf₃ : Integrable (fun x => ∑ i, ‖T i x‖ ^ 2 - P x) μ₁ := hf₁.sub hf₂
  -- `∫ (f₁ - P) dμ₁ = ∫_D B e₃`
  have hBint : Integrable (fun x => B x * e₃ x) (volume.restrict D) := by
    have h := integrable_mul_exp_of_integrable_weightedVolume hD hw₁c hf₃
    refine h.congr ?_
    filter_upwards [ae_restrict_mem hD.measurableSet] with x hx
    rw [hpt x hx]
    simp only [he₃, hw₁def]
    rw [add_sub_cancel_left, mul_comm (Real.exp _) (B x), mul_assoc, ← Real.exp_add]
    ring_nf
  have hsplit : ∫ x, ∑ i, ‖T i x‖ ^ 2 ∂μ₁ = ∫ x, P x ∂μ₁ + ∫ x in D, B x * e₃ x := by
    have h1 : ∫ x, ∑ i, ‖T i x‖ ^ 2 ∂μ₁ = ∫ x, P x ∂μ₁ + ∫ x, (∑ i, ‖T i x‖ ^ 2 - P x) ∂μ₁ := by
      rw [← integral_add hf₂ hf₃]
      congr 1; funext x; ring
    rw [h1]
    congr 1
    rw [integral_weightedVolume hD hw₁c]
    refine setIntegral_congr_fun hD.measurableSet fun x hx => ?_
    simp only [smul_eq_mul]
    rw [hpt x hx, add_sub_cancel_left]
    simp only [he₃, hw₁def]
    rw [mul_comm (Real.exp (-(2 * ψ₀ x))) (B x), ← mul_assoc, mul_comm _ (B x), mul_assoc,
      ← Real.exp_add]
    ring_nf
  -- summing the scalar estimates
  have hsumL : ∫ x in D, vectorLevi Φ x (fun i j => α i j x) * e₃ x =
      ∑ i, ∫ x in D, leviForm Φ x (∑ j, α i j x • coordVec j) * e₃ x := by
    rw [← integral_finsetSum _ fun i _ => (hap i).1]
    congr 1; funext x
    rw [vectorLevi, Finset.sum_mul]
  have hsumT : ∑ i, ∫ x, ‖T i x‖ ^ 2 ∂μ₁ = ∫ x, ∑ i, ‖T i x‖ ^ 2 ∂μ₁ :=
    (integral_finsetSum _ fun i _ => hTint i).symm
  have hineq : ∫ x in D, vectorLevi Φ x (fun i j => α i j x) * e₃ x ≤
      (1 + t) * ∫ x, ∑ i, ‖T i x‖ ^ 2 ∂μ₁ +
        ∑ i, ∫ x, (∑ p, ‖dbarForm (α i) p x‖ ^ 2) * Real.exp (-(Φ x + χ x)) := by
    rw [hsumL, ← hsumT, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => (hap i).2
  have hLint : Integrable (fun x => vectorLevi Φ x (fun i j => α i j x) * e₃ x)
      (volume.restrict D) := by
    have h := integrable_finsetSum Finset.univ fun i _ => (hap i).1
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [vectorLevi, Finset.sum_mul]
    rfl
  have hlhs : ∫ x in D, (vectorLevi Φ x (fun i j => α i j x) - (1 + t) * B x) * e₃ x =
      (∫ x in D, vectorLevi Φ x (fun i j => α i j x) * e₃ x) - (1 + t) * ∫ x in D, B x * e₃ x := by
    have h := integral_sub hLint (hBint.const_mul (1 + t))
    rw [integral_const_mul] at h
    rw [← h]
    congr 1; funext x; ring
  refine ⟨?_, ?_⟩
  · refine (hLint.sub (hBint.const_mul (1 + t))).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply, hB, he₃]
    ring
  rw [hlhs]
  rw [hsplit] at hineq
  linarith

/-- **The pairing bound in the kernel bundle** (Step 2 of `skoda:twisted-hormander`): for a
kernel-valued test form `α`,
`|(α, v)_{w₂}|² ≤ (1 + t) (∫ g e^{-w₁}) (‖P_S T* α‖²_{w₁} + ∑ᵢ ‖∂̄ αᵢ‖²_{w₃})`
(Cauchy--Schwarz against the twisted bound, then `kernel_apriori_on`). -/
theorem kernel_norm_sq_pairing_le {D : Set (ComplexModel n)} (hD : IsOpen D)
    {Φ χ ψ₀ : ComplexModel n → ℝ} (hΦ : ContDiffOn ℝ ∞ Φ D) (hχ : ContDiffOn ℝ ∞ χ D)
    (hψ : ContDiffOn ℝ ∞ ψ₀ D) {t : ℝ} (ht : 0 < t)
    (hLevi : ∀ x ∈ D, ∀ ξ, (1 + 1 / t) * n * ‖fderiv ℝ ψ₀ x‖ ^ 2 * ‖ξ‖ ^ 2 ≤ leviForm χ x ξ)
    {G : Fin R → ComplexModel n → ℂ} (hG : ∀ i, DifferentiableOn ℂ (G i) D)
    (hpos : ∀ z ∈ D, 0 < generatorNormSq G z)
    (hcurv : ∀ z ∈ D, ∀ α : Fin R → Fin n → ℂ, InKernel G z α →
      (1 + t) * secondFundamental G z α ≤ vectorLevi Φ z α)
    {v : Fin R → Fin n → ComplexModel n → ℂ}
    (hv : ∀ i j, MemLp (v i j) 2 (weightedVolume D fun x => Φ x + χ x - ψ₀ x))
    {g : ComplexModel n → ℝ} (hg0 : ∀ x ∈ D, 0 ≤ g x)
    (hvg : ∀ z ∈ D, ∀ α : Fin R → Fin n → ℂ, InKernel G z α →
      ‖∑ i, ∑ j, conj (α i j) * v i j z‖ ^ 2 ≤
        g z * (vectorLevi Φ z α - (1 + t) * secondFundamental G z α))
    (hgi : Integrable (fun x => g x * Real.exp (-(Φ x + χ x - 2 * ψ₀ x))) (volume.restrict D))
    {α : Fin R → Fin n → ComplexModel n → ℂ} (hα : ∀ i, α i ∈ testForms D)
    (hker : ∀ x ∈ D, InKernel G x fun i j => α i j x) :
    ‖∑ i, ∑ j, ∫ x, conj (α i j x) * v i j x
        ∂(weightedVolume D fun x => Φ x + χ x - ψ₀ x)‖ ^ 2 ≤
      (1 + t) * (∫ x in D, g x * Real.exp (-(Φ x + χ x - 2 * ψ₀ x))) *
        ((∫ x, (∑ i, ‖kernelProj G x
            (fun i => tstarForm (fun y => Φ y + χ y - ψ₀ y) ψ₀ (α i) x) i‖ ^ 2)
            ∂(weightedVolume D fun x => Φ x + χ x - 2 * ψ₀ x)) +
          ∑ i, ∫ x, (∑ p, ‖dbarForm (α i) p x‖ ^ 2) * Real.exp (-(Φ x + χ x))) := by
  obtain ⟨iL, hap⟩ := kernel_apriori_on hD hΦ hχ hψ ht hLevi hG hpos hα hker
  have hw₂c : ContinuousOn (fun x => Φ x + χ x - ψ₀ x) D :=
    (hΦ.continuousOn.add hχ.continuousOn).sub hψ.continuousOn
  set curv : ComplexModel n → ℝ := fun x => vectorLevi Φ x (fun i j => α i j x) -
    (1 + t) * secondFundamental G x (fun i j => α i j x) with hcurvdef
  set I := ∑ i, ∑ j, ∫ x, conj (α i j x) * v i j x
    ∂(weightedVolume D fun x => Φ x + χ x - ψ₀ x) with hIdef
  set Gi := ∫ x in D, g x * Real.exp (-(Φ x + χ x - 2 * ψ₀ x)) with hGdef
  set Λ := ∫ x in D, curv x * Real.exp (-(Φ x + χ x)) with hΛdef
  set A := ∫ x, (∑ i, ‖kernelProj G x
    (fun i => tstarForm (fun y => Φ y + χ y - ψ₀ y) ψ₀ (α i) x) i‖ ^ 2)
    ∂(weightedVolume D fun x => Φ x + χ x - 2 * ψ₀ x) with hAdef
  set Bq := ∑ i, ∫ x, (∑ p, ‖dbarForm (α i) p x‖ ^ 2) * Real.exp (-(Φ x + χ x)) with hBdef
  have hαm : ∀ i j, MemLp (fun x => conj (α i j x)) 2
      (weightedVolume D fun x => Φ x + χ x - ψ₀ x) := fun i j => by
    have h := (hα i j).conj
    exact memLp_weightedVolume_of_continuous hD hw₂c h.1.continuous h.2.1 h.2.2 2
  have hint : ∀ i j, Integrable (fun x => conj (α i j x) * v i j x)
      (weightedVolume D fun x => Φ x + χ x - ψ₀ x) := fun i j =>
    integrable_mul_of_memLp_two (hαm i j) (hv i j)
  have hI : I = ∫ x in D, Real.exp (-(Φ x + χ x - ψ₀ x)) •
      ∑ i, ∑ j, conj (α i j x) * v i j x := by
    rw [hIdef, ← integral_weightedVolume hD hw₂c]
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
    exact Finset.sum_congr rfl fun i _ => (integral_finsetSum _ fun j _ => hint i j).symm
  have hnormI : ‖I‖ ≤ ∫ x in D, Real.exp (-(Φ x + χ x - ψ₀ x)) *
      ‖∑ i, ∑ j, conj (α i j x) * v i j x‖ := by
    rw [hI]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1
    funext x
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
  have hG0 : 0 ≤ Gi := setIntegral_nonneg hD.measurableSet fun x hx =>
    mul_nonneg (hg0 x hx) (Real.exp_pos _).le
  have hcurv0 : ∀ x ∈ D, 0 ≤ curv x := fun x hx => by
    have := hcurv x hx _ (hker x hx)
    simp only [hcurvdef]; linarith
  have hΛ0 : 0 ≤ Λ := setIntegral_nonneg hD.measurableSet fun x hx =>
    mul_nonneg (hcurv0 x hx) (Real.exp_pos _).le
  have hA0 : 0 ≤ A := integral_nonneg fun x => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hB0 : 0 ≤ Bq := Finset.sum_nonneg fun i _ => integral_nonneg fun x =>
    mul_nonneg (Finset.sum_nonneg fun p _ => sq_nonneg _) (Real.exp_pos _).le
  -- Cauchy--Schwarz in the form `2 s ‖I‖ ≤ s² G + Λ`
  have hquad : ∀ s : ℝ, 0 ≤ Gi * (s * s) + (-2 * ‖I‖) * s + Λ := by
    intro s
    by_cases hs : s ≤ 0
    · nlinarith [norm_nonneg I, mul_nonneg hG0 (mul_self_nonneg s)]
    push Not at hs
    have hpt : ∀ᵐ x ∂(volume.restrict D),
        (2 * s) * (Real.exp (-(Φ x + χ x - ψ₀ x)) * ‖∑ i, ∑ j, conj (α i j x) * v i j x‖) ≤
          s * s * (g x * Real.exp (-(Φ x + χ x - 2 * ψ₀ x))) +
            curv x * Real.exp (-(Φ x + χ x)) := by
      filter_upwards [ae_restrict_mem hD.measurableSet] with x hx
      have hS2 := hvg x hx _ (hker x hx)
      have hE : Real.exp (-(Φ x + χ x - ψ₀ x)) ^ 2 =
          Real.exp (-(Φ x + χ x - 2 * ψ₀ x)) * Real.exp (-(Φ x + χ x)) := by
        rw [sq, ← Real.exp_add, ← Real.exp_add]; ring_nf
      have hX : 0 ≤ s * s * (g x * Real.exp (-(Φ x + χ x - 2 * ψ₀ x))) :=
        mul_nonneg (mul_self_nonneg s) (mul_nonneg (hg0 x hx) (Real.exp_pos _).le)
      have hY : 0 ≤ curv x * Real.exp (-(Φ x + χ x)) :=
        mul_nonneg (hcurv0 x hx) (Real.exp_pos _).le
      have h := two_mul_le_add_of_sq_le hX hY
        (a := s * (Real.exp (-(Φ x + χ x - ψ₀ x)) * ‖∑ i, ∑ j, conj (α i j x) * v i j x‖)) (by
          have e : (s * (Real.exp (-(Φ x + χ x - ψ₀ x)) *
              ‖∑ i, ∑ j, conj (α i j x) * v i j x‖)) ^ 2 =
              s * s * Real.exp (-(Φ x + χ x - ψ₀ x)) ^ 2 *
                ‖∑ i, ∑ j, conj (α i j x) * v i j x‖ ^ 2 := by ring
          rw [e, hE]
          have hE13 : 0 ≤ s * s * (Real.exp (-(Φ x + χ x - 2 * ψ₀ x)) *
              Real.exp (-(Φ x + χ x))) :=
            mul_nonneg (mul_self_nonneg s) (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
          calc s * s * (Real.exp (-(Φ x + χ x - 2 * ψ₀ x)) * Real.exp (-(Φ x + χ x))) *
                ‖∑ i, ∑ j, conj (α i j x) * v i j x‖ ^ 2
              ≤ s * s * (Real.exp (-(Φ x + χ x - 2 * ψ₀ x)) * Real.exp (-(Φ x + χ x))) *
                (g x * curv x) := mul_le_mul_of_nonneg_left hS2 hE13
            _ = _ := by ring)
      linarith
    have hmono := integral_mono_of_nonneg
      (Eventually.of_forall fun x => mul_nonneg (by linarith)
        (mul_nonneg (Real.exp_pos _).le (norm_nonneg _)))
      ((hgi.const_mul (s * s)).add iL) hpt
    simp only [Pi.add_apply] at hmono
    rw [integral_const_mul, integral_add (hgi.const_mul (s * s)) iL, integral_const_mul] at hmono
    nlinarith
  have hdisc := discrim_le_zero hquad
  rw [discrim] at hdisc
  have hIG : ‖I‖ ^ 2 ≤ Gi * Λ := by nlinarith
  calc ‖I‖ ^ 2 ≤ Gi * Λ := hIG
    _ ≤ Gi * ((1 + t) * A + Bq) := mul_le_mul_of_nonneg_left hap hG0
    _ ≤ (1 + t) * Gi * (A + Bq) := by nlinarith [mul_nonneg hG0 hB0]

end SGPT.Okounkov.TranscendentalSkoda
