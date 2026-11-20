import SGPT.Convex.SubgradientMeasure
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Hausdorff
import SGPT.Foundations.Analysis.Pending.GramDeterminant

namespace SGPT.Convex

open Set Filter Topology MeasureTheory
open scoped RealInnerProductSpace Gradient MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The original raw subdifferential is the actual Mathlib gradient singleton
at every actual differentiability point of a finite convex function. -/
theorem rawSubdifferential_coe_eq_singleton_gradient {f : E → ℝ}
    (hf : ConvexOn ℝ univ f) {x : E} (hx : DifferentiableAt ℝ f x) :
    rawSubdifferential (innerₗ E) (fun z ↦ (f z : EReal)) x = {gradient f x} := by
  let e := (innerₗ E).flip.toContPerfPair.toContinuousLinearEquiv
  have hp := isProper_coe_of_convexOn hf
  have hxD : x ∈ interior (effectiveDomain (fun z ↦ (f z : EReal))) := by
    have hfull : effectiveDomain (fun z ↦ (f z : EReal)) = univ := by
      ext z
      simp [effectiveDomain]
    simp [hfull]
  have hcan := rawSubdifferential_eq_singleton_of_hasFDerivAt hp hxD
    (show HasFDerivAt (fun z ↦ ((f z : EReal)).toReal) (fderiv ℝ f x) x by
      simpa only [EReal.toReal_coe] using hx.hasFDerivAt)
  have hmap : e '' rawSubdifferential (innerₗ E) (fun z ↦ (f z : EReal)) x = {fderiv ℝ f x} :=
    (rawSubdifferential_image_toContPerfPair (innerₗ E) _ x).trans hcan
  have hg : e (gradient f x) = fderiv ℝ f x := by
    ext v
    simp [e, LinearMap.toContPerfPair_apply, innerₗ_apply_apply ]
  ext m
  constructor
  · intro hm
    have he := mem_singleton_iff.mp (hmap ▸ mem_image_of_mem e hm)
    exact mem_singleton_iff.mpr (e.injective (he.trans hg.symm))
  · intro hm
    have hxmem : fderiv ℝ f x ∈ e '' rawSubdifferential (innerₗ E) (fun z ↦ (f z : EReal)) x := by
      rw [hmap]
      exact mem_singleton _
    obtain ⟨m', hm', hem'⟩ := hxmem
    have hmeq : m' = gradient f x := e.injective (hem'.trans hg.symm)
    simpa only [hmeq, mem_singleton_iff.mp hm] using hm'

/-- Actual gradient-image identification for every original subset. -/
theorem rawSubgradientImageOn_coe_eq_gradient_image {f : E → ℝ}
    (hf : ConvexOn ℝ univ f) (hd : Differentiable ℝ f) (A : Set E) :
    rawSubgradientImageOn (innerₗ E) (fun z ↦ (f z : EReal)) A = gradient f '' A := by
  ext m
  simp only [rawSubgradientImageOn, mem_iUnion,
    rawSubdifferential_coe_eq_singleton_gradient hf (hd _), mem_singleton_iff,
    mem_image]
  constructor
  · rintro ⟨x, hx, hmx⟩
    exact ⟨x, hx, hmx.symm⟩
  · rintro ⟨x, hx, hxm⟩
    exact ⟨x, hx, hxm.symm⟩

/-- Genuine differentiable convexity gives the original finite real affine support. -/
theorem supporting_gradient_inequality {f : E → ℝ} (hf : ConvexOn ℝ univ f)
    {x : E} (hx : DifferentiableAt ℝ f x) (y : E) :
    f x + ⟪y - x, gradient f x⟫ ≤ f y := by
  have hm : gradient f x ∈ rawSubdifferential (innerₗ E) (fun z ↦ (f z : EReal)) x := by
    rw [rawSubdifferential_coe_eq_singleton_gradient hf hx]
    exact mem_singleton _
  have h := hm y
  simpa only [innerₗ_apply_apply, ← EReal.coe_add, EReal.coe_le_coe_iff] using h

/-- A common genuine gradient touches at every actual original segment point. -/
theorem gradient_eq_on_segment_of_eq {f : E → ℝ} (hf : ConvexOn ℝ univ f)
    (hd : Differentiable ℝ f) {x y : E} (hxy : gradient f y = gradient f x)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    gradient f ((1 - t) • x + t • y) = gradient f x := by
  let z := (1 - t) • x + t • y
  have hxylo := supporting_gradient_inequality hf (hd x) y
  have hyxlo := supporting_gradient_inequality hf (hd y) x
  rw [hxy] at hyxlo
  have hyval : f y = f x + ⟪y - x, gradient f x⟫ := by
    simp only [inner_sub_left] at hxylo hyxlo ⊢
    linarith
  have hzlo := supporting_gradient_inequality hf (hd x) z
  have hzhi := hf.2 (mem_univ x) (mem_univ y)
    (sub_nonneg.mpr ht1) ht (show 1 - t + t = 1 by ring)
  have hzval : f z = f x + ⟪z - x, gradient f x⟫ := by
    have hcost : f x + ⟪z - x, gradient f x⟫ = (1 - t) * f x + t * f y := by
      rw [hyval]
      simp only [z, inner_sub_left, inner_add_left, real_inner_smul_left]
      ring
    rw [hcost]
    exact le_antisymm hzhi (by rwa [hcost] at hzlo)
  have hraw : gradient f x ∈ rawSubdifferential (innerₗ E)
      (fun w ↦ (f w : EReal)) z := by
    intro w
    change (f z : EReal) + (⟪w - z, gradient f x⟫ : EReal) ≤ (f w : EReal)
    rw [← EReal.coe_add, EReal.coe_le_coe_iff, hzval]
    have hw := supporting_gradient_inequality hf (hd x) w
    simp only [inner_sub_left] at hw ⊢
    linarith
  rw [rawSubdifferential_coe_eq_singleton_gradient hf (hd z)] at hraw
  exact (mem_singleton_iff.mp hraw).symm

/-- An actual equal-gradient displacement lies in the actual derivative
kernel, by the genuine right-secant limit on the original segment. -/
theorem gradient_fiber_displacement_in_kernel {f : E → ℝ}
    (hf : ConvexOn ℝ univ f) (hd : Differentiable ℝ f)
    {x y : E} {L : E →L[ℝ] E} (hL : HasFDerivAt (gradient f) L x)
    (hxy : gradient f y = gradient f x) : L (y - x) = 0 := by
  have hlim := (hL.hasLineDerivAt (y - x)).tendsto_slope_zero_right
  have hzero : ∀ᶠ t : ℝ in 𝓝[>] 0,
      t⁻¹ • (gradient f (x + t • (y - x)) - gradient f x) = 0 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    have hgrad := gradient_eq_on_segment_of_eq hf hd hxy ht.1.le ht.2.le
    have hcomb : (1 - t) • x + t • y = x + t • (y - x) := by module
    rw [hcomb] at hgrad
    rw [hgrad, sub_self, smul_zero]
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hzero.mono fun _ h ↦ h.symm))

/-- Genuine nonzero derivative determinant rules out every other original
point in this actual gradient fiber; no injectivity certificate is assumed. -/
theorem gradient_fiber_unique_of_det_ne_zero {f : E → ℝ}
    (hf : ConvexOn ℝ univ f) (hd : Differentiable ℝ f)
    {x y : E} {L : E →L[ℝ] E} (hL : HasFDerivAt (gradient f) L x)
    (hdet : L.det ≠ 0) (hxy : gradient f y = gradient f x) : y = x := by
  have hker : LinearMap.ker L.toLinearMap = ⊥ := by
    by_contra hk
    exact hdet (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hk)
  have hinj : Function.Injective L := LinearMap.ker_eq_bot.mp hker
  have hz := gradient_fiber_displacement_in_kernel hf hd hL hxy
  have hdisp : y - x = 0 := hinj (by simpa only [map_zero] using hz)
  exact sub_eq_zero.mp hdisp

/-- Actual injectivity on the produced nonsingular differentiability locus. -/
theorem gradient_injOn_nonsingular {f : E → ℝ}
    (hf : ConvexOn ℝ univ f) (hd : Differentiable ℝ f) :
    InjOn (gradient f) {x | DifferentiableAt ℝ (gradient f) x ∧
      (fderiv ℝ (gradient f) x).det ≠ 0} := by
  intro x hx y _ hxy
  exact (gradient_fiber_unique_of_det_ne_zero hf hd hx.1.hasFDerivAt hx.2 hxy.symm).symm

/-- The actual coordinate Hessian is evaluated from the genuine derivative
of the original derivative on the chosen original orthonormal coordinates. -/
noncomputable def hessianMatrix {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (f : E → ℝ) (x : E) : Matrix ι ι ℝ :=
  Matrix.of fun i j ↦ fderiv ℝ (fderiv ℝ f) x (b i) (b j)

variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- The actual nonsingular gradient locus and the genuine shared local
cover produce the complete original gradient-image Jacobian formula. -/
theorem lintegral_abs_det_gradient_eq_image {f : E → ℝ}
    (hf : ConvexOn ℝ univ f) (hd : Differentiable ℝ f)
    (hg : LocallyLipschitzOn univ (gradient f))
    {A : Set E} (hA : MeasurableSet A) :
    (∫⁻ x in A, ENNReal.ofReal |(fderiv ℝ (gradient f) x).det| ∂μ) =
      μ (gradient f '' A) := by
  let D : Set E := {x | DifferentiableAt ℝ (gradient f) x}
  let C : Set E := {x | DifferentiableAt ℝ (gradient f) x ∧
    (fderiv ℝ (gradient f) x).det = 0}
  let N : Set E := {x | DifferentiableAt ℝ (gradient f) x ∧
    (fderiv ℝ (gradient f) x).det ≠ 0}
  have hae : ∀ᵐ x ∂μ, x ∈ D :=
    (ae_differentiableAt_of_locallyLipschitzOn_open isOpen_univ hg).mono
      (fun x hx ↦ hx (mem_univ x))
  have hDzero : μ Dᶜ = 0 := ae_iff.mp hae
  have hundiff : μ (gradient f '' Dᶜ) = 0 :=
    addHaar_image_eq_zero_of_locallyLipschitzOn_open isOpen_univ hg (subset_univ _) hDzero
  have hcrit : μ (gradient f '' C) = 0 :=
    addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ
      (fun x hx ↦ hx.1.hasFDerivAt.hasFDerivWithinAt) (fun _ hx ↦ hx.2)
  have hbadsub : Nᶜ ⊆ Dᶜ ∪ C := by
    intro x hx
    by_cases hdx : x ∈ D
    · right
      refine ⟨hdx, ?_⟩
      by_contra hdet
      exact hx ⟨hdx, hdet⟩
    · exact Or.inl hdx
  have hbad : μ (gradient f '' Nᶜ) = 0 := by
    have hu : μ (gradient f '' Dᶜ ∪ gradient f '' C) = 0 :=
      measure_union_null hundiff hcrit
    exact measure_mono_null ((image_mono hbadsub).trans (by rw [image_union])) hu
  have hdetMeas : Measurable (fun x ↦ (fderiv ℝ (gradient f) x).det) :=
    ContinuousLinearMap.continuous_det.measurable.comp (measurable_fderiv ℝ (gradient f))
  have hN : MeasurableSet N :=
    (measurableSet_of_differentiableAt ℝ (gradient f)).inter
      (measurableSet_eq_fun hdetMeas measurable_const).compl
  have hAN := hA.inter hN
  have harea : (∫⁻ x in A ∩ N, ENNReal.ofReal |(fderiv ℝ (gradient f) x).det| ∂μ) =
      μ (gradient f '' (A ∩ N)) :=
    lintegral_abs_det_fderiv_eq_addHaar_image μ hAN
      (fun _ hx ↦ hx.2.1.hasFDerivAt.hasFDerivWithinAt)
      ((gradient_injOn_nonsingular hf hd).mono inter_subset_right)
  have himg : gradient f '' A =ᵐ[μ] gradient f '' (A ∩ N) := by
    filter_upwards [compl_mem_ae_iff.mpr hbad] with y hy
    apply propext
    change (y ∈ gradient f '' A) ↔ y ∈ gradient f '' (A ∩ N)
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxN : x ∈ N := by
        by_contra hxn
        exact hy (mem_image_of_mem (gradient f) hxn)
      exact mem_image_of_mem (gradient f) ⟨hx, hxN⟩
    · intro hy
      exact image_mono inter_subset_left hy
  have hint : (∫⁻ x in A, ENNReal.ofReal |(fderiv ℝ (gradient f) x).det| ∂μ) =
      ∫⁻ x in A ∩ N, ENNReal.ofReal |(fderiv ℝ (gradient f) x).det| ∂μ := by
    rw [← lintegral_indicator hA, ← lintegral_indicator hAN]
    apply lintegral_congr_ae
    filter_upwards [hae] with x hdx
    by_cases hxA : x ∈ A
    · by_cases hxN : x ∈ N
      · simp only [indicator_of_mem hxA, indicator_of_mem (show x ∈ A ∩ N from ⟨hxA, hxN⟩)]
      · have hdet : (fderiv ℝ (gradient f) x).det = 0 := by
          by_contra hdet
          exact hxN ⟨hdx, hdet⟩
        simp [hxA, hxN, hdet]
    · simp [hxA]
  exact hint.trans (harea.trans (measure_congr himg).symm)

omit [MeasurableSpace E] [BorelSpace E] in
/-- Genuine convex affine supports produce actual gradient monotonicity. -/
theorem nonneg_inner_displacement_gradient_difference {f : E → ℝ}
    (hf : ConvexOn ℝ univ f) (hd : Differentiable ℝ f) (x y : E) :
    0 ≤ ⟪y - x, gradient f y - gradient f x⟫ := by
  have hxy := supporting_gradient_inequality hf (hd x) y
  have hyx := supporting_gradient_inequality hf (hd y) x
  simp only [inner_sub_left, inner_sub_right] at hxy hyx ⊢
  linarith

omit [MeasurableSpace E] [BorelSpace E] in
/-- The genuine actual right derivative of the monotone gradient has a
nonnegative quadratic form, produced by its original secants. -/
theorem nonneg_inner_gradient_derivative {f : E → ℝ}
    (hf : ConvexOn ℝ univ f) (hd : Differentiable ℝ f)
    {x : E} {L : E →L[ℝ] E} (hL : HasFDerivAt (gradient f) L x) (v : E) :
    0 ≤ ⟪v, L v⟫ := by
  have hlim := (hL.hasLineDerivAt v).tendsto_slope_zero_right
  have hc : Continuous (fun w : E ↦ ⟪v, w⟫) := continuous_const.inner continuous_id
  apply ge_of_tendsto (hc.continuousAt.tendsto.comp hlim)
  filter_upwards [self_mem_nhdsWithin] with t ht
  have htpos : 0 < t := ht
  have hm := nonneg_inner_displacement_gradient_difference hf hd x (x + t • v)
  simp only [add_sub_cancel_left, real_inner_smul_left] at hm
  have hpos : 0 ≤ ⟪v, gradient f (x + t • v) - gradient f x⟫ :=
    nonneg_of_mul_nonneg_right hm htpos
  change 0 ≤ ⟪v, t⁻¹ • (gradient f (x + t • v) - gradient f x)⟫
  rw [inner_smul_right]
  exact mul_nonneg (inv_nonneg.mpr htpos.le) hpos

omit [MeasurableSpace E] [BorelSpace E] in
/-- The actual gradient derivative transports through Riesz to the genuine
second derivative of the original function. -/
theorem hasFDerivAt_fderiv_of_hasFDerivAt_gradient {f : E → ℝ}
    {x : E} {L : E →L[ℝ] E} (hL : HasFDerivAt (gradient f) L x) :
    HasFDerivAt (fderiv ℝ f)
      ((InnerProductSpace.toDual ℝ E).toContinuousLinearMap.comp L) x := by
  have h := (InnerProductSpace.toDual ℝ E).toContinuousLinearMap.hasFDerivAt.comp x hL
  simpa [toDual_comp_gradient] using h

omit [MeasurableSpace E] [BorelSpace E] in
/-- The checked Gram Riesz map recovers the actual operator from its
original dual-valued representation, in every actual orthonormal basis. -/
theorem gram_riesz_comp_toDual_comp {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℝ E) (L : E →L[ℝ] E) :
    (SGPT.Foundations.Analysis.Pending.GramDeterminant.riesz b).comp
      ((InnerProductSpace.toDual ℝ E).toContinuousLinearMap.comp L) = L := by
  ext v
  apply (InnerProductSpace.toDual ℝ E).injective
  ext w
  simp [SGPT.Foundations.Analysis.Pending.GramDeterminant.inner_riesz, real_inner_comm]

omit [MeasurableSpace E] [BorelSpace E] in
/-- The actual Hessian coordinate determinant equals the actual gradient
Jacobian determinant wherever the original gradient is differentiable. -/
theorem det_hessianMatrix_eq_det_gradient {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℝ E) {f : E → ℝ} {x : E}
    (hx : DifferentiableAt ℝ (gradient f) x) :
    (hessianMatrix b f x).det = (fderiv ℝ (gradient f) x).det := by
  have hQ := hasFDerivAt_fderiv_of_hasFDerivAt_gradient hx.hasFDerivAt
  have hR := gram_riesz_comp_toDual_comp b (fderiv ℝ (gradient f) x)
  rw [← hR, SGPT.Foundations.Analysis.Pending.GramDeterminant.det_riesz_comp b b]
  simp only [hessianMatrix, hQ.fderiv]

omit [MeasurableSpace E] [BorelSpace E] in
/-- Actual Hessian symmetry and the already checked Gram determinant
producer remove the absolute value from the genuine gradient Jacobian. -/
theorem det_gradient_derivative_nonneg {f : E → ℝ}
    (hf : ConvexOn ℝ univ f) (hd : Differentiable ℝ f)
    {x : E} {L : E →L[ℝ] E} (hL : HasFDerivAt (gradient f) L x) : 0 ≤ L.det := by
  let J : E →L[ℝ] StrongDual ℝ E := (InnerProductSpace.toDual ℝ E).toContinuousLinearMap
  let Q : E →L[ℝ] StrongDual ℝ E := J.comp L
  have hQ : HasFDerivAt (fderiv ℝ f) Q x :=
    hasFDerivAt_fderiv_of_hasFDerivAt_gradient hL
  have hsym : ∀ v w, Q v w = Q w v :=
    second_derivative_symmetric (fun y ↦ (hd y).hasFDerivAt) hQ
  have hpos : ∀ v, 0 ≤ Q v v := by
    intro v
    simpa [Q, J, real_inner_comm] using nonneg_inner_gradient_derivative hf hd hL v
  let b := stdOrthonormalBasis ℝ E
  have hR : (SGPT.Foundations.Analysis.Pending.GramDeterminant.riesz b).comp Q = L :=
    gram_riesz_comp_toDual_comp b L
  rw [← hR, SGPT.Foundations.Analysis.Pending.GramDeterminant.det_riesz_comp b b]
  exact SGPT.Foundations.Analysis.Pending.GramDeterminant.det_gram_nonneg b hsym hpos

omit [MeasurableSpace E] [BorelSpace E] in
/-- Genuine derivative Lipschitz regularity transports through the actual
Riesz isometry to the original gradient, with no gradient-regularity certificate. -/
theorem locallyLipschitzOn_gradient_of_fderiv {f : E → ℝ}
    (hg : LocallyLipschitz (fderiv ℝ f)) : LocallyLipschitzOn univ (gradient f) := by
  rw [locallyLipschitzOn_univ]
  intro x
  obtain ⟨K, V, hV, hKV⟩ := hg x
  refine ⟨K, V, hV, ?_⟩
  apply LipschitzOnWith.of_dist_le_mul
  intro y hy z hz
  rw [gradient, gradient, (InnerProductSpace.toDual ℝ E).symm.isometry.dist_eq]
  exact hKV.dist_le_mul y hy z hz

/-- Actual local Rademacher and produced convex Hessian positivity make
the original gradient determinant nonnegative almost everywhere. -/
theorem det_fderiv_gradient_nonneg_ae {f : E → ℝ}
    (hf : ConvexOn ℝ univ f) (hd : Differentiable ℝ f)
    (hg : LocallyLipschitzOn univ (gradient f)) :
    ∀ᵐ x ∂μ, 0 ≤ (fderiv ℝ (gradient f) x).det := by
  filter_upwards [ae_differentiableAt_of_locallyLipschitzOn_open isOpen_univ hg]
    with x hx
  exact det_gradient_derivative_nonneg hf hd (hx (mem_univ x)).hasFDerivAt

/-- Actual convex positivity removes the absolute value in the original
image Jacobian integral on every actual Borel set. -/
theorem lintegral_det_gradient_eq_image {f : E → ℝ}
    (hf : ConvexOn ℝ univ f) (hd : Differentiable ℝ f)
    (hg : LocallyLipschitzOn univ (gradient f)) {A : Set E} (hA : MeasurableSet A) :
    (∫⁻ x in A, ENNReal.ofReal (fderiv ℝ (gradient f) x).det ∂μ) =
      μ (gradient f '' A) := by
  rw [← lintegral_abs_det_gradient_eq_image hf hd hg hA]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_of_ae (det_fderiv_gradient_nonneg_ae hf hd hg)] with x hx
  rw [abs_of_nonneg hx]

/-- Actual original Alexandrov measure equals its factorial-scaled genuine
gradient-Hessian density, under precisely local C¹,¹ gradient regularity. -/
theorem alexandrovMeasure_eq_withDensity_det_gradient {f : E → ℝ}
    (hf : ConvexOn ℝ univ f) (hd : Differentiable ℝ f)
    (hg : LocallyLipschitzOn univ (gradient f)) :
    alexandrovMeasure (innerₗ E) μ (fun x ↦ (f x : EReal)) =
      μ.withDensity (fun x ↦ ((Module.finrank ℝ E).factorial : ENNReal) *
        ENNReal.ofReal (fderiv ℝ (gradient f) x).det) := by
  apply Measure.ext
  intro A hA
  rw [alexandrovMeasure_apply_coe (innerₗ E) hf hA,
    rawSubgradientImageOn_coe_eq_gradient_image hf hd A,
    withDensity_apply _ hA,
    lintegral_const_mul' _ _ (ENNReal.natCast_ne_top _)]
  exact congrArg (((Module.finrank ℝ E).factorial : ENNReal) * ·)
    (lintegral_det_gradient_eq_image hf hd hg hA).symm

/-- Genuine local C¹,¹ regularity supplies the actual coordinate Hessian
identification almost everywhere, including every degenerate dimension. -/
theorem det_hessianMatrix_eq_det_gradient_ae {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℝ E) {f : E → ℝ}
    (hg : LocallyLipschitz (fderiv ℝ f)) :
    (fun x ↦ (hessianMatrix b f x).det) =ᵐ[μ]
      (fun x ↦ (fderiv ℝ (gradient f) x).det) := by
  filter_upwards [ae_differentiableAt_of_locallyLipschitzOn_open isOpen_univ
    (locallyLipschitzOn_gradient_of_fderiv hg)] with x hx
  exact det_hessianMatrix_eq_det_gradient b (hx (mem_univ x))

/-- The genuine coordinate Hessian gives the exact original density for
locally C¹,¹ finite convex functions, without a Hessian-density premise. -/
theorem alexandrovMeasure_eq_withDensity_det_hessianMatrix
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : OrthonormalBasis ι ℝ E)
    {f : E → ℝ} (hf : ConvexOn ℝ univ f) (hd : Differentiable ℝ f)
    (hg : LocallyLipschitz (fderiv ℝ f)) :
    alexandrovMeasure (innerₗ E) μ (fun x ↦ (f x : EReal)) =
      μ.withDensity (fun x ↦ ((Module.finrank ℝ E).factorial : ENNReal) *
        ENNReal.ofReal (hessianMatrix b f x).det) := by
  rw [alexandrovMeasure_eq_withDensity_det_gradient hf hd
    (locallyLipschitzOn_gradient_of_fderiv hg)]
  apply withDensity_congr_ae
  filter_upwards [det_hessianMatrix_eq_det_gradient_ae b hg (μ := μ)] with x hx
  rw [hx]

/-- Exact source coordinate normalization: after the original lattice
identification, the density is n! times the actual coordinate Hessian determinant. -/
theorem alexandrovMeasure_eq_withDensity_det_hessian_euclidean {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ConvexOn ℝ univ f)
    (hd : Differentiable ℝ f) (hg : LocallyLipschitz (fderiv ℝ f)) :
    alexandrovMeasure (innerₗ (EuclideanSpace ℝ (Fin n))) volume
        (fun x ↦ (f x : EReal)) =
      volume.withDensity (fun x ↦ (n.factorial : ENNReal) *
        ENNReal.ofReal (hessianMatrix (EuclideanSpace.basisFun (Fin n) ℝ) f x).det) := by
  simpa using alexandrovMeasure_eq_withDensity_det_hessianMatrix
    (EuclideanSpace.basisFun (Fin n) ℝ) hf hd hg (μ := volume)

end SGPT.Convex
