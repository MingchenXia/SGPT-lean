import SGPT.Foundations.Analysis.Pending.NaturalHermitianFrozenHodgeEnergy

/-! # Internally proved local Gårding estimates in the unchanged original norms -/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators

namespace SGPT.Foundations.Analysis.Pending.NaturalHermitianLocalGarding

open FirstPass FirstPass.MongeAmpere NaturalHermitianFirstOrderCoefficients
  NaturalHermitianFrozenHodgeEnergy NaturalHermitianFrozenPrincipalEnergy
  NaturalHermitianExteriorCliffordSymbol NaturalHermitianSmoothFormMetric
  NaturalHermitianOriginalFormMetric NaturalHermitianMusicalInverse
  NaturalHermitianMetricCoefficients NaturalHermitianOrthonormalFormBasis
  NaturalHermitianUnitVolume NaturalHermitianHodgeStarSquare ConstantFormProducts
  NaturalHermitianHodgePrincipalSymbol

variable {n : ℕ}

local instance formNormedAddCommGroup (q : ℕ) : NormedAddCommGroup (FormCoefficients n q) :=
  ContinuousAlternatingMap.instNormedAddCommGroup

local instance formNormedSpace (q : ℕ) : NormedSpace ℝ (FormCoefficients n q) :=
  ContinuousAlternatingMap.instNormedSpace

local instance formDualNormedAddCommGroup (q : ℕ) :
    NormedAddCommGroup (FormCoefficients n q →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance formDualNormedSpace (q : ℕ) : NormedSpace ℝ (FormCoefficients n q →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

local instance formBilinearNormedAddCommGroup (q : ℕ) :
    NormedAddCommGroup (FormCoefficients n q →L[ℝ] FormCoefficients n q →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance formBilinearNormedSpace (q : ℕ) :
    NormedSpace ℝ (FormCoefficients n q →L[ℝ] FormCoefficients n q →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- A positive constant from the actual continuous exterior dictionary, with the old norm retained. -/
def formMetricCoercivityConstant (a : FormCoefficients n 2)
    (hJ : IsOneOne a) (hp : IsStrictlyPositive a) (q : ℕ) : ℝ :=
  ((1 + ‖(originalFormDictionary a hJ hp q).toContinuousLinearMap‖) ^ 2)⁻¹

/-- The actual dictionary supplies a positive denominator even for a zero exterior space. -/
theorem formMetricCoercivityConstant_pos (a : FormCoefficients n 2)
    (hJ : IsOneOne a) (hp : IsStrictlyPositive a) (q : ℕ) :
    0 < formMetricCoercivityConstant a hJ hp q := by
  unfold formMetricCoercivityConstant
  positivity

/-- Coercivity is a comparison with the original alternating operator norm, not a new norm instance. -/
theorem original_form_metric_coercive (a : FormCoefficients n 2)
    (hJ : IsOneOne a) (hp : IsStrictlyPositive a) (q : ℕ)
    (η : FormCoefficients n q) :
    formMetricCoercivityConstant a hJ hp q * ‖η‖ ^ 2 ≤
      originalFormMetric a hJ hp q η η := by
  let E := originalFormDictionary a hJ hp q
  let ξ := E.symm η
  have h1 : ‖η‖ ≤ ‖E.toContinuousLinearMap‖ * ‖ξ‖ := by
    calc
      ‖η‖ = ‖E ξ‖ := by simp only [ξ, ContinuousLinearEquiv.apply_symm_apply]
      _ ≤ ‖E.toContinuousLinearMap‖ * ‖ξ‖ := E.toContinuousLinearMap.le_opNorm ξ
  have h2 : ‖η‖ ≤ (1 + ‖E.toContinuousLinearMap‖) * ‖ξ‖ := by
    nlinarith [norm_nonneg ξ]
  have hsq : ‖η‖ ^ 2 ≤ (1 + ‖E.toContinuousLinearMap‖) ^ 2 * ‖ξ‖ ^ 2 := by
    nlinarith [norm_nonneg η, norm_nonneg ξ, norm_nonneg E.toContinuousLinearMap]
  have hd : 0 < (1 + ‖E.toContinuousLinearMap‖) ^ 2 := by positivity
  rw [originalFormMetric_apply, real_inner_self_eq_norm_sq]
  change ((1 + ‖E.toContinuousLinearMap‖) ^ 2)⁻¹ * ‖η‖ ^ 2 ≤ ‖ξ‖ ^ 2
  rw [inv_mul_eq_div]
  exact (div_le_iff₀ hd).mpr (by simpa only [mul_comm] using hsq)

/-- The genuine whole continuous bilinear form gives the original norm upper estimate. -/
theorem original_form_metric_norm_upper (a : FormCoefficients n 2)
    (hJ : IsOneOne a) (hp : IsStrictlyPositive a) (q : ℕ)
    (η : FormCoefficients n q) :
    |originalFormMetric a hJ hp q η η| ≤
      ‖originalFormMetric a hJ hp q‖ * ‖η‖ ^ 2 := by
  let G := originalFormMetric a hJ hp q
  calc
    |G η η| = ‖G η η‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖G η‖ * ‖η‖ := (G η).le_opNorm η
    _ ≤ (‖G‖ * ‖η‖) * ‖η‖ := mul_le_mul_of_nonneg_right (G.le_opNorm η) (norm_nonneg η)
    _ = ‖G‖ * ‖η‖ ^ 2 := by ring

/-- The actual old-norm coordinate covectors supply a positive full-jet comparison constant. -/
def coordinateJetBound (b : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n)) : ℝ :=
  1 + ∑ i, ‖coordinateCovector b i‖ ^ 2

/-- Dimension zero has the same genuinely positive comparison constant. -/
theorem coordinateJetBound_pos (b : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n)) :
    0 < coordinateJetBound b := by
  unfold coordinateJetBound
  positivity

/-- The entire original jet operator norm is controlled by any actual finite basis. -/
theorem original_jet_norm_sq_le_coordinates
    (b : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n)) (q : ℕ)
    (L : ComplexModel n →L[ℝ] FormCoefficients n q) :
    ‖L‖ ^ 2 ≤ coordinateJetBound b * ∑ i, ‖L (b i)‖ ^ 2 := by
  classical
  have hnorm : ‖L‖ ≤ ∑ i, ‖coordinateCovector b i‖ * ‖L (b i)‖ := by
    calc
      ‖L‖ = ‖∑ i, (coordinateCovector b i).smulRight (L (b i))‖ := by
        conv_lhs => rw [originalJet_eq_coordinate_sum b q L]
      _ ≤ ∑ i, ‖(coordinateCovector b i).smulRight (L (b i))‖ := norm_sum_le _ _
      _ = _ := by simp only [ContinuousLinearMap.norm_smulRight_apply]
  have hsum : 0 ≤ ∑ i, ‖coordinateCovector b i‖ * ‖L (b i)‖ :=
    Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hsquare : ‖L‖ ^ 2 ≤ (∑ i, ‖coordinateCovector b i‖ * ‖L (b i)‖) ^ 2 := by
    nlinarith [norm_nonneg L]
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => ‖coordinateCovector b i‖) (fun i => ‖L (b i)‖)
  have hnonneg : 0 ≤ ∑ i, ‖L (b i)‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  unfold coordinateJetBound
  nlinarith

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The literal operator vanishes off the original closed support, without off-target smoothness. -/
theorem localCodifferential_eq_zero_of_notMem_tsupport
    (w : SmoothRealForm n M 2) (e : ComplexChart n M) (q : ℕ)
    (A : ComplexModel n → FormCoefficients n q) (x : ComplexModel n)
    (hx : x ∉ tsupport A) : localCodifferential w e q A x = 0 := by
  classical
  unfold localCodifferential
  split
  · rfl
  · split
    · rename_i hzero hq
      let B : ComplexModel n → FormCoefficients n (2 * n - (q - 1 + 1)) :=
        fun y => degreeStar w e y (q - 1 + 1)
          (castForm (show q = q - 1 + 1 by omega) (A y))
      have hs : tsupport B ⊆ tsupport A := by
        apply closure_mono
        intro y hy
        change B y ≠ 0 at hy
        change A y ≠ 0
        intro hAy
        apply hy
        simp only [B, hAy, map_zero]
      have hd : fderiv ℝ B x = 0 := fderiv_of_notMem_tsupport ℝ (fun h => hx (hs h))
      change (-1 : ℝ) • castForm _ (degreeStar w e x _
        (ContinuousAlternatingMap.alternatizeUncurryFin (fderiv ℝ B x))) = 0
      rw [hd]
      simp only [← ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply, map_zero, smul_zero]
    · rfl

/-- Actual closed support of the literal variable codifferential stays in that of the input. -/
theorem tsupport_localCodifferential_subset
    (w : SmoothRealForm n M 2) (e : ComplexChart n M) (q : ℕ)
    (A : ComplexModel n → FormCoefficients n q) :
    tsupport (localCodifferential w e q A) ⊆ tsupport A := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_contra h
  exact hx (localCodifferential_eq_zero_of_notMem_tsupport w e q A x h)

/-- Actual chart support glues the true C¹ first-jet formula with its genuine zero exterior. -/
theorem localCodifferential_contDiff_of_chart_support
    (w : SmoothRealForm n M 2) (hw : w.IsHermitian) (e : ComplexChart n M) (q : ℕ)
    (A : ComplexModel n → FormCoefficients n q) (hA : ContDiff ℝ 2 A)
    (hs : tsupport A ⊆ e.val.target) : ContDiff ℝ 1 (localCodifferential w e q A) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ tsupport A
  · have htarget := e.val.open_target.mem_nhds (hs hx)
    have hP : ContDiffAt ℝ 1 (fun y => principalJetCLM w e q y) x :=
      ((principalJet_smooth w hw e q).contDiffAt htarget).of_le (by simp)
    have hZ : ContDiffAt ℝ 1 (fun y => zeroOrderCLM w e q y) x :=
      ((zeroOrder_smooth w hw e q).contDiffAt htarget).of_le (by simp)
    have hDA : ContDiffAt ℝ 1 (fderiv ℝ A) x :=
      (hA.fderiv_right (m := 1) (by norm_num)).contDiffAt
    have heq : localCodifferential w e q A =ᶠ[𝓝 x]
        (fun y => principalJetCLM w e q y (fderiv ℝ A y) + zeroOrderCLM w e q y (A y)) := by
      filter_upwards [htarget] with y hy
      exact localCodifferential_eq_first_jet w hw e q y hy A
        (hA.differentiable (by norm_num) y)
    exact ((hP.clm_apply hDA).add
      (hZ.clm_apply (hA.contDiffAt.of_le (by norm_num)))).congr_of_eventuallyEq heq
  · have hz : localCodifferential w e q A =ᶠ[𝓝 x] 0 := by
      filter_upwards [(isClosed_tsupport A).isOpen_compl.mem_nhds hx] with y hy
      exact localCodifferential_eq_zero_of_notMem_tsupport w e q A y hy
    exact contDiffAt_const.congr_of_eventuallyEq hz

section NormSquareIntegration

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- Actual continuous compact support supplies integrability of its original norm square. -/
theorem integrable_norm_sq_of_compact_support {f : E → F}
    (hf : Continuous f) (hc : HasCompactSupport f) :
    Integrable (fun x => ‖f x‖ ^ 2) μ := by
  apply (hf.norm.pow 2).integrable_of_hasCompactSupport
  rw [hasCompactSupport_iff_eventuallyEq] at hc ⊢
  exact hc.mono fun x hx => by simp only [Pi.zero_apply] at hx; simp [hx]

end NormSquareIntegration

/-- The lower metric comparison reads back literally to the original chart field. -/
theorem chart_form_metric_coercive (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e : ComplexChart n M) (z : ComplexModel n) (hz : z ∈ e.val.target)
    (q : ℕ) (η : FormCoefficients n q) :
    formMetricCoercivityConstant (w.coeff e z) (hw e z hz).1 (hw e z hz).2 q * ‖η‖ ^ 2 ≤
      formMetricCoefficients w e z q η η := by
  rw [formMetricCoefficients_eq_original w hw e z hz]
  exact original_form_metric_coercive _ _ _ q η

/-- Whole original chart bilinear metric, with its same original operator norm. -/
theorem chart_form_metric_norm_upper (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e : ComplexChart n M) (z : ComplexModel n) (hz : z ∈ e.val.target)
    (q : ℕ) (η : FormCoefficients n q) :
    formMetricCoefficients w e z q η η ≤ ‖formMetricCoefficients w e z q‖ * ‖η‖ ^ 2 := by
  have h := original_form_metric_norm_upper (w.coeff e z) (hw e z hz).1
    (hw e z hz).2 q η
  rw [← formMetricCoefficients_eq_original w hw e z hz] at h
  exact (le_abs_self _).trans h

/-- The numerical square estimate used on the actual three first-jet terms. -/
theorem three_term_square_le (u v t : ℝ) :
    (u + v + t) ^ 2 ≤ 3 * (u ^ 2 + v ^ 2 + t ^ 2) := by
  nlinarith [sq_nonneg (u - v), sq_nonneg (u - t), sq_nonneg (v - t)]

/-- Pure real absorption of the preceding genuinely produced integral bounds. -/
theorem garding_real_absorption (c B J ε C₀ a d δ j g : ℝ)
    (hc : 0 < c) (hB : 0 < B) (ha : 0 ≤ a) (hd : 0 ≤ d) (hδ : 0 ≤ δ)
    (hsmall : 3 * B * ε ^ 2 * J = c / 4)
    (hjet : j ≤ J * g)
    (henergy : c * g ≤ B * d + 3 * B * (δ + ε ^ 2 * j + C₀ ^ 2 * a)) :
    a + g ≤ (2 + 4 * B * (1 + C₀ ^ 2) / c) * (a + d + δ) := by
  let C := 2 + 4 * B * (1 + C₀ ^ 2) / c
  have hcC : c * C = 2 * c + 4 * B * (1 + C₀ ^ 2) := by dsimp [C]; field_simp
  have herror := mul_le_mul_of_nonneg_left hjet (by positivity : 0 ≤ 3 * B * ε ^ 2)
  have herror' : 3 * B * ε ^ 2 * j ≤ (c / 4) * g := by
    calc
      _ ≤ 3 * B * ε ^ 2 * (J * g) := herror
      _ = (c / 4) * g := by rw [← mul_assoc, hsmall]
  have hAbsorbed : (3 * c / 4) * g ≤ B * d + 3 * B * δ + 3 * B * C₀ ^ 2 * a := by
    nlinarith only [henergy, herror']
  have hAcoeff : (c + 4 * B * C₀ ^ 2) * a ≤ (c * C) * a := by
    apply mul_le_mul_of_nonneg_right _ ha
    rw [hcC]
    nlinarith only [hc, hB]
  have hDcoeff : (4 * B / 3) * d ≤ (c * C) * d := by
    apply mul_le_mul_of_nonneg_right _ hd
    rw [hcC]
    nlinarith only [hc, hB, mul_nonneg hB.le (sq_nonneg C₀)]
  have hδcoeff : (4 * B) * δ ≤ (c * C) * δ := by
    apply mul_le_mul_of_nonneg_right _ hδ
    rw [hcC]
    nlinarith only [hc, mul_nonneg hB.le (sq_nonneg C₀)]
  change a + g ≤ C * (a + d + δ)
  apply (mul_le_mul_iff_left₀ hc).mp
  nlinarith only [hAbsorbed, hAcoeff, hDcoeff, hδcoeff]

/-- All actual chart norm-square energies are internally integrable against the same original Haar measure. -/
theorem integrable_original_chart_energies
    (μ : Measure (ComplexModel n)) [μ.IsAddHaarMeasure]
    (w : SmoothRealForm n M 2) (hw : w.IsHermitian) (e : ComplexChart n M) (q : ℕ)
    (A : ComplexModel n → FormCoefficients n q) (hA : ContDiff ℝ 2 A)
    (hc : HasCompactSupport A) (hs : tsupport A ⊆ e.val.target) :
    Integrable (fun x => ‖A x‖ ^ 2) μ ∧
      Integrable (fun x => ‖fderiv ℝ A x‖ ^ 2) μ ∧
      Integrable (fun x => ‖extDeriv A x‖ ^ 2) μ ∧
      Integrable (fun x => ‖localCodifferential w e q A x‖ ^ 2) μ ∧
      ∀ v, Integrable (fun x => ‖fderiv ℝ A x v‖ ^ 2) μ := by
  let T : (ComplexModel n →L[ℝ] FormCoefficients n q) →L[ℝ] FormCoefficients n (q + 1) :=
    ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (ComplexModel n) ℝ
  have hDA := hA.continuous_fderiv (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  have hδ := localCodifferential_contDiff_of_chart_support w hw e q A hA hs
  have hcδ : HasCompactSupport (localCodifferential w e q A) :=
    hc.of_isClosed_subset (isClosed_tsupport _) (tsupport_localCodifferential_subset w e q A)
  refine ⟨integrable_norm_sq_of_compact_support μ hA.continuous hc,
    integrable_norm_sq_of_compact_support μ hDA (hc.fderiv (𝕜 := ℝ)), ?_,
    integrable_norm_sq_of_compact_support μ hδ.continuous hcδ, ?_⟩
  · exact integrable_norm_sq_of_compact_support μ (T.continuous.comp hDA)
      (hasCompactSupport_clm T (hc.fderiv (𝕜 := ℝ)))
  · intro v
    exact integrable_norm_sq_of_compact_support μ (hDA.clm_apply continuous_const)
      (hc.fderiv_apply (𝕜 := ℝ) v)

/-- The genuine variable original codifferential supplies an internal local Gårding estimate. -/
theorem exists_original_local_garding_estimate
    (μ : Measure (ComplexModel n)) [μ.IsAddHaarMeasure]
    (w : SmoothRealForm n M 2) (hw : w.IsHermitian) (e : ComplexChart n M)
    (z : ComplexModel n) (hz : z ∈ e.val.target) (q : ℕ) :
    ∃ b : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n),
      (∀ i j, associatedMetricCLM (w.coeff e z) (b i) (b j) = if i = j then 1 else 0) ∧
      b.orientation = (coordinateRealBasis n).orientation ∧
      ∃ r > 0, ∃ C > 0, Metric.ball z r ⊆ e.val.target ∧
        ∀ (A : ComplexModel n → FormCoefficients n q), ContDiff ℝ 2 A →
          HasCompactSupport A → tsupport A ⊆ Metric.ball z r →
          (Integrable (fun x => ‖A x‖ ^ 2) μ ∧
            Integrable (fun x => ‖fderiv ℝ A x‖ ^ 2) μ ∧
            Integrable (fun x => ‖extDeriv A x‖ ^ 2) μ ∧
            Integrable (fun x => ‖localCodifferential w e q A x‖ ^ 2) μ ∧
            ∀ i, Integrable (fun x => ‖fderiv ℝ A x (b i)‖ ^ 2) μ) ∧
          (∫ x, ‖A x‖ ^ 2 ∂μ) + (∑ i, ∫ x, ‖fderiv ℝ A x (b i)‖ ^ 2 ∂μ) ≤
            C * ((∫ x, ‖A x‖ ^ 2 ∂μ) + (∫ x, ‖extDeriv A x‖ ^ 2 ∂μ) +
              (∫ x, ‖localCodifferential w e q A x‖ ^ 2 ∂μ)) := by
  classical
  obtain ⟨b, hb, ho⟩ := exists_positive_metric_orthonormal_basis (hw e z hz).1 (hw e z hz).2
  let c := formMetricCoercivityConstant (w.coeff e z) (hw e z hz).1 (hw e z hz).2 q
  let J := coordinateJetBound b
  let B := 1 + ‖formMetricCoefficients w e z (q + 1)‖ +
    ‖formMetricCoefficients w e z (q - 1)‖
  have hcpos : 0 < c := formMetricCoercivityConstant_pos _ _ _ q
  have hJpos : 0 < J := coordinateJetBound_pos b
  have hBpos : 0 < B := by dsimp [B]; positivity
  let ε := Real.sqrt (c / (12 * B * J))
  have hεpos : 0 < ε := Real.sqrt_pos.mpr (div_pos hcpos (by positivity))
  have hεsq : ε ^ 2 = c / (12 * B * J) := Real.sq_sqrt (by positivity)
  have habs : 3 * B * ε ^ 2 * J = c / 4 := by
    rw [hεsq]
    field_simp
    ring
  obtain ⟨r, hr, C₀, hC₀, hball, hfreeze⟩ :=
    exists_original_local_first_order_freezing_estimate w hw e q z hz ε hεpos
  let C := 2 + 4 * B * (1 + C₀ ^ 2) / c
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨b, hb, ho, r, hr, C, hC, hball, ?_⟩
  intro A hA hc hs
  have HI := integrable_original_chart_energies μ w hw e q A hA hc (hs.trans hball)
  have hAi := HI.1
  have hJi := HI.2.1
  have hdi := HI.2.2.1
  have hδi := HI.2.2.2.1
  have hVi (i : Fin (n * 2)) := HI.2.2.2.2 (b i)
  refine ⟨⟨hAi, hJi, hdi, hδi, hVi⟩, ?_⟩
  have HF := integral_frozen_hodge_energy μ w hw e z hz q b hb A hA hc
  have hgn : 0 ≤ ‖formMetricCoefficients w e z (q + 1)‖ :=
    norm_nonneg (formMetricCoefficients w e z (q + 1))
  have hdn : 0 ≤ ‖formMetricCoefficients w e z (q - 1)‖ :=
    norm_nonneg (formMetricCoefficients w e z (q - 1))
  have hGBd : ‖formMetricCoefficients w e z (q + 1)‖ ≤ B := by dsimp [B]; linarith
  have hGBδ : ‖formMetricCoefficients w e z (q - 1)‖ ≤ B := by dsimp [B]; linarith
  have hlower : c * (∑ i, ∫ x, ‖fderiv ℝ A x (b i)‖ ^ 2 ∂μ) ≤
      (∫ x, formMetricCoefficients w e z (q + 1) (extDeriv A x) (extDeriv A x) ∂μ) +
      (∫ x, formMetricCoefficients w e z (q - 1)
        (frozenCodifferential w e z q A x) (frozenCodifferential w e z q A x) ∂μ) := by
    rw [HF.2, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [← integral_const_mul]
    exact integral_mono ((hVi i).const_mul c) (HF.1.2.2 i)
      (fun x => chart_form_metric_coercive w hw e z hz q (fderiv ℝ A x (b i)))
  have hdUpper := integral_mono HF.1.1 (hdi.const_mul B) (fun x =>
    (chart_form_metric_norm_upper w hw e z hz (q + 1) (extDeriv A x)).trans
      (mul_le_mul_of_nonneg_right hGBd (sq_nonneg _)))
  rw [integral_const_mul] at hdUpper
  have hfrozenNorm (x : ComplexModel n) :
      ‖frozenCodifferential w e z q A x‖ ≤
        ‖localCodifferential w e q A x‖ + ε * ‖fderiv ℝ A x‖ + C₀ * ‖A x‖ := by
    by_cases hx : x ∈ Metric.ball z r
    · have he := (hfreeze x hx).2.2 A (hA.differentiable (by norm_num) x)
      change ‖localCodifferential w e q A x - frozenCodifferential w e z q A x‖ ≤ _ at he
      calc
        ‖frozenCodifferential w e z q A x‖ =
            ‖localCodifferential w e q A x -
              (localCodifferential w e q A x - frozenCodifferential w e z q A x)‖ := by
          congr 1
          abel
        _ ≤ ‖localCodifferential w e q A x‖ +
            ‖localCodifferential w e q A x - frozenCodifferential w e z q A x‖ := norm_sub_le _ _
        _ ≤ _ := by linarith
    · have hxs : x ∉ tsupport A := fun h => hx (hs h)
      have hAz := image_eq_zero_of_notMem_tsupport hxs
      have hDz := fderiv_of_notMem_tsupport ℝ hxs
      have hδz := localCodifferential_eq_zero_of_notMem_tsupport w e q A x hxs
      simp only [frozenCodifferential, hDz, map_zero, hAz, hδz, norm_zero, mul_zero, add_zero]
      rfl
  have hfrozenSq (x : ComplexModel n) :
      ‖frozenCodifferential w e z q A x‖ ^ 2 ≤
        3 * (‖localCodifferential w e q A x‖ ^ 2 + ε ^ 2 * ‖fderiv ℝ A x‖ ^ 2 +
          C₀ ^ 2 * ‖A x‖ ^ 2) := by
    have hright : 0 ≤ ‖localCodifferential w e q A x‖ + ε * ‖fderiv ℝ A x‖ + C₀ * ‖A x‖ :=
      by positivity
    calc
      _ ≤ (‖localCodifferential w e q A x‖ + ε * ‖fderiv ℝ A x‖ + C₀ * ‖A x‖) ^ 2 := by
        nlinarith [hfrozenNorm x, norm_nonneg (frozenCodifferential w e z q A x)]
      _ ≤ _ := by
        simpa only [mul_pow] using three_term_square_le
          ‖localCodifferential w e q A x‖ (ε * ‖fderiv ℝ A x‖) (C₀ * ‖A x‖)
  have hδUpper := integral_mono HF.1.2.1
    ((hδi.add (hJi.const_mul (ε ^ 2))).add (hAi.const_mul (C₀ ^ 2)) |>.const_mul (3 * B))
    (fun x => by
      calc
        _ ≤ B * ‖frozenCodifferential w e z q A x‖ ^ 2 :=
          (chart_form_metric_norm_upper w hw e z hz (q - 1) _).trans
            (mul_le_mul_of_nonneg_right hGBδ (sq_nonneg _))
        _ ≤ B * (3 * (‖localCodifferential w e q A x‖ ^ 2 +
            ε ^ 2 * ‖fderiv ℝ A x‖ ^ 2 + C₀ ^ 2 * ‖A x‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left (hfrozenSq x) hBpos.le
        _ = _ := by simp only [Pi.add_apply]; ring)
  simp only [Pi.add_apply] at hδUpper
  have hIntFirst :
      (∫ x, ‖localCodifferential w e q A x‖ ^ 2 + ε ^ 2 * ‖fderiv ℝ A x‖ ^ 2 ∂μ) =
        (∫ x, ‖localCodifferential w e q A x‖ ^ 2 ∂μ) +
          ε ^ 2 * (∫ x, ‖fderiv ℝ A x‖ ^ 2 ∂μ) := by
    calc
      _ = (∫ x, ‖localCodifferential w e q A x‖ ^ 2 ∂μ) +
          (∫ x, ε ^ 2 * ‖fderiv ℝ A x‖ ^ 2 ∂μ) := integral_add hδi (hJi.const_mul (ε ^ 2))
      _ = _ := by rw [integral_const_mul]
  have hIntSum :
      (∫ x, ‖localCodifferential w e q A x‖ ^ 2 + ε ^ 2 * ‖fderiv ℝ A x‖ ^ 2 +
        C₀ ^ 2 * ‖A x‖ ^ 2 ∂μ) = (∫ x, ‖localCodifferential w e q A x‖ ^ 2 ∂μ) +
          ε ^ 2 * (∫ x, ‖fderiv ℝ A x‖ ^ 2 ∂μ) + C₀ ^ 2 * (∫ x, ‖A x‖ ^ 2 ∂μ) := by
    calc
      _ = (∫ x, ‖localCodifferential w e q A x‖ ^ 2 + ε ^ 2 * ‖fderiv ℝ A x‖ ^ 2 ∂μ) +
          (∫ x, C₀ ^ 2 * ‖A x‖ ^ 2 ∂μ) :=
        integral_add (hδi.add (hJi.const_mul (ε ^ 2))) (hAi.const_mul (C₀ ^ 2))
      _ = _ := by rw [hIntFirst, integral_const_mul]
  rw [integral_const_mul, hIntSum] at hδUpper
  have hJetUpper := integral_mono hJi
    ((integrable_finsetSum Finset.univ (fun i _ => hVi i)).const_mul J)
    (fun x => original_jet_norm_sq_le_coordinates b q (fderiv ℝ A x))
  rw [integral_const_mul, integral_finsetSum _ (fun i _ => hVi i)] at hJetUpper
  let aI := ∫ x, ‖A x‖ ^ 2 ∂μ
  let dI := ∫ x, ‖extDeriv A x‖ ^ 2 ∂μ
  let δI := ∫ x, ‖localCodifferential w e q A x‖ ^ 2 ∂μ
  let jI := ∫ x, ‖fderiv ℝ A x‖ ^ 2 ∂μ
  let gI := ∑ i, ∫ x, ‖fderiv ℝ A x (b i)‖ ^ 2 ∂μ
  have haN : 0 ≤ aI := integral_nonneg fun _ => sq_nonneg _
  have hdN : 0 ≤ dI := integral_nonneg fun _ => sq_nonneg _
  have hδN : 0 ≤ δI := integral_nonneg fun _ => sq_nonneg _
  change jI ≤ J * gI at hJetUpper
  have hCombined : c * gI ≤ B * dI + 3 * B * (δI + ε ^ 2 * jI + C₀ ^ 2 * aI) :=
    hlower.trans (add_le_add hdUpper hδUpper)
  change aI + gI ≤ C * (aI + dI + δI)
  exact garding_real_absorption c B J ε C₀ aI dI δI jI gI
    hcpos hBpos haN hdN hδN habs hJetUpper hCombined

end SGPT.Foundations.Analysis.Pending.NaturalHermitianLocalGarding
