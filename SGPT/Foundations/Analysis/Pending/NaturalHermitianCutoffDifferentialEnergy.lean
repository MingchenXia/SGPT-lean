import SGPT.Foundations.Analysis.Pending.NaturalHermitianWeightedLocalGarding
import SGPT.Foundations.Analysis.Pending.NaturalChartCutoffCoefficientTests

/-! # Actual cutoff differential rules and internally bounded local energy -/

set_option autoImplicit false

noncomputable section

open Set Filter TopologicalSpace
open scoped Topology ContDiff BigOperators Distributions

namespace SGPT.Foundations.Analysis.Pending.NaturalHermitianCutoffDifferentialEnergy

open FirstPass FirstPass.MongeAmpere NaturalHermitianSmoothFormMetric
  NaturalHermitianFirstOrderCoefficients NaturalHermitianHodgePrincipalSymbol
  NaturalHermitianExteriorCliffordSymbol NaturalHermitianMetricCoefficients
  NaturalHermitianLocalGarding NaturalHermitianWeightedLocalGarding
  NaturalChartCutoffCoefficientTests

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

local instance formNormedAddCommGroup (q : ℕ) : NormedAddCommGroup (FormCoefficients n q) :=
  ContinuousAlternatingMap.instNormedAddCommGroup

local instance formNormedSpace (q : ℕ) : NormedSpace ℝ (FormCoefficients n q) :=
  ContinuousAlternatingMap.instNormedSpace

local instance jetNormedAddCommGroup (q : ℕ) :
    NormedAddCommGroup (ComplexModel n →L[ℝ] FormCoefficients n q) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance jetNormedSpace (q : ℕ) : NormedSpace ℝ (ComplexModel n →L[ℝ] FormCoefficients n q) :=
  ContinuousLinearMap.toNormedSpace

local instance jetMapNormedAddCommGroup (q r : ℕ) :
    NormedAddCommGroup ((ComplexModel n →L[ℝ] FormCoefficients n q) →L[ℝ] FormCoefficients n r) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance jetMapNormedSpace (q r : ℕ) :
    NormedSpace ℝ ((ComplexModel n →L[ℝ] FormCoefficients n q) →L[ℝ] FormCoefficients n r) :=
  ContinuousLinearMap.toNormedSpace

/-- The genuine variable codifferential product rule includes cancellation of the actual zero-order coefficient. -/
theorem localCodifferential_smul
    (w : SmoothRealForm n M 2) (hw : w.IsHermitian) (e : ComplexChart n M) (q : ℕ)
    (z : ComplexModel n) (hz : z ∈ e.val.target) (f : ComplexModel n → ℝ)
    (A : ComplexModel n → FormCoefficients n q)
    (hf : DifferentiableAt ℝ f z) (hA : DifferentiableAt ℝ A z) :
    localCodifferential w e q (fun y => f y • A y) z =
      f z • localCodifferential w e q A z +
        principalJetCLM w e q z ((fderiv ℝ f z).smulRight (A z)) := by
  rw [localCodifferential_eq_first_jet w hw e q z hz (fun y => f y • A y) (hf.smul hA),
    localCodifferential_eq_first_jet w hw e q z hz A hA, fderiv_fun_smul hf hA,
    map_add, map_smul, map_smul, smul_add]
  abel

/-- Entire ordinary exterior differential product rule in the original coefficient norm. -/
theorem extDeriv_smul (q : ℕ) (z : ComplexModel n) (f : ComplexModel n → ℝ)
    (A : ComplexModel n → FormCoefficients n q)
    (hf : DifferentiableAt ℝ f z) (hA : DifferentiableAt ℝ A z) :
    extDeriv (fun y => f y • A y) z = f z • extDeriv A z +
      ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (ComplexModel n) ℝ
        ((fderiv ℝ f z).smulRight (A z)) := by
  change ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (ComplexModel n) ℝ
    (fderiv ℝ (fun y => f y • A y) z) = _
  rw [fderiv_fun_smul hf hA, map_add, map_smul]
  rfl

/-- Positive-degree commutator is exactly the actual negative metric insertion. -/
theorem localCodifferentialSucc_smul
    (w : SmoothRealForm n M 2) (hw : w.IsHermitian) (e : ComplexChart n M)
    (p : ℕ) (hp : p + 1 ≤ 2 * n) (z : ComplexModel n) (hz : z ∈ e.val.target)
    (f : ComplexModel n → ℝ) (A : ComplexModel n → FormCoefficients n (p + 1))
    (hf : DifferentiableAt ℝ f z) (hA : DifferentiableAt ℝ A z) :
    localCodifferentialSucc w e p hp (fun y => f y • A y) z =
      f z • localCodifferentialSucc w e p hp A z -
        interiorSuccCLM p ((associatedMetricCLM (w.coeff e z)).inverse (fderiv ℝ f z)) (A z) := by
  rw [localCodifferentialSucc_eq_first_jet w hw e p hp z hz (fun y => f y • A y) (hf.smul hA),
    localCodifferentialSucc_eq_first_jet w hw e p hp z hz A hA, fderiv_fun_smul hf hA,
    map_add, map_smul, map_smul, smul_add,
    (principalJetSucc_covector_apply w hw e p hp z hz (fderiv ℝ f z) (A z)).2]
  abel

/-- Literal native cutoff codifferential product rule holds at every original model point. -/
theorem chartCutoffTest_localCodifferential
    (w : SmoothRealForm n M 2) (hw : w.IsHermitian) (e : ComplexChart n M) (q : ℕ)
    (K : Compacts (ComplexModel n)) (hK : (K : Set (ComplexModel n)) ⊆ e.val.target)
    (φ : 𝓓_{K}(ComplexModel n, ℝ)) (α : SmoothRealForm n M q) (x : ComplexModel n) :
    localCodifferential w e q (chartCutoffTest e K hK φ α) x =
      φ x • localCodifferential w e q (α.coeff e) x +
        principalJetCLM w e q x ((fderiv ℝ φ x).smulRight (α.coeff e x)) := by
  by_cases hx : x ∈ e.val.target
  · exact localCodifferential_smul w hw e q x hx φ (α.coeff e)
      (φ.contDiff.differentiable (by simp) x)
      (((α.smooth e).contDiffAt (e.val.open_target.mem_nhds hx)).differentiableAt (by simp))
  · have hxK : x ∉ K := fun h => hx (hK h)
    have hv : φ x = (0 : ℝ) := φ.zero_on_compl hxK
    have hd : fderiv ℝ φ x = 0 :=
      fderiv_of_notMem_tsupport ℝ (fun h => hxK (φ.tsupport_subset h))
    have hδ : localCodifferential w e q (chartCutoffTest e K hK φ α) x = 0 :=
      localCodifferential_eq_zero_of_notMem_tsupport w e q _ x
        (fun h => hxK ((chartCutoffTest e K hK φ α).tsupport_subset h))
    rw [hδ, hv, hd]
    simp only [zero_smul, ContinuousLinearMap.zero_smulRight, map_zero, add_zero]

/-- The original native cutoff value and both differentials genuinely vanish off its same compact support. -/
theorem chartCutoffTest_differentials_zero
    (w : SmoothRealForm n M 2) (e : ComplexChart n M) (q : ℕ)
    (K : Compacts (ComplexModel n)) (hK : (K : Set (ComplexModel n)) ⊆ e.val.target)
    (φ : 𝓓_{K}(ComplexModel n, ℝ)) (α : SmoothRealForm n M q)
    (x : ComplexModel n) (hx : x ∉ K) :
    chartCutoffTest e K hK φ α x = 0 ∧ extDeriv (chartCutoffTest e K hK φ α) x = 0 ∧
      localCodifferential w e q (chartCutoffTest e K hK φ α) x = 0 := by
  refine ⟨(chartCutoffTest e K hK φ α).zero_on_compl hx, ?_,
    localCodifferential_eq_zero_of_notMem_tsupport w e q _ x
      (fun h => hx ((chartCutoffTest e K hK φ α).tsupport_subset h))⟩
  change ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (ComplexModel n) ℝ
    (fderiv ℝ (chartCutoffTest e K hK φ α) x) = 0
  rw [chartCutoffTest_fderiv_eq_zero e K hK φ α x hx, map_zero]

/-- The actual entire native exterior differential reads its exact whole ordinary product jet. -/
theorem chartCutoffTest_extDeriv (e : ComplexChart n M) (q : ℕ)
    (K : Compacts (ComplexModel n)) (hK : (K : Set (ComplexModel n)) ⊆ e.val.target)
    (φ : 𝓓_{K}(ComplexModel n, ℝ)) (α : SmoothRealForm n M q) (x : ComplexModel n) :
    extDeriv (chartCutoffTest e K hK φ α) x = φ x • extDeriv (α.coeff e) x +
      ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (ComplexModel n) ℝ
        ((fderiv ℝ φ x).smulRight (α.coeff e x)) := by
  change ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (ComplexModel n) ℝ
    (fderiv ℝ (chartCutoffTest e K hK φ α) x) = _
  rw [chartCutoffTest_fderiv, map_add, map_smul]
  rfl

/-- Entire old-norm operator inequality for the actual scalar rank-one commutator. -/
theorem norm_smul_add_rank_one_le (q r : ℕ)
    (L : (ComplexModel n →L[ℝ] FormCoefficients n q) →L[ℝ] FormCoefficients n r)
    (f : ℝ) (ℓ : ComplexModel n →L[ℝ] ℝ)
    (η : FormCoefficients n q) (θ : FormCoefficients n r) :
    ‖f • θ + L (ℓ.smulRight η)‖ ≤ |f| * ‖θ‖ + ‖L‖ * ‖ℓ‖ * ‖η‖ := by
  calc
    _ ≤ ‖f • θ‖ + ‖L (ℓ.smulRight η)‖ := norm_add_le _ _
    _ ≤ ‖f • θ‖ + ‖L‖ * ‖ℓ.smulRight η‖ :=
      add_le_add (le_refl ‖f • θ‖) (L.le_opNorm (ℓ.smulRight η))
    _ = _ := by rw [norm_smul, Real.norm_eq_abs, ContinuousLinearMap.norm_smulRight_apply]; ring

/-- Real square absorption of the actual compact cutoff norm estimates. -/
theorem cutoff_energy_real_bound (F D P t a d δ v x y : ℝ)
    (hF : 0 ≤ F) (hD : 0 ≤ D) (hP : 0 ≤ P) (ht : 0 ≤ t)
    (ha : 0 ≤ a) (hd : 0 ≤ d) (hδ : 0 ≤ δ)
    (hv : 0 ≤ v) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hvb : v ≤ F * a) (hxb : x ≤ F * d + t * D * a)
    (hyb : y ≤ F * δ + P * D * a) :
    v ^ 2 + x ^ 2 + y ^ 2 ≤
      (1 + 3 * F ^ 2 + 2 * t ^ 2 * D ^ 2 + 2 * P ^ 2 * D ^ 2) * (a ^ 2 + d ^ 2 + δ ^ 2) := by
  let B := 1 + 3 * F ^ 2 + 2 * t ^ 2 * D ^ 2 + 2 * P ^ 2 * D ^ 2
  have hv2 : v ^ 2 ≤ F ^ 2 * a ^ 2 := by
    have h := (sq_le_sq₀ hv (mul_nonneg hF ha)).mpr hvb
    simpa only [mul_pow] using h
  have hx2 : x ^ 2 ≤ 2 * F ^ 2 * d ^ 2 + 2 * t ^ 2 * D ^ 2 * a ^ 2 := by
    have h := (sq_le_sq₀ hx (add_nonneg (mul_nonneg hF hd)
      (mul_nonneg (mul_nonneg ht hD) ha))).mpr hxb
    nlinarith only [h, sq_nonneg (F * d - t * D * a)]
  have hy2 : y ^ 2 ≤ 2 * F ^ 2 * δ ^ 2 + 2 * P ^ 2 * D ^ 2 * a ^ 2 := by
    have h := (sq_le_sq₀ hy (add_nonneg (mul_nonneg hF hδ)
      (mul_nonneg (mul_nonneg hP hD) ha))).mpr hyb
    nlinarith only [h, sq_nonneg (F * δ - P * D * a)]
  have hAcoeff : F ^ 2 + 2 * t ^ 2 * D ^ 2 + 2 * P ^ 2 * D ^ 2 ≤ B := by
    dsimp [B]
    nlinarith only [sq_nonneg F]
  have hOther : 2 * F ^ 2 ≤ B := by
    dsimp [B]
    nlinarith only [sq_nonneg F, mul_nonneg (sq_nonneg t) (sq_nonneg D),
      mul_nonneg (sq_nonneg P) (sq_nonneg D)]
  have hA := mul_le_mul_of_nonneg_right hAcoeff (sq_nonneg a)
  have hDs := mul_le_mul_of_nonneg_right hOther (sq_nonneg d)
  have hδs := mul_le_mul_of_nonneg_right hOther (sq_nonneg δ)
  change _ ≤ B * _
  nlinarith only [hv2, hx2, hy2, hA, hDs, hδs]

/-- Compactness of the actual cutoff and original principal field internally bounds every smooth-form cutoff energy. -/
theorem exists_compact_cutoff_norm_energy_bound
    (w : SmoothRealForm n M 2) (hw : w.IsHermitian) (e : ComplexChart n M) (q : ℕ)
    (K : Compacts (ComplexModel n)) (hK : (K : Set (ComplexModel n)) ⊆ e.val.target)
    (φ : 𝓓_{K}(ComplexModel n, ℝ)) :
    ∃ B > 0, ∀ (α : SmoothRealForm n M q), ∀ x ∈ K,
      ‖chartCutoffTest e K hK φ α x‖ ^ 2 + ‖extDeriv (chartCutoffTest e K hK φ α) x‖ ^ 2 +
        ‖localCodifferential w e q (chartCutoffTest e K hK φ α) x‖ ^ 2 ≤
      B * (‖α.coeff e x‖ ^ 2 + ‖extDeriv (α.coeff e) x‖ ^ 2 +
        ‖localCodifferential w e q (α.coeff e) x‖ ^ 2) := by
  obtain ⟨F₀, hF₀⟩ := K.isCompact.exists_bound_of_continuousOn φ.contDiff.continuous.continuousOn
  obtain ⟨D₀, hD₀⟩ := K.isCompact.exists_bound_of_continuousOn
    (φ.contDiff.continuous_fderiv (by simp)).continuousOn
  obtain ⟨P₀, hP₀⟩ := K.isCompact.exists_bound_of_continuousOn
    ((principalJet_smooth w hw e q).continuousOn.mono hK)
  let F := |F₀| + 1
  let D := |D₀| + 1
  let P := |P₀| + 1
  let T : (ComplexModel n →L[ℝ] FormCoefficients n q) →L[ℝ] FormCoefficients n (q + 1) :=
    ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (ComplexModel n) ℝ
  have hFpos : 0 < F := by dsimp [F]; positivity
  have hDpos : 0 < D := by dsimp [D]; positivity
  have hPpos : 0 < P := by dsimp [P]; positivity
  have hF (x : ComplexModel n) (hx : x ∈ K) : |φ x| ≤ F := by
    have h := hF₀ x hx
    rw [Real.norm_eq_abs] at h
    exact h.trans ((le_abs_self _).trans (by dsimp [F]; linarith))
  have hD (x : ComplexModel n) (hx : x ∈ K) : ‖fderiv ℝ φ x‖ ≤ D :=
    (hD₀ x hx).trans ((le_abs_self _).trans (by dsimp [D]; linarith))
  have hP (x : ComplexModel n) (hx : x ∈ K) : ‖principalJetCLM w e q x‖ ≤ P :=
    (hP₀ x hx).trans ((le_abs_self _).trans (by dsimp [P]; linarith))
  refine ⟨1 + 3 * F ^ 2 + 2 * ‖T‖ ^ 2 * D ^ 2 + 2 * P ^ 2 * D ^ 2, by positivity, ?_⟩
  intro α x hx
  have hv : ‖chartCutoffTest e K hK φ α x‖ ≤ F * ‖α.coeff e x‖ := by
    rw [chartCutoffTest_apply, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hF x hx) (norm_nonneg _)
  have hd : ‖extDeriv (chartCutoffTest e K hK φ α) x‖ ≤
      F * ‖extDeriv (α.coeff e) x‖ + ‖T‖ * D * ‖α.coeff e x‖ := by
    rw [chartCutoffTest_extDeriv]
    exact (norm_smul_add_rank_one_le q (q + 1) T (φ x) (fderiv ℝ φ x)
      (α.coeff e x) (extDeriv (α.coeff e) x)).trans
      (add_le_add (mul_le_mul_of_nonneg_right (hF x hx) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hD x hx) (norm_nonneg T))
          (norm_nonneg _)))
  have hδ : ‖localCodifferential w e q (chartCutoffTest e K hK φ α) x‖ ≤
      F * ‖localCodifferential w e q (α.coeff e) x‖ + P * D * ‖α.coeff e x‖ := by
    rw [chartCutoffTest_localCodifferential w hw]
    exact (norm_smul_add_rank_one_le q (q - 1) (principalJetCLM w e q x) (φ x)
      (fderiv ℝ φ x) (α.coeff e x) (localCodifferential w e q (α.coeff e) x)).trans
      (add_le_add (mul_le_mul_of_nonneg_right (hF x hx) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (mul_le_mul (hP x hx) (hD x hx)
          (norm_nonneg _) hPpos.le) (norm_nonneg _)))
  exact cutoff_energy_real_bound F D P ‖T‖ _ _ _ _ _ _
    hFpos.le hDpos.le hPpos.le (norm_nonneg T) (norm_nonneg _) (norm_nonneg _)
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hv hd hδ

/-- The literal sum of the same three original volume-weighted differential energies. -/
def weightedChartEnergy (w : SmoothRealForm n M 2) (e : ComplexChart n M) (q : ℕ)
    (A : ComplexModel n → FormCoefficients n q) (x : ComplexModel n) : ℝ :=
  weightedFormMetric w e q x (A x) (A x) +
    weightedFormMetric w e (q + 1) x (extDeriv A x) (extDeriv A x) +
    weightedFormMetric w e (q - 1) x
      (localCodifferential w e q A x) (localCodifferential w e q A x)

/-- Actual local geometry and each actual compact cutoff internally bound the full original weighted energy. -/
theorem exists_original_weighted_cutoff_energy_control
    (w : SmoothRealForm n M 2) (hw : w.IsHermitian) (e : ComplexChart n M) (q : ℕ)
    (z : ComplexModel n) (hz : z ∈ e.val.target) :
    ∃ r > 0, ∃ hball : Metric.ball z r ⊆ e.val.target,
      ∀ (K : Compacts (ComplexModel n)) (hK : (K : Set (ComplexModel n)) ⊆ Metric.ball z r)
        (φ : 𝓓_{K}(ComplexModel n, ℝ)), ∃ C > 0, ∀ (α : SmoothRealForm n M q),
        (∀ x ∈ K, weightedChartEnergy w e q (chartCutoffTest e K (hK.trans hball) φ α) x ≤
          C * weightedChartEnergy w e q (α.coeff e) x) ∧
        ∀ x ∉ K, weightedChartEnergy w e q (chartCutoffTest e K (hK.trans hball) φ α) x = 0 := by
  obtain ⟨r, hr, m, hm, M₀, hM₀, hball, hcomparison⟩ :=
    exists_original_weighted_metric_comparison w hw e z hz q
  refine ⟨r, hr, hball, ?_⟩
  intro K hK φ
  obtain ⟨B, hB, hbound⟩ := exists_compact_cutoff_norm_energy_bound w hw e q K (hK.trans hball) φ
  refine ⟨M₀ * B / m, div_pos (mul_pos hM₀ hB) hm, ?_⟩
  intro α
  refine ⟨?_, ?_⟩
  · intro x hx
    let T := chartCutoffTest e K (hK.trans hball) φ α
    have hU := add_le_add
      (add_le_add (hcomparison x (hK hx) q (Or.inl rfl) (T x)).2
        (hcomparison x (hK hx) (q + 1) (Or.inr (Or.inl rfl)) (extDeriv T x)).2)
      (hcomparison x (hK hx) (q - 1) (Or.inr (Or.inr rfl)) (localCodifferential w e q T x)).2
    have hUpper : weightedChartEnergy w e q T x ≤
        M₀ * (‖T x‖ ^ 2 + ‖extDeriv T x‖ ^ 2 + ‖localCodifferential w e q T x‖ ^ 2) := by
      simpa only [weightedChartEnergy, mul_add] using hU
    have hL := add_le_add
      (add_le_add (hcomparison x (hK hx) q (Or.inl rfl) (α.coeff e x)).1
        (hcomparison x (hK hx) (q + 1) (Or.inr (Or.inl rfl)) (extDeriv (α.coeff e) x)).1)
      (hcomparison x (hK hx) (q - 1) (Or.inr (Or.inr rfl))
        (localCodifferential w e q (α.coeff e) x)).1
    have hLower : m * (‖α.coeff e x‖ ^ 2 + ‖extDeriv (α.coeff e) x‖ ^ 2 +
        ‖localCodifferential w e q (α.coeff e) x‖ ^ 2) ≤
        weightedChartEnergy w e q (α.coeff e) x := by
      simpa only [weightedChartEnergy, mul_add] using hL
    have hdiv := (le_div_iff₀ hm).mpr (by simpa only [mul_comm] using hLower)
    calc
      _ ≤ M₀ * (‖T x‖ ^ 2 + ‖extDeriv T x‖ ^ 2 + ‖localCodifferential w e q T x‖ ^ 2) := hUpper
      _ ≤ M₀ * (B * (‖α.coeff e x‖ ^ 2 + ‖extDeriv (α.coeff e) x‖ ^ 2 +
          ‖localCodifferential w e q (α.coeff e) x‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left (hbound α x hx) hM₀.le
      _ ≤ M₀ * (B * (weightedChartEnergy w e q (α.coeff e) x / m)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdiv hB.le) hM₀.le
      _ = _ := by ring
  · intro x hx
    have hzero := chartCutoffTest_differentials_zero w e q K (hK.trans hball) φ α x hx
    rw [weightedChartEnergy, hzero.1, hzero.2.1, hzero.2.2]
    simp only [map_zero, add_zero]

end SGPT.Foundations.Analysis.Pending.NaturalHermitianCutoffDifferentialEnergy
