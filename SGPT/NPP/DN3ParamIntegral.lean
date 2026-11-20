import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import SGPT.Foundations.Analysis.LeviForm

/-!
# Second derivatives of parametric integrals with uniform compact support

Lane DN3 (`thm:DNT23_C11bar`; FPT `lem:chern-joint-smoothing`, Step 4: "the integrand is smooth
with support in `{|s| ≤ 2}`, so we may differentiate under the integral sign").

For a family `F : P → E → G` that is `C¹` (resp. `C²`) jointly on `U × E` (`U ⊆ P` open, `P`
finite dimensional) and vanishes for `‖s‖ > R` when the parameter lies in `U`:

* `hasFDerivAt_integral_of_contDiffOn` : `D_p ∫ F(p, s) dμ(s) = ∫ D_p F(p, s) dμ(s)`;
* `fderiv_fderiv_integral_of_contDiffOn` : the same for the second derivative;
* `realHessian_integral_of_contDiffOn`, `leviForm_integral_of_contDiffOn` : the real Hessian and
  the Levi form of `p ↦ ∫ F(p, s) dμ(s)` are the integrals of those of `F(·, s)`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace SGPT.NPP.DN3

open SGPT.Foundations.Analysis

section Param

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsFiniteMeasureOnCompacts μ]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

omit [FiniteDimensional ℝ P] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace G] in
/-- The partial derivative in the parameter vanishes outside the uniform support. -/
theorem fderiv_param_eq_zero {F : P → E → G} {U : Set P} (hU : IsOpen U) {R : ℝ}
    (hsupp : ∀ p ∈ U, ∀ s, R < ‖s‖ → F p s = 0) {p : P} (hp : p ∈ U) {s : E} (hs : R < ‖s‖) :
    fderiv ℝ (fun q => F q s) p = 0 := by
  have hev : (fun q => F q s) =ᶠ[𝓝 p] fun _ => (0 : G) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact hsupp q hq s hs
  rw [hev.fderiv_eq]
  exact fderiv_const_apply 0

omit [CompleteSpace G] in
/-- **Differentiation under the integral sign** for a jointly `C¹` family with uniform compact
support. -/
theorem hasFDerivAt_integral_of_contDiffOn {F : P → E → G} {U : Set P} (hU : IsOpen U)
    (hF : ContDiffOn ℝ 1 (fun q : P × E => F q.1 q.2) (U ×ˢ univ)) {R : ℝ}
    (hsupp : ∀ p ∈ U, ∀ s, R < ‖s‖ → F p s = 0) {p₀ : P} (hp₀ : p₀ ∈ U) :
    HasFDerivAt (fun p => ∫ s, F p s ∂μ) (∫ s, fderiv ℝ (fun p => F p s) p₀ ∂μ) p₀ := by
  have : ProperSpace P := FiniteDimensional.proper ℝ P
  have : ProperSpace E := FiniteDimensional.proper ℝ E
  have hW : IsOpen (U ×ˢ (univ : Set E)) := hU.prod isOpen_univ
  -- the partial derivative
  set F' : P → E → P →L[ℝ] G := fun p s =>
    (fderiv ℝ (fun q : P × E => F q.1 q.2) (p, s)).comp (ContinuousLinearMap.inl ℝ P E) with hF'
  have hpart : ∀ p ∈ U, ∀ s, HasFDerivAt (fun q => F q s) (F' p s) p := by
    intro p hp s
    have h1 : HasFDerivAt (fun q : P × E => F q.1 q.2)
        (fderiv ℝ (fun q : P × E => F q.1 q.2) (p, s)) (p, s) :=
      ((hF.differentiableOn one_ne_zero) (p, s) ⟨hp, mem_univ _⟩).differentiableAt
        (hW.mem_nhds ⟨hp, mem_univ _⟩) |>.hasFDerivAt
    exact h1.comp p (hasFDerivAt_prodMk_left (𝕜 := ℝ) p s)
  have hF'c : ContinuousOn (fun q : P × E => F' q.1 q.2) (U ×ˢ univ) := by
    have h := hF.continuousOn_fderiv_of_isOpen hW le_rfl
    exact h.clm_comp continuousOn_const
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU p₀ hp₀
  have hε2 : closedBall p₀ (ε / 2) ⊆ U :=
    (closedBall_subset_ball (half_lt_self hε)).trans hεU
  have hK : IsCompact (closedBall p₀ (ε / 2) ×ˢ closedBall (0 : E) R) :=
    (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
    (hF'c.mono (prod_mono hε2 (subset_univ _)))
  have hFc : ∀ p ∈ U, Continuous fun s => F p s := by
    intro p hp
    have h := hF.continuousOn
    exact continuousOn_univ.mp (h.comp (Continuous.prodMk continuous_const continuous_id).continuousOn
      fun s _ => ⟨hp, mem_univ s⟩)
  have hFs : ∀ p ∈ U, HasCompactSupport fun s => F p s := by
    intro p hp
    refine HasCompactSupport.intro (isCompact_closedBall (0 : E) R) fun s hs => ?_
    simp only [mem_closedBall, dist_zero_right, not_le] at hs
    exact hsupp p hp s hs
  have hF'0c : Continuous fun s => F' p₀ s :=
    continuousOn_univ.mp (hF'c.comp (Continuous.prodMk continuous_const continuous_id).continuousOn
      fun s _ => ⟨hp₀, mem_univ s⟩)
  have hball : ball p₀ (ε / 2) ∈ 𝓝 p₀ := ball_mem_nhds p₀ (half_pos hε)
  have hmain := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := μ) (F := F) (F' := F')
    (bound := (closedBall (0 : E) R).indicator fun _ => M) hball
    (by filter_upwards [hU.mem_nhds hp₀] with p hp; exact (hFc p hp).aestronglyMeasurable)
    ((hFc p₀ hp₀).integrable_of_hasCompactSupport (hFs p₀ hp₀))
    hF'0c.aestronglyMeasurable ?_ ?_ ?_
  · have heq : ∫ s, F' p₀ s ∂μ = ∫ s, fderiv ℝ (fun p => F p s) p₀ ∂μ := by
      congr 1; funext s; exact ((hpart p₀ hp₀ s).fderiv).symm
    rwa [heq] at hmain
  · refine Eventually.of_forall fun s p hp => ?_
    have hpU : p ∈ U := hε2 (ball_subset_closedBall hp)
    by_cases hs : s ∈ closedBall (0 : E) R
    · rw [indicator_of_mem hs]
      exact hM (p, s) ⟨ball_subset_closedBall hp, hs⟩
    · rw [indicator_of_notMem hs]
      simp only [mem_closedBall, dist_zero_right, not_le] at hs
      rw [← (hpart p hpU s).fderiv, fderiv_param_eq_zero hU hsupp hpU hs, norm_zero]
  · exact (integrable_indicator_iff measurableSet_closedBall).mpr
      (integrableOn_const (isCompact_closedBall (0 : E) R).measure_lt_top.ne)
  · exact Eventually.of_forall fun s p hp => hpart p (hε2 (ball_subset_closedBall hp)) s

omit [CompleteSpace G] in
omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The parameter derivative of a jointly `C^{m+1}` family is a jointly `C^m` family. -/
theorem contDiffOn_fderiv_param {F : P → E → G} {U : Set P} (hU : IsOpen U) {m : ℕ}
    (hF : ContDiffOn ℝ (m + 1) (fun q : P × E => F q.1 q.2) (U ×ˢ univ)) :
    ContDiffOn ℝ m (fun q : P × E => fderiv ℝ (fun p => F p q.2) q.1) (U ×ˢ univ) := by
  have hW : IsOpen (U ×ˢ (univ : Set E)) := hU.prod isOpen_univ
  have h1 : ContDiffOn ℝ m (fun q : P × E =>
      (fderiv ℝ (fun q : P × E => F q.1 q.2) q).comp (ContinuousLinearMap.inl ℝ P E))
      (U ×ˢ univ) :=
    (hF.fderiv_of_isOpen hW le_rfl).clm_comp contDiffOn_const
  refine h1.congr fun q hq => ?_
  have h2 : HasFDerivAt (fun q : P × E => F q.1 q.2)
      (fderiv ℝ (fun q : P × E => F q.1 q.2) q) q :=
    ((hF.differentiableOn (by simp)) q hq).differentiableAt (hW.mem_nhds hq) |>.hasFDerivAt
  exact (h2.comp q.1 (hasFDerivAt_prodMk_left (𝕜 := ℝ) q.1 q.2)).fderiv

omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [CompleteSpace G] in
/-- The second parameter derivative of a jointly `C²` family is jointly continuous. -/
theorem continuousOn_fderiv2_param {F : P → E → G} {U : Set P} (hU : IsOpen U)
    (hF : ContDiffOn ℝ 2 (fun q : P × E => F q.1 q.2) (U ×ˢ univ)) :
    ContinuousOn (fun q : P × E => fderiv ℝ (fun p => fderiv ℝ (fun p => F p q.2) p) q.1)
      (U ×ˢ univ) := by
  have h1 : ContDiffOn ℝ 1 (fun q : P × E => fderiv ℝ (fun p => F p q.2) q.1) (U ×ˢ univ) :=
    (contDiffOn_fderiv_param (m := 1) hU (hF.of_le (by norm_num))).of_le (by norm_num)
  have h2 := contDiffOn_fderiv_param (F := fun p s => fderiv ℝ (fun p => F p s) p) (m := 0) hU
    (h1.of_le (by norm_num))
  exact h2.continuousOn

omit [CompleteSpace G] in
/-- **Second derivatives under the integral sign** for a jointly `C²` family with uniform
compact support. -/
theorem fderiv_fderiv_integral_of_contDiffOn {F : P → E → G} {U : Set P} (hU : IsOpen U)
    (hF : ContDiffOn ℝ 2 (fun q : P × E => F q.1 q.2) (U ×ˢ univ)) {R : ℝ}
    (hsupp : ∀ p ∈ U, ∀ s, R < ‖s‖ → F p s = 0) {p₀ : P} (hp₀ : p₀ ∈ U) :
    fderiv ℝ (fderiv ℝ (fun p => ∫ s, F p s ∂μ)) p₀ =
      ∫ s, fderiv ℝ (fderiv ℝ (fun p => F p s)) p₀ ∂μ := by
  have hF1 : ContDiffOn ℝ 1 (fun q : P × E => F q.1 q.2) (U ×ˢ univ) :=
    hF.of_le (by norm_num)
  have hev : fderiv ℝ (fun p => ∫ s, F p s ∂μ) =ᶠ[𝓝 p₀]
      fun p => ∫ s, fderiv ℝ (fun p => F p s) p ∂μ := by
    filter_upwards [hU.mem_nhds hp₀] with p hp
    exact (hasFDerivAt_integral_of_contDiffOn hU hF1 hsupp hp).fderiv
  have hsupp' : ∀ p ∈ U, ∀ s, R < ‖s‖ → fderiv ℝ (fun p => F p s) p = 0 :=
    fun p hp s hs => fderiv_param_eq_zero hU hsupp hp hs
  have h2 := hasFDerivAt_integral_of_contDiffOn (μ := μ) hU
    ((contDiffOn_fderiv_param (m := 1) hU (hF.of_le (by norm_num))).of_le (by norm_num))
    hsupp' hp₀
  rw [hev.fderiv_eq, h2.fderiv]

omit [NormedSpace ℝ P] [FiniteDimensional ℝ P] [NormedSpace ℝ G] [CompleteSpace G] in
/-- A jointly continuous family with uniform compact support is integrable in `s`. -/
theorem integrable_of_continuousOn_param {F : P → E → G} {U : Set P}
    (hF : ContinuousOn (fun q : P × E => F q.1 q.2) (U ×ˢ univ)) {R : ℝ}
    (hsupp : ∀ p ∈ U, ∀ s, R < ‖s‖ → F p s = 0) {p : P} (hp : p ∈ U) :
    Integrable (fun s => F p s) μ := by
  have : ProperSpace E := FiniteDimensional.proper ℝ E
  have hc : Continuous fun s => F p s :=
    continuousOn_univ.mp (hF.comp (Continuous.prodMk continuous_const continuous_id).continuousOn
      fun s _ => ⟨hp, mem_univ s⟩)
  refine hc.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (isCompact_closedBall (0 : E) R) fun s hs => ?_
  simp only [mem_closedBall, dist_zero_right, not_le] at hs
  exact hsupp p hp s hs

omit [NormedSpace ℝ G] [CompleteSpace G] in
/-- **The real Hessian of a parametric integral** is the integral of the real Hessians. -/
theorem realHessian_integral_of_contDiffOn {F : P → E → ℝ} {U : Set P} (hU : IsOpen U)
    (hF : ContDiffOn ℝ 2 (fun q : P × E => F q.1 q.2) (U ×ˢ univ)) {R : ℝ}
    (hsupp : ∀ p ∈ U, ∀ s, R < ‖s‖ → F p s = 0) {p₀ : P} (hp₀ : p₀ ∈ U) (v w : P) :
    realHessian (fun p => ∫ s, F p s ∂μ) p₀ v w =
      ∫ s, realHessian (fun p => F p s) p₀ v w ∂μ := by
  have hW : IsOpen (U ×ˢ (univ : Set E)) := hU.prod isOpen_univ
  have hsupp' : ∀ p ∈ U, ∀ s, R < ‖s‖ → fderiv ℝ (fun p => F p s) p = 0 :=
    fun p hp s hs => fderiv_param_eq_zero hU hsupp hp hs
  have hsupp'' : ∀ p ∈ U, ∀ s, R < ‖s‖ →
      fderiv ℝ (fun p => fderiv ℝ (fun p => F p s) p) p = 0 :=
    fun p hp s hs => fderiv_param_eq_zero hU hsupp' hp hs
  have hc2 : ContinuousOn
      (fun q : P × E => fderiv ℝ (fun p => fderiv ℝ (fun p => F p q.2) p) q.1) (U ×ˢ univ) :=
    continuousOn_fderiv2_param hU hF
  -- (stated through the lemma: the instance search does not find
  -- `ContinuousENorm (P →L[ℝ] P →L[ℝ] ℝ)` unaided)
  have hint := integrable_of_continuousOn_param (μ := μ) (G := P →L[ℝ] P →L[ℝ] ℝ)
    (F := fun p s => fderiv ℝ (fun p => fderiv ℝ (fun p => F p s) p) p) hc2 hsupp'' hp₀
  rw [realHessian_eq_fderiv, fderiv_fderiv_integral_of_contDiffOn hU hF hsupp hp₀,
    ContinuousLinearMap.integral_apply hint, ContinuousLinearMap.integral_apply
      (hint.apply_continuousLinearMap v)]
  simp only [realHessian_eq_fderiv]

omit [NormedSpace ℝ G] [CompleteSpace G] in
/-- **The Levi form of a parametric integral** is the integral of the Levi forms. -/
theorem leviForm_integral_of_contDiffOn [NormedSpace ℂ P] {F : P → E → ℝ} {U : Set P}
    (hU : IsOpen U) (hF : ContDiffOn ℝ 2 (fun q : P × E => F q.1 q.2) (U ×ˢ univ)) {R : ℝ}
    (hsupp : ∀ p ∈ U, ∀ s, R < ‖s‖ → F p s = 0) {p₀ : P} (hp₀ : p₀ ∈ U) (v : P) :
    leviForm (fun p => ∫ s, F p s ∂μ) p₀ v = ∫ s, leviForm (fun p => F p s) p₀ v ∂μ := by
  have hW : IsOpen (U ×ˢ (univ : Set E)) := hU.prod isOpen_univ
  have hc2 : ContinuousOn
      (fun q : P × E => fderiv ℝ (fun p => fderiv ℝ (fun p => F p q.2) p) q.1) (U ×ˢ univ) :=
    continuousOn_fderiv2_param hU hF
  have hsupp' : ∀ p ∈ U, ∀ s, R < ‖s‖ → fderiv ℝ (fun p => F p s) p = 0 :=
    fun p hp s hs => fderiv_param_eq_zero hU hsupp hp hs
  have hsupp'' : ∀ p ∈ U, ∀ s, R < ‖s‖ →
      fderiv ℝ (fun p => fderiv ℝ (fun p => F p s) p) p = 0 :=
    fun p hp s hs => fderiv_param_eq_zero hU hsupp' hp hs
  -- (stated through the lemma: the instance search does not find
  -- `ContinuousENorm (P →L[ℝ] P →L[ℝ] ℝ)` unaided)
  have hint := integrable_of_continuousOn_param (μ := μ) (G := P →L[ℝ] P →L[ℝ] ℝ)
    (F := fun p s => fderiv ℝ (fun p => fderiv ℝ (fun p => F p s) p) p) hc2 hsupp'' hp₀
  have hiv : ∀ u w : P, Integrable (fun s => realHessian (fun p => F p s) p₀ u w) μ := by
    intro u w
    simp only [realHessian_eq_fderiv]
    exact (hint.apply_continuousLinearMap u).apply_continuousLinearMap w
  simp only [leviForm]
  rw [realHessian_integral_of_contDiffOn hU hF hsupp hp₀,
    realHessian_integral_of_contDiffOn hU hF hsupp hp₀, ← integral_add (hiv v v)
      (hiv _ _), ← integral_div]

end Param

end SGPT.NPP.DN3
