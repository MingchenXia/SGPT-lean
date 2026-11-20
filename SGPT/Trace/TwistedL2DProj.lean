import SGPT.Trace.TwistedL2DHilbert

/-!
# Projection onto the orthogonal complement of the special families

Blueprint `claude-tl2-dens.tex` (`claude-tl2-dens:special`, `claude-tl2-dens:projection`).
For a twisted datum `T` on `ℂⁿ`:

* `specV e ψ j k = e^{p_e} (∂_k ψ ∂/∂z_j - ∂_j ψ ∂/∂z_k)` (`ψ` a test function in the frame
  domain): the special families `S*(ψ dz̄_j ∧ dz̄_k)` (`σ` cancels in the `H₂`-pairing,
  `inner_specV`).  Their `T*`-pairing with test sections (`ylam`, `inner_specV_ylam`) and their
  data pairing (`ydF`, `inner_specV_yd`) vanish, because `∂̄∂̄ = 0` (`integral_antisym_eq_zero`).
* `exists_proj`: for a test family `τ` there is `v ∈ H₂` orthogonal to all special families,
  with the same pairings as `τ` against every vector orthogonal to the special families.
* `weak_S`, `weak_T`, `data_v`: the resulting weak equations for the frame coefficients
  `uc e · Weps v` of `v`: `∂̄(σ^♭ v) = 0`, `T* v = T* τ` and `⟨v, ∂̄G⟩ = ⟨τ, ∂̄G⟩`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter MeasureTheory Matrix Bundle
open scoped Topology ContDiff ComplexConjugate ComplexOrder Manifold InnerProductSpace ENNReal NNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.Pending.CauchyGreen SGPT.Foundations.Analysis.Pending.Hormander
  SGPT.Foundations.Analysis.Pending.OTChen
open SGPT.Bergman.TensorDictionaryDraft
open HermitianHolomorphicLineBundle

variable {n : ℕ}

/-! ### Generalities -/

theorem continuous_of_continuousOn_of_eq_zero' {V : Type*} [TopologicalSpace V] [Zero V]
    {f : ComplexModel n → V} {D K : Set (ComplexModel n)} (hD : IsOpen D) (hf : ContinuousOn f D)
    (hK : IsClosed K) (hKD : K ⊆ D) (h0 : ∀ z ∉ K, f z = 0) : Continuous f := by
  refine continuous_iff_continuousAt.mpr fun z => ?_
  by_cases hz : z ∈ D
  · exact hf.continuousAt (hD.mem_nhds hz)
  · have hzK : z ∉ K := fun h => hz (hKD h)
    have hev : f =ᶠ[𝓝 z] fun _ => 0 := by
      filter_upwards [hK.isOpen_compl.mem_nhds hzK] with y hy
      exact h0 y hy
    exact continuousAt_const.congr hev.symm

theorem dDir_eq_zero_of_notMem {f : ComplexModel n → ℂ} {z : ComplexModel n}
    (hz : z ∉ tsupport f) (v : ComplexModel n) : dDir v f z = 0 :=
  dDir_eq_zero_of_eventuallyEq_zero (notMem_tsupport_iff_eventuallyEq.mp hz)

theorem dbarDir_eq_zero_of_notMem {f : ComplexModel n → ℂ} {z : ComplexModel n}
    (hz : z ∉ tsupport f) (v : ComplexModel n) : dbarDir v f z = 0 :=
  dbarDir_eq_zero_of_eventuallyEq_zero (notMem_tsupport_iff_eventuallyEq.mp hz)

theorem continuousOn_mv {S : Set (ComplexModel n)} {M : ComplexModel n → Matrix (Fin n) (Fin n) ℂ}
    {y : ComplexModel n → ComplexModel n} (hM : ∀ i j, ContinuousOn (fun z => M z i j) S)
    (hy : ContinuousOn y S) : ContinuousOn (fun z => mv (M z) (y z)) S := by
  have hfun : (fun z => mv (M z) (y z)) = fun z => ∑ i, ∑ j,
      (M z i j * y z j) • (EuclideanSpace.single i (1 : ℂ) : ComplexModel n) := by
    funext z
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hfun]
  refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ?_
  have hyj : ContinuousOn (fun z => y z j) S :=
    ((EuclideanSpace.proj j : ComplexModel n →L[ℂ] ℂ).continuous).comp_continuousOn hy
  exact ((hM i j).mul hyj).smul continuousOn_const

/-- **`∂̄∂̄ = 0` against test functions**: for `g` smooth on an open `D` and a test function `ψ`
on `D`, `∫ (∂_{j̄} g conj(∂_k ψ) - ∂_{k̄} g conj(∂_j ψ)) = 0`. -/
theorem integral_antisym_eq_zero {D : Set (ComplexModel n)} (hD : IsOpen D)
    {g : ComplexModel n → ℂ} (hg : ContDiffOn ℝ ∞ g D) {ψ : ComplexModel n → ℂ}
    (hψ : IsTestFunctionOn D ψ) (j k : Fin n) :
    ∫ z, (dbarDir (coordVec j) g z * conj (dDir (coordVec k) ψ z) -
      dbarDir (coordVec k) g z * conj (dDir (coordVec j) ψ z)) = 0 := by
  set ψc : ComplexModel n → ℂ := fun z => conj (ψ z) with hψc
  have hψc' : IsTestFunctionOn D ψc := hψ.conj
  have hconj : ∀ (v : ComplexModel n) (z : ComplexModel n),
      conj (dDir v ψ z) = dbarDir v ψc z := fun v z =>
    (dbarDir_conj ((hψ.1.differentiable (by simp)) z)).symm
  have hg1 : ContDiffOn ℝ 1 g D := hg.of_le (by simp)
  have ht : ∀ v, IsTestFunctionOn D (dbarDir v ψc) := fun v => isTestFunctionOn_dbarDir hψc' v
  -- integrability
  have hint : ∀ a b : Fin n, Integrable (fun z => dbarDir (coordVec a) g z *
      dbarDir (coordVec b) ψc z) := by
    intro a b
    have hc : ContinuousOn (dbarDir (coordVec a) g) D :=
      (contDiffOn_dbarDir hD hg _).continuousOn
    exact (continuous_mul_of_continuousOn hD hc (ht _).1.continuous (ht _).2.2).integrable_of_hasCompactSupport
      (ht _).2.1.mul_left
  simp only [hconj]
  rw [integral_sub (hint j k) (hint k j)]
  have e1 := integral_mul_dbarDir_eq_neg_of_contDiffOn (μ := volume) hD hg1
    ((ht (coordVec k)).1.of_le (by simp)) (ht (coordVec k)).2.1 (ht (coordVec k)).2.2 (coordVec j)
  have e2 := integral_mul_dbarDir_eq_neg_of_contDiffOn (μ := volume) hD hg1
    ((ht (coordVec j)).1.of_le (by simp)) (ht (coordVec j)).2.1 (ht (coordVec j)).2.2 (coordVec k)
  have hcomm : ∀ z, dbarDir (coordVec j) (dbarDir (coordVec k) ψc) z =
      dbarDir (coordVec k) (dbarDir (coordVec j) ψc) z := fun z =>
    dbarDir_dbarDir_comm (hψc'.1.contDiffAt.of_le TwistedDatum.two_le_infty)
  have h3 : (∫ z, g z * dbarDir (coordVec j) (dbarDir (coordVec k) ψc) z) =
      ∫ z, g z * dbarDir (coordVec k) (dbarDir (coordVec j) ψc) z := by simp only [hcomm]
  have h4 := neg_inj.mp (e1.symm.trans (h3.trans e2))
  rw [h4, sub_self]

/-- Integration by parts for `ϑ`: for `W` and `p` smooth on an open `D` and a test function `u`
on `D`, `∫ e^{-p} ∑_l ∂_{l̄} u conj(W_l) = ∫ u conj(ϑ_p W) e^{-p}`. -/
theorem integral_dbar_conj_eq {D : Set (ComplexModel n)} (hD : IsOpen D) {p : ComplexModel n → ℝ}
    (hp : ContDiffOn ℝ ∞ p D) {W : ComplexModel n → ComplexModel n} (hW : ContDiffOn ℝ ∞ W D)
    {u : ComplexModel n → ℂ} (hu : IsTestFunctionOn D u) :
    ∫ z, cweight p z * ∑ l, dbarDir (coordVec l) u z * conj (W z l) =
      ∫ z, u z * conj (chartTheta p W z) * cweight p z := by
  set a : Fin n → ComplexModel n → ℂ := fun l z => conj (W z l) * cweight p z with ha
  have hcw : ∀ z, conj (cweight p z) = cweight p z := fun z => by rw [cweight, Complex.conj_ofReal]
  have haD : ∀ l, ContDiffOn ℝ ∞ (a l) D := fun l =>
    ((Complex.conjCLE.contDiff.comp_contDiffOn (contDiffOn_coord hW l)).mul
      (Complex.ofRealCLM.contDiff.comp_contDiffOn (Real.contDiff_exp.comp_contDiffOn hp.neg)))
  have hut : ∀ l, IsTestFunctionOn D (dbarDir (coordVec l) u) := fun l =>
    isTestFunctionOn_dbarDir hu _
  have hint1 : ∀ l, Integrable (fun z => a l z * dbarDir (coordVec l) u z) := fun l =>
    (continuous_mul_of_continuousOn hD (haD l).continuousOn (hut l).1.continuous
      (hut l).2.2).integrable_of_hasCompactSupport (hut l).2.1.mul_left
  have hda : ∀ l, ∀ z ∈ D, dbarDir (coordVec l) (a l) z =
      conj (deltaDir (coordVec l) p (fun y => W y l) z) * cweight p z := by
    intro l z hz
    have hpz : DifferentiableAt ℝ p z :=
      ((hp.contDiffAt (hD.mem_nhds hz)).differentiableAt (by simp))
    have hWz : DifferentiableAt ℝ (fun y => W y l) z :=
      ((contDiffOn_coord hW l).contDiffAt (hD.mem_nhds hz)).differentiableAt (by simp)
    have hfun : a l = fun y => conj (W y l * cweight p y) := by
      funext y; simp only [ha, map_mul, hcw]
    have hd : DifferentiableAt ℝ (fun y => W y l * cweight p y) z :=
      hWz.mul (differentiableAt_cweight hpz)
    rw [hfun, dbarDir_conj hd, ← deltaDir_mul_cweight hpz hWz, map_mul, hcw]
  have hint2 : ∀ l, Integrable (fun z => dbarDir (coordVec l) (a l) z * u z) := fun l =>
    (continuous_mul_of_continuousOn hD (contDiffOn_dbarDir hD (haD l) _).continuousOn
      hu.1.continuous hu.2.2).integrable_of_hasCompactSupport hu.2.1.mul_left
  have hlhs : (fun z => cweight p z * ∑ l, dbarDir (coordVec l) u z * conj (W z l)) =
      fun z => ∑ l, a l z * dbarDir (coordVec l) u z := by
    funext z; simp only [ha, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => by ring
  rw [hlhs, integral_finsetSum _ fun l _ => hint1 l]
  have hstep : ∀ l, ∫ z, a l z * dbarDir (coordVec l) u z =
      -∫ z, u z * conj (deltaDir (coordVec l) p (fun y => W y l) z) * cweight p z := by
    intro l
    rw [integral_mul_dbarDir_eq_neg_of_contDiffOn (μ := volume) hD ((haD l).of_le (by simp))
      (hu.1.of_le (by simp)) hu.2.1 hu.2.2]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    by_cases hz : z ∈ D
    · simp only; rw [hda l z hz]; ring
    · have hzu : u z = 0 := image_eq_zero_of_notMem_tsupport fun h => hz (hu.2.2 h)
      simp [hzu]
  have hint3 : ∀ l, Integrable (fun z =>
      u z * conj (deltaDir (coordVec l) p (fun y => W y l) z) * cweight p z) := by
    intro l
    refine (hint2 l).congr (Eventually.of_forall fun z => ?_)
    by_cases hz : z ∈ D
    · simp only; rw [hda l z hz]; ring
    · have hzu : u z = 0 := image_eq_zero_of_notMem_tsupport fun h => hz (hu.2.2 h)
      simp [hzu]
  simp only [hstep]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ fun l _ => hint3 l, ← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [chartTheta, map_neg, map_sum, Finset.mul_sum, Finset.sum_mul, mul_neg, neg_mul]

theorem inner_toLp_toLp {f g : ComplexModel n → ComplexModel n} (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) : ⟪hf.toLp f, hg.toLp g⟫_ℂ = ∫ z, ⟪f z, g z⟫_ℂ := by
  rw [inner_toLp_left]
  refine integral_congr_ae ?_
  filter_upwards [hg.coeFn_toLp] with z hz
  rw [hz]

/-- **Projection onto the orthogonal complement of a family of vectors** in a Hilbert space. -/
theorem exists_proj_orth {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {ι : Type*} (g : ι → E) (x : E) :
    ∃ v : E, (∀ q, ⟪g q, v⟫_ℂ = 0) ∧ ∀ y : E, (∀ q, ⟪g q, y⟫_ℂ = 0) → ⟪v, y⟫_ℂ = ⟪x, y⟫_ℂ := by
  set K := (Submodule.span ℂ (Set.range g)).topologicalClosure
  have : CompleteSpace K := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  refine ⟨x - K.starProjection x, fun q => ?_, fun y hy => ?_⟩
  · have hq : g q ∈ K := Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨q, rfl⟩)
    exact Submodule.inner_right_of_mem_orthogonal hq (Submodule.sub_starProjection_mem_orthogonal x)
  · have hspan : Submodule.span ℂ (Set.range g) ≤ (ℂ ∙ y)ᗮ := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨q, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right]
      exact inner_eq_zero_symm.mp (hy q)
    have hK : K ≤ (ℂ ∙ y)ᗮ :=
      Submodule.topologicalClosure_minimal _ hspan (Submodule.isClosed_orthogonal _)
    have hP : ⟪K.starProjection x, y⟫_ℂ = 0 := by
      have := hK (K.starProjection_apply_mem x)
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at this
      exact inner_eq_zero_symm.mp this
    rw [inner_sub_left, hP, sub_zero]

namespace TwistedDatum

variable {T : TwistedDatum n (ComplexModel n)} {ρ : ComplexModel n → ℝ}

theorem sT_conjTranspose {z : ComplexModel n} (hz : z ∈ T.U) :
    (sT T.omega T.r z)ᴴ = sT T.omega T.r z :=
  (posDef_sT T.isOpen_U T.kahler hz).isHermitian

theorem sT_mul_sigmaInv {z : ComplexModel n} (hz : z ∈ T.U) :
    sT T.omega T.r z * sigmaInv T.omega T.r z = 1 :=
  mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (posDef_sT T.isOpen_U T.kahler hz).det_pos.ne')

theorem inner_eq_sum (x y : ComplexModel n) : ⟪x, y⟫_ℂ = ∑ l, conj (x l) * y l := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply, RCLike.star_def]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

/-! ### The data vector -/

variable (T ρ) in
/-- The representative `s (√σᵀ)⁻¹ ∂̄G` of the data functional in `H₂`. -/
def ydF (z : ComplexModel n) : ComplexModel n :=
  T.U.indicator (fun z => ((T.sw ρ z : ℝ) : ℂ) • mv (Bi T.omega T.r z) (T.gam z)) z

theorem norm_inner_gam_sq_le {z : ComplexModel n} (hz : z ∈ T.U) (v : ComplexModel n) :
    ‖⟪v, T.gam z⟫_ℂ‖ ^ 2 ≤ max (T.Dσ z) 0 * sigmaQ T.omega T.r z v := by
  set e := atlasFrameAt T.L z
  have hz₀ : z ∈ T.dom e := frameAt_mem_dom hz
  have hzb := ((T.mem_dom).mp hz₀).1
  have hb := T.Dσ_bound chart0 e z ⟨mem_univ z, hzb⟩ hz v
  simp only [chart0_symm_apply] at hb
  have hg : dbarV (chartCoeff T.L chart0 e T.G) z = uc e z • T.gam z := by
    rw [gam_eq hz₀, gamE, indicator_of_mem hz₀, smul_smul, mul_inv_cancel₀ (uc_ne_zero hzb),
      one_smul]
  rw [← inner_dbarV, hg, inner_smul_right, norm_mul, mul_pow] at hb
  have hb' : ‖⟪v, T.gam z⟫_ℂ‖ ^ 2 ≤ T.Dσ z * sigmaQ T.omega T.r z v := by
    have h1 := norm_uc_sq_mul (T := T) hzb
    calc ‖⟪v, T.gam z⟫_ℂ‖ ^ 2
        = ‖uc e z‖ ^ 2 * ‖⟪v, T.gam z⟫_ℂ‖ ^ 2 * frameNormSq T.L e z := by
          rw [mul_comm (‖uc e z‖ ^ 2), mul_assoc, h1, mul_one]
      _ ≤ _ := hb
  have hq : 0 ≤ sigmaQ T.omega T.r z v := by
    rw [sigmaQ_eq_norm_sq T.isOpen_U T.kahler hz]; positivity
  exact hb'.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hq)

variable (hρ : IsChartDensity T.μ chart0 ρ)
include hρ

theorem norm_ydF_sq_le (z : ComplexModel n) :
    ‖T.ydF ρ z‖ ^ 2 ≤ T.U.indicator (fun z => max (T.Dσ z) 0 * T.sw ρ z ^ 2) z := by
  by_cases hz : z ∈ T.U
  · rw [ydF, indicator_of_mem hz, indicator_of_mem hz, norm_smul, Complex.norm_real,
      Real.norm_of_nonneg (sw_pos hρ z).le, mul_pow]
    have h := norm_mv_Bi_sq_le T.isOpen_U T.kahler hz (le_max_right _ _)
      (norm_inner_gam_sq_le hz)
    have hs := sq_nonneg (T.sw ρ z)
    nlinarith
  · simp [ydF, hz]

theorem aestronglyMeasurable_ydF : AEStronglyMeasurable (T.ydF ρ) volume := by
  have hO := T.isOpen_U.measurableSet
  have hr : T.ydF ρ = T.U.indicator
      (fun z => ((T.sw ρ z : ℝ) : ℂ) • mv (Bi T.omega T.r z) (T.gam z)) := rfl
  rw [hr]
  refine (aestronglyMeasurable_indicator_iff hO).mpr ?_
  have h1 : AEStronglyMeasurable (fun z => ((T.sw ρ z : ℝ) : ℂ)) (volume.restrict T.U) :=
    (Complex.continuous_ofReal.comp_continuousOn (continuousOn_sw hρ)).aestronglyMeasurable hO
  have h2 : ∀ i j, AEStronglyMeasurable (fun z => Bi T.omega T.r z i j) (volume.restrict T.U) :=
    fun i j => (continuousOn_entry (continuousOn_Bi T.isOpen_U T.kahler) i j).aestronglyMeasurable hO
  exact h1.smul (aestronglyMeasurable_mv h2 measurable_gam.aestronglyMeasurable)

theorem memLp_ydF : MemLp (T.ydF ρ) 2 volume := by
  refine ⟨aestronglyMeasurable_ydF hρ, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
  have hU := T.isOpen_U.measurableSet
  have hρm : Measurable fun z => ENNReal.ofReal (ρ z) :=
    ENNReal.measurable_ofReal.comp (continuous_of_isChartDensity hρ).measurable
  calc ∫⁻ z, ‖T.ydF ρ z‖ₑ ^ (2 : ℝ≥0∞).toReal
      ≤ ∫⁻ z, T.U.indicator (fun z => ENNReal.ofReal (max (T.Dσ z) 0 * T.sw ρ z ^ 2)) z := by
        refine lintegral_mono fun z => ?_
        have h := norm_ydF_sq_le hρ z
        rw [← ofReal_norm, ENNReal.toReal_ofNat, ENNReal.ofReal_rpow_of_nonneg
          (norm_nonneg _) (by norm_num)]
        by_cases hz : z ∈ T.U
        · rw [indicator_of_mem hz]; rw [indicator_of_mem hz] at h
          exact ENNReal.ofReal_le_ofReal (by exact_mod_cast h)
        · rw [indicator_of_notMem hz]; rw [indicator_of_notMem hz] at h
          have : ‖T.ydF ρ z‖ ^ (2 : ℝ) = 0 := by
            have h0 : ‖T.ydF ρ z‖ = 0 := by nlinarith [norm_nonneg (T.ydF ρ z)]
            rw [h0]; norm_num
          rw [this, ENNReal.ofReal_zero]
    _ = ∫⁻ z in T.U, ENNReal.ofReal (max (T.Dσ z) 0 * T.sw ρ z ^ 2) := lintegral_indicator hU _
    _ = ∫⁻ x in T.U, ENNReal.ofReal (T.Dσ x * Real.exp (-T.φ x)) ∂T.μ := by
        rw [measure_eq_withDensity hρ, restrict_withDensity hU,
          lintegral_withDensity_eq_lintegral_mul_non_measurable _ hρm
            (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
        refine lintegral_congr fun z => ?_
        simp only [Pi.mul_apply]
        rw [← ENNReal.ofReal_mul (pos_of_isChartDensity hρ z).le, sw_sq hρ]
        rcases le_total 0 (T.Dσ z) with h | h
        · rw [max_eq_left h]; ring_nf
        · rw [max_eq_right h, zero_mul, ENNReal.ofReal_zero]
          have h1 := Real.exp_pos (-T.φ z)
          have h2 := pos_of_isChartDensity hρ z
          refine (ENNReal.ofReal_of_nonpos ?_).symm
          have : 0 ≤ ρ z * (-T.Dσ z * Real.exp (-T.φ z)) :=
            mul_nonneg h2.le (mul_nonneg (by linarith) h1.le)
          nlinarith
    _ < ⊤ := T.Dσ_integrable

/-- `⟪repF e h, ydF⟫ = ⟨∂̄G_e, h⟩ e^{-p_e}` pointwise. -/
theorem inner_repF_ydF (e : AtlasFrame T.L) (h : ComplexModel n → ComplexModel n)
    (z : ComplexModel n) :
    ⟪T.repF ρ e h z, T.ydF ρ z⟫_ℂ = (T.dom e).indicator
      (fun z => dbarPairing (chartCoeff T.L chart0 e T.G) z (h z) * cweight (T.pW ρ e) z) z := by
  by_cases hz : z ∈ T.dom e
  · have hzU := dom_subset_U e hz
    rw [repF, indicator_of_mem hz, ydF, indicator_of_mem hzU, indicator_of_mem hz, FD_eq hρ hz,
      inner_smul_left, inner_smul_right, Complex.conj_ofReal, inner_mv_left, Bm_conjTranspose,
      ← mv_mul, Bm_mul_Bi T.isOpen_U T.kahler hzU, mv_one]
    push_cast
    ring
  · rw [repF, indicator_of_notMem hz, indicator_of_notMem hz, inner_zero_left]

/-! ### The `T*`-test vectors -/

variable (T) in
/-- `σ^{-T} ∂̄u`: the `H₂`-representative of `T u = ∂̄u` (in the frame of `u`). -/
def Yu (u : ComplexModel n → ℂ) (z : ComplexModel n) : ComplexModel n :=
  mv (sigmaInv T.omega T.r z) (dbarV u z)

omit hρ in
theorem Yu_eq_zero {u : ComplexModel n → ℂ} {z : ComplexModel n} (hz : z ∉ tsupport u) :
    T.Yu u z = 0 := by
  have : dbarV u z = 0 := by
    ext l; simp [dbarV, dbarDir_eq_zero_of_notMem hz]
  simp [Yu, this]

omit hρ in
theorem tsupport_Yu_subset (u : ComplexModel n → ℂ) : tsupport (T.Yu u) ⊆ tsupport u :=
  closure_minimal (fun z hz => by
    by_contra h
    exact hz (Yu_eq_zero h)) (isClosed_tsupport u)

omit hρ in
theorem continuous_Yu {e : AtlasFrame T.L} {u : ComplexModel n → ℂ}
    (hu : IsTestFunctionOn (T.dom e) u) : Continuous (T.Yu u) := by
  have h2 : Continuous (dbarV u) :=
    (PiLp.continuous_toLp 2 _).comp (continuous_pi fun l => continuous_dbarDir' (hu.1.of_le (by simp)))
  have hc : ContinuousOn (T.Yu u) T.U :=
    continuousOn_mv (fun i j => continuousOn_entry continuousOn_sigmaInv i j) h2.continuousOn
  exact continuous_of_continuousOn_of_eq_zero' T.isOpen_U hc (isClosed_tsupport u)
    (hu.2.2.trans (dom_subset_U e)) fun z hz => Yu_eq_zero hz

theorem memLp_Yu {e : AtlasFrame T.L} {u : ComplexModel n → ℂ}
    (hu : IsTestFunctionOn (T.dom e) u) : MemLp (T.repF ρ e (T.Yu u)) 2 volume :=
  memLp_repF_of_continuous hρ (continuous_Yu hu) (hu.2.1.mono' fun z hz => by
    by_contra h; exact hz (Yu_eq_zero h)) ((tsupport_Yu_subset u).trans hu.2.2)

/-- The test vector of the `T*`-pairing with the test function `u` in the frame `e`. -/
def ylam (e : AtlasFrame T.L) {u : ComplexModel n → ℂ} (hu : IsTestFunctionOn (T.dom e) u) :
    H2 n := (memLp_Yu hρ hu).toLp _

/-- **The `T*`-pairing in frame coordinates.** -/
theorem inner_ylam (e : AtlasFrame T.L) {u : ComplexModel n → ℂ}
    (hu : IsTestFunctionOn (T.dom e) u) (x : H2 n) :
    ⟪x, ylam hρ e hu⟫_ℂ = ∫ z, (T.dom e).indicator (fun z => cweight (T.pW ρ e) z *
      ∑ l, dbarDir (coordVec l) u z * conj ((uc e z • T.Weps ρ x z) l)) z := by
  rw [ylam, inner_toLp_right]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only
  rw [← inner_conj_symm, inner_repF hρ]
  by_cases hz : z ∈ T.dom e
  · have hzU := dom_subset_U e hz
    have hzb := ((T.mem_dom).mp hz).1
    rw [indicator_of_mem hz, indicator_of_mem hz, inner_smul_left, inner_mv_right,
      sT_conjTranspose hzU, Yu, ← mv_mul, sT_mul_sigmaInv hzU, mv_one, inner_eq_sum]
    have hu0 := uc_ne_zero (T := T) hzb
    have hsc : ((T.sw ρ z ^ 2 : ℝ) : ℂ) * (uc e z)⁻¹ = cweight (T.pW ρ e) z * conj (uc e z) := by
      rw [← exp_neg_pW_mul_norm_uc hρ hzb, cweight]
      push_cast
      rw [← Complex.mul_conj']
      field_simp
    simp only [map_mul, map_sum, map_inv₀, Complex.conj_conj, Complex.conj_ofReal, PiLp.smul_apply,
      smul_eq_mul, Finset.mul_sum, dbarV]
    refine Finset.sum_congr rfl fun l _ => ?_
    linear_combination (dbarDir (coordVec l) u z * conj (T.Weps ρ x z l)) * hsc
  · rw [indicator_of_notMem hz, indicator_of_notMem hz, map_zero]

omit hρ in
theorem Weps_congr {x y : ComplexModel n → ComplexModel n} {z : ComplexModel n} (h : x z = y z) :
    T.Weps ρ x z = T.Weps ρ y z := by
  simp only [Weps, Set.indicator, h]

theorem inner_ylam_of_ae (e : AtlasFrame T.L) {u : ComplexModel n → ℂ}
    (hu : IsTestFunctionOn (T.dom e) u) (x : H2 n) {f : ComplexModel n → ComplexModel n}
    (hxf : ⇑x =ᵐ[volume] f) :
    ⟪x, ylam hρ e hu⟫_ℂ = ∫ z, (T.dom e).indicator (fun z => cweight (T.pW ρ e) z *
      ∑ l, dbarDir (coordVec l) u z * conj ((uc e z • T.Weps ρ f z) l)) z := by
  rw [inner_ylam]
  refine integral_congr_ae ?_
  filter_upwards [hxf] with z hz
  simp only [Set.indicator]
  rw [Weps_congr hz]

/-! ### The special families -/

variable (T ρ) in
/-- The special family `e^{p_e} (∂_k ψ ∂/∂z_j - ∂_j ψ ∂/∂z_k) = S*(ψ dz̄_j ∧ dz̄_k)` in the frame
`e`. -/
def specV (e : AtlasFrame T.L) (ψ : ComplexModel n → ℂ) (j k : Fin n) (z : ComplexModel n) :
    ComplexModel n :=
  ((Real.exp (T.pW ρ e z) : ℝ) : ℂ) •
    (dDir (coordVec k) ψ z • (coordVec j : ComplexModel n) - dDir (coordVec j) ψ z • coordVec k)

omit hρ in
theorem specV_eq_zero {e : AtlasFrame T.L} {ψ : ComplexModel n → ℂ} {j k : Fin n}
    {z : ComplexModel n} (hz : z ∉ tsupport ψ) : T.specV ρ e ψ j k z = 0 := by
  simp [specV, dDir_eq_zero_of_notMem hz]

theorem continuous_specV {e : AtlasFrame T.L} {ψ : ComplexModel n → ℂ}
    (hψ : IsTestFunctionOn (T.dom e) ψ) (j k : Fin n) : Continuous (T.specV ρ e ψ j k) := by
  have hO := T.isOpen_dom e
  have h1 : ContinuousOn (fun z => ((Real.exp (T.pW ρ e z) : ℝ) : ℂ)) (T.dom e) :=
    Complex.continuous_ofReal.comp_continuousOn
      (Real.continuous_exp.comp_continuousOn (T.contDiffOn_pW hρ e).continuousOn)
  have hd : ∀ v, Continuous (dDir v ψ) := fun v =>
    (contDiff_dDir (k := 0) (hψ.1.of_le (by norm_num))).continuous
  refine continuous_of_continuousOn_of_eq_zero' hO ?_ (isClosed_tsupport ψ) hψ.2.2
    fun z hz => specV_eq_zero hz
  exact h1.smul ((((hd _).smul continuous_const).sub
    ((hd _).smul continuous_const)).continuousOn)

theorem memLp_specV {e : AtlasFrame T.L} {ψ : ComplexModel n → ℂ}
    (hψ : IsTestFunctionOn (T.dom e) ψ) (j k : Fin n) :
    MemLp (T.repF ρ e (T.specV ρ e ψ j k)) 2 volume := by
  have hsupp : tsupport (T.specV ρ e ψ j k) ⊆ tsupport ψ :=
    closure_minimal (fun z hz => by
      by_contra h
      exact hz (specV_eq_zero h)) (isClosed_tsupport ψ)
  exact memLp_repF_of_continuous hρ (continuous_specV hρ hψ j k)
    (hψ.2.1.mono' fun z hz => subset_closure hz |> hsupp) (hsupp.trans hψ.2.2)

/-- **The `H₂`-pairing with a special family**: `σ` cancels. -/
theorem inner_specV {e : AtlasFrame T.L} {ψ : ComplexModel n → ℂ}
    (hψ : IsTestFunctionOn (T.dom e) ψ) (j k : Fin n) (x : H2 n) :
    ⟪(memLp_specV hρ hψ j k).toLp _, x⟫_ℂ = ∫ z, (T.dom e).indicator (fun z =>
      conj (dDir (coordVec k) ψ z) * mv (sT T.omega T.r z) (uc e z • T.Weps ρ x z) j -
      conj (dDir (coordVec j) ψ z) * mv (sT T.omega T.r z) (uc e z • T.Weps ρ x z) k) z := by
  rw [inner_toLp_left]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only
  rw [inner_repF hρ]
  by_cases hz : z ∈ T.dom e
  · rw [indicator_of_mem hz, indicator_of_mem hz]
    have hzb := ((T.mem_dom).mp hz).1
    have hu0 := uc_ne_zero (T := T) hzb
    have hsc : ((T.sw ρ z ^ 2 : ℝ) : ℂ) * conj (uc e z)⁻¹ * ((Real.exp (T.pW ρ e z) : ℝ) : ℂ) =
        uc e z := by
      rw [← exp_neg_pW_mul_norm_uc hρ hzb]
      have hc : conj (uc e z) ≠ 0 := by simpa using hu0
      have he : ((Real.exp (-T.pW ρ e z) : ℝ) : ℂ) * ((Real.exp (T.pW ρ e z) : ℝ) : ℂ) = 1 := by
        rw [← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, Complex.ofReal_one]
      have h1 : (((Real.exp (-T.pW ρ e z) * ‖uc e z‖ ^ 2 : ℝ)) : ℂ) =
          ((Real.exp (-T.pW ρ e z) : ℝ) : ℂ) * (uc e z * conj (uc e z)) := by
        rw [Complex.ofReal_mul, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      rw [h1, map_inv₀]
      calc ((Real.exp (-T.pW ρ e z) : ℝ) : ℂ) * (uc e z * conj (uc e z)) * (conj (uc e z))⁻¹ *
            ((Real.exp (T.pW ρ e z) : ℝ) : ℂ)
          = uc e z * (((Real.exp (-T.pW ρ e z) : ℝ) : ℂ) * ((Real.exp (T.pW ρ e z) : ℝ) : ℂ)) *
            (conj (uc e z) * (conj (uc e z))⁻¹) := by ring
        _ = uc e z := by rw [he, mul_inv_cancel₀ hc]; ring
    rw [specV, inner_smul_left, inner_smul_left, Complex.conj_ofReal, inner_sub_left,
      inner_smul_left, inner_smul_left, EuclideanSpace.inner_single_left,
      EuclideanSpace.inner_single_left, mv_smul]
    simp only [PiLp.smul_apply, smul_eq_mul, map_one, one_mul]
    linear_combination (conj (dDir (coordVec k) ψ z) * mv (sT T.omega T.r z) (T.Weps ρ (⇑x) z) j -
      conj (dDir (coordVec j) ψ z) * mv (sT T.omega T.r z) (T.Weps ρ (⇑x) z) k) * hsc
  · rw [indicator_of_notMem hz, indicator_of_notMem hz]

variable (T) in
/-- The scalar transport `t_{e e'} u` of a test function from the frame `e` to `e'`. -/
def tsc (e e' : AtlasFrame T.L) (u : ComplexModel n → ℂ) (z : ComplexModel n) : ℂ :=
  open Classical in if z ∈ e.val.baseSet then frameTrans T.L e e' z * u z else 0

omit hρ in
theorem tsc_eventuallyEq_mul {e e' : AtlasFrame T.L} (u : ComplexModel n → ℂ) {z : ComplexModel n}
    (hz : z ∈ e.val.baseSet) : T.tsc e e' u =ᶠ[𝓝 z] fun y => frameTrans T.L e e' y * u y := by
  filter_upwards [e.val.open_baseSet.mem_nhds hz] with y hy
  simp only [tsc, if_pos hy]

omit hρ in
theorem tsc_eventuallyEq_zero {e e' : AtlasFrame T.L} {u : ComplexModel n → ℂ} {z : ComplexModel n}
    (hz : z ∉ tsupport u) : T.tsc e e' u =ᶠ[𝓝 z] fun _ => 0 := by
  filter_upwards [(isClosed_tsupport u).isOpen_compl.mem_nhds hz] with y hy
  simp only [tsc, image_eq_zero_of_notMem_tsupport hy, mul_zero, ite_self]

omit hρ in
theorem contDiffOn_tsc {e e' : AtlasFrame T.L} {u : ComplexModel n → ℂ} (hu : ContDiff ℝ ∞ u)
    (hts : tsupport u ⊆ e.val.baseSet) : ContDiffOn ℝ ∞ (T.tsc e e' u) e'.val.baseSet := by
  intro z hz
  apply ContDiffAt.contDiffWithinAt
  by_cases hz₀ : z ∈ e.val.baseSet
  · have hO : IsOpen (e.val.baseSet ∩ e'.val.baseSet) := e.val.open_baseSet.inter e'.val.open_baseSet
    have ht : ContDiffAt ℝ ∞ (frameTrans T.L e e') z :=
      (contDiffOn_frameTrans e e').contDiffAt (hO.mem_nhds ⟨hz₀, hz⟩)
    exact (ht.mul hu.contDiffAt).congr_of_eventuallyEq (tsc_eventuallyEq_mul u hz₀)
  · exact contDiffAt_const.congr_of_eventuallyEq (tsc_eventuallyEq_zero fun h => hz₀ (hts h))

omit hρ in
theorem sum_dbar_conj_eq_inner (u : ComplexModel n → ℂ) (z Y : ComplexModel n) :
    ∑ l, dbarDir (coordVec l) u z * conj (Y l) = ⟪Y, dbarV u z⟫_ℂ := by
  rw [inner_eq_sum]
  exact Finset.sum_congr rfl fun l _ => by simp [dbarV, mul_comm]

/-- The special families are orthogonal to the `T*`-test vectors (`T* S* = 0`). -/
theorem inner_specV_ylam {e' : AtlasFrame T.L} {ψ : ComplexModel n → ℂ}
    (hψ : IsTestFunctionOn (T.dom e') ψ) (j k : Fin n) {e : AtlasFrame T.L}
    {u : ComplexModel n → ℂ} (hu : IsTestFunctionOn (T.dom e) u) :
    ⟪(memLp_specV hρ hψ j k).toLp _, ylam hρ e hu⟫_ℂ = 0 := by
  rw [inner_ylam_of_ae hρ e hu _ (memLp_specV hρ hψ j k).coeFn_toLp]
  have hut : tsupport u ⊆ e.val.baseSet := fun z hz => ((T.mem_dom).mp (hu.2.2 hz)).1
  have hg : ContDiffOn ℝ ∞ (T.tsc e e' u) (T.dom e') :=
    (contDiffOn_tsc hu.1 hut).mono fun z hz => ((T.mem_dom).mp hz).1
  rw [← integral_antisym_eq_zero (T.isOpen_dom e') hg hψ j k]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only
  by_cases h1 : z ∈ T.dom e'
  · by_cases h2 : z ∈ T.dom e
    · rw [indicator_of_mem h2, Weps_repF hρ h1, sum_dbar_conj_eq_inner]
      have hzb : z ∈ e'.val.baseSet ∩ e.val.baseSet :=
        ⟨((T.mem_dom).mp h1).1, ((T.mem_dom).mp h2).1⟩
      have htt := frameTrans_mul_symm e e' ⟨hzb.2, hzb.1⟩
      have hhol : DifferentiableAt ℂ (frameTrans T.L e e') z :=
        (differentiableOn_frameTrans_model e e').differentiableAt
          ((e.val.open_baseSet.inter e'.val.open_baseSet).mem_nhds ⟨hzb.2, hzb.1⟩)
      have hud : DifferentiableAt ℝ u z := hu.1.differentiable (by simp) z
      have hdg : ∀ v, dbarDir v (T.tsc e e' u) z = frameTrans T.L e e' z * dbarDir v u z :=
        fun v => by
          rw [dbarDir_congr_of_eventuallyEq (tsc_eventuallyEq_mul u hzb.2),
            dbarDir_holo_mul hhol hud]
      have huc : uc e z = frameTrans T.L e' e z * uc e' z := uc_trans hzb
      have hu0 := uc_ne_zero (T := T) hzb.1
      have hcuc : conj (uc e z) * conj (uc e' z)⁻¹ = conj (frameTrans T.L e' e z) := by
        rw [huc, map_mul, map_inv₀]
        have : conj (uc e' z) ≠ 0 := by simpa using hu0
        field_simp
      have hA := (T.gaugeData_pW (ρ := ρ) e' e).cweight_mul (y := z) ⟨h1, h2⟩
      have hB : cweight (T.pW ρ e') z * ((Real.exp (T.pW ρ e' z) : ℝ) : ℂ) = 1 := by
        rw [cweight, ← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
          Complex.ofReal_one]
      rw [specV, inner_smul_left, inner_smul_left, inner_smul_left, inner_sub_left,
        inner_smul_left, inner_smul_left, EuclideanSpace.inner_single_left,
        EuclideanSpace.inner_single_left, hdg, hdg, Complex.conj_ofReal]
      simp only [dbarV, map_one, one_mul, PiLp.toLp_apply]
      linear_combination (cweight (T.pW ρ e) z * ((Real.exp (T.pW ρ e' z) : ℝ) : ℂ) *
          (conj (dDir (coordVec k) ψ z) * dbarDir (coordVec j) u z -
            conj (dDir (coordVec j) ψ z) * dbarDir (coordVec k) u z)) * hcuc +
        (frameTrans T.L e e' z * ((Real.exp (T.pW ρ e' z) : ℝ) : ℂ) *
          (conj (dDir (coordVec k) ψ z) * dbarDir (coordVec j) u z -
            conj (dDir (coordVec j) ψ z) * dbarDir (coordVec k) u z)) * hA +
        (frameTrans T.L e e' z * (conj (dDir (coordVec k) ψ z) * dbarDir (coordVec j) u z -
            conj (dDir (coordVec j) ψ z) * dbarDir (coordVec k) u z)) * hB -
        (cweight (T.pW ρ e) z * ((Real.exp (T.pW ρ e' z) : ℝ) : ℂ) *
          conj (frameTrans T.L e' e z) *
          (conj (dDir (coordVec k) ψ z) * dbarDir (coordVec j) u z -
            conj (dDir (coordVec j) ψ z) * dbarDir (coordVec k) u z)) * htt
    · rw [indicator_of_notMem h2]
      have hzU := dom_subset_U e' h1
      have hzb : z ∉ e.val.baseSet := fun h => h2 ((T.mem_dom).mpr ⟨h, hzU⟩)
      have hzu : z ∉ tsupport u := fun h => hzb (hut h)
      have hev := tsc_eventuallyEq_zero (T := T) (e := e) (e' := e') hzu
      simp [dbarDir_congr_of_eventuallyEq hev, dbarDir_const]
  · have hzψ : z ∉ tsupport ψ := fun h => h1 (hψ.2.2 h)
    rw [dDir_eq_zero_of_notMem hzψ, dDir_eq_zero_of_notMem hzψ]
    by_cases h2 : z ∈ T.dom e
    · rw [indicator_of_mem h2, Weps_repF_of_notMem hρ h1]
      simp
    · rw [indicator_of_notMem h2]; simp

/-- The special families have zero data pairing (`∂̄∂̄G = 0`). -/
theorem inner_specV_yd {e : AtlasFrame T.L} {ψ : ComplexModel n → ℂ}
    (hψ : IsTestFunctionOn (T.dom e) ψ) (j k : Fin n) :
    ⟪(memLp_specV hρ hψ j k).toLp _, (memLp_ydF hρ).toLp _⟫_ℂ = 0 := by
  rw [inner_toLp_toLp]
  simp_rw [inner_repF_ydF hρ]
  rw [← integral_antisym_eq_zero (T.isOpen_dom e) (T.contDiffOn_G e) hψ j k]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only
  by_cases hz : z ∈ T.dom e
  · have hB : cweight (T.pW ρ e) z * ((Real.exp (T.pW ρ e z) : ℝ) : ℂ) = 1 := by
      rw [cweight, ← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
        Complex.ofReal_one]
    rw [indicator_of_mem hz, ← inner_dbarV, specV, inner_smul_left, inner_sub_left,
      inner_smul_left, inner_smul_left, EuclideanSpace.inner_single_left,
      EuclideanSpace.inner_single_left, Complex.conj_ofReal]
    simp only [dbarV, map_one, one_mul, PiLp.toLp_apply]
    linear_combination (dbarDir (coordVec j) (chartCoeff T.L chart0 e T.G) z *
        conj (dDir (coordVec k) ψ z) - dbarDir (coordVec k) (chartCoeff T.L chart0 e T.G) z *
        conj (dDir (coordVec j) ψ z)) * hB
  · have hzψ : z ∉ tsupport ψ := fun h => hz (hψ.2.2 h)
    rw [indicator_of_notMem hz, dDir_eq_zero_of_notMem hzψ, dDir_eq_zero_of_notMem hzψ]
    simp

/-! ### Test families in `H₂` -/

theorem memLp_piece {e : AtlasFrame T.L} {h : ComplexModel n → ComplexModel n}
    (hh : IsLocalTestField T.L T.U chart0 e h) : MemLp (T.repF ρ e h) 2 volume :=
  memLp_repF_of_continuous hρ hh.1.continuous hh.2.1 hh.2.2

/-- The representative of a test family in `H₂`. -/
def repFam (F : T.FrameFamily) : H2 n := ∑ i ∈ F.s, (memLp_piece hρ (F.spec i)).toLp _

theorem coeFn_repFam (F : T.FrameFamily) :
    ⇑(repFam hρ F) =ᵐ[volume] fun z => ∑ i ∈ F.s, T.repF ρ (F.e i) (F.h i) z := by
  have h1 := Lp.coeFn_fun_finsetSum F.s fun i => (memLp_piece hρ (F.spec i)).toLp _
  have h2 : ∀ᵐ z ∂volume, ∀ i ∈ F.s, ((memLp_piece hρ (F.spec i)).toLp _ : H2 n) z =
      T.repF ρ (F.e i) (F.h i) z :=
    (F.s.eventually_all).mpr fun i _ => (memLp_piece hρ (F.spec i)).coeFn_toLp
  filter_upwards [h1, h2] with z hz1 hz2
  rw [repFam, hz1]
  exact Finset.sum_congr rfl hz2

/-- **The data pairing of a family is its `H₂`-pairing with the data vector.** -/
theorem inner_repFam_yd (F : T.FrameFamily) :
    ⟪repFam hρ F, (memLp_ydF hρ).toLp _⟫_ℂ = F.data ρ := by
  rw [repFam, sum_inner, FrameFamily.data]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_toLp_toLp, localDataPairing]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only
  rw [inner_repF_ydF hρ]
  by_cases hz : z ∈ T.dom (F.e i)
  · rw [indicator_of_mem hz]; rfl
  · have h0 : F.h i z = 0 :=
      image_eq_zero_of_notMem_tsupport fun h => hz (T.tsupport_subset_dom F.spec i h)
    rw [indicator_of_notMem hz, h0, dbarPairing_zero, zero_mul]

omit hρ in
theorem Weps_sum {ι : Type*} (s : Finset ι) (f : ι → ComplexModel n → ComplexModel n)
    (z : ComplexModel n) :
    T.Weps ρ (fun z => ∑ i ∈ s, f i z) z = ∑ i ∈ s, T.Weps ρ (f i) z := by
  by_cases hz : z ∈ T.U
  · simp only [Weps, indicator_of_mem hz, mv_sum, Finset.smul_sum]
  · simp [Weps, indicator_of_notMem hz]

theorem uc_Weps_repFam (F : T.FrameFamily) {e : AtlasFrame T.L} {z : ComplexModel n}
    (hz : z ∈ T.dom e) :
    uc e z • T.Weps ρ (fun z => ∑ i ∈ F.s, T.repF ρ (F.e i) (F.h i) z) z =
      T.tot F.s F.e F.h e z := by
  have hc := cov_sum (isCovariant_id (T := T)) F.spec (s := F.s) hz
  rw [Weps_sum, hc]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hzi : z ∈ T.dom (F.e i)
  · exact Weps_repF hρ hzi
  · rw [Weps_repF_of_notMem hρ hzi, image_eq_zero_of_notMem_tsupport
      (fun h => hzi (T.tsupport_subset_dom F.spec i h)), smul_zero]

/-- **The `T*`-pairing of a family** (integration by parts in the frame of the test function). -/
theorem inner_repFam_ylam (F : T.FrameFamily) {e : AtlasFrame T.L} {u : ComplexModel n → ℂ}
    (hu : IsTestFunctionOn (T.dom e) u) :
    ⟪repFam hρ F, ylam hρ e hu⟫_ℂ =
      ∫ z, u z * conj (chartTheta (T.pW ρ e) (T.tot F.s F.e F.h e) z) * cweight (T.pW ρ e) z := by
  rw [inner_ylam_of_ae hρ e hu _ (coeFn_repFam hρ F),
    ← integral_dbar_conj_eq (T.isOpen_dom e) (T.contDiffOn_pW hρ e)
      ((T.contDiffOn_tot F.spec e).mono fun z hz => ((T.mem_dom).mp hz).1) hu]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only
  by_cases hz : z ∈ T.dom e
  · rw [indicator_of_mem hz, uc_Weps_repFam hρ F hz]
  · have hzu : z ∉ tsupport u := fun h => hz (hu.2.2 h)
    rw [indicator_of_notMem hz]
    simp [dbarDir_eq_zero_of_notMem hzu]

/-! ### The projection -/

variable (T) in
/-- The index type of the special families. -/
def SpecIdx : Type :=
  {q : AtlasFrame T.L × (ComplexModel n → ℂ) × Fin n × Fin n // IsTestFunctionOn (T.dom q.1) q.2.1}

/-- The special families in `H₂`. -/
def gen (q : T.SpecIdx) : H2 n := (memLp_specV hρ q.2 q.1.2.2.1 q.1.2.2.2).toLp _

/-- **The projected field** (`claude-tl2-dens:projection`): for every test family `τ` there is
`v ∈ H₂` with `∂̄(σ^♭ v) = 0` weakly in every frame, `T* v = T* τ` weakly in every frame, and
`⟨v, ∂̄G⟩ = ⟨τ, ∂̄G⟩`. -/
theorem exists_v (F : T.FrameFamily) : ∃ v : H2 n,
    (∀ (e : AtlasFrame T.L) (ψ : ComplexModel n → ℂ), IsTestFunctionOn (T.dom e) ψ →
      ∀ j k : Fin n, ∫ z, (T.dom e).indicator (fun z =>
        conj (dDir (coordVec k) ψ z) * mv (sT T.omega T.r z) (uc e z • T.Weps ρ v z) j -
        conj (dDir (coordVec j) ψ z) * mv (sT T.omega T.r z) (uc e z • T.Weps ρ v z) k) z = 0) ∧
    (∀ (e : AtlasFrame T.L) (u : ComplexModel n → ℂ), IsTestFunctionOn (T.dom e) u →
      ∫ z, (T.dom e).indicator (fun z => cweight (T.pW ρ e) z *
        ∑ l, dbarDir (coordVec l) u z * conj ((uc e z • T.Weps ρ v z) l)) z =
      ∫ z, u z * conj (chartTheta (T.pW ρ e) (T.tot F.s F.e F.h e) z) * cweight (T.pW ρ e) z) ∧
    ⟪v, (memLp_ydF hρ).toLp _⟫_ℂ = F.data ρ := by
  obtain ⟨v, h1, h2⟩ := exists_proj_orth (gen hρ) (repFam hρ F)
  refine ⟨v, fun e ψ hψ j k => ?_, fun e u hu => ?_, ?_⟩
  · have := h1 ⟨(e, ψ, j, k), hψ⟩
    rw [show gen hρ ⟨(e, ψ, j, k), hψ⟩ = (memLp_specV hρ hψ j k).toLp _ from rfl,
      inner_specV hρ hψ j k] at this
    exact this
  · have := h2 (ylam hρ e hu) fun q => inner_specV_ylam hρ q.2 _ _ hu
    rw [inner_ylam, inner_repFam_ylam] at this
    exact this
  · rw [h2 _ fun q => inner_specV_yd hρ q.2 _ _, inner_repFam_yd]

end TwistedDatum

end SGPT.Trace.TwistedL2
