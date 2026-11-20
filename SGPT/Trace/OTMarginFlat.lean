import SGPT.Trace.OTMarginRamified
import SGPT.Foundations.Analysis.Pending.ProductMixedMeasure
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-!
# Normal weights in flattening coordinates

Blueprint `claude-ot3.tex`, node `claude-ot3:flat`.

In `ℂ^n = ℂ^m × ℂ^{n-m}` with the coordinate plane `W = {w = 0}` and `|w|² = normalWeight n m`:

* `lintegral_normalWeight_rpow_lt_top`: `|w|^{-2c}` is integrable on bounded sets for `c < n - m`;
* `eq_zero_of_lintegral_normalWeight`: a holomorphic `h` with `∫ |h|² |w|^{-2(n-m)} < ∞` near a
  point of `W` vanishes there (the critical exponent is not integrable);
* `exists_sq_le_normalWeight`: a holomorphic function vanishing on `W` satisfies `|h|² ≤ C |w|²`
  on compact sets.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Trace.OTMargin

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal NNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ProductComplexManifold
  SGPT.Foundations.Analysis.Pending.ProductMixedMeasure
  SGPT.Foundations.Analysis.FirstPass.RegularLocusDense

/-! ### The normal weight in product coordinates -/

theorem normalWeight_eq_norm_snd (m d : ℕ) (z : ComplexModel (m + d)) :
    normalWeight (m + d) m z = ‖((prodModelEquiv m d).symm z).2‖ ^ 2 := by
  rw [normalWeight, Fin.sum_univ_add, EuclideanSpace.norm_sq_eq]
  have h1 : ∑ i : Fin m, (if m ≤ (Fin.castAdd d i).1 then ‖z (Fin.castAdd d i)‖ ^ 2 else 0) = 0 :=
    Finset.sum_eq_zero fun i _ => by rw [if_neg (by simp)]
  rw [h1, zero_add]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [if_pos (by simp)]
  rfl

theorem fst_prodModelEquiv_symm (m d : ℕ) (z : ComplexModel (m + d)) :
    ((prodModelEquiv m d).symm z).1 = coordinateProjection (m + d) m z := by
  ext i
  rw [coordinateProjection_apply, dif_pos (by omega)]
  rfl

theorem normalWeight_le_norm_sq (n m : ℕ) (z : ComplexModel n) : normalWeight n m z ≤ ‖z‖ ^ 2 := by
  rw [normalWeight, EuclideanSpace.norm_sq_eq]
  exact Finset.sum_le_sum fun i _ => by
    split_ifs
    · exact le_rfl
    · positivity

theorem norm_sq_prodModelEquiv_symm (m d : ℕ) (z : ComplexModel (m + d)) :
    ‖((prodModelEquiv m d).symm z).1‖ ^ 2 + ‖((prodModelEquiv m d).symm z).2‖ ^ 2 = ‖z‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
    Fin.sum_univ_add]
  rfl

theorem finrank_real_complexModel' (d : ℕ) : Module.finrank ℝ (ComplexModel d) = 2 * d := by
  rw [← Module.finrank_mul_finrank ℝ ℂ (ComplexModel d), Complex.finrank_real_complex,
    finrank_euclideanSpace_fin]

/-- `|w|^{-2c}` as a function of the normal part. -/
theorem normalWeight_rpow_eq (m d : ℕ) (c : ℝ) (z : ComplexModel (m + d)) :
    normalWeight (m + d) m z ^ (-c) = ‖((prodModelEquiv m d).symm z).2‖ ^ (-(2 * c)) := by
  rw [normalWeight_eq_norm_snd, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
  congr 1; push_cast; ring

/-- Integrals over a product of balls in `ℂ^m × ℂ^d` of functions of the normal part. -/
theorem lintegral_image_prod_ball (m d : ℕ) (a : ComplexModel m) (ε : ℝ) (g : ComplexModel d → ℝ≥0∞)
    (hg : Measurable g) :
    ∫⁻ z in prodModelEquiv m d '' (ball a ε ×ˢ ball (0 : ComplexModel d) ε),
        g ((prodModelEquiv m d).symm z).2 =
      volume (ball a ε) * ∫⁻ w in ball (0 : ComplexModel d) ε, g w := by
  have hmp := measurePreserving_prodModelEquiv m d
  have hemb : MeasurableEmbedding (prodModelEquiv m d) :=
    (prodModelEquiv m d).toHomeomorph.measurableEmbedding
  rw [← hmp.setLIntegral_comp_emb hemb]
  simp only [ContinuousLinearEquiv.symm_apply_apply]
  rw [← Measure.prod_restrict]
  have := lintegral_prod_mul (μ := volume.restrict (ball a ε))
    (ν := volume.restrict (ball (0 : ComplexModel d) ε)) (f := fun _ => (1 : ℝ≥0∞))
    aemeasurable_const hg.aemeasurable
  simp only [one_mul, lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter]
    at this
  exact this

/-- **Subcritical integrability.**  For `0 ≤ c < n - m`, `∫_{B(0,R)} |w|^{-2c} < ∞`. -/
theorem lintegral_normalWeight_rpow_lt_top {n m : ℕ} (hmn : m < n) {c : ℝ}
    (hc : c < ((n - m : ℕ) : ℝ)) (R : ℝ) :
    ∫⁻ z in ball (0 : ComplexModel n) R, ENNReal.ofReal (normalWeight n m z ^ (-c)) < ⊤ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn.le
  have hd : 1 ≤ d := by omega
  have hsub : m + d - m = d := by omega
  rw [hsub] at hc
  set e := prodModelEquiv m d with he
  have hball : ball (0 : ComplexModel (m + d)) R ⊆
      e '' (ball (0 : ComplexModel m) R ×ˢ ball (0 : ComplexModel d) R) := by
    intro z hz
    refine ⟨e.symm z, ⟨?_, ?_⟩, e.apply_symm_apply z⟩
    · rw [mem_ball_zero_iff]
      have h1 := norm_sq_prodModelEquiv_symm m d z
      have h2 : ‖(e.symm z).1‖ ≤ ‖z‖ := by
        nlinarith [norm_nonneg (e.symm z).1, norm_nonneg z, sq_nonneg ‖(e.symm z).2‖]
      exact h2.trans_lt (mem_ball_zero_iff.mp hz)
    · rw [mem_ball_zero_iff]
      have h1 := norm_sq_prodModelEquiv_symm m d z
      have h2 : ‖(e.symm z).2‖ ≤ ‖z‖ := by
        nlinarith [norm_nonneg (e.symm z).2, norm_nonneg z, sq_nonneg ‖(e.symm z).1‖]
      exact h2.trans_lt (mem_ball_zero_iff.mp hz)
  have hgm : Measurable fun w : ComplexModel d => ENNReal.ofReal (‖w‖ ^ (-(2 * c))) :=
    ENNReal.measurable_ofReal.comp (measurable_norm.pow_const _)
  calc ∫⁻ z in ball (0 : ComplexModel (m + d)) R, ENNReal.ofReal (normalWeight (m + d) m z ^ (-c))
      ≤ ∫⁻ z in e '' (ball (0 : ComplexModel m) R ×ˢ ball (0 : ComplexModel d) R),
          ENNReal.ofReal (‖(e.symm z).2‖ ^ (-(2 * c))) := by
        refine (lintegral_mono_set hball).trans (le_of_eq ?_)
        refine lintegral_congr fun z => ?_
        rw [normalWeight_rpow_eq]
    _ = volume (ball (0 : ComplexModel m) R) *
          ∫⁻ w in ball (0 : ComplexModel d) R, ENNReal.ofReal (‖w‖ ^ (-(2 * c))) :=
        lintegral_image_prod_ball m d 0 R _ hgm
    _ < ⊤ := by
        refine ENNReal.mul_lt_top measure_ball_lt_top ?_
        have hfin : 1 ≤ Module.finrank ℝ (ComplexModel d) := by
          rw [finrank_real_complexModel']; omega
        have hα : 2 * c < Module.finrank ℝ (ComplexModel d) := by
          rw [finrank_real_complexModel']; push_cast; linarith
        have hint := integrableOn_ball_of_norm_le_rpow (μ := volume) hfin hα (C := 1)
          (f := fun w : ComplexModel d => ‖w‖ ^ (-(2 * c))) (r := R)
          (Eventually.of_forall fun w => by
            rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg w) _), one_mul])
          (measurable_norm.pow_const _).aestronglyMeasurable
        exact hint.setLIntegral_lt_top

/-- The critical exponent is not integrable: `∫_{B(0,ε)} |w|^{-2d} = ∞` in `ℂ^d`, `d ≥ 1`. -/
theorem lintegral_ball_rpow_critical {d : ℕ} (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    ∫⁻ w in ball (0 : ComplexModel d) ε, ENNReal.ofReal (‖w‖ ^ (-(2 * (d : ℝ)))) = ⊤ := by
  by_contra hne
  have : Nontrivial (ComplexModel d) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_real_complexModel']; omega)
  have hint : IntegrableOn (fun w : ComplexModel d => ‖w‖ ^ (-(2 * (d : ℝ))))
      (ball (0 : ComplexModel d) ε) := by
    refine ⟨(measurable_norm.pow_const _).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun w =>
      Real.rpow_nonneg (norm_nonneg w) _)]
    exact lt_top_iff_ne_top.mpr hne
  have h1 := (integrableOn_fun_norm_addHaar (μ := volume)
    (f := fun y : ℝ => y ^ (-(2 * (d : ℝ)))) (r := ε)).mp hint
  rw [finrank_real_complexModel'] at h1
  have h2 : IntegrableOn (fun y : ℝ => y ^ (-1 : ℝ)) (Ioo 0 ε) := by
    refine h1.congr_fun (fun y hy => ?_) measurableSet_Ioo
    simp only [smul_eq_mul]
    rw [← Real.rpow_natCast, ← Real.rpow_add hy.1]
    congr 1
    rw [Nat.cast_sub (by omega)]
    push_cast; ring
  have := (intervalIntegral.integrableOn_Ioo_rpow_iff hε).mp h2
  linarith

/-- **Vanishing from the critical weight.**  A holomorphic `h` near a point `z₀` of the plane
`{w = 0}` with `∫ |h|² |w|^{-2(n - m)} < ∞` vanishes at `z₀`. -/
theorem eq_zero_of_lintegral_normalWeight {n m : ℕ} (hmn : m < n) {O : Set (ComplexModel n)}
    (hO : IsOpen O) {h : ComplexModel n → ℂ} (hh : ContinuousOn h O) {z₀ : ComplexModel n}
    (hz₀O : z₀ ∈ O) (hz₀ : z₀ ∈ complexCoordinatePlane n m)
    (hint : ∫⁻ z in O, ENNReal.ofReal (‖h z‖ ^ 2) *
      ENNReal.ofReal (normalWeight n m z ^ (-((n - m : ℕ) : ℝ))) ≠ ⊤) :
    h z₀ = 0 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn.le
  have hd : 1 ≤ d := by omega
  have hsub : m + d - m = d := by omega
  rw [hsub] at hint
  by_contra hne
  set e := prodModelEquiv m d with he
  set c : ℝ := ‖h z₀‖ ^ 2 / 4 with hc
  have hcpos : 0 < c := by rw [hc]; have := norm_pos_iff.mpr hne; positivity
  -- a ball on which `|h|² ≥ c`
  have hev : ∀ᶠ z in 𝓝 z₀, z ∈ O ∧ c ≤ ‖h z‖ ^ 2 := by
    have hcont : ContinuousAt (fun z => ‖h z‖ ^ 2) z₀ :=
      ((hh.continuousAt (hO.mem_nhds hz₀O)).norm).pow 2
    have hlt : c < ‖h z₀‖ ^ 2 := by rw [hc]; linarith
    filter_upwards [hO.mem_nhds hz₀O, hcont.eventually (Ioi_mem_nhds hlt)] with z h1 h2
    exact ⟨h1, h2.le⟩
  obtain ⟨ε₂, hε₂, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  set ε := ε₂ / 2 with hε
  have hε0 : 0 < ε := by positivity
  -- the normal part of `z₀` vanishes
  have hz₀2 : (e.symm z₀).2 = 0 := by
    ext j
    show z₀ (Fin.natAdd m j) = 0
    exact hz₀ _ (by simp)
  have hprod : e '' (ball (e.symm z₀).1 ε ×ˢ ball (0 : ComplexModel d) ε) ⊆ ball z₀ ε₂ := by
    rintro _ ⟨q, ⟨hq1, hq2⟩, rfl⟩
    rw [mem_ball, dist_eq_norm]
    have h1 := norm_sq_prodModelEquiv_symm m d (e q - z₀)
    have hq : e.symm (e q - z₀) = (q.1 - (e.symm z₀).1, q.2) := by
      rw [map_sub, e.symm_apply_apply]
      ext <;> simp [hz₀2]
    rw [hq] at h1
    simp only at h1
    rw [mem_ball, dist_eq_norm] at hq1
    rw [mem_ball_zero_iff] at hq2
    have : ‖e q - z₀‖ ^ 2 < ε₂ ^ 2 := by
      rw [← h1]
      have : ε₂ ^ 2 = 4 * ε ^ 2 := by rw [hε]; ring
      nlinarith [norm_nonneg (q.1 - (e.symm z₀).1), norm_nonneg q.2]
    exact lt_of_pow_lt_pow_left₀ 2 hε₂.le this
  have hgm : Measurable fun w : ComplexModel d => ENNReal.ofReal (‖w‖ ^ (-(2 * (d : ℝ)))) :=
    ENNReal.measurable_ofReal.comp (measurable_norm.pow_const _)
  apply hint
  refine top_le_iff.mp ?_
  calc (⊤ : ℝ≥0∞) = ENNReal.ofReal c * (volume (ball (e.symm z₀).1 ε) *
        ∫⁻ w in ball (0 : ComplexModel d) ε, ENNReal.ofReal (‖w‖ ^ (-(2 * (d : ℝ))))) := by
        rw [lintegral_ball_rpow_critical hd hε0, ENNReal.mul_top (measure_ball_pos _ _ hε0).ne',
          ENNReal.mul_top (ENNReal.ofReal_pos.mpr hcpos).ne']
    _ = ENNReal.ofReal c * ∫⁻ z in e '' (ball (e.symm z₀).1 ε ×ˢ ball (0 : ComplexModel d) ε),
          ENNReal.ofReal (‖(e.symm z).2‖ ^ (-(2 * (d : ℝ)))) := by
        rw [lintegral_image_prod_ball m d _ ε _ hgm]
    _ = ∫⁻ z in e '' (ball (e.symm z₀).1 ε ×ˢ ball (0 : ComplexModel d) ε),
          ENNReal.ofReal c * ENNReal.ofReal (normalWeight (m + d) m z ^ (-(d : ℝ))) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun z => ?_
        rw [normalWeight_rpow_eq]
    _ ≤ ∫⁻ z in O, ENNReal.ofReal (‖h z‖ ^ 2) *
          ENNReal.ofReal (normalWeight (m + d) m z ^ (-(d : ℝ))) := by
        refine (setLIntegral_mono' ?_ fun z hz => ?_).trans (lintegral_mono_set ?_)
        · exact ((e.toHomeomorph.isOpenMap _ (isOpen_ball.prod isOpen_ball))).measurableSet
        · exact mul_le_mul' (ENNReal.ofReal_le_ofReal (hball z (hprod hz)).2) le_rfl
        · exact fun z hz => (hball z (hprod hz)).1

/-- **Lipschitz bound.**  A holomorphic `h` on an open `O` vanishing on `O ∩ {w = 0}` satisfies
`|h|² ≤ C |w|²` on every compact `K ⊆ O`. -/
theorem exists_sq_le_normalWeight {n m : ℕ} (_hmn : m ≤ n) {O : Set (ComplexModel n)}
    (hO : IsOpen O) {h : ComplexModel n → ℂ} (hh : DifferentiableOn ℂ h O)
    (hzero : ∀ z ∈ O, z ∈ complexCoordinatePlane n m → h z = 0) {K : Set (ComplexModel n)}
    (hK : IsCompact K) (hKO : K ⊆ O) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K, ‖h z‖ ^ 2 ≤ C * normalWeight n m z := by
  obtain ⟨ε, hε, hεO⟩ := hK.exists_cthickening_subset_open hO hKO
  have hK2 : IsCompact (Metric.cthickening ε K) := hK.cthickening
  have hC1 : ContDiffOn ℂ 1 h O := (contDiffOn_of_differentiableOn_complex hh hO).of_le (by simp)
  have hfd : ContinuousOn (fderiv ℂ h) O := hC1.continuousOn_fderiv_of_isOpen hO le_rfl
  obtain ⟨B, hB⟩ := hK2.exists_bound_of_continuousOn (hfd.mono hεO)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hh.continuousOn.mono hKO)
  set B' := max B 0
  set M' := max M 0
  refine ⟨max (B' ^ 2) (M' ^ 2 / ε ^ 2), le_max_of_le_left (by positivity), fun z hz => ?_⟩
  set π : ComplexModel n := coordinateInclusion n m (coordinateProjection n m z) with hπ
  have hdist : ‖z - π‖ ^ 2 = normalWeight n m z := by
    rw [EuclideanSpace.norm_sq_eq, normalWeight]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hπ, PiLp.sub_apply, coordinateInclusion_apply, coordinateProjection_apply]
    by_cases hi : m ≤ i.1
    · rw [if_pos hi, dif_neg (by omega), sub_zero]
    · rw [if_neg hi, dif_pos (by omega), dif_pos i.2]
      simp
  have hnw := normalWeight_nonneg n m z
  by_cases hclose : ‖z - π‖ < ε
  · -- mean value inequality on the segment from `π` to `z`
    have hseg : ball z ε ⊆ Metric.cthickening ε K := fun y hy =>
      Metric.mem_cthickening_of_dist_le y z ε K hz (mem_ball.mp hy).le
    have hπmem : π ∈ ball z ε := by rw [mem_ball, dist_eq_norm, norm_sub_rev]; exact hclose
    have hπplane : π ∈ complexCoordinatePlane n m := coordinateInclusion_mem_complexCoordinatePlane _
    have hhπ : h π = 0 := hzero π (hεO (hseg hπmem)) hπplane
    have hmv := (convex_ball z ε).norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℂ) (f := h) (C := B')
      (fun y hy => hh.differentiableAt (hO.mem_nhds (hεO (hseg hy))))
      (fun y hy => (hB y (hseg hy)).trans (le_max_left _ _)) hπmem (mem_ball_self hε)
    rw [hhπ, sub_zero] at hmv
    calc ‖h z‖ ^ 2 ≤ (B' * ‖z - π‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hmv 2
      _ = B' ^ 2 * normalWeight n m z := by rw [mul_pow, hdist]
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hnw
  · push Not at hclose
    have hε2 : ε ^ 2 ≤ normalWeight n m z := by
      rw [← hdist]; exact pow_le_pow_left₀ hε.le hclose 2
    have hMz : ‖h z‖ ≤ M' := (hM z hz).trans (le_max_left _ _)
    calc ‖h z‖ ^ 2 ≤ M' ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hMz 2
      _ = M' ^ 2 / ε ^ 2 * ε ^ 2 := by field_simp
      _ ≤ M' ^ 2 / ε ^ 2 * normalWeight n m z :=
          mul_le_mul_of_nonneg_left hε2 (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hnw

end SGPT.Trace.OTMargin
