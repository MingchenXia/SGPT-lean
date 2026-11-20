import SGPT.PSH.SiuGenPole
import SGPT.Okounkov.TranscendentalL2Weight

/-!
# Integrals in the product charts of `X × Δ` and sections of `p₁^*E ⊗ 𝓘(cΦ)`

Blueprint `claude-siu-gen.tex`, nodes `claude-siu-gen:chart-integrals`,
`claude-siu-gen:l2-sections`.

* `setLIntegral_pChart_eq`, `setLIntegral_pChart_le`: in a product chart `w = (z, t)` of `X × Δ`
  the measure `μ ⊗ dλ` is `ρ(z) dz dt`; the comparison `∫_B f(w⁻¹) ρ ≤ ∫_{w⁻¹ B} f d(μ ⊗ λ)` holds
  for every `f` (no measurability needed).
* the bookkeeping of the weights `e^{-(mΦ + Ψ)}` (`mw_le_thetaGen_of_le`, `thetaGen_le_mw_of_le`,
  `mw_mul_le_thetaGen`).
* `mem_multiplierIdeal_of_chartBall`: a holomorphic section `S` of `p₁^*E` with
  `∫_B |S|² e^{-cΦ} < ∞` on a ball `B` around `q` in the chart at `q` has coefficients in `𝓘(cΦ)_q`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.PSH.SiuL2

open Set Filter Metric MeasureTheory Bundle
open scoped Topology ENNReal ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open scoped ProductComplexManifold
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
  SGPT.Bergman.CompactHolomorphicSectionsDraft
open HermitianHolomorphicLineBundle
open SGPT.PSH.GlobalL2 SGPT.NAPotential.NAGaga

/-! ### Weights -/

theorem mw_one_ne_zero {x : EReal} (hx : x ≠ ⊤) : multiplierWeight 1 x ≠ 0 := by
  induction x using EReal.rec with
  | bot => rw [multiplierWeight_bot one_pos]; exact ENNReal.top_ne_zero
  | coe r => rw [multiplierWeight_coe]; exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  | top => exact absurd rfl hx

theorem mw_one_add {x y : EReal} (hx : x ≠ ⊤) (hy : y ≠ ⊤) :
    multiplierWeight 1 (x + y) = multiplierWeight 1 x * multiplierWeight 1 y := by
  induction y using EReal.rec with
  | bot =>
      rw [EReal.add_bot, multiplierWeight_bot one_pos,
        ENNReal.mul_top (mw_one_ne_zero hx)]
  | coe r =>
      rw [multiplierWeight_one_add_coe_real hx r, multiplierWeight_coe, one_mul]
  | top => exact absurd rfl hy

theorem mw_eq_one_mul (c : ℝ) (a : EReal) :
    multiplierWeight c a = multiplierWeight 1 ((c : EReal) * a) := by
  simp only [multiplierWeight, EReal.coe_one, one_mul]

theorem mw_le_thetaGen_of_le {m : ℕ} (hm : 0 < m) {Φq Ψq : EReal} (hΦ : Φq ≠ ⊤) (hΨ : Ψq ≠ ⊤)
    {c : ℝ} (h : Ψq ≤ (c : EReal)) :
    multiplierWeight (m : ℝ) Φq ≤
      ENNReal.ofReal (Real.exp c) * multiplierWeight 1 (((m : ℝ) : EReal) * Φq + Ψq) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  rw [mw_one_add (SiuCover.mul_ne_top_of_pos hm' hΦ) hΨ, ← mw_eq_one_mul]
  have h1 : ENNReal.ofReal (Real.exp (-c)) ≤ multiplierWeight 1 Ψq := by
    rw [← one_mul c, ← multiplierWeight_coe]
    exact multiplierWeight_antitone zero_le_one h
  calc multiplierWeight (m : ℝ) Φq
      = ENNReal.ofReal (Real.exp c) * (multiplierWeight (m : ℝ) Φq *
          ENNReal.ofReal (Real.exp (-c))) := by
        rw [mul_comm (multiplierWeight _ _), ← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
          ← Real.exp_add, add_neg_cancel, Real.exp_zero, ENNReal.ofReal_one, one_mul]
    _ ≤ _ := by gcongr

theorem thetaGen_le_mw_of_le {m : ℕ} (hm : 0 < m) {Φq Ψq : EReal} (hΦ : Φq ≠ ⊤) (hΨ : Ψq ≠ ⊤)
    {c : ℝ} (h : (c : EReal) ≤ Ψq) :
    multiplierWeight 1 (((m : ℝ) : EReal) * Φq + Ψq) ≤
      ENNReal.ofReal (Real.exp (-c)) * multiplierWeight (m : ℝ) Φq := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  rw [mw_one_add (SiuCover.mul_ne_top_of_pos hm' hΦ) hΨ, ← mw_eq_one_mul, mul_comm]
  have h1 : multiplierWeight 1 Ψq ≤ ENNReal.ofReal (Real.exp (-c)) := by
    rw [← one_mul c, ← multiplierWeight_coe]
    exact multiplierWeight_antitone zero_le_one h
  gcongr

theorem mw_mul_le_thetaGen {m : ℕ} (hm : 0 < m) {Φq Ψq : EReal} (hΦ : Φq ≠ ⊤) (hΨ : Ψq ≠ ⊤)
    {N : ℝ} {ℓ : EReal} (h : Ψq ≤ (N : EReal) * ℓ) :
    multiplierWeight (m : ℝ) Φq * multiplierWeight N ℓ ≤
      multiplierWeight 1 (((m : ℝ) : EReal) * Φq + Ψq) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  rw [mw_one_add (SiuCover.mul_ne_top_of_pos hm' hΦ) hΨ, ← mw_eq_one_mul, mw_eq_one_mul N]
  gcongr
  exact multiplierWeight_antitone zero_le_one h

theorem mw_one_mul_add_coe {m : ℝ} (hm : 0 < m) (ρ : ℝ) {a : EReal} (ha : a ≠ ⊤) :
    multiplierWeight 1 ((m : EReal) * ((ρ : EReal) + a)) =
      ENNReal.ofReal (Real.exp (-(m * ρ))) * multiplierWeight m a := by
  induction a using EReal.rec with
  | bot =>
      rw [EReal.add_bot, EReal.coe_mul_bot_of_pos hm, multiplierWeight_bot one_pos,
        multiplierWeight_bot hm, ENNReal.mul_top (by positivity)]
  | coe r =>
      rw [← EReal.coe_add, ← EReal.coe_mul, multiplierWeight_coe, multiplierWeight_coe,
        ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 2
      ring
  | top => exact absurd rfl ha

/-! ### Upper semicontinuity in charts -/

theorem upperSemicontinuousOn_chartFunction_target {N : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel N) M] [IsComplexManifold N M] {θ : SmoothRealForm N M 2}
    {u : M → EReal} (hu : ThetaPlurisubharmonic θ u) (e : ComplexChart N M) :
    UpperSemicontinuousOn (chartFunction u e) e.val.target := by
  have h := SGPT.Okounkov.TranscendentalL2.upperSemicontinuousOn_chartFunction_of_thetaPlurisubharmonicOn
    (Ω := univ) (fun e z hz _ => hu e z hz) e
  exact h.mono fun z hz => ⟨hz, mem_univ _⟩

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X]

/-! ### Integrals in the product charts -/

section Chart

variable {μ : Measure X} [SFinite μ] (q' : X × unitDisc) {ρ : ComplexModel n → ℝ}
  (hρc : ContinuousOn ρ (complexChartAt (n := n) q'.1).val.target)
  (hmap : Measure.map (complexChartAt (n := n) q'.1).val
      (μ.restrict (complexChartAt (n := n) q'.1).val.source) =
    (volume.restrict (complexChartAt (n := n) q'.1).val.target).withDensity
      (fun z => ENNReal.ofReal (ρ z)))
include hρc hmap

theorem continuousOn_dens_pChart :
    ContinuousOn (fun w : ComplexModel (n + 1) => ρ (projX n w)) (pChart (n := n) q').val.target :=
  hρc.comp (projX n).continuous.continuousOn fun w hw => by
    rw [pChart_target] at hw; exact hw.1

/-- `μ ⊗ dλ = ρ(z) dz dt` in the product chart. -/
theorem setLIntegral_pChart_eq {B : Set (ComplexModel (n + 1))} (hB : IsOpen B)
    (hBt : B ⊆ (pChart (n := n) q').val.target) {f : X × unitDisc → ℝ≥0∞}
    (hf : AEMeasurable (fun z => f ((pChart (n := n) q').val.symm z)) (volume.restrict B)) :
    ∫⁻ x in (pChart (n := n) q').val.source ∩ (pChart (n := n) q').val ⁻¹' B, f x ∂(prodMeasure μ) =
      ∫⁻ z in B, f ((pChart (n := n) q').val.symm z) * ENNReal.ofReal (ρ (projX n z)) :=
  setLIntegral_chart_ball (pChart (n := n) q') (ρ := fun w => ρ (projX n w))
    (continuousOn_dens_pChart q' hρc hmap) (map_pChart q' hρc hmap) hB hBt hf

/-- **Chart integrals are bounded by the integral on `X × Δ`** (no measurability needed). -/
theorem setLIntegral_pChart_le {B : Set (ComplexModel (n + 1))} (hB : IsOpen B)
    (hBt : B ⊆ (pChart (n := n) q').val.target) (f : X × unitDisc → ℝ≥0∞) :
    ∫⁻ z in B, f ((pChart (n := n) q').val.symm z) * ENNReal.ofReal (ρ (projX n z)) ≤
      ∫⁻ x in (pChart (n := n) q').val.source ∩ (pChart (n := n) q').val ⁻¹' B, f x
        ∂(prodMeasure μ) := by
  set C := (pChart (n := n) q').val with hC
  set ν := (prodMeasure μ).restrict C.source with hν
  have hmapP := map_pChart q' hρc hmap
  set dens : ComplexModel (n + 1) → ℝ≥0∞ := fun w => ENNReal.ofReal (ρ (projX n w)) with hdens
  set h : ComplexModel (n + 1) → ℝ≥0∞ := B.indicator (fun z => f (C.symm z)) with hh
  have hdensm : AEMeasurable dens (volume.restrict C.target) :=
    (ENNReal.continuous_ofReal.comp_continuousOn (continuousOn_dens_pChart q' hρc hmap)).aemeasurable
      C.open_target.measurableSet
  have hSo : IsOpen (C.source ∩ C ⁻¹' B) := C.isOpen_inter_preimage hB
  calc ∫⁻ z in B, f (C.symm z) * dens z
      = ∫⁻ z in C.target, dens z * h z := by
        have e1 : (fun z => dens z * h z) = B.indicator (fun z => dens z * f (C.symm z)) := by
          funext z
          by_cases hz : z ∈ B
          · simp [hh, indicator_of_mem hz]
          · simp [hh, indicator_of_notMem hz]
        rw [e1, lintegral_indicator hB.measurableSet, Measure.restrict_restrict hB.measurableSet,
          inter_eq_left.mpr hBt]
        exact setLIntegral_congr_fun hB.measurableSet fun z _ => mul_comm _ _
    _ = ∫⁻ z, h z ∂((volume.restrict C.target).withDensity dens) :=
        (lintegral_withDensity_eq_lintegral_mul_non_measurable₀ _ hdensm
          (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) h).symm
    _ = ∫⁻ z, h z ∂(Measure.map C ν) := by
        congr 1
        exact hmapP.symm
    _ ≤ ∫⁻ x, h (C x) ∂ν := lintegral_map_le h C
    _ = ∫⁻ x in C.source, (C.source ∩ C ⁻¹' B).indicator f x ∂(prodMeasure μ) := by
        refine setLIntegral_congr_fun C.open_source.measurableSet fun x hx => ?_
        by_cases hxB : C x ∈ B
        · have hmem : x ∈ C.source ∩ C ⁻¹' B := ⟨hx, hxB⟩
          rw [hh, indicator_of_mem hxB, indicator_of_mem hmem, C.left_inv hx]
        · have hmem : x ∉ C.source ∩ C ⁻¹' B := fun h' => hxB h'.2
          rw [hh, indicator_of_notMem hxB, indicator_of_notMem hmem]
    _ = ∫⁻ x in C.source ∩ C ⁻¹' B, f x ∂(prodMeasure μ) := by
        rw [lintegral_indicator hSo.measurableSet, Measure.restrict_restrict hSo.measurableSet,
          inter_eq_left.mpr inter_subset_left]

end Chart

/-! ### Global `L²` sections lie in the multiplier ideal -/

/-- **Sections of `p₁^*E ⊗ 𝓘(cΦ)`** (`claude-siu-gen:l2-sections`).  Let `S` be a holomorphic
section of `p₁^*E` on `X × Δ`, `Φ` quasi-psh, `c > 0`, `e'` a frame of `E` at `q.1`.  If
`∫_B |S|² e^{-cΦ} < ∞` (read in the chart at `q`) on a ball `B` around the image of `q` whose closure
lies in the chart and over the base set of `e'`, the `e'`-coefficient of `S` lies in `𝓘(cΦ)_q`. -/
theorem mem_multiplierIdeal_of_chartBall {E : HermitianHolomorphicLineBundle.{0, 0} n X}
    {S : (q : X × unitDisc) → E.Fiber q.1} (hS : IsHolomorphicProdSectionOn E S univ)
    {θ' : SmoothRealForm (n + 1) (X × unitDisc) 2} {Φ : X × unitDisc → EReal}
    (hΦ : ThetaPlurisubharmonic θ' Φ) {c : ℝ} (hc : 0 < c) (e' : AtlasFrame E)
    {q : X × unitDisc} (hq : q.1 ∈ e'.val.baseSet) {r : ℝ}
    (hcl : closedBall ((complexChartAt (n := n + 1) q).val q) r ⊆
      (complexChartAt (n := n + 1) q).val.target ∩
        (complexChartAt (n := n + 1) q).val.symm ⁻¹' (Prod.fst ⁻¹' e'.val.baseSet))
    (hr : 0 < r)
    (hint : ∫⁻ z in ball ((complexChartAt (n := n + 1) q).val q) r,
      ENNReal.ofReal (‖S ((complexChartAt (n := n + 1) q).val.symm z)‖ ^ 2) *
        multiplierWeight c (Φ ((complexChartAt (n := n + 1) q).val.symm z)) < ⊤) :
    (multiplierIdeal (n := n + 1) c Φ).mem q
      (fun q' => e'.val.continuousLinearMapAt ℂ q'.1 (S q')) := by
  have := e'.property
  set d := complexChartAt (n := n + 1) q with hd
  set w₀ := d.val q with hw₀
  set B := ball w₀ r with hB
  have hBcl : B ⊆ closedBall w₀ r := ball_subset_closedBall
  refine ⟨hS q (mem_univ _) e' hq, ?_⟩
  -- the frame norm is bounded below on the closed ball
  have hKc : IsCompact (closedBall w₀ r) := isCompact_closedBall w₀ r
  have hne : (closedBall w₀ r).Nonempty := ⟨w₀, mem_closedBall_self hr.le⟩
  have hfc : ContinuousOn (fun z => ‖e'.val.symm (d.val.symm z).1 1‖) (closedBall w₀ r) :=
    (frameNorm_continuousOn E.Fiber e'.val).comp
      (continuous_fst.comp_continuousOn (d.val.continuousOn_symm.mono fun z hz => (hcl hz).1))
      fun z hz => (hcl hz).2
  obtain ⟨z₂, hz₂, hmin₂⟩ := hKc.exists_isMinOn hne hfc
  set m₀ := ‖e'.val.symm (d.val.symm z₂).1 1‖ with hm₀
  have hm₀ : 0 < m₀ := frameNorm_pos E.Fiber e'.val (hcl hz₂).2
  -- the coefficient in the chart
  set f : ComplexModel (n + 1) → ℂ := fun z =>
    e'.val.continuousLinearMapAt ℂ (d.val.symm z).1 (S (d.val.symm z)) with hf
  have hfd : DifferentiableOn ℂ f B := fun z hz =>
    (differentiableAt_comp_symm_of_holomorphicAt d (hcl (hBcl hz)).1
      (hS _ (mem_univ _) e' (hcl (hBcl hz)).2)).differentiableWithinAt
  have hnorm : ∀ z ∈ B, ‖S (d.val.symm z)‖ = ‖f z‖ * ‖e'.val.symm (d.val.symm z).1 1‖ :=
    fun z hz => norm_eq_coef_mul_norm_frame e'.val (hcl (hBcl hz)).2 _
  have husc : UpperSemicontinuousOn (chartFunction Φ d) B :=
    (upperSemicontinuousOn_chartFunction_target hΦ d).mono fun z hz => (hcl (hBcl hz)).1
  have hwm : AEMeasurable (fun z => multiplierWeight c (chartFunction Φ d z)) (volume.restrict B) :=
    DemaillyApproximation.aemeasurable_multiplierWeight_restrict isOpen_ball husc hc.ne'
  have hfm : AEMeasurable (fun z => ENNReal.ofReal (‖f z‖ ^ 2)) (volume.restrict B) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((hfd.continuousOn.aestronglyMeasurable measurableSet_ball).norm.aemeasurable.pow_const 2)
  refine ⟨hc, B, isOpen_ball, mem_ball_self hr, hfd, hfm.mul hwm, ?_⟩
  calc ∫⁻ z in B, multiplierDensity (chartFunction Φ d) c f z
      ≤ ∫⁻ z in B, ENNReal.ofReal ((m₀ ^ 2)⁻¹) *
          (ENNReal.ofReal (‖S (d.val.symm z)‖ ^ 2) * multiplierWeight c (Φ (d.val.symm z))) := by
        refine setLIntegral_mono' measurableSet_ball fun z hz => ?_
        have hmz : m₀ ≤ ‖e'.val.symm (d.val.symm z).1 1‖ := hmin₂ (hBcl hz)
        show ENNReal.ofReal (‖f z‖ ^ 2) * multiplierWeight c (Φ (d.val.symm z)) ≤ _
        rw [hnorm z hz, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le
        rw [mul_pow, inv_mul_eq_div, le_div_iff₀ (by positivity)]
        have h1 : m₀ ^ 2 ≤ ‖e'.val.symm (d.val.symm z).1 1‖ ^ 2 := pow_le_pow_left₀ hm₀.le hmz 2
        nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg ‖f z‖)]
    _ = ENNReal.ofReal ((m₀ ^ 2)⁻¹) * ∫⁻ z in B, ENNReal.ofReal (‖S (d.val.symm z)‖ ^ 2) *
          multiplierWeight c (Φ (d.val.symm z)) := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hint

end SGPT.PSH.SiuL2
