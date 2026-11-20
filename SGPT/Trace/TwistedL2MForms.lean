import SGPT.Trace.TwistedL2MPieces

/-!
# The integrands of the twisted Bochner--Kodaira--Nakano argument are gauge forms

Blueprint `claude-tl2-main.tex` (`claude-tl2-main:pieces`).  For a twisted datum `T` on `ℂⁿ` with
volume density `ρ`, in a frame `e` with local weight `p = p_e` and twisted weight `p' = p - log a`:

* `Fθ`: `ϑ_{p'} u · conj(ϑ_{p'} w) e^{-p'}`;
* `FL`: `Levi(p')(u, w) e^{-p'}`;
* `FT`: `tr(A_u Ā_w) e^{-p'}`;
* `FA`: `(a+b) ϑ_p u · conj(ϑ_p w) e^{-p}` (the integrand of `‖T* τ‖²`);
* `FH`: `H(u, w) e^{-p}` for the sesquilinear twisted curvature
  `H(u,w) = a Levi(p)(u,w) - Levi(a)(u,w) - ∂a(u) conj(∂a(w))/b` (`Hs`);
* `FD`: `⟨∂̄G_e, w⟩ e^{-p}` (the data pairing).

All six are gauge forms (`IsGaugeForm`).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter MeasureTheory Bundle
open scoped Topology ContDiff ComplexConjugate Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.Pending.CauchyGreen SGPT.Foundations.Analysis.Pending.Hormander
open SGPT.Bergman.TensorDictionaryDraft
open HermitianHolomorphicLineBundle

variable {n : ℕ}

namespace TwistedDatum

variable (T : TwistedDatum n (ComplexModel n)) (ρ : ComplexModel n → ℝ)

/-- The twisted adjoint form. -/
def Fθ (e : AtlasFrame T.L) (u w : ComplexModel n → ComplexModel n) (z : ComplexModel n) : ℂ :=
  chartTheta (T.pT ρ e) u z * conj (chartTheta (T.pT ρ e) w z) * cweight (T.pT ρ e) z

/-- The twisted Levi form. -/
def FL (e : AtlasFrame T.L) (u w : ComplexModel n → ComplexModel n) (z : ComplexModel n) : ℂ :=
  leviS (T.pT ρ e) z (u z) (w z) * cweight (T.pT ρ e) z

/-- The twisted `tr(A Ā)` form. -/
def FT (e : AtlasFrame T.L) (u w : ComplexModel n → ComplexModel n) (z : ComplexModel n) : ℂ :=
  trS u w z * cweight (T.pT ρ e) z

/-- The form of `‖T* τ‖²`. -/
def FA (e : AtlasFrame T.L) (u w : ComplexModel n → ComplexModel n) (z : ComplexModel n) : ℂ :=
  ((T.a z + T.b z : ℝ) : ℂ) * chartTheta (T.pW ρ e) u z * conj (chartTheta (T.pW ρ e) w z) *
    cweight (T.pW ρ e) z

/-- `∂a(v) = ∑_j ∂_j a · v_j`. -/
def dA (z v : ComplexModel n) : ℂ := ∑ j, dDir (coordVec j) (fun y => (T.a y : ℂ)) z * v j

/-- The sesquilinear twisted curvature `H(v, w) = a Levi(p)(v,w) - Levi(a)(v,w) - ∂a(v) conj ∂a(w)/b`. -/
def Hs (e : AtlasFrame T.L) (z v w : ComplexModel n) : ℂ :=
  (T.a z : ℂ) * leviS (T.pW ρ e) z v w - leviS T.a z v w - T.dA z v * conj (T.dA z w) / (T.b z : ℂ)

/-- The twisted curvature form. -/
def FH (e : AtlasFrame T.L) (u w : ComplexModel n → ComplexModel n) (z : ComplexModel n) : ℂ :=
  T.Hs ρ e z (u z) (w z) * cweight (T.pW ρ e) z

/-- The data form `⟨∂̄G_e, w⟩ e^{-p}`. -/
def FD (e : AtlasFrame T.L) (_u w : ComplexModel n → ComplexModel n) (z : ComplexModel n) : ℂ :=
  dbarPairing (chartCoeff T.L chart0 e T.G) z (w z) * cweight (T.pW ρ e) z

/-! ### Elementary properties -/

theorem dA_smul (z v : ComplexModel n) (c : ℂ) : T.dA z (c • v) = c * T.dA z v := by
  simp only [dA, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem dA_sum (z : ComplexModel n) {ι : Type*} (s : Finset ι) (w : ι → ComplexModel n) :
    T.dA z (∑ i ∈ s, w i) = ∑ i ∈ s, T.dA z (w i) := by
  simp only [dA, euclid_sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem dA_zero (z : ComplexModel n) : T.dA z 0 = 0 := by simp [dA]

theorem Hs_zero (e : AtlasFrame T.L) (z v : ComplexModel n) : T.Hs ρ e z v 0 = 0 := by
  simp [Hs, leviS_zero_right, dA_zero]

theorem Hs_sum (e : AtlasFrame T.L) (z v : ComplexModel n) {ι : Type*} (s : Finset ι)
    (w : ι → ComplexModel n) : T.Hs ρ e z v (∑ i ∈ s, w i) = ∑ i ∈ s, T.Hs ρ e z v (w i) := by
  simp only [Hs, leviS_finset_sum_right, dA_sum, map_sum, Finset.mul_sum, Finset.sum_div,
    ← Finset.sum_sub_distrib]

theorem Hs_smul (e : AtlasFrame T.L) (z v w : ComplexModel n) (c : ℂ) :
    T.Hs ρ e z (c • v) (c • w) = (c * conj c) * T.Hs ρ e z v w := by
  simp only [Hs, leviS_smul, dA_smul, map_mul]
  ring

variable {T ρ}

theorem pW_contDiffAt (hρ : IsChartDensity T.μ chart0 ρ) {e : AtlasFrame T.L}
    {z : ComplexModel n} (hz : z ∈ T.dom e) : ContDiffAt ℝ ∞ (T.pW ρ e) z :=
  (T.contDiffOn_pW hρ e).contDiffAt ((T.isOpen_dom e).mem_nhds hz)

theorem pT_contDiffAt (hρ : IsChartDensity T.μ chart0 ρ) {e : AtlasFrame T.L}
    {z : ComplexModel n} (hz : z ∈ T.dom e) : ContDiffAt ℝ ∞ (T.pT ρ e) z :=
  (T.contDiffOn_pT hρ e).contDiffAt ((T.isOpen_dom e).mem_nhds hz)

theorem two_le_infty : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top

/-! ### The six gauge forms -/

theorem isGaugeForm_theta (hρ : IsChartDensity T.μ chart0 ρ) : T.IsGaugeForm (T.Fθ ρ) where
  congr e u u' w w' z hu hw := by simp only [Fθ, chartTheta_congr hu, chartTheta_congr hw]
  zero e u w z hw := by simp [Fθ, chartTheta_eq_zero_of_eventuallyEq hw]
  add e u ι s w z _ _ hw := by
    simp only [Fθ, chartTheta_finset_sum s fun i hi => (hw i hi).differentiableAt (by simp),
      map_sum, Finset.mul_sum, Finset.sum_mul]
  gauge e e' u w z hz hz' hu hw := by
    have g := T.gaugeData_pT (ρ := ρ) e e'
    have hzS : z ∈ T.dom e ∩ T.dom e' := ⟨hz, hz'⟩
    have hp : DifferentiableAt ℝ (T.pT ρ e) z := (pT_contDiffAt hρ hz).differentiableAt (by simp)
    simp only [Fθ]
    rw [chartTheta_gauge g hzS hp (hu.differentiableAt (by simp)),
      chartTheta_gauge g hzS hp (hw.differentiableAt (by simp)), ← g.cweight_mul hzS, map_mul]
    ring
  contOn e u w hu hw := by
    have hO := T.isOpen_dom e
    exact ((continuousOn_chartTheta' hO (T.contDiffOn_pT hρ e) hu).mul
      (Complex.continuous_conj.comp_continuousOn
        (continuousOn_chartTheta' hO (T.contDiffOn_pT hρ e) hw))).mul
      (continuousOn_cweight (T.contDiffOn_pT hρ e))

theorem isGaugeForm_levi (hρ : IsChartDensity T.μ chart0 ρ) : T.IsGaugeForm (T.FL ρ) where
  congr e u u' w w' z hu hw := by simp only [FL, hu.self_of_nhds, hw.self_of_nhds]
  zero e u w z hw := by simp [FL, hw.self_of_nhds, leviS_zero_right]
  add e u ι s w z _ _ _ := by
    simp only [FL]
    rw [leviS_finset_sum_right, Finset.sum_mul]
  gauge e e' u w z hz hz' _ _ := by
    have g := T.gaugeData_pT (ρ := ρ) e e'
    have hzS : z ∈ T.dom e ∩ T.dom e' := ⟨hz, hz'⟩
    simp only [FL]
    rw [leviS_gauge g hzS ((pT_contDiffAt hρ hz).of_le two_le_infty), leviS_smul,
      ← g.cweight_mul hzS]
    ring
  contOn e u w hu hw :=
    (continuousOn_leviS (T.isOpen_dom e) (T.contDiffOn_pT hρ e) hu.continuousOn
      hw.continuousOn).mul (continuousOn_cweight (T.contDiffOn_pT hρ e))

theorem isGaugeForm_tr (hρ : IsChartDensity T.μ chart0 ρ) : T.IsGaugeForm (T.FT ρ) where
  congr e u u' w w' z hu hw := by simp only [FT, trS_congr hu hw]
  zero e u w z hw := by simp [FT, trS_eq_zero_of_right hw]
  add e u ι s w z _ _ hw := by
    simp only [FT]
    rw [trS_finset_sum_right u s fun i hi => (hw i hi).differentiableAt (by simp), Finset.sum_mul]
  gauge e e' u w z hz hz' hu hw := by
    have g := T.gaugeData_pT (ρ := ρ) e e'
    have hzS : z ∈ T.dom e ∩ T.dom e' := ⟨hz, hz'⟩
    simp only [FT]
    rw [trS_gauge (g.differentiableAt hzS) (hu.differentiableAt (by simp))
      (hw.differentiableAt (by simp)), ← g.cweight_mul hzS]
    ring
  contOn e u w hu hw :=
    (continuousOn_trS (T.isOpen_dom e) hu hw).mul (continuousOn_cweight (T.contDiffOn_pT hρ e))

theorem continuousOn_ab_dom (e : AtlasFrame T.L) :
    ContinuousOn (fun z => ((T.a z + T.b z : ℝ) : ℂ)) (T.dom e) := by
  have ha := (T.contDiffOn_U T.a_smooth).continuousOn
  have hb := (T.contDiffOn_U T.b_smooth).continuousOn
  exact Complex.continuous_ofReal.comp_continuousOn ((ha.add hb).mono fun z hz =>
    ((T.mem_dom).mp hz).2)

theorem isGaugeForm_tstar (hρ : IsChartDensity T.μ chart0 ρ) : T.IsGaugeForm (T.FA ρ) where
  congr e u u' w w' z hu hw := by simp only [FA, chartTheta_congr hu, chartTheta_congr hw]
  zero e u w z hw := by simp [FA, chartTheta_eq_zero_of_eventuallyEq hw]
  add e u ι s w z _ _ hw := by
    simp only [FA, chartTheta_finset_sum s fun i hi => (hw i hi).differentiableAt (by simp),
      map_sum, Finset.mul_sum, Finset.sum_mul]
  gauge e e' u w z hz hz' hu hw := by
    have g := T.gaugeData_pW (ρ := ρ) e e'
    have hzS : z ∈ T.dom e ∩ T.dom e' := ⟨hz, hz'⟩
    have hp : DifferentiableAt ℝ (T.pW ρ e) z := (pW_contDiffAt hρ hz).differentiableAt (by simp)
    simp only [FA]
    rw [chartTheta_gauge g hzS hp (hu.differentiableAt (by simp)),
      chartTheta_gauge g hzS hp (hw.differentiableAt (by simp)), ← g.cweight_mul hzS, map_mul]
    ring
  contOn e u w hu hw := by
    have hO := T.isOpen_dom e
    exact (((continuousOn_ab_dom e).mul (continuousOn_chartTheta' hO (T.contDiffOn_pW hρ e) hu)).mul
      (Complex.continuous_conj.comp_continuousOn
        (continuousOn_chartTheta' hO (T.contDiffOn_pW hρ e) hw))).mul
      (continuousOn_cweight (T.contDiffOn_pW hρ e))

theorem continuousOn_dA (e : AtlasFrame T.L) {w : ComplexModel n → ComplexModel n}
    (hw : ContinuousOn w (T.dom e)) : ContinuousOn (fun z => T.dA z (w z)) (T.dom e) := by
  have ha : ContDiffOn ℝ ∞ T.a (T.dom e) := (T.contDiffOn_U T.a_smooth).mono fun z hz =>
    ((T.mem_dom).mp hz).2
  unfold dA
  refine continuousOn_finsetSum _ fun j _ => ?_
  exact (contDiffOn_dDir (T.isOpen_dom e) (contDiffOn_ofReal' ha) _).continuousOn.mul
    ((EuclideanSpace.proj j : ComplexModel n →L[ℂ] ℂ).continuous.comp_continuousOn hw)

theorem isGaugeForm_curv (hρ : IsChartDensity T.μ chart0 ρ) : T.IsGaugeForm (T.FH ρ) where
  congr e u u' w w' z hu hw := by simp only [FH, hu.self_of_nhds, hw.self_of_nhds]
  zero e u w z hw := by simp [FH, hw.self_of_nhds, Hs_zero]
  add e u ι s w z _ _ _ := by
    simp only [FH]
    rw [Hs_sum, Finset.sum_mul]
  gauge e e' u w z hz hz' _ _ := by
    have g := T.gaugeData_pW (ρ := ρ) e e'
    have hzS : z ∈ T.dom e ∩ T.dom e' := ⟨hz, hz'⟩
    simp only [FH]
    have hH : T.Hs ρ e' z = T.Hs ρ e z := by
      funext v w'
      simp only [Hs, leviS_gauge g hzS ((pW_contDiffAt hρ hz).of_le two_le_infty)]
    rw [hH, Hs_smul, ← g.cweight_mul hzS]
    ring
  contOn e u w hu hw := by
    have hO := T.isOpen_dom e
    have ha : ContDiffOn ℝ ∞ T.a (T.dom e) := (T.contDiffOn_U T.a_smooth).mono fun z hz =>
      ((T.mem_dom).mp hz).2
    have hb : ContinuousOn (fun z => (T.b z : ℂ)) (T.dom e) :=
      Complex.continuous_ofReal.comp_continuousOn
        ((T.contDiffOn_U T.b_smooth).continuousOn.mono fun z hz => ((T.mem_dom).mp hz).2)
    have hb0 : ∀ z ∈ T.dom e, (T.b z : ℂ) ≠ 0 := fun z hz => by
      exact_mod_cast (T.b_pos ((T.mem_dom).mp hz).2).ne'
    unfold FH Hs
    refine ContinuousOn.mul ?_ (continuousOn_cweight (T.contDiffOn_pW hρ e))
    refine ((((Complex.continuous_ofReal.comp_continuousOn ha.continuousOn).mul
      (continuousOn_leviS hO (T.contDiffOn_pW hρ e) hu.continuousOn hw.continuousOn)).sub
      (continuousOn_leviS hO ha hu.continuousOn hw.continuousOn)).sub ?_)
    exact ((continuousOn_dA e hu.continuousOn).mul (Complex.continuous_conj.comp_continuousOn
      (continuousOn_dA e hw.continuousOn))).div hb hb0

theorem chartCoeff_eventuallyEq (e e' : AtlasFrame T.L) {z : ComplexModel n}
    (hz : z ∈ e.val.baseSet ∩ e'.val.baseSet) :
    chartCoeff T.L chart0 e' T.G =ᶠ[𝓝 z]
      fun y => frameTrans T.L e e' y * chartCoeff T.L chart0 e T.G y := by
  filter_upwards [(e.val.open_baseSet.inter e'.val.open_baseSet).mem_nhds hz] with y hy
  exact frameCoeff_eq_frameTrans_mul e e' T.G hy

theorem contDiffOn_G (e : AtlasFrame T.L) :
    ContDiffOn ℝ ∞ (chartCoeff T.L chart0 e T.G) (T.dom e) := T.G_smooth chart0 e

theorem isGaugeForm_data (hρ : IsChartDensity T.μ chart0 ρ) : T.IsGaugeForm (T.FD ρ) where
  congr e u u' w w' z _ hw := by simp only [FD, hw.self_of_nhds]
  zero e u w z hw := by simp [FD, hw.self_of_nhds, dbarPairing_zero]
  add e u ι s w z _ _ _ := by
    simp only [FD]
    rw [dbarPairing_finset_sum, Finset.sum_mul]
  gauge e e' u w z hz hz' _ _ := by
    have g := T.gaugeData_pW (ρ := ρ) e e'
    have hzS : z ∈ T.dom e ∩ T.dom e' := ⟨hz, hz'⟩
    have hzb : z ∈ e.val.baseSet ∩ e'.val.baseSet := ⟨((T.mem_dom).mp hz).1, ((T.mem_dom).mp hz').1⟩
    have hG : DifferentiableAt ℝ (chartCoeff T.L chart0 e T.G) z :=
      ((T.contDiffOn_G e).contDiffAt ((T.isOpen_dom e).mem_nhds hz)).differentiableAt (by simp)
    have hpair : ∀ v, dbarPairing (chartCoeff T.L chart0 e' T.G) z v =
        dbarPairing (fun y => frameTrans T.L e e' y * chartCoeff T.L chart0 e T.G y) z v := by
      intro v
      simp only [dbarPairing, dbarDir_congr_of_eventuallyEq (T.chartCoeff_eventuallyEq e e' hzb)]
    simp only [FD]
    rw [hpair, dbarPairing_gauge (g.differentiableAt hzS) hG, ← g.cweight_mul hzS]
    ring
  contOn e u w _ hw := by
    have hO := T.isOpen_dom e
    unfold FD dbarPairing
    refine ContinuousOn.mul (continuousOn_finsetSum _ fun j _ => ?_)
      (continuousOn_cweight (T.contDiffOn_pW hρ e))
    exact (Complex.continuous_conj.comp_continuousOn
      ((EuclideanSpace.proj j : ComplexModel n →L[ℂ] ℂ).continuous.comp_continuousOn
        hw.continuousOn)).mul (contDiffOn_dbarDir hO (T.contDiffOn_G e) _).continuousOn

end TwistedDatum

end SGPT.Trace.TwistedL2
