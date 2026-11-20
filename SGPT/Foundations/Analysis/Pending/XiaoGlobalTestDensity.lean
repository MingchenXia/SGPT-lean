import SGPT.Foundations.Analysis.Pending.XiaoTestDensityEstimate
import SGPT.Foundations.Analysis.Pending.NefMixedMass

set_option autoImplicit false

/-!
# Xiao's genuine intrinsic test-density estimate on a compact Kähler manifold

The intrinsic densities are existing `IntegrationCurrent.topRatio` functions
of actual smooth forms. Their continuity, measurability and integrability are
produced internally, as is the actual normalized probability measure. The
mixed mass is the existing `NefMixedMass.slotIntegral` of the actual forms.
-/

open MeasureTheory

namespace SGPT.Foundations.Analysis.Pending.XiaoGlobalTestDensity

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses StronglyPositiveForms
  ProductTestForms IntegrationCurrent TopDegreeDensity MixedMassClassInvariance

variable {m : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]

private theorem semipositive_coefficient {A : ClosedRealOneOneForm (m + 1) X}
    (hA : A.val.IsKahler) (e : ComplexChart (m + 1) X) {z : ComplexModel (m + 1)}
    (hz : z ∈ e.val.target) : IsSemipositiveOneOne (A.val.coeff e z) := by
  refine ⟨(hA.1 e z hz).1, fun v => ?_⟩
  rcases eq_or_ne v 0 with rfl | hv
  · rw [smul_zero, (A.val.coeff e z).map_eq_zero_of_eq ![0, 0]
      (i := 0) (j := 1) (by simp) (by decide)]
  · exact ((hA.1 e z hz).2 v hv).le

private theorem topRatio_wedge_nonneg (w : KahlerBackground (m + 1) X)
    (A : ClosedRealOneOneForm (m + 1) X) (hA : A.val.IsKahler)
    (G : SmoothRealForm (m + 1) X (2 * m))
    (hG : ∀ e z, z ∈ e.val.target → G.coeff e z ∈ spCone m) (x : X) :
    0 ≤ topRatio w.form.val (wedgeTwo G A.val) x := by
  have hz := (complexChartAt (n := m + 1) x).val.map_source (mem_complexChartAt_source x)
  simp only [topRatio, chartRatio, wedgeTwo_coeff]
  exact div_nonneg (topDensity_nonneg_of_mem_spCone
    (wedge_mem_spCone (hG _ _ hz) (semipositive_coefficient hA _ hz)))
    (topDensity_formPow_pos w.isKahler.1 hz).le

/-- Cancelling the true common chart density produces the intrinsic good-set ratio estimate. -/
theorem ratio_ge_of_global_density_bound (w : KahlerBackground (m + 1) X)
    (A B : ClosedRealOneOneForm (m + 1) X) (hA : A.val.IsKahler) (hB : B.val.IsKahler)
    (G : SmoothRealForm (m + 1) X (2 * m))
    (hG : ∀ e z, z ∈ e.val.target → G.coeff e z ∈ spCone m)
    (hv : ∀ x, 0 < topRatio w.form.val (wedgeTwo G B.val) x)
    {c γ M : ℝ} (hc : 0 < c) (hγ : 0 < γ) (hM : 0 < M)
    (hMA : ∀ e z, z ∈ e.val.target → actualTopPowerDensity (A.val.coeff e z) =
      c * topDensity (coordinateWedge (G.coeff e z) (B.val.coeff e z)))
    (x : X)
    (hmix : topRatio w.form.val (slotForm (Fin.cons B (fun _ : Fin m => A))) x /
      topRatio w.form.val (wedgeTwo G B.val) x ≤ γ * M) :
    c / ((m + 1 : ℝ) * γ * M) ≤ topRatio w.form.val (wedgeTwo G A.val) x /
      topRatio w.form.val (wedgeTwo G B.val) x := by
  let e := complexChartAt (n := m + 1) x
  let z := e.val x
  have hz : z ∈ e.val.target := e.val.map_source (mem_complexChartAt_source x)
  let d := topDensity ((formPow w.form.val (m + 1)).coeff e z)
  have hd : 0 < d := topDensity_formPow_pos w.isKahler.1 hz
  have hV : topRatio w.form.val (wedgeTwo G B.val) x =
      topDensity (coordinateWedge (G.coeff e z) (B.val.coeff e z)) / d := rfl
  have hP : topRatio w.form.val (wedgeTwo G A.val) x =
      topDensity (coordinateWedge (G.coeff e z) (A.val.coeff e z)) / d := rfl
  have hQ : topRatio w.form.val (slotForm (Fin.cons B (fun _ : Fin m => A))) x =
      actualMixedTopDensity (Fin.cons (B.val.coeff e z)
        (fun _ : Fin m => A.val.coeff e z)) / d := by
    change topDensity ((slotForm (Fin.cons B (fun _ : Fin m => A))).coeff e z) / d = _
    rw [topDensity_slotForm_coeff]
    congr 2
    funext i
    refine Fin.cases ?_ (fun _ => ?_) i <;> rfl
  have hVpos : 0 < topDensity (coordinateWedge (G.coeff e z) (B.val.coeff e z)) := by
    have h := hv x
    rw [hV] at h
    simpa only [zero_mul] using (lt_div_iff₀ hd).mp h
  have hrawRatio : actualMixedTopDensity (Fin.cons (B.val.coeff e z)
      (fun _ : Fin m => A.val.coeff e z)) /
      topDensity (coordinateWedge (G.coeff e z) (B.val.coeff e z)) ≤ γ * M := by
    rw [hQ, hV] at hmix
    convert hmix using 1
    field_simp [hd.ne', hVpos.ne']
  have hraw := XiaoTestDensityEstimate.ratio_ge_of_density_bound
    (A.property.2 e z hz) (B.property.2 e z hz) (hA.1 e z hz).2 (hB.1 e z hz).2
    (hG e z hz) hVpos hc hγ hM (hMA e z hz) ((div_le_iff₀ hVpos).mp hrawRatio)
  rw [hP, hV]
  convert hraw using 1
  field_simp [hd.ne', hVpos.ne']

/-- The actual compact-manifold estimate: no measurable/integrable ratios or probability
instance are supplied as assumptions, and the mixed mass is the genuine slot integral. -/
theorem integral_testWedge_ge [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (w : KahlerBackground (m + 1) X) (A B : ClosedRealOneOneForm (m + 1) X)
    (hA : A.val.IsKahler) (hB : B.val.IsKahler)
    (G : SmoothRealForm (m + 1) X (2 * m))
    (hG : ∀ e z, z ∈ e.val.target → G.coeff e z ∈ spCone m)
    (hv : ∀ x, 0 < topRatio w.form.val (wedgeTwo G B.val) x)
    (hnorm : ∫ x, topRatio w.form.val (wedgeTwo G B.val) x ∂(kahlerVolume w) = 1)
    {c : ℝ} (hc : 0 < c)
    (hM : 0 < NefMixedMass.slotIntegral w (Fin.cons B (fun _ : Fin m => A)))
    (hMA : ∀ e z, z ∈ e.val.target → actualTopPowerDensity (A.val.coeff e z) =
      c * topDensity (coordinateWedge (G.coeff e z) (B.val.coeff e z))) :
    c / (4 * (m + 1 : ℝ) * NefMixedMass.slotIntegral w (Fin.cons B (fun _ : Fin m => A))) ≤
      ∫ x, topRatio w.form.val (wedgeTwo G A.val) x ∂(kahlerVolume w) := by
  let v : X → ℝ := topRatio w.form.val (wedgeTwo G B.val)
  let P : X → ℝ := topRatio w.form.val (wedgeTwo G A.val)
  let θ : Fin (m + 1) → ClosedRealOneOneForm (m + 1) X := Fin.cons B (fun _ => A)
  let Q : X → ℝ := topRatio w.form.val (slotForm θ)
  let M := NefMixedMass.slotIntegral w θ
  let μ := (kahlerVolume w).withDensity fun x => ENNReal.ofReal (v x)
  let f : X → ℝ := fun x => P x / v x
  let g : X → ℝ := fun x => Q x / v x
  have hvm : Measurable v := (continuous_topRatio w.isKahler.1 (wedgeTwo G B.val)).measurable
  have hQm : Measurable Q := (continuous_topRatio w.isKahler.1 (slotForm θ)).measurable
  let : IsProbabilityMeasure μ :=
    XiaoNormalizedDensityMeasure.isProbabilityMeasure_withDensity_of_integral_one
      (kahlerVolume w) (IntegrationCurrent.integrable_topRatio w _) (fun x => (hv x).le) hnorm
  have hf : Integrable f μ := XiaoNormalizedDensityMeasure.integrable_div_withDensity
    (kahlerVolume w) hvm hv (IntegrationCurrent.integrable_topRatio w _)
  have hg : Integrable g μ := XiaoNormalizedDensityMeasure.integrable_div_withDensity
    (kahlerVolume w) hvm hv (IntegrationCurrent.integrable_topRatio w _)
  have hgm : Measurable g := hQm.div hvm
  have hAs : A.val.IsSemipositive := fun e z hz => (semipositive_coefficient hA e hz).2
  have hBs : B.val.IsSemipositive := fun e z hz => (semipositive_coefficient hB e hz).2
  have hslots : ∀ i, (θ i).val.IsSemipositive := by
    intro i
    refine Fin.cases ?_ (fun _ => ?_) i
    · exact hBs
    · exact hAs
  have hf0 : ∀ x, 0 ≤ f x := fun x =>
    div_nonneg (topRatio_wedge_nonneg w A hA G hG x) (hv x).le
  have hg0 : ∀ x, 0 ≤ g x := fun x =>
    div_nonneg (NefMixedMass.topRatio_slotForm_nonneg w hslots x) (hv x).le
  have hgmass : ∫ x, g x ∂μ = M := by
    rw [XiaoNormalizedDensityMeasure.integral_div_withDensity (kahlerVolume w) hvm hv Q]
    rfl
  have hgood : ∀ x, g x < 2 * M → c / (2 * (m + 1 : ℝ) * M) ≤ f x := by
    intro x hx
    have hraw := ratio_ge_of_global_density_bound w A B hA hB G hG hv
      hc (by norm_num : (0 : ℝ) < 2) hM hMA x hx.le
    simpa only [mul_comm, mul_left_comm] using hraw
  have h := XiaoBadSetEstimate.integral_ge_of_bad_set μ hf hg hgm hf0 hg0 hc.le
    (by positivity : (0 : ℝ) < m + 1) hM hgmass hgood
  rw [XiaoNormalizedDensityMeasure.integral_div_withDensity (kahlerVolume w) hvm hv P] at h
  exact h

end SGPT.Foundations.Analysis.Pending.XiaoGlobalTestDensity
