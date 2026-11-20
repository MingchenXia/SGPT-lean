import SGPT.Toric.TropicalSmoothDensity
import SGPT.Toric.TropicalProductVolume
import SGPT.Toric.LogLogPolarCoordinates
import SGPT.Toric.LogLogLogarithmicSubstitution
import Mathlib.MeasureTheory.Integral.Prod
import SGPT.Convex.SmoothMixedAlexandrov
import SGPT.Convex.AlexandrovLocalFinite
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

set_option autoImplicit false
noncomputable section

namespace SGPT.Toric

open Set Filter MeasureTheory SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Convex
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open scoped Topology BigOperators ContDiff RealInnerProductSpace CompactlySupported

/-- The literal original exponential point, with all angular coordinates retained. -/
def tropicalRadialPoint {n : ℕ} (a : EuclideanSpace ℝ (Fin n))
    (t : Fin n → ℝ) : ComplexModel n :=
  WithLp.toLp 2 (fun i => logLogRadialPoint (a i, t i))

/-- The genuine finite product of the unchanged normalized full-angle probabilities. -/
def tropicalAngularMeasure (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ => logLogAngularMeasure)

private theorem tropicalPolar_radialPoint_mem {n : ℕ}
    (a : EuclideanSpace ℝ (Fin n)) (t : Fin n → ℝ) :
    tropicalRadialPoint a t ∈ complexTorus n := by
  intro i
  exact logLogRadialPoint_ne_zero (a i, t i)

private theorem tropicalPolar_radialPoint_continuous {n : ℕ} :
    Continuous (fun p : EuclideanSpace ℝ (Fin n) × (Fin n → ℝ) =>
      tropicalRadialPoint p.1 p.2) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  exact continuous_logLogRadialPoint.comp
    (((PiLp.continuous_apply 2 _ i).comp continuous_fst).prodMk
      ((continuous_apply i).comp continuous_snd))

theorem tropicalization_tropicalRadialPoint {n : ℕ}
    (a : EuclideanSpace ℝ (Fin n)) (t : Fin n → ℝ) :
    tropicalization (tropicalRadialPoint a t) = a := by
  ext i
  change 2 * Real.log ‖logLogRadialPoint (a i, t i)‖ = a i
  rw [norm_logLogRadialPoint, Real.log_exp]
  ring

theorem tropicalAngularMeasure_univ (n : ℕ) :
    tropicalAngularMeasure n univ = 1 := by
  simp [tropicalAngularMeasure]

private def tropicalPolar_squaredLogMap {n : ℕ} (r : Fin n → ℝ) : Fin n → ℝ :=
  fun i => 2 * Real.log (r i)

private def tropicalPolar_squaredLogDerivative {n : ℕ} (r : Fin n → ℝ) :
    (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi (fun i =>
    (ContinuousLinearMap.toSpanSingleton ℝ (2 * (r i)⁻¹)).comp
      (ContinuousLinearMap.proj i))

private theorem tropicalPolar_squaredLog_hasFDerivAt {n : ℕ} {r : Fin n → ℝ}
    (hr : r ∈ univ.pi (fun _ : Fin n => Ioi (0 : ℝ))) :
    HasFDerivAt tropicalPolar_squaredLogMap (tropicalPolar_squaredLogDerivative r) r := by
  apply hasFDerivAt_pi.mpr
  intro i
  exact ((Real.hasDerivAt_log ((mem_univ_pi.mp hr) i).ne').const_mul 2).hasFDerivAt.comp r
    (hasFDerivAt_apply i r)

private theorem tropicalPolar_squaredLog_det {n : ℕ} (r : Fin n → ℝ) :
    (tropicalPolar_squaredLogDerivative r).det =
      (2 : ℝ) ^ n * ∏ i, (r i)⁻¹ := by
  simp [tropicalPolar_squaredLogDerivative, ContinuousLinearMap.det_pi,
    Finset.prod_mul_distrib]

private theorem tropicalPolar_squaredLog_image {n : ℕ} :
    tropicalPolar_squaredLogMap '' univ.pi (fun _ : Fin n => Ioi (0 : ℝ)) = univ := by
  apply eq_univ_of_forall
  intro a
  refine ⟨fun i => Real.exp (a i / 2), mem_univ_pi.mpr ?_, ?_⟩
  · intro i
    exact Real.exp_pos _
  · funext i
    change 2 * Real.log (Real.exp (a i / 2)) = a i
    rw [Real.log_exp]
    ring

private theorem tropicalPolar_squaredLog_injOn {n : ℕ} :
    InjOn (@tropicalPolar_squaredLogMap n)
      (univ.pi (fun _ : Fin n => Ioi (0 : ℝ))) := by
  intro r hr s hs heq
  funext i
  apply Real.log_injOn_pos ((mem_univ_pi.mp hr) i) ((mem_univ_pi.mp hs) i)
  have hi := congrFun heq i
  change 2 * Real.log (r i) = 2 * Real.log (s i) at hi
  linarith

/-- Genuine all-dimensional Jacobian substitution retains the literal factor 2^-n. -/
theorem integral_tropical_squaredLog_substitution {n : ℕ}
    (B : EuclideanSpace ℝ (Fin n) → ℝ) :
    (∫ r in univ.pi (fun _ : Fin n => Ioi (0 : ℝ)),
      (∏ i, (r i)⁻¹) * B (WithLp.toLp 2 (tropicalPolar_squaredLogMap r))) =
      ((2 : ℝ) ^ n)⁻¹ * ∫ a, B a := by
  have H := integral_image_eq_integral_abs_det_fderiv_smul volume
    (s := univ.pi (fun _ : Fin n => Ioi (0 : ℝ)))
    (f := tropicalPolar_squaredLogMap) (f' := tropicalPolar_squaredLogDerivative)
    (MeasurableSet.univ_pi (fun _ => measurableSet_Ioi))
    (fun r hr => (tropicalPolar_squaredLog_hasFDerivAt hr).hasFDerivWithinAt)
    tropicalPolar_squaredLog_injOn (fun a => B (WithLp.toLp 2 a))
  rw [tropicalPolar_squaredLog_image, setIntegral_univ] at H
  have hleft : (∫ a : Fin n → ℝ, B (WithLp.toLp 2 a)) = ∫ a, B a :=
    (PiLp.volume_preserving_toLp (Fin n)).integral_comp
      (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding B
  have hright : (∫ r in univ.pi (fun _ : Fin n => Ioi (0 : ℝ)),
      |(tropicalPolar_squaredLogDerivative r).det| •
        B (WithLp.toLp 2 (tropicalPolar_squaredLogMap r))) =
      (2 : ℝ) ^ n * ∫ r in univ.pi (fun _ : Fin n => Ioi (0 : ℝ)),
        (∏ i, (r i)⁻¹) * B (WithLp.toLp 2 (tropicalPolar_squaredLogMap r)) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun (MeasurableSet.univ_pi (fun _ => measurableSet_Ioi))
    intro r hr
    change |(tropicalPolar_squaredLogDerivative r).det| •
      B (WithLp.toLp 2 (tropicalPolar_squaredLogMap r)) =
      (2 : ℝ) ^ n * ((∏ i, (r i)⁻¹) *
        B (WithLp.toLp 2 (tropicalPolar_squaredLogMap r)))
    rw [tropicalPolar_squaredLog_det]
    have hn : 0 ≤ (2 : ℝ) ^ n * ∏ i, (r i)⁻¹ := by
      apply mul_nonneg (pow_nonneg (by norm_num) _)
      exact Finset.prod_nonneg fun i _ => inv_nonneg.mpr (le_of_lt ((mem_univ_pi.mp hr) i))
    rw [abs_of_nonneg hn, smul_eq_mul]
    ring
  rw [hleft, hright] at H
  rw [H]
  rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)), one_mul]

private theorem tropicalPolar_tropicalization_continuousAt {n : ℕ}
    {z : ComplexModel n} (hz : z ∈ complexTorus n) :
    ContinuousAt tropicalization z := by
  apply (PiLp.continuous_toLp 2 _).continuousAt.comp
  apply continuousAt_pi.mpr
  intro i
  exact continuousAt_const.mul
    ((Real.continuousAt_log (norm_ne_zero_iff.mpr (hz i))).comp
      (f := fun z : ComplexModel n => ‖z i‖)
      (PiLp.continuous_apply 2 _ i).continuousAt.norm)

/-- The actual signed density retains the original volume denominator. -/
def tropicalSignedTestDensity {n : ℕ} (ρ : EuclideanSpace ℝ (Fin n) → ℝ)
    (η : ComplexModel n → ℝ) (z : ComplexModel n) : ℝ :=
  ρ (tropicalization z) * η z /
    (Real.pi ^ n * ∏ i, Complex.normSq (z i))

/-- The actual compact torus support supplies one window for ALL angles. -/
theorem tropicalSignedTest_radialWindow {n : ℕ} {η : ComplexModel n → ℝ}
    (hK : HasCompactSupport η) (hD : tsupport η ⊆ complexTorus n) :
    ∃ L R : ℝ, ∀ (a : EuclideanSpace ℝ (Fin n)) (t : Fin n → ℝ),
      η (tropicalRadialPoint a t) ≠ 0 → ∀ i, a i ∈ Icc L R := by
  have ht : ContinuousOn tropicalization (tsupport η) := by
    intro z hz
    exact (tropicalPolar_tropicalization_continuousAt (hD hz)).continuousWithinAt
  obtain ⟨M, _hM, hMbound⟩ :=
    (hK.image_of_continuousOn ht).isBounded.exists_pos_norm_le
  refine ⟨-M, M, ?_⟩
  intro a t hη i
  have ha : a ∈ tropicalization '' tsupport η :=
    ⟨tropicalRadialPoint a t, subset_tsupport η hη,
      tropicalization_tropicalRadialPoint a t⟩
  have hi : |a i| ≤ M := by
    exact (show |a i| ≤ ‖a‖ from PiLp.norm_apply_le a i).trans (hMbound a ha)
  exact abs_le.mp hi

theorem continuous_tropicalSignedTestDensity {n : ℕ}
    {ρ : EuclideanSpace ℝ (Fin n) → ℝ} {η : ComplexModel n → ℝ}
    (hρ : Continuous ρ) (hη : Continuous η)
    (hD : tsupport η ⊆ complexTorus n) :
    Continuous (tropicalSignedTestDensity ρ η) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  by_cases hz : z ∈ complexTorus n
  · have hden : Continuous (fun z : ComplexModel n =>
        Real.pi ^ n * ∏ i, Complex.normSq (z i)) := by fun_prop
    have hne : Real.pi ^ n * ∏ i, Complex.normSq (z i) ≠ 0 := by
      apply mul_ne_zero (pow_ne_zero _ Real.pi_ne_zero)
      apply Finset.prod_ne_zero_iff.mpr
      intro i _
      exact mt Complex.normSq_eq_zero.mp (hz i)
    exact ((hρ.continuousAt.comp (tropicalPolar_tropicalization_continuousAt hz)).mul
      hη.continuousAt).div hden.continuousAt hne
  · have hout : z ∉ tsupport η := fun h => hz (hD h)
    have heq : (fun _ : ComplexModel n => (0 : ℝ)) =ᶠ[𝓝 z]
        tropicalSignedTestDensity ρ η := by
      filter_upwards [(isClosed_tsupport η).isOpen_compl.mem_nhds hout] with w hw
      have hηw : η w = 0 := image_eq_zero_of_notMem_tsupport hw
      simp [tropicalSignedTestDensity, hηw]
    exact continuousAt_const.congr_of_eventuallyEq heq.symm

private theorem tropicalPolar_signedDensity_compactSupport {n : ℕ}
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) {η : ComplexModel n → ℝ}
    (hK : HasCompactSupport η) : HasCompactSupport (tropicalSignedTestDensity ρ η) := by
  apply HasCompactSupport.intro (K := tsupport η) hK
  intro z hz
  have hηz : η z = 0 := image_eq_zero_of_notMem_tsupport hz
  simp [tropicalSignedTestDensity, hηz]

theorem integrable_tropicalSignedTestDensity {n : ℕ}
    {ρ : EuclideanSpace ℝ (Fin n) → ℝ} {η : ComplexModel n → ℝ}
    (hρ : Continuous ρ) (hη : Continuous η) (hK : HasCompactSupport η)
    (hD : tsupport η ⊆ complexTorus n) :
    Integrable (tropicalSignedTestDensity ρ η) :=
  (continuous_tropicalSignedTestDensity hρ hη hD).integrable_of_hasCompactSupport
    (tropicalPolar_signedDensity_compactSupport ρ hK)

private theorem tropicalPolar_angularMeasure_normalization (n : ℕ) :
    tropicalAngularMeasure n =
      (ENNReal.ofReal (2 * Real.pi)⁻¹) ^ n •
        (volume : Measure (Fin n → ℝ)).restrict
          (univ.pi (fun _ : Fin n => Ioc (-Real.pi) Real.pi)) := by
  classical
  unfold tropicalAngularMeasure
  rw [volume_pi, Measure.restrict_pi_pi]
  apply Measure.pi_eq
  intro s _hs
  simp [logLogAngularMeasure, Measure.smul_apply, smul_eq_mul,
    Measure.pi_pi, Finset.prod_mul_distrib]

private theorem tropicalPolar_integral_angle_normalization {n : ℕ}
    (f : (Fin n → ℝ) → ℝ) :
    (∫ t in univ.pi (fun _ : Fin n => Ioo (-Real.pi) Real.pi), f t) =
      (2 * Real.pi) ^ n * ∫ t, f t ∂tropicalAngularMeasure n := by
  have hs : (univ.pi (fun _ : Fin n => Ioc (-Real.pi) Real.pi))
      =ᵐ[volume] univ.pi (fun _ : Fin n => Ioo (-Real.pi) Real.pi) := by
    rw [volume_pi]
    exact Measure.pi_Ioo_ae_eq_pi_Ioc.symm
  rw [tropicalPolar_angularMeasure_normalization, integral_smul_measure,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal
      (inv_nonneg.mpr (by positivity : 0 ≤ 2 * Real.pi)),
    setIntegral_congr_set hs]
  simp only [smul_eq_mul]
  rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀
    (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero), one_pow, one_mul]

private theorem tropicalPolar_integral_regroup {n : ℕ}
    (f : (Fin n → ℝ × ℝ) → ℝ)
    (hf : IntegrableOn f (univ.pi (fun _ : Fin n => Complex.polarCoord.target))) :
    (∫ p in univ.pi (fun _ : Fin n => Complex.polarCoord.target), f p) =
      ∫ r in univ.pi (fun _ : Fin n => Ioi (0 : ℝ)),
        ∫ t in univ.pi (fun _ : Fin n => Ioo (-Real.pi) Real.pi),
          f (fun i => (r i, t i)) := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n)
  let R := univ.pi (fun _ : Fin n => Ioi (0 : ℝ))
  let T := univ.pi (fun _ : Fin n => Ioo (-Real.pi) Real.pi)
  have hRT : MeasurableSet (R ×ˢ T) :=
    (MeasurableSet.univ_pi (fun _ => measurableSet_Ioi)).prod
      (MeasurableSet.univ_pi (fun _ => measurableSet_Ioo))
  have hs : e ⁻¹' (R ×ˢ T) =
      univ.pi (fun _ : Fin n => Complex.polarCoord.target) := by
    ext p
    simp [e, R, T, MeasurableEquiv.arrowProdEquivProdArrow,
      Complex.polarCoord_target, forall_and]
  have h := (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin n)).restrict_preimage hRT
  change MeasurePreserving e (volume.restrict (e ⁻¹' (R ×ˢ T)))
    (((volume : Measure (Fin n → ℝ)).prod volume).restrict (R ×ˢ T)) at h
  rw [hs, ← Measure.prod_restrict] at h
  have hi := MeasurePreserving.symm e h
  have hf' := hi.integrable_comp_of_integrable hf
  have heq := hi.integral_comp e.symm.measurableEmbedding f
  calc
    _ = ∫ p, f (e.symm p)
        ∂(volume.restrict R).prod (volume.restrict T) := heq.symm
    _ = ∫ r in R, ∫ t in T, f (e.symm (r, t)) := integral_prod _ hf'
    _ = _ := rfl

private theorem tropicalPolar_point_eq {n : ℕ} {r : Fin n → ℝ}
    (hr : r ∈ univ.pi (fun _ : Fin n => Ioi (0 : ℝ))) (t : Fin n → ℝ) :
    WithLp.toLp 2 (fun i => Complex.polarCoord.symm (r i, t i)) =
      tropicalRadialPoint (WithLp.toLp 2 (tropicalPolar_squaredLogMap r)) t := by
  ext i
  exact polarCoord_symm_eq_logLogRadialPoint ((mem_univ_pi.mp hr) i) (t i)

private theorem tropicalPolar_densityJacobian {n : ℕ}
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (η : ComplexModel n → ℝ)
    {r : Fin n → ℝ} (hr : r ∈ univ.pi (fun _ : Fin n => Ioi (0 : ℝ)))
    (t : Fin n → ℝ) :
    (∏ i, r i) * tropicalSignedTestDensity ρ η
        (WithLp.toLp 2 (fun i => Complex.polarCoord.symm (r i, t i))) =
      (Real.pi ^ n)⁻¹ * (∏ i, (r i)⁻¹) *
        (ρ (WithLp.toLp 2 (tropicalPolar_squaredLogMap r)) *
          η (tropicalRadialPoint (WithLp.toLp 2 (tropicalPolar_squaredLogMap r)) t)) := by
  have hn : (∏ i, Complex.normSq (Complex.polarCoord.symm (r i, t i))) =
      (∏ i, r i) ^ 2 := by
    calc
      _ = ∏ i, (r i) ^ 2 := by
        apply Finset.prod_congr rfl
        intro i _
        rw [Complex.normSq_eq_norm_sq, Complex.norm_polarCoord_symm,
          abs_of_pos ((mem_univ_pi.mp hr) i)]
      _ = _ := Finset.prod_pow _ _ _
  have hne : (∏ i, r i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => ((mem_univ_pi.mp hr) i).ne')
  unfold tropicalSignedTestDensity
  change (∏ i, r i) * (ρ (tropicalization
      (WithLp.toLp 2 (fun i => Complex.polarCoord.symm (r i, t i)))) *
      η (WithLp.toLp 2 (fun i => Complex.polarCoord.symm (r i, t i))) /
      (Real.pi ^ n * ∏ i, Complex.normSq (Complex.polarCoord.symm (r i, t i)))) = _
  rw [hn, tropicalPolar_point_eq hr, tropicalization_tropicalRadialPoint,
    Finset.prod_inv_distrib]
  field_simp [hne, Real.pi_ne_zero]

private theorem tropicalPolar_integrableJacobian {n : ℕ}
    {ρ : EuclideanSpace ℝ (Fin n) → ℝ} {η : ComplexModel n → ℝ}
    (hρ : Continuous ρ) (hη : Continuous η) (hK : HasCompactSupport η)
    (hD : tsupport η ⊆ complexTorus n) :
    IntegrableOn (fun p : Fin n → ℝ × ℝ =>
      (∏ i, (p i).1) * tropicalSignedTestDensity ρ η
        (WithLp.toLp 2 (fun i => Complex.polarCoord.symm (p i))))
      (univ.pi (fun _ : Fin n => Complex.polarCoord.target)) := by
  let Q := tropicalSignedTestDensity ρ η
  let e := MeasurableEquiv.piCongrRight
    (fun _ : Fin n => Complex.measurableEquivRealProd.symm)
  have hQ : Integrable (fun z : Fin n → ℂ => Q (WithLp.toLp 2 z)) :=
    (volume_preserving_complexModel_toLp n).integrable_comp_of_integrable
      (integrable_tropicalSignedTestDensity hρ hη hK hD)
  have hreal := (volume_preserving_pi
    (fun _ : Fin n => Complex.volume_preserving_equiv_real_prod.symm)).integrable_comp_of_integrable hQ
  have H := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    (s := univ.pi (fun _ : Fin n => polarCoord.target))
    (f := fun p : Fin n → ℝ × ℝ => fun i => polarCoord.symm (p i))
    (f' := fderivPiPolarCoordSymm)
    measurableSet_pi_polarCoord_target
    (fun p _ => (hasFDerivAt_pi_polarCoord_symm p).hasFDerivWithinAt)
    injOn_pi_polarCoord_symm (fun p => Q (WithLp.toLp 2 (e p)))
  have hi := H.mp hreal.integrableOn
  apply hi.congr_fun _ measurableSet_pi_polarCoord_target
  intro p hp
  have he : e (fun i => polarCoord.symm (p i)) =
      (fun i => Complex.polarCoord.symm (p i)) := by
    funext i
    exact Complex.measurableEquivRealProd_symm_polarCoord_symm_apply (p i)
  change |(fderivPiPolarCoordSymm p).det| •
    Q (WithLp.toLp 2 (e (fun i => polarCoord.symm (p i)))) = _
  rw [det_fderivPiPolarCoordSymm, Finset.abs_prod]
  simp_rw [abs_fst_of_mem_pi_polarCoord_target hp]
  rw [smul_eq_mul, he]

/-- Every original signed torus-supported compact test has the exact full polar integral. -/
theorem integral_tropicalSignedTestDensity {n : ℕ}
    {ρ : EuclideanSpace ℝ (Fin n) → ℝ} {η : ComplexModel n → ℝ}
    (hρ : Continuous ρ) (hη : Continuous η) (hK : HasCompactSupport η)
    (hD : tsupport η ⊆ complexTorus n) :
    (∫ z : ComplexModel n, tropicalSignedTestDensity ρ η z) =
      ∫ a : EuclideanSpace ℝ (Fin n), ρ a *
        ∫ t, η (tropicalRadialPoint a t) ∂tropicalAngularMeasure n := by
  have hi := tropicalPolar_integrableJacobian hρ hη hK hD
  have hc := integral_complexModel_coordinates
    (fun z : Fin n → ℂ => tropicalSignedTestDensity ρ η (WithLp.toLp 2 z))
  have hp := Complex.integral_comp_pi_polarCoord_symm
    (fun z : Fin n → ℂ => tropicalSignedTestDensity ρ η (WithLp.toLp 2 z))
  calc
    _ = ∫ z : Fin n → ℂ, tropicalSignedTestDensity ρ η (WithLp.toLp 2 z) := by
      simpa only [WithLp.toLp_ofLp, volume_pi] using hc
    _ = ∫ p in univ.pi (fun _ : Fin n => Complex.polarCoord.target),
        (∏ i, (p i).1) * tropicalSignedTestDensity ρ η
          (WithLp.toLp 2 (fun i => Complex.polarCoord.symm (p i))) := by
      simpa only [smul_eq_mul] using hp.symm
    _ = ∫ r in univ.pi (fun _ : Fin n => Ioi (0 : ℝ)),
        ∫ t in univ.pi (fun _ : Fin n => Ioo (-Real.pi) Real.pi),
          (∏ i, r i) * tropicalSignedTestDensity ρ η
            (WithLp.toLp 2 (fun i => Complex.polarCoord.symm (r i, t i))) :=
      tropicalPolar_integral_regroup _ hi
    _ = ∫ r in univ.pi (fun _ : Fin n => Ioi (0 : ℝ)),
        (2 : ℝ) ^ n * ((∏ i, (r i)⁻¹) *
          (ρ (WithLp.toLp 2 (tropicalPolar_squaredLogMap r)) *
            ∫ t, η (tropicalRadialPoint (WithLp.toLp 2 (tropicalPolar_squaredLogMap r)) t)
              ∂tropicalAngularMeasure n)) := by
      apply setIntegral_congr_fun (MeasurableSet.univ_pi (fun _ => measurableSet_Ioi))
      intro r hr
      have heq : (fun t : Fin n → ℝ =>
          (∏ i, r i) * tropicalSignedTestDensity ρ η
            (WithLp.toLp 2 (fun i => Complex.polarCoord.symm (r i, t i)))) =
          fun t => ((Real.pi ^ n)⁻¹ * (∏ i, (r i)⁻¹) *
            ρ (WithLp.toLp 2 (tropicalPolar_squaredLogMap r))) *
              η (tropicalRadialPoint (WithLp.toLp 2 (tropicalPolar_squaredLogMap r)) t) := by
        funext t
        rw [tropicalPolar_densityJacobian ρ η hr t]
        ring
      change (∫ t in univ.pi (fun _ : Fin n => Ioo (-Real.pi) Real.pi),
        (∏ i, r i) * tropicalSignedTestDensity ρ η
          (WithLp.toLp 2 (fun i => Complex.polarCoord.symm (r i, t i)))) = _
      rw [heq, integral_const_mul, tropicalPolar_integral_angle_normalization]
      rw [mul_pow]
      calc
        _ = ((Real.pi ^ n)⁻¹ * Real.pi ^ n) *
            ((2 : ℝ) ^ n * ((∏ i, (r i)⁻¹) *
              (ρ (WithLp.toLp 2 (tropicalPolar_squaredLogMap r)) *
                ∫ t, η (tropicalRadialPoint (WithLp.toLp 2 (tropicalPolar_squaredLogMap r)) t)
                  ∂tropicalAngularMeasure n))) := by ring
        _ = _ := by rw [inv_mul_cancel₀ (pow_ne_zero _ Real.pi_ne_zero), one_mul]
    _ = (2 : ℝ) ^ n * ∫ r in univ.pi (fun _ : Fin n => Ioi (0 : ℝ)),
        (∏ i, (r i)⁻¹) * (ρ (WithLp.toLp 2 (tropicalPolar_squaredLogMap r)) *
          ∫ t, η (tropicalRadialPoint (WithLp.toLp 2 (tropicalPolar_squaredLogMap r)) t)
            ∂tropicalAngularMeasure n) := integral_const_mul _ _
    _ = _ := by
      rw [integral_tropical_squaredLog_substitution
        (fun a => ρ a * ∫ t, η (tropicalRadialPoint a t) ∂tropicalAngularMeasure n),
        ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)), one_mul]

private def tropicalPolar_compactLift {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) :
    Set (ComplexModel n) :=
  (fun p => tropicalRadialPoint p.1 p.2) ''
    (K ×ˢ univ.pi (fun _ : Fin n => Icc (-Real.pi) Real.pi))

private theorem tropicalPolar_compactLift_compact {n : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) :
    IsCompact (tropicalPolar_compactLift K) :=
  (hK.prod (isCompact_univ_pi (fun _ => isCompact_Icc))).image
    tropicalPolar_radialPoint_continuous

private theorem tropicalPolar_compactLift_subset {n : ℕ}
    (K : Set (EuclideanSpace ℝ (Fin n))) :
    tropicalPolar_compactLift K ⊆ complexTorus n := by
  rintro z ⟨p, _hp, rfl⟩
  exact tropicalPolar_radialPoint_mem p.1 p.2

private theorem tropicalPolar_radialPoint_arg {n : ℕ} {z : ComplexModel n}
    (hz : z ∈ complexTorus n) :
    tropicalRadialPoint (tropicalization z) (fun i => Complex.arg (z i)) = z := by
  ext i
  change Complex.exp (((2 * Real.log ‖z i‖) / 2 : ℝ) +
    (Complex.arg (z i) : ℂ) * Complex.I) = z i
  rw [show (2 * Real.log ‖z i‖) / 2 = Real.log ‖z i‖ by ring]
  exact Complex.exp_log (hz i)

private theorem tropicalPolar_mem_compactLift {n : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin n))} {z : ComplexModel n}
    (hz : z ∈ complexTorus n) (hK : tropicalization z ∈ K) :
    z ∈ tropicalPolar_compactLift K := by
  refine ⟨(tropicalization z, fun i => Complex.arg (z i)), ⟨hK, ?_⟩,
    tropicalPolar_radialPoint_arg hz⟩
  exact mem_univ_pi.mpr (fun i => ⟨(Complex.neg_pi_lt_arg (z i)).le,
    Complex.arg_le_pi (z i)⟩)

private def tropicalPolar_filledTest {n : ℕ}
    (φ : EuclideanSpace ℝ (Fin n) → ℝ) : ComplexModel n → ℝ :=
  (complexTorus n).indicator (fun z => φ (tropicalization z))

private theorem tropicalPolar_filledTest_tsupport {n : ℕ}
    (φ : EuclideanSpace ℝ (Fin n) → ℝ) (hK : HasCompactSupport φ) :
    tsupport (tropicalPolar_filledTest φ) ⊆ tropicalPolar_compactLift (tsupport φ) := by
  apply closure_minimal _ (tropicalPolar_compactLift_compact hK).isClosed
  intro z hz
  by_cases hD : z ∈ complexTorus n
  · apply tropicalPolar_mem_compactLift hD
    apply subset_tsupport φ
    simpa only [Function.mem_support, tropicalPolar_filledTest, indicator_of_mem hD] using hz
  · exact False.elim (hz (indicator_of_notMem hD _))

private theorem tropicalPolar_filledTest_hasCompactSupport {n : ℕ}
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hK : HasCompactSupport φ) :
    HasCompactSupport (tropicalPolar_filledTest φ) :=
  (tropicalPolar_compactLift_compact hK).of_isClosed_subset
    (isClosed_tsupport _) (tropicalPolar_filledTest_tsupport φ hK)

private theorem tropicalPolar_filledTest_continuous {n : ℕ}
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : Continuous φ)
    (hK : HasCompactSupport φ) : Continuous (tropicalPolar_filledTest φ) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  by_cases hz : z ∈ complexTorus n
  · have heq : tropicalPolar_filledTest φ =ᶠ[𝓝 z] (fun w => φ (tropicalization w)) := by
      filter_upwards [(isOpen_complexTorus n).mem_nhds hz] with w hw
      exact indicator_of_mem hw _
    exact (hφ.continuousAt.comp (tropicalPolar_tropicalization_continuousAt hz)).congr_of_eventuallyEq heq
  · have hzK : z ∉ tropicalPolar_compactLift (tsupport φ) :=
      fun h => hz (tropicalPolar_compactLift_subset _ h)
    have heq : tropicalPolar_filledTest φ =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
      filter_upwards [(tropicalPolar_compactLift_compact hK).isClosed.isOpen_compl.mem_nhds hzK]
        with w hw
      exact image_eq_zero_of_notMem_tsupport (fun h => hw (tropicalPolar_filledTest_tsupport φ hK h))
    exact continuousAt_const.congr_of_eventuallyEq heq

private theorem tropicalPolar_hessianMatrix {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (a : EuclideanSpace ℝ (Fin n)) :
    (fun j k : Fin n => tropicalHessianEntry f a j k) =
      hessianMatrix (EuclideanSpace.basisFun (Fin n) ℝ) f a := by
  ext j k
  simp [tropicalHessianEntry, hessianMatrix, realHessian_eq_fderiv]

private def tropicalPolar_realDensity {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (a : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (n.factorial : ℝ) * (hessianMatrix (EuclideanSpace.basisFun (Fin n) ℝ) f a).det

private theorem tropicalPolar_realDensity_continuous {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ ∞ f) :
    Continuous (tropicalPolar_realDensity f) :=
  continuous_const.mul ((SGPT.Convex.continuous_hessianMatrix_of_contDiff
    (EuclideanSpace.basisFun (Fin n) ℝ) hf).matrix_det)

private theorem tropicalPolar_realDensity_nonneg {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : ConvexOn ℝ univ f) (a : EuclideanSpace ℝ (Fin n)) :
    0 ≤ tropicalPolar_realDensity f a :=
  mul_nonneg (Nat.cast_nonneg _) ((SGPT.Convex.hessianMatrix_posSemidef_of_contDiff_convex
    (EuclideanSpace.basisFun (Fin n) ℝ) hc hf a).det_nonneg)

private theorem tropicalPolar_weight_continuousOn {n : ℕ}
    {ρ : EuclideanSpace ℝ (Fin n) → ℝ} (hρ : Continuous ρ) :
    ContinuousOn (tropicalSignedTestDensity ρ (fun _ => 1)) (complexTorus n) := by
  intro z hz
  have hden : Continuous (fun z : ComplexModel n =>
      Real.pi ^ n * ∏ i, Complex.normSq (z i)) := by fun_prop
  have hne : Real.pi ^ n * ∏ i, Complex.normSq (z i) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ Real.pi_ne_zero)
      (Finset.prod_ne_zero_iff.mpr (fun i _ => mt Complex.normSq_eq_zero.mp (hz i)))
  exact (((hρ.continuousAt.comp (tropicalPolar_tropicalization_continuousAt hz)).mul
    continuousAt_const).div hden.continuousAt hne).continuousWithinAt

private theorem tropicalPolar_realMA_density {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : ConvexOn ℝ univ f) :
    alexandrovMeasure (innerₗ (EuclideanSpace ℝ (Fin n))) volume (fun a => (f a : EReal)) =
      volume.withDensity (fun a => ENNReal.ofReal (tropicalPolar_realDensity f a)) := by
  have h2 : ContDiff ℝ 2 f := hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  rw [alexandrovMeasure_eq_withDensity_det_hessian_euclidean hc
    (h2.differentiable (by norm_num)) (h2.fderiv_right (by norm_num)).locallyLipschitz]
  apply withDensity_congr_ae
  exact Eventually.of_forall fun a => by
    simp [tropicalPolar_realDensity, ENNReal.ofReal_mul, Nat.cast_nonneg]

private theorem tropicalPolar_smoothMeasure_weight {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : ConvexOn ℝ univ f) :
    smoothMeasure (tropicalSmoothDomain n) (fun y => f (tropicalization y))
      (isSmoothPshOn_tropicalSmoothProfile hf hc) =
        (volume.restrict (complexTorus n)).withDensity
          (fun z => ENNReal.ofReal (tropicalSignedTestDensity
            (tropicalPolar_realDensity f) (fun _ => 1) z)) := by
  rw [smoothMeasure_tropicalization_eq_withDensity hf hc]
  apply withDensity_congr_ae
  exact Eventually.of_forall fun z => by
    simp only [tropicalSignedTestDensity, mul_one, tropicalPolar_realDensity,
      tropicalPolar_hessianMatrix]

/-- Every actual signed real compact test reads the printed original Euclidean MA measure. -/
theorem integral_tropicalSmoothMeasure_source_test {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : ConvexOn ℝ univ f) {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hφ : Continuous φ) (hK : HasCompactSupport φ) :
    (∫ z, φ (tropicalization z) ∂smoothMeasure (tropicalSmoothDomain n)
      (fun y => f (tropicalization y)) (isSmoothPshOn_tropicalSmoothProfile hf hc)) =
      ∫ a, φ a ∂alexandrovMeasure (innerₗ (EuclideanSpace ℝ (Fin n))) volume
        (fun a => (f a : EReal)) := by
  let ρ := tropicalPolar_realDensity f
  let η := tropicalPolar_filledTest φ
  have hρ : Continuous ρ := tropicalPolar_realDensity_continuous hf
  have hη : Continuous η := tropicalPolar_filledTest_continuous hφ hK
  have hηK : HasCompactSupport η := tropicalPolar_filledTest_hasCompactSupport hK
  have hηD : tsupport η ⊆ complexTorus n :=
    (tropicalPolar_filledTest_tsupport φ hK).trans (tropicalPolar_compactLift_subset _)
  have hρnn := tropicalPolar_realDensity_nonneg hf hc
  have hw : ∀ z : ComplexModel n, 0 ≤ tropicalSignedTestDensity ρ (fun _ => 1) z := by
    intro z
    apply div_nonneg
    · exact mul_nonneg (hρnn _) (by norm_num)
    · exact mul_nonneg (pow_nonneg Real.pi_pos.le _)
        (Finset.prod_nonneg fun i _ => Complex.normSq_nonneg _)
  have hμ := tropicalPolar_smoothMeasure_weight hf hc
  have hm := (ENNReal.continuous_ofReal.comp_continuousOn
    (tropicalPolar_weight_continuousOn hρ)).aemeasurable (μ := volume)
      (isOpen_complexTorus n).measurableSet
  change AEMeasurable (fun z => ENNReal.ofReal (tropicalSignedTestDensity ρ (fun _ => 1) z))
    (volume.restrict (complexTorus n)) at hm
  have hθreal : (tropicalAngularMeasure n).real univ = 1 := by
    rw [measureReal_def, tropicalAngularMeasure_univ]
    norm_num
  calc
    _ = ∫ z in complexTorus n, tropicalSignedTestDensity ρ (fun _ => 1) z *
        φ (tropicalization z) := by
      rw [hμ, integral_withDensity_eq_integral_toReal_smul₀ hm
        (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
      apply integral_congr_ae
      exact Eventually.of_forall fun z => by
        change (ENNReal.ofReal (tropicalSignedTestDensity ρ (fun _ => 1) z)).toReal •
          φ (tropicalization z) = tropicalSignedTestDensity ρ (fun _ => 1) z * φ (tropicalization z)
        rw [ENNReal.toReal_ofReal (hw z), smul_eq_mul]
    _ = ∫ z, tropicalSignedTestDensity ρ η z := by
      calc
        _ = ∫ z in complexTorus n, tropicalSignedTestDensity ρ η z := by
          apply setIntegral_congr_fun (isOpen_complexTorus n).measurableSet
          intro z hz
          simp [tropicalSignedTestDensity, η, tropicalPolar_filledTest, indicator_of_mem hz]
          ring
        _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
          simp [tropicalSignedTestDensity, η, tropicalPolar_filledTest, indicator_of_notMem hz]
    _ = ∫ a, ρ a * ∫ t, η (tropicalRadialPoint a t) ∂tropicalAngularMeasure n :=
      integral_tropicalSignedTestDensity hρ hη hηK hηD
    _ = ∫ a, ρ a * φ a := by
      apply integral_congr_ae
      exact Eventually.of_forall fun a => by
        simp [η, tropicalPolar_filledTest, tropicalPolar_radialPoint_mem,
          tropicalization_tropicalRadialPoint, integral_const, hθreal]
    _ = _ := by
      have hmR : Measurable (fun a => ENNReal.ofReal (ρ a)) :=
        (ENNReal.continuous_ofReal.comp hρ).measurable
      rw [tropicalPolar_realMA_density hf hc]
      change (∫ a, ρ a * φ a) = ∫ a, φ a ∂volume.withDensity (fun a => ENNReal.ofReal (ρ a))
      rw [integral_withDensity_eq_integral_toReal_smul hmR
          (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
      apply integral_congr_ae
      exact Eventually.of_forall fun a => by
        change ρ a * φ a = (ENNReal.ofReal (ρ a)).toReal • φ a
        rw [ENNReal.toReal_ofReal (show 0 ≤ ρ a from hρnn a), smul_eq_mul]

private theorem tropicalPolar_tropicalization_measurable (n : ℕ) :
    Measurable (@tropicalization n) := by
  apply (PiLp.continuous_toLp 2 _).measurable.comp
  apply measurable_pi_lambda
  intro i
  exact measurable_const.mul (Real.measurable_log.comp
    ((PiLp.continuous_apply 2 _ i).measurable.norm))

private theorem tropicalPolar_compactLift_measure_lt_top {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : ConvexOn ℝ univ f) {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) :
    smoothMeasure (tropicalSmoothDomain n) (fun y => f (tropicalization y))
      (isSmoothPshOn_tropicalSmoothProfile hf hc) (tropicalPolar_compactLift K) < ⊤ := by
  let L := tropicalPolar_compactLift K
  let ρ := tropicalPolar_realDensity f
  have hL : IsCompact L := tropicalPolar_compactLift_compact hK
  have hLD : L ⊆ complexTorus n := tropicalPolar_compactLift_subset K
  have hi : IntegrableOn (tropicalSignedTestDensity ρ (fun _ => 1)) L :=
    ((tropicalPolar_weight_continuousOn (tropicalPolar_realDensity_continuous hf)).mono
      hLD).integrableOn_compact hL
  rw [tropicalPolar_smoothMeasure_weight hf hc, withDensity_apply _ hL.measurableSet,
    Measure.restrict_restrict hL.measurableSet, inter_eq_left.mpr hLD]
  change (∫⁻ z in L, ENNReal.ofReal (tropicalSignedTestDensity ρ (fun _ => 1) z)) < ⊤
  exact (lintegral_ofReal_le_lintegral_enorm _).trans_lt hi.hasFiniteIntegral

private theorem tropicalPolar_smoothMeasure_restrict {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : ConvexOn ℝ univ f) :
    (smoothMeasure (tropicalSmoothDomain n) (fun y => f (tropicalization y))
      (isSmoothPshOn_tropicalSmoothProfile hf hc)).restrict (complexTorus n) =
      smoothMeasure (tropicalSmoothDomain n) (fun y => f (tropicalization y))
        (isSmoothPshOn_tropicalSmoothProfile hf hc) := by
  unfold smoothMeasure
  change ((volume.restrict (complexTorus n)).withDensity
    (fun z => ENNReal.ofReal (smoothDensity (fun y => f (tropicalization y)) z))).restrict
      (complexTorus n) = (volume.restrict (complexTorus n)).withDensity
        (fun z => ENNReal.ofReal (smoothDensity (fun y => f (tropicalization y)) z))
  rw [restrict_withDensity (isOpen_complexTorus n).measurableSet,
    Measure.restrict_restrict (isOpen_complexTorus n).measurableSet, inter_self]

private theorem tropicalPolar_pushforward_finite_compacts {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : ConvexOn ℝ univ f) :
    IsFiniteMeasureOnCompacts (Measure.map tropicalization
      (smoothMeasure (tropicalSmoothDomain n) (fun y => f (tropicalization y))
        (isSmoothPshOn_tropicalSmoothProfile hf hc))) := by
  constructor
  intro K hK
  rw [Measure.map_apply (tropicalPolar_tropicalization_measurable n) hK.measurableSet,
    ← tropicalPolar_smoothMeasure_restrict hf hc,
    Measure.restrict_apply ((tropicalPolar_tropicalization_measurable n) hK.measurableSet)]
  apply lt_of_le_of_lt (measure_mono ?_) (tropicalPolar_compactLift_measure_lt_top hf hc hK)
  intro z hz
  exact tropicalPolar_mem_compactLift hz.2 hz.1

/-- The actual original tropical pushforward equals original Euclidean Alexandrov MA in all dimensions. -/
theorem tropicalization_smoothMeasure_eq_alexandrov {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : ConvexOn ℝ univ f) :
    Measure.map tropicalization (smoothMeasure (tropicalSmoothDomain n)
      (fun y => f (tropicalization y)) (isSmoothPshOn_tropicalSmoothProfile hf hc)) =
      alexandrovMeasure (innerₗ (EuclideanSpace ℝ (Fin n))) volume (fun a => (f a : EReal)) := by
  let : IsFiniteMeasureOnCompacts (Measure.map tropicalization
      (smoothMeasure (tropicalSmoothDomain n) (fun y => f (tropicalization y))
        (isSmoothPshOn_tropicalSmoothProfile hf hc))) :=
    tropicalPolar_pushforward_finite_compacts hf hc
  let : IsLocallyFiniteMeasure
      (alexandrovMeasure (innerₗ (EuclideanSpace ℝ (Fin n))) volume (fun a => (f a : EReal))) :=
    isLocallyFiniteMeasure_alexandrovMeasure_coe _ hc
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro φ
  have hφ : AEStronglyMeasurable (fun a => φ a) (Measure.map tropicalization
      (smoothMeasure (tropicalSmoothDomain n) (fun y => f (tropicalization y))
        (isSmoothPshOn_tropicalSmoothProfile hf hc))) := φ.continuous.aestronglyMeasurable
  rw [integral_map (tropicalPolar_tropicalization_measurable n).aemeasurable
    hφ]
  exact integral_tropicalSmoothMeasure_source_test hf hc φ.continuous φ.hasCompactSupport

/-- The actual original map and compact torus lift, assembled from the
already proved private Borel and compact-geometry producers. -/
theorem exists_compact_tropical_torus_lift {n : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) :
    Measurable (@tropicalization n) ∧
      ∃ L : Set (ComplexModel n), IsCompact L ∧ L ⊆ complexTorus n ∧
        ∀ z ∈ complexTorus n, tropicalization z ∈ K → z ∈ L := by
  refine ⟨tropicalPolar_tropicalization_measurable n, tropicalPolar_compactLift K,
    tropicalPolar_compactLift_compact hK, tropicalPolar_compactLift_subset K, ?_⟩
  intro z hz hT
  exact tropicalPolar_mem_compactLift hz hT

/-- Every original signed real compact test has its actual filled compact
pullback inside the torus; the complete private geometry is reused once. -/
theorem exists_tropical_compact_test_pullback {n : ℕ}
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : Continuous φ)
    (hK : HasCompactSupport φ) :
    ∃ η : ComplexModel n → ℝ, Continuous η ∧ HasCompactSupport η ∧
      tsupport η ⊆ complexTorus n ∧
      ∀ z ∈ complexTorus n, η z = φ (tropicalization z) := by
  refine ⟨tropicalPolar_filledTest φ, tropicalPolar_filledTest_continuous hφ hK,
    tropicalPolar_filledTest_hasCompactSupport hK,
    (tropicalPolar_filledTest_tsupport φ hK).trans (tropicalPolar_compactLift_subset _), ?_⟩
  intro z hz
  exact indicator_of_mem hz _

end SGPT.Toric
