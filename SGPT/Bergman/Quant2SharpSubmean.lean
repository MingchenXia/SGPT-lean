import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.Complex.MeanValue
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Integral.Pi
import SGPT.Bergman.Quant2SharpLocalCalculus

/-!
# Quant2SharpSubmean

Sub-mean-value inequalities on discs and polydiscs with radial Gaussian weights, and Gaussian integrals on polydiscs.

Support for source `prop:smooth_weak_conv` (sharp upper bound `τ ≤ θ^n_{P_{θ,X}[φ]_I(v)}` for every
weak cluster point `τ` of the Bergman measures). Ported verbatim (modulo module names) from the
previous team's drafts under `wip/RESUME-20261109/KODAIRA-TRANSPORT/` and re-checked.
-/

-- Ported from `wip/RESUME-20261109/KODAIRA-TRANSPORT/ORIGINAL-SMOOTH-WEAK-CONV01/sources/SourceSharpDiskPolar.lean`.
section
set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.SharpLocalUpper
open Complex Real Metric Set MeasureTheory
open scoped ENNReal
/-- Exact nonnegative integral change of variables for the SAME complex disk.
No integrability or Gaussian normalization certificate is an input. The
Jacobian is the true radius, including every curvature sign in later uses. -/
theorem sourceSharp_disk_lintegral_polar (R : ℝ) (f : ℂ → ℝ≥0∞) :
    (∫⁻ z in ball (0 : ℂ) R, f z) =
      ∫⁻ p in Ioo (0 : ℝ) R ×ˢ Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal p.1 * f (Complex.polarCoord.symm p) := by
  let Q := Ioo (0 : ℝ) R ×ˢ Ioo (-Real.pi) Real.pi
  let G := fun p : ℝ × ℝ => ENNReal.ofReal p.1 * f (Complex.polarCoord.symm p)
  have hQ : MeasurableSet Q := measurableSet_Ioo.prod measurableSet_Ioo
  have hsub : Q ⊆ Complex.polarCoord.target := by
    intro p hp
    exact ⟨hp.1.1, hp.2⟩
  calc
    (∫⁻ z in ball (0 : ℂ) R, f z) =
        ∫⁻ z, (ball (0 : ℂ) R).indicator f z :=
      (lintegral_indicator measurableSet_ball f).symm
    _ = ∫⁻ p in Complex.polarCoord.target,
        ENNReal.ofReal p.1 * (ball (0 : ℂ) R).indicator f (Complex.polarCoord.symm p) :=
      (Complex.lintegral_comp_polarCoord_symm _).symm
    _ = ∫⁻ p in Complex.polarCoord.target, Q.indicator G p := by
      apply setLIntegral_congr_fun (isOpen_Ioi.prod isOpen_Ioo).measurableSet
      intro p hp
      have hp0 : 0 < p.1 := hp.1
      have hnorm : Complex.polarCoord.symm p ∈ ball (0 : ℂ) R ↔ p.1 < R := by
        rw [mem_ball, dist_zero_right, norm_polarCoord_symm, abs_of_pos hp0]
      change ENNReal.ofReal p.1 * (ball (0 : ℂ) R).indicator f
        (Complex.polarCoord.symm p) = Q.indicator G p
      by_cases hlt : p.1 < R
      · rw [indicator_of_mem (hnorm.mpr hlt), indicator_of_mem]
        exact ⟨⟨hp0, hlt⟩, hp.2⟩
      · rw [indicator_of_notMem (mt hnorm.mp hlt), mul_zero, indicator_of_notMem]
        intro hmem
        exact hlt hmem.1.2
    _ = ∫⁻ p in Q, G p := by
      rw [setLIntegral_indicator hQ, inter_eq_left.mpr hsub]

end SGPT.Bergman.SharpLocalUpper
end
end

-- Ported from `wip/RESUME-20261109/KODAIRA-TRANSPORT/ORIGINAL-SMOOTH-WEAK-CONV01/sources/SourceSharpCircleSubmean.lean`.
section
set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.SharpLocalUpper
open Complex Real Metric Set
open scoped ComplexConjugate
/-- The angular L² submean needed by the original smooth Bergman sharp upper
producer. Its normalized circle average keeps the exact constant one. -/
theorem sourceSharpCircle_norm_sq_submean {F : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hF : DiffContOnCl ℂ F (ball 0 R)) :
    ‖F 0‖ ^ 2 ≤ circleAverage (fun z => ‖F z‖ ^ 2) 0 R := by
  have hc : ContinuousOn F (sphere 0 R) :=
    hF.continuousOn.mono (by rw [closure_ball _ hR.ne']; exact sphere_subset_closedBall)
  have hi : CircleIntegrable F 0 R := hc.circleIntegrable hR.le
  have hiq : CircleIntegrable (fun z => ‖F z‖ ^ 2) 0 R :=
    (hc.norm.pow 2).circleIntegrable hR.le
  have hic : CircleIntegrable (fun z => (conj (F 0) * F z).re) 0 R :=
    (Complex.continuous_re.comp_continuousOn (hc.const_mul (conj (F 0)))).circleIntegrable hR.le
  have hm : circleAverage F 0 R = F 0 := by
    have hF' : DiffContOnCl ℂ F (ball 0 |R|) := by simpa only [abs_of_pos hR] using hF
    exact hF'.circleAverage
  have hcross : circleAverage (fun z => (conj (F 0) * F z).re) 0 R = ‖F 0‖ ^ 2 := by
    have hmul : CircleIntegrable (fun z => conj (F 0) • F z) 0 R :=
      by simpa only [smul_eq_mul] using (hc.const_mul (conj (F 0))).circleIntegrable hR.le
    rw [show (fun z => (conj (F 0) * F z).re) =
      Complex.reCLM ∘ (fun z => conj (F 0) • F z) from rfl,
      Complex.reCLM.circleAverage_comp_comm hmul, circleAverage_fun_smul, hm]
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp [Complex.mul_re]
  have hn := circleAverage_nonneg_of_nonneg (c := (0 : ℂ)) (R := R)
    (f := fun z => ‖F z - F 0‖ ^ 2) (fun _ _ => sq_nonneg _)
  have hid : (fun z => ‖F z - F 0‖ ^ 2) =
      (fun z => ‖F z‖ ^ 2 + ‖F 0‖ ^ 2 - 2 * (conj (F 0) * F z).re) := by
    funext z
    simpa only [Complex.normSq_eq_norm_sq, mul_comm] using Complex.normSq_sub (F z) (F 0)
  have hi2c : CircleIntegrable (fun z => 2 * (conj (F 0) * F z).re) 0 R := hic.const_mul 2
  have hsum : CircleIntegrable (fun z => ‖F z‖ ^ 2 + ‖F 0‖ ^ 2) 0 R :=
    hiq.add (circleIntegrable_const (‖F 0‖ ^ 2) 0 R)
  rw [hid, circleAverage_fun_sub hsum hi2c,
    circleAverage_fun_add hiq (circleIntegrable_const (‖F 0‖ ^ 2) 0 R), circleAverage_const,
    show (fun z => 2 * (conj (F 0) * F z).re) =
      (fun z => (2 : ℝ) • (conj (F 0) * F z).re) from rfl,
    circleAverage_fun_smul, hcross] at hn
  norm_num only [smul_eq_mul] at hn
  linarith
end SGPT.Bergman.SharpLocalUpper
end
end

-- Ported from `wip/RESUME-20261109/KODAIRA-TRANSPORT/ORIGINAL-SMOOTH-WEAK-CONV01/sources/SourceSharpRadialSubmean.lean`.
section
set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.SharpLocalUpper
open Complex Real Metric Set MeasureTheory
/-- Actual polar radial factor, with every real curvature eigenvalue allowed. -/
def sourceSharpRadialWeight (d r : ℝ) : ℝ :=
  2 * Real.pi * r * Real.exp (-d * r ^ 2)

/-- Integrating the exact angular submean against the positive radial weight.
The technical integrability input is to be manufactured by compact continuity
in the disk consumer; it is not a sharp estimate or a global L² certificate. -/
theorem sourceSharp_radial_submean {F : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hF : DiffContOnCl ℂ F (ball 0 R)) (d : ℝ)
    (hI : IntervalIntegrable
      (fun r => sourceSharpRadialWeight d r * circleAverage (fun z => ‖F z‖ ^ 2) 0 r)
      volume 0 R) :
    ‖F 0‖ ^ 2 * (∫ r in (0 : ℝ)..R, sourceSharpRadialWeight d r) ≤
      ∫ r in (0 : ℝ)..R,
        sourceSharpRadialWeight d r * circleAverage (fun z => ‖F z‖ ^ 2) 0 r := by
  have hw : Continuous (sourceSharpRadialWeight d) := by unfold sourceSharpRadialWeight; fun_prop
  have hleft : IntervalIntegrable (fun r => sourceSharpRadialWeight d r * ‖F 0‖ ^ 2) volume 0 R :=
    (hw.mul continuous_const).intervalIntegrable _ _
  have hm := intervalIntegral.integral_mono_on hR.le hleft hI (fun r hr => ?_)
  · rw [intervalIntegral.integral_mul_const] at hm
    simpa only [mul_comm] using hm
  · have hnonneg : 0 ≤ sourceSharpRadialWeight d r := by
      unfold sourceSharpRadialWeight
      exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hr.1) (Real.exp_pos _).le
    apply mul_le_mul_of_nonneg_left _ hnonneg
    by_cases hr0 : r = 0
    · subst r; simp
    · exact sourceSharpCircle_norm_sq_submean (lt_of_le_of_ne hr.1 (Ne.symm hr0))
        (hF.mono (ball_subset_ball hr.2))

/-- A nonpositive eigenvalue contributes at least the unweighted disk factor.
This is the lower bound forcing the signed/zero branch of the sharp upper
bound to vanish; no positive inverse is applied to that branch. -/
theorem sourceSharp_radial_factor_nonpositive {d R : ℝ} (hd : d ≤ 0) (hR : 0 ≤ R) :
    Real.pi * R ^ 2 ≤ ∫ r in (0 : ℝ)..R, sourceSharpRadialWeight d r := by
  have hw : Continuous (sourceSharpRadialWeight d) := by unfold sourceSharpRadialWeight; fun_prop
  have hbase : Continuous (fun r : ℝ => 2 * Real.pi * r) := by fun_prop
  have hm := intervalIntegral.integral_mono_on (μ := volume) hR (hbase.intervalIntegrable _ _)
    (hw.intervalIntegrable _ _) (fun r hr => ?_)
  · have hid : (∫ r in (0 : ℝ)..R, 2 * Real.pi * r) = Real.pi * R ^ 2 := by
      rw [intervalIntegral.integral_const_mul, integral_id]
      ring
    rw [hid] at hm
    exact hm
  · have hexp : 1 ≤ Real.exp (-d * r ^ 2) := Real.one_le_exp_iff.mpr (mul_nonneg (neg_nonneg.mpr hd) (sq_nonneg r))
    exact (le_mul_of_one_le_right (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hr.1 : 0 ≤ 2 * Real.pi * r) hexp)
end SGPT.Bergman.SharpLocalUpper
end
end

-- Ported from `wip/RESUME-20261109/KODAIRA-TRANSPORT/ORIGINAL-SMOOTH-WEAK-CONV01/sources/SourceSharpCircleRadiusContinuity.lean`.
section
set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.SharpLocalUpper
open Complex Real Metric Set MeasureTheory Filter
open scoped Topology
/-- Compact continuity of the SAME coefficient manufactures radial angular
integrability. No integrability certificate remains a premise of the consumer. -/
theorem sourceSharpCircle_average_continuousOn {F : ℂ → ℂ} {R : ℝ}
    (hF : ContinuousOn F (closedBall 0 R)) :
    ContinuousOn (fun r => circleAverage (fun z => ‖F z‖ ^ 2) 0 r) (Icc 0 R) := by
  let J := Icc (0 : ℝ) R
  have hmap (r : J) (θ : ℝ) : circleMap 0 (r : ℝ) θ ∈ closedBall (0 : ℂ) R := by
    rw [mem_closedBall, dist_zero_right, norm_circleMap_zero, abs_of_nonneg r.property.1]
    exact r.property.2
  have hcθ (r : J) : Continuous (fun θ => ‖F (circleMap 0 (r : ℝ) θ)‖ ^ 2) :=
    ((hF.comp_continuous (continuous_circleMap _ _) (hmap r)).norm.pow 2)
  have hcr (θ : ℝ) : Continuous (fun r : J => ‖F (circleMap 0 (r : ℝ) θ)‖ ^ 2) := by
    apply Continuous.pow _ 2
    apply Continuous.norm
    apply hF.comp_continuous (by fun_prop)
    exact fun r => hmap r θ
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn hF
  let B := max C 0
  have hB : 0 ≤ B := le_max_right _ _
  have hb (r : J) (θ : ℝ) : ‖(‖F (circleMap 0 (r : ℝ) θ)‖ ^ 2 : ℝ)‖ ≤ B ^ 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hle : ‖F (circleMap 0 (r : ℝ) θ)‖ ≤ B :=
      (hC _ (hmap r θ)).trans (le_max_left _ _)
    exact pow_le_pow_left₀ (norm_nonneg _) hle 2
  have hint : Continuous (fun r : J => ∫ θ in (0 : ℝ)..2 * Real.pi,
      ‖F (circleMap 0 (r : ℝ) θ)‖ ^ 2) := by
    apply intervalIntegral.continuous_of_dominated_interval
      (bound := fun _ => B ^ 2)
    · intro r; exact (hcθ r).aestronglyMeasurable.restrict
    · intro r; exact ae_of_all _ (fun θ _ => hb r θ)
    · exact intervalIntegrable_const
    · exact ae_of_all _ (fun θ _ => hcr θ)
  rw [continuousOn_iff_continuous_domRestrict]
  change Continuous (fun r : J => (2 * Real.pi)⁻¹ *
    ∫ θ in (0 : ℝ)..2 * Real.pi, ‖F (circleMap 0 (r : ℝ) θ)‖ ^ 2)
  exact continuous_const.mul hint


/-- The radial submean with its compact integrability premise now discharged
from original holomorphy and continuity. Every real eigenvalue is retained. -/
theorem sourceSharp_radial_submean_of_holomorphic {F : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hF : DiffContOnCl ℂ F (ball 0 R)) (d : ℝ) :
    ‖F 0‖ ^ 2 * (∫ r in (0 : ℝ)..R, sourceSharpRadialWeight d r) ≤
      ∫ r in (0 : ℝ)..R,
        sourceSharpRadialWeight d r * circleAverage (fun z => ‖F z‖ ^ 2) 0 r := by
  apply sourceSharp_radial_submean hR hF d
  have hc : ContinuousOn F (closedBall 0 R) := by
    simpa only [closure_ball _ hR.ne'] using hF.continuousOn
  have hw : Continuous (sourceSharpRadialWeight d) := by
    unfold sourceSharpRadialWeight; fun_prop
  exact (hw.continuousOn.mul (sourceSharpCircle_average_continuousOn hc)).intervalIntegrable_of_Icc hR.le
end SGPT.Bergman.SharpLocalUpper
end
end

-- Ported from `wip/RESUME-20261109/KODAIRA-TRANSPORT/ORIGINAL-SMOOTH-WEAK-CONV01/sources/SourceSharpDiskIntegral.lean`.
section
set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.SharpLocalUpper
open Complex Real Metric Set MeasureTheory
open scoped ENNReal
/-- Exact real integral change of variables for the SAME complex disk.
No integrability or Gaussian normalization certificate is an input. The
Jacobian is the true radius, including every curvature sign in later uses. -/
theorem sourceSharp_disk_integral_polar (R : ℝ) (f : ℂ → ℝ) :
    (∫ z in ball (0 : ℂ) R, f z) =
      ∫ p in Ioo (0 : ℝ) R ×ˢ Ioo (-Real.pi) Real.pi,
        p.1 * f (Complex.polarCoord.symm p) := by
  let Q := Ioo (0 : ℝ) R ×ˢ Ioo (-Real.pi) Real.pi
  let G := fun p : ℝ × ℝ => p.1 * f (Complex.polarCoord.symm p)
  have hQ : MeasurableSet Q := measurableSet_Ioo.prod measurableSet_Ioo
  have hsub : Q ⊆ Complex.polarCoord.target := by
    intro p hp
    exact ⟨hp.1.1, hp.2⟩
  calc
    (∫ z in ball (0 : ℂ) R, f z) =
        ∫ z, (ball (0 : ℂ) R).indicator f z :=
      (integral_indicator measurableSet_ball).symm
    _ = ∫ p in Complex.polarCoord.target,
        p.1 * (ball (0 : ℂ) R).indicator f (Complex.polarCoord.symm p) :=
      (Complex.integral_comp_polarCoord_symm _).symm
    _ = ∫ p in Complex.polarCoord.target, Q.indicator G p := by
      apply setIntegral_congr_fun (isOpen_Ioi.prod isOpen_Ioo).measurableSet
      intro p hp
      have hp0 : 0 < p.1 := hp.1
      have hnorm : Complex.polarCoord.symm p ∈ ball (0 : ℂ) R ↔ p.1 < R := by
        rw [mem_ball, dist_zero_right, norm_polarCoord_symm, abs_of_pos hp0]
      change p.1 * (ball (0 : ℂ) R).indicator f
        (Complex.polarCoord.symm p) = Q.indicator G p
      by_cases hlt : p.1 < R
      · rw [indicator_of_mem (hnorm.mpr hlt), indicator_of_mem]
        exact ⟨⟨hp0, hlt⟩, hp.2⟩
      · rw [indicator_of_notMem (mt hnorm.mp hlt), mul_zero, indicator_of_notMem]
        intro hmem
        exact hlt hmem.1.2
    _ = ∫ p in Q, G p := by
      rw [setIntegral_indicator hQ, inter_eq_right.mpr hsub]

end SGPT.Bergman.SharpLocalUpper
end
end

-- Ported from `wip/RESUME-20261109/KODAIRA-TRANSPORT/ORIGINAL-SMOOTH-WEAK-CONV01/sources/SourceSharpDiskRadialIdentity.lean`.
section
set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.SharpLocalUpper
open Complex Real Metric Set MeasureTheory
/-- Exact disk integral as the actual normalized angular mean and polar
radial factor. Compact continuity supplies Fubini, with no incoming norm bound. -/
theorem sourceSharp_disk_integral_eq_radial {f : ℂ → ℝ} {R : ℝ}
    (hR : 0 < R) (hf : ContinuousOn f (closedBall 0 R)) :
    (∫ z in ball (0 : ℂ) R, f z) =
      ∫ r in (0 : ℝ)..R, 2 * Real.pi * r * circleAverage f 0 r := by
  let K := Icc (0 : ℝ) R ×ˢ Icc (-Real.pi) Real.pi
  let Q := Ioo (0 : ℝ) R ×ˢ Ioo (-Real.pi) Real.pi
  let G := fun p : ℝ × ℝ => p.1 * f (Complex.polarCoord.symm p)
  have hpolar : Continuous (fun p : ℝ × ℝ => Complex.polarCoord.symm p) := by
    simp_rw [Complex.polarCoord_symm_apply]
    fun_prop
  have hmap : MapsTo (fun p : ℝ × ℝ => Complex.polarCoord.symm p) K (closedBall 0 R) := by
    intro p hp
    rw [mem_closedBall, dist_zero_right, norm_polarCoord_symm, abs_of_nonneg hp.1.1]
    exact hp.1.2
  have hc : ContinuousOn G K :=
    continuous_fst.continuousOn.mul (hf.comp hpolar.continuousOn hmap)
  have hiK : IntegrableOn G K := hc.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hi : IntegrableOn G Q (volume.prod volume) := by
    simpa only [← Measure.volume_eq_prod] using
      hiK.mono_set (Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  have hcoord (r θ : ℝ) : Complex.polarCoord.symm (r, θ) = circleMap 0 r θ := by
    apply Complex.ext <;> simp [Complex.polarCoord_symm_apply, circleMap_zero_re, circleMap_zero_im, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  have hangle (r : ℝ) : (∫ θ in Ioo (-Real.pi) Real.pi,
      f (Complex.polarCoord.symm (r, θ))) = 2 * Real.pi * circleAverage f 0 r := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
    simp_rw [hcoord]
    have hper : Function.Periodic (fun θ => f (circleMap 0 r θ)) (2 * Real.pi) :=
      fun θ => congrArg f (periodic_circleMap 0 r θ)
    have hshift := hper.intervalIntegral_add_eq (-Real.pi) 0
    rw [show -Real.pi + 2 * Real.pi = Real.pi by ring, zero_add] at hshift
    rw [hshift, circleAverage, smul_eq_mul]
    field_simp [Real.pi_ne_zero]
  rw [sourceSharp_disk_integral_polar]
  change (∫ p in Q, G p ∂volume.prod volume) = _
  rw [setIntegral_prod G hi, intervalIntegral.integral_of_le hR.le, integral_Ioc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro r _
  change (∫ θ in Ioo (-Real.pi) Real.pi, r * f (Complex.polarCoord.symm (r, θ))) = _
  rw [integral_const_mul, hangle]
  ring
end SGPT.Bergman.SharpLocalUpper
end
end

-- Ported from `wip/RESUME-20261109/KODAIRA-TRANSPORT/ORIGINAL-SMOOTH-WEAK-CONV01/sources/SourceSharpWeightedDiskSubmean.lean`.
section
set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.SharpLocalUpper
open Complex Real Metric Set MeasureTheory
/-- A radial Gaussian is constant on the exact circle; this identity allows
all signed eigenvalues and retains the true angular normalization. -/
theorem sourceSharp_circle_gaussian_factor (F : ℂ → ℂ) (d r : ℝ) :
    circleAverage (fun z => ‖F z‖ ^ 2 * Real.exp (-d * ‖z‖ ^ 2)) 0 r =
      Real.exp (-d * r ^ 2) * circleAverage (fun z => ‖F z‖ ^ 2) 0 r := by
  have heq : circleAverage (fun z => ‖F z‖ ^ 2 * Real.exp (-d * ‖z‖ ^ 2)) 0 r =
      circleAverage (fun z => Real.exp (-d * r ^ 2) • ‖F z‖ ^ 2) 0 r := by
    apply circleAverage_congr_sphere
    intro z hz
    dsimp only
    have hn : ‖z‖ = |r| := by simpa only [mem_sphere, dist_zero_right] using hz
    rw [hn, sq_abs, smul_eq_mul, mul_comm]
  rw [heq, circleAverage_fun_smul, smul_eq_mul]

/-- The actual disk Gaussian mass equals the polar radial factor. This is a
proved measure identity, not a supplied Gaussian-mass certificate. -/
theorem sourceSharp_disk_gaussian_eq_radial (d : ℝ) {R : ℝ} (hR : 0 < R) :
    (∫ z in ball (0 : ℂ) R, Real.exp (-d * ‖z‖ ^ 2)) =
      ∫ r in (0 : ℝ)..R, sourceSharpRadialWeight d r := by
  have hc : Continuous (fun z : ℂ => Real.exp (-d * ‖z‖ ^ 2)) := by fun_prop
  rw [sourceSharp_disk_integral_eq_radial hR hc.continuousOn]
  apply intervalIntegral.integral_congr
  intro r _
  dsimp only
  have h := sourceSharp_circle_gaussian_factor (fun _ => (1 : ℂ)) d r
  simp only [norm_one, one_pow, one_mul, circleAverage_const, mul_one] at h
  rw [h]
  rfl

/-- Exact constant-one Gaussian weighted disk submean for the original
Berman upper producer. No eigenvalue sign, sharp bound, maximizing function,
or integrability conclusion is assumed. -/
theorem sourceSharp_weighted_disk_submean {F : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hF : DiffContOnCl ℂ F (ball 0 R)) (d : ℝ) :
    ‖F 0‖ ^ 2 * (∫ z in ball (0 : ℂ) R, Real.exp (-d * ‖z‖ ^ 2)) ≤
      ∫ z in ball (0 : ℂ) R, ‖F z‖ ^ 2 * Real.exp (-d * ‖z‖ ^ 2) := by
  have hcF : ContinuousOn F (closedBall 0 R) := by
    simpa only [closure_ball _ hR.ne'] using hF.continuousOn
  have hcW : ContinuousOn (fun z => ‖F z‖ ^ 2 * Real.exp (-d * ‖z‖ ^ 2))
      (closedBall 0 R) :=
    (hcF.norm.pow 2).mul (by fun_prop)
  rw [sourceSharp_disk_gaussian_eq_radial d hR,
    sourceSharp_disk_integral_eq_radial hR hcW]
  have hid : (∫ r in (0 : ℝ)..R,
      2 * Real.pi * r * circleAverage (fun z => ‖F z‖ ^ 2 * Real.exp (-d * ‖z‖ ^ 2)) 0 r) =
      ∫ r in (0 : ℝ)..R,
        sourceSharpRadialWeight d r * circleAverage (fun z => ‖F z‖ ^ 2) 0 r := by
    apply intervalIntegral.integral_congr
    intro r _
    dsimp only
    rw [sourceSharp_circle_gaussian_factor]
    unfold sourceSharpRadialWeight
    ring
  rw [hid]
  exact sourceSharp_radial_submean_of_holomorphic hR hF d
end SGPT.Bergman.SharpLocalUpper
end
end

-- Ported from `wip/RESUME-20261109/KODAIRA-TRANSPORT/ORIGINAL-SMOOTH-WEAK-CONV01/sources/SourceSharpPolydiscSlices.lean`.
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Bergman.SharpLocalUpper
open Complex Real Metric Set
/-- In the existing Pi norm, a polydisc splits into its actual first disk
and remaining polydisc. No new carrier is introduced. -/
theorem sourceSharp_finCons_mem_ball {n : ℕ} {R : ℝ} (hR : 0 < R)
    (s : ℂ) (z : Fin n → ℂ) :
    Fin.cons (α := fun _ : Fin (n+1) => ℂ) s z ∈ ball (0 : Fin (n+1) → ℂ) R ↔
      s ∈ ball (0 : ℂ) R ∧ z ∈ ball (0 : Fin n → ℂ) R := by
  simp only [mem_ball, dist_zero_right, pi_norm_lt_iff hR,
    Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ]

theorem sourceSharp_finCons_mem_closedBall {n : ℕ} {R : ℝ} (hR : 0 ≤ R)
    (s : ℂ) (z : Fin n → ℂ) :
    Fin.cons (α := fun _ : Fin (n+1) => ℂ) s z ∈ closedBall (0 : Fin (n+1) → ℂ) R ↔
      s ∈ closedBall (0 : ℂ) R ∧ z ∈ closedBall (0 : Fin n → ℂ) R := by
  simp only [mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hR,
    Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ]

/-- Original joint holomorphy manufactures the remaining-coordinate slice. -/
theorem sourceSharp_polydisc_tail_holomorphic {n : ℕ} {R : ℝ} (hR : 0 < R)
    {F : (Fin (n+1) → ℂ) → ℂ} (hF : DiffContOnCl ℂ F (ball 0 R))
    {s : ℂ} (hs : s ∈ ball (0 : ℂ) R) :
    DiffContOnCl ℂ (fun z : Fin n → ℂ => F (Fin.cons (α := fun _ : Fin (n+1) => ℂ) s z)) (ball 0 R) := by
  have hd : Differentiable ℂ (fun z : Fin n → ℂ => Fin.cons (α := fun _ : Fin (n+1) => ℂ) s z) := by
    apply differentiable_pi.mpr
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [Fin.cons_zero] using
        (differentiable_const s : Differentiable ℂ (fun _ : Fin n → ℂ => s))
    · simpa only [Fin.cons_succ] using (differentiable_apply j :
        Differentiable ℂ (fun z : Fin n → ℂ => z j))

  exact hF.comp hd.diffContOnCl (fun z hz => (sourceSharp_finCons_mem_ball hR s z).mpr ⟨hs,hz⟩)

/-- Original joint holomorphy manufactures the first-coordinate disk slice. -/
theorem sourceSharp_polydisc_head_holomorphic {n : ℕ} {R : ℝ} (hR : 0 < R)
    {F : (Fin (n+1) → ℂ) → ℂ} (hF : DiffContOnCl ℂ F (ball 0 R))
    {z : Fin n → ℂ} (hz : z ∈ ball (0 : Fin n → ℂ) R) :
    DiffContOnCl ℂ (fun s : ℂ => F (Fin.cons (α := fun _ : Fin (n+1) => ℂ) s z)) (ball 0 R) := by
  have hd : Differentiable ℂ (fun s : ℂ => Fin.cons (α := fun _ : Fin (n+1) => ℂ) s z) := by
    apply differentiable_pi.mpr
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero]
      exact differentiable_id
    · simpa only [Fin.cons_succ] using
        (differentiable_const (z j) : Differentiable ℂ (fun _ : ℂ => z j))

  exact hF.comp hd.diffContOnCl (fun s hs => (sourceSharp_finCons_mem_ball hR s z).mpr ⟨hs,hz⟩)
end SGPT.Bergman.SharpLocalUpper
end
end

-- Ported from `wip/RESUME-20261109/KODAIRA-TRANSPORT/runtime/prerequisite-original-sources/SourceActualGaussianIntegral.lean`.
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SGPT.Bergman.SharpLocalUpper

open MeasureTheory Real Complex
open scoped BigOperators

/-- Actual complex Gaussian integrability, from the actual volume-preserving
real-coordinate equivalence and the two real Gaussian factors. -/
theorem sourceComplexGaussian_integrable {b : ℝ} (hb : 0 < b) :
    Integrable (fun z : ℂ => Real.exp (-b * ‖z‖ ^ 2)) := by
  have hprod := (integrable_exp_neg_mul_sq hb).mul_prod (integrable_exp_neg_mul_sq hb)
  have hcomplex := (Complex.volume_preserving_equiv_real_prod.integrable_comp_emb
    Complex.measurableEquivRealProd.measurableEmbedding).2 hprod
  have hfun : (fun z : ℂ => Real.exp (-b * ‖z‖ ^ 2)) =
      (fun z : ℝ × ℝ => Real.exp (-b * z.1 ^ 2) * Real.exp (-b * z.2 ^ 2)) ∘
        Complex.measurableEquivRealProd := by
    funext z
    change Real.exp (-b * ‖z‖ ^ 2) = Real.exp (-b * z.re ^ 2) * Real.exp (-b * z.im ^ 2)
    rw [← Real.exp_add, Complex.sq_norm, Complex.normSq_apply]
    congr 1
    ring
  rw [hfun]
  exact hcomplex

/-- Exact evaluation in actual complex Lebesgue measure. Positivity avoids
confusing the zero-valued undefined Bochner integral with a divergent Gaussian. -/
theorem sourceComplexGaussian_integral {b : ℝ} (hb : 0 < b) :
    (∫ z : ℂ, Real.exp (-b * ‖z‖ ^ 2)) = Real.pi / b := by
  calc
    (∫ z : ℂ, Real.exp (-b * ‖z‖ ^ 2)) =
        ∫ z : ℂ, Real.exp (-b * z.re ^ 2) * Real.exp (-b * z.im ^ 2) := by
      congr 1
      ext z
      rw [← Real.exp_add, Complex.sq_norm, Complex.normSq_apply]
      congr 1
      ring
    _ = ∫ x : ℝ × ℝ, Real.exp (-b * x.1 ^ 2) * Real.exp (-b * x.2 ^ 2) :=
      Complex.volume_preserving_equiv_real_prod.integral_comp'
        (fun x : ℝ × ℝ => Real.exp (-b * x.1 ^ 2) * Real.exp (-b * x.2 ^ 2))
    _ = (Real.sqrt (Real.pi / b)) ^ 2 := by
      change (∫ x : ℝ × ℝ, Real.exp (-b * x.1 ^ 2) * Real.exp (-b * x.2 ^ 2)
        ∂(volume.prod volume)) = _
      rw [integral_prod_mul (fun x : ℝ => Real.exp (-b * x ^ 2))
        (fun x : ℝ => Real.exp (-b * x ^ 2)), integral_gaussian, ← pow_two]
    _ = Real.pi / b := Real.sq_sqrt (div_nonneg Real.pi_pos.le hb.le)

/-- The genuine all-coordinate exponential, including the empty product. -/
def sourceDiagonalGaussian {ι : Type*} [Fintype ι] (b : ι → ℝ) (z : ι → ℂ) : ℝ :=
  Real.exp (-∑ i, b i * ‖z i‖ ^ 2)

theorem sourceDiagonalGaussian_eq_prod {ι : Type*} [Fintype ι]
    (b : ι → ℝ) (z : ι → ℂ) :
    sourceDiagonalGaussian b z = ∏ i, Real.exp (-b i * ‖z i‖ ^ 2) := by
  simp only [sourceDiagonalGaussian, ← Finset.sum_neg_distrib, neg_mul]
  exact Real.exp_sum _ _

/-- Actual integrability on the finite complex product, also dimension zero. -/
theorem sourceDiagonalGaussian_integrable {ι : Type*} [Fintype ι]
    {b : ι → ℝ} (hb : ∀ i, 0 < b i) : Integrable (sourceDiagonalGaussian b) := by
  change Integrable (fun z : ι → ℂ => sourceDiagonalGaussian b z)
  simp_rw [sourceDiagonalGaussian_eq_prod]
  exact Integrable.fintype_prod (fun i => sourceComplexGaussian_integrable (hb i))

/-- Computed finite-dimensional Gaussian normalization. No evaluation or
normalization output is assumed, and the zero-dimensional answer is one. -/
theorem sourceDiagonalGaussian_integral {ι : Type*} [Fintype ι]
    {b : ι → ℝ} (hb : ∀ i, 0 < b i) :
    (∫ z : ι → ℂ, sourceDiagonalGaussian b z) = ∏ i, Real.pi / b i := by
  simp_rw [sourceDiagonalGaussian_eq_prod]
  rw [integral_fintype_prod_volume_eq_prod
    (fun i (z : ℂ) => Real.exp (-b i * ‖z‖ ^ 2))]
  exact Finset.prod_congr rfl (fun i _ => sourceComplexGaussian_integral (hb i))

end SGPT.Bergman.SharpLocalUpper
end
end

-- Ported from `wip/RESUME-20261109/KODAIRA-TRANSPORT/ORIGINAL-SMOOTH-WEAK-CONV01/sources/SourceSharpPolydiscIntegrability.lean`.
section
set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.SharpLocalUpper
open Complex Real Metric Set MeasureTheory
/-- The existing Pi Lebesgue measure restricted to the actual polydisc is
exactly the product of its existing scalar restricted disk measures. -/
theorem sourceSharp_pi_disk_measure {n : ℕ} {R : ℝ} (hR : 0 < R) :
    Measure.pi (fun _ : Fin n => (volume : Measure ℂ).restrict (ball 0 R)) =
      (volume : Measure (Fin n → ℂ)).restrict (ball 0 R) := by
  rw [ball_pi (0 : Fin n → ℂ) hR]
  exact (Measure.restrict_pi_pi (μ := fun _ : Fin n => (volume : Measure ℂ))
    (fun _ => ball 0 R)).symm

/-- Compact original holomorphy manufactures the actual weighted integrability
on the whole finite polydisc, for all real signed eigenvalues. -/
theorem sourceSharp_polydisc_weighted_integrable {n : ℕ} {R : ℝ} (hR : 0 < R)
    {F : (Fin n → ℂ) → ℂ} (hF : DiffContOnCl ℂ F (ball 0 R)) (d : Fin n → ℝ) :
    Integrable (fun z => ‖F z‖ ^ 2 * sourceDiagonalGaussian d z)
      (Measure.pi (fun _ : Fin n => (volume : Measure ℂ).restrict (ball 0 R))) := by
  rw [sourceSharp_pi_disk_measure hR]
  have hg : Continuous (sourceDiagonalGaussian d) := by
    unfold sourceDiagonalGaussian
    fun_prop
  exact ((hF.continuousOn_ball.norm.pow 2).mul hg.continuousOn).integrableOn_compact
    (isCompact_closedBall (0 : Fin n → ℂ) R) |>.mono_set ball_subset_closedBall

/-- Exact existing finite-product measure equivalence supplies actual
integrability after the true first-coordinate split. -/
theorem sourceSharp_polydisc_split_integrable {n : ℕ} {R : ℝ} (hR : 0 < R)
    {F : (Fin (n+1) → ℂ) → ℂ} (hF : DiffContOnCl ℂ F (ball 0 R)) (d : Fin (n+1) → ℝ) :
    Integrable (fun p : ℂ × (Fin n → ℂ) =>
      ‖F (Fin.cons p.1 p.2)‖ ^ 2 * sourceDiagonalGaussian d (Fin.cons p.1 p.2))
      (((volume : Measure ℂ).restrict (ball 0 R)).prod
        (Measure.pi (fun _ : Fin n => (volume : Measure ℂ).restrict (ball 0 R)))) := by
  let μ := fun _ : Fin (n+1) => (volume : Measure ℂ).restrict (ball 0 R)
  have h := ((measurePreserving_piFinSuccAbove μ 0).symm).integrable_comp_emb
    (MeasurableEquiv.measurableEmbedding _) |>.2 (sourceSharp_polydisc_weighted_integrable hR hF d)
  simpa only [μ, Function.comp_def, MeasurableEquiv.piFinSuccAbove_symm_apply,
    Fin.insertNthEquiv, Fin.insertNth_zero, Fin.zero_succAbove, Equiv.coe_fn_mk, cast_eq] using h
end SGPT.Bergman.SharpLocalUpper
end
end

-- Ported from `wip/RESUME-20261109/KODAIRA-TRANSPORT/ORIGINAL-SMOOTH-WEAK-CONV01/sources/SourceSharpWeightedPolydiscSubmean.lean`.
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Bergman.SharpLocalUpper
open Complex Real Metric Set MeasureTheory
open scoped BigOperators

theorem sourceSharp_diagonalGaussian_finCons {n : ℕ} (d : Fin (n+1) → ℝ)
    (s : ℂ) (z : Fin n → ℂ) :
    sourceDiagonalGaussian d (Fin.cons s z) =
      Real.exp (-d 0 * ‖s‖ ^ 2) * sourceDiagonalGaussian (fun j => d j.succ) z := by
  simp only [sourceDiagonalGaussian_eq_prod, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]

/-- Exact finite-product Gaussian submean from original holomorphy. All real
signed eigenvalues and the actual zero-dimensional empty product are retained.
No incoming sharp estimate, selected family or integrability output is assumed. -/
theorem sourceSharp_polydisc_submean_product :
    ∀ n : ℕ, ∀ {R : ℝ} (_hR : 0 < R) {F : (Fin n → ℂ) → ℂ},
      DiffContOnCl ℂ F (ball 0 R) → ∀ d : Fin n → ℝ,
      ‖F 0‖ ^ 2 * (∏ j, ∫ s in ball (0 : ℂ) R, Real.exp (-d j * ‖s‖ ^ 2)) ≤
        ∫ z, ‖F z‖ ^ 2 * sourceDiagonalGaussian d z
          ∂Measure.pi (fun _ : Fin n => (volume : Measure ℂ).restrict (ball 0 R)) := by
  intro n
  induction n with
  | zero =>
      intro R hR F hF d
      have hc : (fun z : Fin 0 → ℂ => ‖F z‖ ^ 2) = (fun _ => ‖F 0‖ ^ 2) := by
        funext z
        rw [Subsingleton.elim z (0 : Fin 0 → ℂ)]
      simp only [sourceDiagonalGaussian, Finset.univ_eq_empty, Finset.sum_empty,
        Finset.prod_empty, neg_zero, Real.exp_zero, mul_one]
      rw [hc, integral_const]
      simp [measureReal_def, Measure.pi_empty_univ]
  | succ n ih =>
      intro R hR F hF d
      let μ : Measure ℂ := volume.restrict (ball 0 R)
      let ν : Measure (Fin n → ℂ) := Measure.pi (fun _ : Fin n => μ)
      let dt : Fin n → ℝ := fun j => d j.succ
      let wt : (Fin n → ℂ) → ℝ := sourceDiagonalGaussian dt
      let w0 : ℂ → ℝ := fun s => Real.exp (-d 0 * ‖s‖ ^ 2)
      let m0 : ℝ := ∫ s, w0 s ∂μ
      let Pt : ℝ := ∏ j : Fin n, ∫ s in ball (0 : ℂ) R, Real.exp (-dt j * ‖s‖ ^ 2)
      let J : ℂ × (Fin n → ℂ) → ℝ := fun p =>
        (‖F (Fin.cons p.1 p.2)‖ ^ 2 * w0 p.1) * wt p.2
      have hJfun : (fun p : ℂ × (Fin n → ℂ) =>
          ‖F (Fin.cons p.1 p.2)‖ ^ 2 * sourceDiagonalGaussian d (Fin.cons p.1 p.2)) = J := by
        funext p
        rw [sourceSharp_diagonalGaussian_finCons]
        dsimp [J, w0, wt, dt]
        ring
      have hJ : Integrable J (μ.prod ν) := by
        rw [← hJfun]
        exact sourceSharp_polydisc_split_integrable hR hF d
      have hm0 : 0 ≤ m0 := integral_nonneg (fun s => (Real.exp_pos _).le)
      have hzero : (0 : ℂ) ∈ ball (0 : ℂ) R := by simpa using hR
      have hF0 := sourceSharp_polydisc_tail_holomorphic hR hF hzero
      have hz0 : Fin.cons (α := fun _ : Fin (n+1) => ℂ) (0 : ℂ) (0 : Fin n → ℂ) = 0 := by
        funext i
        exact Fin.cases rfl (fun _ => rfl) i
      have htail : ‖F 0‖ ^ 2 * Pt ≤
          ∫ z, ‖F (Fin.cons 0 z)‖ ^ 2 * wt z ∂ν := by
        simpa only [hz0] using ih hR hF0 dt
      have hi0 : Integrable (fun z => ‖F (Fin.cons 0 z)‖ ^ 2 * wt z) ν :=
        sourceSharp_polydisc_weighted_integrable hR hF0 dt
      have hae : ∀ᵐ z ∂ν, z ∈ ball (0 : Fin n → ℂ) R := by
        dsimp [ν, μ]
        rw [sourceSharp_pi_disk_measure hR]
        exact ae_restrict_mem measurableSet_ball
      have hbound : m0 * (∫ z, ‖F (Fin.cons 0 z)‖ ^ 2 * wt z ∂ν) ≤
          ∫ z, ∫ s, J (s,z) ∂μ ∂ν := by
        have hb := integral_mono_ae (hi0.const_mul m0) hJ.integral_prod_right
          (hae.mono (fun z hz => ?_))
        · simpa only [integral_const_mul] using hb
        · have hs := sourceSharp_weighted_disk_submean hR
            (sourceSharp_polydisc_head_holomorphic hR hF hz) (d 0)
          change ‖F (Fin.cons 0 z)‖ ^ 2 * m0 ≤
            ∫ s, ‖F (Fin.cons s z)‖ ^ 2 * w0 s ∂μ at hs
          have hw : 0 ≤ wt z := (Real.exp_pos _).le
          have hs' := mul_le_mul_of_nonneg_right hs hw
          change m0 * (‖F (Fin.cons 0 z)‖ ^ 2 * wt z) ≤
            ∫ s, (‖F (Fin.cons s z)‖ ^ 2 * w0 s) * wt z ∂μ
          rw [integral_mul_const]
          simpa only [mul_comm, mul_left_comm, mul_assoc] using hs'
      have hfull : (∫ z : Fin (n+1) → ℂ, ‖F z‖ ^ 2 * sourceDiagonalGaussian d z
          ∂Measure.pi (fun _ : Fin (n+1) => μ)) = ∫ z, ∫ s, J (s,z) ∂μ ∂ν := by
        calc
          _ = ∫ p : ℂ × (Fin n → ℂ),
              ‖F (Fin.cons p.1 p.2)‖ ^ 2 * sourceDiagonalGaussian d (Fin.cons p.1 p.2)
              ∂μ.prod ν := by
            rw [← ((measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) 0).symm).integral_comp']
            simp only [MeasurableEquiv.piFinSuccAbove_symm_apply,
              Fin.insertNthEquiv, Fin.insertNth_zero, Fin.zero_succAbove, Equiv.coe_fn_mk, cast_eq]
            rfl
          _ = ∫ p, J p ∂μ.prod ν := by rw [hJfun]
          _ = ∫ z, ∫ s, J (s,z) ∂μ ∂ν := integral_prod_symm J hJ
      rw [Fin.prod_univ_succ]
      change ‖F 0‖ ^ 2 * (m0 * Pt) ≤ _
      calc
        _ = m0 * (‖F 0‖ ^ 2 * Pt) := by ring
        _ ≤ m0 * (∫ z, ‖F (Fin.cons 0 z)‖ ^ 2 * wt z ∂ν) := mul_le_mul_of_nonneg_left htail hm0
        _ ≤ ∫ z, ∫ s, J (s,z) ∂μ ∂ν := hbound
        _ = _ := hfull.symm
end SGPT.Bergman.SharpLocalUpper
end
end

-- Ported from `wip/RESUME-20261109/KODAIRA-TRANSPORT/ORIGINAL-SMOOTH-WEAK-CONV01/sources/SourceSharpPolydiscGaussianMass.lean`.
section
set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.SharpLocalUpper
open Complex Real Metric Set MeasureTheory WithLp
open scoped BigOperators ENNReal
/-- The actual truncated diagonal Gaussian mass is the product of the actual
scalar disk masses. Signed eigenvalues and dimension zero are included. -/
theorem sourceSharp_polydisc_gaussian_mass {n : ℕ} {R : ℝ} (hR : 0 < R) (d : Fin n → ℝ) :
    (∫ z in ball (0 : Fin n → ℂ) R, sourceDiagonalGaussian d z) =
      ∏ j, ∫ s in ball (0 : ℂ) R, Real.exp (-d j * ‖s‖ ^ 2) := by
  rw [← sourceSharp_pi_disk_measure hR]
  simp_rw [sourceDiagonalGaussian_eq_prod]
  exact integral_fin_nat_prod_eq_prod
    (μ := fun _ : Fin n => (volume : Measure ℂ).restrict (ball 0 R))
    (fun j (s : ℂ) => Real.exp (-d j * ‖s‖ ^ 2))

/-- Exact finite-polydisc weighted submean with the literal truncated
Gaussian denominator; every technical integrability input is produced. -/
theorem sourceSharp_weighted_polydisc_submean {n : ℕ} {R : ℝ} (hR : 0 < R)
    {F : (Fin n → ℂ) → ℂ} (hF : DiffContOnCl ℂ F (ball 0 R)) (d : Fin n → ℝ) :
    ‖F 0‖ ^ 2 * (∫ z in ball (0 : Fin n → ℂ) R, sourceDiagonalGaussian d z) ≤
      ∫ z in ball (0 : Fin n → ℂ) R, ‖F z‖ ^ 2 * sourceDiagonalGaussian d z := by
  rw [sourceSharp_polydisc_gaussian_mass hR d, ← sourceSharp_pi_disk_measure hR]
  exact sourceSharp_polydisc_submean_product n hR hF d

/-- The exact coordinate-Haar transport needed by the original chart
consumer, for arbitrary nonnegative densities, with no supplied map equality. -/
theorem sourceSharp_complexModel_lintegral_eq_pi (n : ℕ)
    (f : EuclideanSpace ℂ (Fin n) → ℝ≥0∞) :
    (∫⁻ z, f z) = ∫⁻ z : Fin n → ℂ, f (toLp 2 z) := by
  have h : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin n → ℂ)).symm :=
    sourceSharp_complexModel_ofLp_measurePreserving n
  exact (h.symm.lintegral_comp_emb (MeasurableEquiv.toLp 2 (Fin n → ℂ)).measurableEmbedding f).symm
end SGPT.Bergman.SharpLocalUpper
end
end

-- Ported from `wip/RESUME-20261109/KODAIRA-TRANSPORT/ORIGINAL-SMOOTH-WEAK-CONV01/sources/SourceSharpRescaledPolydiscIntegral.lean`.
section
set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.SharpLocalUpper
open Complex Module WithLp Set MeasureTheory Metric
open scoped ENNReal
/-- The actual Euclidean model volume restricted to the actual closed
coordinate polydisc transports to its original product complex volume. -/
theorem sourceSharp_complexModel_polydisc_lintegral {n : ℕ} (R : ℝ)
    (g : EuclideanSpace ℂ (Fin n) → ℝ≥0∞) :
    (∫⁻ z in (fun w : Fin n → ℂ => toLp 2 w) '' closedBall 0 R, g z) =
      ∫⁻ w in closedBall (0 : Fin n → ℂ) R, g (toLp 2 w) := by
  let T := fun w : Fin n → ℂ => toLp 2 w
  let K := T '' closedBall (0 : Fin n → ℂ) R
  have hT : Continuous T := (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)).symm.continuous
  have hK : MeasurableSet K := ((isCompact_closedBall (0 : Fin n → ℂ) R).image hT).measurableSet
  change (∫⁻ z in K, g z) = _
  rw [← lintegral_indicator hK g, sourceSharp_complexModel_lintegral_eq_pi]
  have hfun : (fun w : Fin n → ℂ => K.indicator g (toLp 2 w)) =
      (closedBall (0 : Fin n → ℂ) R).indicator (fun w => g (toLp 2 w)) := by
    funext w
    by_cases hw : w ∈ closedBall (0 : Fin n → ℂ) R
    · rw [indicator_of_mem (show toLp 2 w ∈ K from ⟨w,hw,rfl⟩), indicator_of_mem hw]
    · have hn : toLp 2 w ∉ K := by
        rintro ⟨v,hv,hvw⟩
        have heq : v = w := (MeasurableEquiv.toLp 2 (Fin n → ℂ)).injective hvw
        exact hw (heq ▸ hv)
      rw [indicator_of_notMem hn, indicator_of_notMem hw]
  rw [hfun, lintegral_indicator measurableSet_closedBall]

/-- Exact original rescaling image integral in product coordinates. The only
spectral datum is the accepted actual S determinant readback; no volume or
Jacobian equality is an incoming field. -/
theorem sourceSharp_rescaled_polydisc_lintegral {n k : ℕ} (hk : 0 < k)
    (a : EuclideanSpace ℂ (Fin n))
    (S : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n))
    (hS : Complex.normSq (LinearMap.det S) = 1) (R : ℝ)
    (g : EuclideanSpace ℂ (Fin n) → ℝ≥0∞) :
    (∫⁻ y in (fun z => a + sourceRescaleRadius k • S z) ''
      ((fun w : Fin n → ℂ => toLp 2 w) '' closedBall 0 R), g y) =
      ∫⁻ w in closedBall (0 : Fin n → ℂ) R,
        ENNReal.ofReal (((k : ℝ) ^ n)⁻¹) * g (a + sourceRescaleRadius k • S (toLp 2 w)) := by
  have hT : Continuous (fun w : Fin n → ℂ => toLp 2 w) :=
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)).symm.continuous
  have hK := ((isCompact_closedBall (0 : Fin n → ℂ) R).image hT).measurableSet
  rw [sourceSharp_rescaled_image_lintegral hk a S hS _ hK,
    sourceSharp_complexModel_polydisc_lintegral]
end SGPT.Bergman.SharpLocalUpper
end
end
