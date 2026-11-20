import SGPT.Foundations.Analysis.FirstPass.MongeAmpere
import SGPT.Foundations.Analysis.Pending.PshConvexCone
import SGPT.Foundations.Analysis.Pending.MinkowskiDeterminant
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

set_option autoImplicit false

/-! Actual normalized smooth Monge–Ampère Minkowski inequalities.
The existing derivative Hessian, genuine disc-PSH condition and measure are
retained. The nonsmooth and global non-pluripolar mass inequalities are separate.
-/

noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ContDiff Topology ComplexOrder MatrixOrder

namespace SGPT.MongeAmpere

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending.MinkowskiDeterminant

variable {n : ℕ} {Ω : Opens (ComplexModel n)}
  {u v : ComplexModel n → ℝ} {a b : ℝ}

/-- Positive combinations manufacture genuine smooth PSH and the exact
coordinate Hessian identity for the same real function. -/
theorem isSmoothPshOn_positiveCombination
    (hu : IsSmoothPshOn Ω u) (hv : IsSmoothPshOn Ω v)
    (ha : 0 < a) (hb : 0 < b) :
    IsSmoothPshOn Ω (a • u + b • v) ∧
      ∀ z ∈ Ω, complexHessian (a • u + b • v) z =
        a • complexHessian u z + b • complexHessian v z := by
  have hH (z : ComplexModel n) (hz : z ∈ Ω) :
      complexHessian (a • u + b • v) z =
        a • complexHessian u z + b • complexHessian v z := by
    have hu2 : ContDiffAt ℝ 2 u z :=
      (hu.1.contDiffAt (Ω.isOpen.mem_nhds hz)).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    have hv2 : ContDiffAt ℝ 2 v z :=
      (hv.1.contDiffAt (Ω.isOpen.mem_nhds hz)).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    rw [complexHessian_add (u := a • u) (v := b • v)
      (hu2.const_smul a) (hv2.const_smul b),
      complexHessian_smul hu2 a, complexHessian_smul hv2 b]
    ext i j
    simp [Complex.real_smul]
  have hp : PlurisubharmonicOn (fun z => ((a • u + b • v) z : EReal)) Ω := by
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, EReal.coe_add,
      EReal.coe_mul] using (hu.2.1.const_mul ha).add (hv.2.1.const_mul hb)
  refine ⟨⟨(hu.1.const_smul a).add (hv.1.const_smul b), hp, ?_⟩, hH⟩
  intro z hz
  rw [hH z hz]
  have hscale (c : ℝ) (hc : 0 ≤ c) (A : Matrix (Fin n) (Fin n) ℂ)
      (hA : A.PosSemidef) : (c • A).PosSemidef := by
    have he : c • A = (c : ℂ) • A := by
      ext i j
      simp [Complex.real_smul]
    rw [he]
    exact hA.smul (by exact_mod_cast hc)
  exact (hscale a ha.le _ (hu.2.2 z hz)).add (hscale b hb.le _ (hv.2.2 z hz))

/-- Minkowski's root inequality for the literal smooth MA density, with
the existing factorial/π normalization and actual derivative Hessians. -/
theorem smoothDensity_positiveCombination_minkowski (hn : 0 < n)
    (hu : IsSmoothPshOn Ω u) (hv : IsSmoothPshOn Ω v)
    (ha : 0 < a) (hb : 0 < b) {z : ComplexModel n} (hz : z ∈ Ω) :
    a * smoothDensity u z ^ ((n : ℝ)⁻¹) +
      b * smoothDensity v z ^ ((n : ℝ)⁻¹) ≤
        smoothDensity (a • u + b • v) z ^ ((n : ℝ)⁻¹) := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have hscale (c : ℝ) (hc : 0 ≤ c) (A : Matrix (Fin n) (Fin n) ℂ)
      (hA : A.PosSemidef) : (c • A).PosSemidef := by
    have he : c • A = (c : ℂ) • A := by
      ext i j
      simp [Complex.real_smul]
    rw [he]
    exact hA.smul (by exact_mod_cast hc)
  have h := rpow_inv_card_re_det_add_le
    (hscale a ha.le _ (hu.2.2 z hz)) (hscale b hb.le _ (hv.2.2 z hz))
  rw [rpow_inv_card_re_det_smul (hu.2.2 z hz) ha.le,
    rpow_inv_card_re_det_smul (hv.2.2 z hz) hb.le] at h
  simp only [Fintype.card_fin] at h
  obtain ⟨hw, hH⟩ := isSmoothPshOn_positiveCombination hu hv ha hb
  rw [← hH z hz] at h
  let κ : ℝ := (n.factorial : ℝ) / Real.pi ^ n
  have hκ : 0 ≤ κ := by dsimp only [κ]; positivity
  change a * (κ * (complexHessian u z).det.re) ^ ((n : ℝ)⁻¹) +
    b * (κ * (complexHessian v z).det.re) ^ ((n : ℝ)⁻¹) ≤
      (κ * (complexHessian (a • u + b • v) z).det.re) ^ ((n : ℝ)⁻¹)
  rw [Real.mul_rpow hκ (re_det_nonneg (hu.2.2 z hz)),
    Real.mul_rpow hκ (re_det_nonneg (hv.2.2 z hz)),
    Real.mul_rpow hκ (re_det_nonneg (hw.2.2 z hz))]
  calc
    _ = κ ^ ((n : ℝ)⁻¹) *
        (a * (complexHessian u z).det.re ^ ((n : ℝ)⁻¹) +
          b * (complexHessian v z).det.re ^ ((n : ℝ)⁻¹)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hκ _)

/-- Component lower bounds for the actual smooth measures produce the
Minkowski lower bound for the same manufactured positive combination. -/
theorem smoothMeasure_positiveCombination_lower_bound (hn : 0 < n)
    (hu : IsSmoothPshOn Ω u) (hv : IsSmoothPshOn Ω v)
    (ha : 0 < a) (hb : 0 < b) {f g : ComplexModel n → ℝ}
    (hf : Measurable f) (hg : Measurable g)
    (hf0 : ∀ z, 0 ≤ f z) (hg0 : ∀ z, 0 ≤ g z)
    (huf : (volume.restrict (Ω : Set (ComplexModel n))).withDensity
      (fun z => ENNReal.ofReal (f z)) ≤ smoothMeasure Ω u hu)
    (hvg : (volume.restrict (Ω : Set (ComplexModel n))).withDensity
      (fun z => ENNReal.ofReal (g z)) ≤ smoothMeasure Ω v hv) :
    (volume.restrict (Ω : Set (ComplexModel n))).withDensity
      (fun z => ENNReal.ofReal
        ((a * f z ^ ((n : ℝ)⁻¹) + b * g z ^ ((n : ℝ)⁻¹)) ^ n)) ≤
      smoothMeasure Ω (a • u + b • v)
        (isSmoothPshOn_positiveCombination hu hv ha hb).1 := by
  let μ : Measure (ComplexModel n) := volume.restrict (Ω : Set (ComplexModel n))
  have hfu : ∀ᵐ z ∂μ, ENNReal.ofReal (f z) ≤ ENNReal.ofReal (smoothDensity u z) := by
    apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite hf.ennreal_ofReal
    intro s hs _
    rw [← withDensity_apply _ hs, ← withDensity_apply _ hs]
    exact Measure.le_iff'.mp huf s
  have hgv : ∀ᵐ z ∂μ, ENNReal.ofReal (g z) ≤ ENNReal.ofReal (smoothDensity v z) := by
    apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite hg.ennreal_ofReal
    intro s hs _
    rw [← withDensity_apply _ hs, ← withDensity_apply _ hs]
    exact Measure.le_iff'.mp hvg s
  change μ.withDensity _ ≤ μ.withDensity _
  apply withDensity_mono
  filter_upwards [hfu, hgv, ae_restrict_mem Ω.isOpen.measurableSet] with z hfz hgz hz
  have hu0 := smoothDensity_nonneg (hu.2.2 z hz)
  have hv0 := smoothDensity_nonneg (hv.2.2 z hz)
  have hw := (isSmoothPshOn_positiveCombination hu hv ha hb).1
  have hw0 := smoothDensity_nonneg (hw.2.2 z hz)
  have hfu' : f z ≤ smoothDensity u z := (ENNReal.ofReal_le_ofReal_iff hu0).mp hfz
  have hgv' : g z ≤ smoothDensity v z := (ENNReal.ofReal_le_ofReal_iff hv0).mp hgz
  have hr : 0 < (n : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hn)
  have hroots : a * f z ^ ((n : ℝ)⁻¹) + b * g z ^ ((n : ℝ)⁻¹) ≤
      a * smoothDensity u z ^ ((n : ℝ)⁻¹) + b * smoothDensity v z ^ ((n : ℝ)⁻¹) :=
    add_le_add
      (mul_le_mul_of_nonneg_left
        ((Real.rpow_le_rpow_iff (hf0 z) hu0 hr).2 hfu') ha.le)
      (mul_le_mul_of_nonneg_left
        ((Real.rpow_le_rpow_iff (hg0 z) hv0 hr).2 hgv') hb.le)
  have hsum0 : 0 ≤ a * f z ^ ((n : ℝ)⁻¹) + b * g z ^ ((n : ℝ)⁻¹) :=
    add_nonneg (mul_nonneg ha.le (Real.rpow_nonneg (hf0 z) _))
      (mul_nonneg hb.le (Real.rpow_nonneg (hg0 z) _))
  have hpower := pow_le_pow_left₀ hsum0
    (hroots.trans (smoothDensity_positiveCombination_minkowski hn hu hv ha hb hz)) n
  rw [Real.rpow_inv_natCast_pow hw0 (Nat.ne_of_gt hn)] at hpower
  exact ENNReal.ofReal_le_ofReal hpower

end SGPT.MongeAmpere
