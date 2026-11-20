import SGPT.NPP.LogConcavityDinewFrame
import SGPT.MongeAmpere.LocalMongeAmpereUpperTests
import SGPT.Foundations.Analysis.Pending.MollifierPeanoHessian
import SGPT.Foundations.Analysis.Pending.BedfordTaylorFixedWeight
import SGPT.Foundations.Analysis.PlurisubharmonicAE

/-!
# Upper test functions of Monge–Ampère subsolutions

FPT `prop:bounded-monge-ampere-linear-density`, (1) ⇒ (2): if `u` is a locally bounded
plurisubharmonic function on `Ω ⊆ ℂⁿ` with `(ddᶜu)ⁿ ≥ c · (n!/πⁿ) dV` (`c > 0`), then every quadratic
polynomial `u x + ℓ (y - x) + M (y - x) (y - x)` touching `u` from above at `x` has complex Hessian
`H = complexHessianOfBilin (M + Mᵀ)` positive semidefinite with `det H ≥ c`
(`upperTest_det_ge`). The proof is the comparison principle (S50's
`canonicalBedfordTaylorMeasure_gt_le_smoothMeasure`) against `q + δ‖· - x‖² - δr²/2` on a small ball.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Matrix
open scoped Topology ComplexOrder ContDiff
open TopologicalSpace

namespace SGPT.NPP.LogConcavityDinew

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending.SemiconcaveHessian SGPT.Foundations.Analysis.Pending.ComplexHessianDeterminant
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.MongeAmpere

variable {n : ℕ}

/-- The normalization `n!/πⁿ` of `(ddᶜ ‖z‖²)ⁿ` against Lebesgue measure. -/
def mongeAmpereConst (n : ℕ) : ℝ := (n.factorial : ℝ) / Real.pi ^ n

theorem mongeAmpereConst_pos : 0 < mongeAmpereConst n := by
  unfold mongeAmpereConst; positivity

theorem complexHessianOfBilin_add (A B : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ) :
    complexHessianOfBilin (A + B) = complexHessianOfBilin A + complexHessianOfBilin B := by
  ext j k
  simp only [complexHessianOfBilin, ContinuousLinearMap.add_apply, Matrix.add_apply]
  push_cast
  ring

theorem complexHessianOfBilin_smul (c : ℝ) (A : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ) :
    complexHessianOfBilin (c • A) = (c : ℂ) • complexHessianOfBilin A := by
  ext j k
  simp only [complexHessianOfBilin, ContinuousLinearMap.smul_apply, smul_eq_mul, Matrix.smul_apply]
  push_cast
  ring

theorem complexHessianOfBilin_innerBilin :
    complexHessianOfBilin ((2 : ℝ) • innerBilin n) = 1 := by
  have h := complexHessian_norm_sq (n := n) 0
  rw [← h]
  ext j k
  simp only [complexHessianOfBilin, complexHessian, ContinuousLinearMap.smul_apply, smul_eq_mul,
    innerBilin_apply, realHessian_norm_sq]

/-- The quadratic polynomial of an upper test. -/
def testPoly (c : ℝ) (x : ComplexModel n) (ℓ : ComplexModel n →L[ℝ] ℝ)
    (M : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ) (y : ComplexModel n) : ℝ :=
  c + ℓ (y - x) + M (y - x) (y - x)

theorem contDiff_testPoly (c : ℝ) (x : ComplexModel n) (ℓ : ComplexModel n →L[ℝ] ℝ)
    (M : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ) :
    ContDiff ℝ ∞ (testPoly c x ℓ M) := by
  unfold testPoly
  have h1 : ContDiff ℝ ∞ fun y : ComplexModel n => y - x := contDiff_id.sub contDiff_const
  exact (contDiff_const.add (ℓ.contDiff.comp h1)).add
    (M.isBoundedBilinearMap.contDiff.comp (h1.prodMk h1))

theorem testPoly_eq (c : ℝ) (x : ComplexModel n) (ℓ : ComplexModel n →L[ℝ] ℝ)
    (M : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ) :
    testPoly c x ℓ M = fun z => (c + ℓ (z - x) + (M + M.flip) (z - x) (z - x) / 2) + 0 := by
  funext z
  simp [testPoly, ContinuousLinearMap.flip_apply]
  ring

theorem realHessian_testPoly (c : ℝ) (x : ComplexModel n) (ℓ : ComplexModel n →L[ℝ] ℝ)
    (M : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ) (y a b : ComplexModel n) :
    realHessian (testPoly c x ℓ M) y a b = (M + M.flip) a b := by
  rw [testPoly_eq]
  exact realHessian_quadratic (fun v w => by simp [ContinuousLinearMap.flip_apply, add_comm]) y a b

theorem complexHessian_testPoly (c : ℝ) (x : ComplexModel n) (ℓ : ComplexModel n →L[ℝ] ℝ)
    (M : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ) (y : ComplexModel n) :
    complexHessian (testPoly c x ℓ M) y = complexHessianOfBilin (M + M.flip) := by
  ext j k
  simp only [complexHessian, complexHessianOfBilin, realHessian_testPoly]

theorem leviForm_testPoly (c : ℝ) (x : ComplexModel n) (ℓ : ComplexModel n →L[ℝ] ℝ)
    (M : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ) (y v : ComplexModel n) :
    leviForm (testPoly c x ℓ M) y v = leviFormOfBilin (M + M.flip) v := by
  simp only [leviForm, leviFormOfBilin, realHessian_testPoly]

theorem symm_add_flip (M : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ) (a b : ComplexModel n) :
    (M + M.flip) a b = (M + M.flip) b a := by
  simp [ContinuousLinearMap.flip_apply, add_comm]

theorem leviFormOfBilin_nonneg_of_posSemidef {A : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ}
    (hA : ∀ a b, A a b = A b a) (hpsd : (complexHessianOfBilin A).PosSemidef) (v : ComplexModel n) :
    0 ≤ leviFormOfBilin A v := by
  have h := dotProduct_mulVec_complexHessianOfBilin hA (fun i => star (v i))
  rw [coordCombination_star] at h
  have := hpsd.dotProduct_mulVec_nonneg (fun i => star (v i))
  rw [h] at this
  exact_mod_cast this

/-- **Upper tests of Monge–Ampère subsolutions** (FPT `prop:bounded-monge-ampere-linear-density`,
(1) ⇒ (2)). -/
theorem upperTest_det_ge (hn : 0 < n) {Ω : Opens (ComplexModel n)} {u : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u) {c : ℝ} (hc : 0 < c)
    (hμ : ENNReal.ofReal (mongeAmpereConst n * c) • volume.restrict (Ω : Set (ComplexModel n)) ≤
      canonicalBedfordTaylorMeasure Ω u hu)
    {x : ComplexModel n} (hx : x ∈ Ω) {ℓ : ComplexModel n →L[ℝ] ℝ}
    {M : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ} (htest : IsQuadraticUpperTest u x ℓ M) :
    (complexHessianOfBilin (M + M.flip)).PosSemidef ∧
      c ≤ (complexHessianOfBilin (M + M.flip)).det.re := by
  set q := testPoly (u x) x ℓ M with hq
  set H := complexHessianOfBilin (M + M.flip) with hH
  have hqs : ContDiff ℝ ∞ q := contDiff_testPoly _ _ _ _
  have hpsd : H.PosSemidef := by
    have h := SGPT.MongeAmpere.complexHessian_posSemidef_of_smooth_upper_test hu.1 hx hqs
      (by simp [hq, testPoly]) (htest.mono fun y hy => EReal.coe_le_coe_iff.mpr hy)
    have h' : (complexHessian (testPoly (u x) x ℓ M) x).PosSemidef := h.1
    rw [complexHessian_testPoly] at h'
    exact h'
  refine ⟨hpsd, ?_⟩
  by_contra hdet
  push Not at hdet
  -- a small positive perturbation keeps the determinant below `c`
  have hcont : Continuous fun t : ℝ => (H + (t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).det.re :=
    Complex.continuous_re.comp (continuous_const.add
      ((Complex.continuous_ofReal.smul continuous_const))).matrix_det
  have hev : ∀ᶠ t : ℝ in 𝓝 0, (H + ((t : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).det.re < c :=
    hcont.continuousAt.eventually (gt_mem_nhds (by simpa using hdet))
  obtain ⟨δ₀, hδ₀, hδball⟩ := Metric.eventually_nhds_iff.mp hev
  set δ : ℝ := δ₀ / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  have hdetδ : (H + (δ : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).det.re < c :=
    hδball (by rw [Real.dist_eq, sub_zero, abs_of_pos hδ0]; linarith)
  -- the radius
  obtain ⟨r₀, hr₀, hball⟩ := Metric.eventually_nhds_iff.mp
    (htest.and (Ω.isOpen.mem_nhds hx))
  set r : ℝ := r₀ / 2 with hr
  have hr0 : 0 < r := by positivity
  let Ω' : Opens (ComplexModel n) := ⟨Metric.ball x r, Metric.isOpen_ball⟩
  have hΩ'r₀ : ∀ y ∈ (Ω' : Set (ComplexModel n)), dist y x < r₀ := fun y hy => by
    have : dist y x < r := hy
    linarith
  have hΩ'Ω : Ω' ≤ Ω := fun y hy => (hball (hΩ'r₀ y hy)).2
  have hu' : IsLocallyBoundedPshOn Ω' u := BedfordTaylor.IsLocallyBoundedPshOn.mono_opens hu hΩ'Ω
  -- the comparison function
  set Mδ : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ := M + δ • innerBilin n with hMδ
  set b : ComplexModel n → ℝ := fun y => testPoly (u x) x ℓ Mδ y - δ * r ^ 2 / 2 with hb
  have hHδ : complexHessianOfBilin (Mδ + Mδ.flip) = H + (δ : ℂ) • 1 := by
    have e : Mδ + Mδ.flip = (M + M.flip) + δ • ((2 : ℝ) • innerBilin n) := by
      ext a b'
      simp [hMδ, ContinuousLinearMap.flip_apply, innerBilin_apply, real_inner_comm]
      ring
    rw [e, complexHessianOfBilin_add, complexHessianOfBilin_smul, complexHessianOfBilin_innerBilin]
  have hbs : ContDiff ℝ ∞ b := (contDiff_testPoly _ _ _ _).sub contDiff_const
  have hbH : ∀ y, complexHessian b y = H + (δ : ℂ) • 1 := by
    intro y
    have : b = testPoly (u x) x ℓ Mδ + fun _ => -(δ * r ^ 2 / 2) := by
      funext y; simp [hb, sub_eq_add_neg]
    rw [this, complexHessian_add ((contDiff_testPoly _ _ _ _).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt
      contDiff_const.contDiffAt, complexHessian_testPoly, hHδ]
    simp
  have hHδpsd : (H + (δ : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef :=
    (DeterminantTraceInf.posDef_add_smul_one hpsd hδ0).posSemidef
  have hbpsh : IsSmoothPshOn Ω' b := by
    refine ⟨hbs.contDiffOn, ?_, fun y _ => (hbH y).symm ▸ hHδpsd⟩
    refine plurisubharmonicOn_of_levi_nonneg (hbs.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) Ω'.isOpen fun y _ v => ?_
    have : b = testPoly (u x) x ℓ Mδ + fun _ => -(δ * r ^ 2 / 2) := by
      funext y; simp [hb, sub_eq_add_neg]
    rw [this, leviForm_add ((contDiff_testPoly _ _ _ _).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt
      contDiff_const.contDiffAt, leviForm_testPoly, leviForm_const, add_zero]
    exact leviFormOfBilin_nonneg_of_posSemidef (symm_add_flip Mδ) (hHδ ▸ hHδpsd) v
  -- the comparison principle
  set K : Set (ComplexModel n) := Metric.closedBall x (3 * r / 4) with hK
  have hKc : IsCompact K := isCompact_closedBall _ _
  have hKΩ' : K ⊆ Ω' := Metric.closedBall_subset_ball (by linarith)
  have houtside : ∀ z ∈ Ω', z ∉ K → u z ≤ b z := by
    intro z hz hzK
    have hzK' : 3 * r / 4 < dist z x := by
      simpa [hK, Metric.mem_closedBall, not_le] using hzK
    have hux := (hball (hΩ'r₀ z hz)).1
    have h1 : b z = testPoly (u x) x ℓ M z + δ * ‖z - x‖ ^ 2 - δ * r ^ 2 / 2 := by
      simp only [hb, testPoly, hMδ, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        smul_eq_mul, innerBilin_apply, real_inner_self_eq_norm_sq]
      ring
    have h2 : δ * r ^ 2 / 2 ≤ δ * ‖z - x‖ ^ 2 := by
      rw [← dist_eq_norm]
      have : (3 * r / 4) ^ 2 ≤ dist z x ^ 2 := pow_le_pow_left₀ (by positivity) hzK'.le 2
      nlinarith
    rw [h1]
    have : u z ≤ testPoly (u x) x ℓ M z := hux
    linarith
  have hcomp := SGPT.MongeAmpere.canonicalBedfordTaylorMeasure_gt_le_smoothMeasure hn hu' hbpsh
    hKc hKΩ' houtside
  set S : Set (ComplexModel n) := {z | z ∈ Ω' ∧ b z < u z} with hS
  have hSΩ' : S ⊆ Ω' := fun z hz => hz.1
  have hSm : MeasurableSet S := by
    have hsc : UpperSemicontinuousOn (fun z : Ω' => (u z : EReal)) univ :=
      hu'.1.upperSemicontinuousOn.comp continuous_subtype_val.continuousOn (fun z _ => z.property)
    have humE : Measurable (fun z : Ω' => (u z : EReal)) :=
      (upperSemicontinuousOn_univ_iff.mp hsc).measurable
    have hum : Measurable (fun z : Ω' => u z) := by
      simpa only [EReal.toReal_coe] using humE.ereal_toReal
    have hbm : Measurable (fun z : Ω' => b z) :=
      hbs.continuous.measurable.comp measurable_subtype_coe
    have hs := Ω'.isOpen.measurableSet.subtype_image (measurableSet_lt hbm hum)
    convert hs using 1
    ext z
    exact ⟨fun hz => ⟨⟨z, hz.1⟩, hz.2, rfl⟩, fun ⟨w, hw, hwz⟩ => hwz ▸ ⟨w.property, hw⟩⟩
  -- evaluate both sides
  have hsmooth : smoothMeasure Ω' b hbpsh S =
      ENNReal.ofReal (mongeAmpereConst n * (H + (δ : ℂ) • 1).det.re) * volume S := by
    rw [smoothMeasure]
    have : (fun z => ENNReal.ofReal (smoothDensity b z)) =
        fun _ => ENNReal.ofReal (mongeAmpereConst n * (H + (δ : ℂ) • 1).det.re) := by
      funext z; simp [smoothDensity, hbH, mongeAmpereConst]
    rw [this, withDensity_const, Measure.smul_apply, Measure.restrict_apply hSm,
      inter_eq_left.mpr hSΩ', smul_eq_mul]
  have hBT : ENNReal.ofReal (mongeAmpereConst n * c) * volume S ≤
      canonicalBedfordTaylorMeasure Ω' u hu' S := by
    rw [← MongeAmpere.canonicalBedfordTaylorMeasure_restrict hΩ'Ω hu hu',
      Measure.restrict_apply hSm, inter_eq_left.mpr hSΩ']
    have := hμ S
    rwa [Measure.smul_apply, Measure.restrict_apply hSm, inter_eq_left.mpr (hSΩ'.trans hΩ'Ω),
      smul_eq_mul] at this
  have hvol : volume S = 0 := by
    by_contra hS0
    have hSfin : volume S < ⊤ :=
      (measure_mono (hSΩ'.trans Metric.ball_subset_closedBall)).trans_lt
        (isCompact_closedBall x r).measure_lt_top
    have h1 := (hBT.trans hcomp).trans_eq hsmooth
    have h2 := (ENNReal.mul_le_mul_iff_left hS0 hSfin.ne).mp h1
    have h3 := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg mongeAmpereConst_pos.le
      (Complex.nonneg_iff.mp hHδpsd.det_nonneg).1)).mp h2
    have h4 := le_of_mul_le_mul_left h3 mongeAmpereConst_pos
    linarith
  -- almost everywhere comparison
  have hae : ∀ᵐ y ∂volume.restrict (Ω' : Set (ComplexModel n)), (u y : EReal) ≤ (b y : EReal) := by
    rw [ae_restrict_iff' Ω'.isOpen.measurableSet]
    have : ∀ᵐ y ∂volume, y ∉ S := measure_eq_zero_iff_ae_notMem.mp hvol
    filter_upwards [this] with y hyS hyΩ'
    exact EReal.coe_le_coe_iff.mpr (not_lt.mp fun h => hyS ⟨hyΩ', h⟩)
  have hle := PlurisubharmonicOn.le_of_ae_le hu'.1 Ω'.isOpen
    ((continuous_coe_real_ereal.comp hbs.continuous).upperSemicontinuous.upperSemicontinuousOn _)
    volume hae x (Metric.mem_ball_self hr0)
  have hbx : b x = u x - δ * r ^ 2 / 2 := by simp [hb, testPoly]
  have hle' : (u x : EReal) ≤ (b x : EReal) := hle
  rw [hbx, EReal.coe_le_coe_iff] at hle'
  have : 0 < δ * r ^ 2 / 2 := by positivity
  linarith

end SGPT.NPP.LogConcavityDinew
