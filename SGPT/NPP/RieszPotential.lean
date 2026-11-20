import SGPT.BBJ.ProbabilityPshAverage
import SGPT.Foundations.Analysis.LogPole
import SGPT.Foundations.Analysis.PlurisubharmonicPullback
import SGPT.Foundations.Analysis.Pending.PshConvexCone
import SGPT.Foundations.Analysis.FirstPass.ComplexManifold
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import SGPT.Foundations.Analysis.Pending.LelongPoincareOneVariable
import SGPT.Foundations.Analysis.FirstPass.MongeAmpere
import SGPT.Foundations.Analysis.Pending.XiaoPoissonLeviPositivity

/-!
# Logarithmic potentials of bounded measures in the plane

Route for the reverse inequality of source `ex:1Dnpp` (`chapter_npp.tex`) in one variable
(blueprint `claude-rc:log-potential`).  For a finite positive measure `ν` on `ℂ¹ = ComplexModel 1`
and a real level `C`, the *logarithmic potential below the level `C`* is

  `p_ν(z) = C ν(ℂ¹) - ∫ (C - log ‖z - w‖²)⁺ dν(w)`        (`logPotential`),

with the logarithm `log 0 = -∞` (TN's `logNormSq`).  When `log ‖z - w‖² ≤ C` for all `z` in a set
`W` and `ν`-almost every `w`, this is the classical potential `∫ log ‖z - w‖² dν(w)` on `W`.

* `discPshOn_logPotential`: `p_ν` is subharmonic on `W` (an average of the subharmonic kernels
  `log ‖· - w‖²`, through `SGPT.BBJ.discPshOn_probabilityPshAverage`);
* `logPotential_add`: additivity in the measure;
* `logPotential_sub_le_of_le`: removing mass raises the normalized potential
  `p_ν - C ν(ℂ¹)`;
* `logPotential_ge_of_closest`: the closest-point bound — if `ν` is carried by a compact set `A`
  on which `p_ν ≥ -M`, then `p_ν ≥ -M - ν(ℂ¹) log 4` everywhere;
* `integral_log_normSq_sub_mul_leviForm`: the one-variable Lelong--Poincaré formula on `ℂ¹`,
  `∫ log ‖z - w‖² · L_φ(z) dz = π φ(w)` with `L_φ = leviForm φ · e₀ = Δφ/4`, transferred from TN's
  `LelongPoincareOneVariable.integral_log_norm_sub_mul_laplacian` along `ℂ ≃ ℂ¹` (`lineIso`);
* `integral_testLevi_mul_logPotential`: `∫ L_φ · p_ν = π ∫ φ dν` for test functions `φ` on an open
  set on which the kernel stays below the level (Fubini, with the local integrability of
  `log ‖·‖²`, `integrableOn_log_normSq_ball`).
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.NPP.Riesz

open Set Filter MeasureTheory SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ENNReal ContDiff Laplacian Distributions

/-- The deficit `(C - log ‖z - w‖²)⁺ ∈ [0, ∞]` of the logarithmic kernel below the level `C`. -/
def kernelDeficit (C : ℝ) (z w : ComplexModel 1) : ℝ≥0∞ :=
  ((C : EReal) - logNormSq (z - w)).toENNReal

/-- The logarithmic potential of a finite measure `ν`, read below the level `C`:
`p_ν(z) = C ν(ℂ¹) - ∫ (C - log ‖z - w‖²)⁺ dν(w)`. -/
def logPotential (C : ℝ) (ν : Measure (ComplexModel 1)) (z : ComplexModel 1) : EReal :=
  (((ν univ).toReal * C : ℝ) : EReal) - ((∫⁻ w, kernelDeficit C z w ∂ν : ℝ≥0∞) : EReal)

theorem continuous_kernelDeficit (C : ℝ) :
    Continuous (fun p : ComplexModel 1 × ComplexModel 1 => kernelDeficit C p.1 p.2) :=
  (continuous_finiteDeficit C).comp (continuous_logNormSq.comp (continuous_fst.sub continuous_snd))

theorem measurable_kernelDeficit (C : ℝ) :
    Measurable (fun p : ComplexModel 1 × ComplexModel 1 => kernelDeficit C p.1 p.2) :=
  (continuous_kernelDeficit C).measurable

theorem logPotential_le (C : ℝ) (ν : Measure (ComplexModel 1)) (z : ComplexModel 1) :
    logPotential C ν z ≤ (((ν univ).toReal * C : ℝ) : EReal) := by
  have h := EReal.sub_le_sub (le_refl (((ν univ).toReal * C : ℝ) : EReal))
    (EReal.coe_ennreal_nonneg (∫⁻ w, kernelDeficit C z w ∂ν))
  simpa only [logPotential, sub_zero] using h

theorem logPotential_ne_top (C : ℝ) (ν : Measure (ComplexModel 1)) (z : ComplexModel 1) :
    logPotential C ν z ≠ ⊤ :=
  ne_top_of_le_ne_top (EReal.coe_ne_top _) (logPotential_le C ν z)

/-- The potential is `-∞` exactly where the deficit integral is infinite. -/
theorem logPotential_eq_bot_iff (C : ℝ) (ν : Measure (ComplexModel 1)) (z : ComplexModel 1) :
    logPotential C ν z = ⊥ ↔ ∫⁻ w, kernelDeficit C z w ∂ν = ⊤ := by
  constructor
  · intro h
    by_contra hne
    have : logPotential C ν z = (((ν univ).toReal * C -
        (∫⁻ w, kernelDeficit C z w ∂ν).toReal : ℝ) : EReal) := by
      rw [logPotential, EReal.coe_sub, ← EReal.coe_ennreal_toReal hne]
    rw [this] at h
    exact EReal.coe_ne_bot _ h
  · intro h
    rw [logPotential, h, EReal.coe_ennreal_top, EReal.sub_top]

/-- The real form of the potential where the deficit integral is finite. -/
theorem logPotential_eq_coe {C : ℝ} {ν : Measure (ComplexModel 1)} {z : ComplexModel 1}
    (h : ∫⁻ w, kernelDeficit C z w ∂ν ≠ ⊤) :
    logPotential C ν z = (((ν univ).toReal * C -
      (∫⁻ w, kernelDeficit C z w ∂ν).toReal : ℝ) : EReal) := by
  rw [logPotential, EReal.coe_sub, ← EReal.coe_ennreal_toReal h]

/-- The kernel `z ↦ log ‖z - w‖²` is subharmonic on every set. -/
theorem discPshOn_logNormSq_sub (w : ComplexModel 1) (W : Set (ComplexModel 1)) :
    DiscPshOn (fun z => logNormSq (z - w)) W := by
  have h := (discPshOn_logNormSq (H := ComplexModel 1) univ).comp_affine
    (ContinuousLinearMap.id ℂ (ComplexModel 1)) (-w)
  refine (h.mono (subset_univ W)).congr fun z _ => ?_
  simp only [ContinuousLinearMap.coe_id', id_eq, neg_add_eq_sub]

/-- **The logarithmic potential is subharmonic** on every set `W` on which the kernel stays below
the level `C` for `w` in a measurable set `K` carrying `ν`. -/
theorem discPshOn_logPotential {C : ℝ} {ν : Measure (ComplexModel 1)} [IsFiniteMeasure ν]
    {K W : Set (ComplexModel 1)} (hK : MeasurableSet K) (hνK : ν Kᶜ = 0)
    (hCK : ∀ z ∈ W, ∀ w ∈ K, logNormSq (z - w) ≤ (C : EReal)) :
    DiscPshOn (logPotential C ν) W := by
  classical
  by_cases hν : ν univ = 0
  · have h0 : ν = 0 := Measure.measure_univ_eq_zero.mp hν
    subst h0
    refine (discPshOn_const 0 EReal.zero_ne_top W).congr fun z _ => ?_
    simp [logPotential]
  · set M : ℝ≥0∞ := ν univ with hMdef
    have hMtop : M ≠ ⊤ := measure_ne_top ν univ
    set m : ℝ := M.toReal with hmdef
    have hm : 0 < m := ENNReal.toReal_pos hν hMtop
    set μ : Measure (ComplexModel 1) := M⁻¹ • ν with hμdef
    have hμ : IsProbabilityMeasure μ := ⟨by
      simp only [hμdef, Measure.smul_apply, smul_eq_mul]
      exact ENNReal.inv_mul_cancel hν hMtop⟩
    set u : ComplexModel 1 → ComplexModel 1 → EReal :=
      fun w z => if w ∈ K then logNormSq (z - w) else (C : EReal) with hudef
    have hdef : (fun p : ComplexModel 1 × ComplexModel 1 => ((C : EReal) - u p.1 p.2).toENNReal) =
        (K ×ˢ univ).indicator (fun p => kernelDeficit C p.2 p.1) := by
      funext p
      by_cases hp : p.1 ∈ K
      · simp [hudef, hp, kernelDeficit, Set.indicator, mem_prod]
      · simp [hudef, hp, Set.indicator, mem_prod]
    have hmeas : Measurable
        (fun p : ComplexModel 1 × ComplexModel 1 => ((C : EReal) - u p.1 p.2).toENNReal) := by
      rw [hdef]
      exact ((measurable_kernelDeficit C).comp measurable_swap).indicator
        (hK.prod MeasurableSet.univ)
    have hC : ∀ w, ∀ z ∈ W, u w z ≤ (C : EReal) := by
      intro w z hz
      by_cases hw : w ∈ K
      · simpa [hudef, hw] using hCK z hz w hw
      · simp [hudef, hw]
    have hu : ∀ w, DiscPshOn (u w) W := by
      intro w
      by_cases hw : w ∈ K
      · simpa only [hudef, hw, if_true] using discPshOn_logNormSq_sub w W
      · simpa only [hudef, hw, if_false] using discPshOn_const _ (EReal.coe_ne_top C) W
    have havg := SGPT.BBJ.discPshOn_probabilityPshAverage μ C u W hmeas hC hu
    refine (havg.const_mul hm).congr fun z _ => ?_
    -- the averaged deficit is the normalized deficit integral
    have hae : (fun w => ((C : EReal) - u w z).toENNReal) =ᵐ[ν] fun w => kernelDeficit C z w := by
      have : ∀ᵐ w ∂ν, w ∈ K := by
        rw [ae_iff]
        exact hνK
      filter_upwards [this] with w hw
      simp [hudef, hw, kernelDeficit]
    have hint : ∫⁻ w, ((C : EReal) - u w z).toENNReal ∂μ =
        M⁻¹ * ∫⁻ w, kernelDeficit C z w ∂ν := by
      rw [hμdef, lintegral_smul_measure, lintegral_congr_ae hae]
      rfl
    simp only [SGPT.BBJ.probabilityPshAverage, hint, logPotential]
    set X : ℝ≥0∞ := ∫⁻ w, kernelDeficit C z w ∂ν with hX
    by_cases hXtop : X = ⊤
    · have hinvX : M⁻¹ * X = ⊤ := by
        rw [hXtop]
        exact ENNReal.mul_top (ENNReal.inv_ne_zero.mpr hMtop)
      rw [hinvX, hXtop, EReal.coe_ennreal_top, EReal.sub_top, EReal.sub_top,
        EReal.coe_mul_bot_of_pos hm]
    · have hinvX : M⁻¹ * X ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hν) hXtop
      rw [← EReal.coe_ennreal_toReal hinvX, ← EReal.coe_ennreal_toReal hXtop, ← EReal.coe_sub,
        ← EReal.coe_mul, ← EReal.coe_sub]
      congr 1
      rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ← hmdef]
      field_simp

/-! ### Additivity and monotonicity in the measure -/

private theorem coe_add_sub_coe_add (a b : ℝ) (X Y : ℝ≥0∞) :
    ((a + b : ℝ) : EReal) - ((X + Y : ℝ≥0∞) : EReal) =
      ((a : EReal) - (X : EReal)) + ((b : EReal) - (Y : EReal)) := by
  by_cases hX : X = ⊤
  · subst hX
    simp [EReal.sub_top, EReal.bot_add]
  by_cases hY : Y = ⊤
  · subst hY
    simp [EReal.sub_top, EReal.add_bot]
  rw [← EReal.coe_ennreal_toReal hX, ← EReal.coe_ennreal_toReal hY,
    ← EReal.coe_ennreal_toReal (ENNReal.add_ne_top.mpr ⟨hX, hY⟩), ENNReal.toReal_add hX hY]
  simp only [← EReal.coe_sub, ← EReal.coe_add]
  congr 1
  ring

/-- **Additivity** of the potential in the measure. -/
theorem logPotential_add (C : ℝ) (ν₁ ν₂ : Measure (ComplexModel 1)) [IsFiniteMeasure ν₁]
    [IsFiniteMeasure ν₂] (z : ComplexModel 1) :
    logPotential C (ν₁ + ν₂) z = logPotential C ν₁ z + logPotential C ν₂ z := by
  simp only [logPotential, Measure.add_apply, lintegral_add_measure]
  rw [ENNReal.toReal_add (measure_ne_top ν₁ univ) (measure_ne_top ν₂ univ), add_mul]
  exact coe_add_sub_coe_add _ _ _ _

/-- The deficit integral is monotone in the measure. -/
theorem lintegral_kernelDeficit_mono {C : ℝ} {ρ ν : Measure (ComplexModel 1)} (h : ρ ≤ ν)
    (z : ComplexModel 1) :
    ∫⁻ w, kernelDeficit C z w ∂ρ ≤ ∫⁻ w, kernelDeficit C z w ∂ν :=
  lintegral_mono' h le_rfl

/-- A smaller measure has a finite potential wherever the larger one does. -/
theorem logPotential_ne_bot_of_le {C : ℝ} {ρ ν : Measure (ComplexModel 1)} (h : ρ ≤ ν)
    {z : ComplexModel 1} (hz : logPotential C ν z ≠ ⊥) : logPotential C ρ z ≠ ⊥ := by
  rw [Ne, logPotential_eq_bot_iff] at hz ⊢
  exact fun h' => hz (top_le_iff.mp (h' ▸ lintegral_kernelDeficit_mono h z))

/-- A lower bound for the potential from an upper bound of its deficit integral. -/
theorem coe_sub_le_logPotential {C D : ℝ} (hD : 0 ≤ D) {ν : Measure (ComplexModel 1)}
    {z : ComplexModel 1} (h : ∫⁻ w, kernelDeficit C z w ∂ν ≤ ENNReal.ofReal D) :
    (((ν univ).toReal * C - D : ℝ) : EReal) ≤ logPotential C ν z := by
  have hfin : ∫⁻ w, kernelDeficit C z w ∂ν ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
  rw [logPotential_eq_coe hfin, EReal.coe_le_coe_iff]
  have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rw [ENNReal.toReal_ofReal hD] at h1
  linarith

/-- The deficit integral is the real number `C ν(ℂ¹) - p_ν(z)` where the potential is finite. -/
theorem lintegral_kernelDeficit_eq {C : ℝ} {ν : Measure (ComplexModel 1)} {z : ComplexModel 1}
    (hz : logPotential C ν z ≠ ⊥) :
    ∫⁻ w, kernelDeficit C z w ∂ν =
      ENNReal.ofReal ((ν univ).toReal * C - (logPotential C ν z).toReal) := by
  have hfin : ∫⁻ w, kernelDeficit C z w ∂ν ≠ ⊤ := fun h => hz ((logPotential_eq_bot_iff C ν z).mpr h)
  rw [logPotential_eq_coe hfin, EReal.toReal_coe, sub_sub_cancel, ENNReal.ofReal_toReal hfin]

/-! ### The closest-point bound -/

private theorem toENNReal_sub_le_add {C c : ℝ} (hc : 0 ≤ c) {a b : EReal}
    (hab : b ≤ a + (c : EReal)) :
    ((C : EReal) - a).toENNReal ≤ ((C : EReal) - b).toENNReal + ENNReal.ofReal c := by
  induction a using EReal.rec with
  | bot =>
    have hb : b = ⊥ := by simpa using hab
    subst hb
    simp
  | top => simp
  | coe a =>
    induction b using EReal.rec with
    | bot => simp
    | top => exact absurd hab (by rw [← EReal.coe_add]; exact not_le.mpr (EReal.coe_lt_top _))
    | coe b =>
      rw [← EReal.coe_add, EReal.coe_le_coe_iff] at hab
      rw [← EReal.coe_sub, ← EReal.coe_sub, EReal.real_coe_toENNReal, EReal.real_coe_toENNReal]
      calc ENNReal.ofReal (C - a) ≤ ENNReal.ofReal (max (C - b) 0 + c) :=
            ENNReal.ofReal_le_ofReal (by linarith [le_max_left (C - b) 0])
        _ = ENNReal.ofReal (max (C - b) 0) + ENNReal.ofReal c :=
            ENNReal.ofReal_add (le_max_right _ _) hc
        _ = ENNReal.ofReal (C - b) + ENNReal.ofReal c := by
            rw [ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_left zero_le]

/-- The logarithmic kernel loses at most `log 4` when `w` is replaced by a point at most twice as
far. -/
theorem logNormSq_le_add_log_four {x y : ComplexModel 1} (h : ‖x‖ ≤ 2 * ‖y‖) :
    logNormSq x ≤ logNormSq y + ((Real.log 4 : ℝ) : EReal) := by
  have h4 : ((Real.log 4 : ℝ) : EReal) = ENNReal.log (ENNReal.ofReal 4) :=
    (ENNReal.log_ofReal_of_pos (by norm_num)).symm
  rw [h4, add_comm, logNormSq, logNormSq, ← ENNReal.log_mul_add, ← ENNReal.ofReal_mul (by norm_num)]
  refine ENNReal.log_monotone (ENNReal.ofReal_le_ofReal ?_)
  have hx : 0 ≤ ‖x‖ := norm_nonneg x
  nlinarith

/-- **The closest-point bound.**  If `ν` is carried by a nonempty compact set `A` on which the
potential is at least `-M`, then the potential is at least `-M - ν(ℂ¹) log 4` everywhere. -/
theorem logPotential_ge_of_closest {C : ℝ} {ν : Measure (ComplexModel 1)} [IsFiniteMeasure ν]
    {A : Set (ComplexModel 1)} (hA : IsCompact A) (hAne : A.Nonempty) (hνA : ν Aᶜ = 0) {M : ℝ}
    (hM : ∀ y ∈ A, ((-M : ℝ) : EReal) ≤ logPotential C ν y) (z : ComplexModel 1) :
    ((-M - (ν univ).toReal * Real.log 4 : ℝ) : EReal) ≤ logPotential C ν z := by
  obtain ⟨z', hz'A, hz'⟩ := hA.exists_infDist_eq_dist hAne z
  have hfin' : logPotential C ν z' ≠ ⊥ := fun h => by
    have := hM z' hz'A
    rw [h] at this
    exact EReal.coe_ne_bot _ (le_bot_iff.mp this)
  have hdef : ∀ w ∈ A, kernelDeficit C z w ≤ kernelDeficit C z' w + ENNReal.ofReal (Real.log 4) := by
    intro w hw
    refine toENNReal_sub_le_add (Real.log_nonneg (by norm_num)) (logNormSq_le_add_log_four ?_)
    have h1 : dist z z' ≤ dist z w := hz' ▸ Metric.infDist_le_dist_of_mem hw
    have h2 : dist z' w ≤ dist z' z + dist z w := dist_triangle z' z w
    rw [dist_comm z' z] at h2
    rw [← dist_eq_norm, ← dist_eq_norm]
    linarith
  have hae : ∀ᵐ w ∂ν, w ∈ A := by rw [ae_iff]; exact hνA
  have hint : ∫⁻ w, kernelDeficit C z w ∂ν ≤
      ∫⁻ w, kernelDeficit C z' w ∂ν + ENNReal.ofReal (Real.log 4) * ν univ := by
    calc ∫⁻ w, kernelDeficit C z w ∂ν
        ≤ ∫⁻ w, (kernelDeficit C z' w + ENNReal.ofReal (Real.log 4)) ∂ν :=
          lintegral_mono_ae (hae.mono fun w hw => hdef w hw)
      _ = ∫⁻ w, kernelDeficit C z' w ∂ν + ENNReal.ofReal (Real.log 4) * ν univ := by
          rw [lintegral_add_right _ measurable_const, lintegral_const]
  rw [lintegral_kernelDeficit_eq hfin'] at hint
  have hM' : -M ≤ (logPotential C ν z').toReal := by
    have := hM z' hz'A
    rw [← EReal.coe_toReal (logPotential_ne_top C ν z') hfin', EReal.coe_le_coe_iff] at this
    exact this
  have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hD : ∫⁻ w, kernelDeficit C z w ∂ν ≤ ENNReal.ofReal
      ((ν univ).toReal * C - (logPotential C ν z').toReal + Real.log 4 * (ν univ).toReal) := by
    refine hint.trans (le_of_eq ?_)
    have e1 : ENNReal.ofReal (Real.log 4) * ν univ =
        ENNReal.ofReal (Real.log 4 * (ν univ).toReal) := by
      rw [ENNReal.ofReal_mul hlog, ENNReal.ofReal_toReal (measure_ne_top ν univ)]
    have h0 : 0 ≤ (ν univ).toReal * C - (logPotential C ν z').toReal := by
      have := logPotential_le C ν z'
      rw [← EReal.coe_toReal (logPotential_ne_top C ν z') hfin', EReal.coe_le_coe_iff] at this
      linarith
    rw [e1, ← ENNReal.ofReal_add h0 (mul_nonneg hlog ENNReal.toReal_nonneg)]
  have hD0 : 0 ≤ (ν univ).toReal * C - (logPotential C ν z').toReal +
      Real.log 4 * (ν univ).toReal := by
    have := logPotential_le C ν z'
    rw [← EReal.coe_toReal (logPotential_ne_top C ν z') hfin', EReal.coe_le_coe_iff] at this
    nlinarith [ENNReal.toReal_nonneg (a := ν univ)]
  refine le_trans ?_ (coe_sub_le_logPotential hD0 hD)
  rw [EReal.coe_le_coe_iff]
  nlinarith

/-! ### The one-variable Lelong--Poincaré formula on `ℂ¹` -/

/-- `ℂ ≃ ℂ¹` as a real linear isometry. -/
def lineIso : ℂ ≃ₗᵢ[ℝ] ComplexModel 1 where
  toLinearEquiv := (OrthonormalBasis.singleton (Fin 1) ℂ).repr.toLinearEquiv.restrictScalars ℝ
  norm_map' := (OrthonormalBasis.singleton (Fin 1) ℂ).repr.norm_map

theorem lineIso_apply (t : ℂ) : lineIso t = t • FirstPass.MongeAmpere.coordinateVector 0 := by
  ext i
  fin_cases i
  change (OrthonormalBasis.singleton (Fin 1) ℂ).repr t 0 = _
  rw [OrthonormalBasis.singleton_repr]
  simp [FirstPass.MongeAmpere.coordinateVector]

theorem eq_smul_coordinateVector (w : ComplexModel 1) :
    w = w 0 • FirstPass.MongeAmpere.coordinateVector 0 := by
  ext i
  fin_cases i
  simp [FirstPass.MongeAmpere.coordinateVector]

theorem norm_coordinateVector_zero : ‖FirstPass.MongeAmpere.coordinateVector (n := 1) 0‖ = 1 := by
  simp [FirstPass.MongeAmpere.coordinateVector]

/-- **The Lelong--Poincaré formula on `ℂ¹`**: `∫ log ‖z - w‖² · L_φ(z) dz = π φ(w)`, where
`L_φ(z) = leviForm φ z e₀ = Δφ(z)/4` (equivalently `dd^c log ‖· - w‖² = δ_w`). -/
theorem integral_log_normSq_sub_mul_leviForm {φ : ComplexModel 1 → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (w : ComplexModel 1) :
    ∫ z, Real.log (‖z - w‖ ^ 2) * leviForm φ z (FirstPass.MongeAmpere.coordinateVector 0) =
      Real.pi * φ w := by
  have hχe : (fun t : ℂ => φ (0 + t • FirstPass.MongeAmpere.coordinateVector 0)) =
      φ ∘ lineIso := by
    funext t
    simp [lineIso_apply]
  have hχs : ContDiff ℝ ∞ (fun t : ℂ => φ (0 + t • FirstPass.MongeAmpere.coordinateVector 0)) := by
    rw [hχe]
    exact hφ.comp lineIso.toContinuousLinearEquiv.contDiff
  have hχc : HasCompactSupport
      (fun t : ℂ => φ (0 + t • FirstPass.MongeAmpere.coordinateVector 0)) := by
    rw [hχe]
    exact hφc.comp_homeomorph lineIso.toHomeomorph
  have h2 : ContDiff ℝ 2 φ := hφ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hmp : MeasurePreserving lineIso := lineIso.measurePreserving
  have hemb : MeasurableEmbedding lineIso := lineIso.toHomeomorph.measurableEmbedding
  rw [← hmp.integral_comp hemb]
  have hw := eq_smul_coordinateVector w
  have key : ∀ t : ℂ, Real.log (‖lineIso t - w‖ ^ 2) *
      leviForm φ (lineIso t) (FirstPass.MongeAmpere.coordinateVector 0) =
      (1 / 2 : ℝ) * (Real.log ‖t - w 0‖ *
        Δ (fun t : ℂ => φ (0 + t • FirstPass.MongeAmpere.coordinateVector 0)) t) := by
    intro t
    have hL := SGPT.Foundations.Analysis.laplacian_complexLine h2 0
      (FirstPass.MongeAmpere.coordinateVector 0) t
    rw [lineIso_apply]
    have hn : ‖t • FirstPass.MongeAmpere.coordinateVector (n := 1) 0 - w‖ = ‖t - w 0‖ := by
      conv_lhs => rw [hw]
      rw [← sub_smul, norm_smul, norm_coordinateVector_zero, mul_one]
    rw [hn, Real.log_pow, hL]
    simp only [zero_add]
    push_cast
    ring
  simp_rw [key]
  rw [integral_const_mul,
    SGPT.Foundations.Analysis.Pending.LelongPoincareOneVariable.integral_log_norm_sub_mul_laplacian
      hχs hχc (w 0)]
  have : φ (0 + w 0 • FirstPass.MongeAmpere.coordinateVector 0) = φ w := by
    rw [zero_add, ← hw]
  rw [this]
  ring

/-! ### Local integrability of the kernel -/

theorem finrank_complexModel_one : Module.finrank ℝ (ComplexModel 1) = 2 := by
  rw [← lineIso.toLinearEquiv.finrank_eq, Complex.finrank_real_complex]

/-- `log ‖y‖²` is integrable on every ball of `ℂ¹`. -/
theorem integrableOn_log_normSq_ball (R : ℝ) :
    IntegrableOn (fun y : ComplexModel 1 => Real.log (‖y‖ ^ 2)) (Metric.ball 0 R) := by
  have h : IntegrableOn (fun y : ComplexModel 1 => Real.log ‖y‖) (Metric.ball 0 R) := by
    rw [integrableOn_fun_norm_addHaar (volume : Measure (ComplexModel 1)) (f := Real.log),
      finrank_complexModel_one]
    have hfun : (fun y : ℝ => y ^ (2 - 1) • Real.log y) = fun y => y * Real.log y := by
      funext y
      norm_num
    rw [hfun]
    exact (Real.continuous_mul_log.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have h2 : IntegrableOn (fun y : ComplexModel 1 => 2 * Real.log ‖y‖) (Metric.ball 0 R) :=
    Integrable.const_mul h 2
  refine IntegrableOn.congr_fun h2 (fun y _ => ?_) measurableSet_ball
  simp only [Real.log_pow]
  push_cast
  ring

theorem lintegral_log_normSq_ball_lt_top (R : ℝ) :
    ∫⁻ y in Metric.ball (0 : ComplexModel 1) R, ENNReal.ofReal |Real.log (‖y‖ ^ 2)| < ⊤ := by
  have h := (integrableOn_log_normSq_ball R).2
  simpa only [HasFiniteIntegral, ← ofReal_norm, Real.norm_eq_abs] using h

theorem measurable_logKernel :
    Measurable (fun p : ComplexModel 1 × ComplexModel 1 => Real.log (‖p.1 - p.2‖ ^ 2)) :=
  Real.measurable_log.comp ((continuous_fst.sub continuous_snd).norm.pow 2).measurable

/-- Off the diagonal and below the level, the deficit is the real deficit `C - log ‖z - w‖²`. -/
theorem kernelDeficit_eq_ofReal {C : ℝ} {z w : ComplexModel 1} (hzw : z ≠ w) :
    kernelDeficit C z w = ENNReal.ofReal (C - Real.log (‖z - w‖ ^ 2)) := by
  rw [kernelDeficit, logNormSq_of_ne_zero (sub_ne_zero.mpr hzw), ← EReal.coe_sub,
    EReal.real_coe_toENNReal]

theorem kernelDeficit_le_abs {C : ℝ} {z w : ComplexModel 1} (hzw : z ≠ w) :
    kernelDeficit C z w ≤ ENNReal.ofReal |C| + ENNReal.ofReal |Real.log (‖z - w‖ ^ 2)| := by
  rw [kernelDeficit_eq_ofReal hzw, ← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (by linarith [le_abs_self C, neg_abs_le (Real.log (‖z - w‖ ^ 2))])

/-- **A uniform bound for the logarithm on a bounded set.** -/
theorem setLIntegral_log_normSq_sub_le {R : ℝ} {S : Set (ComplexModel 1)} (hSm : MeasurableSet S)
    (hS : S ⊆ Metric.closedBall 0 R) {w : ComplexModel 1} (hw : ‖w‖ ≤ R) :
    ∫⁻ z in S, ENNReal.ofReal |Real.log (‖z - w‖ ^ 2)| ≤
      ∫⁻ y in Metric.ball (0 : ComplexModel 1) (2 * R + 1), ENNReal.ofReal |Real.log (‖y‖ ^ 2)| := by
  set g : ComplexModel 1 → ℝ≥0∞ := fun y => ENNReal.ofReal |Real.log (‖y‖ ^ 2)| with hg
  calc ∫⁻ z in S, g (z - w)
      = ∫⁻ z in S, (Metric.ball (0 : ComplexModel 1) (2 * R + 1)).indicator g (z - w) := by
        refine setLIntegral_congr_fun hSm fun z hz => ?_
        have hz' := hS hz
        rw [Metric.mem_closedBall, dist_zero_right] at hz'
        have : z - w ∈ Metric.ball (0 : ComplexModel 1) (2 * R + 1) := by
          rw [Metric.mem_ball, dist_zero_right]
          calc ‖z - w‖ ≤ ‖z‖ + ‖w‖ := norm_sub_le z w
            _ < 2 * R + 1 := by linarith
        rw [Set.indicator_of_mem this]
    _ ≤ ∫⁻ z, (Metric.ball (0 : ComplexModel 1) (2 * R + 1)).indicator g (z - w) :=
        setLIntegral_le_lintegral _ _
    _ = ∫⁻ y, (Metric.ball (0 : ComplexModel 1) (2 * R + 1)).indicator g y :=
        lintegral_sub_right_eq_self _ w
    _ = ∫⁻ y in Metric.ball (0 : ComplexModel 1) (2 * R + 1), g y :=
        lintegral_indicator measurableSet_ball _

/-- **A uniform bound for the deficit on a bounded set.** -/
theorem setLIntegral_kernelDeficit_le {C R : ℝ} {S : Set (ComplexModel 1)} (hSm : MeasurableSet S)
    (hS : S ⊆ Metric.closedBall 0 R) {w : ComplexModel 1} (hw : ‖w‖ ≤ R) :
    ∫⁻ z in S, kernelDeficit C z w ≤ ENNReal.ofReal |C| * volume S +
      ∫⁻ y in Metric.ball (0 : ComplexModel 1) (2 * R + 1), ENNReal.ofReal |Real.log (‖y‖ ^ 2)| := by
  have hnull : volume ({w} : Set (ComplexModel 1)) = 0 := measure_singleton w
  have hae : ∀ᵐ z ∂(volume.restrict S), kernelDeficit C z w ≤
      ENNReal.ofReal |C| + ENNReal.ofReal |Real.log (‖z - w‖ ^ 2)| := by
    have : ∀ᵐ z ∂(volume : Measure (ComplexModel 1)), z ≠ w := by
      rw [ae_iff]
      simp [hnull]
    filter_upwards [ae_restrict_of_ae this] with z hz
    exact kernelDeficit_le_abs hz
  calc ∫⁻ z in S, kernelDeficit C z w
      ≤ ∫⁻ z in S, (ENNReal.ofReal |C| + ENNReal.ofReal |Real.log (‖z - w‖ ^ 2)|) :=
        lintegral_mono_ae hae
    _ = ENNReal.ofReal |C| * volume S + ∫⁻ z in S, ENNReal.ofReal |Real.log (‖z - w‖ ^ 2)| := by
        rw [lintegral_add_left measurable_const, setLIntegral_const, mul_comm]
    _ ≤ _ := add_le_add le_rfl (setLIntegral_log_normSq_sub_le hSm hS hw)

/-! ### `dd^c p_ν = ν` -/

open SGPT.Foundations.Analysis.Pending.XiaoPoissonLeviPositivity in
/-- **The distributional equation `dd^c p_ν = ν`**, in Levi form: on an open set `W` on which the
kernel stays below the level `C` for `w` in a compact set `K` carrying `ν`, for every test function
`φ` on `W`, `∫ L_φ · p_ν = π ∫ φ dν`, where `L_φ = leviForm φ · e₀ = Δφ/4`. -/
theorem integral_testLevi_mul_logPotential {C : ℝ} {ν : Measure (ComplexModel 1)}
    [IsFiniteMeasure ν] {K : Set (ComplexModel 1)} (hK : IsCompact K) (hνK : ν Kᶜ = 0)
    {W : TopologicalSpace.Opens (ComplexModel 1)}
    (hCK : ∀ z ∈ (W : Set (ComplexModel 1)), ∀ w ∈ K, logNormSq (z - w) ≤ (C : EReal))
    (φ : 𝓓(W, ℝ)) :
    ∫ z, testLeviCLM (FirstPass.MongeAmpere.coordinateVector 0) φ z *
        (logPotential C ν z).toReal = Real.pi * ∫ w, φ w ∂ν := by
  classical
  set e : ComplexModel 1 := FirstPass.MongeAmpere.coordinateVector 0 with he
  set ψ : 𝓓(W, ℝ) := testLeviCLM e φ with hψ
  set S : Set (ComplexModel 1) := tsupport ψ with hS
  have hSc : IsCompact S := ψ.hasCompactSupport
  have hSm : MeasurableSet S := (isClosed_tsupport _).measurableSet
  have hSW : S ⊆ W := ψ.tsupport_subset
  obtain ⟨R₀, hR₀⟩ := (hSc.isBounded.union hK.isBounded).subset_closedBall 0
  set R : ℝ := max R₀ 0 with hRdef
  have hSR : S ⊆ Metric.closedBall 0 R := fun z hz =>
    Metric.closedBall_subset_closedBall (le_max_left _ _) (hR₀ (Or.inl hz))
  have hKR : ∀ w ∈ K, ‖w‖ ≤ R := fun w hw => by
    have := Metric.closedBall_subset_closedBall (le_max_left R₀ 0) (hR₀ (Or.inr hw))
    rwa [Metric.mem_closedBall, dist_zero_right] at this
  set B : ℝ≥0∞ := ∫⁻ y in Metric.ball (0 : ComplexModel 1) (2 * R + 1),
    ENNReal.ofReal |Real.log (‖y‖ ^ 2)| with hBdef
  have hB : B < ⊤ := lintegral_log_normSq_ball_lt_top _
  obtain ⟨Mψ, hMψ⟩ := ψ.continuous.bounded_above_of_compact_support ψ.hasCompactSupport
  have hMψ0 : 0 ≤ Mψ := (norm_nonneg _).trans (hMψ 0)
  have hψ0 : ∀ z, z ∉ S → ψ z = 0 := fun z hz => image_eq_zero_of_notMem_tsupport hz
  have hνae : ∀ᵐ w ∂ν, w ∈ K := by rw [ae_iff]; exact hνK
  set m : ℝ := (ν univ).toReal with hm
  set k : ComplexModel 1 → ComplexModel 1 → ℝ := fun z w => Real.log (‖z - w‖ ^ 2) with hk
  -- integrability of `ψ(z) (C - k(z,w))` on the product
  set F : ComplexModel 1 → ComplexModel 1 → ℝ := fun z w => ψ z * (C - k z w) with hF
  have hFm : Measurable (Function.uncurry F) :=
    (ψ.continuous.measurable.comp measurable_fst).mul (measurable_const.sub measurable_logKernel)
  have hFbound : ∀ z w, ‖F z w‖ₑ ≤ ENNReal.ofReal Mψ *
      S.indicator (fun z => ENNReal.ofReal |C| + ENNReal.ofReal |k z w|) z := by
    intro z w
    by_cases hz : z ∈ S
    · rw [Set.indicator_of_mem hz, ← ofReal_norm, Real.norm_eq_abs, hF, abs_mul,
        ← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _), ← ENNReal.ofReal_mul hMψ0]
      refine ENNReal.ofReal_le_ofReal (mul_le_mul (by simpa using hMψ z) ?_ (abs_nonneg _) hMψ0)
      exact (abs_sub _ _).trans le_rfl
    · simp [hF, hψ0 z hz, Set.indicator_of_notMem hz]
  have hFint : Integrable (Function.uncurry F) ((volume : Measure (ComplexModel 1)).prod ν) := by
    refine ⟨hFm.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral, lintegral_prod _ hFm.enorm.aemeasurable]
    rw [lintegral_lintegral_swap (f := fun z w => ‖Function.uncurry F (z, w)‖ₑ)
      hFm.enorm.aemeasurable]
    calc ∫⁻ w, ∫⁻ z, ‖Function.uncurry F (z, w)‖ₑ ∂volume ∂ν
        ≤ ∫⁻ w, ENNReal.ofReal Mψ * (ENNReal.ofReal |C| * volume S + B) ∂ν := by
          refine lintegral_mono_ae (hνae.mono fun w hw => ?_)
          calc ∫⁻ z, ‖Function.uncurry F (z, w)‖ₑ
              ≤ ∫⁻ z, ENNReal.ofReal Mψ *
                  S.indicator (fun z => ENNReal.ofReal |C| + ENNReal.ofReal |k z w|) z :=
                lintegral_mono fun z => hFbound z w
            _ = ENNReal.ofReal Mψ * ∫⁻ z in S, (ENNReal.ofReal |C| + ENNReal.ofReal |k z w|) := by
                rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_indicator hSm]
            _ ≤ ENNReal.ofReal Mψ * (ENNReal.ofReal |C| * volume S + B) := by
                refine mul_le_mul_right ?_ _
                rw [lintegral_add_left measurable_const, setLIntegral_const, mul_comm]
                exact add_le_add le_rfl (setLIntegral_log_normSq_sub_le hSm hSR (hKR w hw))
      _ < ⊤ := by
          rw [lintegral_const]
          exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
            (ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top
              hSc.measure_lt_top, hB⟩)) (measure_lt_top ν univ)
  -- the inner integral in `z`
  have hinner : ∀ w ∈ K, ∫ z, F z w = C * (∫ z, ψ z) - Real.pi * φ w := by
    intro w hw
    have hint_k : Integrable (fun z => ψ z * k z w) := by
      set f : ComplexModel 1 → ℝ :=
        (Metric.ball (0 : ComplexModel 1) (2 * R + 1)).indicator fun y => Real.log (‖y‖ ^ 2)
      have hf : Integrable f :=
        (integrable_indicator_iff measurableSet_ball).mpr (integrableOn_log_normSq_ball _)
      have hfw : Integrable (fun z => f (z - w)) := hf.comp_sub_right w
      have h2 := hfw.bdd_mul (c := Mψ) ψ.continuous.aestronglyMeasurable
        (Eventually.of_forall fun z => by simpa using hMψ z)
      refine h2.congr (Eventually.of_forall fun z => ?_)
      by_cases hz : z ∈ S
      · have hz' := hSR hz
        rw [Metric.mem_closedBall, dist_zero_right] at hz'
        have hzw : z - w ∈ Metric.ball (0 : ComplexModel 1) (2 * R + 1) := by
          rw [Metric.mem_ball, dist_zero_right]
          calc ‖z - w‖ ≤ ‖z‖ + ‖w‖ := norm_sub_le z w
            _ < 2 * R + 1 := by linarith [hKR w hw]
        simp only [f, Set.indicator_of_mem hzw, hk]
      · simp [hψ0 z hz]
    have hint_ψ : Integrable (fun z => ψ z) := ψ.continuous.integrable_of_hasCompactSupport
      ψ.hasCompactSupport
    have hmodel := integral_log_normSq_sub_mul_leviForm φ.contDiff φ.hasCompactSupport w
    have hψe : ∀ z, ψ z = leviForm φ z e := fun z => testLeviCLM_apply e φ z
    have h3 : ∫ z, ψ z * k z w = Real.pi * φ w := by
      rw [← hmodel]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp only [hψe, hk, he]
      ring
    calc ∫ z, F z w = ∫ z, (C * ψ z - ψ z * k z w) := by
          congr 1; funext z; simp only [hF]; ring
      _ = C * (∫ z, ψ z) - ∫ z, ψ z * k z w := by
          rw [integral_sub (hint_ψ.const_mul C) hint_k, integral_const_mul]
      _ = C * (∫ z, ψ z) - Real.pi * φ w := by rw [h3]
  -- the inner integral in `w` and the potential
  have hX : ∀ᵐ z ∂(volume : Measure (ComplexModel 1)), z ∈ S → ∫⁻ w, kernelDeficit C z w ∂ν < ⊤ := by
    have hmeas : Measurable fun z => ∫⁻ w, kernelDeficit C z w ∂ν :=
      (measurable_kernelDeficit C).lintegral_prod_right'
    have hfin : ∫⁻ z in S, ∫⁻ w, kernelDeficit C z w ∂ν ≠ ⊤ := by
      rw [lintegral_lintegral_swap ((measurable_kernelDeficit C).comp
        measurable_id).aemeasurable]
      refine ne_of_lt (lt_of_le_of_lt (lintegral_mono_ae (hνae.mono fun w hw =>
        setLIntegral_kernelDeficit_le (C := C) hSm hSR (hKR w hw))) ?_)
      rw [lintegral_const]
      exact ENNReal.mul_lt_top (ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        hSc.measure_lt_top, hB⟩) (measure_lt_top ν univ)
    have h1 := ae_lt_top hmeas hfin
    rwa [ae_restrict_iff' hSm] at h1
  -- the pointwise identity for the potential
  have hpt : ∀ᵐ z ∂(volume : Measure (ComplexModel 1)),
      ψ z * (logPotential C ν z).toReal = C * m * ψ z - ∫ w, F z w ∂ν := by
    filter_upwards [hX] with z hz
    by_cases hzS : z ∈ S
    · have hXz := hz hzS
      have hzW : z ∈ (W : Set (ComplexModel 1)) := hSW hzS
      have hνz : ν {z} = 0 := by
        by_contra hne
        have htop : ∫⁻ w, kernelDeficit C z w ∂ν = ⊤ := by
          refine top_le_iff.mp ?_
          calc (⊤ : ℝ≥0∞) = kernelDeficit C z z * ν {z} := by
                simp [kernelDeficit, ENNReal.top_mul hne]
            _ = ∫⁻ w in {z}, kernelDeficit C z w ∂ν := (lintegral_singleton _ _).symm
            _ ≤ ∫⁻ w, kernelDeficit C z w ∂ν := setLIntegral_le_lintegral _ _
        exact absurd htop hXz.ne
      have hae : ∀ᵐ w ∂ν, kernelDeficit C z w = ENNReal.ofReal (C - k z w) ∧ 0 ≤ C - k z w := by
        have hne : ∀ᵐ w ∂ν, w ≠ z := by
          rw [ae_iff]
          simpa using hνz
        filter_upwards [hne, hνae] with w hw hwK
        refine ⟨kernelDeficit_eq_ofReal (Ne.symm hw), ?_⟩
        have := hCK z hzW w hwK
        rw [logNormSq_of_ne_zero (sub_ne_zero.mpr (Ne.symm hw)), EReal.coe_le_coe_iff] at this
        simp only [hk]
        linarith
      have hkm : Measurable fun w => C - k z w := by
        simp only [hk]
        exact measurable_const.sub (Real.measurable_log.comp
          ((continuous_const.sub continuous_id).norm.pow 2).measurable)
      have hint : ∫ w, (C - k z w) ∂ν = (∫⁻ w, kernelDeficit C z w ∂ν).toReal := by
        rw [integral_eq_lintegral_of_nonneg_ae (hae.mono fun w hw => hw.2) hkm.aestronglyMeasurable]
        congr 1
        exact lintegral_congr_ae (hae.mono fun w hw => hw.1.symm)
      rw [logPotential_eq_coe hXz.ne, EReal.toReal_coe]
      have hF' : ∫ w, F z w ∂ν = ψ z * ∫ w, (C - k z w) ∂ν := by
        simp only [hF]
        exact integral_const_mul _ _
      rw [hF', hint, ← hm]
      ring
    · simp [hψ0 z hzS, hF]
  have hint_ψ : Integrable (fun z => ψ z) :=
    ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport
  have hint_φ : Integrable (fun w => φ w) ν :=
    φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  have hFl : Integrable (fun z => ∫ w, F z w ∂ν) := hFint.integral_prod_left
  calc ∫ z, ψ z * (logPotential C ν z).toReal
      = ∫ z, (C * m * ψ z - ∫ w, F z w ∂ν) := integral_congr_ae hpt
    _ = C * m * (∫ z, ψ z) - ∫ z, ∫ w, F z w ∂ν := by
        rw [integral_sub (hint_ψ.const_mul _) hFl, integral_const_mul]
    _ = C * m * (∫ z, ψ z) - ∫ w, (∫ z, F z w) ∂ν := by
        congr 1
        exact integral_integral_swap hFint
    _ = C * m * (∫ z, ψ z) - ∫ w, (C * (∫ z, ψ z) - Real.pi * φ w) ∂ν := by
        congr 1
        exact integral_congr_ae (hνae.mono fun w hw => hinner w hw)
    _ = Real.pi * ∫ w, φ w ∂ν := by
        rw [integral_sub (integrable_const _) (hint_φ.const_mul _), integral_const,
          integral_const_mul, smul_eq_mul, Measure.real, ← hm]
        ring

end SGPT.NPP.Riesz
