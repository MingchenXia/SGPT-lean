import SGPT.Foundations.Analysis.Pending.LocalHolomorphicLelongReaderCovariance
import SGPT.Foundations.Analysis.Pending.ActualLelongPositiveScaling
import SGPT.Foundations.Analysis.Pending.PrincipalGeneratorLogPointwiseNormalForm

set_option autoImplicit false

/-! # Exact local generic coordinate orders of a full principal family

The literal point-infimum on a coordinate hyperplane is read from a true
full-point logarithmic normal form. Zero coefficients are retained, and an
actual point avoiding the other coordinate hyperplanes is supplied internally.
This local computation is not an intrinsic all-prime-divisor dictionary.
Reference: Demailly, CADG and Analytic Methods, local principal ideals;
supplementary direct logarithmic-reader computation.
-/

open Set Filter Metric
open scoped Topology ENNReal NNReal

namespace SGPT.Foundations.Analysis.Pending.SNCLogarithmicGenericCoordinateOrders

open FirstPass FirstPass.NonKahlerLocus

noncomputable section

private theorem coe_sum_real {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ((∑ i ∈ s, f i : ℝ) : EReal) = ∑ i ∈ s, (f i : EReal) :=
  map_sum (⟨⟨fun r : ℝ => (r : EReal), EReal.coe_zero⟩, EReal.coe_add⟩ : ℝ →+ EReal) f s

private theorem lelongNumber_zero_on_hyperplane {n : ℕ} (j : Fin n)
    {x : ComplexModel n} (hx : x j = 0) :
    lelongNumber (n := n) (fun _ : ComplexModel n => (0 : EReal)) x = 0 := by
  apply le_antisymm ?_ bot_le
  apply ENNReal.le_of_forall_pos_le_add (b := 0)
  intro ε hε _
  have hεr : (0 : ℝ) < ε := by exact_mod_cast hε
  have hnormc : ContinuousAt (fun z : ComplexModel n => ‖z j‖) x :=
    (EuclideanSpace.proj (𝕜 := ℂ) j).continuous.continuousAt.norm
  have hnorm : ∀ᶠ z in 𝓝 x, ‖z j‖ < 1 :=
    hnormc.eventually (gt_mem_nhds (by
      change ‖x j‖ < 1
      rw [hx, norm_zero]
      exact zero_lt_one))
  have hle : ∀ᶠ z in 𝓝[≠] x,
      ((ε : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal ‖z j‖) ≤ 0 := by
    filter_upwards [hnorm.filter_mono nhdsWithin_le_nhds] with z hz
    have hlog : ENNReal.log (ENNReal.ofReal ‖z j‖) ≤ 0 := by
      simpa only [ENNReal.log_one] using
        ENNReal.log_monotone (ENNReal.ofReal_le_one.mpr hz.le)
    calc
      _ ≤ ((ε : ℝ) : EReal) * 0 := by gcongr
      _ = 0 := mul_zero _
  have h := KahlerCurrentMax.lelongNumber_le_of_eventually_le (n := n) hle
  rw [ActualLelongPositiveScaling.lelongNumber_smul_eq hεr,
    LocalHolomorphicLelongReaderCovariance.lelongNumber_coordinate_log_eq_one_of_eq_zero j hx,
    mul_one, ENNReal.ofReal_coe_nnreal] at h
  simpa only [zero_add] using h

private theorem lelongNumber_scaled_coordinate_eq {n : ℕ} (j : Fin n)
    {x : ComplexModel n} (hx : x j = 0) {a : ℝ} (ha : 0 ≤ a) :
    lelongNumber (n := n)
      (fun z : ComplexModel n => (a : EReal) * ENNReal.log (ENNReal.ofReal ‖z j‖)) x =
      ENNReal.ofReal a := by
  by_cases hzero : a = 0
  · subst a
    simpa only [EReal.coe_zero, zero_mul, ENNReal.ofReal_zero] using
      lelongNumber_zero_on_hyperplane j hx
  · rw [ActualLelongPositiveScaling.lelongNumber_smul_eq (lt_of_le_of_ne ha (Ne.symm hzero)),
      LocalHolomorphicLelongReaderCovariance.lelongNumber_coordinate_log_eq_one_of_eq_zero j hx,
      mul_one]

private theorem coordinate_log_term_le {n : ℕ} (i : Fin n)
    {a B : ℝ} (ha : 0 ≤ a) (hB : 0 < B) {z : ComplexModel n} (hz : ‖z‖ ≤ B) :
    (a : EReal) * ENNReal.log (ENNReal.ofReal ‖z i‖) ≤ (a * Real.log B : EReal) := by
  have hlog : ENNReal.log (ENNReal.ofReal ‖z i‖) ≤ (Real.log B : EReal) := by
    calc
      _ ≤ ENNReal.log (ENNReal.ofReal B) :=
        ENNReal.log_monotone (ENNReal.ofReal_le_ofReal ((PiLp.norm_apply_le z i).trans hz))
      _ = _ := ENNReal.log_ofReal_of_pos hB
  calc
    _ ≤ (a : EReal) * (Real.log B : EReal) := by gcongr
    _ = _ := (EReal.coe_mul a (Real.log B)).symm

private theorem coordinate_sum_reader_lower {n : ℕ} (a : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (j : Fin n) {x : ComplexModel n} (hx : x j = 0)
    {ρ : ComplexModel n → ℝ} (hρ : ContinuousAt ρ x) :
    ENNReal.ofReal (a j) ≤ lelongNumber (n := n)
      (fun z => (∑ i : Fin n, (a i : EReal) * ENNReal.log (ENNReal.ofReal ‖z i‖)) +
        (ρ z : EReal)) x := by
  classical
  let S := (Finset.univ : Finset (Fin n)).erase j
  let B : ℝ := ‖x‖ + 1
  have hB : 0 < B := by dsimp only [B]; positivity
  have hnorm : ∀ᶠ z in 𝓝 x, ‖z‖ ≤ B :=
    (continuous_norm.continuousAt.eventually (gt_mem_nhds (by dsimp only [B]; linarith))).mono
      fun _ hz => hz.le
  have hρbound : ∀ᶠ z in 𝓝 x, ρ z ≤ ρ x + 1 :=
    (hρ.eventually (gt_mem_nhds (lt_add_one (ρ x)))).mono fun _ hz => hz.le
  have hupper : ∀ᶠ z in 𝓝[≠] x,
      (∑ i : Fin n, (a i : EReal) * ENNReal.log (ENNReal.ofReal ‖z i‖)) + (ρ z : EReal) ≤
      (a j : EReal) * ENNReal.log (ENNReal.ofReal ‖z j‖) +
        (((∑ i ∈ S, a i * Real.log B) + (ρ x + 1) : ℝ) : EReal) := by
    filter_upwards [(hnorm.and hρbound).filter_mono nhdsWithin_le_nhds] with z hz
    rw [← Finset.add_sum_erase Finset.univ
      (fun i : Fin n => (a i : EReal) * ENNReal.log (ENNReal.ofReal ‖z i‖))
      (Finset.mem_univ j)]
    rw [add_assoc, EReal.coe_add, coe_sum_real]
    exact add_le_add le_rfl (add_le_add
      (Finset.sum_le_sum fun i _ => coordinate_log_term_le i (ha i) hB hz.1)
      (EReal.coe_le_coe_iff.mpr hz.2))
  have h := KahlerCurrentMax.lelongNumber_le_of_eventually_le (n := n) hupper
  rw [LelongChartReaderInvariance.lelongNumber_add_continuous_eq continuousAt_const,
    lelongNumber_scaled_coordinate_eq j hx (ha j)] at h
  exact h

private theorem coordinate_sum_reader_eq_at_unit_point {n : ℕ} (a : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (j : Fin n) {x : ComplexModel n} (hx : x j = 0)
    (hother : ∀ i : Fin n, i ≠ j → x i ≠ 0)
    {ρ : ComplexModel n → ℝ} (hρ : ContinuousAt ρ x) :
    lelongNumber (n := n)
      (fun z => (∑ i : Fin n, (a i : EReal) * ENNReal.log (ENNReal.ofReal ‖z i‖)) +
        (ρ z : EReal)) x = ENNReal.ofReal (a j) := by
  classical
  let S := (Finset.univ : Finset (Fin n)).erase j
  let η : ComplexModel n → ℝ := fun z => (∑ i ∈ S, a i * Real.log ‖z i‖) + ρ z
  have hη : ContinuousAt η x := by
    apply ContinuousAt.add ?_ hρ
    refine tendsto_finsetSum S fun i hi => continuousAt_const.mul ?_
    exact ((EuclideanSpace.proj (𝕜 := ℂ) i).continuous.continuousAt.norm).log
      (norm_ne_zero_iff.mpr (hother i (Finset.mem_erase.mp hi).1))
  have hcoords : ∀ᶠ z in 𝓝 x, ∀ i : Fin n, i ≠ j → z i ≠ 0 := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi : i ≠ j
    · exact ((EuclideanSpace.proj (𝕜 := ℂ) i).continuous.continuousAt.eventually_ne
        (hother i hi)).mono fun z hz _ => hz
    · exact Eventually.of_forall fun _ h => False.elim (hi h)
  have heq : (fun z => (∑ i : Fin n, (a i : EReal) * ENNReal.log (ENNReal.ofReal ‖z i‖)) +
      (ρ z : EReal)) =ᶠ[𝓝 x]
      (fun z => (a j : EReal) * ENNReal.log (ENNReal.ofReal ‖z j‖) + (η z : EReal)) := by
    filter_upwards [hcoords] with z hz
    rw [← Finset.add_sum_erase Finset.univ
      (fun i : Fin n => (a i : EReal) * ENNReal.log (ENNReal.ofReal ‖z i‖))
      (Finset.mem_univ j), add_assoc]
    congr 1
    dsimp only [η]
    rw [EReal.coe_add, coe_sum_real]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [ENNReal.log_ofReal_of_pos (norm_pos_iff.mpr (hz i (Finset.mem_erase.mp hi).1)),
      EReal.coe_mul]
  rw [LelongNumberComparison.lelongNumber_congr heq,
    LelongChartReaderInvariance.lelongNumber_add_continuous_eq hη,
    lelongNumber_scaled_coordinate_eq j hx (ha j)]

/-- The literal local hyperplane infimum equals its coefficient, including
coefficient zero. A genuine point avoiding all other hyperplanes is internally supplied. -/
theorem iInf_lelongNumber_coordinate_hyperplane_eq {n : ℕ} (a : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (j : Fin n) {ρ : ComplexModel n → ℝ} {R : ℝ}
    (hR : 0 < R) (hρ : ∀ z ∈ ball (0 : ComplexModel n) R, ContinuousAt ρ z) :
    (⨅ x ∈ ball (0 : ComplexModel n) R ∩ {x | x j = 0},
      lelongNumber (n := n)
        (fun z => (∑ i : Fin n, (a i : EReal) * ENNReal.log (ENNReal.ofReal ‖z i‖)) +
          (ρ z : EReal)) x) = ENNReal.ofReal (a j) := by
  classical
  apply le_antisymm
  · let v : ComplexModel n := WithLp.toLp 2 (fun i => if i = j then 0 else (1 : ℂ))
    let δ : ℝ := R / (‖v‖ + 1)
    let y : ComplexModel n := δ • v
    have hd : 0 < δ := div_pos hR (by positivity)
    have hdR : δ * (‖v‖ + 1) = R := by
      dsimp only [δ]
      exact div_mul_cancel₀ _ (ne_of_gt (by positivity : (0 : ℝ) < ‖v‖ + 1))
    have hyball : y ∈ ball (0 : ComplexModel n) R := by
      rw [mem_ball_zero_iff]
      dsimp only [y]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hd]
      nlinarith
    have hyj : y j = 0 := by simp [y, v]
    have hyother : ∀ i : Fin n, i ≠ j → y i ≠ 0 := by
      intro i hi
      change δ • (if i = j then (0 : ℂ) else 1) ≠ 0
      rw [if_neg hi]
      exact smul_ne_zero hd.ne' one_ne_zero
    exact (iInf₂_le (f := fun x (_ : x ∈ ball (0 : ComplexModel n) R ∩ {x | x j = 0}) =>
      lelongNumber (n := n)
        (fun z => (∑ i : Fin n, (a i : EReal) * ENNReal.log (ENNReal.ofReal ‖z i‖)) +
          (ρ z : EReal)) x) y ⟨hyball, hyj⟩).trans_eq
      (coordinate_sum_reader_eq_at_unit_point a ha j hyj hyother (hρ y hyball))
  · refine le_iInf fun x => le_iInf fun hx => ?_
    exact coordinate_sum_reader_lower a ha j hx.2 (hρ x hx.1)

/-- The complete original principal family internally supplies one set of
integer orders and one ball, with exact literal generic reader on every coordinate hyperplane. -/
theorem exists_generatorLog_generic_coordinate_orders {n s : ℕ}
    (G : Fin s → ComplexModel n → ℂ)
    (hG : ∀ i, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (G i) z)
    {H : ComplexModel n → ℂ} (hH : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ H z)
    (hHnon : ∃ᶠ z in 𝓝 (0 : ComplexModel n), H z ≠ 0)
    (hspan : Ideal.span (Set.range fun i => HolGerm.mk (G i) (hG i)) =
      Ideal.span {HolGerm.mk H hH})
    (hzero : ∀ᶠ z in 𝓝 0, H z = 0 → ∃ j : Fin n, z j = 0) :
    ∃ (a : Fin n → ℕ) (R : ℝ), 0 < R ∧ ∀ j : Fin n,
      (⨅ x ∈ ball (0 : ComplexModel n) R ∩ {x | x j = 0},
        lelongNumber (n := n) (generatorLog G) x) = ENNReal.ofReal (2 * (a j : ℝ)) := by
  obtain ⟨a, η, R, hR, hη, heq⟩ :=
    PrincipalGeneratorLogPointwiseNormalForm.exists_generatorLog_coordinate_normal_form
      G hG hH hHnon hspan hzero
  refine ⟨a, R, hR, fun j => ?_⟩
  have hreader : ∀ x ∈ ball (0 : ComplexModel n) R,
      lelongNumber (n := n) (generatorLog G) x = lelongNumber (n := n)
        (fun z => (∑ i : Fin n, ((2 * (a i : ℝ) : ℝ) : EReal) *
          ENNReal.log (ENNReal.ofReal ‖z i‖)) + (η z : EReal)) x := by
    intro x hx
    apply LelongNumberComparison.lelongNumber_congr
    exact (show ∀ᶠ z in 𝓝 x, z ∈ ball (0 : ComplexModel n) R from
      isOpen_ball.mem_nhds hx).mono fun z hz => heq z hz
  calc
    _ = ⨅ x ∈ ball (0 : ComplexModel n) R ∩ {x | x j = 0},
        lelongNumber (n := n)
          (fun z => (∑ i : Fin n, ((2 * (a i : ℝ) : ℝ) : EReal) *
            ENNReal.log (ENNReal.ofReal ‖z i‖)) + (η z : EReal)) x :=
      iInf_congr fun x => iInf_congr fun hx => hreader x hx.1
    _ = _ := iInf_lelongNumber_coordinate_hyperplane_eq
      (fun i => 2 * (a i : ℝ)) (fun i => by positivity) j hR hη

end
end SGPT.Foundations.Analysis.Pending.SNCLogarithmicGenericCoordinateOrders
