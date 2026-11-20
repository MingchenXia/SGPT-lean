import SGPT.Foundations.Analysis.Pending.SingularModelFiniteEnergyOrderedComparison
import SGPT.Foundations.Analysis.Pending.SingularModelFiniteEnergyGapMax
import SGPT.Foundations.Analysis.Pending.RooftopContactGeneral
import SGPT.Foundations.Analysis.Pending.GlobalDiagonalConvexScaling
import SGPT.Foundations.Analysis.Pending.ThetaCapacity

set_option autoImplicit false

/-!
# Actual singular-model Darvas--diagonal comparison

Xia SGPT PDF0162--0163, Theorem 4.3.1. Actual rooftop obstacle measure
domination, genuine E1 cross-measure integrability, and the actual ordered
endpoint comparison provide the source lower Darvas--diagonal comparison.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.SingularModelDarvasDiagonalComparison

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses RelativeEnergyIntegrability DiagonalMass
  SingularModelFiniteEnergyDiagonalGap SingularModelFiniteEnergyOrderedComparison

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

variable {θ : ClosedRealOneOneForm n M} {φ u v : M → EReal} {hφ : IsModelPotential θ φ}

/-- Actual rooftop contact measure domination gives weighted gap domination
on the actual smaller-obstacle measure, without an integrability premise. -/
theorem lintegral_rooftop_gap_le (omega : KahlerBackground n M)
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential θ.val v)
    (hr : IsThetaPshPotential θ.val (rooftop θ u v)) :
    (∫⁻ x, canonicalERealAbsDiff (u x) (rooftop θ u v x)
      ∂diagonalPotentialMeasure θ (rooftop θ u v) hr) ≤
        ∫⁻ x, canonicalERealAbsDiff (u x) (v x) ∂diagonalPotentialMeasure θ v hv := by
  have h := RooftopContactGeneral.relativeFiniteEnergyIntegral_rooftop_le_general
    omega θ hu hv hr (rooftop_le_left hu hv) (rooftop_le_right hu hv) (phi := u)
  have hz (x : M) : canonicalERealAbsDiff (u x) (u x) = 0 :=
    canonicalERealAbsDiff_self_of_ne_top (hu.1.quasiPlurisubharmonic.ne_top x)
  simpa only [relativeFiniteEnergyIntegral, hz, lintegral_zero, zero_add, rooftop] using h

omit [BorelSpace M] [CompactSpace M] in
private theorem ofReal_integral_norm_eq_canonicalAbs {a b : M → EReal}
    (ha : IsThetaPshPotential θ.val a) (hb : IsThetaPshPotential θ.val b)
    (μ : Measure M) (haz : μ {x | a x = ⊥} = 0) (hbz : μ {x | b x = ⊥} = 0)
    (hi : Integrable (fun x => canonicalERealDiffToReal (a x) (b x)) μ) :
    ENNReal.ofReal (∫ x, ‖canonicalERealDiffToReal (a x) (b x)‖ ∂μ) =
      ∫⁻ x, canonicalERealAbsDiff (a x) (b x) ∂μ := by
  rw [ofReal_integral_eq_lintegral_ofReal hi.norm (Eventually.of_forall fun _ => norm_nonneg _)]
  have hAEa : ∀ᵐ x ∂μ, a x ≠ ⊥ := ae_iff.mpr (by simpa only [not_not] using haz)
  have hAEb : ∀ᵐ x ∂μ, b x ≠ ⊥ := ae_iff.mpr (by simpa only [not_not] using hbz)
  apply lintegral_congr_ae
  filter_upwards [hAEa, hAEb] with x hab hbb
  have hpole : a x = ⊥ ↔ b x = ⊥ := ⟨fun h => (hab h).elim, fun h => (hbb h).elim⟩
  rw [Real.norm_eq_abs, canonicalERealAbsDiff_eq_ofReal_abs_diff
    (ha.1.quasiPlurisubharmonic.ne_top x) (hb.1.quasiPlurisubharmonic.ne_top x) hpole]

/-- Actual ordered E1 comparison and obstacle measure domination bound the
actual energy loss to the rooftop by the opposite endpoint's diagonal gap. -/
theorem ofReal_energy_sub_rooftop_le [ConnectedSpace M] (omega : KahlerBackground n M)
    (hu : RelativeFiniteEnergyPreceq θ φ u hφ) (hv : RelativeFiniteEnergyPreceq θ φ v hφ) :
    ENNReal.ofReal ((energy θ φ hφ u).toReal - (energy θ φ hφ (rooftop θ u v)).toReal) ≤
      ∫⁻ x, canonicalERealAbsDiff (u x) (v x) ∂diagonalPotentialMeasure θ v hv.1.plurisubharmonic := by
  have hr := relativeFiniteEnergyPreceq_rooftop omega hu hv
  let μr := diagonalPotentialMeasure θ (rooftop θ u v) hr.1.plurisubharmonic
  let g := fun x => canonicalERealDiffToReal (u x) (rooftop θ u v x)
  have hi : Integrable g μr :=
    (SingularModelFiniteEnergyDiagonalGap.integrable_canonicalDiff_diagonal_add omega hu hr
      (rooftop_le_left hu.1.plurisubharmonic hv.1.plurisubharmonic)).right_of_add_measure
  calc ENNReal.ofReal ((energy θ φ hφ u).toReal - (energy θ φ hφ (rooftop θ u v)).toReal)
      ≤ ENNReal.ofReal (∫ x, g x ∂μr) := ENNReal.ofReal_le_ofReal
        (energy_sub_le_integral_smaller_diagonal_of_preceq omega hu hr
          (rooftop_le_left hu.1.plurisubharmonic hv.1.plurisubharmonic))
    _ ≤ ENNReal.ofReal (∫ x, ‖g x‖ ∂μr) := ENNReal.ofReal_le_ofReal
      (integral_mono_ae hi hi.norm (Eventually.of_forall fun x => Real.le_norm_self (g x)))
    _ = ∫⁻ x, canonicalERealAbsDiff (u x) (rooftop θ u v x) ∂μr :=
      ofReal_integral_norm_eq_canonicalAbs hu.1.plurisubharmonic hr.1.plurisubharmonic μr
        (GlobalDiagonalScaling.globalMixedMeasure_pole_null_of_nondegenerate
          (fun _ : Fin n => hr.1.plurisubharmonic.1) hu.1.plurisubharmonic)
        (FiniteEnergyCharacterization.diagonalPotentialMeasure_pole_null θ hr.1.plurisubharmonic) hi
    _ ≤ _ := lintegral_rooftop_gap_le omega hu.1.plurisubharmonic hv.1.plurisubharmonic hr.1.plurisubharmonic

private theorem canonicalAbs_symm (a b : EReal) :
    canonicalERealAbsDiff a b = canonicalERealAbsDiff b a := by
  cases a <;> cases b <;>
    simp [canonicalERealAbsDiff, poleModifiedERealAbsDiff, ← EReal.coe_sub,
      EReal.abs_def, abs_sub_comm]

/-- The actual lower Darvas--diagonal comparison holds for all singular
model E1 pairs; integrability and the genuine rooftop are produced internally. -/
theorem ofReal_relativeD1_le_diagonalGapIntegral [ConnectedSpace M]
    (omega : KahlerBackground n M)
    (hu : RelativeFiniteEnergyPreceq θ φ u hφ) (hv : RelativeFiniteEnergyPreceq θ φ v hφ) :
    ENNReal.ofReal (relativeD1 θ φ hφ u v) ≤
      diagonalGapIntegral θ u v hu.1.plurisubharmonic hv.1.plurisubharmonic := by
  have hr := relativeFiniteEnergyPreceq_rooftop omega hu hv
  have hru := rooftop_le_left hu.1.plurisubharmonic hv.1.plurisubharmonic
  have hrv := rooftop_le_right hu.1.plurisubharmonic hv.1.plurisubharmonic
  have hu0 : 0 ≤ (energy θ φ hφ u).toReal - (energy θ φ hφ (rooftop θ u v)).toReal :=
    sub_nonneg.mpr (SingularModelFiniteRealEnergy.toReal_energy_mono omega hr hu hru)
  have hv0 : 0 ≤ (energy θ φ hφ v).toReal - (energy θ φ hφ (rooftop θ u v)).toReal :=
    sub_nonneg.mpr (SingularModelFiniteRealEnergy.toReal_energy_mono omega hr hv hrv)
  have ha := ofReal_energy_sub_rooftop_le omega hu hv
  have hb := ofReal_energy_sub_rooftop_le omega hv hu
  rw [rooftop_comm θ v u] at hb
  simp only [canonicalAbs_symm] at hb
  have hc := add_le_add hb ha
  rw [← ENNReal.ofReal_add hv0 hu0] at hc
  have he : ((energy θ φ hφ v).toReal - (energy θ φ hφ (rooftop θ u v)).toReal) +
      ((energy θ φ hφ u).toReal - (energy θ φ hφ (rooftop θ u v)).toReal) =
      relativeD1 θ φ hφ u v := by rw [relativeD1]; ring
  rw [he] at hc
  simpa only [diagonalGapIntegral, lintegral_add_measure] using hc

/-- Genuine positive convex combinations of actual E1 endpoints are E1,
using their produced rooftop as a genuine E1 lower barrier. -/
theorem relativeFiniteEnergyPreceq_convexComb [ConnectedSpace M]
    (omega : KahlerBackground n M)
    (hu : RelativeFiniteEnergyPreceq θ φ u hφ) (hv : RelativeFiniteEnergyPreceq θ φ v hφ)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    RelativeFiniteEnergyPreceq θ φ (ThetaPshConvexCombination.convexComb t u v) hφ := by
  have hr := relativeFiniteEnergyPreceq_rooftop omega hu hv
  have hm := SingularModelFiniteEnergyGapMax.relativeFiniteEnergyPreceq_max omega hu hv
  have hlow : rooftop θ u v ≤ ThetaPshConvexCombination.convexComb t u v := by
    have h := ThetaPshConvexCombination.convexComb_mono ht0.le ht1.le
      (rooftop_le_left hu.1.plurisubharmonic hv.1.plurisubharmonic)
      (rooftop_le_right hu.1.plurisubharmonic hv.1.plurisubharmonic)
    rwa [ThetaCapacity.convexComb_self ht0 ht1] at h
  have hhigh : ThetaPshConvexCombination.convexComb t u v ≤ fun x => max (u x) (v x) := by
    have h := ThetaPshConvexCombination.convexComb_mono ht0.le ht1.le
      (show u ≤ fun x => max (u x) (v x) from fun _ => le_max_left _ _)
      (show v ≤ fun x => max (u x) (v x) from fun _ => le_max_right _ _)
    rwa [ThetaCapacity.convexComb_self ht0 ht1] at h
  exact SingularModelFiniteEnergyGapMax.relativeFiniteEnergyPreceq_of_le omega hr
    ⟨ThetaPshConvexCombination.isThetaPshPotential_convexComb hu.1.plurisubharmonic hv.1.plurisubharmonic ht0 ht1,
      (MoreSingularOn.of_le fun x _ => hhigh x).trans hm.1.relativePSHPreceq.2⟩ hlow

/-- Xia's actual midpoint estimate (4.19), with the source constant produced
by the separate smaller-diagonal bound n+1, over every singular model. -/
theorem relativeD1_midpoint_le [ConnectedSpace M] (omega : KahlerBackground n M)
    (hu : RelativeFiniteEnergyPreceq θ φ u hφ) (hv : RelativeFiniteEnergyPreceq θ φ v hφ) :
    relativeD1 θ φ hφ u (ThetaPshConvexCombination.convexComb (1 / 2 : ℝ) u v) ≤
      (3 * ((n : ℝ) + 1) / 2) * relativeD1 θ φ hφ u v := by
  let h := ThetaPshConvexCombination.convexComb (1 / 2 : ℝ) u v
  let r := rooftop θ u v
  have hr := relativeFiniteEnergyPreceq_rooftop omega hu hv
  have hh : RelativeFiniteEnergyPreceq θ φ h hφ :=
    relativeFiniteEnergyPreceq_convexComb omega hu hv (by norm_num) (by norm_num)
  have hru : r ≤ u := rooftop_le_left hu.1.plurisubharmonic hv.1.plurisubharmonic
  have hrv : r ≤ v := rooftop_le_right hu.1.plurisubharmonic hv.1.plurisubharmonic
  have hrh : r ≤ h := by
    have hc := ThetaPshConvexCombination.convexComb_mono
      (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (1 / 2 : ℝ) ≤ 1 by norm_num) hru hrv
    rwa [ThetaCapacity.convexComb_self (by norm_num) (by norm_num)] at hc
  let μr := diagonalPotentialMeasure θ r hr.1.plurisubharmonic
  let gu := fun x => canonicalERealDiffToReal (u x) (r x)
  let gv := fun x => canonicalERealDiffToReal (v x) (r x)
  let gh := fun x => canonicalERealDiffToReal (h x) (r x)
  have hiu : Integrable gu μr :=
    (SingularModelFiniteEnergyDiagonalGap.integrable_canonicalDiff_diagonal_add omega hu hr hru).right_of_add_measure
  have hiv : Integrable gv μr :=
    (SingularModelFiniteEnergyDiagonalGap.integrable_canonicalDiff_diagonal_add omega hv hr hrv).right_of_add_measure
  have hpole (w : M → EReal) (hw : IsThetaPshPotential θ.val w) : ∀ᵐ x ∂μr, w x ≠ ⊥ := by
    have hz : μr {x | w x = ⊥} = 0 :=
      GlobalDiagonalScaling.globalMixedMeasure_pole_null_of_nondegenerate
        (fun _ : Fin n => hr.1.plurisubharmonic.1) hw
    exact ae_iff.mpr (by simpa only [not_not] using hz)
  have hgap : gh =ᵐ[μr] fun x => (1 / 2 : ℝ) * (gu x + gv x) := by
    filter_upwards [hpole u hu.1.plurisubharmonic, hpole v hv.1.plurisubharmonic,
      hpole r hr.1.plurisubharmonic] with x hub hvb hrb
    dsimp only [gh, gu, gv, h]
    have huc := EReal.coe_toReal (hu.1.plurisubharmonic.1.quasiPlurisubharmonic.ne_top x) hub
    have hvc := EReal.coe_toReal (hv.1.plurisubharmonic.1.quasiPlurisubharmonic.ne_top x) hvb
    have hrc : ((r x).toReal : EReal) = r x :=
      EReal.coe_toReal (hr.1.plurisubharmonic.1.quasiPlurisubharmonic.ne_top x) hrb
    rw [ThetaPshConvexCombination.convexComb_apply, ← huc, ← hvc, ← hrc]
    simp only [← EReal.coe_mul, ← EReal.coe_add, canonicalERealDiffToReal_coe_coe]
    ring
  have hI : (∫ x, gh x ∂μr) = (1 / 2 : ℝ) * ((∫ x, gu x ∂μr) + ∫ x, gv x ∂μr) := by
    rw [integral_congr_ae hgap, integral_const_mul, integral_add hiu hiv]
  have htri : relativeD1 θ φ hφ u h ≤
      ((energy θ φ hφ u).toReal - (energy θ φ hφ r).toReal) +
        ((energy θ φ hφ h).toReal - (energy θ φ hφ r).toReal) := by
    have hc := SingularModelDarvasContraction.relativeD1_triangle omega hu hh hr
    rw [relativeD1_comm θ φ hφ u r, relativeD1_eq_sub_of_le hr.1.plurisubharmonic hru,
      relativeD1_eq_sub_of_le hr.1.plurisubharmonic hrh] at hc
    exact hc
  have hcu := integral_le_energy_sub_le_integral_le_mul omega hu hr hru
  have hcv := integral_le_energy_sub_le_integral_le_mul omega hv hr hrv
  have hch := energy_sub_le_integral_smaller_diagonal_of_preceq omega hh hr hrh
  have hv0 : 0 ≤ (energy θ φ hφ v).toReal - (energy θ φ hφ r).toReal :=
    sub_nonneg.mpr (SingularModelFiniteRealEnergy.toReal_energy_mono omega hr hv hrv)
  have hn : 0 ≤ (n : ℝ) + 1 := by positivity
  change relativeD1 θ φ hφ u h ≤ (3 * ((n : ℝ) + 1) / 2) * relativeD1 θ φ hφ u v
  change (energy θ φ hφ h).toReal - (energy θ φ hφ r).toReal ≤ ∫ x, gh x ∂μr at hch
  rw [hI] at hch
  change relativeD1 θ φ hφ u h ≤ (3 * ((n : ℝ) + 1) / 2) *
    ((energy θ φ hφ u).toReal + (energy θ φ hφ v).toReal - 2 * (energy θ φ hφ r).toReal)
  nlinarith [hcu.2.1, hcu.2.2, hcv.2.2, mul_nonneg hn hv0]

/-- Actual non-pluripolar multilinearity and positivity produce the inverse
midpoint measure domination, including dimension zero and singular endpoints. -/
theorem diagonalPotentialMeasure_le_pow_smul_midpoint
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential θ.val v) :
    diagonalPotentialMeasure θ u hu ≤ ENNReal.ofReal ((2 : ℝ) ^ n) •
      diagonalPotentialMeasure θ (ThetaPshConvexCombination.convexComb (1 / 2 : ℝ) u v)
        (ThetaPshConvexCombination.isThetaPshPotential_convexComb hu hv (by norm_num) (by norm_num)) := by
  rw [Measure.le_iff]
  intro E _
  rw [Measure.smul_apply, smul_eq_mul]
  have hs : ENNReal.ofReal ((1 / 2 : ℝ) ^ n) * diagonalPotentialMeasure θ u hu E ≤
      diagonalPotentialMeasure θ (ThetaPshConvexCombination.convexComb (1 / 2 : ℝ) u v)
        (ThetaPshConvexCombination.isThetaPshPotential_convexComb hu hv (by norm_num) (by norm_num)) E :=
    GlobalDiagonalConvexScaling.globalMixedMeasure_diagonal_convexComb_le hu hv (by norm_num) (by norm_num) E
  have hc : ENNReal.ofReal ((2 : ℝ) ^ n) * ENNReal.ofReal ((1 / 2 : ℝ) ^ n) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), ← mul_pow]
    norm_num
  have hm := mul_le_mul_right hs (ENNReal.ofReal ((2 : ℝ) ^ n))
  rwa [← mul_assoc, hc, one_mul] at hm

end

end SGPT.Foundations.Analysis.Pending.SingularModelDarvasDiagonalComparison
