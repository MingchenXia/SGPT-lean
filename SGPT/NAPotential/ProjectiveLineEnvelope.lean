import SGPT.NAPotential.BerkovichPiecewiseLinear
import SGPT.NAPotential.PointwiseEnvelope
import SGPT.NAPotential.RayEnvelope
import SGPT.Toric.ProjectiveLineLogSingularity
import SGPT.Toric.ProjectiveLineNativePotential
import SGPT.Foundations.Analysis.Pending.PluripolarCapacityDichotomy
import Mathlib.Data.Fin.VecNotation

/-!
The target is the literal pointwise LCE with real-height epigraph. It says
nothing about any spatially regularized or amended envelope.
-/
set_option autoImplicit false
noncomputable section

namespace SGPT.NAPotential.ProjectiveLineEnvelope

open Set Filter
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Toric
open SGPT.NAPotential.Berkovich SGPT.NAPotential.PointwiseRayEnvelope

local notation "P1" => Projectivization ℂ (Fin 2 → ℂ)

private theorem native_atlas_roundtrip (α : ClosedRealOneOneForm 1 P1) :
    atlasClosedFormToNative (nativeClosedFormToAtlas α) = α := by
  rcases α with ⟨a, ha⟩
  cases a
  rfl

def fsForm : AtlasClosedRealOneOneForm (ofFixedModel 1 P1) :=
  nativeClosedFormToAtlas projectiveNativeFSBackground.form

/-- Actual book data: 0 and the genuine FS logarithmic pole, at 0 and -1. -/
def data : PiecewiseLinearData fsForm where
  N := 1
  A := ![(fun _ => (0 : EReal)), projectiveLogSingularity]
  τ := ![(0 : ℝ), -1]
  strictAnti := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num at *
  isThetaPSH := by
    intro i
    fin_cases i
    · apply (isThetaPSH_iff_nativeThetaPotential _ _).mpr
      rw [fsForm, native_atlas_roundtrip]
      exact PluripolarCapacityDichotomy.isThetaPshPotential_zero _
    · apply (isThetaPSH_iff_nativeThetaPotential _ _).mpr
      rw [fsForm, native_atlas_roundtrip]
      exact isThetaPshPotential_projectiveNativeFS_of_source
        isThetaPSH_projectiveLogSingularity

/-- The literal pointwise upper envelope; no spatial regularization. -/
def envelope (s : ℝ) (p : P1) : EReal :=
  data.pointwiseUpperConcaveEnvelope s p

/-- At the pole the curve is supported at parameter zero. The open interval
proof must use positive scalar times bottom, not 0 times bottom. -/
theorem curve_at_origin (s : ℝ) :
    data.curve s projectiveOrigin = if s = 0 then 0 else ⊥ := by
  by_cases hs0 : s = 0
  · subst s
    have h := data.curve_tau 0
    change data.curve 0 = (fun _ => 0) at h
    simpa only [if_true] using congrFun h projectiveOrigin
  by_cases hspos : 0 < s
  · have h := data.curve_of_lt (s := s) (show data.τ 0 < s from hspos)
    rw [h, if_neg hs0]
  by_cases hslast : s ≤ -1
  · have h := data.curve_of_le_last (s := s)
      (show s ≤ data.τ (Fin.last data.N) from hslast)
    change data.curve s = projectiveLogSingularity at h
    rw [h, projectiveLogSingularity_origin, if_neg hs0]
  have hsneg : s < 0 := lt_of_le_of_ne (not_lt.mp hspos) hs0
  have ht0 : 0 < -s := neg_pos.mpr hsneg
  have ht1 : -s < 1 := by linarith
  have h := data.curve_affine 0 (by decide) ht0 ht1
  change data.curve ((1 - -s) * 0 + -s * -1) =
    PiecewiseLinearData.affineComb (-s) (data.A 0) (data.A (Fin.last 1)) at h
  have heq : (1 - -s) * 0 + -s * -1 = s := by ring
  rw [heq] at h
  rw [h]
  change (((1 - -s : ℝ) : EReal) * 0 + ((-s : ℝ) : EReal) *
    projectiveLogSingularity projectiveOrigin) = if s = 0 then 0 else ⊥
  rw [mul_zero, zero_add, projectiveLogSingularity_origin,
    EReal.coe_mul_bot_of_pos ht0, if_neg hs0]

/-- On finite nonzero chart points the log potential is a finite nonpositive real. -/
theorem log_value_finite_nonpos (z : ComplexModel 1) (hz : z 0 ≠ 0) :
    ∃ c : ℝ, c ≤ 0 ∧
      projectiveLogSingularity ((projectiveModelChart false).symm z) = (c : EReal) := by
  let x : ℝ := ‖z 0‖ ^ 2
  have hx : 0 < x := pow_pos (norm_pos_iff.mpr hz) 2
  have hd : 0 < 1 + x := by linarith
  have hratio : 0 < x / (1 + x) := div_pos hx hd
  have hratio1 : x / (1 + x) ≤ 1 := (div_le_one₀ hd).mpr (by linarith)
  refine ⟨Real.log (x / (1 + x)), Real.log_nonpos hratio.le hratio1, ?_⟩
  have h := projectiveLogSingularity_finite z
  rw [Complex.normSq_eq_norm_sq, ENNReal.log_ofReal_of_pos hratio] at h
  exact h

/-- The whole original curve is nonpositive at finite nonzero chart points. -/
theorem curve_nonpos (z : ComplexModel 1) (hz : z 0 ≠ 0) (s : ℝ) :
    data.curve s ((projectiveModelChart false).symm z) ≤ 0 := by
  obtain ⟨c, hc, heq⟩ := log_value_finite_nonpos z hz
  by_cases hspos : 0 < s
  · rw [data.curve_of_lt (show data.τ 0 < s from hspos)]
    exact bot_le
  by_cases hslast : s ≤ -1
  · have h := data.curve_of_le_last (s := s)
      (show s ≤ data.τ (Fin.last data.N) from hslast)
    change data.curve s = projectiveLogSingularity at h
    rw [h, heq]
    exact EReal.coe_le_coe hc
  by_cases hs0 : s = 0
  · subst s
    have h := data.curve_tau 0
    change data.curve 0 = (fun _ => 0) at h
    rw [h]
  have hsneg : s < 0 := lt_of_le_of_ne (not_lt.mp hspos) hs0
  have ht0 : 0 < -s := neg_pos.mpr hsneg
  have ht1 : -s < 1 := by linarith
  have h := data.curve_affine 0 (by decide) ht0 ht1
  change data.curve ((1 - -s) * 0 + -s * -1) =
    PiecewiseLinearData.affineComb (-s) (data.A 0) (data.A (Fin.last 1)) at h
  have heqs : (1 - -s) * 0 + -s * -1 = s := by ring
  rw [heqs] at h
  rw [h]
  change (((1 - -s : ℝ) : EReal) * 0 + ((-s : ℝ) : EReal) *
    projectiveLogSingularity ((projectiveModelChart false).symm z)) ≤ 0
  rw [mul_zero, zero_add, heq, ← EReal.coe_mul]
  have hc' : (-s) * c ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht0.le hc
  exact EReal.coe_le_coe hc'

/-- At the actual logarithmic pole the literal upper envelope is -∞. -/
theorem envelope_at_origin : envelope (-1) projectiveOrigin = ⊥ := by
  have hfun : (fun s : ℝ => -data.curve s projectiveOrigin) =
      SGPT.Convex.indicator ({0} : Set ℝ) := by
    funext s
    rw [curve_at_origin]
    by_cases hs : s = 0 <;> simp [SGPT.Convex.indicator, hs]
  have hconv : SGPT.Convex.IsConvex (fun s : ℝ => -data.curve s projectiveOrigin) := by
    rw [hfun]
    exact SGPT.Convex.isConvex_indicator (convex_singleton 0)
  have heq := SGPT.Convex.lowerConvexEnvelope_eq_self hconv
  change -SGPT.Convex.lowerConvexEnvelope
    (fun s => -data.curve s projectiveOrigin) (-1) = ⊥
  rw [heq]
  change -(-data.curve (-1) projectiveOrigin) = ⊥
  rw [curve_at_origin]
  norm_num

/-- Every nonzero finite coordinate has envelope value 0 at parameter -1. -/
theorem envelope_at_nonzero (z : ComplexModel 1) (hz : z 0 ≠ 0) :
    envelope (-1) ((projectiveModelChart false).symm z) = 0 := by
  obtain ⟨c, hc, heq⟩ := log_value_finite_nonpos z hz
  have hzero : data.curve 0 ((projectiveModelChart false).symm z) = 0 := by
    have h := data.curve_tau 0
    change data.curve 0 = (fun _ => 0) at h
    exact congrFun h ((projectiveModelChart false).symm z)
  have htail : ∀ t : ℝ, t ≤ -1 →
      data.curve t ((projectiveModelChart false).symm z) = (c : EReal) := by
    intro t ht
    have h := data.curve_of_le_last (s := t)
      (show t ≤ data.τ (Fin.last data.N) from ht)
    change data.curve t = projectiveLogSingularity at h
    rw [h]
    exact heq
  exact upper_envelope_neg_one_eq_zero (curve_nonpos z hz) hzero c htail

/-- The two exact point-value results imply failure of spatial USC. -/
theorem envelope_not_upperSemicontinuous :
    ¬ UpperSemicontinuous (envelope (-1)) := by
  intro hu
  have hp : envelope (-1) projectiveOrigin < (0 : EReal) := by
    rw [envelope_at_origin]
    exact EReal.bot_lt_coe 0
  have hnear := hu projectiveOrigin 0 hp
  have hzT : (0 : ComplexModel 1) ∈ (projectiveModelChart false).target := by
    simp [projectiveModelChart, projectiveQuotientScalarChart_target]
  have hnear' : ∀ᶠ z in 𝓝 (0 : ComplexModel 1),
      envelope (-1) ((projectiveModelChart false).symm z) < 0 := by
    have h := ((projectiveModelChart false).symm.continuousAt hzT).eventually hnear
    simpa [projectiveOrigin] using h
  obtain ⟨z, hz, hzD⟩ := (projectiveCoordinate_frequently_ne_zero 0).and_eventually
    hnear' |>.exists
  have hz' : z 0 ≠ 0 := by simpa [projectiveModelEquiv_symm_apply] using hz
  have hval := envelope_at_nonzero z hz'
  have hlt : envelope (-1) ((projectiveModelChart false).symm z) < 0 := hzD
  rw [hval] at hlt
  exact lt_irrefl _ hlt

/-- The same source slice fails the original theta-psh predicate. -/
theorem envelope_not_thetaPSH :
    ¬ (ofFixedModel 1 P1).IsThetaPSH fsForm (envelope (-1)) := by
  intro h
  apply envelope_not_upperSemicontinuous
  exact ((isThetaPSH_iff_nativeThetaPotential fsForm _).mp h).1.quasiPlurisubharmonic.upperSemicontinuous

end SGPT.NAPotential.ProjectiveLineEnvelope
