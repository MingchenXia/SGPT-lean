import SGPT.Foundations.Analysis.Pending.ModificationReferenceVolumeLimit
import SGPT.Foundations.Analysis.Pending.AmbientMassBackgroundMonotone
import SGPT.Foundations.Analysis.Pending.LowerCalibratedCurrentACLimit
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

set_option autoImplicit false

/-! # Global measure lower calibration in original chart densities
The full statements and ENTIRE blueprint proofs precede implementation.
Reference: Boucksom 4.6 and 3.5, supplementary measure descent argument.
-/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal Distributions
universe u
namespace SGPT.Foundations.Analysis.Pending.GlobalACLowerCalibration

open FirstPass FirstPass.PositiveClasses FirstPass.MongeAmpere GlobalCurrents
  IntegrationCurrent GlobalNonPluripolar DiagonalMass
  AnalyticModificationLocalDiscrepancy AnalyticModificationStrongPullback
  GlobalPositiveCurrentACRestriction GlobalPositiveCurrentACTopMeasure
  ActualAnalyticCurrentLocalDensity LocalProductCurrents LocalCurrentDeterminant
  PositiveCurrentACTopMeasure TopDegreeDensity

section Reference
variable {m : ℕ} {X Y : Type u} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [ChartedSpace (ComplexModel (m+1)) X] [IsComplexManifold (m+1) X]
  [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [ChartedSpace (ComplexModel (m+1)) Y] [IsComplexManifold (m+1) Y]

/-- The natural semipositive enlargement produces the whole original-space
reference measure lower bound, without a measure-comparison input. -/
theorem reference_volume_le_map [CompactSpace X]
    {π : Y → X} (hπ : IsAnalyticModification (n := m+1) π)
    (ω : KahlerBackground (m+1) X) (ωY Ω : KahlerBackground (m+1) Y)
    {δ : ℝ} (hδ : 0 < δ)
    (hΩ : Ω.form = ClosedRealOneOneForm.pullback hπ.1 ω.form + δ • ωY.form) :
    letI : CompactSpace Y := compactSpace_of_isAnalyticModification hπ
    kahlerVolume ω ≤ (kahlerVolume Ω).map π := by
  let : CompactSpace Y := compactSpace_of_isAnalyticModification hπ
  let A := ClosedRealOneOneForm.pullback hπ.1 ω.form
  have hA := (LocalPotentials.isThetaPshPotential_zero_iff A).mpr
    (ClosedRealOneOneForm.pullback_isSemipositive hπ.1 ω.isSemipositive)
  have hΩpsh : ThetaPlurisubharmonic (A + δ • ωY.form).val (fun _ => 0) := by
    rw [← hΩ]
    exact ((LocalPotentials.isThetaPshPotential_zero_iff Ω.form).mpr Ω.isSemipositive).1
  have hle := AmbientMassBackgroundMonotone.globalMixedMeasure_diagonal_le_add_smul
    ωY.isSemipositive hδ hA hΩpsh
  have hmap := Measure.map_mono hle hπ.1.continuous.measurable
  rw [ModificationReferenceVolumeLimit.map_zero_reference_measure hπ ω] at hmap
  have hr : globalMixedMeasure (fun _ : Fin (m+1) => A + δ • ωY.form)
      (fun _ _ => 0) (fun _ => hΩpsh) = kahlerVolume Ω := by
    exact AmbientMassBackgroundMonotone.globalMixedMeasure_congr_tuples
      (funext fun _ => hΩ.symm) rfl (fun _ => hΩpsh)
      (fun _ => ((LocalPotentials.isThetaPshPotential_zero_iff Ω.form).mpr
        Ω.isSemipositive).1)
  rwa [hr] at hmap
end Reference

variable {m : ℕ} {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel (m+1)) M] [IsComplexManifold (m+1) M]

private theorem global_inter_chart [CompactSpace M]
    (T : GlobalCurrent (m+1) M (degreeTwo (Nat.succ_pos m)))
    (hT : IsFullPositive T) (e : ComplexChart (m+1) M) (S : Set M) :
    globalACtopMeasure T hT (S ∩ e.val.source) =
      acTopMeasure (isPositive_chartSpanCurrent T hT e)
        (e.val.target ∩ e.val.symm ⁻¹' S) := by
  have hInv : MeasurableEmbedding (fun z : e.val.target => e.val.symm z) :=
    (MeasurableEmbedding.subtype_coe e.val.open_source.measurableSet).comp
      (e.val.toHomeomorphSourceTarget).symm.measurableEmbedding
  have hsub : MeasurableEmbedding (Subtype.val : e.val.target → ComplexModel (m+1)) :=
    MeasurableEmbedding.subtype_coe e.val.open_target.measurableSet
  have h := congrArg (fun μ : Measure M => μ S) (globalACtopMeasure_restrict_chart T hT e)
  rw [Measure.restrict_apply' e.val.open_source.measurableSet] at h
  refine h.trans ?_
  change (((acTopMeasure (isPositive_chartSpanCurrent T hT e)).comap
      (Subtype.val : e.val.target → ComplexModel (m+1))).map
        (fun z : e.val.target => e.val.symm z)) S = _
  rw [hInv.map_apply, hsub.comap_apply]
  congr 1
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.property, hw⟩
  · intro hz
    exact ⟨⟨z, hz.1⟩, hz.2, rfl⟩

private theorem local_measure_le [CompactSpace M]
    (R T : GlobalCurrent (m+1) M (degreeTwo (Nat.succ_pos m)))
    (hR : IsFullPositive R) (hT : IsFullPositive T)
    {c : ℝ} (h : ENNReal.ofReal c • globalACtopMeasure R hR ≤ globalACtopMeasure T hT)
    (e : ComplexChart (m+1) M) :
    ENNReal.ofReal c • acTopMeasure (isPositive_chartSpanCurrent R hR e) ≤
      acTopMeasure (isPositive_chartSpanCurrent T hT e) := by
  apply Measure.le_iff'.mpr
  intro K
  let Q : Set M := e.val.symm '' (K ∩ e.val.target)
  have hQ : Q ⊆ e.val.source := by
    rintro _ ⟨z, hz, rfl⟩
    exact e.val.map_target hz.2
  have hset : e.val.target ∩ e.val.symm ⁻¹' Q = K ∩ e.val.target := by
    ext z
    constructor
    · rintro ⟨hz, w, hw, heq⟩
      have hwz : w = z := by
        calc w = e.val (e.val.symm w) := (e.val.right_inv hw.2).symm
          _ = e.val (e.val.symm z) := congrArg e.val heq
          _ = z := e.val.right_inv hz
      exact hwz ▸ hw
    · intro hz
      exact ⟨hz.2, z, hz, rfl⟩
  have hRset := global_inter_chart R hR e Q
  have hTset := global_inter_chart T hT e Q
  rw [inter_eq_left.mpr hQ, hset] at hRset hTset
  have hh := Measure.le_iff'.mp h Q
  rw [Measure.smul_apply, hRset, hTset] at hh
  have hs (S : GlobalCurrent (m+1) M (degreeTwo (Nat.succ_pos m)))
      (hS : IsFullPositive S) :
      acTopMeasure (isPositive_chartSpanCurrent S hS e) (K ∩ e.val.target) =
        acTopMeasure (isPositive_chartSpanCurrent S hS e) K := by
    unfold acTopMeasure
    rw [Measure.restrict_apply' (chartTarget e).isOpen.measurableSet,
      Measure.restrict_apply' (chartTarget e).isOpen.measurableSet]
    congr 1
    change (K ∩ e.val.target) ∩ e.val.target = K ∩ e.val.target
    rw [inter_assoc, inter_self]
  rw [hs R hR, hs T hT] at hh
  simpa only [Measure.smul_apply] using hh

private theorem topDensity_eq_det {U : Opens (ComplexModel (m+1))}
    {S : LocalProductCurrent (m+1) U m} (hS : IsPositive S) (x : ComplexModel (m+1)) :
    actualTopPowerDensity (acForm hS x) =
      ((m+1).factorial : ℝ) / Real.pi ^ (m+1) * (acMatrix hS x).det.re := by
  rw [actualTopPowerDensity_eq_normalizedTopPowerDensity _ (isOneOne_acForm hS x),
    normalizedTopPowerDensity, complexTopCoefficient_eq]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rfl

/-- Genuine global measure order internally supplies the original chart density
order. No determinant-integrability or analytic-singularity input is needed. -/
theorem ae_chart_density_le_of_measure_le [CompactSpace M]
    (R T : GlobalCurrent (m+1) M (degreeTwo (Nat.succ_pos m)))
    (hR : IsFullPositive R) (hT : IsFullPositive T) {c : ℝ} (hc : 0 ≤ c)
    (h : ENNReal.ofReal c • globalACtopMeasure R hR ≤ globalACtopMeasure T hT)
    (e : ComplexChart (m+1) M) :
    ∀ᵐ x ∂volume.restrict (chartTarget e),
      c * actualTopPowerDensity (acForm (isPositive_chartSpanCurrent R hR e) x) ≤
        actualTopPowerDensity (acForm (isPositive_chartSpanCurrent T hT e) x) := by
  let hRe := isPositive_chartSpanCurrent R hR e
  let hTe := isPositive_chartSpanCurrent T hT e
  have hm := local_measure_le R T hR hT h e
  unfold acTopMeasure at hm
  rw [← Measure.restrict_smul, ← withDensity_smul' _ _ ENNReal.ofReal_ne_top,
    restrict_withDensity (chartTarget e).isOpen.measurableSet,
    restrict_withDensity (chartTarget e).isOpen.measurableSet] at hm
  have hf : Measurable (fun x => ENNReal.ofReal c *
      ENNReal.ofReal (actualTopPowerDensity (acForm hRe x))) :=
    measurable_const.mul (ENNReal.measurable_ofReal.comp (measurable_acTopDensity hRe))
  have hAE := ae_le_of_forall_setLIntegral_le_of_sigmaFinite hf (fun s hs _ => by
    have hh := Measure.le_iff'.mp hm s
    simpa only [withDensity_apply _ hs, Pi.smul_apply, smul_eq_mul] using hh)
  filter_upwards [hAE, ae_restrict_of_ae (ae_posSemidef_acMatrix hTe)] with x hx hpos
  have hn : 0 ≤ actualTopPowerDensity (acForm hTe x) := by
    rw [topDensity_eq_det]
    exact mul_nonneg (by positivity) (MinkowskiDeterminant.re_det_nonneg hpos)
  rw [← ENNReal.ofReal_mul hc] at hx
  exact (ENNReal.ofReal_le_ofReal_iff hn).mp hx

/-- Actual per-stage global measure bounds, with the actual full weak tests,
produce the global limit bound without caller-supplied chart density data. -/
theorem measure_le_of_lower_calibrated_filter [CompactSpace M]
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (T : ι → GlobalCurrent (m+1) M (degreeTwo (Nat.succ_pos m)))
    (T₀ R : GlobalCurrent (m+1) M (degreeTwo (Nat.succ_pos m)))
    (hT : ∀ i, IsFullPositive (T i)) (hT₀ : IsFullPositive T₀) (hR : IsFullPositive R)
    (hconv : ∀ (e : ComplexChart (m+1) M) γ φ,
      Tendsto (fun i => chartSpanCurrent (T i) e γ φ) l
        (𝓝 (chartSpanCurrent T₀ e γ φ)))
    {c : ι → ℝ} {a : ℝ} (hc : ∀ i, 0 ≤ c i) (hca : Tendsto c l (𝓝 a))
    (hcal : ∀ i, ENNReal.ofReal (c i) • globalACtopMeasure R hR ≤
      globalACtopMeasure (T i) (hT i)) :
    ENNReal.ofReal a • globalACtopMeasure R hR ≤ globalACtopMeasure T₀ hT₀ :=
  LowerCalibratedCurrentACLimit.globalACtopMeasure_le_of_lower_calibrated_filter
    T T₀ R hT hT₀ hR hconv hc hca
    (fun i e => ae_chart_density_le_of_measure_le R (T i) hR (hT i) (hc i) (hcal i) e)

end SGPT.Foundations.Analysis.Pending.GlobalACLowerCalibration
