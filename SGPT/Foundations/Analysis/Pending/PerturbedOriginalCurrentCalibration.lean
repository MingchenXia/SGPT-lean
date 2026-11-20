import SGPT.Foundations.Analysis.Pending.ResolvedOriginalACCalibration
import SGPT.Foundations.Analysis.Pending.GlobalACLowerCalibration
import SGPT.Foundations.Analysis.Pending.FixedBottChernClassCurrentCompactness

set_option autoImplicit false

/-!
# A calibrated original current in an enlarged class

The actual resolution calibration and fixed-class weak compactness produce
an original positive closed current with an entire AC measure lower bound.
No family, class equality, weak limit or calibration is supplied as an input.
Reference: Boucksom 4.6, first reference-perturbation limit, with the
lower-calibration adaptation of 3.5. The complete blueprint statement and
ENTIRE mathematical proof precede the implementation.
-/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal Distributions
universe u
namespace SGPT.Foundations.Analysis.Pending.PerturbedOriginalCurrentCalibration

open FirstPass FirstPass.PositiveClasses FirstPass.MongeAmpere
  FirstPass.GlobalAnalyticSingularities FirstPass.NumericalRestrictedVolumeScaffold
  FirstPass.BlowupSequences IntegrationCurrent BoundedGlobalProduct NefMixedMass
  CurrentBottChernClass CanonicalCurrentFrame GlobalCurrentPotentials
  ThetaPotentialCurrentBottChernClass
  NaturalThetaPshGeometricCurrent NaturalThetaPshClosedCurrent
  GlobalPositiveCurrentACRestriction GlobalPositiveCurrentACTopMeasure
  ActualAnalyticCurrentLocalDensity AnalyticModificationLocalDiscrepancy

private theorem isAnalyticModification_id
    {n : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] :
    IsAnalyticModification (n := n) (id : X → X) := by
  refine ⟨contMDiff_id, isProperMap_id, ∅, ∅, id,
    isClosed_empty, isComplexAnalyticSubset_empty, ?_,
    isClosed_empty, isComplexAnalyticSubset_empty, ?_, ?_,
    contMDiff_id.contMDiffOn, fun _ _ => rfl, fun _ _ => rfl⟩ <;> simp

private theorem isAnalyticModification_of_isBlowupSequence
    {n : ℕ} {X Y : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    {π : Y → X} (hπ : IsBlowupSequence n X Y π) :
    IsAnalyticModification (n := n) π := by
  induction hπ with
  | refl => exact isAnalyticModification_id
  | step f C b _ hb ih =>
      exact AnalyticModificationComposition.isAnalyticModification_comp ih
        (PrescribedBlowupDomination.isAnalyticModification_of_isBlowupAlong hb)

private theorem zero_has_analytic_type
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] :
    HasManifoldAnalyticSingularitiesSmoothOffPole (n := n) (fun _ : M => 0) := by
  intro e z _
  let one : Fin 1 → ComplexModel n → ℂ := fun _ _ => 1
  have hlog (y : ComplexModel n) : generatorLog one y = 0 := by
    rw [generatorLog_eq_log_sum]
    simp [one]
  refine ⟨1, 1, one, one_pos, ⟨univ, isOpen_univ, mem_univ _,
    fun _ => differentiableOn_const 1⟩, fun _ => 0,
    boundedRealGermAt_of_continuousAt continuousAt_const,
    Eventually.of_forall fun _ _ => contDiffAt_const,
    Eventually.of_forall fun y => ?_⟩
  simp only [chartFunction, hlog, mul_zero, EReal.coe_zero, add_zero]

variable {m : ℕ} {X : Type u} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [ChartedSpace (ComplexModel (m+1)) X] [IsComplexManifold (m+1) X]
  [CompactSpace X] [ConnectedSpace X]

/-- An arbitrary original positive closed current internally produces a
positive closed current in its epsilon-enlarged class whose entire AC measure
has the original total AC mass as a lower benchmark. Zero mass is included. -/
theorem exists_perturbed_original_current_ac_lower_bound
    (ω : KahlerBackground (m+1) X)
    (T : ClosedOneOneCurrent (M := X) (canonicalBasis (m+1)) (Nat.succ_pos m))
    (hT : IsFullPositive T.val) {ε : ℝ} (hε : 0 < ε) :
    globalACtopMeasure T.val hT univ < ⊤ ∧
    ∃ (S : ClosedOneOneCurrent (M := X) (canonicalBasis (m+1)) (Nat.succ_pos m))
      (hS : IsFullPositive S.val),
      bottChernClass (canonicalBasis (m+1)) (Nat.succ_pos m) S =
        bottChernClass (canonicalBasis (m+1)) (Nat.succ_pos m) T +
          ε • RealBottChern.ofRepresentative ω.form ∧
      ENNReal.ofReal ((globalACtopMeasure T.val hT).real univ /
        (kahlerVolume ω).real univ) • kahlerVolume ω ≤ globalACtopMeasure S.val hS := by
  classical
  obtain ⟨θ, _hθ, Y, tY, cY, mY, π, hπ, hcpt, hconn, ωY, F,
      _hnef, hmajor, hfamily⟩ :=
    ResolvedOriginalACCalibration.exists_original_space_calibrations ω T hT hε
  let : MeasurableSpace Y := borel Y
  have : BorelSpace Y := ⟨rfl⟩
  let β := ClosedRealOneOneForm.pullback hπ.contMDiff (θ + ε • ω.form) - F.curvature
  let I : ℝ := slotIntegral ωY (fun _ => β)
  have hπa := isAnalyticModification_of_isBlowupSequence hπ
  let δ : ℕ → ℝ := fun j => 1 / (j+1 : ℝ)
  have hδ (j : ℕ) : 0 < δ j := by dsimp [δ]; positivity
  have hδlim : Tendsto δ atTop (𝓝 0) := by
    simpa only [δ, one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  choose Ω hΩ s hs hc hclasses hcal using fun j => hfamily (δ j) (hδ j)
  let K (j : ℕ) := thetaClosedCurrent (θ + ε • ω.form) (s j) (hs j)
  have hK (j : ℕ) : IsFullPositive (K j).val := fun e α hα =>
    thetaPotentialCurrent_full_positive (θ + ε • ω.form).val (s j) (hs j) e α hα
  let V : ℝ := (kahlerVolume ω).real univ
  let c (j : ℕ) : ℝ := I / (kahlerVolume (Ω j)).real univ
  let a : ℝ := I / V
  have hV : 0 < V := NefCoreKahlerCurrent.kahlerVolume_real_univ_pos ω
  have hvol : Tendsto (fun j => (kahlerVolume (Ω j)).real univ) atTop (𝓝 V) := by
    have h := ModificationReferenceVolumeLimit.tendsto_integral_map_reference_volume
      hπa ω ωY δ hδlim Ω hΩ (fun _ => (1 : ℝ)) continuous_const
    simpa only [V, integral_const, Measure.real, Measure.map_apply
      hπa.1.continuous.measurable MeasurableSet.univ, preimage_univ,
      smul_eq_mul, mul_one] using h
  have hclim : Tendsto c atTop (𝓝 a) := tendsto_const_nhds.div hvol hV.ne'
  have hc' (j : ℕ) : 0 ≤ c j := hc j
  have ha : 0 ≤ a := ge_of_tendsto hclim (Eventually.of_forall hc')
  have hI : 0 ≤ I := by
    have hmul : a * V = I := div_mul_cancel₀ I hV.ne'
    exact hmul ▸ mul_nonneg ha hV.le
  have hfinite : globalACtopMeasure T.val hT univ < ⊤ :=
    hmajor.trans_lt ENNReal.ofReal_lt_top
  have hreal : (globalACtopMeasure T.val hT).real univ ≤ I := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmajor
    rwa [ENNReal.toReal_ofReal hI] at h
  have hba : (globalACtopMeasure T.val hT).real univ / V ≤ a :=
    (div_le_div_iff_of_pos_right hV).mpr hreal
  let U : Ultrafilter ℕ := Ultrafilter.of atTop
  have hU : (U : Filter ℕ) ≤ atTop := Ultrafilter.of_le atTop
  obtain ⟨S, hS, hclass, hweak⟩ :=
    FixedBottChernClassCurrentCompactness.exists_tendsto_same_class_originalClosedPositiveCurrent
      U (bottChernClass (canonicalBasis (m+1)) (Nat.succ_pos m) T +
        ε • RealBottChern.ofRepresentative ω.form) K hK hclasses
  have hu0 := (LocalPotentials.isThetaPshPotential_zero_iff ω.form).mpr ω.isSemipositive
  let R := thetaPotentialCurrent ω.form.val (fun _ => 0) hu0
  have hR : IsFullPositive R := fun e α hα =>
    thetaPotentialCurrent_full_positive ω.form.val (fun _ => 0) hu0 e α hα
  have href : globalACtopMeasure R hR = kahlerVolume ω :=
    OriginalCurrentAnalyticACMajorization.globalACtopMeasure_theta_analytic_eq
      ω.form hu0 zero_has_analytic_type
  have hlower (j : ℕ) :
      ENNReal.ofReal (c j) • globalACtopMeasure R hR ≤ globalACtopMeasure (K j).val (hK j) := by
    rw [href]
    change ENNReal.ofReal (c j) • kahlerVolume ω ≤
      globalACtopMeasure (thetaPotentialCurrent (θ + ε • ω.form).val (s j) (hs j)) _
    rw [hcal j]
    apply Measure.le_iff'.mpr
    intro A
    simp only [Measure.smul_apply, smul_eq_mul]
    exact mul_le_mul_right (Measure.le_iff'.mp
      (GlobalACLowerCalibration.reference_volume_le_map hπa ω ωY (Ω j) (hδ j) (hΩ j)) A) _
  have hconv (e : ComplexChart (m+1) X) γ φ :
      Tendsto (fun j => chartSpanCurrent (K j).val e γ φ) (U : Filter ℕ)
        (𝓝 (chartSpanCurrent S.val e γ φ)) := hweak e _
  have hlimit := GlobalACLowerCalibration.measure_le_of_lower_calibrated_filter
    (fun j => (K j).val) S.val R hK hS hR hconv hc' (hclim.mono_left hU) hlower
  rw [href] at hlimit
  refine ⟨hfinite, S, hS, hclass, ?_⟩
  apply le_trans ?_ hlimit
  apply Measure.le_iff'.mpr
  intro A
  simp only [Measure.smul_apply, smul_eq_mul]
  simpa only [mul_comm] using mul_le_mul_right (ENNReal.ofReal_le_ofReal hba)
    (kahlerVolume ω A)

end SGPT.Foundations.Analysis.Pending.PerturbedOriginalCurrentCalibration
