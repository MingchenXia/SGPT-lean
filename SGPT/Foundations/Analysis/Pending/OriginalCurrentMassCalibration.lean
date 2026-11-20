import SGPT.Foundations.Analysis.Pending.PerturbedOriginalCurrentCalibration
import SGPT.Foundations.Analysis.Pending.MovingBottChernClassCurrentCompactness
import SGPT.Foundations.Analysis.Pending.XiaoPureSmoothBottChernClosure

set_option autoImplicit false

/-!
# Original-class calibration of an arbitrary current mass

The epsilon-to-zero moving-class weak limit is constructed internally from
an arbitrary original positive closed current. Its actual original AC mass
is the whole-measure lower benchmark. Boucksom 4.6, second limit, using the
lower-calibration adaptation of 3.5. The volume supremum is a later step.
The complete blueprint statement and ENTIRE proof precede implementation.
-/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal Distributions
universe u
namespace SGPT.Foundations.Analysis.Pending.OriginalCurrentMassCalibration

open FirstPass FirstPass.PositiveClasses FirstPass.MongeAmpere
  FirstPass.GlobalAnalyticSingularities FirstPass.NumericalRestrictedVolumeScaffold
  CurrentBottChernClass CanonicalCurrentFrame GlobalCurrentPotentials
  ThetaPotentialCurrentBottChernClass NaturalThetaPshGeometricCurrent
  NaturalThetaPshClosedCurrent GlobalPositiveCurrentACRestriction
  GlobalPositiveCurrentACTopMeasure ActualAnalyticCurrentLocalDensity
  IntegrationCurrent XiaoPureSmoothTopology XiaoPureSmoothBottChernClosure

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

/-- An arbitrary original positive closed current internally produces an
original-class positive closed current with the entire original mass benchmark.
No class limit, family or weak-current calibration is an input. -/
theorem exists_same_class_original_current_ac_lower_bound
    (ω : KahlerBackground (m+1) X)
    (T : ClosedOneOneCurrent (M := X) (canonicalBasis (m+1)) (Nat.succ_pos m))
    (hT : IsFullPositive T.val) :
    globalACtopMeasure T.val hT univ < ⊤ ∧
    ∃ (S : ClosedOneOneCurrent (M := X) (canonicalBasis (m+1)) (Nat.succ_pos m))
      (hS : IsFullPositive S.val),
      bottChernClass (canonicalBasis (m+1)) (Nat.succ_pos m) S =
        bottChernClass (canonicalBasis (m+1)) (Nat.succ_pos m) T ∧
      ENNReal.ofReal ((globalACtopMeasure T.val hT).real univ /
        (kahlerVolume ω).real univ) • kahlerVolume ω ≤ globalACtopMeasure S.val hS := by
  classical
  have hfinite := (PerturbedOriginalCurrentCalibration.exists_perturbed_original_current_ac_lower_bound
    ω T hT (ε := 1) zero_lt_one).1
  let ε : ℕ → ℝ := fun j => 1 / (j+1 : ℝ)
  have hε (j : ℕ) : 0 < ε j := by dsimp [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε, one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  choose K hK hclass hcal using fun j =>
    (PerturbedOriginalCurrentCalibration.exists_perturbed_original_current_ac_lower_bound
      ω T hT (hε j)).2
  obtain ⟨θ, u, hu, heq, _hread⟩ :=
    OriginalPositiveCurrentThetaRepresentation.exists_theta_representation_of_original_closed_full_positive
      T.val T.property.1 T.property.2 hT
  have hTc : T = thetaClosedCurrent θ u hu := Subtype.ext heq
  have hθ : bottChernClass (canonicalBasis (m+1)) (Nat.succ_pos m) T =
      RealBottChern.ofRepresentative θ := by
    rw [hTc, bottChernClass_thetaClosedCurrent]
  have hclasses : Tendsto (fun j => bottChernClass (canonicalBasis (m+1))
      (Nat.succ_pos m) (K j)) atTop
      (@nhds (RealBottChern (m+1) X) classPureSmoothTopology
        (bottChernClass (canonicalBasis (m+1)) (Nat.succ_pos m) T)) := by
    let : TopologicalSpace (ClosedRealOneOneForm (m+1) X) := formPureSmoothTopology
    let : TopologicalSpace (RealBottChern (m+1) X) := classPureSmoothTopology
    let : IsTopologicalAddGroup (ClosedRealOneOneForm (m+1) X) :=
      formPureSmoothTopology_isTopologicalAddGroup
    let : ContinuousSMul ℝ (ClosedRealOneOneForm (m+1) X) := formPureSmoothTopology_continuousSMul
    have hform : Tendsto (fun j => θ + ε j • ω.form) atTop (𝓝 θ) := by
      simpa only [zero_smul, add_zero] using tendsto_const_nhds.add (hεlim.smul_const ω.form)
    have h := (isOpenQuotientMap_ofRepresentative ω).continuous.tendsto θ |>.comp hform
    have hf : (fun j => bottChernClass (canonicalBasis (m+1)) (Nat.succ_pos m) (K j)) =
        RealBottChern.ofRepresentative ∘ (fun j => θ + ε j • ω.form) := by
      funext j
      simp only [Function.comp_apply, hclass j, hθ,
        RealBottChern.ofRepresentative_add, RealBottChern.ofRepresentative_smul]
    rw [hf, hθ]
    exact h
  let U : Ultrafilter ℕ := Ultrafilter.of atTop
  have hU : (U : Filter ℕ) ≤ atTop := Ultrafilter.of_le atTop
  obtain ⟨S, hS, hSclass, hweak⟩ :=
    MovingBottChernClassCurrentCompactness.exists_tendsto_moving_class_originalClosedPositiveCurrent
      ω U hU (bottChernClass (canonicalBasis (m+1)) (Nat.succ_pos m) T) K hK hclasses
  have hu0 := (LocalPotentials.isThetaPshPotential_zero_iff ω.form).mpr ω.isSemipositive
  let R := thetaPotentialCurrent ω.form.val (fun _ => 0) hu0
  have hR : IsFullPositive R := fun e α hα =>
    thetaPotentialCurrent_full_positive ω.form.val (fun _ => 0) hu0 e α hα
  have href : globalACtopMeasure R hR = kahlerVolume ω :=
    OriginalCurrentAnalyticACMajorization.globalACtopMeasure_theta_analytic_eq
      ω.form hu0 zero_has_analytic_type
  let b : ℝ := (globalACtopMeasure T.val hT).real univ / (kahlerVolume ω).real univ
  have hb : 0 ≤ b := div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hconv (e : ComplexChart (m+1) X) γ φ :
      Tendsto (fun j => chartSpanCurrent (K j).val e γ φ) (U : Filter ℕ)
        (𝓝 (chartSpanCurrent S.val e γ φ)) := hweak e _
  have hlower (j : ℕ) :
      ENNReal.ofReal b • globalACtopMeasure R hR ≤ globalACtopMeasure (K j).val (hK j) := by
    rw [href]
    exact hcal j
  have hlimit := GlobalACLowerCalibration.measure_le_of_lower_calibrated_filter
    (fun j => (K j).val) S.val R hK hS hR hconv (c := fun _ => b)
    (fun _ => hb) (tendsto_const_nhds (x := b)) hlower
  rw [href] at hlimit
  exact ⟨hfinite, S, hS, hSclass, hlimit⟩

end SGPT.Foundations.Analysis.Pending.OriginalCurrentMassCalibration
