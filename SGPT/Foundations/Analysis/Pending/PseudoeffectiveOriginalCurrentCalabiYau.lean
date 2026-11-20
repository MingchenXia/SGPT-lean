import SGPT.Foundations.Analysis.Pending.OriginalCurrentMassCalibration
import SGPT.Foundations.Analysis.Pending.OriginalCurrentACVolume

set_option autoImplicit false

/-!
# Calabi--Yau measure calibration for the actual pseudoeffective class

Natural potential pseudoeffectivity and the actual original-current volume
supremum internally produce an original positive closed current whose entire
canonical AC measure is exactly calibrated to that volume. All near-supremum
currents, class identities and weak limits are internal. Boucksom 4.6;
positive-dimensional compact connected Kahler domain, including zero volume.
The complete blueprint statement and ENTIRE proof precede implementation.
-/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal Distributions
universe u
namespace SGPT.Foundations.Analysis.Pending.PseudoeffectiveOriginalCurrentCalabiYau

open FirstPass FirstPass.PositiveClasses FirstPass.MongeAmpere
  FirstPass.GlobalAnalyticSingularities FirstPass.NumericalRestrictedVolumeScaffold
  CurrentBottChernClass CanonicalCurrentFrame GlobalCurrentPotentials
  ThetaPotentialCurrentBottChernClass NaturalThetaPshGeometricCurrent
  NaturalThetaPshClosedCurrent GlobalPositiveCurrentACRestriction
  GlobalPositiveCurrentACTopMeasure ActualAnalyticCurrentLocalDensity IntegrationCurrent
  OriginalCurrentACVolume

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

omit [MeasurableSpace X] [BorelSpace X] [ConnectedSpace X] in
private theorem exists_original_current_of_class_pseudoeffective
    (α : RealBottChern (m+1) X) : ClassPseudoeffectiveViaPotentials α →
    ∃ (T : ClosedOneOneCurrent (M := X) (canonicalBasis (m+1)) (Nat.succ_pos m))
      (_hT : IsFullPositive T.val),
      bottChernClass (canonicalBasis (m+1)) (Nat.succ_pos m) T = α := by
  refine Quotient.inductionOn α ?_
  intro θ hθ
  obtain ⟨u, hu⟩ := hθ
  refine ⟨thetaClosedCurrent θ u hu, fun e η hη =>
    thetaPotentialCurrent_full_positive θ.val u hu e η hη, ?_⟩
  exact bottChernClass_thetaClosedCurrent θ u hu

/-- Natural pseudoeffectivity internally produces an original positive closed
current with its entire AC measure exactly equal to the original volume
calibration. All near-supremum currents and weak limits are constructed. -/
theorem exists_original_current_ac_eq_volume
    (ω : KahlerBackground (m+1) X) (α : RealBottChern (m+1) X)
    (hα : ClassPseudoeffectiveViaPotentials α) :
    ∃ (S : ClosedOneOneCurrent (M := X) (canonicalBasis (m+1)) (Nat.succ_pos m))
      (hS : IsFullPositive S.val),
      bottChernClass (canonicalBasis (m+1)) (Nat.succ_pos m) S = α ∧
      globalACtopMeasure S.val hS =
        ENNReal.ofReal ((originalCurrentACVolume α).toReal /
          (kahlerVolume ω).real univ) • kahlerVolume ω := by
  classical
  obtain ⟨T₀, hT₀, hT₀class⟩ := exists_original_current_of_class_pseudoeffective α hα
  have hvfinite := originalCurrentACVolume_lt_top ω α
  by_cases hvzero : originalCurrentACVolume α = 0
  · have hmzero : globalACtopMeasure T₀.val hT₀ univ = 0 := le_antisymm
      ((ac_top_mass_le_volume T₀ hT₀ hT₀class).trans_eq hvzero) bot_le
    have hz := Measure.measure_univ_eq_zero.mp hmzero
    refine ⟨T₀, hT₀, hT₀class, ?_⟩
    simp only [hz, hvzero, ENNReal.toReal_zero, zero_div, ENNReal.ofReal_zero, zero_smul]
  let v : ℝ := (originalCurrentACVolume α).toReal
  let V : ℝ := (kahlerVolume ω).real univ
  have hv : 0 < v := ENNReal.toReal_pos_iff.mpr ⟨pos_iff_ne_zero.mpr hvzero, hvfinite⟩
  have hV : 0 < V := NefCoreKahlerCurrent.kahlerVolume_real_univ_pos ω
  let ε : ℕ → ℝ := fun j => 1 / (j+1 : ℝ)
  have hε (j : ℕ) : 0 < ε j := by dsimp [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε, one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  let r (j : ℕ) : ℝ := max (v - ε j) 0
  have hr (j : ℕ) : 0 ≤ r j := le_max_right _ _
  have hrlt (j : ℕ) : ENNReal.ofReal (r j) < originalCurrentACVolume α := by
    rw [← ENNReal.ofReal_toReal hvfinite.ne]
    exact (ENNReal.ofReal_lt_ofReal_iff hv).mpr (max_lt (sub_lt_self _ (hε j)) hv)
  have hrlim : Tendsto r atTop (𝓝 v) := by
    simpa only [r, sub_zero, max_eq_left hv.le] using
      ((tendsto_const_nhds (x := v)).sub hεlim).max
        (tendsto_const_nhds (x := (0 : ℝ)))
  choose T hT hclass hgt using fun j => exists_current_mass_gt α (hrlt j)
  have hreal (j : ℕ) : r j ≤ (globalACtopMeasure (T j).val (hT j)).real univ := by
    have hfin : globalACtopMeasure (T j).val (hT j) univ ≠ ⊤ :=
      ((ac_top_mass_le_volume (T j) (hT j) (hclass j)).trans_lt hvfinite).ne
    have h := ENNReal.toReal_mono hfin (hgt j).le
    simpa only [ENNReal.toReal_ofReal (hr j), Measure.real] using h
  choose K hK hKclass hKcal using fun j =>
    (OriginalCurrentMassCalibration.exists_same_class_original_current_ac_lower_bound
      ω (T j) (hT j)).2
  have hclasses (j : ℕ) : bottChernClass (canonicalBasis (m+1)) (Nat.succ_pos m) (K j) = α :=
    (hKclass j).trans (hclass j)
  let U : Ultrafilter ℕ := Ultrafilter.of atTop
  have hU : (U : Filter ℕ) ≤ atTop := Ultrafilter.of_le atTop
  obtain ⟨S, hS, hSclass, hweak⟩ :=
    FixedBottChernClassCurrentCompactness.exists_tendsto_same_class_originalClosedPositiveCurrent
      U α K hK hclasses
  have hu0 := (LocalPotentials.isThetaPshPotential_zero_iff ω.form).mpr ω.isSemipositive
  let R := thetaPotentialCurrent ω.form.val (fun _ => 0) hu0
  have hR : IsFullPositive R := fun e η hη =>
    thetaPotentialCurrent_full_positive ω.form.val (fun _ => 0) hu0 e η hη
  have href : globalACtopMeasure R hR = kahlerVolume ω :=
    OriginalCurrentAnalyticACMajorization.globalACtopMeasure_theta_analytic_eq
      ω.form hu0 zero_has_analytic_type
  let c (j : ℕ) : ℝ := r j / V
  let a : ℝ := v / V
  have hc (j : ℕ) : 0 ≤ c j := div_nonneg (hr j) hV.le
  have hclim : Tendsto c atTop (𝓝 a) := hrlim.div_const V
  have hcal (j : ℕ) :
      ENNReal.ofReal (c j) • globalACtopMeasure R hR ≤ globalACtopMeasure (K j).val (hK j) := by
    rw [href]
    apply le_trans ?_ (hKcal j)
    apply Measure.le_iff'.mpr
    intro A
    simp only [Measure.smul_apply, smul_eq_mul]
    have hratio : c j ≤ (globalACtopMeasure (T j).val (hT j)).real univ / V :=
      (div_le_div_iff_of_pos_right hV).mpr (hreal j)
    simpa only [mul_comm] using mul_le_mul_right
      (ENNReal.ofReal_le_ofReal hratio) (kahlerVolume ω A)
  have hconv (e : ComplexChart (m+1) X) γ φ :
      Tendsto (fun j => chartSpanCurrent (K j).val e γ φ) (U : Filter ℕ)
        (𝓝 (chartSpanCurrent S.val e γ φ)) := hweak e _
  have hlimit := GlobalACLowerCalibration.measure_le_of_lower_calibrated_filter
    (fun j => (K j).val) S.val R hK hS hR hconv hc (hclim.mono_left hU) hcal
  rw [href] at hlimit
  let L : Measure X := ENNReal.ofReal a • kahlerVolume ω
  have hLmass : L univ = originalCurrentACVolume α := by
    dsimp only [L]
    rw [Measure.smul_apply, smul_eq_mul,
      ← ENNReal.ofReal_toReal (measure_ne_top (kahlerVolume ω) univ),
      ← ENNReal.ofReal_mul (div_nonneg hv.le hV.le)]
    change ENNReal.ofReal ((v / V) * V) = originalCurrentACVolume α
    rw [div_mul_cancel₀ _ hV.ne', ENNReal.ofReal_toReal hvfinite.ne]
  have hSupper := ac_top_mass_le_volume S hS hSclass
  have hSlower : originalCurrentACVolume α ≤ globalACtopMeasure S.val hS univ := by
    rw [← hLmass]
    exact Measure.le_iff'.mp hlimit univ
  have hSmass := le_antisymm hSupper hSlower
  let : IsFiniteMeasure L := ⟨hLmass.trans_lt hvfinite⟩
  have heq : L = globalACtopMeasure S.val hS :=
    Measure.eq_of_le_of_measure_univ_eq hlimit (hLmass.trans hSmass.symm)
  exact ⟨S, hS, hSclass, heq.symm⟩

end SGPT.Foundations.Analysis.Pending.PseudoeffectiveOriginalCurrentCalabiYau
