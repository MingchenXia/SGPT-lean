import SGPT.Foundations.Analysis.Pending.PseudoeffectiveOriginalCurrentCalabiYau
import SGPT.Foundations.Analysis.Pending.MovingBottChernClassCurrentCompactness

set_option autoImplicit false

/-! # Upper semicontinuity of the actual original-current volume

Boucksom published Proposition 4.5, final assertion. Full statement and
ENTIRE proof precede implementation. Natural sequence pseudoeffectivity
and actual quotient convergence internally supply calibrated currents,
filter refinement, same-class weak limit and volume limsup inequality.
-/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal Distributions
universe u
namespace SGPT.Foundations.Analysis.Pending.OriginalCurrentVolumeUpperSemicontinuity
open FirstPass FirstPass.PositiveClasses FirstPass.MongeAmpere
  FirstPass.GlobalAnalyticSingularities FirstPass.NumericalRestrictedVolumeScaffold
  CurrentBottChernClass CanonicalCurrentFrame GlobalCurrentPotentials
  ThetaPotentialCurrentBottChernClass NaturalThetaPshGeometricCurrent
  GlobalPositiveCurrentACRestriction GlobalPositiveCurrentACTopMeasure
  ActualAnalyticCurrentLocalDensity IntegrationCurrent OriginalCurrentACVolume
  XiaoPureSmoothBottChernClosure

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

/-- Natural original pseudoeffective classes and their actual smooth quotient
convergence internally produce the extended volume limsup upper bound. -/
theorem limsup_originalCurrentACVolume_le
    (ω : KahlerBackground (m+1) X) (αj : ℕ → RealBottChern (m+1) X)
    (α : RealBottChern (m+1) X)
    (hαj : ∀ j, ClassPseudoeffectiveViaPotentials (αj j))
    (hlim : Tendsto αj atTop
      (@nhds (RealBottChern (m+1) X) classPureSmoothTopology α)) :
    limsup (fun j => originalCurrentACVolume (αj j)) atTop ≤
      originalCurrentACVolume α := by
  classical
  choose T hT hclass hcal using fun j =>
    PseudoeffectiveOriginalCurrentCalabiYau.exists_original_current_ac_eq_volume
      ω (αj j) (hαj j)
  let V : ℝ := (kahlerVolume ω).real univ
  have hV : 0 < V := NefCoreKahlerCurrent.kahlerVolume_real_univ_pos ω
  by_contra hle
  obtain ⟨r, hrα, hr⟩ := exists_between (lt_of_not_ge hle)
  have hfreq : ∃ᶠ j in atTop, r < originalCurrentACVolume (αj j) :=
    frequently_lt_of_lt_limsup (h := hr)
  obtain ⟨j₀, hj₀⟩ := hfreq.exists
  have hrfin : r < ⊤ := hj₀.trans (originalCurrentACVolume_lt_top ω (αj j₀))
  let B : Set ℕ := {j | r < originalCurrentACVolume (αj j)}
  let l : Filter ℕ := atTop ⊓ 𝓟 B
  have hl : l.NeBot := by
    apply inf_principal_neBot_iff.mpr
    intro A hA
    obtain ⟨j, hj, hjA⟩ := (hfreq.and_eventually hA).exists
    exact ⟨j, hjA, hj⟩
  let : l.NeBot := hl
  let U : Ultrafilter ℕ := Ultrafilter.of l
  have hUl : (U : Filter ℕ) ≤ l := Ultrafilter.of_le l
  have hU : (U : Filter ℕ) ≤ atTop := hUl.trans inf_le_left
  have hB : ∀ᶠ j in (U : Filter ℕ), j ∈ B :=
    le_principal_iff.mp (hUl.trans inf_le_right)
  have hclasses : Tendsto (fun j => bottChernClass (canonicalBasis (m+1))
      (Nat.succ_pos m) (T j)) atTop
      (@nhds (RealBottChern (m+1) X) classPureSmoothTopology α) := by
    simpa only [hclass] using hlim
  obtain ⟨S, hS, hSclass, hweak⟩ :=
    MovingBottChernClassCurrentCompactness.exists_tendsto_moving_class_originalClosedPositiveCurrent
      ω U hU α T hT hclasses
  have hu0 := (LocalPotentials.isThetaPshPotential_zero_iff ω.form).mpr ω.isSemipositive
  let R := thetaPotentialCurrent ω.form.val (fun _ => 0) hu0
  have hR : IsFullPositive R := fun e η hη =>
    thetaPotentialCurrent_full_positive ω.form.val (fun _ => 0) hu0 e η hη
  have href : globalACtopMeasure R hR = kahlerVolume ω :=
    OriginalCurrentAnalyticACMajorization.globalACtopMeasure_theta_analytic_eq
      ω.form hu0 zero_has_analytic_type
  let a : ℝ := r.toReal / V
  let c (j : ℕ) : ℝ := if j ∈ B then a else 0
  have ha : 0 ≤ a := div_nonneg ENNReal.toReal_nonneg hV.le
  have hc (j : ℕ) : 0 ≤ c j := by
    dsimp only [c]
    split_ifs <;> positivity
  have hclim : Tendsto c (U : Filter ℕ) (𝓝 a) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hB] with j hj
    simp only [c, if_pos hj]
  have hcal' (j : ℕ) : ENNReal.ofReal (c j) • globalACtopMeasure R hR ≤
      globalACtopMeasure (T j).val (hT j) := by
    rw [href, hcal j]
    dsimp only [c]
    split_ifs with hj
    · have hrreal : r.toReal ≤ (originalCurrentACVolume (αj j)).toReal :=
        ENNReal.toReal_mono (originalCurrentACVolume_lt_top ω (αj j)).ne hj.le
      have hratio : a ≤ (originalCurrentACVolume (αj j)).toReal / V :=
        (div_le_div_iff_of_pos_right hV).mpr hrreal
      apply Measure.le_iff'.mpr
      intro A
      simp only [Measure.smul_apply, smul_eq_mul]
      simpa only [mul_comm] using mul_le_mul_right
        (ENNReal.ofReal_le_ofReal hratio) (kahlerVolume ω A)
    · simp only [ENNReal.ofReal_zero, zero_smul]
      exact bot_le
  have hconv (e : ComplexChart (m+1) X) γ φ :
      Tendsto (fun j => chartSpanCurrent (T j).val e γ φ) (U : Filter ℕ)
        (𝓝 (chartSpanCurrent S.val e γ φ)) := hweak e _
  have hlimit := GlobalACLowerCalibration.measure_le_of_lower_calibrated_filter
    (fun j => (T j).val) S.val R hT hS hR hconv hc hclim hcal'
  rw [href] at hlimit
  have hmass : (ENNReal.ofReal a • kahlerVolume ω) univ = r := by
    rw [Measure.smul_apply, smul_eq_mul,
      ← ENNReal.ofReal_toReal (measure_ne_top (kahlerVolume ω) univ),
      ← ENNReal.ofReal_mul ha]
    change ENNReal.ofReal ((r.toReal / V) * V) = r
    rw [div_mul_cancel₀ _ hV.ne', ENNReal.ofReal_toReal hrfin.ne]
  have hrbound : r ≤ originalCurrentACVolume α := by
    calc
      r = (ENNReal.ofReal a • kahlerVolume ω) univ := hmass.symm
      _ ≤ globalACtopMeasure S.val hS univ := Measure.le_iff'.mp hlimit univ
      _ ≤ originalCurrentACVolume α := ac_top_mass_le_volume S hS hSclass
  exact not_le_of_gt hrα hrbound

end SGPT.Foundations.Analysis.Pending.OriginalCurrentVolumeUpperSemicontinuity
