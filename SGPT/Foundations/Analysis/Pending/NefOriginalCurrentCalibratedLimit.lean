import SGPT.Foundations.Analysis.Pending.YauTheoremInterface
import SGPT.Foundations.Analysis.Pending.NefMixedMass
import SGPT.Foundations.Analysis.Pending.MovingBottChernClassCurrentCompactness
import SGPT.Foundations.Analysis.Pending.GlobalFilterCalibratedCurrentACLimit
import SGPT.Foundations.Analysis.Pending.ActualAnalyticRNDensityIdentification
import SGPT.Foundations.Analysis.Pending.XiaoPureSmoothTopology

set_option autoImplicit false

/-! Full mathematical BP statements and ENTIRE proofs precede this source.
Nefness internally produces the genuine Yau-calibrated family and its original
same-class weak limit. No family, limit, calibration or desired comparison input.
Connected positive-dimensional specialization, not arbitrary pseff CY or volume. -/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions
namespace SGPT.Foundations.Analysis.Pending.NefOriginalCurrentCalibratedLimit
open FirstPass FirstPass.PositiveClasses FirstPass.MongeAmpere
  FirstPass.NumericalRestrictedVolumeScaffold CanonicalCurrentFrame
  CurrentBottChernClass GlobalCurrentPotentials NaturalThetaPshGeometricCurrent
  NaturalThetaPshClosedCurrent GlobalPositiveCurrentACRestriction
  GlobalPositiveCurrentACTopMeasure ActualAnalyticCurrentLocalDensity
  LocalCurrentDeterminant LocalProductCurrents
  LelongPoincareDivisor ManifoldTubePositivity IntegrationCurrent NefMixedMass
  XiaoPureSmoothTopology XiaoPureSmoothBottChernClosure
  _root_.SGPT.Foundations.Analysis.LocalCurrents

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m+1)) M] [IsComplexManifold (m+1) M]

private theorem zero_current (σ : ClosedRealOneOneForm (m+1) M)
    (hu : IsThetaPshPotential σ.val (fun _ => 0)) :
    thetaPotentialCurrent σ.val (fun _ => 0) hu =
      (smoothClosedCurrent (canonicalBasis (m+1)) (Nat.succ_pos m) σ).val := by
  have hz : globalDDC (canonicalBasis (m+1)) (Nat.succ_pos m) (fun _ => 0)
      hu.quasiPshPotential = 0 := by
    apply globalCurrent_ext (canonicalBasis (m+1))
    intro e
    rw [globalDDC_coefficients, GlobalCurrent.coefficients_zero]
    have hreg : regularDistribution (canonicalBasis (m+1)).addHaar
        (fun z => (chartFunction (fun _ : M => (0 : EReal)) e z).toReal)
        (quasiPsh_chart_locallyIntegrable (canonicalBasis (m+1))
          (Nat.succ_pos m) (fun _ => 0) hu.quasiPshPotential e) = 0 := by
      ext φ
      simp [regularDistribution_apply,chartFunction]
    change ddC _ = 0
    rw [hreg]
    ext v : 1
    have hv : v = ![v 0,v 1] := by ext i; fin_cases i <;> rfl
    rw [hv,ddC_apply]
    simp
  rw [thetaPotentialCurrent,hz,add_zero]
  rfl

private theorem fullPositive_smooth
    (σ : ClosedRealOneOneForm (m+1) M) (hσ : σ.val.IsSemipositive) :
    IsFullPositive (smoothClosedCurrent (canonicalBasis (m+1)) (Nat.succ_pos m) σ).val := by
  have hu := (LocalPotentials.isThetaPshPotential_zero_iff σ).mpr hσ
  have hp := (thetaPotentialCurrent_closed_type_positive σ.val (fun _ => 0) hu).2.2
  rw [zero_current σ hu] at hp
  exact hp

private theorem acForm_congr {U : Opens (ComplexModel (m+1))}
    {T S : LocalProductCurrent (m+1) U m} (hT : IsPositive T) (hS : IsPositive S)
    (heq : T = S) : acForm hT = acForm hS := by
  subst S
  rfl

/-- The actual smooth original positive current has its SAME smooth canonical
RN coefficient form on every chart, for any full-positivity proof. -/
theorem ae_acForm_smoothClosedCurrent
    (σ : ClosedRealOneOneForm (m+1) M) (hσ : σ.val.IsSemipositive)
    (hT : IsFullPositive (smoothClosedCurrent (canonicalBasis (m+1)) (Nat.succ_pos m) σ).val)
    (e : ComplexChart (m+1) M) :
    ∀ᵐ x ∂volume.restrict (chartTarget e),
      acForm (isPositive_chartSpanCurrent
        (smoothClosedCurrent (canonicalBasis (m+1)) (Nat.succ_pos m) σ).val hT e) x =
        σ.val.coeff e x := by
  have hu := (LocalPotentials.isThetaPshPotential_zero_iff σ).mpr hσ
  have han : HasManifoldAnalyticSingularitiesSmoothOffPole (n := m+1)
      (fun _ : M => 0) := by
    intro f z _
    let one : Fin 1 → ComplexModel (m+1) → ℂ := fun _ _ => 1
    have hlog (y : ComplexModel (m+1)) : generatorLog one y = 0 := by
      rw [generatorLog_eq_log_sum]
      simp [one]
    refine ⟨1,1,one,one_pos,⟨univ,isOpen_univ,mem_univ _,
      fun _ => differentiableOn_const 1⟩,fun _ => 0,
      boundedRealGermAt_of_continuousAt continuousAt_const,
      Eventually.of_forall fun _ _ => contDiffAt_const,
      Eventually.of_forall fun y => ?_⟩
    simp only [chartFunction,hlog,mul_zero,EReal.coe_zero,add_zero]
  have heq := zero_current σ hu
  have hae := ActualAnalyticRNDensityIdentification.ae_acForm_eq_original_reader
    σ (fun _ => 0) hu han e
  have hac := acForm_congr
    (ActualAnalyticCurrentLocalDensity.isPositive_chartSpanCurrent σ.val (fun _ => 0) hu e)
    (GlobalPositiveCurrentACRestriction.isPositive_chartSpanCurrent
      (smoothClosedCurrent (canonicalBasis (m+1)) (Nat.succ_pos m) σ).val hT e)
    (congrArg (fun T => chartSpanCurrent T e) heq)
  apply (ae_restrict_iff' e.val.open_target.measurableSet).mpr
  filter_upwards [hae] with x hx hxe
  rw [← hac]
  simpa only [chartFunction,EReal.toReal_zero,smoothDDC_zero,add_zero] using hx hxe

variable [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

private theorem exists_kahler_calibration [ConnectedSpace M]
    (ω : KahlerBackground (m+1) M) (θ : ClosedRealOneOneForm (m+1) M)
    (hnef : NefWithRespectTo ω θ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (A : KahlerBackground (m+1) M),
      RealBottChern.ofRepresentative A.form =
        RealBottChern.ofRepresentative (θ + ε • ω.form) ∧
      0 < slotIntegral ω (fun _ => θ + ε • ω.form) / (kahlerVolume ω).real univ ∧
      ∀ (e : ComplexChart (m+1) M) z, z ∈ e.val.target →
        actualTopPowerDensity (A.form.val.coeff e z) =
          (slotIntegral ω (fun _ => θ + ε • ω.form) / (kahlerVolume ω).real univ) *
            actualTopPowerDensity (ω.form.val.coeff e z) := by
  obtain ⟨h,hh,hpos⟩ := hnef (ε/2) (half_pos hε)
  let σ : ClosedRealOneOneForm (m+1) M := θ + ddcClosedForm h hh + (ε/2) • ω.form
  have hσ : σ.val.IsSemipositive := fun e z hz v => by
    simpa [σ,ddcClosedForm_coeff] using hpos e z hz v
  have hBeq : σ + (ε/2) • ω.form = θ + ε • ω.form + ddcClosedForm h hh := by
    apply ClosedRealOneOneForm.ext
    intro e z
    simp only [σ,ClosedRealOneOneForm.coeff_add,ClosedRealOneOneForm.coeff_smul]
    module
  have hB : (θ + ε • ω.form + ddcClosedForm h hh).val.IsKahler := by
    rw [← hBeq]
    exact NefCoreKahlerCurrent.isKahler_add_smul_of_isSemipositive ω hσ (half_pos hε)
  let B : KahlerBackground (m+1) M := ⟨_,hB⟩
  obtain ⟨φ,hφ,hA,hcal⟩ := YauTheorem.exists_kahler_mongeAmpere_eq_smul
    (Nat.succ_pos m) B ω
  let A : KahlerBackground (m+1) M := ⟨B.form + ddcClosedForm φ hφ,hA⟩
  have hclassB : ClosedRealOneOneForm.BottChernRel (θ + ε • ω.form) B.form := by
    refine ⟨h,hh,?_⟩
    intro e z _
    simp only [B,ClosedRealOneOneForm.coeff_add,ddcClosedForm_coeff]
  have hclassA : ClosedRealOneOneForm.BottChernRel B.form A.form := by
    refine ⟨φ,hφ,?_⟩
    intro e z _
    simp only [A,ClosedRealOneOneForm.coeff_add,ddcClosedForm_coeff]
  have hvol : (kahlerVolume B).real univ = slotIntegral ω (fun _ => θ + ε • ω.form) := by
    rw [← YauTheorem.integral_topRatio_formPow_eq ω B,
      integral_formPow_eq_slotIntegral]
    exact slotIntegral_add_ddc ω (fun _ => θ + ε • ω.form) (fun _ => h) (fun _ => hh)
  refine ⟨A,((RealBottChern.ofRepresentative_eq_iff _ _).mpr
    (hclassB.trans hclassA)).symm,?_,?_⟩
  · rw [← hvol]
    exact YauTheorem.kahlerVolume_div_pos (Nat.succ_pos m) B ω
  intro e z hz
  simpa only [A,hvol] using hcal e z hz

/-- Nefness internally constructs genuine Yau solutions, their SAME-class
original weak limit, and a complete canonical global AC measure lower bound. -/
theorem exists_nef_original_current_ac_lower_bound [ConnectedSpace M]
    (ω : KahlerBackground (m+1) M) (θ : ClosedRealOneOneForm (m+1) M)
    (hnef : NefWithRespectTo ω θ) :
    0 ≤ slotIntegral ω (fun _ => θ) / (kahlerVolume ω).real univ ∧
    ∃ (S : ClosedOneOneCurrent (M := M) (canonicalBasis (m+1)) (Nat.succ_pos m))
      (hS : IsFullPositive S.val),
      bottChernClass (canonicalBasis (m+1)) (Nat.succ_pos m) S =
        RealBottChern.ofRepresentative θ ∧
      ENNReal.ofReal (slotIntegral ω (fun _ => θ) / (kahlerVolume ω).real univ) •
        globalACtopMeasure
          (smoothClosedCurrent (canonicalBasis (m+1)) (Nat.succ_pos m) ω.form).val
          (fullPositive_smooth ω.form ω.isSemipositive) ≤ globalACtopMeasure S.val hS := by
  classical
  let ε : ℕ → ℝ := fun j => 1 / (j+1 : ℝ)
  have hε (j : ℕ) : 0 < ε j := by dsimp [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε,one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  choose A hAclass hcpos hAcal using fun j => exists_kahler_calibration ω θ hnef (ε j) (hε j)
  let T (j : ℕ) := smoothClosedCurrent (canonicalBasis (m+1)) (Nat.succ_pos m) (A j).form
  have hT (j : ℕ) : IsFullPositive (T j).val := fullPositive_smooth _ (A j).isSemipositive
  let V : ℝ := (kahlerVolume ω).real univ
  let c (j : ℕ) : ℝ := slotIntegral ω (fun _ => θ + ε j • ω.form) / V
  let a : ℝ := slotIntegral ω (fun _ => θ) / V
  have hc (j : ℕ) : 0 ≤ c j := (hcpos j).le
  have hclim : Tendsto c atTop (𝓝 a) := by
    have hcont := (continuous_slotIntegral_add_smul ω (fun _ => θ) (fun _ => ω.form)).tendsto 0
    have hi := hcont.comp hεlim
    simpa only [c,a,V,Function.comp_apply,zero_smul,add_zero] using hi.div_const V
  have hclasses : Tendsto (fun j => bottChernClass (canonicalBasis (m+1))
      (Nat.succ_pos m) (T j)) atTop
      (@nhds (RealBottChern (m+1) M) classPureSmoothTopology
        (RealBottChern.ofRepresentative θ)) := by
    let : TopologicalSpace (ClosedRealOneOneForm (m+1) M) := formPureSmoothTopology
    let : TopologicalSpace (RealBottChern (m+1) M) := classPureSmoothTopology
    let : IsTopologicalAddGroup (ClosedRealOneOneForm (m+1) M) :=
      formPureSmoothTopology_isTopologicalAddGroup
    let : ContinuousSMul ℝ (ClosedRealOneOneForm (m+1) M) := formPureSmoothTopology_continuousSMul
    have hform : Tendsto (fun j => θ + ε j • ω.form) atTop (𝓝 θ) := by
      simpa only [zero_smul,add_zero] using tendsto_const_nhds.add (hεlim.smul_const ω.form)
    have hq := (isOpenQuotientMap_ofRepresentative ω).continuous.tendsto θ
    have h := hq.comp hform
    convert h using 1
    funext j
    rw [bottChernClass_smoothClosedCurrent]
    exact hAclass j
  let U : Ultrafilter ℕ := Ultrafilter.of atTop
  have hU : (U : Filter ℕ) ≤ atTop := Ultrafilter.of_le atTop
  obtain ⟨S,hS,hclass,hweak⟩ :=
    MovingBottChernClassCurrentCompactness.exists_tendsto_moving_class_originalClosedPositiveCurrent
      ω U hU (RealBottChern.ofRepresentative θ) T hT hclasses
  let R := (smoothClosedCurrent (canonicalBasis (m+1)) (Nat.succ_pos m) ω.form).val
  have hR : IsFullPositive R := fullPositive_smooth _ ω.isSemipositive
  have hcal (j : ℕ) (e : ComplexChart (m+1) M) :
      ∀ᵐ x ∂volume.restrict (chartTarget e),
        actualTopPowerDensity (acForm (isPositive_chartSpanCurrent (T j).val (hT j) e) x) =
          c j * actualTopPowerDensity (acForm (isPositive_chartSpanCurrent R hR e) x) := by
    filter_upwards [ae_acForm_smoothClosedCurrent (A j).form (A j).isSemipositive (hT j) e,
      ae_acForm_smoothClosedCurrent ω.form ω.isSemipositive hR e,
      ae_restrict_mem e.val.open_target.measurableSet] with x hx hxR hxe
    rw [hx,hxR]
    exact hAcal j e x hxe
  have hconv (e : ComplexChart (m+1) M) γ φ :
      Tendsto (fun j => chartSpanCurrent (T j).val e γ φ) (U : Filter ℕ)
        (𝓝 (chartSpanCurrent S.val e γ φ)) := hweak e _
  refine ⟨ge_of_tendsto hclim (Eventually.of_forall hc),S,hS,hclass,?_⟩
  exact GlobalFilterCalibratedCurrentACLimit.globalACtopMeasure_le_of_calibrated_filter
    (fun j => (T j).val) S.val R hT hS hR hconv hc (hclim.mono_left hU) hcal

end SGPT.Foundations.Analysis.Pending.NefOriginalCurrentCalibratedLimit
