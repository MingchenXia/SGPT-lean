import SGPT.Okounkov.TranscendentalVolumeConcavityACVolume
import SGPT.Foundations.Analysis.Pending.PseudoeffectiveOriginalCurrentCalabiYau
import SGPT.Foundations.Analysis.Pending.PositiveCurrentACTopMonotonicity
import SGPT.Foundations.Analysis.Pending.GlobalACLowerCalibration
import SGPT.Foundations.Analysis.Pending.ActualMixedMassPositiveScaling
import SGPT.Foundations.Analysis.Pending.RestrictedApproximantComparison

/-!
# The Minkowski inequality for the volume and the concavity of `vol^{1/n}`

Source: blueprint node `tok:ext-volume-concave` (Boucksom, *On the volume of a line bundle*,
published Proposition 4.5: `α ↦ v(α)^{1/n}` is homogeneous and concave on the
pseudo-effective cone).

Boucksom's proof: by his Theorem 4.6 (TN `exists_original_current_ac_eq_volume`) a
pseudo-effective class `α` contains a closed positive current `T_α` with
`(T_α)_ac^n = (v(α)/V) ω^n` almost everywhere (`V = ∫_X ω^n`). The absolutely continuous part of
`T_α + T_β` is `(T_α)_ac + (T_β)_ac` (TN `ae_acForm_add`), so Minkowski's determinant inequality
`det(A + B)^{1/n} ≥ det(A)^{1/n} + det(B)^{1/n}` gives
`((T_α + T_β)_ac)^n ≥ ((v(α)/V)^{1/n} + (v(β)/V)^{1/n})^n ω^n` a.e., whence
`v(α + β)^{1/n} ≥ v(α)^{1/n} + v(β)^{1/n}`. With `v(cα) = c^n v(α)` this is the concavity of
`v^{1/n}`. By `sourceClassVolume_eq_originalCurrentACVolume` everything holds for the volume
`vol` of `def:volcohclass`.

## Main results

* `volumeRoot_add_le`: `vol(α)^{1/n} + vol(β)^{1/n} ≤ vol(α + β)^{1/n}` for pseudo-effective
  `α`, `β`;
* `sourceClassVolume_smul`: `vol(cα) = c^n vol(α)` for `c > 0`;
* `concaveOn_volumeRoot_psef`, `volumeRootConcave` (`VolumeRootConcaveStatement`): concavity of
  `vol^{1/n}` on the pseudo-effective cone and on the big cone; `convex_bigCone`.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalVolumeConcavity

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal Topology Distributions ComplexOrder
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.GlobalAnalyticSingularities
open SGPT.Foundations.Analysis.FirstPass.NumericalRestrictedVolumeScaffold
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DiagonalMass SGPT.Foundations.Analysis.Pending.GlobalNonPluripolar
open SGPT.Foundations.Analysis.Pending.MixedMass
open SGPT.Foundations.Analysis.Pending.CurrentBottChernClass
open SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame
open SGPT.Foundations.Analysis.Pending.GlobalCurrentPotentials
open SGPT.Foundations.Analysis.Pending.ThetaPotentialCurrentBottChernClass
open SGPT.Foundations.Analysis.Pending.NaturalThetaPshGeometricCurrent
open SGPT.Foundations.Analysis.Pending.GlobalPositiveCurrentACRestriction
open SGPT.Foundations.Analysis.Pending.GlobalPositiveCurrentACTopMeasure
open SGPT.Foundations.Analysis.Pending.ActualAnalyticCurrentLocalDensity
open SGPT.Foundations.Analysis.Pending.LocalCurrentDeterminant
open SGPT.Foundations.Analysis.Pending.LocalCurrentDensityMatrix
open SGPT.Foundations.Analysis.Pending.PositiveCurrentACTopMeasure
open SGPT.Foundations.Analysis.Pending.TopDegreeDensity
open SGPT.Foundations.Analysis.Pending.LocalProductCurrents
open SGPT.Foundations.Analysis.Pending.IntegrationCurrent
open SGPT.Foundations.Analysis.Pending.OriginalCurrentACVolume
open _root_.SGPT.Foundations.Analysis.LocalCurrents
open SGPT.PSH.VariableComplexAtlas

/-! ### A scalar inequality -/

/-- If `cα w ≤ a`, `cβ w ≤ b` and `a^{1/n} + b^{1/n} ≤ s^{1/n}` (all quantities nonnegative),
then `(cα^{1/n} + cβ^{1/n})^n w ≤ s`. -/
theorem minkowski_scalar {N : ℕ} (hN : 0 < N) {a b s w cα cβ : ℝ} (_ha : 0 ≤ a) (_hb : 0 ≤ b)
    (hs : 0 ≤ s) (hw : 0 ≤ w) (hcα : 0 ≤ cα) (hcβ : 0 ≤ cβ) (hα : cα * w ≤ a) (hβ : cβ * w ≤ b)
    (hmin : a ^ ((N : ℝ)⁻¹) + b ^ ((N : ℝ)⁻¹) ≤ s ^ ((N : ℝ)⁻¹)) :
    (cα ^ ((N : ℝ)⁻¹) + cβ ^ ((N : ℝ)⁻¹)) ^ N * w ≤ s := by
  set r : ℝ := (N : ℝ)⁻¹ with hr
  have hr0 : 0 ≤ r := inv_nonneg.mpr (Nat.cast_nonneg N)
  have hrN : r * N = 1 := inv_mul_cancel₀ (by exact_mod_cast hN.ne')
  have h1 : cα ^ r * w ^ r ≤ a ^ r := by
    rw [← Real.mul_rpow hcα hw]
    exact Real.rpow_le_rpow (mul_nonneg hcα hw) hα hr0
  have h2 : cβ ^ r * w ^ r ≤ b ^ r := by
    rw [← Real.mul_rpow hcβ hw]
    exact Real.rpow_le_rpow (mul_nonneg hcβ hw) hβ hr0
  have hsum : (cα ^ r + cβ ^ r) * w ^ r ≤ s ^ r := by
    rw [add_mul]
    exact (add_le_add h1 h2).trans hmin
  have hpow := pow_le_pow_left₀ (mul_nonneg (add_nonneg (Real.rpow_nonneg hcα r)
    (Real.rpow_nonneg hcβ r)) (Real.rpow_nonneg hw r)) hsum N
  have hwr : (w ^ r) ^ N = w := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hw, hrN, Real.rpow_one]
  have hsr : (s ^ r) ^ N = s := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs, hrN, Real.rpow_one]
  rw [mul_pow, hwr, hsr] at hpow
  exact hpow

variable {m : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X] [CompactSpace X] [ConnectedSpace X]
  [MeasurableSpace X] [BorelSpace X]

/-! ### The pointwise Minkowski step -/

private theorem topDensity_eq_det' {U : Opens (ComplexModel (m + 1))}
    {S : LocalProductCurrent (m + 1) U m} (hS : IsPositive S) (x : ComplexModel (m + 1)) :
    actualTopPowerDensity (acForm hS x) =
      ((m + 1).factorial : ℝ) / Real.pi ^ (m + 1) * (acMatrix hS x).det.re := by
  rw [actualTopPowerDensity_eq_normalizedTopPowerDensity _ (isOneOne_acForm hS x),
    normalizedTopPowerDensity, complexTopCoefficient_eq]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rfl

/-- **The local Minkowski step**: if the top densities of the absolutely continuous parts of
two positive currents `S`, `T` dominate `cα` and `cβ` times that of `R`, then the top density of
`(S + T)_ac` dominates `(cα^{1/n} + cβ^{1/n})^n` times that of `R`, almost everywhere. -/
theorem ae_minkowski_acDensity {U : Opens (ComplexModel (m + 1))}
    {R S T : LocalProductCurrent (m + 1) U m} (hR : IsPositive R) (hS : IsPositive S)
    (hT : IsPositive T) {cα cβ : ℝ} (hcα : 0 ≤ cα) (hcβ : 0 ≤ cβ)
    (hSR : ∀ᵐ x ∂volume.restrict U,
      cα * actualTopPowerDensity (acForm hR x) ≤ actualTopPowerDensity (acForm hS x))
    (hTR : ∀ᵐ x ∂volume.restrict U,
      cβ * actualTopPowerDensity (acForm hR x) ≤ actualTopPowerDensity (acForm hT x)) :
    ∀ᵐ x ∂volume.restrict U,
      (cα ^ (((m + 1 : ℕ) : ℝ)⁻¹) + cβ ^ (((m + 1 : ℕ) : ℝ)⁻¹)) ^ (m + 1) *
          actualTopPowerDensity (acForm hR x) ≤
        actualTopPowerDensity (acForm (hS.add hT) x) := by
  filter_upwards [hSR, hTR,
    (ae_restrict_iff' U.isOpen.measurableSet).mpr
      (PositiveCurrentACTopMonotonicity.ae_acForm_add hS hT),
    ae_restrict_of_ae (ae_posSemidef_acMatrix hR), ae_restrict_of_ae (ae_posSemidef_acMatrix hS),
    ae_restrict_of_ae (ae_posSemidef_acMatrix hT)]
    with x hxS hxT hadd hpR hpS hpT
  have heq : acMatrix (hS.add hT) x = acMatrix hS x + acMatrix hT x := by
    change normalizedHermitianMatrix _ = _
    rw [hadd, normalizedHermitianMatrix_add]
    rfl
  set K : ℝ := ((m + 1).factorial : ℝ) / Real.pi ^ (m + 1) with hK
  have hKpos : 0 < K := by positivity
  rw [topDensity_eq_det', topDensity_eq_det'] at hxS hxT
  rw [topDensity_eq_det', topDensity_eq_det', heq]
  have hwR := MinkowskiDeterminant.re_det_nonneg hpR
  have hwS := MinkowskiDeterminant.re_det_nonneg hpS
  have hwT := MinkowskiDeterminant.re_det_nonneg hpT
  have hwST := MinkowskiDeterminant.re_det_nonneg (hpS.add hpT)
  have hS' : cα * (acMatrix hR x).det.re ≤ (acMatrix hS x).det.re := by
    have h := hxS
    rw [mul_left_comm] at h
    exact le_of_mul_le_mul_left h hKpos
  have hT' : cβ * (acMatrix hR x).det.re ≤ (acMatrix hT x).det.re := by
    have h := hxT
    rw [mul_left_comm] at h
    exact le_of_mul_le_mul_left h hKpos
  have hmin := MinkowskiDeterminant.rpow_inv_card_re_det_add_le hpS hpT
  simp only [Fintype.card_fin] at hmin
  have hkey := minkowski_scalar (Nat.succ_pos m) hwS hwT hwST hwR hcα hcβ hS' hT' hmin
  calc (cα ^ (((m + 1 : ℕ) : ℝ)⁻¹) + cβ ^ (((m + 1 : ℕ) : ℝ)⁻¹)) ^ (m + 1) *
        (K * (acMatrix hR x).det.re)
      = K * ((cα ^ (((m + 1 : ℕ) : ℝ)⁻¹) + cβ ^ (((m + 1 : ℕ) : ℝ)⁻¹)) ^ (m + 1) *
          (acMatrix hR x).det.re) := by ring
    _ ≤ K * (acMatrix hS x + acMatrix hT x).det.re :=
        mul_le_mul_of_nonneg_left hkey hKpos.le

/-! ### The global Minkowski inequality -/

omit [IsComplexManifold (m + 1) X] [CompactSpace X] [ConnectedSpace X] [MeasurableSpace X]
  [BorelSpace X] in
private theorem zero_has_analytic_type' :
    HasManifoldAnalyticSingularitiesSmoothOffPole (n := m + 1) (fun _ : X => 0) := by
  intro e z _
  let one : Fin 1 → ComplexModel (m + 1) → ℂ := fun _ _ => 1
  have hlog (y : ComplexModel (m + 1)) : generatorLog one y = 0 := by
    rw [generatorLog_eq_log_sum]
    simp [one]
  refine ⟨1, 1, one, one_pos, ⟨univ, isOpen_univ, mem_univ _,
    fun _ => differentiableOn_const 1⟩, fun _ => 0,
    boundedRealGermAt_of_continuousAt continuousAt_const,
    Eventually.of_forall fun _ _ => contDiffAt_const,
    Eventually.of_forall fun y => ?_⟩
  simp only [chartFunction, hlog, mul_zero, EReal.coe_zero, add_zero]

/-- **Minkowski's inequality for Boucksom's volume** (Boucksom, published Proposition 4.5):
`v(α)^{1/n} + v(β)^{1/n} ≤ v(α + β)^{1/n}` for pseudo-effective `α`, `β`. -/
theorem originalCurrentACVolume_root_add_le (ω : KahlerBackground (m + 1) X)
    {α β : RealBottChern (m + 1) X} (hα : ClassPseudoeffectiveViaPotentials α)
    (hβ : ClassPseudoeffectiveViaPotentials β) :
    (originalCurrentACVolume α).toReal ^ (((m + 1 : ℕ) : ℝ)⁻¹) +
        (originalCurrentACVolume β).toReal ^ (((m + 1 : ℕ) : ℝ)⁻¹) ≤
      (originalCurrentACVolume (α + β)).toReal ^ (((m + 1 : ℕ) : ℝ)⁻¹) := by
  classical
  set r : ℝ := ((m + 1 : ℕ) : ℝ)⁻¹ with hr
  set V : ℝ := (kahlerVolume ω).real univ with hV
  have hVpos : 0 < V := NefCoreKahlerCurrent.kahlerVolume_real_univ_pos ω
  set a : ℝ := (originalCurrentACVolume α).toReal with ha
  set b : ℝ := (originalCurrentACVolume β).toReal with hb
  have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
  have hb0 : 0 ≤ b := ENNReal.toReal_nonneg
  obtain ⟨Sα, hSα, hSαclass, hSαcal⟩ :=
    PseudoeffectiveOriginalCurrentCalabiYau.exists_original_current_ac_eq_volume ω α hα
  obtain ⟨Sβ, hSβ, hSβclass, hSβcal⟩ :=
    PseudoeffectiveOriginalCurrentCalabiYau.exists_original_current_ac_eq_volume ω β hβ
  have hu0 := (LocalPotentials.isThetaPshPotential_zero_iff ω.form).mpr ω.isSemipositive
  let R := thetaPotentialCurrent ω.form.val (fun _ => 0) hu0
  have hR : IsFullPositive R := fun e η hη =>
    thetaPotentialCurrent_full_positive ω.form.val (fun _ => 0) hu0 e η hη
  have href : globalACtopMeasure R hR = kahlerVolume ω :=
    OriginalCurrentAnalyticACMajorization.globalACtopMeasure_theta_analytic_eq
      ω.form hu0 zero_has_analytic_type'
  set cα : ℝ := a / V with hcα
  set cβ : ℝ := b / V with hcβ
  have hcα0 : 0 ≤ cα := div_nonneg ha0 hVpos.le
  have hcβ0 : 0 ≤ cβ := div_nonneg hb0 hVpos.le
  have hcalα : ENNReal.ofReal cα • globalACtopMeasure R hR ≤ globalACtopMeasure Sα.val hSα := by
    rw [href, hSαcal]
  have hcalβ : ENNReal.ofReal cβ • globalACtopMeasure R hR ≤ globalACtopMeasure Sβ.val hSβ := by
    rw [href, hSβcal]
  let hsum : IsFullPositive (Sα + Sβ).val := isFullPositive_add hSα hSβ
  set c : ℝ := (cα ^ r + cβ ^ r) ^ (m + 1) with hc
  have hc0 : 0 ≤ c := pow_nonneg (add_nonneg (Real.rpow_nonneg hcα0 r)
    (Real.rpow_nonneg hcβ0 r)) _
  have hdens (e : ComplexChart (m + 1) X) : ∀ᵐ x ∂volume.restrict (chartTarget e),
      c * actualTopPowerDensity (acForm (isPositive_chartSpanCurrent R hR e) x) ≤
        actualTopPowerDensity (acForm (isPositive_chartSpanCurrent (Sα + Sβ).val hsum e) x) :=
    ae_minkowski_acDensity (isPositive_chartSpanCurrent R hR e)
      (isPositive_chartSpanCurrent Sα.val hSα e) (isPositive_chartSpanCurrent Sβ.val hSβ e)
      hcα0 hcβ0
      (GlobalACLowerCalibration.ae_chart_density_le_of_measure_le R Sα.val hR hSα hcα0 hcalα e)
      (GlobalACLowerCalibration.ae_chart_density_le_of_measure_le R Sβ.val hR hSβ hcβ0 hcalβ e)
  have hmeas : ENNReal.ofReal c • globalACtopMeasure R hR ≤
      globalACtopMeasure (Sα + Sβ).val hsum :=
    LowerCalibratedCurrentACLimit.globalACtopMeasure_le_of_lower_calibrated_filter
      (l := (⊤ : Filter Unit)) (fun _ => (Sα + Sβ).val) (Sα + Sβ).val R (fun _ => hsum) hsum hR
      (fun _ _ _ => tendsto_const_nhds) (c := fun _ => c) (fun _ => hc0) tendsto_const_nhds
      (fun _ e => hdens e)
  have hclass : bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) (Sα + Sβ) = α + β := by
    rw [bottChernClass_add, hSαclass, hSβclass]
  have hle : ENNReal.ofReal c * kahlerVolume ω univ ≤ originalCurrentACVolume (α + β) := by
    have h1 := Measure.le_iff'.mp hmeas univ
    rw [href, Measure.smul_apply, smul_eq_mul] at h1
    exact h1.trans (ac_top_mass_le_volume (Sα + Sβ) hsum hclass)
  have hkV : kahlerVolume ω univ = ENNReal.ofReal V := by
    rw [hV, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [hkV, ← ENNReal.ofReal_mul hc0] at hle
  have hfin := originalCurrentACVolume_lt_top ω (α + β)
  have hreal : c * V ≤ (originalCurrentACVolume (α + β)).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hfin.ne).mp hle
  -- `c V = (a^{1/n} + b^{1/n})^n`
  have hrN : r * ((m + 1 : ℕ) : ℝ) = 1 := inv_mul_cancel₀ (by positivity)
  have hVr : (V ^ r) ^ (m + 1) = V := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hVpos.le, hrN, Real.rpow_one]
  have hVr0 : 0 < V ^ r := Real.rpow_pos_of_pos hVpos r
  have hcV : c * V = (a ^ r + b ^ r) ^ (m + 1) := by
    have hsplit : cα ^ r + cβ ^ r = (a ^ r + b ^ r) / V ^ r := by
      rw [hcα, hcβ, Real.div_rpow ha0 hVpos.le, Real.div_rpow hb0 hVpos.le, add_div]
    rw [hc, hsplit, div_pow, hVr, div_mul_cancel₀ _ hVpos.ne']
  rw [hcV] at hreal
  have hab0 : 0 ≤ a ^ r + b ^ r := add_nonneg (Real.rpow_nonneg ha0 r) (Real.rpow_nonneg hb0 r)
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hNr : ((m + 1 : ℕ) : ℝ) * r = 1 := by rw [hr]; exact mul_inv_cancel₀ (by positivity)
  have hroot := Real.rpow_le_rpow (pow_nonneg hab0 (m + 1)) hreal hr0
  rwa [← Real.rpow_natCast, ← Real.rpow_mul hab0, hNr, Real.rpow_one] at hroot

/-- **Minkowski's inequality for the volume**: `vol(α)^{1/n} + vol(β)^{1/n} ≤ vol(α + β)^{1/n}`
for pseudo-effective `α`, `β`. -/
theorem volumeRoot_add_le (ω : KahlerBackground (m + 1) X)
    {α β : RealBottChern (m + 1) X} (hα : ClassPseudoeffectiveViaPotentials α)
    (hβ : ClassPseudoeffectiveViaPotentials β) :
    volumeRoot α + volumeRoot β ≤ volumeRoot (α + β) := by
  unfold volumeRoot
  rw [sourceClassVolume_eq_originalCurrentACVolume ω, sourceClassVolume_eq_originalCurrentACVolume ω,
    sourceClassVolume_eq_originalCurrentACVolume ω]
  exact originalCurrentACVolume_root_add_le ω hα hβ

/-! ### Pseudo-effective classes -/

omit [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X] in
/-- The sum of pseudo-effective classes is pseudo-effective. -/
theorem classPseudoeffective_add {α β : RealBottChern (m + 1) X}
    (hα : ClassPseudoeffectiveViaPotentials α) (hβ : ClassPseudoeffectiveViaPotentials β) :
    ClassPseudoeffectiveViaPotentials (α + β) := by
  obtain ⟨S, hS, hSc⟩ :=
    (PseudoeffectiveOriginalCurrentEquivalence.classPseudoeffectiveViaPotentials_iff_exists_original_current
      α).mp hα
  obtain ⟨T, hT, hTc⟩ :=
    (PseudoeffectiveOriginalCurrentEquivalence.classPseudoeffectiveViaPotentials_iff_exists_original_current
      β).mp hβ
  refine (PseudoeffectiveOriginalCurrentEquivalence.classPseudoeffectiveViaPotentials_iff_exists_original_current
    _).mpr ⟨S + T, isFullPositive_add hS hT, ?_⟩
  rw [bottChernClass_add, hSc, hTc]

omit [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X] in
/-- A nonnegative multiple of a pseudo-effective class is pseudo-effective. -/
theorem classPseudoeffective_smul {α : RealBottChern (m + 1) X}
    (hα : ClassPseudoeffectiveViaPotentials α) {c : ℝ} (hc : 0 ≤ c) :
    ClassPseudoeffectiveViaPotentials (c • α) := by
  obtain ⟨S, hS, hSc⟩ :=
    (PseudoeffectiveOriginalCurrentEquivalence.classPseudoeffectiveViaPotentials_iff_exists_original_current
      α).mp hα
  refine (PseudoeffectiveOriginalCurrentEquivalence.classPseudoeffectiveViaPotentials_iff_exists_original_current
    _).mpr ⟨c • S, fun e ψ hψ => mul_nonneg hc (hS e ψ hψ), ?_⟩
  rw [← hSc]
  exact (bottChernClassLinearMap (canonicalBasis (m + 1)) (Nat.succ_pos m)).map_smul c S

/-- A big class is pseudo-effective. -/
theorem classPseudoeffective_of_isBigClass (ω : KahlerBackground (m + 1) X)
    {α : RealBottChern (m + 1) X} (hα : IsBigClass α) : ClassPseudoeffectiveViaPotentials α := by
  by_contra h
  have hpos := (sourceClassVolume_pos_iff_isBigClass ω α).mpr hα
  rw [sourceClassVolume_eq_zero_of_not_pseudoeffective h] at hpos
  exact lt_irrefl _ hpos

/-! ### Homogeneity -/

/-- `vol(cα) ≥ c^n vol(α)` for `c > 0`. -/
theorem sourceClassVolume_smul_ge (ω : KahlerBackground (m + 1) X)
    (α : RealBottChern (m + 1) X) {c : ℝ} (hc : 0 < c) :
    ENNReal.ofReal (c ^ (m + 1)) * sourceClassVolume α ≤ sourceClassVolume (c • α) := by
  by_cases hα : ClassPseudoeffectiveViaPotentials α
  swap
  · rw [sourceClassVolume_eq_zero_of_not_pseudoeffective hα, mul_zero]
    exact bot_le
  induction α using Quotient.inductionOn with
  | h θ =>
  change ClassPseudoeffectiveViaPotentials (RealBottChern.ofRepresentative θ) at hα
  change ENNReal.ofReal (c ^ (m + 1)) * sourceClassVolume (RealBottChern.ofRepresentative θ) ≤
    sourceClassVolume (c • RealBottChern.ofRepresentative θ)
  obtain ⟨u, hu⟩ := (classPseudoeffectiveViaPotentials_ofRepresentative θ).mp hα
  obtain ⟨hV, hvol⟩ := sourceClassVolume_ofRepresentative ω θ hu
  have hcV := RestrictedApproximantComparison.isThetaPshPotential_smul hV hc
  have hscale := ActualMixedMassPositiveScaling.globalMixedMass_positive_smul
    (θ := fun _ : Fin (m + 1) => θ) (u := fun _ => thetaPshSupremum θ.val)
    (fun _ => hV) (c := fun _ => c) (fun _ => hc)
  have hprod : (∏ _i : Fin (m + 1), c) = c ^ (m + 1) := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hprod] at hscale
  rw [hvol, ← RealBottChern.ofRepresentative_smul]
  calc ENNReal.ofReal (c ^ (m + 1)) * diagonalPotentialMass θ (thetaPshSupremum θ.val) hV
      = diagonalPotentialMass (c • θ) (fun x => (c : EReal) * thetaPshSupremum θ.val x) hcV :=
        hscale.symm
    _ ≤ sourceClassVolume (RealBottChern.ofRepresentative (c • θ)) :=
        diagonalPotentialMass_le_sourceClassVolume ω (c • θ) hcV

/-- **Homogeneity of the volume**: `vol(cα) = c^n vol(α)` for `c > 0`. -/
theorem sourceClassVolume_smul (ω : KahlerBackground (m + 1) X)
    (α : RealBottChern (m + 1) X) {c : ℝ} (hc : 0 < c) :
    sourceClassVolume (c • α) = ENNReal.ofReal (c ^ (m + 1)) * sourceClassVolume α := by
  apply le_antisymm _ (sourceClassVolume_smul_ge ω α hc)
  have h := sourceClassVolume_smul_ge ω (c • α) (inv_pos.mpr hc)
  rw [smul_smul, inv_mul_cancel₀ hc.ne', one_smul] at h
  have hcn : 0 < c ^ (m + 1) := pow_pos hc _
  have hmul : ENNReal.ofReal (c ^ (m + 1)) *
      (ENNReal.ofReal (c⁻¹ ^ (m + 1)) * sourceClassVolume (c • α)) ≤
      ENNReal.ofReal (c ^ (m + 1)) * sourceClassVolume α := by
    gcongr
  rwa [← mul_assoc, ← ENNReal.ofReal_mul hcn.le, inv_pow, mul_inv_cancel₀ hcn.ne',
    ENNReal.ofReal_one, one_mul] at hmul

/-- `vol(cα)^{1/n} = c vol(α)^{1/n}` for `c > 0`. -/
theorem volumeRoot_smul (ω : KahlerBackground (m + 1) X) (α : RealBottChern (m + 1) X)
    {c : ℝ} (hc : 0 < c) : volumeRoot (c • α) = c * volumeRoot α := by
  unfold volumeRoot
  rw [sourceClassVolume_smul ω α hc, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_pos hc _).le,
    Real.mul_rpow (pow_pos hc _).le ENNReal.toReal_nonneg, ← Real.rpow_natCast,
    ← Real.rpow_mul hc.le, mul_inv_cancel₀ (by positivity), Real.rpow_one]

/-! ### Concavity -/

omit [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X] in
/-- The pseudo-effective cone is convex. -/
theorem convex_classPseudoeffective :
    Convex ℝ {α : RealBottChern (m + 1) X | ClassPseudoeffectiveViaPotentials α} := by
  intro x hx y hy a b ha hb _
  exact classPseudoeffective_add (classPseudoeffective_smul hx ha) (classPseudoeffective_smul hy hb)

/-- **`vol^{1/n}` is concave on the pseudo-effective cone** (Boucksom, published
Proposition 4.5). -/
theorem concaveOn_volumeRoot_psef (ω : KahlerBackground (m + 1) X) :
    ConcaveOn ℝ {α : RealBottChern (m + 1) X | ClassPseudoeffectiveViaPotentials α}
      volumeRoot := by
  refine ⟨convex_classPseudoeffective, fun x hx y hy a b ha hb hab => ?_⟩
  rcases ha.eq_or_lt with rfl | ha'
  · rw [zero_add] at hab
    subst hab
    simp
  rcases hb.eq_or_lt with rfl | hb'
  · rw [add_zero] at hab
    subst hab
    simp
  have h := volumeRoot_add_le ω (classPseudoeffective_smul hx ha)
    (classPseudoeffective_smul hy hb)
  rw [volumeRoot_smul ω x ha', volumeRoot_smul ω y hb'] at h
  simpa only [smul_eq_mul] using h

/-- The big cone is convex. -/
theorem convex_bigCone (ω : KahlerBackground (m + 1) X) : Convex ℝ (bigCone (m := m) X) := by
  intro x hx y hy a b ha hb hab
  change SGPT.PSH.BookCurrent.IsBig x at hx
  change SGPT.PSH.BookCurrent.IsBig y at hy
  change SGPT.PSH.BookCurrent.IsBig (a • x + b • y)
  have hxb := (SGPT.PSH.BookCurrent.isBig_iff_isBigClass x).mp hx
  have hyb := (SGPT.PSH.BookCurrent.isBig_iff_isBigClass y).mp hy
  have hxp := classPseudoeffective_of_isBigClass ω hxb
  have hyp := classPseudoeffective_of_isBigClass ω hyb
  have hx0 : 0 < volumeRoot x := by
    unfold volumeRoot
    exact Real.rpow_pos_of_pos (ENNReal.toReal_pos ((sourceClassVolume_pos_iff_isBigClass ω x).mpr
      hxb).ne' (sourceClassVolume_lt_top ω x).ne) _
  have hy0 : 0 < volumeRoot y := by
    unfold volumeRoot
    exact Real.rpow_pos_of_pos (ENNReal.toReal_pos ((sourceClassVolume_pos_iff_isBigClass ω y).mpr
      hyb).ne' (sourceClassVolume_lt_top ω y).ne) _
  have hconc := (concaveOn_volumeRoot_psef ω).2 hxp hyp ha hb hab
  have hpos : 0 < volumeRoot (a • x + b • y) := by
    refine lt_of_lt_of_le ?_ hconc
    rcases ha.eq_or_lt with rfl | ha'
    · rw [zero_add] at hab
      subst hab
      simpa using hy0
    · exact add_pos_of_pos_of_nonneg (mul_pos ha' hx0) (mul_nonneg hb hy0.le)
  rw [SGPT.PSH.BookCurrent.isBig_iff_isBigClass, ← sourceClassVolume_pos_iff_isBigClass ω]
  unfold volumeRoot at hpos
  by_contra h0
  rw [not_lt, nonpos_iff_eq_zero] at h0
  rw [h0, ENNReal.toReal_zero, Real.zero_rpow (by positivity)] at hpos
  exact lt_irrefl _ hpos

/-- **`tok:ext-volume-concave`, concavity**: `vol^{1/n}` is concave on the big cone. -/
theorem volumeRootConcave (ω : KahlerBackground (m + 1) X) :
    VolumeRootConcaveStatement (m := m) X := by
  refine ⟨convex_bigCone ω, fun x hx y hy a b ha hb hab => ?_⟩
  have hxp := classPseudoeffective_of_isBigClass ω
    ((SGPT.PSH.BookCurrent.isBig_iff_isBigClass x).mp hx)
  have hyp := classPseudoeffective_of_isBigClass ω
    ((SGPT.PSH.BookCurrent.isBig_iff_isBigClass y).mp hy)
  exact (concaveOn_volumeRoot_psef ω).2 hxp hyp ha hb hab

end SGPT.Okounkov.TranscendentalVolumeConcavity
