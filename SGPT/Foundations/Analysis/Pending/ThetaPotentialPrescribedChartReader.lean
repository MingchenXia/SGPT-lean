import SGPT.Foundations.Analysis.Pending.NaturalThetaPshClosedCurrent
import SGPT.Foundations.Analysis.Pending.GlobalPositiveCurrentACRestriction
import SGPT.Foundations.Analysis.Pending.ThetaPshDecreasingLimit
import SGPT.Foundations.Analysis.Pending.ActualCanonicalComplementaryCurrentCalibration
import SGPT.Foundations.Analysis.Pending.ActualDistributionTwoFormDdc

set_option autoImplicit false

/-! The SAME original theta current in any natural smooth local background
potential, retaining unbounded poles and infinite AC mass. Entire BP before
Lean; no compactness, Kahler, analytic, finite or current identity input. -/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff
namespace SGPT.Foundations.Analysis.Pending.ThetaPotentialPrescribedChartReader
open FirstPass _root_.SGPT.Foundations.Analysis.LocalCurrents GlobalCurrents
  GlobalCurrentPotentials CanonicalCurrentFrame LelongPoincareDivisor
  NaturalThetaPshGeometricCurrent NaturalThetaPshClosedCurrent
  ActualDistributionTwoFormReading ActualDistributionTwoFormDdc
  ActualCanonicalComplementaryCurrentCalibration ActualAnalyticCurrentLocalDensity
  LocalProductCurrents LocalBedfordTaylorLocality LocalBedfordTaylorProducts
  ScalarLeviPositiveCurrent LocalCurrentLebesgue PositiveCurrentACTopMeasure
  GlobalPositiveCurrentACRestriction

private theorem reader_restrict {m : ℕ} {U V : Opens (ComplexModel (m + 1))}
    (hVU : V ≤ U) (D : DistributionForm U 2) :
    complementaryRead (restrictForm D hVU) = restrict hVU (complementaryRead D) := by
  ext γ φ
  have hφ : (TestFunction.monoCLM ℝ φ : 𝓓(U, ℝ)) = extTest hVU φ := by
    ext y
    rw [congrFun (testFunction_inclusion_coe hVU φ) y, extTest_apply]
  simp only [complementaryRead, LinearMap.smul_apply, LinearMap.smulRight_apply,
    LinearMap.sum_apply, _root_.sum_apply, _root_.smul_apply, restrictForm_apply,
    LocalBedfordTaylorLocality.restrict_apply, smul_eq_mul, hφ]

private theorem regular_canonical_volume {n : ℕ} {U : Opens (ComplexModel n)}
    (f : ComplexModel n → ℝ)
    (hf : LocallyIntegrableOn f U (canonicalBasis n).addHaar)
    (hv : LocallyIntegrableOn f U volume) :
    regularDistribution (canonicalBasis n).addHaar f hf = regularDistribution volume f hv := by
  ext φ
  simp only [regularDistribution_apply]
  rw [addHaar_canonicalBasis]

private theorem ac_congr {m : ℕ} {U : Opens (ComplexModel (m + 1))}
    {S R : LocalProductCurrent (m + 1) U m}
    (hS : IsPositive S) (hR : IsPositive R) (h : S = R) :
    acTopMeasure hS = acTopMeasure hR := by
  subst R
  rfl

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- Any genuine prescribed smooth local background potential internally gives
PSH, finite AE, L1 and the SAME full original theta current and AC measure.
No compactness, Kahler, analytic, bounded, finite or current-equality input. -/
theorem exists_corrected_original_chart_reader
    (θ : SmoothRealForm (m + 1) M 2) {u : M → EReal}
    (hu : IsThetaPshPotential θ u) (e : ComplexChart (m + 1) M)
    {W : Opens (ComplexModel (m + 1))} (ρ : ComplexModel (m + 1) → ℝ)
    (hpot : IsSmoothLocalPotential θ e W ρ) :
    let hW : W ≤ chartTarget e := hpot.2.1
    let v : ComplexModel (m + 1) → EReal := fun z => chartFunction u e z + (ρ z : EReal)
    let T := thetaPotentialCurrent θ u hu
    let hT : IsFullPositive T := fun e α hα => thetaPotentialCurrent_full_positive θ u hu e α hα
    let hS := isPositive_chartSpanCurrent T hT e
    PlurisubharmonicOn v W ∧
      (∀ᵐ z ∂volume.restrict (W : Set (ComplexModel (m + 1))), v z ≠ ⊤ ∧ v z ≠ ⊥) ∧
      ∃ hL : LocallyIntegrableOn (fun z => (v z).toReal) W volume,
        restrictForm (T.coefficients (canonicalBasis (m + 1)) e) hW =
          ddC (regularDistribution volume (fun z => (v z).toReal) hL) ∧
        let R := ddc (scalarTopCurrent (regularDistribution volume (fun z => (v z).toReal) hL))
        restrict hW (chartSpanCurrent T e) = R ∧
        ∃ hR : IsPositive R,
          acTopMeasure hR = (acTopMeasure hS).restrict (W : Set (ComplexModel (m + 1))) := by
  let hW : W ≤ chartTarget e := hpot.2.1
  let v : ComplexModel (m + 1) → EReal := fun z => chartFunction u e z + (ρ z : EReal)
  let T := thetaPotentialCurrent θ u hu
  let hT : IsFullPositive T := fun e α hα => thetaPotentialCurrent_full_positive θ u hu e α hα
  let hS := isPositive_chartSpanCurrent T hT e
  have hp : PlurisubharmonicOn v W :=
    ThetaPshDecreasingLimit.plurisubharmonicOn_corrected_of_thetaPlurisubharmonic hu.1 e hpot
  have hraw : ∀ᵐ z ∂volume.restrict (W : Set (ComplexModel (m + 1))),
      chartFunction u e z ≠ ⊤ ∧ chartFunction u e z ≠ ⊥ := by
    have h := quasiPsh_chart_ae_finite (canonicalBasis (m + 1)) (Nat.succ_pos m)
      u hu.quasiPshPotential e
    rw [addHaar_canonicalBasis] at h
    exact h.filter_mono (ae_mono (Measure.restrict_mono_set volume hW))
  have hfin : ∀ᵐ z ∂volume.restrict (W : Set (ComplexModel (m + 1))),
      v z ≠ ⊤ ∧ v z ≠ ⊥ := by
    filter_upwards [hraw] with z hz
    have hc := EReal.coe_toReal hz.1 hz.2
    change chartFunction u e z + (ρ z : EReal) ≠ ⊤ ∧
      chartFunction u e z + (ρ z : EReal) ≠ ⊥
    rw [← hc, ← EReal.coe_add]
    exact ⟨EReal.coe_ne_top _, EReal.coe_ne_bot _⟩
  let f := fun z => (chartFunction u e z).toReal
  have hfe : LocallyIntegrableOn f (chartTarget e) volume :=
    hu.quasiPshPotential.locallyIntegrableOn_chart_toReal e
  have hfu := hfe.mono_set hW
  have hρ : LocallyIntegrableOn ρ W volume :=
    hpot.2.2.1.continuousOn.locallyIntegrableOn W.isOpen.measurableSet
  have hcorr : (fun z => f z + ρ z) =ᵐ[volume.restrict W] fun z => (v z).toReal := by
    filter_upwards [hraw] with z hz
    dsimp only [v, f]
    rw [EReal.toReal_add hz.1 hz.2 (EReal.coe_ne_top _) (EReal.coe_ne_bot _), EReal.toReal_coe]
  have hL : LocallyIntegrableOn (fun z => (v z).toReal) W volume :=
    (hfu.add hρ).congr hcorr
  have hsum : regularDistribution volume (fun z => (v z).toReal) hL =
      regularDistribution volume ρ hρ + regularDistribution volume f hfu := by
    rw [regularDistribution_congr_ae_on hL (hfu.add hρ) hcorr.symm]
    exact (ThetaPshChartLimitGluing.regularDistribution_add hfu hρ).trans (add_comm _ _)
  have hcoeff : restrictForm (T.coefficients (canonicalBasis (m + 1)) e) hW =
      ddC (regularDistribution volume (fun z => (v z).toReal) hL) := by
    change restrictForm ((smoothGlobalCurrent (canonicalBasis (m + 1)) θ +
      globalDDC (canonicalBasis (m + 1)) (Nat.succ_pos m) u hu.quasiPshPotential).coefficients
        (canonicalBasis (m + 1)) e) hW = _
    rw [GlobalCurrent.coefficients_add, restrictForm_add,
      restrictForm_smoothFormDistribution_eq_ddC θ e hW ρ hpot,
      globalDDC_coefficients, chartDDC, restrictForm_ddC, restrictDistribution_regularDistribution]
    change ddC (regularDistribution (canonicalBasis (m + 1)).addHaar ρ _) +
      ddC (regularDistribution (canonicalBasis (m + 1)).addHaar f _) = _
    rw [regular_canonical_volume ρ _ hρ, regular_canonical_volume f _ hfu]
    have hadd := map_add ddCLM (regularDistribution volume ρ hρ)
      (regularDistribution volume f hfu)
    exact hadd.symm.trans (congrArg ddC hsum.symm)
  have hreader : restrict hW (chartSpanCurrent T e) =
      ddc (scalarTopCurrent (regularDistribution volume (fun z => (v z).toReal) hL)) := by
    calc
      restrict hW (chartSpanCurrent T e) =
          complementaryRead (restrictForm (T.coefficients (canonicalBasis (m + 1)) e) hW) := by
        rw [reader_restrict, complementaryRead_coefficients_eq_chartSpanCurrent]
      _ = _ := by rw [hcoeff, complementaryRead_ddC]
  have hR : IsPositive (ddc (scalarTopCurrent
      (regularDistribution volume (fun z => (v z).toReal) hL))) := by
    rw [← hreader]
    exact isPositive_restrict hS hW
  have hmeasure := (ac_congr (isPositive_restrict hS hW) hR hreader).symm.trans
    (acTopMeasure_restrict hS hW)
  exact ⟨hp, hfin, hL, hcoeff, hreader, hR, hmeasure⟩

end SGPT.Foundations.Analysis.Pending.ThetaPotentialPrescribedChartReader
