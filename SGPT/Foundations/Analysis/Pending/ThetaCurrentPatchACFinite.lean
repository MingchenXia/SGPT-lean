import SGPT.Foundations.Analysis.Pending.ThetaPshPatchACFinite
import SGPT.Foundations.Analysis.Pending.NaturalThetaPshClosedCurrent
import SGPT.Foundations.Analysis.Pending.GlobalPositiveCurrentACRestriction
import SGPT.Foundations.Analysis.Pending.FullPositiveCurrentLocalPshPotential

set_option autoImplicit false

/-! Exact SAME original theta current on genuine potential patches and
canonical original-chart AC finiteness. Entire BP math/proof precedes Lean.
No weak analytic, prescribed reader/current equality/mass/class cert. -/
noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions
namespace SGPT.Foundations.Analysis.Pending.ThetaCurrentPatchACFinite
open FirstPass FirstPass.GlobalPotentialPatches FirstPass.PositiveClasses
  _root_.SGPT.Foundations.Analysis.LocalCurrents LocalProductCurrents LocalBedfordTaylorProducts
  LocalBedfordTaylorLocality ScalarLeviPositiveCurrent LelongPoincareDivisor
  GlobalCurrents GlobalCurrentPotentials CanonicalCurrentFrame
  ActualDistributionTwoFormReading ActualDistributionTwoFormDdc ActualCanonicalComplementaryCurrentCalibration
  ActualAnalyticCurrentLocalDensity GlobalPositiveCurrentACRestriction PositiveCurrentACTopMeasure
  NaturalThetaPshGeometricCurrent NaturalThetaPshClosedCurrent ThetaPshPatchACFinite

private theorem reader_restrict {m : ℕ} {U V : Opens (ComplexModel (m+1))}
    (hVU : V ≤ U) (A : DistributionForm U 2) :
    complementaryRead (restrictForm A hVU) = restrict hVU (complementaryRead A) := by
  ext γ φ
  have hφ : (TestFunction.monoCLM ℝ φ : 𝓓(U, ℝ)) = extTest hVU φ := by
    ext y
    rw [congrFun (testFunction_inclusion_coe hVU φ) y, extTest_apply]
  simp only [complementaryRead, LinearMap.smul_apply,
    LinearMap.smulRight_apply, LinearMap.sum_apply, _root_.sum_apply, _root_.smul_apply,
    restrictForm_apply, LocalBedfordTaylorLocality.restrict_apply, smul_eq_mul, hφ]

private theorem ac_congr {m : ℕ} {U : Opens (ComplexModel (m+1))}
    {S R : LocalProductCurrent (m+1) U m} (hS : IsPositive S) (hR : IsPositive R)
    (h : S = R) : acTopMeasure hS = acTopMeasure hR := by
  subst R
  rfl

private theorem regular_canonical_volume {n : ℕ} {U : Opens (ComplexModel n)}
    (f : ComplexModel n → ℝ)
    (hf : LocallyIntegrableOn f U (canonicalBasis n).addHaar)
    (hv : LocallyIntegrableOn f U volume) :
    regularDistribution (canonicalBasis n).addHaar f hf = regularDistribution volume f hv := by
  ext φ
  simp only [regularDistribution_apply]
  rw [addHaar_canonicalBasis]

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel (m+1)) M] [IsComplexManifold (m+1) M] [CompactSpace M]

/-- SAME original full current equals the actual corrected scalar reader;
its original canonical AC measure is internally finite on ALL patch compacts. -/
theorem exists_original_chart_ac_finite
    (omega : KahlerBackground (m+1) M) (σ : ClosedRealOneOneForm (m+1) M)
    {u : M → EReal} (hu : IsThetaPshPotential σ.val u)
    (P : Patch (fun _ : Fin (m+1) => σ) (fun _ => u)) :
    let T := thetaPotentialCurrent σ.val u hu
    let hpos : IsFullPositive T := fun e α hα => thetaPotentialCurrent_full_positive σ.val u hu e α hα
    let hS := isPositive_chartSpanCurrent T hpos P.chart
    ∃ hL : LocallyIntegrableOn (fun z => (P.corrected 0 z).toReal) P.domain volume,
      restrict P.domain_le_target (chartSpanCurrent T P.chart) =
        ddc (scalarTopCurrent (regularDistribution volume (fun z => (P.corrected 0 z).toReal) hL)) ∧
      ∀ K : Set (ComplexModel (m+1)), IsCompact K → K ⊆ P.domain → acTopMeasure hS K < ⊤ := by
  classical
  dsimp only
  let θ : SmoothRealForm (m+1) M 2 := σ.val
  have hU : P.domain ≤ chartTarget P.chart := P.domain_le_target
  let T := thetaPotentialCurrent θ u hu
  let hpos : IsFullPositive T := fun e α hα => thetaPotentialCurrent_full_positive σ.val u hu e α hα
  let hS := isPositive_chartSpanCurrent T hpos P.chart
  obtain ⟨hL,hTv,_hle,hfinite⟩ := exists_patch_ac_domination_and_finite omega σ hu P
  let f := fun z => (chartFunction u P.chart z).toReal
  have hfe : LocallyIntegrableOn f (chartTarget P.chart) volume :=
    hu.quasiPshPotential.locallyIntegrableOn_chart_toReal P.chart
  have hfu := hfe.mono_set P.domain_le_target
  have hρ : LocallyIntegrableOn (P.potential 0) P.domain volume :=
    (P.localPotential 0).2.2.1.continuousOn.locallyIntegrableOn P.domain.isOpen.measurableSet
  have hraw : ∀ᵐ z ∂volume.restrict P.domain,
      chartFunction u P.chart z ≠ ⊤ ∧ chartFunction u P.chart z ≠ ⊥ := by
    have h := quasiPsh_chart_ae_finite (canonicalBasis (m+1)) (Nat.succ_pos m)
      u hu.quasiPshPotential P.chart
    rw [addHaar_canonicalBasis] at h
    exact h.filter_mono (ae_mono (Measure.restrict_mono_set volume P.domain_le_target))
  have hcorr : (fun z => (P.corrected 0 z).toReal)
      =ᵐ[volume.restrict P.domain] fun z => f z + P.potential 0 z := by
    filter_upwards [hraw] with z hz
    dsimp only [Patch.corrected,f]
    rw [EReal.toReal_add hz.1 hz.2 (EReal.coe_ne_top _) (EReal.coe_ne_bot _), EReal.toReal_coe]
  have hsum : regularDistribution volume (fun z => (P.corrected 0 z).toReal) hL =
      regularDistribution volume (P.potential 0) hρ + regularDistribution volume f hfu := by
    rw [regularDistribution_congr_ae_on hL (hfu.add hρ) hcorr]
    change regularDistribution volume (fun z => f z + P.potential 0 z) (hfu.add hρ) = _
    exact (ThetaPshChartLimitGluing.regularDistribution_add hfu hρ).trans (add_comm _ _)
  have hcoeff : restrictForm (T.coefficients (canonicalBasis (m+1)) P.chart) hU =
      ddC (regularDistribution volume (fun z => (P.corrected 0 z).toReal) hL) := by
    change restrictForm ((smoothGlobalCurrent (canonicalBasis (m+1)) θ +
      globalDDC (canonicalBasis (m+1)) (Nat.succ_pos m) u hu.quasiPshPotential).coefficients
        (canonicalBasis (m+1)) P.chart) hU = _
    rw [GlobalCurrent.coefficients_add, restrictForm_add,
      restrictForm_smoothFormDistribution_eq_ddC θ P.chart hU
        (P.potential 0) (P.localPotential 0), globalDDC_coefficients, chartDDC,
      restrictForm_ddC, restrictDistribution_regularDistribution]
    change ddC (regularDistribution (canonicalBasis (m+1)).addHaar (P.potential 0) _) +
      ddC (regularDistribution (canonicalBasis (m+1)).addHaar f _) = _
    rw [regular_canonical_volume (P.potential 0) _ hρ, regular_canonical_volume f _ hfu]
    have hadd : ddC (regularDistribution volume (P.potential 0) hρ + regularDistribution volume f hfu) =
        ddC (regularDistribution volume (P.potential 0) hρ) + ddC (regularDistribution volume f hfu) :=
      map_add ddCLM _ _
    exact hadd.symm.trans (congrArg ddC hsum.symm)
  have hcurrent : restrict hU (chartSpanCurrent T P.chart) =
      ddc (scalarTopCurrent (regularDistribution volume (fun z => (P.corrected 0 z).toReal) hL)) := by
    calc
      restrict hU (chartSpanCurrent T P.chart) =
          restrict hU (complementaryRead (T.coefficients (canonicalBasis (m+1)) P.chart)) :=
        congrArg (restrict hU) (complementaryRead_coefficients_eq_chartSpanCurrent T P.chart).symm
      _ = complementaryRead (restrictForm (T.coefficients (canonicalBasis (m+1)) P.chart) hU) :=
        (reader_restrict hU _).symm
      _ = _ := by rw [hcoeff,complementaryRead_ddC]
  refine ⟨hL,hcurrent,?_⟩
  let hR := isPositive_restrict hS hU
  have hmu := ac_congr hR hTv hcurrent
  intro K hK hKP
  have heq : acTopMeasure hS K = acTopMeasure hTv K := by
    calc
      acTopMeasure hS K = (acTopMeasure hS).restrict P.domain K := by
        rw [Measure.restrict_apply hK.measurableSet, inter_eq_left.mpr hKP]
      _ = acTopMeasure hR K := congrArg (fun μ => μ K) (acTopMeasure_restrict hS hU).symm
      _ = acTopMeasure hTv K := congrArg (fun μ => μ K) hmu
  rw [heq]
  exact hfinite K hK hKP

end SGPT.Foundations.Analysis.Pending.ThetaCurrentPatchACFinite
