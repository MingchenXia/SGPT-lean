import SGPT.Foundations.Analysis.Pending.SingularModelEnergyCoreDefectIdentification
import SGPT.Foundations.Analysis.Pending.RawCurveCoreCutoffs
import SGPT.Foundations.Analysis.Pending.SingularSmoothTestLocalizedChartStokes

set_option autoImplicit false

/-!
# The actual finite core model-energy pairing is the genuine global test pairing

Xia SGPT PDF0171's signed current computation, on actual defining E1 model
energy and actual global NP measures. The genuine finite geometric inputs
produce every signed chart field and both independent integral identities.
The actual simultaneous base cover and global regularizer choice are later
producers; no fibre/current identity or energy affinity is assumed here.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.SingularModelEnergyGlobalCorePairing

open scoped ProductComplexManifold
open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativePreceqClasses
  GlobalNonPluripolar GlobalSlotStokes ProductComplexManifold CompactAffineCurveCharts
  FiniteGeodesicMaximality BedfordTaylorStripCovariance FiniteGeodesicStripCharts
  BedfordTaylorTimeSlot SingularModelEnergyCoreChartData
  SingularModelEnergyCoreSignedChartData SingularModelEnergyFibrePairing
  SingularModelEnergyProductPartition SingularModelEnergyCoreDefectIdentification
  SmoothLastSlotChartRegularizer RawCurveCoreCutoffs
  SingularSmoothTestLastSlot SingularSmoothTestChartStokes SingularSmoothTestLocalizedChartStokes

noncomputable section

variable {n : ℕ} {M T : Type*}
  [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]
  [TopologicalSpace T] [MeasurableSpace T] [BorelSpace T]
  [ChartedSpace (ComplexModel 1) T] [IsComplexManifold 1 T] [CompactSpace T]
  {θ : ClosedRealOneOneForm n M} {φ : M → EReal} {hφ : IsModelPotential θ φ}

/-- Genuine finite core geometry internally produces defining model-energy test integrability and its exact global compact NP diagonal pairing, without a current/fibre identity input. -/
theorem integrable_and_energy_pairing_eq_global_test
    (omegaM : KahlerBackground n M) (omegaHost : KahlerBackground (n + 1) (M × T))
    (e : ComplexChart 1 T) (N : Opens T) (κ : ClosedRealOneOneForm 1 T)
    (hκzero : ∀ z ∈ e.val.target, e.val.symm z ∈ N → κ.val.coeff e z = 0)
    (Γ : ClosedRealOneOneForm (n + 1) (M × T))
    {W : M × T → EReal}
    (hW : IsThetaPshPotential (prodForm θ κ).val W)
    (hΦ : IsThetaPshPotential (prodForm θ κ).val (fun z : M × T => φ z.1))
    (hWΦ : SameSingularityTypeOn W (fun z : M × T => φ z.1) univ)
    (U : ℝ → M → EReal) (time : T → ℂ)
    (hcore : ∀ x y, y ∈ N → W (x, y) = U (time y).re x)
    (hU : ∀ σ ∈ coreTimeDomain e N,
      RelativeFiniteEnergyPreceq θ φ (U (time (e.val.symm (curveModelEquiv.symm σ))).re) hφ)
    {m : ℕ} (χ : Fin m → M → ℝ) (J : Fin m → SlotChart (fun _ : Fin n => θ) θ)
    (hχs : ∀ a, ChartSmooth (n := n) (χ a)) (hχ0 : ∀ a x, 0 ≤ χ a x)
    (hχJ : ∀ a, tsupport (χ a) ⊆ ((J a).source : Set M))
    (hχc : ∀ a, HasCompactSupport (χ a)) (hχ1 : ∀ x, ∑ a, χ a x = 1)
    (ρΓ : Fin m → ComplexModel (n + 1) → ℝ)
    (hρΓ : ∀ a, IsSmoothLocalPotential Γ.val (productComplexChart (J a).chart e)
      (stripLift (J a).domain (coreTimeDomain e N) (coreTimeDomain e N).isOpen) (ρΓ a))
    {ξ : T → ℝ} (hξ : ChartSmooth (n := 1) ξ) (hξc : HasCompactSupport ξ)
    (hξe : tsupport ξ ⊆ e.val.source) (hξN : tsupport ξ ⊆ (N : Set T))
    (hξ0 : ∀ y, 0 ≤ ξ y) (G : M × T → ℝ) (hGsm : ChartSmooth (n := n + 1) G)
    (hp : IsThetaPshPotential Γ.val (fun z => (G z : EReal)))
    (hq : IsThetaPshPotential Γ.val (fun _ => 0))
    (hξG : EqOn (fun z : M × T => ξ z.2) (fun _ => 1) (tsupport G))
    {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψS : tsupport ψ ⊆ (coreTimeDomain e N : Set ℂ))
    (hξψ : ∀ σ ∈ tsupport ψ, rawCurveCutoff e ξ σ = 1)
    (hG : ∀ a, EqOn (fun z => G ((productComplexChart (J a).chart e).val.symm z))
      (timeLift n ψ) (stripLift (J a).domain (coreTimeDomain e N) (coreTimeDomain e N).isOpen)) :
    let F := fun σ => timeLaplacian ψ σ * modelEnergyCurve θ φ hφ
      (fun σ => U (time (e.val.symm (curveModelEquiv.symm σ))).re) (coreTimeDomain e N) σ
    Integrable F ∧ (((n : ℝ) + 1) / Real.pi) * (∫ σ : ℂ, F σ) =
      (∫ z, G z ∂globalMixedMeasure (fun _ => prodForm θ κ) (fun _ => W) (fun _ => hW.1)) -
      (∫ z, G z ∂globalMixedMeasure (fun _ => prodForm θ κ)
        (fun _ => fun z : M × T => φ z.1) (fun _ => hΦ.1)) := by
  classical
  intro F
  let S := coreTimeDomain e N
  let V := fun σ => U (time (e.val.symm (curveModelEquiv.symm σ))).re
  let ζ := rawCurveCutoff e ξ
  have hz := rawCurveCutoff_properties e N hξ hξc hξe hξN hξ0
  have hζ : Continuous ζ := hz.1.continuous
  have hζc : HasCompactSupport ζ := hz.2.1
  have hζS : tsupport ζ ⊆ (S : Set ℂ) := hz.2.2.1
  have hζ0 : ∀ σ, 0 ≤ ζ σ := hz.2.2.2
  have hzero : ChartSmooth (n := n + 1) (fun _ : M × T => (0 : ℝ)) :=
    fun _ => contDiffOn_const
  let d : ∀ a, SignedChartData θ φ V S S.isOpen (J a) (χ a) ψ ζ := fun a =>
    signedChartData_of_smooth_compact_host omegaHost (J a) e N κ hκzero Γ (ρΓ a) (hρΓ a)
      hW.1 hΦ.1 hWΦ U time hcore (hχs a) (hχc a) (hχJ a) hζ hζc hζS
      (fun _ => G) (fun _ _ => 0) (fun _ => hGsm) (fun _ => hzero)
      (fun _ => hp.1) (fun _ => hq.1) G (fun _ _ => (zero_add _).symm) (hG a)
  have hpair := integrable_and_sum_defect_eq_model_energy_pairing omegaM V S S.isOpen hU
    χ J hχs hχ0 hχJ hχc hχ1 hζ hζc hζS hζ0 hψ hψS hξψ d
  let P := fun a => coreStokesSlotChart (J a) e N κ hκzero Γ (ρΓ a) (hρΓ a)
  let w := fun a => productWeight (χ a) ξ
  have hws (a : Fin m) : ChartSmooth (n := n + 1) (w a) :=
    chartSmooth_productWeight (hχs a) hξ
  have hwP (a : Fin m) : tsupport (w a) ⊆ ((P a).source : Set (M × T)) :=
    tsupport_productWeight_subset_core_chart (J a) e N (hχJ a) hξe hξN
  have hξhost : Continuous (fun z : M × T => ξ z.2) :=
    (ProductTestForms.ChartSmooth.continuous hξ).comp continuous_snd
  have hsum (z : M × T) : (∑ a, w a z) = ξ z.2 := sum_productWeight_eq χ ξ hχ1 z
  have hstokes := sum_localized_chart_defect_eq_smooth_test_stokes omegaHost hW hΦ hWΦ
    hp hq hGsm w P hws hwP hξhost hξG hsum
  have hd (k : Fin (n + 1)) (a : Fin m) : (d a).defect k =
      (∫ q, chartWeight (P a) (w a) W (fun z : M × T => φ z.1) q
        ∂lastHybridChartMeasure hW hΦ hp (P a) k) -
      (∫ q, chartWeight (P a) (w a) W (fun z : M × T => φ z.1) q
        ∂lastHybridChartMeasure hW hΦ hq (P a) k) := by
    exact produced_defect_eq_stokes_chart_defect omegaHost (J a) e N κ hκzero Γ (ρΓ a) (hρΓ a)
      hW hΦ hWΦ U time hcore (hχs a) (hχc a) (hχJ a) hξ hξc hξe hξN
      (fun _ => G) (fun _ _ => 0) (fun _ => hGsm) (fun _ => hzero)
      (fun _ => hp) (fun _ => hq) G (fun _ _ => (zero_add _).symm) (hG a) k
  refine ⟨hpair.1, ?_⟩
  calc
    (((n : ℝ) + 1) / Real.pi) * (∫ σ : ℂ, F σ) = ∑ k : Fin (n + 1), ∑ a : Fin m, (d a).defect k :=
      hpair.2.symm
    _ = _ := by
      rw [Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun a _ => hd k a))]
      exact hstokes

end

end SGPT.Foundations.Analysis.Pending.SingularModelEnergyGlobalCorePairing
