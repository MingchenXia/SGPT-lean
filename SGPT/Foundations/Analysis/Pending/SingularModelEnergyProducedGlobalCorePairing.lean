import SGPT.Foundations.Analysis.Pending.SingularModelEnergyGlobalCorePairing
import SGPT.Foundations.Analysis.Pending.SingularModelEnergySimultaneousPartition
import SGPT.Foundations.Analysis.Pending.FlatCurveRegularizerPotential
import SGPT.Foundations.Analysis.Pending.SingularProductCoreTestStokesZero

set_option autoImplicit false

/-!
# Actual compact test geometry produces the full model-energy test pairing

Xia SGPT PDF0171. The actual simultaneous base cover, actual flat product
regularizer potential, actual global smooth test background and actual
curve cutoff are produced internally. Neither partition/local-potential
certificates, smooth PSH pair certificates, scalar chart identities nor
target fibre/current/energy identities are incoming assumptions.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.SingularModelEnergyProducedGlobalCorePairing

open scoped ProductComplexManifold
open FirstPass FirstPass.HolomorphicMaps FirstPass.PositiveClasses
  RelativeEnergy RelativePreceqClasses GlobalNonPluripolar GlobalSlotStokes
  ProductComplexManifold FlatComplexTorus CompactAffineCurveCharts
  AffineCurveSmoothTests AffineCurveCoreTests RawCurveCoreCutoffs
  FiniteGeodesicMaximality BedfordTaylorStripCovariance FiniteGeodesicStripCharts
  BedfordTaylorTimeSlot SingularModelEnergyCoreChartData SingularModelEnergyFibrePairing
  SingularModelEnergySimultaneousPartition FlatCurveRegularizerPotential
  SingularSmoothTestStokes SingularModelEnergyGlobalCorePairing SingularProductCoreTestStokesZero

noncomputable section

variable {n : ℕ} {M : Type*}
  [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]
  {θ : ClosedRealOneOneForm n M} {φ : M → EReal} {hφ : IsModelPotential θ φ}

/-- Actual compact curve fit internally supplies the base partition, smooth test background and both PSH slots, all regularizer local potentials, the core cutoff and all actual scalar readings; the defining energy pairing and its integrability follow. -/
theorem integrable_and_energy_pairing_eq_global_test
    (omegaM : KahlerBackground n M) (e : ComplexChart 1 (Torus 1))
    (N : Opens (Torus 1)) (hNe : (N : Set (Torus 1)) ⊆ e.val.source)
    (κ : ClosedRealOneOneForm 1 (Torus 1))
    (hκzero : ∀ z ∈ e.val.target, e.val.symm z ∈ N → κ.val.coeff e z = 0)
    {W : M × Torus 1 → EReal}
    (hW : IsThetaPshPotential (prodForm θ κ).val W)
    (hΦ : IsThetaPshPotential (prodForm θ κ).val (fun z : M × Torus 1 => φ z.1))
    (hWΦ : SameSingularityTypeOn W (fun z : M × Torus 1 => φ z.1) univ)
    (U : ℝ → M → EReal) (time : Torus 1 → ℂ)
    (hcore : ∀ x y, y ∈ N → W (x, y) = U (time y).re x)
    (hU : ∀ σ ∈ coreTimeDomain e N,
      RelativeFiniteEnergyPreceq θ φ (U (time (e.val.symm (curveModelEquiv.symm σ))).re) hφ)
    (z0 : ComplexModel 1) {δ : ℝ} (hδ : 0 < δ) {ψ : ℂ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψc : IsCompact (tsupport ψ))
    (hfit : ∀ τ ∈ tsupport ψ, z0 + δ • curveModelEquiv.symm τ ∈ e.val.target)
    (hfitN : ∀ τ ∈ tsupport ψ, e.val.symm (z0 + δ • curveModelEquiv.symm τ) ∈ N) :
    let G := fun z : M × Torus 1 => affineCurveTest e z0 δ ψ z.2
    let F := fun σ => timeLaplacian (rawTimeTest z0 δ ψ) σ * modelEnergyCurve θ φ hφ
      (fun σ => U (time (e.val.symm (curveModelEquiv.symm σ))).re) (coreTimeDomain e N) σ
    Integrable F ∧ (((n : ℝ) + 1) / Real.pi) * (∫ σ : ℂ, F σ) =
      (∫ z, G z ∂globalMixedMeasure (fun _ => prodForm θ κ) (fun _ => W) (fun _ => hW.1)) -
      (∫ z, G z ∂globalMixedMeasure (fun _ => prodForm θ κ)
        (fun _ => fun z : M × Torus 1 => φ z.1) (fun _ => hΦ.1)) := by
  classical
  intro G F
  let omegaHost := prodKahlerBackground omegaM (flatKahlerBackground 1)
  have hGsm : ChartSmooth (n := n + 1) G :=
    chartSmooth_product_affineCurveTest e z0 hδ.ne' hψ hψc hfit
  obtain ⟨A, _, hp, hq, _⟩ := exists_smooth_test_background omegaHost G hGsm
  let Γ := A • omegaHost.form
  obtain ⟨m, χ, J, rM, hχs, hχ0, hχJ, hχc, hχ1, hrM, _⟩ :=
    exists_finite_energy_chart_partition_with_background θ omegaM.form
  let ρΓ : Fin m → ComplexModel (n + 1) → ℝ := fun a q => A *
    (rM a (coordinateMap (Prod.fst : M × Torus 1 → M)
      (productComplexChart (J a).chart e) (J a).chart q) +
    Real.pi * ‖coordinateMap (Prod.snd : M × Torus 1 → Torus 1)
      (productComplexChart (J a).chart e) e q‖ ^ 2)
  have hρΓ (a : Fin m) : IsSmoothLocalPotential Γ.val (productComplexChart (J a).chart e)
      (stripLift (J a).domain (coreTimeDomain e N) (coreTimeDomain e N).isOpen) (ρΓ a) :=
    isSmoothLocalPotential_product_core (J a) e N omegaM.form (rM a) (hrM a) A
  let K := (fun τ => e.val.symm (z0 + δ • curveModelEquiv.symm τ)) '' tsupport ψ
  have hKc : IsCompact K := by
    apply hψc.image_of_continuousOn
    have hc : Continuous (fun τ : ℂ => z0 + δ • curveModelEquiv.symm τ) := by fun_prop
    exact e.val.symm.continuousOn.comp hc.continuousOn hfit
  have hKN : K ⊆ (N : Set (Torus 1)) := by
    rintro _ ⟨τ, hτ, rfl⟩
    exact hfitN τ hτ
  obtain ⟨ξ, hξ, hξc, hξN, hξ01, O, _, hKO, hξO⟩ := exists_chartSmooth_core_cutoff hKc N hKN
  have hξe : tsupport ξ ⊆ e.val.source := hξN.trans hNe
  have hξK (y : Torus 1) (hy : y ∈ K) : ξ y = 1 := hξO y (hKO hy)
  have hξψ : ∀ σ ∈ tsupport (rawTimeTest z0 δ ψ), rawCurveCutoff e ξ σ = 1 :=
    rawCurveCutoff_eq_one_on_test_support e z0 hδ.ne' hψc ξ hfit
      (fun τ hτ => hξK _ ⟨τ, hτ, rfl⟩)
  have hGsupport : tsupport G ⊆ Prod.snd ⁻¹' K := by
    intro q hq
    have hcurve := tsupport_comp_subset_preimage (affineCurveTest e z0 δ ψ) continuous_snd hq
    exact tsupport_affineCurveTest_subset e z0 hδ.ne' hψc hfit hcurve
  have hξG : EqOn (fun z : M × Torus 1 => ξ z.2) (fun _ => 1) (tsupport G) :=
    fun q hq => hξK q.2 (hGsupport hq)
  have hGraw (a : Fin m) : EqOn
      (fun q => G ((productComplexChart (J a).chart e).val.symm q))
      (timeLift n (rawTimeTest z0 δ ψ))
      (stripLift (J a).domain (coreTimeDomain e N) (coreTimeDomain e N).isOpen) := by
    intro q hq
    have hcurve : curveModelEquiv.symm ((stripModelEquiv n q).2) =
        ((prodModelEquiv n 1).symm q).2 := by
      change curveModelEquiv.symm (curveModelEquiv (((prodModelEquiv n 1).symm q).2)) = _
      exact curveModelEquiv.symm_apply_apply _
    exact product_affineCurveTest_eq_timeLift (J a).chart e z0 δ ψ q (hcurve ▸ hq.2.1)
  have hraw := rawTimeTest_compact_support_core e z0 hδ.ne' hψc N hfit hfitN
  exact SingularModelEnergyGlobalCorePairing.integrable_and_energy_pairing_eq_global_test
    omegaM omegaHost e N κ hκzero Γ hW hΦ hWΦ U time hcore hU χ J hχs hχ0 hχJ hχc hχ1
    ρΓ hρΓ hξ hξc hξe hξN (fun y => (hξ01 y).1) G hGsm hp hq hξG
    (contDiff_rawTimeTest z0 δ hψ) hraw.2 hξψ hGraw

/-- Genuine finite-energy Perron endpoints and actual compact affine core geometry internally produce the full raw model-energy test integrability and zero integral, from the actual two independently proved diagonal NP equations. -/
theorem integrable_and_core_perron_energy_pairing_eq_zero
    (omegaM : KahlerBackground n M) {u₀ u₁ : M → EReal}
    (hu₀ : RelativeFiniteEnergyPreceq θ φ u₀ hφ) (hu₁ : RelativeFiniteEnergyPreceq θ φ u₁ hφ)
    (e : ComplexChart 1 (Torus 1)) (N : Opens (Torus 1))
    (hNe : (N : Set (Torus 1)) ⊆ e.val.source) (κ : ClosedRealOneOneForm 1 (Torus 1))
    (hκzero : ∀ z ∈ e.val.target, e.val.symm z ∈ N → κ.val.coeff e z = 0)
    {W : M × Torus 1 → EReal}
    (hW : IsThetaPshPotential (prodForm θ κ).val W)
    (hΦ : IsThetaPshPotential (prodForm θ κ).val (fun z : M × Torus 1 => φ z.1))
    (hWΦ : SameSingularityTypeOn W (fun z : M × Torus 1 => φ z.1) univ)
    (z0 : ComplexModel 1) {δ : ℝ} (hδ : 0 < δ)
    (htime : ∀ y ∈ N, (curveModelEquiv (δ⁻¹ • (e.val y - z0))).re ∈ Ioo (0 : ℝ) 1)
    (hcore : ∀ x y, y ∈ N → W (x, y) =
      finiteGeodesic θ.val u₀ u₁ (curveModelEquiv (δ⁻¹ • (e.val y - z0))).re x)
    {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : IsCompact (tsupport ψ))
    (hfit : ∀ τ ∈ tsupport ψ, z0 + δ • curveModelEquiv.symm τ ∈ e.val.target)
    (hfitN : ∀ τ ∈ tsupport ψ, e.val.symm (z0 + δ • curveModelEquiv.symm τ) ∈ N) :
    let time := fun y : Torus 1 => curveModelEquiv (δ⁻¹ • (e.val y - z0))
    let F := fun σ => timeLaplacian (rawTimeTest z0 δ ψ) σ * modelEnergyCurve θ φ hφ
      (fun σ => finiteGeodesic θ.val u₀ u₁ (time (e.val.symm (curveModelEquiv.symm σ))).re)
      (coreTimeDomain e N) σ
    Integrable F ∧ (∫ σ : ℂ, F σ) = 0 := by
  classical
  intro time F
  have hU (σ : ℂ) (hσ : σ ∈ coreTimeDomain e N) :
      RelativeFiniteEnergyPreceq θ φ
        (finiteGeodesic θ.val u₀ u₁ (time (e.val.symm (curveModelEquiv.symm σ))).re) hφ :=
    relativeFiniteEnergyPreceq_finiteGeodesic omegaM hu₀ hu₁
      (htime _ hσ.2)
  have hpair := integrable_and_energy_pairing_eq_global_test omegaM e N hNe κ hκzero
    hW hΦ hWΦ (finiteGeodesic θ.val u₀ u₁) time hcore hU z0 hδ hψ hψc hfit hfitN
  let G := fun q : M × Torus 1 => affineCurveTest e z0 δ ψ q.2
  have hgs (q : M × Torus 1) (hq : q ∈ tsupport G) : q.2 ∈ e.val.source ∧ q.2 ∈ N := by
    have hcurve := tsupport_comp_subset_preimage (affineCurveTest e z0 δ ψ) continuous_snd hq
    obtain ⟨τ, hτ, heq⟩ := tsupport_affineCurveTest_subset e z0 hδ.ne' hψc hfit hcurve
    have hN : q.2 ∈ N := heq ▸ hfitN τ hτ
    exact ⟨hNe hN, hN⟩
  have hsub := finiteGeodesic_isSubgeodesicFrom_of_relativeFullMassPreceq omegaM hu₀.1 hu₁.1
  have hIW := integral_core_perron_diagonal_eq_zero e N κ hκzero hW.1 hsub
    z0 hδ htime hcore G hgs
  have hIΦ := integral_core_reference_diagonal_eq_zero e N κ hκzero
    hφ.plurisubharmonic.1 hΦ.1 G hgs
  have heq := hpair.2
  rw [hIW, hIΦ, sub_self] at heq
  have hcoef : ((n : ℝ) + 1) / Real.pi ≠ 0 := div_ne_zero (by positivity) Real.pi_ne_zero
  exact ⟨hpair.1, (mul_eq_zero.mp heq).resolve_left hcoef⟩

end

end SGPT.Foundations.Analysis.Pending.SingularModelEnergyProducedGlobalCorePairing
