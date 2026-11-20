import SGPT.Foundations.Analysis.Pending.SingularModelEnergyProducedGlobalCorePairing
import SGPT.Foundations.Analysis.Pending.SingularPerronCompactification
import SGPT.Foundations.Analysis.Pending.AffineTimeTestScaling

set_option autoImplicit false

/-!
# Actual Perron defining energy has zero weak time Laplacian

The true fitted affine chart identifies the actual defining energy on the
test support. Zero Laplacian elsewhere and actual planar Haar scaling
transport both the integral and its integrability. The genuine compact
Perron extension and fully produced signed core pairing then yield the
weak equation in the original time variable, without a current or energy
identity input.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.SingularPerronWeakEnergyLaplacian

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance RelativePreceqClasses
  CompactAffineCurveCharts CompactAffineCurveRegions AffineCurveCoreTests
  SingularModelEnergyCoreChartData SingularModelEnergyFibrePairing
  BedfordTaylorTimeSlot BedfordTaylorStripIBP AffineTimeTestScaling
  FlatComplexTorus SingularPerronCompactification

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]
  {θ : ClosedRealOneOneForm n M} {φ : M → EReal} {hφ : IsModelPotential θ φ}

/-- Actual chart inverses and support fit identify the defining energy in
the two time coordinates. Haar area cancellation transports the signed
pairing and its integrability, without either conclusion as an input. -/
theorem affine_model_energy_pairing
    {T : Type*} [TopologicalSpace T] [ChartedSpace (ComplexModel 1) T]
    (U : ℝ → M → EReal) (e : ComplexChart 1 T) (N : Opens T)
    (z0 : ComplexModel 1) {δ : ℝ} (hδ : 0 < δ)
    {ψ : ℂ → ℝ} (hψ : ContDiff ℝ 2 ψ)
    (hfit : ∀ τ ∈ tsupport ψ, z0 + δ • curveModelEquiv.symm τ ∈ e.val.target)
    (hfitN : ∀ τ ∈ tsupport ψ, e.val.symm (z0 + δ • curveModelEquiv.symm τ) ∈ N) :
    let time := fun y : T => curveModelEquiv (δ⁻¹ • (e.val y - z0))
    let R := modelEnergyCurve θ φ hφ
      (fun σ => U (time (e.val.symm (curveModelEquiv.symm σ))).re) (coreTimeDomain e N)
    (Integrable (fun σ => timeLaplacian (rawTimeTest z0 δ ψ) σ * R σ) ↔
      Integrable (fun τ => timeLaplacian ψ τ * (energy θ φ hφ (U τ.re)).toReal)) ∧
    (∫ σ : ℂ, timeLaplacian (rawTimeTest z0 δ ψ) σ * R σ) =
      ∫ τ : ℂ, timeLaplacian ψ τ * (energy θ φ hφ (U τ.re)).toReal := by
  classical
  intro time R
  let F : ℂ → ℂ := fun τ => curveModelEquiv z0 + δ • τ
  have hmodel (τ : ℂ) : curveModelEquiv.symm (F τ) = z0 + δ • curveModelEquiv.symm τ := by
    dsimp only [F]
    rw [map_add, map_real_smul curveModelEquiv.symm curveModelEquiv.symm.continuous,
      ContinuousLinearEquiv.symm_apply_apply]
  have hE (τ : ℂ) (hτ : τ ∈ tsupport ψ) :
      R (F τ) = (energy θ φ hφ (U τ.re)).toReal := by
    have hS : F τ ∈ (coreTimeDomain e N : Set ℂ) := by
      change curveModelEquiv.symm (F τ) ∈ e.val.target ∧
        e.val.symm (curveModelEquiv.symm (F τ)) ∈ N
      rw [hmodel]
      exact ⟨hfit τ hτ, hfitN τ hτ⟩
    have htime : time (e.val.symm (curveModelEquiv.symm (F τ))) = τ := by
      dsimp only [time]
      rw [hmodel, e.val.right_inv (hfit τ hτ)]
      exact model_affine_left_inverse z0 hδ.ne' τ
    change modelEnergyCurve θ φ hφ
      (fun σ => U (time (e.val.symm (curveModelEquiv.symm σ))).re) (coreTimeDomain e N) (F τ) = _
    rw [modelEnergyCurve, if_pos hS, htime]
  have heq : (fun σ => timeLaplacian (rawTimeTest z0 δ ψ) σ * R σ) =
      (fun σ => timeLaplacian (rawTimeTest z0 δ ψ) σ *
        (energy θ φ hφ (U (δ⁻¹ • (σ - curveModelEquiv z0)).re)).toReal) := by
    funext σ
    by_cases hτ : δ⁻¹ • (σ - curveModelEquiv z0) ∈ tsupport ψ
    · have hF : F (δ⁻¹ • (σ - curveModelEquiv z0)) = σ := by
        dsimp only [F]
        rw [smul_inv_smul₀ hδ.ne']
        abel
      have h := hE (δ⁻¹ • (σ - curveModelEquiv z0)) hτ
      rw [hF] at h
      rw [h]
    · have hlap : timeLaplacian (rawTimeTest z0 δ ψ) σ = 0 := by
        change timeLaplacian (fun q => ψ (δ⁻¹ • (q - curveModelEquiv z0))) σ = 0
        rw [timeLaplacian_comp_inverse_affine hψ,
          timeLaplacian_eq_zero_of_notMem_tsupport hτ, mul_zero]
      rw [hlap, zero_mul, zero_mul]
  rw [heq]
  exact timeLaplacian_affine_pairing hψ
    (fun τ => (energy θ φ hφ (U τ.re)).toReal) hδ (curveModelEquiv z0)

variable [BorelSpace M] [ConnectedSpace M]

/-- Genuine finite-energy, finite-type endpoints internally produce the
actual compact host, all core test geometry, signed pairing and Haar
transport; the resulting original-time weak equation has no target
integrability, current, energy identity or affinity premise. -/
theorem integrable_and_integral_energy_timeLaplacian_eq_zero
    (omega : KahlerBackground n M) {u₀ u₁ : M → EReal}
    (hu₀ : RelativeFiniteEnergyPreceq θ φ u₀ hφ) (hu₁ : RelativeFiniteEnergyPreceq θ φ u₁ hφ)
    (hEInf₀ : RelativeEInfinity θ φ u₀) (hEInf₁ : RelativeEInfinity θ φ u₁)
    {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : IsCompact (tsupport ψ))
    (hψS : tsupport ψ ⊆ complexTimeStrip) :
    Integrable (fun τ => timeLaplacian ψ τ *
      (energy θ φ hφ (finiteGeodesic θ.val u₀ u₁ τ.re)).toReal) ∧
    (∫ τ : ℂ, timeLaplacian ψ τ *
      (energy θ φ hφ (finiteGeodesic θ.val u₀ u₁ τ.re)).toReal) = 0 := by
  let : MeasurableSpace (Torus 1) := borel _
  let : BorelSpace (Torus 1) := ⟨rfl⟩
  obtain ⟨e, z0, δ, C, κ, W, N, -, hδ, -, hfit, -, hNo, hKN, hNe,
    htime, -, hΦ, hW, hsame, hκzero, hcore, -⟩ :=
    exists_singular_perron_compactification θ (flatKahlerBackground 1) (0 : Torus 1)
      hφ.plurisubharmonic hEInf₀ hEInf₁ hψc hψS
  let No : Opens (Torus 1) := ⟨N, hNo⟩
  have hfitN (τ : ℂ) (hτ : τ ∈ tsupport ψ) :
      e.val.symm (z0 + δ • curveModelEquiv.symm τ) ∈ No := hKN ⟨τ, hτ, rfl⟩
  have hraw := SingularModelEnergyProducedGlobalCorePairing.integrable_and_core_perron_energy_pairing_eq_zero
    omega hu₀ hu₁ e No hNe κ (hκzero e) hW hΦ hsame z0 hδ htime hcore hψ hψc hfit hfitN
  have htrans := affine_model_energy_pairing (hφ := hφ)
    (finiteGeodesic θ.val u₀ u₁) e No z0 hδ
    (hψ.of_le (WithTop.coe_le_coe.mpr le_top)) hfit hfitN
  exact ⟨htrans.1.mp hraw.1, htrans.2.symm.trans hraw.2⟩

end

end SGPT.Foundations.Analysis.Pending.SingularPerronWeakEnergyLaplacian
