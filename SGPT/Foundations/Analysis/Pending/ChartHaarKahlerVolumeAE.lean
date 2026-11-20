import SGPT.Foundations.Analysis.Pending.SmoothMixedMeasureDensity
import SGPT.Foundations.Analysis.Pending.SingularModelDarvasMonotoneLimits
import Mathlib.MeasureTheory.Constructions.Polish.Basic

set_option autoImplicit false

/-!
# Actual forward chart-Haar to global Kahler-volume AE transport

An independent consequence of the actual smooth mixed-density chart-map
formula. Absolute continuity of the actual density measure, genuine chart
measurability, and a finite actual chart-source cover produce the global
AE fact. The actual native increasing Darvas consumer then gives the global
smooth-volume limit in Xia SGPT PDF0167--0168. No inverse density lower bound,
global-volume equivalence, or arbitrary-null-set pluripolarity is assumed.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.ChartHaarKahlerVolumeAE

open FirstPass FirstPass.PositiveClasses GlobalNonPluripolar DiagonalMass IntegrationCurrent
  SmoothMixedMeasureDensity

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

/-- Actual inverse-chart density push-forward transports a measurable predicate to the chart source. -/
theorem ae_restrict_chartSource_of_ae_chartTarget (omega : KahlerBackground n M)
    (e : ComplexChart n M) {P : M → Prop} (hP : MeasurableSet {x | P x})
    (hae : ∀ᵐ z ∂(volume.restrict e.val.target), P (e.val.symm z)) :
    ∀ᵐ x ∂((kahlerVolume omega).restrict e.val.source), P x := by
  have h0 : IsThetaPshPotential omega.form.val (fun _ => (0 : EReal)) :=
    (LocalPotentials.isThetaPshPotential_zero_iff omega.form).mpr omega.isSemipositive
  have himage : e.val.symm '' e.val.target = e.val.source := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact e.val.symm.map_source hz
    · intro hx
      exact ⟨e.val x, e.val.map_source hx, e.val.left_inv hx⟩
  let ν := (volume.restrict e.val.target).withDensity (chartDensity (fun _ => omega.form) e)
  have hν : ν ≪ volume.restrict e.val.target := withDensity_absolutelyContinuous _ _
  have hmap : AEMeasurable e.val.symm ν :=
    (e.val.continuousOn_symm.aemeasurable e.val.open_target.measurableSet).mono_ac hν
  rw [← himage, kahlerVolume, diagonalPotentialMeasure,
    restrict_image_eq_map (fun _ => h0.1) e e.val.open_target.measurableSet (Subset.refl _)]
  exact (ae_map_iff hmap hP).mpr (hν.ae_le hae)

/-- A finite actual chart cover globalizes the true local forward AE transport. -/
theorem ae_kahlerVolume_of_forall_chart_ae (omega : KahlerBackground n M)
    {P : M → Prop} (hP : MeasurableSet {x | P x})
    (hae : ∀ e : ComplexChart n M, ∀ᵐ z ∂(volume.restrict e.val.target), P (e.val.symm z)) :
    ∀ᵐ x ∂kahlerVolume omega, P x := by
  classical
  let U : M → Set M := fun x => (complexChartAt (n := n) x).val.source
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U
    (fun x => (complexChartAt (n := n) x).val.open_source)
    (fun x _ => mem_iUnion.mpr ⟨x, mem_complexChartAt_source x⟩)
  have hunion : (⋃ x ∈ s, U x) = univ := Subset.antisymm (subset_univ _) hs
  have hlocal : ∀ x ∈ s, ∀ᵐ y ∂((kahlerVolume omega).restrict (U x)), P y :=
    fun x _ => ae_restrict_chartSource_of_ae_chartTarget omega (complexChartAt (n := n) x) hP
      (hae (complexChartAt (n := n) x))
  have h := (ae_restrict_biUnion_finset_iff U s P).mpr hlocal
  simpa only [hunion, Measure.restrict_univ] using h

/-- The measurable convergence predicate transports actual chart AE limits to actual global volume. -/
theorem ae_tendsto_kahlerVolume_of_forall_chart_ae (omega : KahlerBackground n M)
    {ui : ℕ → M → EReal} {u : M → EReal} (hui : ∀ i, Measurable (ui i)) (hu : Measurable u)
    (hae : ∀ e : ComplexChart n M, ∀ᵐ z ∂(volume.restrict e.val.target),
      Tendsto (fun i => ui i (e.val.symm z)) atTop (𝓝 (u (e.val.symm z)))) :
    ∀ᵐ x ∂kahlerVolume omega, Tendsto (fun i => ui i x) atTop (𝓝 (u x)) :=
  ae_kahlerVolume_of_forall_chart_ae omega (measurableSet_tendsto_fun hui hu) hae

variable [ConnectedSpace M]
  {θ : ClosedRealOneOneForm n M} {φ : M → EReal} {hφ : IsModelPotential θ φ}

open RelativePreceqClasses SingularModelDarvasMetricSpace

/-- Actual native increasing Darvas convergence produces actual global Kahler-volume AE pointwise convergence. -/
theorem ae_kahlerVolume_tendsto_of_monotone_native_tendsto (omega : KahlerBackground n M)
    (ui : ℕ → ModelFiniteEnergyPotential θ φ hφ) (u : ModelFiniteEnergyPotential θ φ hφ)
    (hm : ∀ x, Monotone fun j => (ui j).val x) :
    letI := finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
    letI : UniformSpace (ModelFiniteEnergyPotential θ φ hφ) :=
      (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace
    letI : TopologicalSpace (ModelFiniteEnergyPotential θ φ hφ) :=
      (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace.toTopologicalSpace
    Tendsto ui atTop (𝓝 u) →
      ∀ᵐ x ∂kahlerVolume omega, Tendsto (fun i => (ui i).val x) atTop (𝓝 (u.val x)) := by
  let := finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
  let : UniformSpace (ModelFiniteEnergyPotential θ φ hφ) :=
    (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace
  let : TopologicalSpace (ModelFiniteEnergyPotential θ φ hφ) :=
    (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace.toTopologicalSpace
  intro hlim
  apply ae_tendsto_kahlerVolume_of_forall_chart_ae omega
    (fun i => GlobalSlotComparison.ThetaPlurisubharmonic.measurable (ui i).property.1.plurisubharmonic.1)
    (GlobalSlotComparison.ThetaPlurisubharmonic.measurable u.property.1.plurisubharmonic.1)
  intro e
  exact SingularModelDarvasMonotoneLimits.ae_chart_tendsto_of_monotone_native_tendsto omega ui u hm e hlim

end

end SGPT.Foundations.Analysis.Pending.ChartHaarKahlerVolumeAE
