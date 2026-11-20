import SGPT.Foundations.Analysis.Pending.SingularModelDarvasDecreasingCauchyLimit
import SGPT.Foundations.Analysis.Pending.SingularModelDarvasIncreasingCauchyLimit
import SGPT.Foundations.Analysis.Pending.IncreasingThetaPshChartL1

set_option autoImplicit false

/-!
# Actual potential limits of native monotone Darvas sequences

Xia SGPT PDF0167--0168: actual decreasing infima and increasing regularized
suprema are identified with given native metric limits by actual monotone
Cauchy producers and uniqueness. The increasing almost-everywhere consumer
explicitly uses chart Haar volume, via genuine normalization and the actual
chart regularization-deficit producer. No global-volume null-set transport
or pointwise convergence certificate is assumed.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SingularModelDarvasMonotoneLimits

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses SingularModelDarvasMetricSpace

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]
  {θ : ClosedRealOneOneForm n M} {φ : M → EReal} {hφ : IsModelPotential θ φ}

/-- Actual function infimum equals the native metric limit of a decreasing sequence. -/
theorem iInf_eq_of_antitone_tendsto (omega : KahlerBackground n M)
    (ui : ℕ → ModelFiniteEnergyPotential θ φ hφ) (u : ModelFiniteEnergyPotential θ φ hφ)
    (hanti : ∀ x, Antitone fun j => (ui j).val x) :
    letI := finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
    letI : UniformSpace (ModelFiniteEnergyPotential θ φ hφ) :=
      (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace
    letI : TopologicalSpace (ModelFiniteEnergyPotential θ φ hφ) :=
      (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace.toTopologicalSpace
    Tendsto ui atTop (𝓝 u) → (⨅ j, (ui j).val) = u.val := by
  let := finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
  let : UniformSpace (ModelFiniteEnergyPotential θ φ hφ) :=
    (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace
  let : TopologicalSpace (ModelFiniteEnergyPotential θ φ hφ) :=
    (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace.toTopologicalSpace
  intro hlim
  obtain ⟨hU, hUlim⟩ := SingularModelDarvasDecreasingCauchyLimit.tendsto_iInf_of_antitone_cauchySeq
    omega ui hanti hlim.cauchySeq
  have heq : (⟨⨅ j, (ui j).val, hU⟩ : ModelFiniteEnergyPotential θ φ hφ) = u :=
    tendsto_nhds_unique hUlim hlim
  exact congrArg Subtype.val heq

/-- Actual regularized function supremum equals the native metric limit of an increasing sequence. -/
theorem uscRegularization_iSup_eq_of_monotone_tendsto (omega : KahlerBackground n M)
    (ui : ℕ → ModelFiniteEnergyPotential θ φ hφ) (u : ModelFiniteEnergyPotential θ φ hφ)
    (hm : ∀ x, Monotone fun j => (ui j).val x) :
    letI := finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
    letI : UniformSpace (ModelFiniteEnergyPotential θ φ hφ) :=
      (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace
    letI : TopologicalSpace (ModelFiniteEnergyPotential θ φ hφ) :=
      (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace.toTopologicalSpace
    Tendsto ui atTop (𝓝 u) → uscRegularization (⨆ j, (ui j).val) = u.val := by
  let := finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
  let : UniformSpace (ModelFiniteEnergyPotential θ φ hφ) :=
    (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace
  let : TopologicalSpace (ModelFiniteEnergyPotential θ φ hφ) :=
    (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace.toTopologicalSpace
  intro hlim
  obtain ⟨hU, hUlim⟩ := SingularModelDarvasIncreasingCauchyLimit.tendsto_uscRegularization_iSup_of_monotone_cauchySeq
    omega ui hm hlim.cauchySeq
  have heq : (⟨uscRegularization (⨆ j, (ui j).val), hU⟩ : ModelFiniteEnergyPotential θ φ hφ) = u :=
    tendsto_nhds_unique hUlim hlim
  exact congrArg Subtype.val heq

/-- Native decreasing metric convergence produces actual pointwise convergence, including poles. -/
theorem pointwise_tendsto_of_antitone_native_tendsto (omega : KahlerBackground n M)
    (ui : ℕ → ModelFiniteEnergyPotential θ φ hφ) (u : ModelFiniteEnergyPotential θ φ hφ)
    (hanti : ∀ x, Antitone fun j => (ui j).val x) :
    letI := finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
    letI : UniformSpace (ModelFiniteEnergyPotential θ φ hφ) :=
      (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace
    letI : TopologicalSpace (ModelFiniteEnergyPotential θ φ hφ) :=
      (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace.toTopologicalSpace
    Tendsto ui atTop (𝓝 u) → ∀ x, Tendsto (fun j => (ui j).val x) atTop (𝓝 (u.val x)) := by
  let := finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
  let : UniformSpace (ModelFiniteEnergyPotential θ φ hφ) :=
    (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace
  let : TopologicalSpace (ModelFiniteEnergyPotential θ φ hφ) :=
    (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace.toTopologicalSpace
  intro hlim x
  rw [← iInf_eq_of_antitone_tendsto omega ui u hanti hlim, iInf_apply]
  exact tendsto_atTop_iInf (hanti x)

/-- Native increasing convergence produces chart-Haar AE pointwise convergence, with exact measure scope. -/
theorem ae_chart_tendsto_of_monotone_native_tendsto (omega : KahlerBackground n M)
    (ui : ℕ → ModelFiniteEnergyPotential θ φ hφ) (u : ModelFiniteEnergyPotential θ φ hφ)
    (hm : ∀ x, Monotone fun j => (ui j).val x) (e : ComplexChart n M) :
    letI := finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
    letI : UniformSpace (ModelFiniteEnergyPotential θ φ hφ) :=
      (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace
    letI : TopologicalSpace (ModelFiniteEnergyPotential θ φ hφ) :=
      (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace.toTopologicalSpace
    Tendsto ui atTop (𝓝 u) → ∀ᵐ z ∂(volume.restrict e.val.target),
      Tendsto (fun j => chartFunction (ui j).val e z) atTop (𝓝 (chartFunction u.val e z)) := by
  let := finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
  let : UniformSpace (ModelFiniteEnergyPotential θ φ hφ) :=
    (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace
  let : TopologicalSpace (ModelFiniteEnergyPotential θ φ hφ) :=
    (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace.toTopologicalSpace
  intro hlim
  have hreg := uscRegularization_iSup_eq_of_monotone_tendsto omega ui u hm hlim
  obtain ⟨R, _, hR⟩ := SingularModelDarvasIncreasingCauchyLimit.exists_pos_bound_relativeD1_of_cauchySeq
    omega ui hlim.cauchySeq
  obtain ⟨C, hC⟩ := SingularModelDarvasSupremumControl.exists_uniform_upper_bound_of_relativeD1_le
    omega (fun i => (ui i).property) hR
  let g : ℕ → M → EReal := fun j x => (ui j).val x + ((-C : ℝ) : EReal)
  have hg : ∀ j, IsThetaPshPotential θ.val (g j) :=
    fun j => (ui j).property.1.plurisubharmonic.add_const (-C)
  have hg0 : ∀ j, g j ≤ 0 := by
    intro j x
    calc
      _ ≤ (C : EReal) + ((-C : ℝ) : EReal) := add_le_add (hC j x) le_rfl
      _ = 0 := by rw [← EReal.coe_add]; simp
  have hgm : Monotone g := fun i j hij x => add_le_add (hm x hij) le_rfl
  have hsup : (⨆ j, g j) = fun x => (⨆ j, (ui j).val) x + ((-C : ℝ) : EReal) := by
    funext x
    simp only [g, iSup_apply]
    exact (NegligibleSetNotCharged.iSup_add_coe (fun j => (ui j).val x) (-C)).symm
  have hregg : uscRegularization (⨆ j, g j) = fun x => u.val x + ((-C : ℝ) : EReal) := by
    rw [hsup, uscRegularization_add_coe_const, hreg]
  have hae := IncreasingThetaPshChartL1.ae_chartFunction_iSup_eq hg hg0 hgm hregg e
  filter_upwards [hae] with z hz
  change (⨆ j, (ui j).val (e.val.symm z) + ((-C : ℝ) : EReal)) =
    u.val (e.val.symm z) + ((-C : ℝ) : EReal) at hz
  rw [← NegligibleSetNotCharged.iSup_add_coe (fun j => (ui j).val (e.val.symm z)) (-C)] at hz
  have heq := IncreasingThetaPshChartL1.eReal_add_coe_right_cancel hz
  change Tendsto (fun j => (ui j).val (e.val.symm z)) atTop (𝓝 (u.val (e.val.symm z)))
  rw [← heq]
  exact tendsto_atTop_iSup (hm (e.val.symm z))

end

end SGPT.Foundations.Analysis.Pending.SingularModelDarvasMonotoneLimits
