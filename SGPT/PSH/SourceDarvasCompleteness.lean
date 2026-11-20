import SGPT.PSH.SourceDarvasMetric
import SGPT.Envelopes.SourceRelativeEnergyClosure
import SGPT.Foundations.Analysis.Pending.SingularModelDarvasMetricCompleteness
import SGPT.Foundations.Analysis.Pending.ChartHaarKahlerVolumeAE
import Mathlib.Topology.MetricSpace.Isometry

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open scoped Topology

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

/-- Actual source/native E1 equivalence is an isometry for the genuine
Darvas metrics. Every underlying original potential is unchanged. -/
def sourceDarvasIsometryEquiv (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (φ : M → EReal)
    (hφ : SourceModelPotential θ φ) :
    letI := sourceDarvasMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
    letI : UniformSpace (SourceFiniteEnergyPotential θ φ hφ) :=
      (sourceDarvasMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace
    letI : TopologicalSpace (SourceFiniteEnergyPotential θ φ hφ) :=
      (sourceDarvasMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace.toTopologicalSpace
    letI := SingularModelDarvasMetricSpace.finiteEnergyMetricSpace
      (θ := atlasClosedFormToNative θ) (φ := φ) (hφ := hφ.toNative) omega
    letI : UniformSpace (SingularModelDarvasMetricSpace.ModelFiniteEnergyPotential
        (atlasClosedFormToNative θ) φ hφ.toNative) :=
      (SingularModelDarvasMetricSpace.finiteEnergyMetricSpace
        (θ := atlasClosedFormToNative θ) (φ := φ) (hφ := hφ.toNative) omega).toUniformSpace
    letI : TopologicalSpace (SingularModelDarvasMetricSpace.ModelFiniteEnergyPotential
        (atlasClosedFormToNative θ) φ hφ.toNative) :=
      (SingularModelDarvasMetricSpace.finiteEnergyMetricSpace
        (θ := atlasClosedFormToNative θ) (φ := φ) (hφ := hφ.toNative) omega).toUniformSpace.toTopologicalSpace
    SourceFiniteEnergyPotential θ φ hφ ≃ᵢ
      SingularModelDarvasMetricSpace.ModelFiniteEnergyPotential
        (atlasClosedFormToNative θ) φ hφ.toNative := by
  letI := sourceDarvasMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
  letI : UniformSpace (SourceFiniteEnergyPotential θ φ hφ) :=
    (sourceDarvasMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace
  letI : TopologicalSpace (SourceFiniteEnergyPotential θ φ hφ) :=
    (sourceDarvasMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace.toTopologicalSpace
  letI := SingularModelDarvasMetricSpace.finiteEnergyMetricSpace
    (θ := atlasClosedFormToNative θ) (φ := φ) (hφ := hφ.toNative) omega
  letI : UniformSpace (SingularModelDarvasMetricSpace.ModelFiniteEnergyPotential
      (atlasClosedFormToNative θ) φ hφ.toNative) :=
    (SingularModelDarvasMetricSpace.finiteEnergyMetricSpace
      (θ := atlasClosedFormToNative θ) (φ := φ) (hφ := hφ.toNative) omega).toUniformSpace
  letI : TopologicalSpace (SingularModelDarvasMetricSpace.ModelFiniteEnergyPotential
      (atlasClosedFormToNative θ) φ hφ.toNative) :=
    (SingularModelDarvasMetricSpace.finiteEnergyMetricSpace
      (θ := atlasClosedFormToNative θ) (φ := φ) (hφ := hφ.toNative) omega).toUniformSpace.toTopologicalSpace
  refine { toEquiv := sourceFiniteEnergyPotentialEquivNative θ φ hφ, isometry_toFun := ?_ }
  exact Isometry.of_dist_eq fun _ _ ↦ rfl

variable {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
  {hφ : SourceModelPotential θ φ}

/-- Actual source metric convergence is precisely convergence to zero of
the literal source energy/rooftop distance, for arbitrary filters. -/
theorem sourceDarvas_metric_tendsto_iff {I : Type*} {F : Filter I}
    (omega : KahlerBackground n M) (ui : I → SourceFiniteEnergyPotential θ φ hφ)
    (u : SourceFiniteEnergyPotential θ φ hφ) :
    letI := sourceDarvasMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
    letI : UniformSpace (SourceFiniteEnergyPotential θ φ hφ) :=
      (sourceDarvasMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace
    letI : TopologicalSpace (SourceFiniteEnergyPotential θ φ hφ) :=
      (sourceDarvasMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace.toTopologicalSpace
    Tendsto ui F (𝓝 u) ↔
      Tendsto (fun i ↦ sourceDarvasDistance θ φ hφ (ui i) u) F (𝓝 0) := by
  let := sourceDarvasMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
  let : UniformSpace (SourceFiniteEnergyPotential θ φ hφ) :=
    (sourceDarvasMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace
  let : TopologicalSpace (SourceFiniteEnergyPotential θ φ hφ) :=
    (sourceDarvasMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace.toTopologicalSpace
  rw [tendsto_iff_dist_tendsto_zero]
  simp only [sourceDarvasMetricSpace_dist omega]

/-- The complete original/native distance dictionary preserves actual
metric convergence of the SAME functions, for every filter. -/
theorem sourceDarvas_tendsto_iff_native {I : Type*} {F : Filter I}
    (omega : KahlerBackground n M) (ui : I → SourceFiniteEnergyPotential θ φ hφ)
    (u : SourceFiniteEnergyPotential θ φ hφ) :
    letI := SingularModelDarvasMetricSpace.finiteEnergyMetricSpace
      (θ := atlasClosedFormToNative θ) (φ := φ) (hφ := hφ.toNative) omega
    letI : UniformSpace (SingularModelDarvasMetricSpace.ModelFiniteEnergyPotential
        (atlasClosedFormToNative θ) φ hφ.toNative) :=
      (SingularModelDarvasMetricSpace.finiteEnergyMetricSpace
        (θ := atlasClosedFormToNative θ) (φ := φ) (hφ := hφ.toNative) omega).toUniformSpace
    letI : TopologicalSpace (SingularModelDarvasMetricSpace.ModelFiniteEnergyPotential
        (atlasClosedFormToNative θ) φ hφ.toNative) :=
      (SingularModelDarvasMetricSpace.finiteEnergyMetricSpace
        (θ := atlasClosedFormToNative θ) (φ := φ) (hφ := hφ.toNative) omega).toUniformSpace.toTopologicalSpace
    Tendsto (fun i ↦ sourceDarvasDistance θ φ hφ (ui i) u) F (𝓝 0) ↔
      Tendsto (fun i ↦ sourceFiniteEnergyPotentialEquivNative θ φ hφ (ui i)) F
        (𝓝 (sourceFiniteEnergyPotentialEquivNative θ φ hφ u)) := by
  let := SingularModelDarvasMetricSpace.finiteEnergyMetricSpace
    (θ := atlasClosedFormToNative θ) (φ := φ) (hφ := hφ.toNative) omega
  let : UniformSpace (SingularModelDarvasMetricSpace.ModelFiniteEnergyPotential
      (atlasClosedFormToNative θ) φ hφ.toNative) :=
    (SingularModelDarvasMetricSpace.finiteEnergyMetricSpace
      (θ := atlasClosedFormToNative θ) (φ := φ) (hφ := hφ.toNative) omega).toUniformSpace
  let : TopologicalSpace (SingularModelDarvasMetricSpace.ModelFiniteEnergyPotential
      (atlasClosedFormToNative θ) φ hφ.toNative) :=
    (SingularModelDarvasMetricSpace.finiteEnergyMetricSpace
      (θ := atlasClosedFormToNative θ) (φ := φ) (hφ := hφ.toNative) omega).toUniformSpace.toTopologicalSpace
  conv_rhs => rw [tendsto_iff_dist_tendsto_zero]
  change Tendsto (fun i ↦ sourceDarvasDistance θ φ hφ (ui i) u) F (𝓝 0) ↔
    Tendsto (fun i ↦ RelativeDarvasDistance.relativeD1 (atlasClosedFormToNative θ) φ
      hφ.toNative (ui i).val u.val) F (𝓝 0)
  simp only [sourceDarvasDistance_eq_native omega]

/-- WHOLE original thm:d1_complete on the actual metric/uniformity of
the ENTIRE original preceq E1 class. Actual native monotone-Cauchy producers
manufacture all limits; no bounded reference or output certificate. -/
theorem sourceDarvas_completeSpace (omega : KahlerBackground n M) :
    letI := sourceDarvasMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
    letI : UniformSpace (SourceFiniteEnergyPotential θ φ hφ) :=
      (sourceDarvasMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace
    letI : TopologicalSpace (SourceFiniteEnergyPotential θ φ hφ) :=
      (sourceDarvasMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace.toTopologicalSpace
    CompleteSpace (SourceFiniteEnergyPotential θ φ hφ) := by
  let := sourceDarvasMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
  let : UniformSpace (SourceFiniteEnergyPotential θ φ hφ) :=
    (sourceDarvasMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace
  let : TopologicalSpace (SourceFiniteEnergyPotential θ φ hφ) :=
    (sourceDarvasMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace.toTopologicalSpace
  let := SingularModelDarvasMetricSpace.finiteEnergyMetricSpace
    (θ := atlasClosedFormToNative θ) (φ := φ) (hφ := hφ.toNative) omega
  let : UniformSpace (SingularModelDarvasMetricSpace.ModelFiniteEnergyPotential
      (atlasClosedFormToNative θ) φ hφ.toNative) :=
    (SingularModelDarvasMetricSpace.finiteEnergyMetricSpace
      (θ := atlasClosedFormToNative θ) (φ := φ) (hφ := hφ.toNative) omega).toUniformSpace
  let : TopologicalSpace (SingularModelDarvasMetricSpace.ModelFiniteEnergyPotential
      (atlasClosedFormToNative θ) φ hφ.toNative) :=
    (SingularModelDarvasMetricSpace.finiteEnergyMetricSpace
      (θ := atlasClosedFormToNative θ) (φ := φ) (hφ := hφ.toNative) omega).toUniformSpace.toTopologicalSpace
  let : CompleteSpace (SingularModelDarvasMetricSpace.ModelFiniteEnergyPotential
      (atlasClosedFormToNative θ) φ hφ.toNative) :=
    SingularModelDarvasMetricCompleteness.completeSpace_finiteEnergyMetricSpace omega
  exact (sourceDarvasIsometryEquiv omega θ φ hφ).completeSpace

/-- A decreasing source Darvas sequence has the LITERAL original function
infimum as its given limit, including every original pole. -/
theorem sourceDarvas_antitone_infimum (omega : KahlerBackground n M)
    (ui : ℕ → SourceFiniteEnergyPotential θ φ hφ) (u : SourceFiniteEnergyPotential θ φ hφ)
    (hanti : ∀ x, Antitone fun i ↦ (ui i).val x)
    (hd : Tendsto (fun i ↦ sourceDarvasDistance θ φ hφ (ui i) u) atTop (𝓝 0)) :
    (⨅ i, (ui i).val) = u.val := by
  have hn := (sourceDarvas_tendsto_iff_native omega ui u).mp hd
  exact SingularModelDarvasMonotoneLimits.iInf_eq_of_antitone_tendsto omega
    (fun i ↦ sourceFiniteEnergyPotentialEquivNative θ φ hφ (ui i))
    (sourceFiniteEnergyPotentialEquivNative θ φ hφ u) hanti hn

/-- An increasing source Darvas sequence has its actual original whole
neighborhood-regularized supremum as its given identical limit. -/
theorem sourceDarvas_monotone_uscSupremum (omega : KahlerBackground n M)
    (ui : ℕ → SourceFiniteEnergyPotential θ φ hφ) (u : SourceFiniteEnergyPotential θ φ hφ)
    (hm : ∀ x, Monotone fun i ↦ (ui i).val x)
    (hd : Tendsto (fun i ↦ sourceDarvasDistance θ φ hφ (ui i) u) atTop (𝓝 0)) :
    SGPT.PSH.uscSup (fun i ↦ (ui i).val) = u.val := by
  rw [sourceUscSup_eq_native]
  have hn := (sourceDarvas_tendsto_iff_native omega ui u).mp hd
  exact SingularModelDarvasMonotoneLimits.uscRegularization_iSup_eq_of_monotone_tendsto omega
    (fun i ↦ sourceFiniteEnergyPotentialEquivNative θ φ hφ (ui i))
    (sourceFiniteEnergyPotentialEquivNative θ φ hφ u) hm hn

/-- The decreasing case of the original printed monotone-limit consequence
actually converges at EVERY point in EReal, retaining infinite poles. -/
theorem sourceDarvas_antitone_pointwise_limit (omega : KahlerBackground n M)
    (ui : ℕ → SourceFiniteEnergyPotential θ φ hφ) (u : SourceFiniteEnergyPotential θ φ hφ)
    (hanti : ∀ x, Antitone fun i ↦ (ui i).val x)
    (hd : Tendsto (fun i ↦ sourceDarvasDistance θ φ hφ (ui i) u) atTop (𝓝 0)) :
    ∀ x, Tendsto (fun i ↦ (ui i).val x) atTop (𝓝 (u.val x)) := by
  have hn := (sourceDarvas_tendsto_iff_native omega ui u).mp hd
  exact SingularModelDarvasMonotoneLimits.pointwise_tendsto_of_antitone_native_tendsto omega
    (fun i ↦ sourceFiniteEnergyPotentialEquivNative θ φ hφ (ui i))
    (sourceFiniteEnergyPotentialEquivNative θ φ hφ u) hanti hn

/-- WHOLE original unlabelled line972 consequence for BOTH monotone cases,
with the actual original GLOBAL Kähler-volume measure. The native genuine
chart-density/finite-cover theorem supplies the global AE transport. -/
theorem sourceDarvas_monotone_ae_limit (omega : KahlerBackground n M)
    (ui : ℕ → SourceFiniteEnergyPotential θ φ hφ) (u : SourceFiniteEnergyPotential θ φ hφ)
    (hm : (∀ x, Monotone fun i ↦ (ui i).val x) ∨ (∀ x, Antitone fun i ↦ (ui i).val x))
    (hd : Tendsto (fun i ↦ sourceDarvasDistance θ φ hφ (ui i) u) atTop (𝓝 0)) :
    ∀ᵐ x ∂sourceKahlerVolume omega,
      Tendsto (fun i ↦ (ui i).val x) atTop (𝓝 (u.val x)) := by
  rw [sourceKahlerVolume_eq_native]
  rcases hm with hm | hanti
  · have hn := (sourceDarvas_tendsto_iff_native omega ui u).mp hd
    exact ChartHaarKahlerVolumeAE.ae_kahlerVolume_tendsto_of_monotone_native_tendsto omega
      (fun i ↦ sourceFiniteEnergyPotentialEquivNative θ φ hφ (ui i))
      (sourceFiniteEnergyPotentialEquivNative θ φ hφ u) hm hn
  · exact Eventually.of_forall (sourceDarvas_antitone_pointwise_limit omega ui u hanti hd)

end SGPT.PSH.VariableComplexAtlas
