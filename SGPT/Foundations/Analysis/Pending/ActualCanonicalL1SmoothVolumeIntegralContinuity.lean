import SGPT.Foundations.Analysis.Pending.GlobalQuasiPshVolumeIntegrability
import SGPT.Foundations.Analysis.FirstPass.PotentialL1ConvergenceInMeasure

set_option autoImplicit false

/-! # Actual canonical local-L1 continuity of smooth-volume real integrals

Original canonical error controls the original real integral difference,
including all pole cases. Genuine original theta-PSH supplies integrability
internally for every actual smooth positive global volume. Complete
mathematical statements and proofs preceded SOURCE. No energy, model,
compactness, maximizer or prescribed MA certificate is assumed.
-/

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.ActualCanonicalL1SmoothVolumeIntegralContinuity

open FirstPass ChartwiseGlobalL1

noncomputable section

/-- The whole canonical error controls actual integrals of the real
representatives without a pole-null or finite-error certificate. -/
theorem edist_integral_toReal_le_globalL1EDistance {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {u v : X → EReal}
    (hu : Integrable (fun x => (u x).toReal) μ)
    (hv : Integrable (fun x => (v x).toReal) μ) :
    edist (∫ x, (u x).toReal ∂μ) (∫ x, (v x).toReal ∂μ) ≤ globalL1EDistance μ u v := by
  exact (edist_integral_le_lintegral_edist hu hv).trans
    (lintegral_mono fun x => edist_toReal_le_canonicalERealAbsDiff (u x) (v x))

/-- Canonical chart-local L1 convergence of original genuine potentials
internally produces smooth-volume integrability and real integral continuity
along any indexing filter, without prior finite energy of the original limit. -/
theorem integrable_and_integral_toReal_tendsto_of_manifoldL1LocallyTendsto
    {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
    {ι : Type*} {l : Filter ι} {u : ι → M → EReal} {v : M → EReal}
    (μ : Measure M) (hμ : IsSmoothPositiveVolume (n := n) μ)
    (θ : SmoothRealForm n M 2)
    (hu : ∀ i, IsThetaPshPotential θ (u i)) (hv : IsThetaPshPotential θ v)
    (hlim : ManifoldL1LocallyTendsto (n := n) u l v) :
    (∀ i, Integrable (fun x => (u i x).toReal) μ) ∧
    Integrable (fun x => (v x).toReal) μ ∧
    Tendsto (fun i => ∫ x, (u i x).toReal ∂μ) l (𝓝 (∫ x, (v x).toReal ∂μ)) := by
  have hi : ∀ i, Integrable (fun x => (u i x).toReal) μ := fun i =>
    GlobalQuasiPshVolumeIntegrability.integrable_toReal_of_genuine_thetaPsh μ hμ θ (u i) (hu i)
  have hvI := GlobalQuasiPshVolumeIntegrability.integrable_toReal_of_genuine_thetaPsh μ hμ θ v hv
  have hglobal := (manifoldL1LocallyTendsto_iff_tendsto_globalL1EDistance hμ
    (fun i => (hu i).quasiPshPotential.1.upperSemicontinuous.measurable)
    hv.quasiPshPotential.1.upperSemicontinuous.measurable).mp hlim
  have herr : Tendsto
      (fun i => edist (∫ x, (u i x).toReal ∂μ) (∫ x, (v x).toReal ∂μ)) l (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hglobal
      (fun _ => zero_le) (fun i => edist_integral_toReal_le_globalL1EDistance (hi i) hvI)
  exact ⟨hi, hvI, EMetric.tendsto_nhds.mpr fun ε hε => (tendsto_order.1 herr).2 ε hε⟩

end

end SGPT.Foundations.Analysis.Pending.ActualCanonicalL1SmoothVolumeIntegralContinuity
