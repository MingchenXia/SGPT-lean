import SGPT.Foundations.Analysis.Pending.TraceRepresentativeConstruction
import SGPT.Foundations.Analysis.Pending.SingularNativeCommonBackground

set_option autoImplicit false

/-! # Genuine native and trace transport between target auxiliaries -/

open Set Filter
open scoped Topology Manifold ENNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.TraceTargetAuxiliaryIndependence

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  FirstPass.QuasiEquisingularApproximation TraceRepresentativeConstruction
  ThetaPshL1Topology SingularCanonicalSingularityDistance PluripolarCapacityDichotomy

noncomputable section

variable {k : ℕ} {V : Type*} [TopologicalSpace V]
  [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]

/-- Each actual native convergence is converted through the genuine
defining radial distance, whose auxiliary-dependent model parameter is a proof. -/
theorem tendsto_native_iff_auxiliary_choices
    (omega κ : KahlerBackground k V) (θ : ClosedRealOneOneForm k V)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {I : Type*} (F : Filter I) (w : I → ThetaPshL1 θ.val) (v : ThetaPshL1 θ.val) :
    Tendsto w F (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace v) ↔
    Tendsto w F (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace κ θ hbig).toUniformSpace.toTopologicalSpace v) := by
  have htransfer (a b : KahlerBackground k V)
      (hlim : Tendsto w F (@nhds (ThetaPshL1 θ.val)
        (singularityPseudoMetricSpace a θ hbig).toUniformSpace.toTopologicalSpace v)) :
      Tendsto w F (@nhds (ThetaPshL1 θ.val)
        (singularityPseudoMetricSpace b θ hbig).toUniformSpace.toTopologicalSpace v) := by
    let := singularityPseudoMetricSpace a θ hbig
    let : TopologicalSpace (ThetaPshL1 θ.val) :=
      (singularityPseudoMetricSpace a θ hbig).toUniformSpace.toTopologicalSpace
    have hd : Tendsto (fun i => (singularityDistance a θ hbig (w i).val v.val).toReal)
        F (𝓝 0) := by
      simpa only [dist_eq_singularityDistance_toReal a θ hbig] using
        (tendsto_iff_dist_tendsto_zero.mp hlim)
    let := singularityPseudoMetricSpace b θ hbig
    let : TopologicalSpace (ThetaPshL1 θ.val) :=
      (singularityPseudoMetricSpace b θ hbig).toUniformSpace.toTopologicalSpace
    apply tendsto_iff_dist_tendsto_zero.mpr
    simpa only [dist_eq_singularityDistance_toReal b θ hbig, singularityDistance] using hd
  exact ⟨htransfer omega κ, htransfer κ omega⟩

/-- Changing the actual target auxiliary keeps every approximation,
admissibility and PSH field and transports only the genuine native limit. -/
theorem isTraceRepresentativeAlong_iff_target_auxiliary_choices
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (omega : KahlerBackground n M) (omegaV κV : KahlerBackground k V)
    {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (u : M → EReal) (τ : V → EReal) :
    IsTraceRepresentativeAlong omega omegaV hι u τ ↔
      IsTraceRepresentativeAlong omega κV hι u τ := by
  constructor
  · intro h
    obtain ⟨hg, θ, ε, uSeq, happ, β, hadm, hτ, hv, hlim⟩ := h
    refine ⟨hg, θ, ε, uSeq, happ, β, hadm, hτ, hv, ?_⟩
    exact (tendsto_native_iff_auxiliary_choices omegaV κV β.form (isBigClass_kahler β)
      atTop (fun j => (⟨fun y => uSeq j (ι y), hv j⟩ : ThetaPshL1 β.form.val))
      ⟨τ, hτ⟩).mp hlim
  · intro h
    obtain ⟨hg, θ, ε, uSeq, happ, β, hadm, hτ, hv, hlim⟩ := h
    refine ⟨hg, θ, ε, uSeq, happ, β, hadm, hτ, hv, ?_⟩
    exact (tendsto_native_iff_auxiliary_choices omegaV κV β.form (isBigClass_kahler β)
      atTop (fun j => (⟨fun y => uSeq j (ι y), hv j⟩ : ThetaPshL1 β.form.val))
      ⟨τ, hτ⟩).mpr hlim

end

end SGPT.Foundations.Analysis.Pending.TraceTargetAuxiliaryIndependence
