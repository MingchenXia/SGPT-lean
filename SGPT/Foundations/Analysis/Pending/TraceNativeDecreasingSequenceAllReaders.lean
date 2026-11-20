import SGPT.Foundations.Analysis.Pending.TraceCompatibleNativeDecreasingSequence
import SGPT.Foundations.Analysis.Pending.TraceRepresentativeAllChoices
import SGPT.Foundations.Analysis.Pending.SingularNativeCommonBackground

set_option autoImplicit false

/-! # Every original full trace reader of a decreasing native sequence -/

open Set Filter Metric
open scoped Topology Manifold ENNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.TraceNativeDecreasingSequenceAllReaders

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  FirstPass.TraceBackground TraceRepresentativeConstruction ThetaPshL1Topology
  SingularCanonicalSingularityDistance SingularCanonicalDistanceZeroPEquivalence
  PluripolarCapacityDichotomy

noncomputable section

variable {n k : ℕ} {M V : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M] [TopologicalSpace V] [MeasurableSpace V]
  [BorelSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [CompactSpace V] [ConnectedSpace V]

/-- Every literal original full reader, with arbitrary varying witness
auxiliaries, converges in its originally given genuine big target background. -/
theorem tendsto_native_trace_readers_of_antitone
    (omega : KahlerBackground n M) (omegaV : KahlerBackground k V)
    (θ : ClosedRealOneOneForm n M) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (ui : ℕ → ThetaPshL1 θ.val) (u : ThetaPshL1 θ.val)
    (hanti : ∀ x, Antitone fun j => (ui j).val x)
    (hlim : Tendsto ui atTop (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace u))
    {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (η : ClosedRealOneOneForm k V) (hη : IsBigClass (RealBottChern.ofRepresentative η))
    (τj : ℕ → ThetaPshL1 η.val) (τ : ThetaPshL1 η.val)
    {omegaj : ℕ → KahlerBackground n M} {omegaVj : ℕ → KahlerBackground k V}
    {omega₀ : KahlerBackground n M} {omegaV₀ : KahlerBackground k V}
    (hTj : ∀ j, IsTraceRepresentativeAlong (omegaj j) (omegaVj j) hι (ui j).val (τj j).val)
    (hT : IsTraceRepresentativeAlong omega₀ omegaV₀ hι u.val τ.val) :
    Tendsto τj atTop (@nhds (ThetaPshL1 η.val)
      (singularityPseudoMetricSpace omegaV η hη).toUniformSpace.toTopologicalSpace τ) := by
  classical
  obtain ⟨β, Sj, S, hSj, hS, hSlim⟩ :=
    TraceCompatibleNativeDecreasingSequence.exists_native_trace_readers_of_antitone
      omega omegaV θ hbig ui u hanti hlim hι hT.1
  let B : Bool → ClosedRealOneOneForm k V := fun b => if b then η else β.form
  obtain ⟨C, hC, hdom⟩ := KahlerDomination.exists_pos_forall_isSemipositive_add_smul
    omegaV (fun b : Bool => -(B b))
  let γ : KahlerBackground k V := KahlerBackground.smul hC omegaV
  have hγof (b : Bool) {p : V → EReal} (hp : IsThetaPshPotential (B b).val p) :
      IsThetaPshPotential γ.form.val p := by
    have hform : B b + (-B b + C • omegaV.form) = γ.form := by
      dsimp only [γ, KahlerBackground.smul_form]
      module
    simpa only [hform] using
      LocalPotentials.isThetaPshPotential_add_of_semipositive hp (hdom b)
  have hSγ (j : ℕ) : IsThetaPshPotential γ.form.val (Sj j).val := hγof false (Sj j).property
  have hS₀γ : IsThetaPshPotential γ.form.val S.val := hγof false S.property
  have hτγ (j : ℕ) : IsThetaPshPotential γ.form.val (τj j).val := hγof true (τj j).property
  have hτ₀γ : IsThetaPshPotential γ.form.val τ.val := hγof true τ.property
  let A : ℕ → ThetaPshL1 γ.form.val := fun j => ⟨(Sj j).val, hSγ j⟩
  let a : ThetaPshL1 γ.form.val := ⟨S.val, hS₀γ⟩
  let W : ℕ → ThetaPshL1 γ.form.val := fun j => ⟨(τj j).val, hτγ j⟩
  let w : ThetaPshL1 γ.form.val := ⟨τ.val, hτ₀γ⟩
  have hA : Tendsto A atTop (@nhds (ThetaPshL1 γ.form.val)
      (singularityPseudoMetricSpace omegaV γ.form
        (isBigClass_kahler γ)).toUniformSpace.toTopologicalSpace a) :=
    (SingularNativeCommonBackground.tendsto_native_iff_common_backgrounds omegaV
      β.form γ.form (isBigClass_kahler β) (isBigClass_kahler γ) atTop
      (fun j => (Sj j).property) S.property hSγ hS₀γ).mp hSlim
  let := singularityPseudoMetricSpace omegaV γ.form (isBigClass_kahler γ)
  let : TopologicalSpace (ThetaPshL1 γ.form.val) :=
    (singularityPseudoMetricSpace omegaV γ.form
      (isBigClass_kahler γ)).toUniformSpace.toTopologicalSpace
  have hzero (j : ℕ) : dist (W j) (A j) = 0 := by
    have heq := TraceRepresentativeAllChoices.sourcePEquivalent_of_isTraceRepresentativeAlong
      (omegaVj j) omegaV hι (hTj j) (hSj j)
    have he := (singularityDistance_eq_zero_iff_sourcePEquivalent omegaV γ.form
      (isBigClass_kahler γ) (W j).property (A j).property).mpr heq
    rw [dist_eq_singularityDistance_toReal omegaV γ.form
      (isBigClass_kahler γ), he, EReal.toReal_zero]
  have hzero₀ : dist a w = 0 := by
    have heq := TraceRepresentativeAllChoices.sourcePEquivalent_of_isTraceRepresentativeAlong
      omegaV omegaV₀ hι hS hT
    have he := (singularityDistance_eq_zero_iff_sourcePEquivalent omegaV γ.form
      (isBigClass_kahler γ) a.property w.property).mpr heq
    rw [dist_eq_singularityDistance_toReal omegaV γ.form
      (isBigClass_kahler γ), he, EReal.toReal_zero]
  have hW : Tendsto W atTop (𝓝 w) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun _ => dist_nonneg) (fun j => ?_)
      (tendsto_iff_dist_tendsto_zero.mp hA)
    have h1 := dist_triangle (W j) (A j) w
    have h2 := dist_triangle (A j) a w
    have h1' : dist (W j) w ≤ dist (A j) w := by simpa only [hzero, zero_add] using h1
    have h2' : dist (A j) w ≤ dist (A j) a := by simpa only [hzero₀, add_zero] using h2
    exact h1'.trans h2'
  exact (SingularNativeCommonBackground.tendsto_native_iff_common_backgrounds omegaV
    γ.form η (isBigClass_kahler γ) hη atTop hτγ hτ₀γ
    (fun j => (τj j).property) τ.property).mp hW

end
end SGPT.Foundations.Analysis.Pending.TraceNativeDecreasingSequenceAllReaders
