import SGPT.Foundations.Analysis.Pending.DemaillyCommonGeometryFixedBackgroundRows
import SGPT.Foundations.Analysis.Pending.DemaillyCommonGeometryDiagonalOrder
import SGPT.Foundations.Analysis.Pending.DemaillyCommonGeometryUniformMultiplierLevel
import SGPT.Foundations.Analysis.Pending.GenuineMultiplierIdealChartInclusion
import SGPT.Foundations.Analysis.Pending.NativeStrictGapMultiplierInclusion

set_option autoImplicit false

/-! # Full actual Demailly diagonals from decreasing native inputs -/

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.DemaillyCommonGeometryDiagonalFullQea
open FirstPass FirstPass.PositiveClasses FirstPass.HolomorphicIdealSheaves
  FirstPass.QuasiEquisingularApproximation FirstPass.NonKahlerLocus ThetaPshL1Topology
  SingularCanonicalSingularityDistance QuantitativeRegularizationFixedCover
  DemaillyCommonGeometryFixedBackgroundRows DemaillyCommonGeometryDiagonalOrder
  DemaillyCommonGeometryUniformMultiplierLevel GenuineMultiplierIdealChartInclusion
  NativeStrictGapMultiplierInclusion

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- The common geometry is produced internally. Every increasing cofinal dyadic
diagonal is a full approximation, with its genuine half-margin retained. -/
theorem exists_common_geometry_full_diagonal
    (hn : 0 < n) (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (ui : ℕ → ThetaPshL1 θ.val) (u : ThetaPshL1 θ.val)
    (hanti : ∀ x, Antitone fun j => (ui j).val x)
    (hinf : ∀ x, (⨅ j, (ui j).val x) = u.val x)
    (hlim : Tendsto ui atTop (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace u)) :
    ∃ (F : FixedChartCover n M) (ρ : F.t → ComplexModel n → ℝ) (D : ℝ) (K : ℕ),
      0 ≤ D ∧
      (∀ j, IsSmoothLocalPotential θ.val (F.chart j)
        (ball (F.center j) (F.potentialRadius j)) (ρ j)) ∧
      (∀ v : M → EReal, IsThetaPshPotential θ.val v →
        IsQuasiEquisingularApproximation omega (θ + omega.form) v (fun _ => 0)
          (fun j => DemaillyApproximationSequence.seq F ρ v (2 * (D + 1 / 4)) (j + K))) ∧
      ∀ k : ℕ → ℕ, Monotone k → Tendsto k atTop atTop →
        IsQuasiEquisingularApproximation omega (θ + omega.form) u.val (fun _ => 0)
          (fun j => DemaillyApproximationSequence.seq F ρ (ui j).val
            (2 * (D + 1 / 4)) (k j + K)) ∧
        ∀ j, IsThetaPshPotential (θ + (1 / 2 : ℝ) • omega.form).val
          (DemaillyApproximationSequence.seq F ρ (ui j).val (2 * (D + 1 / 4)) (k j + K)) := by
  obtain ⟨F, ρ, D, K, hD, hρ, hall⟩ :=
    exists_common_fixed_background_full_rows hn omega θ
  have hdouble := fun v hv => (hall v hv).1
  have hrows := fun v hv => (hall v hv).2.1
  refine ⟨F, ρ, D, K, hD, hρ, hrows, ?_⟩
  intro k hk hktop
  have hk' : Monotone fun j => k j + K :=
    fun _ _ hij => Nat.add_le_add_right (hk hij) K
  have hk'top : Tendsto (fun j => k j + K) atTop atTop :=
    (tendsto_add_atTop_nat K).comp hktop
  have hdiaganti (x : M) : Antitone fun j =>
      DemaillyApproximationSequence.seq F ρ (ui j).val (2 * (D + 1 / 4)) (k j + K) x :=
    antitone_diagonal_seq F ρ hanti (fun j => hdouble (ui j).val (ui j).property) hk' x
  have hdiaglim (x : M) : Tendsto (fun j =>
      DemaillyApproximationSequence.seq F ρ (ui j).val (2 * (D + 1 / 4)) (k j + K) x)
      atTop (𝓝 (u.val x)) := by
    have heq := (iInf_diagonal_seq F hρ (fun j => (ui j).property.1) hanti
      (fun j => hdouble (ui j).val (ui j).property) hk'top x).trans (hinf x)
    simpa only [heq] using tendsto_atTop_iInf (hdiaganti x)
  have htarget : IsThetaPshPotential (θ + omega.form).val u.val :=
    LocalPotentials.isThetaPshPotential_add_of_semipositive u.property omega.isSemipositive
  have hhalf (j : ℕ) := (hall (ui j).val (ui j).property).2.2.1 (k j)
  refine ⟨⟨htarget, ⟨fun _ => le_rfl, antitone_const, tendsto_const_nhds⟩,
    fun j => (hrows (ui j).val (ui j).property).term (k j),
    fun j => (hrows (ui j).val (ui j).property).term_hasAnalyticSingularityType (k j),
    ⟨hdiaganti, hdiaglim⟩, ?_⟩, hhalf⟩
  intro c d hc hcd
  obtain ⟨r, hcr, hrd⟩ := exists_between hcd
  have hr : 0 < r := hc.trans hcr
  have hsource := eventually_multiplierIdeal_le_of_native_limit omega θ hbig atTop ui u hc hcr hlim
  obtain ⟨L, hL⟩ := exists_uniform_multiplier_level hn F hρ hdouble hr hrd
  filter_upwards [hsource, hk'top.eventually_ge_atTop L] with j hj hjL
  have hfirst := hL (ui j).val (ui j).property (k j + K) hjL
  have hsecond := multiplierIdealIncluded_of_multiplierIdeal_le
    (ui j).property.1 u.property.1 hr hc hj
  intro e z hz f hf hint
  exact hsecond e z hz f hf (hfirst e z hz f hf hint)

end
end SGPT.Foundations.Analysis.Pending.DemaillyCommonGeometryDiagonalFullQea
