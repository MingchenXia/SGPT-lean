import SGPT.Foundations.Analysis.Pending.NaturalSourceTraceExistencePositiveAmbient
import SGPT.Foundations.Analysis.Pending.QuasiEquisingularApproximationDemailly
import SGPT.Foundations.Analysis.Pending.GlobalQuasiPshKahlerBackground
import SGPT.Foundations.Analysis.Pending.RooftopDimZero

set_option autoImplicit false

/-! # Natural source trace existence, including the actual zero-ambient branch -/

open Set Filter
open scoped Topology Manifold ENNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.NaturalSourceTraceExistenceAllDimensions

open FirstPass FirstPass.BlowupSequences FirstPass.PositiveClasses
  FirstPass.QuasiEquisingularApproximation FirstPass.TraceBackground
  ThetaPshL1Topology SingularCanonicalSingularityDistance PluripolarCapacityDichotomy
  SourceTraceRepresentativeDefinition NaturalSubmanifoldSourceTraceDefinition

noncomputable section

/-- The same ordinary restriction and constant approximation give an actual
source trace in zero ambient dimension; no native generic-zero premise. -/
theorem sourceTrace_ordinaryRestriction_zero
    {M V : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel 0) M]
    [IsComplexManifold 0 M] [TopologicalSpace V] [ChartedSpace (ComplexModel 0) V]
    [IsComplexManifold 0 V] [MeasurableSpace V] [BorelSpace V]
    [CompactSpace V] [ConnectedSpace V]
    (omega : KahlerBackground 0 M) (omegaV : KahlerBackground 0 V)
    {θ : ClosedRealOneOneForm 0 M} {u : M → EReal}
    (hu : IsThetaPshPotential θ.val u) {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel 0) 𝓘(ℂ, ComplexModel 0) ∞ ι) :
    IsSourceTraceRepresentativeAlong omega omegaV hι u (fun y => u (ι y)) := by
  obtain ⟨c, 𝔞, hsing⟩ :=
    DemaillyApproximationAnalyticType.hasAnalyticSingularities_of_dim_zero hu
  have happ := Pending.isQuasiEquisingularApproximation_const omega θ hu
    hsing.hasManifoldAnalyticSingularityType
  have hrestr : IsThetaPshPotential omegaV.form.val (fun y => u (ι y)) :=
    RooftopDimZero.isThetaPshPotential_of_dim_zero rfl
      (LocalPotentials.closedRealOneOne_hasLocalPotentials omegaV.form)
      (fun y => hu.1.quasiPlurisubharmonic.ne_top (ι y))
      (fun y => RooftopDimZero.ne_bot_of_locallyNondegenerate_of_dim_zero rfl hu.2 (ι y))
  have hadm : IsAdmissibleTraceBackground hι omega θ (fun _ => 0) omegaV.form := by
    refine ⟨omegaV.isKahler, ?_⟩
    intro j e z hz v
    have hv : v = 0 := Subsingleton.elim _ _
    subst v
    rw [((omegaV.form - ClosedRealOneOneForm.pullback hι
      (θ + (0 : ℝ) • omega.form)).val.coeff e z).map_coord_zero (0 : Fin 2) rfl]
  refine ⟨sourceGenericLelongNumber_zero_dimension rfl ι u,
    θ, (fun _ => 0), (fun _ => u), happ, omegaV, hadm, hrestr,
    (fun _ => hrestr), ?_⟩
  exact @tendsto_const_nhds (ThetaPshL1 omegaV.form.val)
    (singularityPseudoMetricSpace omegaV omegaV.form
      (isBigClass_kahler omegaV)).toUniformSpace.toTopologicalSpace
    ℕ ⟨fun y => u (ι y), hrestr⟩ atTop

variable {n k : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

/-- The original closed form and genuine potential internally supply the
approximation and every target object, in all ambient dimensions. -/
theorem exists_naturalSourceTrace_of_isThetaPshPotential
    (omega : KahlerBackground n M) {W : Set M}
    (hW : IsClosedConnectedSubmanifold n W k)
    {θ : ClosedRealOneOneForm n M} {u : M → EReal}
    (hu : IsThetaPshPotential θ.val u)
    (hgeneric : sourceGenericLelongNumber (n := n) (Subtype.val : W → M) u = 0) :
    ∃ τ : W → EReal, IsNaturalSourceTraceRepresentative omega hW u τ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hk : k = 0 := Nat.eq_zero_of_le_zero
      (SubmanifoldChartedSpace.le_of_isClosedConnectedSubmanifold hW)
    subst k
    let hdim : 0 ≤ 0 := SubmanifoldChartedSpace.le_of_isClosedConnectedSubmanifold hW
    let : ChartedSpace (ComplexModel 0) W :=
      SubmanifoldChartedSpace.chartedSpace hdim hW.2.2
    let : IsComplexManifold 0 W :=
      SubmanifoldChartedSpace.isComplexManifold_chartedSpace hdim hW.2.2
    let : ConnectedSpace W := isConnected_iff_connectedSpace.mp hW.2.1
    let : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
    let : MeasurableSpace W := borel W
    let : BorelSpace W := ⟨rfl⟩
    let omegaW : KahlerBackground 0 W :=
      SubmanifoldKahlerRestriction.kahlerBackground hdim hW.2.2 omega
    let hι := SubmanifoldChartedSpace.contMDiff_val hdim hW.2.2
    refine ⟨fun y => u (y : M), ?_⟩
    change IsSourceTraceRepresentativeAlong omega omegaW hι u (fun y => u (y : M))
    exact sourceTrace_ordinaryRestriction_zero omega omegaW hu hι
  · obtain ⟨ε, uSeq, happ⟩ :=
      QuasiEquisingularApproximationDemailly.exists_quasiEquisingularApproximation omega θ hu
    exact NaturalSourceTraceExistencePositiveAmbient.exists_naturalSourceTrace_of_QEA
      (Nat.ne_of_gt hn) hW happ hgeneric

/-- The same genuine global quasi-PSH potential internally supplies its
closed background as well as the complete all-dimensional trace data. -/
theorem exists_naturalSourceTrace_of_globalQuasiPshPotential
    (omega : KahlerBackground n M) {W : Set M}
    (hW : IsClosedConnectedSubmanifold n W k) {u : M → EReal}
    (hu : IsGlobalQuasiPshPotential (n := n) u)
    (hgeneric : sourceGenericLelongNumber (n := n) (Subtype.val : W → M) u = 0) :
    ∃ τ : W → EReal, IsNaturalSourceTraceRepresentative omega hW u τ := by
  obtain ⟨θ, hθu⟩ :=
    (GlobalQuasiPshKahlerBackground.isGlobalQuasiPshPotential_iff_exists_closed_background
      omega u).mp hu
  exact exists_naturalSourceTrace_of_isThetaPshPotential omega hW hθu hgeneric

end
end SGPT.Foundations.Analysis.Pending.NaturalSourceTraceExistenceAllDimensions
