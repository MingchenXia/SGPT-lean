import SGPT.Okounkov.SourceTraceOperations
import SGPT.NPP.DimensionZero
import SGPT.Foundations.Analysis.Pending.NaturalSubmanifoldSourceTraceDefinition
import SGPT.Foundations.Analysis.Pending.DominationLogResolution
import SGPT.Foundations.Analysis.Pending.SingularCanonicalDistanceZeroPEquivalence

/-!
# The trace operator along a point

Source: the unlabelled example of `chapter_trace.tex` following `prop:traceunique`
(`chapter_trace:example:6`): when `Y` is a single point, `QPSH(Y)` is canonically
identified with `ℝ`, and any constant `c ∈ ℝ` is a trace operator of every
`φ ∈ QPSH(X)` with `ν(φ, Y) = 0`.

A point is a closed connected complex submanifold of dimension `0`
(`DominationLogResolution.isClosedConnectedSubmanifold_singleton`), so it is its
own normalization and the natural trace predicate
`IsNaturalSourceTraceRepresentative` (source `def:traceop` on a smooth target, with
the complex and Kähler structure induced from `X`) applies literally.

Main results:

* `SGPT.Trace.sourceQPSHEquivReal_of_dim_zero`: `QPSH(Y) ≃ ℝ` on a connected
  zero-dimensional manifold;
* `SGPT.Trace.isSourceTraceRepresentativeAlong_const_of_dim_zero`: on a
  zero-dimensional connected target, a trace representative may be replaced by any
  real constant;
* `SGPT.Trace.isNaturalSourceTraceRepresentative_singleton_const`: the statement
  of the example for `Y = {x}`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology Manifold ENNReal ContDiff

namespace SGPT.Trace

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences
  SGPT.Foundations.Analysis.Pending
  SourceTraceRepresentativeDefinition NaturalSubmanifoldSourceTraceDefinition
  SquaredLogLelongSourceNormalization SingularGlobalPOrder ThetaPshL1Topology
  SingularCanonicalSingularityDistance PluripolarCapacityDichotomy
open SGPT.PSH SGPT.PSH.VariableComplexAtlas

section DimZero

variable {V : Type*} [TopologicalSpace V] [ChartedSpace (ComplexModel 0) V]
  [IsComplexManifold 0 V]

/-- In dimension `0`, a function is quasi-psh in the source sense iff it is finite
everywhere. -/
theorem isQPSH_iff_finite_of_dim_zero (u : V → EReal) :
    (ofFixedModel 0 V).IsQPSH u ↔ ∀ y, u y ≠ ⊤ ∧ u y ≠ ⊥ := by
  constructor
  · rintro ⟨θ, hθ⟩
    exact (SGPT.NPP.isThetaPSH_iff_finite_of_dim_zero θ u).mp hθ
  · intro hu
    exact ⟨nativeClosedFormToAtlas 0,
      (SGPT.NPP.isThetaPSH_iff_finite_of_dim_zero _ u).mpr hu⟩

/-- Source `chapter_trace:example:6`, first claim: on a connected zero-dimensional
manifold (a point), evaluation at the point identifies `QPSH(Y)` with `ℝ`, the
inverse being the constant functions. -/
def sourceQPSHEquivReal_of_dim_zero [ConnectedSpace V] (y₀ : V) :
    {u : V → EReal // (ofFixedModel 0 V).IsQPSH u} ≃ ℝ where
  toFun u := (u.1 y₀).toReal
  invFun c := ⟨fun _ => (c : EReal),
    (isQPSH_iff_finite_of_dim_zero _).mpr fun _ => ⟨EReal.coe_ne_top c, EReal.coe_ne_bot c⟩⟩
  left_inv u := by
    let : Subsingleton V := SGPT.NPP.subsingleton_of_dim_zero
    apply Subtype.ext
    funext y
    have hfin := (isQPSH_iff_finite_of_dim_zero u.1).mp u.2 y₀
    rw [Subsingleton.elim y y₀]
    exact EReal.coe_toReal hfin.1 hfin.2
  right_inv c := by
    simp only [EReal.toReal_coe]

variable [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]

/-- Two finite functions on a connected zero-dimensional compact manifold are
`P`-equivalent. -/
theorem sourcePEquivalent_of_finite_of_dim_zero (omegaV : KahlerBackground 0 V)
    {u v : V → EReal} (hu : ∀ y, u y ≠ ⊤ ∧ u y ≠ ⊥) (hv : ∀ y, v y ≠ ⊤ ∧ v y ≠ ⊥) :
    SourcePEquivalent (n := 0) u v := by
  let : Subsingleton V := SGPT.NPP.subsingleton_of_dim_zero
  have hups : IsThetaPshPotential omegaV.form.val u :=
    RooftopDimZero.isThetaPshPotential_of_dim_zero rfl
      (LocalPotentials.closedRealOneOne_hasLocalPotentials omegaV.form)
      (fun z => (hu z).1) (fun z => (hu z).2)
  have hvps : IsThetaPshPotential omegaV.form.val v :=
    RooftopDimZero.isThetaPshPotential_of_dim_zero rfl
      (LocalPotentials.closedRealOneOne_hasLocalPotentials omegaV.form)
      (fun z => (hv z).1) (fun z => (hv z).2)
  have hmore (a b : V → EReal) (ha : ∀ y, a y ≠ ⊤ ∧ a y ≠ ⊥)
      (hb : ∀ y, b y ≠ ⊤ ∧ b y ≠ ⊥) : MoreSingularOn a b Set.univ := by
    by_cases hV : Nonempty V
    · obtain ⟨y⟩ := hV
      have haco : ((a y).toReal : EReal) = a y := EReal.coe_toReal (ha y).1 (ha y).2
      have hbco : ((b y).toReal : EReal) = b y := EReal.coe_toReal (hb y).1 (hb y).2
      refine ⟨(a y).toReal - (b y).toReal, ?_⟩
      intro z _hz
      rw [Subsingleton.elim z y, ← haco, ← hbco, ← EReal.coe_add]
      exact_mod_cast (by linarith : (a y).toReal ≤
        (b y).toReal + ((a y).toReal - (b y).toReal))
    · exact ⟨0, fun z _ => (hV ⟨z⟩).elim⟩
  exact ⟨sourcePOrder_of_moreSingularOn omegaV omegaV.form omegaV.form hups hvps
      (hmore u v hu hv),
    sourcePOrder_of_moreSingularOn omegaV omegaV.form omegaV.form hvps hups
      (hmore v u hv hu)⟩

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- On a connected zero-dimensional target, if `τ` is a trace operator of `u`, then so
is every real constant: the canonical singularity distance between two finite
functions on a point vanishes. -/
theorem isSourceTraceRepresentativeAlong_const_of_dim_zero
    {omega : KahlerBackground n M} {omegaV : KahlerBackground 0 V} {ι : V → M}
    {hι : ContMDiff 𝓘(ℂ, ComplexModel 0) 𝓘(ℂ, ComplexModel n) ∞ ι}
    {u : M → EReal} {τ : V → EReal}
    (hT : IsSourceTraceRepresentativeAlong omega omegaV hι u τ) (c : ℝ) :
    IsSourceTraceRepresentativeAlong omega omegaV hι u (fun _ => (c : EReal)) := by
  obtain ⟨hg, θ, ε, U, happ, β, hadm, hτ, hterms, hlim⟩ := hT
  have hc : IsThetaPshPotential β.form.val (fun _ : V => (c : EReal)) :=
    RooftopDimZero.isThetaPshPotential_of_dim_zero rfl
      (LocalPotentials.closedRealOneOne_hasLocalPotentials β.form)
      (fun _ => EReal.coe_ne_top c) (fun _ => EReal.coe_ne_bot c)
  have hτfin : ∀ y, τ y ≠ ⊤ ∧ τ y ≠ ⊥ := fun y =>
    ⟨hτ.1.quasiPlurisubharmonic.ne_top y,
      RooftopDimZero.ne_bot_of_locallyNondegenerate_of_dim_zero rfl hτ.2 y⟩
  have hPeq : SourcePEquivalent (n := 0) τ (fun _ : V => (c : EReal)) :=
    sourcePEquivalent_of_finite_of_dim_zero omegaV hτfin
      (fun _ => ⟨EReal.coe_ne_top c, EReal.coe_ne_bot c⟩)
  have hd : singularityDistance omegaV β.form (isBigClass_kahler β) τ
      (fun _ : V => (c : EReal)) = 0 :=
    (SingularCanonicalDistanceZeroPEquivalence.singularityDistance_eq_zero_iff_sourcePEquivalent
      omegaV β.form (isBigClass_kahler β) hτ hc).mpr hPeq
  refine ⟨hg, θ, ε, U, happ, β, hadm, hc, hterms, ?_⟩
  let := singularityPseudoMetricSpace omegaV β.form (isBigClass_kahler β)
  let a : ThetaPshL1 β.form.val := ⟨τ, hτ⟩
  let b : ThetaPshL1 β.form.val := ⟨fun _ => (c : EReal), hc⟩
  have hdist : dist a b = 0 := by
    rw [dist_eq_singularityDistance_toReal]
    change (singularityDistance omegaV β.form (isBigClass_kahler β) τ
      (fun _ : V => (c : EReal))).toReal = 0
    rw [hd, EReal.toReal_zero]
  have hins : @Inseparable _ (singularityPseudoMetricSpace omegaV β.form
      (isBigClass_kahler β)).toUniformSpace.toTopologicalSpace a b :=
    Metric.inseparable_iff.mpr hdist
  rw [← @Inseparable.nhds_eq _ (singularityPseudoMetricSpace omegaV β.form
    (isBigClass_kahler β)).toUniformSpace.toTopologicalSpace _ _ hins]
  exact hlim

end DimZero

section Point

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

omit [IsComplexManifold n M] in
/-- Along a point the generic Lelong number is the Lelong number at that point. -/
theorem sourceGenericLelongNumber_singleton (x : M) (u : M → EReal) :
    sourceGenericLelongNumber (n := n) (Subtype.val : ({x} : Set M) → M) u =
      squaredLogLelongNumber (n := n) u x := by
  unfold sourceGenericLelongNumber
  let : Unique ({x} : Set M) := Set.uniqueSingleton x
  rw [iInf_unique]
  rfl

private theorem nativeGlobal_of_sourceQPSH {u : M → EReal}
    (hu : (ofFixedModel n M).IsQPSH u) : IsGlobalQuasiPshPotential (n := n) u := by
  obtain ⟨θ, hθ⟩ := hu
  exact ((isThetaPSH_iff_nativeThetaPotential θ u).mp hθ).quasiPshPotential

variable [CompactSpace M]

/-- Source `chapter_trace:example:6`: let `Y = {x}` be a point of the compact Kähler
manifold `X` and let `φ ∈ QPSH(X)` with `ν(φ, Y) = 0`. Then every real constant `c` is
a trace operator of `φ` along `Y` (for the complex and Kähler structure that the point
inherits from `X`). -/
theorem isNaturalSourceTraceRepresentative_singleton_const
    (omega : KahlerBackground n M) (x : M) {u : M → EReal}
    (hu : (ofFixedModel n M).IsQPSH u)
    (hν : sourceGenericLelongNumber (n := n) (Subtype.val : ({x} : Set M) → M) u = 0)
    (c : ℝ) :
    IsNaturalSourceTraceRepresentative omega
      (DominationLogResolution.isClosedConnectedSubmanifold_singleton (k := n) x) u
      (fun _ => (c : EReal)) := by
  have hW := DominationLogResolution.isClosedConnectedSubmanifold_singleton (k := n) x
  let hk : 0 ≤ n := SubmanifoldChartedSpace.le_of_isClosedConnectedSubmanifold hW
  let : ChartedSpace (ComplexModel 0) ({x} : Set M) :=
    SubmanifoldChartedSpace.chartedSpace hk hW.2.2
  let : IsComplexManifold 0 ({x} : Set M) :=
    SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hW.2.2
  let : ConnectedSpace ({x} : Set M) := isConnected_iff_connectedSpace.mp hW.2.1
  let : CompactSpace ({x} : Set M) := isCompact_iff_compactSpace.mp hW.1.isCompact
  let : MeasurableSpace ({x} : Set M) := borel _
  let : BorelSpace ({x} : Set M) := ⟨rfl⟩
  let omegaW := SubmanifoldKahlerRestriction.kahlerBackground hk hW.2.2 omega
  let hι := SubmanifoldChartedSpace.contMDiff_val hk hW.2.2
  obtain ⟨τ, hT⟩ := SGPT.TraceOperations.exists_sourceTrace_of_globalQuasiPshPotential hk
    omega omegaW (nativeGlobal_of_sourceQPSH hu) hι hν
  exact isSourceTraceRepresentativeAlong_const_of_dim_zero hT c

/-- Source `chapter_trace:example:6`, the same statement with the hypothesis
`ν(φ, x) = 0` written at the point. -/
theorem isNaturalSourceTraceRepresentative_singleton_const_of_lelong
    (omega : KahlerBackground n M) (x : M) {u : M → EReal}
    (hu : (ofFixedModel n M).IsQPSH u)
    (hν : squaredLogLelongNumber (n := n) u x = 0) (c : ℝ) :
    IsNaturalSourceTraceRepresentative omega
      (DominationLogResolution.isClosedConnectedSubmanifold_singleton (k := n) x) u
      (fun _ => (c : EReal)) :=
  isNaturalSourceTraceRepresentative_singleton_const omega x hu
    ((sourceGenericLelongNumber_singleton x u).trans hν) c

end Point

end SGPT.Trace
