import SGPT.Envelopes.SourceNonPluripolarMassOrder
import SGPT.PSH.SourceRayL1
import SGPT.Foundations.Analysis.Pending.NaturalThetaPshHartogsRecovery
import SGPT.Foundations.Analysis.Pending.DecreasingContactMassLimit
import SGPT.Foundations.Analysis.Pending.DiagonalMeasureWeakConvergenceReduction

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending KahlerVolumeSmoothPositive

/-- Pure scalar small-distance sequence test; the source consumer discharges
its sequence premise using the actual full analytic sequence producer. -/
theorem limsup_le_of_small_distance_sequences {I : Type*} (F : Filter I) [NeBot F]
    (e f : I → ℝ≥0∞) (L : ℝ≥0∞) (he : Tendsto e F (𝓝 0))
    (hseq : ∀ j : ℕ → I, Tendsto (fun k => e (j k)) atTop (𝓝 0) →
      limsup (fun k => f (j k)) atTop ≤ L) : limsup f F ≤ L := by
  by_contra hn
  obtain ⟨b, hLb, hb⟩ := exists_between (not_le.mp hn)
  have hbad : ∃ᶠ i in F, b < f i := frequently_lt_of_lt_limsup (by isBoundedDefault) hb
  have hchoose : ∀ k : ℕ, ∃ i, b < f i ∧
      e i < ENNReal.ofReal (1 / ((k : ℝ) + 1)) := by
    intro k
    have hpos : 0 < ENNReal.ofReal (1 / ((k : ℝ) + 1)) :=
      ENNReal.ofReal_pos.mpr (by positivity)
    exact (hbad.and_eventually (he.eventually (gt_mem_nhds hpos))).exists
  choose j hjbad hje using hchoose
  have heps : Tendsto (fun k : ℕ => ENNReal.ofReal (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero, Function.comp_def] using
      (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp
        tendsto_one_div_add_atTop_nhds_zero_nat
  have hje0 : Tendsto (fun k => e (j k)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds heps
      (Eventually.of_forall fun _ => zero_le) (Eventually.of_forall fun k => (hje k).le)
  have hbl : b ≤ limsup (fun k => f (j k)) atTop := by
    apply le_limsup_of_le (by isBoundedDefault)
    intro c hc
    obtain ⟨k, hk⟩ := hc.exists
    exact (hjbad k).le.trans hk
  exact (not_le_of_gt hLb) (hbl.trans (hseq j hje0))

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- The literal original actual zero-contact mass, with every original value retained. -/
def sourceZeroContactMass (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (u : M → EReal) (hu : (ofFixedModel n M).IsThetaPSH θ u) : ℝ≥0∞ :=
  sourcePotentialNonPluripolarMeasure θ u hu {x | u x = 0}

omit [BorelSpace M] in
/-- The native contact mass is exactly the same original diagonal measure on the same set. -/
theorem sourceZeroContactMass_eq_native (u : M → EReal)
    (hu : (ofFixedModel n M).IsThetaPSH θ u) :
    sourceZeroContactMass θ u hu = RooftopMassDiamondLimit.contactMass
      (atlasClosedFormToNative θ) u ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu) := rfl

/-- Genuine original contact mass is finite before any ordinary real readback. -/
theorem sourceZeroContactMass_lt_top (ω : KahlerBackground n M) {u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) : sourceZeroContactMass θ u hu < ⊤ :=
  DiagonalMeasureRegularity.diagonalPotentialMeasure_lt_top ω (atlasClosedFormToNative θ)
    ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu) _

omit [BorelSpace M] in
/-- The source global distance uses the ACTUAL source volume omega^n, not an auxiliary measure. -/
theorem sourceContactL1Distance_eq_sourceVolume (ω : KahlerBackground n M) (u v : M → EReal) :
    sourceGlobalL1Distance ω u v =
      ∫⁻ x, canonicalERealAbsDiff (u x) (v x) ∂sourceKahlerVolume ω := by
  rw [sourceKahlerVolume_eq_native]
  rfl

/-- The original global L1 hypothesis gives precisely native chart-local L1
for every genuine original family and indexing filter, with no ray restriction. -/
theorem sourceContact_globalL1_iff_chartL1 (ω : KahlerBackground n M)
    {I : Type*} (F : Filter I) {u : I → M → EReal} {v : M → EReal}
    (hu : ∀ i, (ofFixedModel n M).IsThetaPSH θ (u i))
    (hv : (ofFixedModel n M).IsThetaPSH θ v) :
    Tendsto (fun i => sourceGlobalL1Distance ω (u i) v) F (𝓝 0) ↔
      ManifoldL1LocallyTendsto (n := n) u F v := by
  exact (manifoldL1LocallyTendsto_iff_global_of_eventually_measurable
    (isSmoothPositiveVolume_kahlerVolume ω)
    (Eventually.of_forall fun i => ((isThetaPSH_iff_nativeThetaPotential θ (u i)).mp
      (hu i)).1.quasiPlurisubharmonic.upperSemicontinuous.measurable)
    ((isThetaPSH_iff_nativeThetaPotential θ v).mp hv).1.quasiPlurisubharmonic.upperSemicontinuous.measurable).symm

/-- The source's actual upper-regularized canonical tail over the ENTIRE original family. -/
def sourceCanonicalL1Tail (u : ℕ → M → EReal) (N : ℕ) : M → EReal :=
  SGPT.PSH.uscSup (fun j : ℕ => u (j + N))

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- The whole original neighborhood regularization and all tail members are unchanged. -/
theorem sourceCanonicalL1Tail_eq_native (u : ℕ → M → EReal) (N : ℕ) :
    sourceCanonicalL1Tail u N = uscRegularization (⨆ j : ℕ, u (j + N)) :=
  sourceUscSup_eq_native (fun j : ℕ => u (j + N))

/-- Actual Hartogs recovery manufactures EVERY output tail property from original L1.
No original monotonicity, pointwise limit or output genuineness is assumed. -/
theorem sourceCanonicalL1Tail_recovery (ω : KahlerBackground n M)
    {u : ℕ → M → EReal} {v : M → EReal}
    (hu : ∀ j, (ofFixedModel n M).IsThetaPSH θ (u j))
    (hu0 : ∀ j, u j ≤ 0) (hv : (ofFixedModel n M).IsThetaPSH θ v)
    (hL1 : Tendsto (fun j => sourceGlobalL1Distance ω (u j) v) atTop (𝓝 0)) :
    (∀ N, (ofFixedModel n M).IsThetaPSH θ (sourceCanonicalL1Tail u N)) ∧
    (∀ N, sourceCanonicalL1Tail u N ≤ 0) ∧
    Antitone (sourceCanonicalL1Tail u) ∧ (∀ N, u N ≤ sourceCanonicalL1Tail u N) ∧
    (⨅ N, sourceCanonicalL1Tail u N) = v ∧
    (∀ x, Tendsto (fun N => sourceCanonicalL1Tail u N x) atTop (𝓝 (v x))) := by
  have h := NaturalThetaPshHartogsRecovery.usc_tailSup_iInf_eq_and_tendsto
    (fun j => (isThetaPSH_iff_nativeThetaPotential θ (u j)).mp (hu j))
    ((isThetaPSH_iff_nativeThetaPotential θ v).mp hv)
    ((sourceContact_globalL1_iff_chartL1 ω atTop hu hv).mp hL1)
    (C := 0) (by intro j x; simpa using hu0 j x)
  simp only [← sourceCanonicalL1Tail_eq_native] at h
  refine ⟨fun N => (isThetaPSH_iff_nativeThetaPotential θ _).mpr (h.1 N), ?_,
    h.2.1, ?_, h.2.2.1, h.2.2.2⟩
  · intro N
    rw [sourceCanonicalL1Tail_eq_native]
    exact uscRegularization_le upperSemicontinuous_const (iSup_le fun j => hu0 (j + N))
  · intro N
    rw [sourceCanonicalL1Tail_eq_native]
    have hself : u N ≤ ⨆ j : ℕ, u (j + N) := by
      simpa only [Nat.zero_add] using (le_iSup (fun j : ℕ => u (j + N)) 0)
    exact hself.trans (le_uscRegularization _)

/-- Genuine ordered nonpositive zero-contact monotonicity reuses the actual native producer. -/
theorem sourceZeroContactMass_mono (ω : KahlerBackground n M) {u v : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hv : (ofFixedModel n M).IsThetaPSH θ v)
    (hv0 : v ≤ 0) (huv : u ≤ v) : sourceZeroContactMass θ u hu ≤ sourceZeroContactMass θ v hv :=
  DiagonalMeasureWeakConvergenceReduction.contactMass_le_contactMass_of_le_of_nonpositive
    ω (atlasClosedFormToNative θ)
    ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu)
    ((isThetaPSH_iff_nativeThetaPotential θ v).mp hv) hv0 huv

/-- FULL arbitrary nonpositive original L1 sequence, without input antitonicity. -/
theorem sourceZeroContactMass_limsup_sequence (ω : KahlerBackground n M)
    {u : ℕ → M → EReal} {v : M → EReal}
    (hu : ∀ j, (ofFixedModel n M).IsThetaPSH θ (u j))
    (hu0 : ∀ j, u j ≤ 0) (hv : (ofFixedModel n M).IsThetaPSH θ v)
    (hL1 : Tendsto (fun j => sourceGlobalL1Distance ω (u j) v) atTop (𝓝 0)) :
    limsup (fun j => sourceZeroContactMass θ (u j) (hu j)) atTop ≤ sourceZeroContactMass θ v hv := by
  obtain ⟨hU, hU0, hanti, hself, _hinf, hpoint⟩ := sourceCanonicalL1Tail_recovery ω hu hu0 hv hL1
  have hdom : ∀ j, sourceZeroContactMass θ (u j) (hu j) ≤
      sourceZeroContactMass θ (sourceCanonicalL1Tail u j) (hU j) := fun j =>
    sourceZeroContactMass_mono ω (hu j) (hU j) (hU0 j) (hself j)
  have htail := DecreasingContactMassLimit.contactMeasure_limsup_le_of_antitone_of_tendsto
    ω (atlasClosedFormToNative θ) (sourceCanonicalL1Tail u)
    (fun j => (isThetaPSH_iff_nativeThetaPotential θ _).mp (hU j))
    hU0 v ((isThetaPSH_iff_nativeThetaPotential θ v).mp hv) hanti hpoint
  exact (Filter.limsup_le_limsup (Eventually.of_forall hdom)).trans htail

/-- WHOLE original arbitrary-directed-L1-net contact upper semicontinuity.
No monotonicity, cofinality, pointwise/metric output or analytic certificate is input. -/
theorem sourceZeroContactMass_limsup_net (ω : KahlerBackground n M)
    {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    {u : I → M → EReal} {v : M → EReal}
    (hu : ∀ i, (ofFixedModel n M).IsThetaPSH θ (u i))
    (hu0 : ∀ i, u i ≤ 0) (hv : (ofFixedModel n M).IsThetaPSH θ v)
    (hL1 : Tendsto (fun i => sourceGlobalL1Distance ω (u i) v) atTop (𝓝 0)) :
    limsup (fun i => sourceZeroContactMass θ (u i) (hu i)) atTop ≤ sourceZeroContactMass θ v hv := by
  apply limsup_le_of_small_distance_sequences atTop
    (fun i => sourceGlobalL1Distance ω (u i) v)
    (fun i => sourceZeroContactMass θ (u i) (hu i)) (sourceZeroContactMass θ v hv) hL1
  intro j hj
  exact sourceZeroContactMass_limsup_sequence ω (fun k => hu (j k)) (fun k => hu0 (j k)) hv hj

end SGPT.PSH.VariableComplexAtlas
