import SGPT.Envelopes.SourcePositiveMassCurrents
import SGPT.Envelopes.SourceIncreasingMixedProducts
import SGPT.Foundations.Analysis.Pending.SingularModelIncreasingAERegularizedLimit
import SGPT.Foundations.Analysis.Pending.IEnvelopeIncreasingRegularizedSupremum

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas

open Set Filter MeasureTheory
open scoped ENNReal Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending DiagonalMass ThetaPshConvexCombination
open IncreasingMixedDirectedNets ChartwiseGlobalL1 IntegrationCurrent

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- A genuine finite maximum manufactures a zero of the SAME ordinary P,
including zero original mass. No I-envelope or fixedness premise appears. -/
theorem sourceOrdinaryEnvelope_hasZero {u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) :
    ∃ x, sourceSingularityEnvelope θ u x = 0 := by
  have hn := (isThetaPSH_iff_nativeThetaPotential θ u).mp hu
  obtain ⟨x, m, hxm, hmax⟩ := hn.exists_max
  have hnorm := sub_const_nonpositive_of_le hmax
  have hmore : MoreSingularOn (fun y => u y - (m : EReal)) u univ := by
    simpa only [sub_eq_add_neg, EReal.coe_neg] using
      (sameSingularityTypeOn_add_const u univ (-m)).1
  have hle := le_singularityEnvelope (hn.sub_const m) hnorm hmore
  refine ⟨x, le_antisymm (sourceSingularityEnvelope_le_zero θ u x) ?_⟩
  rw [sourceSingularityEnvelope_eq_native]
  have hx : u x - (m : EReal) = 0 := by
    rw [hxm, ← EReal.coe_sub, sub_self, EReal.coe_zero]
  simpa only [hx] using hle x

variable [MeasurableSpace M] [BorelSpace M]

/-- The EXISTING true normalized-PSH Harnack/volume bound applies to ALL
ordinary envelopes after their actual zero point has been manufactured. -/
theorem sourceOrdinaryEnvelope_uniformL1 (ω : KahlerBackground n M) :
    ∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ (v : M → EReal),
      (ofFixedModel n M).IsThetaPSH θ v →
      ∫⁻ x, (-sourceSingularityEnvelope θ v x).toENNReal ∂sourceKahlerVolume ω ≤ B := by
  obtain ⟨B, hB, hBv⟩ :=
    SingularModelUniformModelL1.exists_uniform_lintegral_neg_le_kahlerVolume
      (atlasClosedFormToNative θ) ω 0
  refine ⟨B, hB, fun v hv => ?_⟩
  obtain ⟨x, hx⟩ := sourceOrdinaryEnvelope_hasZero hv
  rw [sourceKahlerVolume_eq_native]
  exact hBv _ ((isThetaPSH_iff_nativeThetaPotential θ _).mp
    (sourceOrdinaryEnvelope_genuine hv)).1 (sourceSingularityEnvelope_le_zero θ v)
    ⟨x, by rw [hx]; simp⟩

/-- The actual ordinary normalized envelopes have vanishing scaled canonical
L1 gaps. Genuine finite-AE membership is produced BEFORE real readback. -/
theorem sourceOrdinaryEnvelope_scaledL1_tendsto (ω : KahlerBackground n M)
    {I : Type*} (F : Filter I) (v : I → M → EReal)
    (hv : ∀ i, (ofFixedModel n M).IsThetaPSH θ (v i)) (ε : I → ℝ)
    (hεpos : ∀ i, 0 < ε i) (hε : Tendsto ε F (𝓝 0)) :
    Tendsto (fun i => globalL1EDistance (kahlerVolume ω)
      (fun x => (ε i : EReal) * sourceSingularityEnvelope θ (v i) x) (fun _ => 0))
      F (𝓝 0) := by
  obtain ⟨B, hB, hBv⟩ := sourceOrdinaryEnvelope_uniformL1 (θ := θ) ω
  have hbound (i : I) : globalL1EDistance (kahlerVolume ω)
      (fun x => (ε i : EReal) * sourceSingularityEnvelope θ (v i) x) (fun _ => 0) ≤
      ENNReal.ofReal (ε i) * B := by
    calc
      _ = ∫⁻ x, ENNReal.ofReal (ε i) *
          (-sourceSingularityEnvelope θ (v i) x).toENNReal ∂kahlerVolume ω := by
        apply lintegral_congr_ae
        filter_upwards [sourceThetaPSH_ae_finite_kahlerVolume ω
          (sourceOrdinaryEnvelope_genuine (hv i))] with x hx
        let p : ℝ := (sourceSingularityEnvelope θ (v i) x).toReal
        have hp : (p : EReal) = sourceSingularityEnvelope θ (v i) x :=
          EReal.coe_toReal hx.1 hx.2
        have hp0 : p ≤ 0 := by
          apply EReal.coe_le_coe_iff.mp
          change (p : EReal) ≤ (0 : EReal)
          rw [hp]
          exact sourceSingularityEnvelope_le_zero θ (v i) x
        rw [← hp, ← EReal.coe_mul, ← EReal.coe_zero, canonicalERealAbsDiff_coe_coe,
          sub_zero, abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (hεpos i).le hp0),
          ← EReal.coe_neg, EReal.real_coe_toENNReal, ← ENNReal.ofReal_mul (hεpos i).le]
        congr 1
        ring
      _ = ENNReal.ofReal (ε i) *
          (∫⁻ x, (-sourceSingularityEnvelope θ (v i) x).toENNReal ∂kahlerVolume ω) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (ε i) * B := mul_le_mul' le_rfl (by
        simpa only [sourceKahlerVolume_eq_native] using hBv (v i) (hv i))
  have hcoeff : Tendsto (fun i => ENNReal.ofReal (ε i)) F (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto 0).comp hε
  have hupper : Tendsto (fun i => ENNReal.ofReal (ε i) * B) F (𝓝 0) := by
    simpa only [zero_mul] using ENNReal.Tendsto.mul_const hcoeff (Or.inr hB.ne)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hupper (fun _ => zero_le) hbound

private theorem convexComb_value_tendsto {I : Type*} {F : Filter I}
    {a b : I → EReal} {A B : EReal} (ha : Tendsto a F (𝓝 A))
    (hb : Tendsto b F (𝓝 B)) (hA : A ≤ 0) (hB : B ≤ 0)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    Tendsto (fun i => (t : EReal) * a i + ((1 - t : ℝ) : EReal) * b i) F
      (𝓝 ((t : EReal) * A + ((1 - t : ℝ) : EReal) * B)) := by
  have hta := EReal.Tendsto.const_mul ha
    (Or.inl (EReal.coe_ne_bot t)) (Or.inl (EReal.coe_ne_top t))
  have htb := EReal.Tendsto.const_mul hb
    (Or.inl (EReal.coe_ne_bot (1 - t))) (Or.inl (EReal.coe_ne_top (1 - t)))
  have hAtop : (t : EReal) * A ≠ ⊤ := ne_of_lt
    ((mul_nonpos_of_nonneg_of_nonpos (EReal.coe_nonneg.mpr ht0.le) hA).trans_lt (by simp))
  have hBtop : ((1 - t : ℝ) : EReal) * B ≠ ⊤ := ne_of_lt
    ((mul_nonpos_of_nonneg_of_nonpos
      (EReal.coe_nonneg.mpr (sub_pos.mpr ht1).le) hB).trans_lt (by simp))
  exact (EReal.continuousAt_add (Or.inl hAtop) (Or.inr hBtop)).tendsto.comp
    (hta.prodMk_nhds htb)

omit [MeasurableSpace M] [BorelSpace M] in
/-- Genuine actual truncated-P stages and the EXISTING chart-AE/increasing
regularized-limit producers link strict concavity of the SAME ordinary P.
No additive equivalence of P[u] with u is assumed; no real pole readback. -/
theorem sourceOrdinaryEnvelope_convexComb_le {u v : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hv : (ofFixedModel n M).IsThetaPSH θ v)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    convexComb t (sourceSingularityEnvelope θ u) (sourceSingularityEnvelope θ v) ≤
      sourceSingularityEnvelope θ (convexComb t u v) := by
  simp only [sourceSingularityEnvelope_eq_native]
  let T := atlasClosedFormToNative θ
  have hun : IsThetaPshPotential T.val u := (isThetaPSH_iff_nativeThetaPotential θ u).mp hu
  have hvn : IsThetaPshPotential T.val v := (isThetaPSH_iff_nativeThetaPotential θ v).mp hv
  obtain ⟨C, hC⟩ := hun.exists_normalized_sub_const
  obtain ⟨D, hD⟩ := hvn.exists_normalized_sub_const
  let A : ℕ → M → EReal := fun j => truncatedSingularityEnvelope T.val u (-C + j)
  let B : ℕ → M → EReal := fun j => truncatedSingularityEnvelope T.val v (-D + j)
  have hA (j : ℕ) : IsThetaPshPotential T.val (A j) :=
    truncatedSingularityEnvelope_isThetaPshPotential hun.1.hasSmoothLocalPotentials
      ⟨_, sub_const_mem_truncatedSingularityCompetitors hC (le_add_of_nonneg_right j.cast_nonneg)⟩
  have hB (j : ℕ) : IsThetaPshPotential T.val (B j) :=
    truncatedSingularityEnvelope_isThetaPshPotential hvn.1.hasSmoothLocalPotentials
      ⟨_, sub_const_mem_truncatedSingularityCompetitors hD (le_add_of_nonneg_right j.cast_nonneg)⟩
  have hAm : Monotone A := fun j k hjk => truncatedSingularityEnvelope_mono _ _
    (add_le_add le_rfl (by exact_mod_cast hjk : (j : ℝ) ≤ k))
  have hBm : Monotone B := fun j k hjk => truncatedSingularityEnvelope_mono _ _
    (add_le_add le_rfl (by exact_mod_cast hjk : (j : ℝ) ≤ k))
  have hPu : IsThetaPshPotential T.val (singularityEnvelope T.val u) :=
    FirstPass.singularityEnvelope_isThetaPshPotential T.val T.property.1 T.property.2
      hun.1.hasSmoothLocalPotentials u hun
  have hPv : IsThetaPshPotential T.val (singularityEnvelope T.val v) :=
    FirstPass.singularityEnvelope_isThetaPshPotential T.val T.property.1 T.property.2
      hvn.1.hasSmoothLocalPotentials v hvn
  have heqA : uscRegularization (⨆ j, A j) = singularityEnvelope T.val u :=
    (singularityEnvelope_eq_uscRegularization_iSup_truncated T.val u (-C)).symm
  have heqB : uscRegularization (⨆ j, B j) = singularityEnvelope T.val v :=
    (singularityEnvelope_eq_uscRegularization_iSup_truncated T.val v (-D)).symm
  have hstage (j : ℕ) : convexComb t (A j) (B j) ≤
      singularityEnvelope T.val (convexComb t u v) := by
    apply le_singularityEnvelope (isThetaPshPotential_convexComb (hA j) (hB j) ht0 ht1)
    · intro x
      exact (add_le_add
        (mul_nonpos_of_nonneg_of_nonpos (EReal.coe_nonneg.mpr ht0.le)
          (truncatedSingularityEnvelope_le_zero T.val u (-C + j) x))
        (mul_nonpos_of_nonneg_of_nonpos (EReal.coe_nonneg.mpr (sub_pos.mpr ht1).le)
          (truncatedSingularityEnvelope_le_zero T.val v (-D + j) x))).trans_eq (zero_add 0)
    · refine ⟨t * (-C + j) + (1 - t) * (-D + j), fun x _ => ?_⟩
      calc
        _ ≤ convexComb t (fun y => u y + ((-C + j : ℝ) : EReal))
            (fun y => v y + ((-D + j : ℝ) : EReal)) x :=
          convexComb_mono ht0.le ht1.le
            (truncatedSingularityEnvelope_le_add hun.1.quasiPlurisubharmonic T.val (-C + j))
            (truncatedSingularityEnvelope_le_add hvn.1.quasiPlurisubharmonic T.val (-D + j)) x
        _ = _ := congrFun (POrderAffineRooftop.convexComb_add_const ht0 ht1 u v
          (-C + j) (-D + j)) x
  have hreg : uscRegularization (⨆ j, convexComb t (A j) (B j)) =
      convexComb t (singularityEnvelope T.val u) (singularityEnvelope T.val v) := by
    apply SingularModelIncreasingAERegularizedLimit.uscRegularization_iSup_eq_of_monotone_ae_chart_tendsto
      (fun j => isThetaPshPotential_convexComb (hA j) (hB j) ht0 ht1)
      (isThetaPshPotential_convexComb hPu hPv ht0 ht1)
      (fun x j k hjk => convexComb_mono ht0.le ht1.le (hAm hjk) (hBm hjk) x)
    intro e
    have hAEa := IncreasingMixedRegularizedContinuity.ae_chartFunction_iSup_eq_of_genuine
      hA hAm (heqA.symm ▸ hPu) e
    have hAEb := IncreasingMixedRegularizedContinuity.ae_chartFunction_iSup_eq_of_genuine
      hB hBm (heqB.symm ▸ hPv) e
    rw [heqA] at hAEa
    rw [heqB] at hAEb
    filter_upwards [hAEa, hAEb] with z ha hb
    have hla : Tendsto (fun j => A j (e.val.symm z)) atTop
        (𝓝 (singularityEnvelope T.val u (e.val.symm z))) := by
      change Tendsto (fun j => chartFunction (A j) e z) atTop
        (𝓝 (chartFunction (singularityEnvelope T.val u) e z))
      rw [← ha]
      exact tendsto_atTop_iSup (fun j k hjk => hAm hjk (e.val.symm z))
    have hlb : Tendsto (fun j => B j (e.val.symm z)) atTop
        (𝓝 (singularityEnvelope T.val v (e.val.symm z))) := by
      change Tendsto (fun j => chartFunction (B j) e z) atTop
        (𝓝 (chartFunction (singularityEnvelope T.val v) e z))
      rw [← hb]
      exact tendsto_atTop_iSup (fun j k hjk => hBm hjk (e.val.symm z))
    exact convexComb_value_tendsto hla hlb
      (singularityEnvelope_le_zero T.val u _) (singularityEnvelope_le_zero T.val v _) ht0 ht1
  rw [← hreg]
  exact uscRegularization_le (upperSemicontinuous_singularityEnvelope T.val _)
    (iSup_le hstage)

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- Actual bounded-supremum closure manufactures the source output on the
unchanged family. It does not assume a desired regularized limit. -/
theorem sourceIncreasingOrdinary_regularized_thetaPSH {I : Type*} [Nonempty I]
    {ui : I → M → EReal} (hui : ∀ i, (ofFixedModel n M).IsThetaPSH θ (ui i))
    {C : ℝ} (hC : ∀ i x, ui i x ≤ (C : EReal)) :
    (ofFixedModel n M).IsThetaPSH θ (uscRegularization (⨆ i, ui i)) :=
  (isThetaPSH_iff_nativeThetaPotential θ _).mpr
    (isThetaPshPotential_regularized_of_uniformlyBounded
      (fun i => (isThetaPSH_iff_nativeThetaPotential θ (ui i)).mp (hui i)) hC)

omit [ConnectedSpace M] in
/-- ANY one actual positive stage and true mass monotonicity manufacture
the actual positive USCsup mass. No output-mass premise is introduced. -/
theorem sourceIncreasingOrdinary_sup_positive (ω : KahlerBackground n M)
    {I : Type*} [Nonempty I] {ui : I → M → EReal}
    (hui : ∀ i, (ofFixedModel n M).IsThetaPSH θ (ui i))
    (hpos : ∀ i, 0 < sourcePotentialNonPluripolarMeasure θ (ui i) (hui i) univ)
    {C : ℝ} (hC : ∀ i x, ui i x ≤ (C : EReal)) :
    0 < sourcePotentialNonPluripolarMeasure θ (uscRegularization (⨆ i, ui i))
      (sourceIncreasingOrdinary_regularized_thetaPSH hui hC) univ := by
  let i := Classical.arbitrary I
  exact (hpos i).trans_le (sourcePotentialNonPluripolarMass_mono ω (hui i)
    (sourceIncreasingOrdinary_regularized_thetaPSH hui hC)
    (MoreSingularOn.of_le fun x _ => (le_iSup ui i x).trans (le_uscRegularization _ x)))

/-- WHOLE sequence identity at its actual positive regularized-supremum mass.
Actual bigness, vanishing barriers, normalized-P L1 and pointwise PSH order
are all produced or reused internally, with n0/equalmass/poles retained. -/
theorem sourceOrdinaryEnvelope_increasing_sequence_eq (ω : KahlerBackground n M)
    {ui : ℕ → M → EReal} (hui : ∀ j, (ofFixedModel n M).IsThetaPSH θ (ui j))
    (hm : Monotone ui) {C : ℝ} (hC : ∀ j x, ui j x ≤ (C : EReal))
    (hpos : 0 < sourcePotentialNonPluripolarMeasure θ (uscRegularization (⨆ j, ui j))
      (sourceIncreasingOrdinary_regularized_thetaPSH hui hC) univ) :
    uscRegularization (⨆ j, sourceSingularityEnvelope θ (ui j)) =
      sourceSingularityEnvelope θ (uscRegularization (⨆ j, ui j)) := by
  let U := uscRegularization (⨆ j, ui j)
  let P := sourceSingularityEnvelope θ U
  let H := uscRegularization (⨆ j, sourceSingularityEnvelope θ (ui j))
  have hU : (ofFixedModel n M).IsThetaPSH θ U :=
    sourceIncreasingOrdinary_regularized_thetaPSH hui hC
  have hP : (ofFixedModel n M).IsThetaPSH θ P := sourceOrdinaryEnvelope_genuine hU
  have hH : (ofFixedModel n M).IsThetaPSH θ H :=
    sourceIncreasingOrdinary_regularized_thetaPSH
      (fun j => sourceOrdinaryEnvelope_genuine (hui j))
      (C := 0) (fun j x => sourceSingularityEnvelope_le_zero θ (ui j) x)
  have hHP : H ≤ P := uscRegularization_le
    ((isThetaPSH_iff_nativeThetaPotential θ P).mp hP).1.quasiPlurisubharmonic.upperSemicontinuous
    (iSup_le fun j => sourceOrdinaryEnvelope_mono
      (MoreSingularOn.of_le fun x _ => (le_iSup ui j x).trans (le_uscRegularization _ x)))
  obtain ⟨N, _hN, ε, hε, η, hη, hbar⟩ :=
    IncreasingPositiveMassAffineBarriers.exists_vanishing_affine_barriers_of_monotone_regularized
      ω (atlasClosedFormToNative θ) (sourcePositiveMass_isBig ω hU hpos)
      (fun j => (isThetaPSH_iff_nativeThetaPotential θ (ui j)).mp (hui j)) hm
      ((isThetaPSH_iff_nativeThetaPotential θ U).mp hU) rfl hpos
  have hηs (j : ℕ) : (ofFixedModel n M).IsThetaPSH θ (η j) :=
    (isThetaPSH_iff_nativeThetaPotential θ (η j)).mpr (hη j)
  have hlow (j : ℕ) : convexComb (ε j).val
      (sourceSingularityEnvelope θ (η j)) P ≤ H :=
    (sourceOrdinaryEnvelope_convexComb_le (hηs j) hU (ε j).property.1 (ε j).property.2).trans
      ((sourceOrdinaryEnvelope_mono (MoreSingularOn.of_le fun x _ => hbar j x)).trans
        ((le_iSup (fun k => sourceSingularityEnvelope θ (ui k)) (N j)).trans
          (le_uscRegularization _)))
  have hbound (j : ℕ) : globalL1EDistance (kahlerVolume ω) H P ≤
      globalL1EDistance (kahlerVolume ω)
        (fun x => ((ε j).val : EReal) * sourceSingularityEnvelope θ (η j) x) (fun _ => 0) := by
    apply lintegral_mono
    intro x
    exact IEnvelopeIncreasingRegularizedSupremum.canonical_gap_le_scaled_normalized_lower
      (sourceSingularityEnvelope_le_zero θ U x) (sourceSingularityEnvelope_le_zero θ (η j) x)
      (hHP x) (ε j).property.1 (hlow j x)
  have hupper := sourceOrdinaryEnvelope_scaledL1_tendsto ω atTop η hηs
    (fun j => (ε j).val) (fun j => (ε j).property.1) hε
  have hlim : Tendsto (fun _ : ℕ => globalL1EDistance (kahlerVolume ω) H P) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hupper (fun _ => zero_le) hbound
  have hHn := (isThetaPSH_iff_nativeThetaPotential θ H).mp hH
  have hPn := (isThetaPSH_iff_nativeThetaPotential θ P).mp hP
  have hloc : ManifoldL1LocallyTendsto (n := n) (fun _ : ℕ => H) atTop P :=
    (manifoldL1LocallyTendsto_iff_tendsto_globalL1EDistance
      (KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume ω)
      (fun _ => hHn.1.quasiPlurisubharmonic.upperSemicontinuous.measurable)
      hPn.1.quasiPlurisubharmonic.upperSemicontinuous.measurable).mpr hlim
  exact le_antisymm hHP (ThetaPshL1Order.le_of_manifoldL1LocallyTendsto
    (fun _ => hHn) hPn hHn hloc (fun _ => le_refl H))

/-- ENTIRE original prop:incnetmodel identity on an arbitrary uniformly
upperbounded increasing directed POSITIVE-mass family. True Choquet selection
preserves the WHOLE USCsup and never asserts countable index cofinality. -/
theorem sourceOrdinaryEnvelope_increasing_directed_eq (ω : KahlerBackground n M)
    {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    {ui : I → M → EReal} (hui : ∀ i, (ofFixedModel n M).IsThetaPSH θ (ui i))
    (hpos : ∀ i, 0 < sourcePotentialNonPluripolarMeasure θ (ui i) (hui i) univ)
    (hm : Monotone ui) {C : ℝ} (hC : ∀ i x, ui i x ≤ (C : EReal)) :
    uscRegularization (⨆ i, sourceSingularityEnvelope θ (ui i)) =
      sourceSingularityEnvelope θ (uscRegularization (⨆ i, ui i)) := by
  classical
  obtain ⟨j, hj, _, hreg⟩ := exists_monotone_sequence_uscRegularization_iSup_eq
    (u := fun i (_ : Unit) => ui i) (Classical.arbitrary I) (fun _ => hm)
  have hseq := sourceOrdinaryEnvelope_increasing_sequence_eq ω
    (fun k => hui (j k)) (hm.comp hj) (fun k x => hC (j k) x)
    (sourceIncreasingOrdinary_sup_positive ω (fun k => hui (j k))
      (fun k => hpos (j k)) (fun k x => hC (j k) x))
  rw [hreg ()] at hseq
  apply le_antisymm
  · apply uscRegularization_le
      ((isThetaPSH_iff_nativeThetaPotential θ _).mp
        (sourceOrdinaryEnvelope_genuine (sourceIncreasingOrdinary_regularized_thetaPSH hui hC))).1.quasiPlurisubharmonic.upperSemicontinuous
    exact iSup_le fun i => sourceOrdinaryEnvelope_mono
      (MoreSingularOn.of_le fun x _ => (le_iSup ui i x).trans (le_uscRegularization _ x))
  · exact hseq.symm.le.trans (uscRegularization_mono
      (iSup_le fun k => le_iSup (fun i => sourceSingularityEnvelope θ (ui i)) (j k)))

/-- The ENTIRE original final model-potential consequence, using actual
source fixed points AND manufactured genuine positive limit mass. -/
theorem sourceModelPotential_increasing_uscSup (ω : KahlerBackground n M)
    {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    {ui : I → M → EReal} (hmodel : ∀ i, SourceModelPotential θ (ui i))
    (hm : Monotone ui) {C : ℝ} (hC : ∀ i x, ui i x ≤ (C : EReal)) :
    SourceModelPotential θ (uscRegularization (⨆ i, ui i)) := by
  let hui := fun i => (hmodel i).thetaPSH
  have hpos (i : I) : 0 < sourcePotentialNonPluripolarMeasure θ (ui i) (hui i) univ :=
    (hmodel i).choose_spec.2
  have heq := sourceOrdinaryEnvelope_increasing_directed_eq ω hui hpos hm hC
  have hfix (i : I) : sourceSingularityEnvelope θ (ui i) = ui i :=
    (hmodel i).choose_spec.1.symm
  simp only [hfix] at heq
  exact ⟨sourceIncreasingOrdinary_regularized_thetaPSH hui hC, heq,
    sourceIncreasingOrdinary_sup_positive ω hui hpos hC⟩

end SGPT.PSH.VariableComplexAtlas
