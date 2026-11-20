import SGPT.Bergman.SourcePartialEnvelopeBounds
import SGPT.Bergman.SourceWeightedSubset
import SGPT.Envelopes.SourceIncreasingOrdinaryEnvelopes
import SGPT.PSH.SourceSingularityDistanceConvergence
import SGPT.PSH.SourceIEnvelopeSingularityContinuity
import SGPT.Bergman.SourcePartialEnvelopeEverywhere
import SGPT.Foundations.Analysis.Pending.KahlerVolumeChartAEEquivalence

/-! Local P01 candidate. The complete mathematical route precedes this file in
`monotone-convergence.tex`. No source-index or coverage claim is made here. -/
set_option autoImplicit false
noncomputable section

namespace SGPT.Bergman.MonotonePartialEnvelopes

open Set Filter MeasureTheory SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Bergman.PartialEnvelope SGPT.Bergman.PartialEnvelopeRetention
open SGPT.Bergman.PartialEnvelopeSameType SGPT.Bergman.PartialEnvelopeUniformBound
open SGPT.Bergman.PartialEnvelopeConcavityConsumer
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending ThetaPshConvexCombination
open ChartwiseGlobalL1 IntegrationCurrent IncreasingMixedDirectedNets
open scoped Topology ENNReal

universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]

/-- One implementation of the two literal original partial operators. -/
def partialChoice (ideal : Bool) (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (φ : M → EReal) (K : Set M) (f : K → EReal) : M → EReal :=
  if ideal then partialIEnvelope θ φ K f else partialEnvelope θ φ K f

omit [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in
private theorem choice_usc (ideal : Bool)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (φ : M → EReal)
    (K : Set M) (f : K → EReal) : UpperSemicontinuous (partialChoice ideal θ φ K f) := by
  cases ideal <;> simp only [partialChoice, Bool.false_eq_true, if_false, if_true]
  · exact upperSemicontinuous_partialEnvelope θ φ K f
  · exact upperSemicontinuous_partialIEnvelope θ φ K f

omit [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in
private theorem choice_mono (ideal : Bool)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ ψ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ)
    (hψ : (ofFixedModel n M).IsThetaPSH θ ψ) (K : Set M) (f : K → EReal)
    (h : SGPT.PSH.SingularityLE φ ψ) :
    partialChoice ideal θ φ K f ≤ partialChoice ideal θ ψ K f := by
  cases ideal
  · change partialEnvelope θ φ K f ≤ partialEnvelope θ ψ K f
    apply uscRegularization_le (upperSemicontinuous_partialEnvelope θ ψ K f)
    intro x
    apply iSup_le
    intro v
    exact le_partialEnvelope v.property.1 v.property.2.1 (v.property.2.2.trans h) x
  · exact partialIEnvelope_mono_reference θ K f (sourceIOrder_of_singularityLE hφ hψ h)

omit [MeasurableSpace M] [BorelSpace M] in
private theorem choice_concave (ideal : Bool)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ ψ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ)
    (hψ : (ofFixedModel n M).IsThetaPSH θ ψ) (K : Set M) (f : K → EReal)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    convexComb t (partialChoice ideal θ φ K f) (partialChoice ideal θ ψ K f) ≤
      partialChoice ideal θ (convexComb t φ ψ) K f := by
  cases ideal
  · exact (partialEnvelopes_convexComb hφ hψ K f ht0 ht1).1
  · exact (partialEnvelopes_convexComb hφ hψ K f ht0 ht1).2

private theorem uscSup_add_const {I X : Type*} [TopologicalSpace X]
    (v : I → X → EReal) (c : ℝ) :
    uscSup (fun i x => v i x + (c : EReal)) = fun x => uscSup v x + (c : EReal) := by
  have heq : (fun x => ⨆ i, v i x + (c : EReal)) =
      fun x => (⨆ i, v i x) + (c : EReal) := by
    funext x
    exact iSup_add_coe (fun i => v i x) c
  change uscRegularization (fun x => ⨆ i, v i x + (c : EReal)) = _
  rw [heq, uscRegularization_add_coe_const]
  rfl

omit [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- Actual lower normalized P-barriers work for zero-mass references too. -/
theorem lower_normalized_envelope (ideal : Bool)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ) {K : Set M} {f : K → EReal}
    {L : ℝ} (hL : ∀ x : K, (L : EReal) ≤ f x) :
    (fun x => sourceSingularityEnvelope θ φ x + (L : EReal)) ≤
      partialChoice ideal θ φ K f := by
  have hP : (fun x => sourceSingularityEnvelope θ φ x + (L : EReal)) ≤
      partialEnvelope θ φ K f := by
    have hs : uscSup (fun a : sourceSingularityCompetitors θ φ =>
        fun x => a.val x + (L : EReal)) ≤ partialEnvelope θ φ K f := by
      apply uscRegularization_le (upperSemicontinuous_partialEnvelope θ φ K f)
      intro x
      apply iSup_le
      intro a
      have ha := sourceThetaPSH_add_const a.property.1 L
      have haK : ∀ y : K, a.val y.val + (L : EReal) ≤ f y := by
        intro y
        have hbound : a.val y.val + (L : EReal) ≤ (L : EReal) := by
          simpa only [Pi.zero_apply, zero_add] using
            add_le_add (a.property.2.1 y.val) (le_refl (L : EReal))
        exact hbound.trans (hL y)
      exact le_partialEnvelope ha (partialObstacle_of_forall haK)
        ((show SGPT.PSH.SingularityLE (fun y => a.val y + (L : EReal)) a.val from
          ⟨L, fun _ _ => le_rfl⟩).trans a.property.2.2) x
    rw [uscSup_add_const] at hs
    exact hs
  cases ideal
  · exact hP
  · exact hP.trans (partialEnvelope_le_partialIEnvelope hφ K f)

omit [MeasurableSpace M] [BorelSpace M] in
/-- Genuine reference and actual real obstacle bounds supply BOTH genuine
outputs; positive reference mass is not needed for this auxiliary fact. -/
theorem choice_genuine (ideal : Bool)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ) {K : Set M}
    (hK : (ofFixedModel n M).NonPluripolar K) {f : K → EReal}
    (hlo : ∃ L : ℝ, ∀ x : K, (L : EReal) ≤ f x)
    (hup : ∃ U : ℝ, ∀ x : K, f x ≤ (U : EReal)) :
    (ofFixedModel n M).IsThetaPSH θ (partialChoice ideal θ φ K f) := by
  obtain ⟨L, hL⟩ := hlo
  obtain ⟨A, hA⟩ := ((isThetaPSH_iff_nativeThetaPotential θ φ).mp hφ).exists_global_upper_bound
  let c := L - A
  have hχ := sourceThetaPSH_add_const hφ c
  have hχK : partialObstacle (n := n) K f (fun x => φ x + (c : EReal)) := by
    apply partialObstacle_of_forall
    intro x
    apply le_trans (add_le_add (hA x.val) le_rfl)
    have heq : (A : EReal) + (c : EReal) = (L : EReal) := by
      rw [← EReal.coe_add]
      congr 1
      dsimp only [c]
      ring_nf
    exact heq.le.trans (hL x)
  have hχφ : SGPT.PSH.SingularityLE (fun x => φ x + (c : EReal)) φ :=
    ⟨c, fun _ _ => le_rfl⟩
  cases ideal
  · let : Nonempty (partialCompetitors θ φ K f) := ⟨⟨_, hχ, hχK, hχφ⟩⟩
    exact (boundedFamily_of_partialObstacle hK hup
      (fun a : partialCompetitors θ φ K f => a.property.1)
      (fun a => a.property.2.1)).choose_spec.2.2
  · let : Nonempty (partialICompetitors θ φ K f) :=
      ⟨⟨_, hχ, hχK, sourceIOrder_of_singularityLE hχ hφ hχφ⟩⟩
    exact (boundedFamily_of_partialObstacle hK hup
      (fun a : partialICompetitors θ φ K f => a.property.1)
      (fun a => a.property.2.1)).choose_spec.2.2

omit [MeasurableSpace M] [BorelSpace M] in
private theorem choice_bound (ideal : Bool)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) {K : Set M}
    (hK : (ofFixedModel n M).NonPluripolar K) (U : ℝ)
    (φ : M → EReal) (f : K → EReal) (hf : ∀ x, f x ≤ (U : EReal)) :
    partialChoice ideal θ φ K f ≤ fun _ => (uniformUpperBound θ hK U : EReal) := by
  cases ideal
  · exact (partialEnvelopes_le_uniformUpperBound θ hK U φ f hf).1
  · exact (partialEnvelopes_le_uniformUpperBound θ hK U φ f hf).2

/-- The true uniform Harnack-volume theorem controls the fixed finite
translate of normalized ordinary P, before any scalar readback. -/
theorem shifted_normalized_scaledL1_tendsto (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    (a : ℕ → M → EReal) (ha : ∀ j, (ofFixedModel n M).IsThetaPSH θ (a j))
    (D : ℝ) (hD : 0 ≤ D) (ε : ℕ → ℝ) (hεpos : ∀ j, 0 < ε j)
    (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun j => globalL1EDistance (kahlerVolume ω)
      (fun x => (ε j : EReal) * (sourceSingularityEnvelope θ (a j) x + ((-D : ℝ) : EReal)))
      (fun _ => 0)) atTop (𝓝 0) := by
  let b : ℕ → M → EReal := fun j x => sourceSingularityEnvelope θ (a j) x + ((-D : ℝ) : EReal)
  have hb (j) : (ofFixedModel n M).IsThetaPSH θ (b j) :=
    sourceThetaPSH_add_const (sourceOrdinaryEnvelope_genuine (ha j)) (-D)
  have hb0 (j) (x) : b j x ≤ 0 := by
    exact (add_le_add (sourceSingularityEnvelope_le_zero θ (a j) x)
      (EReal.coe_nonpos.mpr (neg_nonpos.mpr hD))).trans_eq (zero_add 0)
  obtain ⟨B, hB, hBv⟩ := SingularModelUniformModelL1.exists_uniform_lintegral_neg_le_kahlerVolume
    (atlasClosedFormToNative θ) ω D
  have hbound (j) : globalL1EDistance (kahlerVolume ω)
      (fun x => (ε j : EReal) * b j x) (fun _ => 0) ≤ ENNReal.ofReal (ε j) * B := by
    have hbint : (∫⁻ x, (-b j x).toENNReal ∂kahlerVolume ω) ≤ B := by
      apply hBv _ ((isThetaPSH_iff_nativeThetaPotential θ _).mp (hb j)).1 (hb0 j)
      obtain ⟨x, hx⟩ := sourceOrdinaryEnvelope_hasZero (ha j)
      exact ⟨x, by simp only [b, hx, zero_add, le_refl]⟩
    calc
      _ = ∫⁻ x, ENNReal.ofReal (ε j) * (-b j x).toENNReal ∂kahlerVolume ω := by
        apply lintegral_congr_ae
        have hfin := sourceThetaPSH_ae_finite_kahlerVolume ω (hb j)
        filter_upwards [hfin] with x hx
        let p : ℝ := (b j x).toReal
        have hp : (p : EReal) = b j x := EReal.coe_toReal hx.1 hx.2
        have hp0 : p ≤ 0 := EReal.coe_le_coe_iff.mp (hp ▸ hb0 j x)
        rw [← hp, ← EReal.coe_mul, ← EReal.coe_zero, canonicalERealAbsDiff_coe_coe,
          sub_zero, abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (hεpos j).le hp0),
          ← EReal.coe_neg, EReal.real_coe_toENNReal, ← ENNReal.ofReal_mul (hεpos j).le]
        congr 1
        ring_nf
      _ = ENNReal.ofReal (ε j) * (∫⁻ x, (-b j x).toENNReal ∂kahlerVolume ω) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (ε j) * B := mul_le_mul' le_rfl hbint
  have he : Tendsto (fun j => ENNReal.ofReal (ε j)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto 0).comp hε
  have hupper : Tendsto (fun j => ENNReal.ofReal (ε j) * B) atTop (𝓝 0) := by
    simpa only [zero_mul] using ENNReal.Tendsto.mul_const he (Or.inr hB.ne)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun _ => zero_le) hbound

/-- Increasing references with their ACTUAL positive regularized supremum
produce literal equality for BOTH original partial operators. -/
theorem choice_increasing_regularized_eq (ideal : Bool) (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    {ui : ℕ → M → EReal} {u : M → EReal}
    (hui : ∀ j, (ofFixedModel n M).IsThetaPSH θ (ui j)) (hm : Monotone ui)
    (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hreg : uscRegularization (⨆ j, ui j) = u)
    (hpos : 0 < sourcePotentialNonPluripolarMeasure θ u hu univ)
    {K : Set M} (hK : (ofFixedModel n M).NonPluripolar K) {f : K → EReal}
    (hlo : ∃ L : ℝ, ∀ x : K, (L : EReal) ≤ f x)
    (hup : ∃ U : ℝ, ∀ x : K, f x ≤ (U : EReal)) :
    uscRegularization (⨆ j, partialChoice ideal θ (ui j) K f) = partialChoice ideal θ u K f := by
  obtain ⟨L, hL⟩ := hlo
  obtain ⟨U, hU⟩ := hup
  let F := fun v => partialChoice ideal θ v K f
  let A := F u
  let H := uscRegularization (⨆ j, F (ui j))
  have hA : (ofFixedModel n M).IsThetaPSH θ A := choice_genuine ideal hu hK ⟨L, hL⟩ ⟨U, hU⟩
  have hF (j) : (ofFixedModel n M).IsThetaPSH θ (F (ui j)) :=
    choice_genuine ideal (hui j) hK ⟨L, hL⟩ ⟨U, hU⟩
  let C₀ := uniformUpperBound θ hK U
  have hFbound (v) : F v ≤ fun _ => (C₀ : EReal) := choice_bound ideal θ hK U v f hU
  have hH : (ofFixedModel n M).IsThetaPSH θ H :=
    sourceIncreasingOrdinary_regularized_thetaPSH hF (fun j x => hFbound (ui j) x)
  have hui_u (j) : ui j ≤ u := by
    rw [← hreg]
    exact (le_iSup ui j).trans (le_uscRegularization _)
  have hHA : H ≤ A := uscRegularization_le (choice_usc ideal θ u K f)
    (iSup_le fun j => choice_mono ideal (hui j) hu K f
      (MoreSingularOn.of_le fun x _ => hui_u j x))
  obtain ⟨N, _hN, ε, hε, a, ha, hbar⟩ :=
    IncreasingPositiveMassAffineBarriers.exists_vanishing_affine_barriers_of_monotone_regularized
      ω (atlasClosedFormToNative θ) (sourcePositiveMass_isBig ω hu hpos)
      (fun j => (isThetaPSH_iff_nativeThetaPotential θ _).mp (hui j)) hm
      ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu) hreg hpos
  have has (j) : (ofFixedModel n M).IsThetaPSH θ (a j) :=
    (isThetaPSH_iff_nativeThetaPotential θ _).mpr (ha j)
  have hlow (j) : convexComb (ε j).val
      (fun x => sourceSingularityEnvelope θ (a j) x + (L : EReal)) A ≤ H := by
    have hcomb : (ofFixedModel n M).IsThetaPSH θ (convexComb (ε j).val (a j) u) :=
      (isThetaPSH_iff_nativeThetaPotential θ _).mpr
        (isThetaPshPotential_convexComb (ha j) ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu)
          (ε j).property.1 (ε j).property.2)
    exact (convexComb_mono (ε j).property.1.le (ε j).property.2.le
      (lower_normalized_envelope ideal (has j) hL) le_rfl).trans
      ((choice_concave ideal (has j) hu K f (ε j).property.1 (ε j).property.2).trans
        ((choice_mono ideal hcomb (hui (N j)) K f
          (MoreSingularOn.of_le fun x _ => hbar j x)).trans
          ((le_iSup (fun k => F (ui k)) (N j)).trans (le_uscRegularization _))))
  let C : ℝ := max C₀ L
  let D : ℝ := C - L
  have hD : 0 ≤ D := sub_nonneg.mpr (le_max_right _ _)
  let A' : M → EReal := fun x => A x + ((-C : ℝ) : EReal)
  let H' : M → EReal := fun x => H x + ((-C : ℝ) : EReal)
  have hA' := sourceThetaPSH_add_const hA (-C)
  have hH' := sourceThetaPSH_add_const hH (-C)
  have hA0 (x) : A' x ≤ 0 := by
    have hAC : A x ≤ (C : EReal) := (hFbound u x).trans
      (EReal.coe_le_coe_iff.mpr (le_max_left _ _))
    simpa only [A', ← EReal.coe_add, add_neg_cancel, EReal.coe_zero] using
      add_le_add hAC (le_refl ((-C : ℝ) : EReal))
  have hH'A' : H' ≤ A' := fun x => add_le_add (hHA x) le_rfl
  have hlow' (j) : convexComb (ε j).val
      (fun x => sourceSingularityEnvelope θ (a j) x + ((-D : ℝ) : EReal)) A' ≤ H' := by
    have heq (x) : sourceSingularityEnvelope θ (a j) x + ((-D : ℝ) : EReal) =
        (sourceSingularityEnvelope θ (a j) x + (L : EReal)) + ((-C : ℝ) : EReal) := by
      rw [add_assoc, ← EReal.coe_add]
      congr 1
      dsimp only [D]
      ring_nf
    have hc := POrderAffineRooftop.convexComb_add_const (ε j).property.1 (ε j).property.2
      (fun x => sourceSingularityEnvelope θ (a j) x + (L : EReal)) A (-C) (-C)
    have hcc : (ε j).val * -C + (1 - (ε j).val) * -C = -C := by ring_nf
    rw [hcc] at hc
    intro x
    change convexComb (ε j).val _ _ x ≤ H x + ((-C : ℝ) : EReal)
    simp_rw [heq]
    rw [hc]
    exact add_le_add (hlow j x) le_rfl
  have hbound (j) : globalL1EDistance (kahlerVolume ω) H' A' ≤
      globalL1EDistance (kahlerVolume ω)
        (fun x => ((ε j).val : EReal) *
          (sourceSingularityEnvelope θ (a j) x + ((-D : ℝ) : EReal))) (fun _ => 0) := by
    apply lintegral_mono
    intro x
    apply IEnvelopeIncreasingRegularizedSupremum.canonical_gap_le_scaled_normalized_lower
      (hA0 x) _ (hH'A' x) (ε j).property.1 (hlow' j x)
    exact (add_le_add (sourceSingularityEnvelope_le_zero θ (a j) x)
      (EReal.coe_nonpos.mpr (neg_nonpos.mpr hD))).trans_eq (zero_add 0)
  have hupper := shifted_normalized_scaledL1_tendsto ω a has D hD
    (fun j => (ε j).val) (fun j => (ε j).property.1) hε
  have hlim : Tendsto (fun _ : ℕ => globalL1EDistance (kahlerVolume ω) H' A') atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
      (fun _ => zero_le) hbound
  have hHn := (isThetaPSH_iff_nativeThetaPotential θ H').mp hH'
  have hAn := (isThetaPSH_iff_nativeThetaPotential θ A').mp hA'
  have hloc : ManifoldL1LocallyTendsto (n := n) (fun _ : ℕ => H') atTop A' :=
    (manifoldL1LocallyTendsto_iff_tendsto_globalL1EDistance
      (KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume ω)
      (fun _ => hHn.1.quasiPlurisubharmonic.upperSemicontinuous.measurable)
      hAn.1.quasiPlurisubharmonic.upperSemicontinuous.measurable).mpr hlim
  have hAH' : A' ≤ H' := ThetaPshL1Order.le_of_manifoldL1LocallyTendsto
    (fun _ => hHn) hAn hHn hloc (fun _ => le_refl H')
  apply le_antisymm hHA
  intro x
  have h := add_le_add (hAH' x) (le_refl (C : EReal))
  simpa only [A', H', add_assoc, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero,
    add_zero] using h



/-- Original-volume AE increasing input convergence produces BOTH the exact
regularized-supremum identity and actual AE pointwise output convergence. -/
theorem choice_increasing_original (ideal : Bool) (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    {ui : ℕ → M → EReal} {u : M → EReal}
    (hui : ∀ j, (ofFixedModel n M).IsThetaPSH θ (ui j)) (hm : Monotone ui)
    (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hpos : 0 < sourcePotentialNonPluripolarMeasure θ u hu univ)
    (hae : ∀ᵐ x ∂sourceKahlerVolume ω, Tendsto (fun j => ui j x) atTop (𝓝 (u x)))
    {K : Set M} (hK : (ofFixedModel n M).NonPluripolar K) {f : K → EReal}
    (hlo : ∃ L : ℝ, ∀ x : K, (L : EReal) ≤ f x)
    (hup : ∃ U : ℝ, ∀ x : K, f x ≤ (U : EReal)) :
    Monotone (fun j => partialChoice ideal θ (ui j) K f) ∧
      uscRegularization (⨆ j, partialChoice ideal θ (ui j) K f) = partialChoice ideal θ u K f ∧
      ∀ᵐ x ∂sourceKahlerVolume ω,
        Tendsto (fun j => partialChoice ideal θ (ui j) K f x) atTop
          (𝓝 (partialChoice ideal θ u K f x)) := by
  have huin (j) := (isThetaPSH_iff_nativeThetaPotential θ _).mp (hui j)
  have hun := (isThetaPSH_iff_nativeThetaPotential θ _).mp hu
  have haen := hae
  rw [sourceKahlerVolume_eq_native] at haen
  have hreg : uscRegularization (⨆ j, ui j) = u :=
    SingularModelIncreasingAERegularizedLimit.uscRegularization_iSup_eq_of_monotone_ae_chart_tendsto
      huin hun (fun x j k hjk => hm hjk x)
      (fun e => KahlerVolumeChartAEEquivalence.ae_chartTarget_of_ae_kahlerVolume ω e haen)
  have heq := choice_increasing_regularized_eq ideal ω hui hm hu hreg hpos hK hlo hup
  have hmF : Monotone (fun j => partialChoice ideal θ (ui j) K f) := fun j k hjk =>
    choice_mono ideal (hui j) (hui k) K f (MoreSingularOn.of_le fun x _ => hm hjk x)
  have hF (j) := choice_genuine ideal (hui j) hK hlo hup
  have hA := choice_genuine ideal hu hK hlo hup
  have hH : (ofFixedModel n M).IsThetaPSH θ
      (uscRegularization (⨆ j, partialChoice ideal θ (ui j) K f)) := heq.symm ▸ hA
  have hmFmeas (j) : Measurable (partialChoice ideal θ (ui j) K f) :=
    (choice_usc ideal θ (ui j) K f).measurable
  have hAmeas : Measurable (partialChoice ideal θ u K f) :=
    (choice_usc ideal θ u K f).measurable
  have haesup : ∀ᵐ x ∂kahlerVolume ω,
      (⨆ j, partialChoice ideal θ (ui j) K f x) = partialChoice ideal θ u K f x := by
    apply (KahlerVolumeChartAEEquivalence.ae_kahlerVolume_iff_forall_chart_ae ω
      (measurableSet_eq_fun (Measurable.iSup hmFmeas) hAmeas)).mpr
    intro e
    have h := IncreasingMixedRegularizedContinuity.ae_chartFunction_iSup_eq_of_genuine
      (fun j => (isThetaPSH_iff_nativeThetaPotential θ _).mp (hF j)) hmF
      ((isThetaPSH_iff_nativeThetaPotential θ _).mp hH) e
    rw [heq] at h
    exact h
  refine ⟨hmF, heq, ?_⟩
  rw [sourceKahlerVolume_eq_native]
  filter_upwards [haesup] with x hx
  rw [← hx]
  exact tendsto_atTop_iSup (fun j k hjk => hmF hjk x)

/-- Both original increasing conclusions at an actual original weighted
subset. Weight bounds are manufactured from compactness, internally. -/
theorem partialEnvelopes_increasing (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    {ui : ℕ → M → EReal} {u : M → EReal}
    (hui : ∀ j, (ofFixedModel n M).IsThetaPSH θ (ui j))
    (_huipos : ∀ j, 0 < sourcePotentialNonPluripolarMeasure θ (ui j) (hui j) univ)
    (hm : Monotone ui) (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hpos : 0 < sourcePotentialNonPluripolarMeasure θ u hu univ)
    (hae : ∀ᵐ x ∂sourceKahlerVolume ω, Tendsto (fun j => ui j x) atTop (𝓝 (u x)))
    (W : SGPT.Bergman.WeightedSubset.WeightedSubset n M) :
    (Monotone (fun j => partialEnvelope θ (ui j) W.carrier W.erealWeight) ∧
      uscRegularization (⨆ j, partialEnvelope θ (ui j) W.carrier W.erealWeight) =
        partialEnvelope θ u W.carrier W.erealWeight ∧
      ∀ᵐ x ∂sourceKahlerVolume ω,
        Tendsto (fun j => partialEnvelope θ (ui j) W.carrier W.erealWeight x) atTop
          (𝓝 (partialEnvelope θ u W.carrier W.erealWeight x))) ∧
    (Monotone (fun j => partialIEnvelope θ (ui j) W.carrier W.erealWeight) ∧
      uscRegularization (⨆ j, partialIEnvelope θ (ui j) W.carrier W.erealWeight) =
        partialIEnvelope θ u W.carrier W.erealWeight ∧
      ∀ᵐ x ∂sourceKahlerVolume ω,
        Tendsto (fun j => partialIEnvelope θ (ui j) W.carrier W.erealWeight x) atTop
          (𝓝 (partialIEnvelope θ u W.carrier W.erealWeight x))) := by
  obtain ⟨L, U, hL, hU⟩ := W.partialEnvelope_weight_bounds
  exact ⟨choice_increasing_original false ω hui hm hu hpos hae W.nonPluripolar_carrier
      ⟨L, hL⟩ ⟨U, hU⟩,
    choice_increasing_original true ω hui hm hu hpos hae W.nonPluripolar_carrier
      ⟨L, hL⟩ ⟨U, hU⟩⟩




/-- The original normalized ordinary and ideal envelopes, kept distinct. -/
def normalizedChoice (ideal : Bool) (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (φ : M → EReal) : M → EReal :=
  if ideal then sourceIEnvelope θ φ else sourceSingularityEnvelope θ φ

omit [MeasurableSpace M] [BorelSpace M] in
/-- Actual common C(theta,K,U) gives the upper additive comparison to the
correct normalized envelope for every genuine reference, even at zero mass. -/
theorem choice_le_normalized (ideal : Bool)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ) {K : Set M}
    (hK : (ofFixedModel n M).NonPluripolar K) (U : ℝ) {f : K → EReal}
    (hf : ∀ x, f x ≤ (U : EReal)) :
    partialChoice ideal θ φ K f ≤ fun x =>
      normalizedChoice ideal θ φ x + (uniformUpperBound θ hK U : EReal) := by
  let C := uniformUpperBound θ hK U
  have hnormalize {a : M → EReal} (ha : a ≤ fun _ => (C : EReal)) :
      (fun x => a x + ((-C : ℝ) : EReal)) ≤ 0 := by
    intro x
    simpa only [← EReal.coe_add, add_neg_cancel, EReal.coe_zero, Pi.zero_apply] using
      add_le_add (ha x) (le_refl ((-C : ℝ) : EReal))
  cases ideal
  · change partialEnvelope θ φ K f ≤ fun x => sourceSingularityEnvelope θ φ x + (C : EReal)
    apply uscRegularization_le
      (upperSemicontinuous_add_coe_const (upperSemicontinuous_sourceSingularityEnvelope θ φ) C)
    intro x
    apply iSup_le
    intro a
    have haC := (le_partialEnvelope a.property.1 a.property.2.1 a.property.2.2).trans
      ((partialEnvelopes_le_uniformUpperBound θ hK U φ f hf).1)
    have ha := sourceThetaPSH_add_const a.property.1 (-C)
    have hmore : SGPT.PSH.SingularityLE (fun y => a.val y + ((-C : ℝ) : EReal)) φ :=
      (show SGPT.PSH.SingularityLE (fun y => a.val y + ((-C : ℝ) : EReal)) a.val from
        ⟨-C, fun _ _ => le_rfl⟩).trans a.property.2.2
    exact POrderAffineRooftop.le_add_coe_of_add_neg_le
      (le_sourceSingularityEnvelope ha (hnormalize haC) hmore x)
  · change partialIEnvelope θ φ K f ≤ fun x => sourceIEnvelope θ φ x + (C : EReal)
    apply uscRegularization_le
      (upperSemicontinuous_add_coe_const (upperSemicontinuous_sourceIEnvelope θ φ) C)
    intro x
    apply iSup_le
    intro a
    have haC := (le_partialIEnvelope a.property.1 a.property.2.1 a.property.2.2).trans
      ((partialEnvelopes_le_uniformUpperBound θ hK U φ f hf).2)
    have ha := sourceThetaPSH_add_const a.property.1 (-C)
    have hI : sourceIOrder (ofFixedModel n M) (fun y => a.val y + ((-C : ℝ) : EReal)) φ :=
      sourceIOrder_trans (sourceIOrder_of_singularityLE ha a.property.1
        ⟨-C, fun _ _ => le_rfl⟩) a.property.2.2
    have hle : (fun y => a.val y + ((-C : ℝ) : EReal)) ≤ sourceIEnvelope θ φ := by
      rw [sourceIEnvelope_eq_sSup_sourceIOrder hφ]
      exact le_sSup ⟨ha, hnormalize haC, hI⟩
    exact POrderAffineRooftop.le_add_coe_of_add_neg_le (hle x)

private theorem sourcePOrder_of_pointwise (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {a b : M → EReal}
    (ha : (ofFixedModel n M).IsThetaPSH θ a) (hb : (ofFixedModel n M).IsThetaPSH θ b)
    (h : a ≤ b) : GlobalPComparison.sourcePOrder (n := n) a b :=
  GlobalPComparison.sourcePOrder_of_moreSingular ω
    ((isThetaPSH_iff_nativeThetaPotential θ a).mp ha).quasiPshPotential
    ((isThetaPSH_iff_nativeThetaPotential θ b).mp hb).quasiPshPotential
    (MoreSingularOn.of_le fun x _ => h x)

/-- The normalized ideal infimum identity follows from genuine I-continuity
and the existing P-envelope infimum theorem; its fixedness is produced by
accepted sourcePEnvelope_iEnvelope rather than supplied as a premise. -/
theorem normalizedChoice_decreasing_infimum (ideal : Bool) (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {ui : ℕ → M → EReal} {u : M → EReal}
    (hui : ∀ j, (ofFixedModel n M).IsThetaPSH θ (ui j)) (hanti : Antitone ui)
    (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hpos : 0 < sourcePotentialNonPluripolarMeasure θ u hu univ)
    (hlim : Tendsto (fun j => (⟨ui j, hui j⟩ : SourceThetaPotentialL1 θ)) atTop
      (@nhds (SourceThetaPotentialL1 θ) (sourceSingularityTopology ω θ hbig) ⟨u, hu⟩)) :
    normalizedChoice ideal θ u = ⨅ j, normalizedChoice ideal θ (ui j) := by
  cases ideal
  · exact sourcePEnvelope_eq_iInf_of_antitone_sourcePOrder_tendsto ω θ hbig
      (fun j => ⟨ui j, hui j⟩) ⟨u, hu⟩
      (fun i j hij => sourcePOrder_of_pointwise ω (hui j) (hui i) (hanti hij)) hlim hpos
  · have hIlim := tendsto_sourceIEnvelope_of_sourceSingularityTopology ω θ hbig atTop
      (fun j => ⟨ui j, hui j⟩) ⟨u, hu⟩ hpos hlim
    have hI (j) := isThetaPSH_sourceIEnvelope (hui j)
    have hIanti : Antitone (fun j => sourceIEnvelope θ (ui j)) := fun i j hij =>
      sourceIEnvelope_mono_of_singularityLE (hui j) (hui i)
        (MoreSingularOn.of_le fun x _ => hanti hij x)
    have hIpos := sourceThetaPotentialIEnvelope_positive_mass ω (⟨u, hu⟩ : SourceThetaPotentialL1 θ) hpos
    have heq := sourcePEnvelope_eq_iInf_of_antitone_sourcePOrder_tendsto ω θ hbig
      (fun j => sourceThetaPotentialIEnvelope (⟨ui j, hui j⟩ : SourceThetaPotentialL1 θ))
      (sourceThetaPotentialIEnvelope (⟨u, hu⟩ : SourceThetaPotentialL1 θ))
      (fun i j hij => sourcePOrder_of_pointwise ω (hI j) (hI i) (hIanti hij)) hIlim hIpos
    change sourceSingularityEnvelope θ (sourceIEnvelope θ u) =
      ⨅ j, sourceSingularityEnvelope θ (sourceIEnvelope θ (ui j)) at heq
    change sourceIEnvelope θ u = ⨅ j, sourceIEnvelope θ (ui j)
    simpa only [sourcePEnvelope_iEnvelope hu, sourcePEnvelope_iEnvelope (hui _)] using heq

/-- A true dS limit of decreasing positive references has the genuine
original global P-order below EVERY stage, without assuming pointwise order. -/
theorem reference_globalP_lower (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {ui : ℕ → M → EReal} {u : M → EReal}
    (hui : ∀ j, (ofFixedModel n M).IsThetaPSH θ (ui j))
    (huipos : ∀ j, 0 < sourcePotentialNonPluripolarMeasure θ (ui j) (hui j) univ)
    (hanti : Antitone ui) (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hpos : 0 < sourcePotentialNonPluripolarMeasure θ u hu univ)
    (hlim : Tendsto (fun j => (⟨ui j, hui j⟩ : SourceThetaPotentialL1 θ)) atTop
      (@nhds (SourceThetaPotentialL1 θ) (sourceSingularityTopology ω θ hbig) ⟨u, hu⟩)) :
    ∀ j, GlobalPComparison.sourcePOrder (n := n) u (ui j) := by
  have heq := normalizedChoice_decreasing_infimum false ω hbig hui hanti hu hpos hlim
  change sourceSingularityEnvelope θ u = ⨅ j, sourceSingularityEnvelope θ (ui j) at heq
  intro j
  apply (GlobalPComparison.sourcePOrder_iff_positive_background ω (atlasClosedFormToNative θ)
    ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu)
    ((isThetaPSH_iff_nativeThetaPotential θ (ui j)).mp (hui j)) hpos (huipos j)).mpr
  change singularityEnvelope (atlasClosedFormToNative θ).val u ≤
    singularityEnvelope (atlasClosedFormToNative θ).val (ui j)
  simp only [← sourceSingularityEnvelope_eq_native]
  rw [heq]
  exact iInf_le _ j

omit [MeasurableSpace M] [BorelSpace M] in
private theorem choice_obstacle (ideal : Bool)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (φ : M → EReal) {K : Set M}
    (hK : (ofFixedModel n M).NonPluripolar K) {f : K → EReal}
    (hup : ∃ U : ℝ, ∀ x : K, f x ≤ (U : EReal)) :
    partialObstacle (n := n) K f (partialChoice ideal θ φ K f) := by
  cases ideal
  · exact partialEnvelope_obstacle θ φ hK hup
  · exact partialIEnvelope_obstacle θ φ hK hup

/-- BOTH decreasing outputs have exact pointwise infimum and EVERYWHERE
convergence, from original reference dS convergence and actual obstacle data. -/
theorem choice_decreasing_original (ideal : Bool) (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {ui : ℕ → M → EReal} {u : M → EReal}
    (hui : ∀ j, (ofFixedModel n M).IsThetaPSH θ (ui j))
    (huipos : ∀ j, 0 < sourcePotentialNonPluripolarMeasure θ (ui j) (hui j) univ)
    (hanti : Antitone ui) (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hpos : 0 < sourcePotentialNonPluripolarMeasure θ u hu univ)
    (hlim : Tendsto (fun j => (⟨ui j, hui j⟩ : SourceThetaPotentialL1 θ)) atTop
      (@nhds (SourceThetaPotentialL1 θ) (sourceSingularityTopology ω θ hbig) ⟨u, hu⟩))
    {K : Set M} (hK : (ofFixedModel n M).NonPluripolar K) {f : K → EReal}
    (hlo : ∃ L : ℝ, ∀ x : K, (L : EReal) ≤ f x)
    (hup : ∃ U : ℝ, ∀ x : K, f x ≤ (U : EReal)) :
    Antitone (fun j => partialChoice ideal θ (ui j) K f) ∧
      (⨅ j, partialChoice ideal θ (ui j) K f) = partialChoice ideal θ u K f ∧
      ∀ x, Tendsto (fun j => partialChoice ideal θ (ui j) K f x) atTop
        (𝓝 (partialChoice ideal θ u K f x)) := by
  let F := fun v => partialChoice ideal θ v K f
  let A := F u
  let L : M → EReal := fun x => ⨅ j, F (ui j) x
  have hA := choice_genuine ideal hu hK hlo hup
  have hF (j) := choice_genuine ideal (hui j) hK hlo hup
  have hantiF : Antitone (fun j => F (ui j)) := fun i j hij =>
    choice_mono ideal (hui j) (hui i) K f (MoreSingularOn.of_le fun x _ => hanti hij x)
  have hreference := reference_globalP_lower ω hbig hui huipos hanti hu hpos hlim
  have hbelow (j) : A ≤ F (ui j) := by
    cases ideal
    · exact partialEnvelope_mono_globalPOrder ω hu (hui j) hpos (huipos j) hlo (hreference j)
    · exact partialIEnvelope_mono_reference θ K f
        (sourceIOrder_of_sourcePOrder ⟨θ, hu⟩ ⟨θ, hui j⟩ (hreference j))
  have hAL : A ≤ L := fun x => le_iInf fun j => hbelow j x
  have hAn := (isThetaPSH_iff_nativeThetaPotential θ A).mp hA
  obtain ⟨x₀, m, hx₀, _hmax⟩ := hAn.exists_max
  have hsup (j) : (m : EReal) ≤ ⨆ x, F (ui j) x :=
    hx₀.symm.le.trans ((hbelow j x₀).trans (le_iSup (F (ui j)) x₀))
  have hLn := (SGPT.PSH.isThetaPshPotential_iInf_of_compact_antitone_iSup_lower_bound
    (fun j => (isThetaPSH_iff_nativeThetaPotential θ _).mp (hF j))
    (fun x j k hjk => hantiF hjk x) m hsup).1
  have hL : (ofFixedModel n M).IsThetaPSH θ L :=
    (isThetaPSH_iff_nativeThetaPotential θ L).mpr hLn
  obtain ⟨U, hU⟩ := hup
  let C := uniformUpperBound θ hK U
  have hnorm := normalizedChoice_decreasing_infimum ideal ω hbig hui hanti hu hpos hlim
  have hupper : L ≤ fun x => normalizedChoice ideal θ u x + (C : EReal) := by
    intro x
    change (⨅ j, F (ui j) x) ≤ normalizedChoice ideal θ u x + (C : EReal)
    have he := congrFun hnorm x
    simp only [iInf_apply] at he
    rw [he, ← ThetaPshDecreasingLimit.iInf_add_coe]
    exact iInf_mono fun j => choice_le_normalized ideal (hui j) hK U hU x
  have hmore : SGPT.PSH.SingularityLE L (normalizedChoice ideal θ u) :=
    (singularityLE_iff_exists_real _ _).mpr ⟨C, hupper⟩
  have hLK : partialObstacle (n := n) K f L :=
    partialObstacle_of_le (choice_obstacle ideal θ (ui 0) hK ⟨U, hU⟩) (fun x => iInf_le _ 0)
  have hLA : L ≤ A := by
    cases ideal
    · change SGPT.PSH.SingularityLE L (sourceSingularityEnvelope θ u) at hmore
      have hLP := GlobalPComparison.sourcePOrder_of_moreSingular ω
        hLn.quasiPshPotential
        ((isThetaPSH_iff_nativeThetaPotential θ _).mp (sourceOrdinaryEnvelope_genuine hu)).quasiPshPotential
        hmore
      have hPu := GlobalPComparison.sourcePEquivalent_singularityEnvelope ω
        (atlasClosedFormToNative θ) ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu) hpos
      have hLu : GlobalPComparison.sourcePOrder (n := n) L u :=
        GlobalPComparison.sourcePOrder_trans ω hLP (by
          simpa only [sourceSingularityEnvelope_eq_native] using hPu.2)
      change L ≤ partialEnvelope θ u K f
      rw [(SGPT.Bergman.PartialEnvelopeEverywhere.partialEnvelope_globalP_full_descriptions ω hu hpos hlo).1]
      intro x
      exact (le_iSup (fun v : SGPT.Bergman.PartialPOrder.partialPCompetitors θ u K f => v.val x)
        ⟨L, hL, hLK, hLu⟩).trans (le_uscRegularization
          (fun y => ⨆ v : SGPT.Bergman.PartialPOrder.partialPCompetitors θ u K f, v.val y) x)
    · change SGPT.PSH.SingularityLE L (sourceIEnvelope θ u) at hmore
      have hLI := sourceIOrder_of_singularityLE hL (isThetaPSH_sourceIEnvelope hu) hmore
      exact le_partialIEnvelope hL hLK (sourceIOrder_trans hLI (sourceIEquivalent_iEnvelope hu).2)
  have heq : (⨅ j, F (ui j)) = A := by
    funext x
    simpa only [iInf_apply] using congrFun (le_antisymm hLA hAL) x
  refine ⟨hantiF, heq, ?_⟩
  intro x
  have hp : (⨅ j, F (ui j) x) = A x := by
    simpa only [iInf_apply] using congrFun heq x
  change Tendsto (fun j => F (ui j) x) atTop (𝓝 (A x))
  rw [← hp]
  exact tendsto_atTop_iInf (fun j k hjk => hantiF hjk x)




/-- Both original decreasing conclusions at the original weighted subset;
actual target positivity internally supplies the dS background. -/
theorem partialEnvelopes_decreasing (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    {ui : ℕ → M → EReal} {u : M → EReal}
    (hui : ∀ j, (ofFixedModel n M).IsThetaPSH θ (ui j))
    (huipos : ∀ j, 0 < sourcePotentialNonPluripolarMeasure θ (ui j) (hui j) univ)
    (hanti : Antitone ui) (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hpos : 0 < sourcePotentialNonPluripolarMeasure θ u hu univ)
    (hlim : Tendsto (fun j => (⟨ui j, hui j⟩ : SourceThetaPotentialL1 θ)) atTop
      (@nhds (SourceThetaPotentialL1 θ)
        (sourceSingularityTopology ω θ (sourcePositiveMass_isBig ω hu hpos)) ⟨u, hu⟩))
    (W : SGPT.Bergman.WeightedSubset.WeightedSubset n M) :
    (Antitone (fun j => partialEnvelope θ (ui j) W.carrier W.erealWeight) ∧
      (⨅ j, partialEnvelope θ (ui j) W.carrier W.erealWeight) =
        partialEnvelope θ u W.carrier W.erealWeight ∧
      ∀ x, Tendsto (fun j => partialEnvelope θ (ui j) W.carrier W.erealWeight x) atTop
        (𝓝 (partialEnvelope θ u W.carrier W.erealWeight x))) ∧
    (Antitone (fun j => partialIEnvelope θ (ui j) W.carrier W.erealWeight) ∧
      (⨅ j, partialIEnvelope θ (ui j) W.carrier W.erealWeight) =
        partialIEnvelope θ u W.carrier W.erealWeight ∧
      ∀ x, Tendsto (fun j => partialIEnvelope θ (ui j) W.carrier W.erealWeight x) atTop
        (𝓝 (partialIEnvelope θ u W.carrier W.erealWeight x))) := by
  obtain ⟨L, U, hL, hU⟩ := W.partialEnvelope_weight_bounds
  exact ⟨choice_decreasing_original false ω (sourcePositiveMass_isBig ω hu hpos)
      hui huipos hanti hu hpos hlim W.nonPluripolar_carrier ⟨L, hL⟩ ⟨U, hU⟩,
    choice_decreasing_original true ω (sourcePositiveMass_isBig ω hu hpos)
      hui huipos hanti hu hpos hlim W.nonPluripolar_carrier ⟨L, hL⟩ ⟨U, hU⟩⟩

/-- WHOLE ORIGINAL prop:conv_of_K_env: ALL four P/I × decreasing everywhere /
increasing actual-Kahler-volume AE conclusions, with actual original continuous
weighted-subset data. All output regularity, bounds, approximation and type
comparisons are manufactured by the proved producers. -/
theorem partialEnvelopes_monotone_convergence (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    {ui : ℕ → M → EReal} {u : M → EReal}
    (hui : ∀ j, (ofFixedModel n M).IsThetaPSH θ (ui j))
    (huipos : ∀ j, 0 < sourcePotentialNonPluripolarMeasure θ (ui j) (hui j) univ)
    (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hpos : 0 < sourcePotentialNonPluripolarMeasure θ u hu univ)
    (W : SGPT.Bergman.WeightedSubset.WeightedSubset n M) :
    (Antitone ui →
      Tendsto (fun j => (⟨ui j, hui j⟩ : SourceThetaPotentialL1 θ)) atTop
        (@nhds (SourceThetaPotentialL1 θ)
          (sourceSingularityTopology ω θ (sourcePositiveMass_isBig ω hu hpos)) ⟨u, hu⟩) →
      (Antitone (fun j => partialEnvelope θ (ui j) W.carrier W.erealWeight) ∧
        (⨅ j, partialEnvelope θ (ui j) W.carrier W.erealWeight) =
          partialEnvelope θ u W.carrier W.erealWeight ∧
        ∀ x, Tendsto (fun j => partialEnvelope θ (ui j) W.carrier W.erealWeight x) atTop
          (𝓝 (partialEnvelope θ u W.carrier W.erealWeight x))) ∧
      (Antitone (fun j => partialIEnvelope θ (ui j) W.carrier W.erealWeight) ∧
        (⨅ j, partialIEnvelope θ (ui j) W.carrier W.erealWeight) =
          partialIEnvelope θ u W.carrier W.erealWeight ∧
        ∀ x, Tendsto (fun j => partialIEnvelope θ (ui j) W.carrier W.erealWeight x) atTop
          (𝓝 (partialIEnvelope θ u W.carrier W.erealWeight x)))) ∧
    (Monotone ui →
      (∀ᵐ x ∂sourceKahlerVolume ω, Tendsto (fun j => ui j x) atTop (𝓝 (u x))) →
      (Monotone (fun j => partialEnvelope θ (ui j) W.carrier W.erealWeight) ∧
        uscRegularization (⨆ j, partialEnvelope θ (ui j) W.carrier W.erealWeight) =
          partialEnvelope θ u W.carrier W.erealWeight ∧
        ∀ᵐ x ∂sourceKahlerVolume ω,
          Tendsto (fun j => partialEnvelope θ (ui j) W.carrier W.erealWeight x) atTop
            (𝓝 (partialEnvelope θ u W.carrier W.erealWeight x))) ∧
      (Monotone (fun j => partialIEnvelope θ (ui j) W.carrier W.erealWeight) ∧
        uscRegularization (⨆ j, partialIEnvelope θ (ui j) W.carrier W.erealWeight) =
          partialIEnvelope θ u W.carrier W.erealWeight ∧
        ∀ᵐ x ∂sourceKahlerVolume ω,
          Tendsto (fun j => partialIEnvelope θ (ui j) W.carrier W.erealWeight x) atTop
            (𝓝 (partialIEnvelope θ u W.carrier W.erealWeight x)))) :=
  ⟨fun hanti hlim => partialEnvelopes_decreasing ω hui huipos hanti hu hpos hlim W,
    fun hm hae => partialEnvelopes_increasing ω hui huipos hm hu hpos hae W⟩


end SGPT.Bergman.MonotonePartialEnvelopes
