import SGPT.PSH.SourceTestCurveBackgroundProjection
import SGPT.Envelopes.SourceOrdinaryEnvelopeAlgebra
import SGPT.Foundations.Analysis.Pending.MixedSummandCapacityDomination
import Mathlib.Topology.Maps.Proper.Basic

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set Filter Topology MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination

/-- A genuinely joint upper-semicontinuous compact-index family has an actual usc supremum. -/
theorem sourceCompact_iSup_upperSemicontinuous {K X : Type*}
    [TopologicalSpace K] [CompactSpace K] [Nonempty K] [TopologicalSpace X]
    (H : K × X → EReal) (hH : UpperSemicontinuous H) :
    UpperSemicontinuous (fun x => ⨆ k, H (k, x)) := by
  apply upperSemicontinuous_iff_IsClosed_hypograph.mpr
  let A : Set (K × (X × EReal)) := {p | p.2.2 ≤ H (p.1, p.2.1)}
  have hc : Continuous (fun p : K × (X × EReal) => ((p.1, p.2.1), p.2.2)) :=
    (continuous_fst.prodMk continuous_snd.fst).prodMk continuous_snd.snd
  have hA : IsClosed A := hH.IsClosed_hypograph.preimage hc
  have hp : IsClosed (Prod.snd '' A) := isClosedMap_snd_of_compactSpace A hA
  have heq : Prod.snd '' A = {p : X × EReal | p.2 ≤ ⨆ k, H (k, p.1)} := by
    ext p
    constructor
    · rintro ⟨⟨k, q⟩, hk, he⟩
      change q = p at he
      subst q
      exact hk.trans (le_iSup (fun k => H (k, p.1)) k)
    · intro h
      change p.2 ≤ ⨆ k, H (k, p.1) at h
      have hu : UpperSemicontinuous (fun k => H (k, p.1)) :=
        hH.comp (continuous_id.prodMk continuous_const)
      obtain ⟨k, _, hmax⟩ := UpperSemicontinuousOn.exists_isMaxOn
        (s := (univ : Set K)) univ_nonempty isCompact_univ (hu.upperSemicontinuousOn univ)
      refine ⟨(k, p), ?_, rfl⟩
      change p.2 ≤ H (k, p.1)
      exact h.trans (iSup_le fun j => (show H (j, p.1) ≤ H (k, p.1) from hmax (mem_univ j)))
  rw [heq] at hp
  exact hp

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ σ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

omit [MeasurableSpace M] [BorelSpace M] in
/-- The actual whole extension is jointly upper semicontinuous, including cutoff and poles. -/
theorem SourceTestCurvePredata.at_joint_upperSemicontinuous (Γ : SourceTestCurvePredata θ) :
    UpperSemicontinuous (fun p : ℝ × M => sourceTestCurveAt Γ p.1 p.2) := by
  intro p a ha
  change sourceTestCurveAt Γ p.1 p.2 < a at ha
  rw [Γ.at_eq_earlierInf p.2 p.1] at ha
  obtain ⟨s, hs⟩ := iInf_lt_iff.mp ha
  have hsp : UpperSemicontinuous (sourceTestCurveAt Γ s.1) := by
    by_cases hle : s.1 ≤ Γ.max
    · have hp := (source_test_curve_extension_whole Γ).2.2.2 s.1 hle
      exact ((isThetaPSH_iff_nativeThetaPotential θ _).mp hp).1.quasiPlurisubharmonic.upperSemicontinuous
    · rw [sourceTestCurveAt_of_gt Γ (lt_of_not_ge hle)]
      exact upperSemicontinuous_const
  have hfst : ∀ᶠ q : ℝ × M in 𝓝 p, s.1 < q.1 :=
    (continuous_fst.tendsto p) (Ioi_mem_nhds s.2)
  have hsnd : ∀ᶠ q : ℝ × M in 𝓝 p, sourceTestCurveAt Γ s.1 q.2 < a :=
    (continuous_snd.tendsto p) (hsp p.2 a hs)
  filter_upwards [hfst, hsnd] with q hq hqa
  exact (Γ.at_antitone q.2 hq.le).trans_lt hqa

/-- The literal original raw sum: no usc regularization is inserted. -/
def sourceTestCurveRawSum (Γ : SourceTestCurvePredata θ) (Δ : SourceTestCurvePredata σ)
    (τ : ℝ) (x : M) : EReal :=
  ⨆ r : ℝ, sourceTestCurveAt Γ r x + sourceTestCurveAt Δ (τ-r) x

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- The actual whole raw family retains its common finite upper bound. -/
theorem sourceTestCurveRawSum_le_zero (Γ : SourceTestCurvePredata θ)
    (Δ : SourceTestCurvePredata σ) (τ : ℝ) (x : M) : sourceTestCurveRawSum Γ Δ τ x ≤ 0 := by
  apply iSup_le
  intro r
  simpa only [add_zero, Pi.zero_apply] using
    add_le_add (Γ.at_le_zero r x) (Δ.at_le_zero (τ-r) x)

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- Exact restriction to the closed interval retains both genuine cutoff values. -/
theorem sourceTestCurveRawSum_eq_compact (Γ : SourceTestCurvePredata θ)
    (Δ : SourceTestCurvePredata σ) (τ : ℝ) :
    sourceTestCurveRawSum Γ Δ τ = fun x =>
      ⨆ r : Icc (τ-Δ.max) Γ.max, sourceTestCurveAt Γ r.1 x + sourceTestCurveAt Δ (τ-r.1) x := by
  funext x
  apply le_antisymm
  · apply iSup_le
    intro r
    by_cases hr : r ∈ Icc (τ-Δ.max) Γ.max
    · exact le_iSup (fun r : Icc (τ-Δ.max) Γ.max =>
        sourceTestCurveAt Γ r.1 x + sourceTestCurveAt Δ (τ-r.1) x) ⟨r, hr⟩
    · by_cases hright : r ≤ Γ.max
      · have hleft : r < τ-Δ.max := lt_of_not_ge (fun h => hr ⟨h, hright⟩)
        rw [sourceTestCurveAt_of_gt Δ (show Δ.max < τ-r by linarith)]
        simp only [Pi.bot_apply, EReal.add_bot]
        exact bot_le
      · rw [sourceTestCurveAt_of_gt Γ (lt_of_not_ge hright)]
        simp only [Pi.bot_apply, EReal.bot_add]
        exact bot_le
  · apply iSup_le
    intro r
    exact le_iSup (fun s : ℝ => sourceTestCurveAt Γ s x + sourceTestCurveAt Δ (τ-s) x) r.1

omit [MeasurableSpace M] [BorelSpace M] in
private theorem rawSum_summand_jointUSC (Γ : SourceTestCurvePredata θ)
    (Δ : SourceTestCurvePredata σ) (τ : ℝ) :
    UpperSemicontinuous (fun p : ℝ × M =>
      sourceTestCurveAt Γ p.1 p.2 + sourceTestCurveAt Δ (τ-p.1) p.2) := by
  have hΔ : UpperSemicontinuous (fun p : ℝ × M => sourceTestCurveAt Δ (τ-p.1) p.2) :=
    Δ.at_joint_upperSemicontinuous.comp
      ((continuous_const.sub continuous_fst).prodMk continuous_snd)
  apply Γ.at_joint_upperSemicontinuous.add' hΔ
  intro p
  have hz : (0 : EReal) < ⊤ := by simp
  exact EReal.continuousAt_add
    (Or.inl (ne_of_lt ((Γ.at_le_zero p.1 p.2).trans_lt hz)))
    (Or.inr (ne_of_lt ((Δ.at_le_zero (τ-p.1) p.2).trans_lt hz)))

omit [MeasurableSpace M] [BorelSpace M] in
/-- Every strict or cutoff raw value is attained on the actual nonempty closed interval. -/
theorem sourceTestCurveRawSum_attained (Γ : SourceTestCurvePredata θ)
    (Δ : SourceTestCurvePredata σ) {τ : ℝ} (hτ : τ ≤ Γ.max + Δ.max) (x : M) :
    ∃ r : Icc (τ-Δ.max) Γ.max, sourceTestCurveRawSum Γ Δ τ x =
      sourceTestCurveAt Γ r.1 x + sourceTestCurveAt Δ (τ-r.1) x := by
  let K := Icc (τ-Δ.max) Γ.max
  have : Nonempty K := ⟨⟨Γ.max, by constructor; linarith; exact le_rfl⟩⟩
  have hu : UpperSemicontinuous (fun r : K =>
      sourceTestCurveAt Γ r.1 x + sourceTestCurveAt Δ (τ-r.1) x) :=
    (rawSum_summand_jointUSC Γ Δ τ).comp (continuous_subtype_val.prodMk continuous_const)
  obtain ⟨r, _, hmax⟩ := UpperSemicontinuousOn.exists_isMaxOn
    (s := (univ : Set K)) univ_nonempty isCompact_univ (hu.upperSemicontinuousOn univ)
  refine ⟨r, ?_⟩
  rw [sourceTestCurveRawSum_eq_compact]
  exact le_antisymm (iSup_le fun j => (show
    sourceTestCurveAt Γ j.1 x + sourceTestCurveAt Δ (τ-j.1) x ≤
      sourceTestCurveAt Γ r.1 x + sourceTestCurveAt Δ (τ-r.1) x from hmax (mem_univ j)))
    (le_iSup (fun j : K => sourceTestCurveAt Γ j.1 x + sourceTestCurveAt Δ (τ-j.1) x) r)

omit [MeasurableSpace M] [BorelSpace M] in
/-- Genuine PSH of the literal unregularized real supremum, retaining actual cutoff summands. -/
theorem sourceTestCurveRawSum_thetaPSH (Γ : SourceTestCurvePredata θ)
    (Δ : SourceTestCurvePredata σ) {τ : ℝ} (hτ : τ ≤ Γ.max + Δ.max) :
    (ofFixedModel n M).IsThetaPSH
      (nativeClosedFormToAtlas (atlasClosedFormToNative θ + atlasClosedFormToNative σ))
      (sourceTestCurveRawSum Γ Δ τ) := by
  let K := Icc (τ-Δ.max) Γ.max
  have : Nonempty K := ⟨⟨Γ.max, by constructor; linarith; exact le_rfl⟩⟩
  let T := nativeClosedFormToAtlas (atlasClosedFormToNative θ + atlasClosedFormToNative σ)
  let F : K → M → EReal := fun r x =>
    sourceTestCurveAt Γ r.1 x + sourceTestCurveAt Δ (τ-r.1) x
  have hF (r : K) : (ofFixedModel n M).IsThetaPSH T (F r) := by
    apply sourceIndependentSum_thetaPSH
    · exact (source_test_curve_extension_whole Γ).2.2.2 r.1 r.2.2
    · apply (source_test_curve_extension_whole Δ).2.2.2
      have hr : τ-Δ.max ≤ r.1 := r.2.1
      linarith
  have heq : (fun x => ⨆ r : K, F r x) = sourceTestCurveRawSum Γ Δ τ :=
    (sourceTestCurveRawSum_eq_compact Γ Δ τ).symm
  have hraw : UpperSemicontinuous (sourceTestCurveRawSum Γ Δ τ) := by
    rw [← heq]
    apply sourceCompact_iSup_upperSemicontinuous (fun p : K × M => F p.1 p.2)
    exact (rawSum_summand_jointUSC Γ Δ τ).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  apply (isThetaPSH_iff_nativeThetaPotential T _).mpr
  have hn := SubgeodesicSupremumInterior.isThetaPshPotential_uscRegularization_iSup
    (fun r => (isThetaPSH_iff_nativeThetaPotential T (F r)).mp (hF r))
    (C := 0) (fun r x => by
      exact (le_iSup (fun s : ℝ => sourceTestCurveAt Γ s x + sourceTestCurveAt Δ (τ-s) x) r.1).trans
        (sourceTestCurveRawSum_le_zero Γ Δ τ x))
  rw [heq, uscRegularization_eq hraw] at hn
  exact hn

omit [ConnectedSpace M] in
/-- The actual two-background sum mass dominates an actual selected diagonal mass. -/
theorem sourceIndependentSum_mass_ge_left {u v : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hv : (ofFixedModel n M).IsThetaPSH σ v) :
    sourcePotentialNonPluripolarMeasure θ u hu univ ≤
      sourcePotentialNonPluripolarMeasure
        (nativeClosedFormToAtlas (atlasClosedFormToNative θ + atlasClosedFormToNative σ))
        (fun x => u x + v x) (sourceIndependentSum_thetaPSH hu hv) univ := by
  classical
  let α : Bool → ClosedRealOneOneForm n M := fun b =>
    if b then atlasClosedFormToNative θ else atlasClosedFormToNative σ
  let f : Bool → M → EReal := fun b => if b then u else v
  have hf (b : Bool) : IsThetaPshPotential (α b).val (f b) := by
    cases b
    · exact (isThetaPSH_iff_nativeThetaPotential σ v).mp hv
    · exact (isThetaPSH_iff_nativeThetaPotential θ u).mp hu
  have h := MixedSummandCapacityDomination.selectedMixedMeasure_apply_le_diagonal_sum
    (T := Finset.univ) (w := fun _ : Bool => (1 : ℝ))
    Finset.univ_nonempty (fun _ => zero_lt_one) hf
    (fun _ : Fin n => true) (fun _ => Finset.mem_univ _) (univ : Set M)
  have hQ : GlobalMultilinearExpansion.sumPot Finset.univ (fun _ : Bool => (1 : ℝ)) f =
      fun x => u x + v x := by
    funext x
    simp only [GlobalMultilinearExpansion.sumPot, Fintype.sum_bool, f,
      Bool.false_eq_true, ↓reduceIte, EReal.coe_one, one_mul]
  have hA : GlobalMultilinearExpansion.sumForm Finset.univ (fun _ : Bool => (1 : ℝ)) α =
      atlasClosedFormToNative θ + atlasClosedFormToNative σ := by
    simp only [GlobalMultilinearExpansion.sumForm, Fintype.sum_bool, α,
      Bool.false_eq_true, ↓reduceIte, one_smul]
  simp only [hQ, hA] at h
  simpa [sourcePotentialNonPluripolarMeasure, DiagonalMass.diagonalPotentialMeasure,
    sourceNativeAtlasForm_roundTrip, α, f] using h

/-- Strict subcutoff raw sums have internally produced positive actual mass. -/
theorem sourceTestCurveRawSum_mass_positive (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (Δ : SourceTestCurve σ) {τ : ℝ} (hτ : τ < Γ.max + Δ.max) :
    0 < sourcePotentialNonPluripolarMeasure
      (nativeClosedFormToAtlas (atlasClosedFormToNative θ + atlasClosedFormToNative σ))
      (sourceTestCurveRawSum Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata τ)
      (sourceTestCurveRawSum_thetaPSH Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata hτ.le) univ := by
  let r : Iio Γ.max := ⟨(τ-Δ.max+Γ.max)/2, by change (τ-Δ.max+Γ.max)/2 < Γ.max; linarith⟩
  let s : Iio Δ.max := ⟨τ-r.1, by change τ-r.1 < Δ.max; dsimp [r]; linarith⟩
  have hsum := sourceIndependentSum_thetaPSH (Γ.thetaPSH r) (Δ.thetaPSH s)
  have hpos := (Γ.mass_positive omega r).trans_le
    (sourceIndependentSum_mass_ge_left (Γ.thetaPSH r) (Δ.thetaPSH s))
  have hle : (fun x => Γ.potential r x + Δ.potential s x) ≤
      sourceTestCurveRawSum Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata τ := by
    intro x
    have h := le_iSup (fun q : ℝ => sourceTestCurveAt Γ.toSourceTestCurvePredata q x +
      sourceTestCurveAt Δ.toSourceTestCurvePredata (τ-q) x) r.1
    have hs : τ-r.1 < Δ.max := s.2
    rw [sourceTestCurveAt_of_lt Γ.toSourceTestCurvePredata r.2,
      sourceTestCurveAt_of_lt Δ.toSourceTestCurvePredata hs] at h
    change Γ.potential r x + Δ.potential s x ≤
      sourceTestCurveRawSum Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata τ x at h
    exact h
  exact hpos.trans_le (sourcePotentialNonPluripolarMass_mono omega hsum
    (sourceTestCurveRawSum_thetaPSH Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata hτ.le)
    (MoreSingularOn.of_le fun x _ => hle x))

/-- The ordinary model of each strict raw sum is genuinely produced from its actual mass. -/
theorem sourceTestCurveRawSum_model (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (Δ : SourceTestCurve σ) {τ : ℝ} (hτ : τ < Γ.max + Δ.max) :
    SourceModelPotential
      (nativeClosedFormToAtlas (atlasClosedFormToNative θ + atlasClosedFormToNative σ))
      (sourceSingularityEnvelope
        (nativeClosedFormToAtlas (atlasClosedFormToNative θ + atlasClosedFormToNative σ))
        (sourceTestCurveRawSum Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata τ)) :=
  sourceOrdinaryEnvelope_model omega
    (sourceTestCurveRawSum_thetaPSH Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata hτ.le)
    (sourceTestCurveRawSum_mass_positive omega Γ Δ hτ)

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- Literal raw sums decrease on the entire real parameter line. -/
theorem sourceTestCurveRawSum_antitone (Γ : SourceTestCurvePredata θ)
    (Δ : SourceTestCurvePredata σ) (x : M) : Antitone (fun τ => sourceTestCurveRawSum Γ Δ τ x) := by
  intro a b hab
  apply iSup_le
  intro r
  exact (add_le_add le_rfl (Δ.at_antitone x (sub_le_sub_right hab r))).trans
    (le_iSup (fun s : ℝ => sourceTestCurveAt Γ s x + sourceTestCurveAt Δ (a-s) x) r)

omit [MeasurableSpace M] [BorelSpace M] in
private theorem at_strict_chord (Γ : SourceTestCurvePredata θ) (a b : ℝ)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    convexComb t (sourceTestCurveAt Γ a) (sourceTestCurveAt Γ b) ≤
      sourceTestCurveAt Γ (t*a+(1-t)*b) := by
  intro x
  have ht : 0 < 1-t := sub_pos.mpr ht1
  have hz : (0 : EReal) < ⊤ := by simp
  have haTop := ne_of_lt ((Γ.at_le_zero a x).trans_lt hz)
  have hbTop := ne_of_lt ((Γ.at_le_zero b x).trans_lt hz)
  cases haVal : sourceTestCurveAt Γ a x using EReal.rec with
  | top => exact False.elim (haTop haVal)
  | bot =>
    simp only [convexComb, haVal, EReal.coe_mul_bot_of_pos ht0, EReal.bot_add]
    exact bot_le
  | coe u =>
    cases hbVal : sourceTestCurveAt Γ b x using EReal.rec with
    | top => exact False.elim (hbTop hbVal)
    | bot =>
      simp only [convexComb, hbVal, EReal.coe_mul_bot_of_pos ht, EReal.add_bot]
      exact bot_le
    | coe v =>
      have hpa : (a, -u) ∈ SGPT.Convex.epigraph (sourceTestCurveClosedNegativeTrace Γ x) := by
        change -(sourceTestCurveAt Γ a x) ≤ ((-u : ℝ) : EReal)
        rw [haVal, EReal.coe_neg]
      have hpb : (b, -v) ∈ SGPT.Convex.epigraph (sourceTestCurveClosedNegativeTrace Γ x) := by
        change -(sourceTestCurveAt Γ b x) ≤ ((-v : ℝ) : EReal)
        rw [hbVal, EReal.coe_neg]
      have hc := Γ.closedNegativeTrace_convex x hpa hpb ht0.le ht.le
        (show t+(1-t)=1 by ring)
      change -(sourceTestCurveAt Γ (t*a+(1-t)*b) x) ≤
        ((t*(-u)+(1-t)*(-v) : ℝ) : EReal) at hc
      have he : ((t*(-u)+(1-t)*(-v) : ℝ) : EReal) =
          -((t*u+(1-t)*v : ℝ) : EReal) := by
        rw [← EReal.coe_neg]
        congr 1
        ring
      rw [he] at hc
      simpa only [convexComb, haVal, hbVal, ← EReal.coe_mul, ← EReal.coe_add] using
        (EReal.neg_le_neg_iff.mp hc)

omit [MeasurableSpace M] [BorelSpace M] in
/-- Actual compact attaining parameters and whole closed epigraphs supply the raw strict chord. -/
theorem sourceTestCurveRawSum_convexComb_le (Γ : SourceTestCurvePredata θ)
    (Δ : SourceTestCurvePredata σ) (a b : Iio (Γ.max+Δ.max))
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    convexComb t (sourceTestCurveRawSum Γ Δ a.1) (sourceTestCurveRawSum Γ Δ b.1) ≤
      sourceTestCurveRawSum Γ Δ (t*a.1+(1-t)*b.1) := by
  intro x
  obtain ⟨r, hr⟩ := sourceTestCurveRawSum_attained Γ Δ a.2.le x
  obtain ⟨s, hs⟩ := sourceTestCurveRawSum_attained Γ Δ b.2.le x
  have hG := at_strict_chord Γ r.1 s.1 ht0 ht1 x
  have hD := at_strict_chord Δ (a.1-r.1) (b.1-s.1) ht0 ht1 x
  have hd : t*(a.1-r.1)+(1-t)*(b.1-s.1) =
      (t*a.1+(1-t)*b.1)-(t*r.1+(1-t)*s.1) := by ring
  rw [hd] at hD
  calc
    convexComb t (sourceTestCurveRawSum Γ Δ a.1) (sourceTestCurveRawSum Γ Δ b.1) x =
        ((t : EReal)*sourceTestCurveAt Γ r.1 x + ((1-t : ℝ) : EReal)*sourceTestCurveAt Γ s.1 x) +
        ((t : EReal)*sourceTestCurveAt Δ (a.1-r.1) x +
          ((1-t : ℝ) : EReal)*sourceTestCurveAt Δ (b.1-s.1) x) := by
      change (t : EReal)*sourceTestCurveRawSum Γ Δ a.1 x +
        ((1-t : ℝ) : EReal)*sourceTestCurveRawSum Γ Δ b.1 x = _
      rw [hr, hs,
        EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr ht0.le) (EReal.coe_ne_top t),
        EReal.left_distrib_of_nonneg_of_ne_top
          (EReal.coe_nonneg.mpr (sub_pos.mpr ht1).le) (EReal.coe_ne_top (1-t))]
      ac_rfl
    _ ≤ sourceTestCurveAt Γ (t*r.1+(1-t)*s.1) x +
        sourceTestCurveAt Δ ((t*a.1+(1-t)*b.1)-(t*r.1+(1-t)*s.1)) x := add_le_add hG hD
    _ ≤ sourceTestCurveRawSum Γ Δ (t*a.1+(1-t)*b.1) x :=
      le_iSup (fun q : ℝ => sourceTestCurveAt Γ q x +
        sourceTestCurveAt Δ ((t*a.1+(1-t)*b.1)-q) x) (t*r.1+(1-t)*s.1)

private def sumPredata (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (Δ : SourceTestCurve σ) :
    SourceTestCurvePredata
      (nativeClosedFormToAtlas (atlasClosedFormToNative θ + atlasClosedFormToNative σ)) where
  max := Γ.max + Δ.max
  potential r := sourceSingularityEnvelope
    (nativeClosedFormToAtlas (atlasClosedFormToNative θ + atlasClosedFormToNative σ))
    (sourceTestCurveRawSum Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata r.1)
  thetaPSH r := (sourceTestCurveRawSum_model omega Γ Δ r.2).thetaPSH
  antitone x := by
    intro a b hab
    exact sourceOrdinaryEnvelope_mono
      (MoreSingularOn.of_le fun y _ =>
        sourceTestCurveRawSum_antitone Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata y hab) x
  concave x := by
    apply sourceTestCurveNegativeTrace_convex_of_chords
    intro a b t ht0 ht1
    apply (sourceOrdinaryEnvelope_convexComb_le
      (sourceTestCurveRawSum_thetaPSH Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata a.2.le)
      (sourceTestCurveRawSum_thetaPSH Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata b.2.le)
      ht0 ht1).trans
    exact sourceOrdinaryEnvelope_mono
      (MoreSingularOn.of_le fun y _ =>
        sourceTestCurveRawSum_convexComb_le Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata
          a b ht0 ht1 y)
  fixedPoint r := (sourceTestCurveRawSum_model omega Γ Δ r.2).choose_spec.1.symm

/-- The genuine original ordinary sum, with internally positive actual usc-limit mass. -/
def SourceTestCurve.sum (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (Δ : SourceTestCurve σ) :
    SourceTestCurve
      (nativeClosedFormToAtlas (atlasClosedFormToNative θ + atlasClosedFormToNative σ)) where
  toSourceTestCurvePredata := sumPredata omega Γ Δ
  positiveLimitMass := by
    let S := sumPredata omega Γ Δ
    let r : Iio S.max := ⟨S.max-1, by change S.max-1 < S.max; linarith⟩
    have hr : r.1 < Γ.max + Δ.max := r.2
    have hm : SourceModelPotential
        (nativeClosedFormToAtlas (atlasClosedFormToNative θ + atlasClosedFormToNative σ))
        (S.potential r) := sourceTestCurveRawSum_model omega Γ Δ hr
    have hle : S.potential r ≤ sourceTestCurveLimit S := by
      intro x
      change S.potential r x ≤ uscRegularization (fun y => ⨆ q, S.potential q y) x
      exact (le_iSup (fun q => S.potential q x) r).trans
        (le_uscRegularization (fun y => ⨆ q, S.potential q y) x)
    exact hm.choose_spec.2.trans_le (sourcePotentialNonPluripolarMass_mono omega
      hm.thetaPSH S.limit_thetaPSH (MoreSingularOn.of_le fun x _ => hle x))

/-- Literal original cutoff of the genuine ordinary sum. -/
theorem SourceTestCurve.sum_max (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (Δ : SourceTestCurve σ) :
    (SourceTestCurve.sum omega Γ Δ).max = Γ.max + Δ.max := rfl

/-- Literal original P-envelope of the unregularized all-real inner supremum. -/
theorem SourceTestCurve.sum_potential (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (Δ : SourceTestCurve σ)
    (r : Iio (SourceTestCurve.sum omega Γ Δ).max) :
    (SourceTestCurve.sum omega Γ Δ).potential r =
      sourceSingularityEnvelope
        (nativeClosedFormToAtlas (atlasClosedFormToNative θ + atlasClosedFormToNative σ))
        (sourceTestCurveRawSum Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata r.1) := rfl

/-- The original union witness is the genuinely produced actual positive model limit. -/
theorem SourceTestCurve.sum_mem_positive (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (Δ : SourceTestCurve σ) :
    SourceTestCurve.sum omega Γ Δ ∈ SourceTestCurvesPositive
      (nativeClosedFormToAtlas (atlasClosedFormToNative θ + atlasClosedFormToNative σ)) :=
  (SourceTestCurve.sum omega Γ Δ).mem_positive omega

end SGPT.PSH.VariableComplexAtlas
