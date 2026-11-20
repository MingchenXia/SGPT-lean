import SGPT.PSH.SourceIGoodBackground
import SGPT.PSH.SourceTestCurvePositiveScaling
import SGPT.PSH.SourceSingularityDistanceConvergence
import SGPT.PSH.SourceSingularityMaximumLimits
import SGPT.Foundations.Analysis.Pending.GlobalQuasiPshPositivePDomain
import SGPT.Foundations.Analysis.Pending.PositiveMassAnalyticCurrentSequences
import SGPT.Foundations.Analysis.Pending.RationalAnalyticAddition
import SGPT.Foundations.Analysis.Pending.RationalAnalyticMaximum
import SGPT.Foundations.Analysis.Pending.SingularNativeAdditionContinuity
import SGPT.Foundations.Analysis.Pending.IGoodNativeClosed

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set Filter MeasureTheory
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open ThetaPshL1Topology SingularCanonicalSingularityDistance

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem native_add_genuine {θ σ : ClosedRealOneOneForm n M}
    {u v : M → EReal} (hu : IsThetaPshPotential θ.val u)
    (hv : IsThetaPshPotential σ.val v) :
    IsThetaPshPotential (θ+σ).val (fun x => u x+v x) := by
  have hu' : (ofFixedModel n M).IsThetaPSH (nativeClosedFormToAtlas θ) u :=
    (isThetaPSH_iff_nativeThetaPotential _ _).mpr (by
      simpa only [sourceNativeAtlasForm_roundTrip] using hu)
  have hv' : (ofFixedModel n M).IsThetaPSH (nativeClosedFormToAtlas σ) v :=
    (isThetaPSH_iff_nativeThetaPotential _ _).mpr (by
      simpa only [sourceNativeAtlasForm_roundTrip] using hv)
  have h := (isThetaPSH_iff_nativeThetaPotential _ _).mp
    (sourceIndependentSum_thetaPSH hu' hv')
  simpa only [sourceNativeAtlasForm_roundTrip] using h

/-- Genuine original I-goodness is preserved by actual addition. -/
theorem sourceIGood_add (omega : KahlerBackground n M) {u v : M → EReal}
    (hu : sourceIGood (n := n) u) (hv : sourceIGood (n := n) v) :
    sourceIGood (n := n) (fun x => u x+v x) := by
  rw [sourceIGood_iff_native] at hu hv ⊢
  obtain ⟨θ, hθ, hgu⟩ := hu
  obtain ⟨σ, hσ, hgv⟩ := hv
  obtain ⟨C, hC, huC, hvC, hup, hvp⟩ :=
    GlobalQuasiPshPositivePDomain.exists_pos_common_kahler_background omega
      hθ.quasiPshPotential hσ.quasiPshPotential
  have hguC := (IGoodPositiveBackgroundIndependence.iGoodWith_iff_positive_common_potential
    omega θ (C • omega.form) hθ huC hgu.positiveMass hup).mp hgu
  have hgvC := (IGoodPositiveBackgroundIndependence.iGoodWith_iff_positive_common_potential
    omega σ (C • omega.form) hσ hvC hgv.positiveMass hvp).mp hgv
  have hbig : IsBigClass (RealBottChern.ofRepresentative (C • omega.form)) :=
    PluripolarCapacityDichotomy.isBigClass_kahler (KahlerBackground.smul hC omega)
  obtain ⟨A, hA, hAlim⟩ :=
    PositiveMassAnalyticCurrentSequences.exists_analytic_current_sequence_native_of_iGoodWith
      omega (C • omega.form) hbig huC hguC
  obtain ⟨B, hB, hBlim⟩ :=
    PositiveMassAnalyticCurrentSequences.exists_analytic_current_sequence_native_of_iGoodWith
      omega (C • omega.form) hbig hvC hgvC
  let γ := C • omega.form + C • omega.form
  have hγ : IsBigClass (RealBottChern.ofRepresentative γ) := by
    have he : γ = (2*C) • omega.form := by dsimp [γ]; module
    rw [he]
    exact PluripolarCapacityDichotomy.isBigClass_kahler
      (KahlerBackground.smul (by positivity : 0 < 2*C) omega)
  let S : ℕ → ThetaPshL1 γ.val := fun j =>
    ⟨fun x => (A j).val x+(B j).val x, native_add_genuine (A j).property (B j).property⟩
  let U : ThetaPshL1 γ.val := ⟨fun x => u x+v x, native_add_genuine huC hvC⟩
  have hlim : Tendsto S atTop (@nhds (ThetaPshL1 γ.val)
      (singularityPseudoMetricSpace omega γ hγ).toUniformSpace.toTopologicalSpace U) :=
    SingularNativeAdditionContinuity.tendsto_native_add omega
      (C • omega.form) (C • omega.form) hbig hbig atTop A B ⟨u,huC⟩ ⟨v,hvC⟩ hAlim hBlim
  have hgood (j : ℕ) : IGood (n := n) (S j).val := by
    apply AnalyticPotentialsIGood.iGood_of_globalQuasiPsh_of_analytic_type
      omega (S j).property.quasiPshPotential
    intro e z hz
    exact RationalAnalyticAddition.hasAnalyticSingularityTypeAt_add
      ((hA j).1 e z hz) ((hB j).1 e z hz)
  exact IGoodNativeClosed.iGood_of_native_filter_limit omega γ hγ atTop S U
    (Eventually.of_forall hgood) hlim

/-- Genuine original I-goodness is preserved by the actual pointwise maximum. -/
theorem sourceIGood_max (omega : KahlerBackground n M) {u v : M → EReal}
    (hu : sourceIGood (n := n) u) (hv : sourceIGood (n := n) v) :
    sourceIGood (n := n) (fun x => max (u x) (v x)) := by
  rw [sourceIGood_iff_native] at hu hv ⊢
  obtain ⟨θ, hθ, hgu⟩ := hu
  obtain ⟨σ, hσ, hgv⟩ := hv
  obtain ⟨C, hC, huC, hvC, hup, hvp⟩ :=
    GlobalQuasiPshPositivePDomain.exists_pos_common_kahler_background omega
      hθ.quasiPshPotential hσ.quasiPshPotential
  have hguC := (IGoodPositiveBackgroundIndependence.iGoodWith_iff_positive_common_potential
    omega θ (C • omega.form) hθ huC hgu.positiveMass hup).mp hgu
  have hgvC := (IGoodPositiveBackgroundIndependence.iGoodWith_iff_positive_common_potential
    omega σ (C • omega.form) hσ hvC hgv.positiveMass hvp).mp hgv
  have hbig : IsBigClass (RealBottChern.ofRepresentative (C • omega.form)) :=
    PluripolarCapacityDichotomy.isBigClass_kahler (KahlerBackground.smul hC omega)
  obtain ⟨A, hA, hAlim⟩ :=
    PositiveMassAnalyticCurrentSequences.exists_analytic_current_sequence_native_of_iGoodWith
      omega (C • omega.form) hbig huC hguC
  obtain ⟨B, hB, hBlim⟩ :=
    PositiveMassAnalyticCurrentSequences.exists_analytic_current_sequence_native_of_iGoodWith
      omega (C • omega.form) hbig hvC hgvC
  let S : ℕ → ThetaPshL1 (C • omega.form).val := fun j =>
    ⟨fun x => max ((A j).val x) ((B j).val x),
      SGPT.Foundations.Analysis.Pending.IsThetaPshPotential.max (A j).property (B j).property⟩
  let U : ThetaPshL1 (C • omega.form).val :=
    ⟨fun x => max (u x) (v x), SGPT.Foundations.Analysis.Pending.IsThetaPshPotential.max huC hvC⟩
  have hlim : Tendsto S atTop (@nhds (ThetaPshL1 (C • omega.form).val)
      (singularityPseudoMetricSpace omega (C • omega.form) hbig).toUniformSpace.toTopologicalSpace U) :=
    SingularNativeMaximumContinuity.tendsto_native_max omega (C • omega.form) hbig
      atTop A B ⟨u,huC⟩ ⟨v,hvC⟩ hAlim hBlim
  have hgood (j : ℕ) : IGood (n := n) (S j).val := by
    apply AnalyticPotentialsIGood.iGood_of_globalQuasiPsh_of_analytic_type
      omega (S j).property.quasiPshPotential
    intro e z hz
    exact RationalAnalyticMaximum.hasAnalyticSingularityTypeAt_max
      ((hA j).1 e z hz) ((hB j).1 e z hz)
  exact IGoodNativeClosed.iGood_of_native_filter_limit omega (C • omega.form) hbig
    atTop S U (Eventually.of_forall hgood) hlim

/-- Every positive REAL scalar preserves the original existential I-goodness. -/
theorem sourceIGood_pos_mul {u : M → EReal} (hu : sourceIGood (n := n) u)
    {c : ℝ} (hc : 0 < c) : sourceIGood (n := n) (fun x => (c : EReal)*u x) := by
  obtain ⟨θ, hθ, hg⟩ := hu
  let Θ := nativeClosedFormToAtlas (c • atlasClosedFormToNative θ)
  have hs := sourcePositiveScaling_thetaPSH hθ hc
  have hI : sourceIEnvelope Θ (fun x => (c : EReal)*u x) =
      fun x => (c : EReal)*sourceIEnvelope θ u x := by
    rw [sourceIEnvelope_eq_native Θ _ hs, sourceNativeAtlasForm_roundTrip,
      ActualIEnvelopePositiveScaling.iSingularityEnvelope_smul
        (atlasClosedFormToNative θ) ((isThetaPSH_iff_nativeThetaPotential θ u).mp hθ) hc,
      ← sourceIEnvelope_eq_native θ u hθ]
  refine ⟨Θ, hs, ?_, ?_⟩
  · rw [sourcePositiveScaling_actualMass hθ hc]
    exact ENNReal.mul_pos_iff.mpr ⟨ENNReal.ofReal_pos.mpr (pow_pos hc n), hg.1⟩
  · rw [sourceOrdinaryEnvelope_positiveScaling u hc, hI]
    exact congrArg (fun f : M → EReal => fun x => (c : EReal)*f x) hg.2

/-- Every NONEMPTY finite original maximum is both genuinely theta-PSH and I-good. -/
theorem sourceIGood_finset_sup (omega : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {I : Type*}
    (u : I → M → EReal) (s : Finset I) (hs : s.Nonempty)
    (hpsh : ∀ i ∈ s, (ofFixedModel n M).IsThetaPSH θ (u i))
    (hgood : ∀ i ∈ s, sourceIGood (n := n) (u i)) :
    (ofFixedModel n M).IsThetaPSH θ (fun x => s.sup' hs (fun i => u i x)) ∧
      sourceIGood (n := n) (fun x => s.sup' hs (fun i => u i x)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.not_nonempty_empty] at hs
  | @insert i s hi ih =>
    by_cases ht : s.Nonempty
    · have hpsh' : ∀ j ∈ s, (ofFixedModel n M).IsThetaPSH θ (u j) :=
        fun j hj => hpsh j (Finset.mem_insert_of_mem hj)
      have hgood' : ∀ j ∈ s, sourceIGood (n := n) (u j) :=
        fun j hj => hgood j (Finset.mem_insert_of_mem hj)
      obtain ⟨hP, hG⟩ := ih ht hpsh' hgood'
      have he : (fun x => (insert i s).sup' hs (fun j => u j x)) =
          fun x => max (u i x) (s.sup' ht (fun j => u j x)) := by
        funext x
        exact Finset.sup'_insert ht (fun j => u j x)
      rw [he]
      refine ⟨(isThetaPSH_iff_nativeThetaPotential θ _).mpr ?_,
        sourceIGood_max omega (hgood i (Finset.mem_insert_self i s)) hG⟩
      exact SGPT.Foundations.Analysis.Pending.IsThetaPshPotential.max
        ((isThetaPSH_iff_nativeThetaPotential θ _).mp (hpsh i (Finset.mem_insert_self i s)))
        ((isThetaPSH_iff_nativeThetaPotential θ _).mp hP)
    · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
      subst s
      simpa only [Finset.insert_empty, Finset.sup'_singleton] using
        And.intro (hpsh i (Finset.mem_insert_self i ∅)) (hgood i (Finset.mem_insert_self i ∅))

/-- WHOLE original arbitrary-family I-good USC supremum, with exactly local uniform boundedness. -/
theorem sourceIGood_uscSup (omega : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {I : Type*} [Nonempty I]
    (u : I → M → EReal) (hpsh : ∀ i, (ofFixedModel n M).IsThetaPSH θ (u i))
    (hgood : ∀ i, sourceIGood (n := n) (u i))
    (hbounded : FirstPass.LocallyUniformlyBoundedAbove (range u) univ) :
    sourceIGood (n := n) (uscRegularization (⨆ i, u i)) := by
  classical
  obtain ⟨C, hC⟩ := hbounded.exists_uniform_upper_bound_on_compact isCompact_univ (subset_refl _)
  let S := {s : Finset I // s.Nonempty}
  let : Nonempty S := ⟨⟨{Classical.arbitrary I}, Finset.singleton_nonempty _⟩⟩
  let : IsDirectedOrder S := ⟨fun a b =>
    ⟨⟨a.1 ∪ b.1, a.2.mono Finset.subset_union_left⟩,
      Finset.subset_union_left, Finset.subset_union_right⟩⟩
  let F : S → M → EReal := fun s x => s.1.sup' s.2 (fun i => u i x)
  have hF (s : S) : (ofFixedModel n M).IsThetaPSH θ (F s) ∧ sourceIGood (n := n) (F s) :=
    sourceIGood_finset_sup omega u s.1 s.2 (fun i _ => hpsh i) (fun i _ => hgood i)
  have hmono : Monotone F := by
    intro s t hst x
    exact (Finset.sup'_le_iff s.2 (fun i => u i x)).mpr
      (fun i hi => Finset.le_sup' (fun j => u j x) (hst hi))
  have hFC (s : S) (x : M) : F s x ≤ (C : EReal) :=
    (Finset.sup'_le_iff s.2 (fun i => u i x)).mpr
      (fun i _ => hC (u i) (mem_range_self i) x (mem_univ x))
  let γ := atlasClosedFormToNative θ + omega.form
  have hγ : IsBigClass (RealBottChern.ofRepresentative γ) := by
    simpa only [one_smul] using
      PositiveCurrentAssembly.isBigClass_add_smul_of_isThetaPshPotential omega
        (atlasClosedFormToNative θ)
        ((isThetaPSH_iff_nativeThetaPotential θ _).mp (hpsh (Classical.arbitrary I))) zero_lt_one
  let w : S → ThetaPshL1 γ.val := fun s =>
    ⟨F s, LocalPotentials.isThetaPshPotential_add_of_semipositive
      ((isThetaPSH_iff_nativeThetaPotential θ _).mp (hF s).1) omega.isSemipositive⟩
  let U : ThetaPshL1 γ.val :=
    ⟨uscRegularization (⨆ s, (w s).val),
      IncreasingMixedDirectedNets.isThetaPshPotential_regularized_of_uniformlyBounded
        (fun s => (w s).property) hFC⟩
  have hlim : Tendsto w atTop (@nhds (ThetaPshL1 γ.val)
      (singularityPseudoMetricSpace omega γ hγ).toUniformSpace.toTopologicalSpace U) :=
    SingularCanonicalSingularityIncreasing.tendsto_native_of_monotone_uniformlyBounded
      omega γ hγ w hmono hFC
  have hG : IGood (n := n) U.val :=
    IGoodNativeClosed.iGood_of_native_filter_limit omega γ hγ atTop w U
      (Eventually.of_forall fun s => (sourceIGood_iff_native _).mp (hF s).2) hlim
  have hraw : (⨆ s : S, (w s).val) = ⨆ i, u i := by
    funext x
    simp only [iSup_apply]
    change (⨆ s : S, F s x) = ⨆ i, u i x
    apply le_antisymm
    · apply iSup_le
      intro s
      exact (Finset.sup'_le_iff s.2 (fun i => u i x)).mpr
        (fun i _ => le_iSup (fun j => u j x) i)
    · apply iSup_le
      intro i
      let s : S := ⟨{i}, Finset.singleton_nonempty i⟩
      simpa only [F, s, Finset.sup'_singleton] using (le_iSup (fun s : S => F s x) s)
  apply (sourceIGood_iff_native _).mpr
  change IGood (n := n) (uscRegularization (⨆ s : S, (w s).val)) at hG
  rw [hraw] at hG
  exact hG

/-- EVERY original linear-operation clause, retaining the printed positive REAL scalar. -/
theorem source_i_good_linear_whole (omega : KahlerBackground n M)
    {u v : M → EReal} (hu : sourceIGood (n := n) u) (hv : sourceIGood (n := n) v)
    {c : ℝ} (hc : 0 < c) :
    sourceIGood (n := n) (fun x => u x+v x) ∧
      sourceIGood (n := n) (fun x => max (u x) (v x)) ∧
      sourceIGood (n := n) (fun x => (c : EReal)*u x) :=
  ⟨sourceIGood_add omega hu hv, sourceIGood_max omega hu hv, sourceIGood_pos_mul hu hc⟩

end SGPT.PSH.VariableComplexAtlas
