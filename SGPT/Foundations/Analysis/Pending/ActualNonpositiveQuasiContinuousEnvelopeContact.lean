import SGPT.Foundations.Analysis.Pending.ActualExtendedObstacleBorelRepresentative
import SGPT.Foundations.Analysis.Pending.ActualBoundedQuasiContinuousEnvelopeContact
import SGPT.Foundations.Analysis.Pending.RooftopTruncationConcentrationMeasurable
import SGPT.Foundations.Analysis.Pending.RooftopDecreasingLimitQE

set_option autoImplicit false

/-! # Genuine contact for original nonpositive unbounded obstacles

Xia, PDF 0080--0081, Step 1.2. Original extended-real quasicontinuity
and actual envelope noncollapse internally produce genuineness, Borel
representatives, all finite-stage contacts and decreasing concentration.
The nonpositive normalization and positive dimension are explicit.
-/

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.ActualNonpositiveQuasiContinuousEnvelopeContact

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus DiagonalMass
  ThetaCapacity CapacityWeightedConvergence ActualExtendedObstacleQuasiContinuity
  ContinuousObstacleEnvelopeContact RooftopObstacleQuasiEverywhere
  DominationPrincipleAffineContactProof PolydiskPatchBalayageContactQE

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

private theorem genuine_of_nonpositive {θ : ClosedRealOneOneForm n M}
    {f : M → EReal} (hf0 : ∀ x, f x ≤ 0)
    (hnb : rooftopEnvelope θ.val f ≠ (fun _ => ⊥)) :
    IsThetaPshPotential θ.val (rooftopEnvelope θ.val f) := by
  rcases eq_empty_or_nonempty (rooftopCompetitors θ.val f) with h | h
  · exact False.elim (hnb (rooftopEnvelope_of_empty h))
  · refine isThetaPshPotential_rooftop_of_nonempty h ⟨0, fun g hg => ?_⟩
    exact le_coe_of_ae_in_charts_le hg.1.1 continuous_const fun e => by
      filter_upwards [hg.2.ae_in_chart e volume] with z hz
      exact hz.trans (hf0 _)

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

/-- Nonpositive original extended-real quasicontinuity and actual envelope
noncollapse internally produce a genuine envelope and its contact nullity. -/
theorem exists_genuine_envelope_and_contact (hn : 0 < n)
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {f : M → EReal} (hf0 : ∀ x, f x ≤ 0)
    (hf : QuasiContinuousERealFor (thetaCapacity omega.form (fun _ => 0)) f)
    (hnb : rooftopEnvelope θ.val f ≠ (fun _ => ⊥)) :
    ∃ hP : IsThetaPshPotential θ.val (rooftopEnvelope θ.val f),
      diagonalPotentialMeasure θ (rooftopEnvelope θ.val f) hP
        {x | rooftopEnvelope θ.val f x < f x} = 0 := by
  classical
  obtain ⟨g, hgm, hg0, hgQC, E, _hEm, hEc, hfg⟩ :=
    ActualExtendedObstacleBorelRepresentative.exists_borel_representative omega hf0 hf
  have hEp : ManifoldLocallyPluripolar (n := n) E :=
    KahlerVolumePositive.manifoldLocallyPluripolar_of_outerCapacityZero' hn omega hEc
  have hfgQE : QuasiEverywhere (n := n) (fun x => f x = g x) := by
    refine hEp.mono fun x hx => ?_
    by_contra hxE
    exact hx (hfg hxE)
  have henv : rooftopEnvelope θ.val f = rooftopEnvelope θ.val g :=
    rooftopEnvelope_congr_qe hfgQE
  have hPg : IsThetaPshPotential θ.val (rooftopEnvelope θ.val g) :=
    genuine_of_nonpositive hg0 (by rwa [← henv])
  have hne := nonempty_rooftopCompetitors hPg
  let F : ℕ → M → ℝ := fun j x => (max (g x) (((-(j : ℝ)) : ℝ) : EReal)).toReal
  have hFfin : ∀ (j : ℕ) x, max (g x) (((-(j : ℝ)) : ℝ) : EReal) ≠ ⊥ ∧
      max (g x) (((-(j : ℝ)) : ℝ) : EReal) ≠ ⊤ := by
    intro j x
    have h0 : max (g x) (((-(j : ℝ)) : ℝ) : EReal) ≤ 0 :=
      max_le (hg0 x) (EReal.coe_nonpos.mpr (neg_nonpos.mpr (Nat.cast_nonneg j)))
    exact ⟨ne_of_gt ((EReal.bot_lt_coe (-(j : ℝ))).trans_le (le_max_right _ _)),
      ne_of_lt (h0.trans_lt (by norm_num : (0 : EReal) < ⊤))⟩
  have hFcast : ∀ j x, (F j x : EReal) = max (g x) (((-(j : ℝ)) : ℝ) : EReal) :=
    fun j x => EReal.coe_toReal (hFfin j x).2 (hFfin j x).1
  have hFb : ∀ (j : ℕ) x, -(j : ℝ) ≤ F j x ∧ F j x ≤ 0 := by
    intro j x
    constructor
    · exact EReal.coe_le_coe_iff.mp (by rw [hFcast]; exact le_max_right _ _)
    · apply EReal.coe_nonpos.mp
      rw [hFcast]
      exact max_le (hg0 x) (EReal.coe_nonpos.mpr (neg_nonpos.mpr (Nat.cast_nonneg j)))
  have hFqc : ∀ j, QuasiContinuousFor (thetaCapacity omega.form (fun _ => 0)) (F j) := by
    intro j
    simpa only [F, EReal.coe_zero, min_eq_left (hg0 _)] using
      quasiContinuousFor_clamp (neg_nonpos.mpr (Nat.cast_nonneg j)) hgQC
  choose hp hc using fun j : ℕ =>
    ActualBoundedQuasiContinuousEnvelopeContact.exists_genuine_envelope_and_contact
      hn omega θ hbig (by positivity : 0 ≤ (j : ℝ))
      (fun x => abs_le.mpr ⟨(hFb j x).1, (hFb j x).2.trans (by positivity)⟩) (hFqc j)
  let p : ℕ → M → EReal := fun j => rooftopEnvelope θ.val (fun x => (F j x : EReal))
  have hple : ∀ j, QuasiEverywhere (n := n) (fun x => p j x ≤ (F j x : EReal)) :=
    fun j => rooftopEnvelope_le_quasiEverywhere_of_kahler omega θ (hp j)
  have hp0 : ∀ j x, p j x ≤ 0 := by
    intro j
    exact le_coe_of_ae_in_charts_le (hp j).1 continuous_const fun e => by
      filter_upwards [(hple j).ae_in_chart e volume] with z hz
      exact hz.trans (EReal.coe_nonpos.mpr (hFb j _).2)
  have hFa : ∀ x, Antitone (fun j => (F j x : EReal)) := by
    intro x j k hjk
    change (F k x : EReal) ≤ (F j x : EReal)
    rw [hFcast, hFcast]
    exact max_le_max le_rfl (EReal.coe_le_coe_iff.mpr (neg_le_neg (Nat.cast_le.mpr hjk)))
  have hFi : ∀ x, (⨅ j : ℕ, (F j x : EReal)) = g x := by
    intro x
    simp_rw [hFcast]
    exact RooftopUscDecreasingLimit.iInf_max_neg_natCast (g x)
  have hpa : ∀ x, Antitone (fun j => p j x) := fun x j k hjk =>
    rooftopEnvelope_mono (θ := θ.val) (fun y => hFa y hjk) x
  have hgp : ∀ j x, rooftopEnvelope θ.val g x ≤ p j x := fun j x =>
    rooftopEnvelope_mono (θ := θ.val) (fun y => by rw [hFcast]; exact le_max_left _ _) x
  have hpl : ∀ x, Tendsto (fun j => p j x) atTop (𝓝 (rooftopEnvelope θ.val g x)) :=
    fun x => RooftopDecreasingLimitQE.tendsto_rooftopEnvelope_of_antitone_qe
      (PluripolarOuterCapacity.countablyStablePluripolar omega)
      hFi hFa (fun j => (hp j).1) hple hne x
  have hzc : ∀ j, diagonalPotentialMeasure θ (p j) (hp j) {x | p j x < g x} = 0 := by
    intro j
    refine measure_mono_null (t := {x | p j x < (F j x : EReal)}) ?_ (hc j)
    intro x hx
    change p j x < (F j x : EReal)
    change p j x < g x at hx
    exact hx.trans_le (by rw [hFcast]; exact le_max_left _ _)
  have hgcontact : diagonalPotentialMeasure θ (rooftopEnvelope θ.val g) hPg
      {x | rooftopEnvelope θ.val g x < g x} = 0 :=
    RooftopTruncationConcentrationMeasurable.diagonalPotentialMeasure_lt_eq_zero_of_antitone_family
      hn hbig (MinimalSingularityLelongVanishing.isThetaPshPotential_thetaPshSupremum θ hbig)
      hgm hg0 (refTruncationsQuasiContinuous_of_original omega θ hbig hg0 hgQC)
      hp hp0 hpa hPg hgp hpl hzc
  have hPf : IsThetaPshPotential θ.val (rooftopEnvelope θ.val f) := by
    rw [henv]
    exact hPg
  refine ⟨hPf, ?_⟩
  simp only [henv]
  refine measure_mono_null (t := {x | rooftopEnvelope θ.val g x < g x} ∪ E) ?_ ?_
  · intro x hx
    by_cases hxE : x ∈ E
    · exact Or.inr hxE
    · apply Or.inl
      change rooftopEnvelope θ.val g x < g x
      change rooftopEnvelope θ.val g x < f x at hx
      rw [← hfg hxE]
      exact hx
  · exact measure_union_null hgcontact
      (GlobalNonPluripolar.globalMixedMeasure_doesNotChargeManifoldPluripolar
        (fun _ : Fin n => hPg.1) E hEp)

end
end SGPT.Foundations.Analysis.Pending.ActualNonpositiveQuasiContinuousEnvelopeContact
