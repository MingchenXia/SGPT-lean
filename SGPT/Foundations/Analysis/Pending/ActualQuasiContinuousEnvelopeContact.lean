import SGPT.Foundations.Analysis.Pending.ActualNoncollapsedObstacleEnvelope
import SGPT.Foundations.Analysis.Pending.ActualNonpositiveQuasiContinuousEnvelopeContact
import SGPT.Foundations.Analysis.Pending.RooftopEnvelopeNormalization
import SGPT.Foundations.Analysis.Pending.RooftopDimZero
import SGPT.Foundations.Analysis.Pending.NonBigPotentialMass

set_option autoImplicit false

/-! # Genuine contact for arbitrary original quasi-continuous obstacles

Xia, PDF 0079--0083, Theorem 2.4.4. Original extended-real quasicontinuity
and actual noncollapse internally produce genuineness, a strict finite
envelope bound, normalization and contact. The non-big class and dimension
zero are retained; original measurability and boundedness are not assumed.
-/

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.ActualQuasiContinuousEnvelopeContact

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus DiagonalMass ThetaCapacity
  ActualExtendedObstacleQuasiContinuity RooftopEnvelopeNormalization

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

omit [MeasurableSpace M] [BorelSpace M] in
private theorem envelope_eq_obstacle_of_dim_zero (hn : n = 0)
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    {f : M → EReal} (hP : IsThetaPshPotential θ.val (rooftopEnvelope θ.val f)) :
    rooftopEnvelope θ.val f = f := by
  have hqe := PolydiskPatchBalayageContactQE.rooftopEnvelope_le_quasiEverywhere_of_kahler
    omega θ hP
  have hempty : {x | ¬ rooftopEnvelope θ.val f x ≤ f x} = ∅ := by
    subst hn
    exact PluripolarOuterCapacity.eq_empty_of_manifoldLocallyPluripolar_dim_zero hqe
  have hpf : ∀ x, rooftopEnvelope θ.val f x ≤ f x := by
    intro x
    by_contra h
    have hm : x ∈ ({y | ¬ rooftopEnvelope θ.val f y ≤ f y} : Set M) := h
    rw [hempty] at hm
    exact hm
  have hfbot : ∀ x, f x ≠ ⊥ := by
    intro x hx
    have hpbot : rooftopEnvelope θ.val f x ≤ ⊥ := by simpa only [hx] using hpf x
    exact RooftopDimZero.ne_bot_of_locallyNondegenerate_of_dim_zero hn hP.2 x
      (le_bot_iff.mp hpbot)
  funext x
  refine le_antisymm (hpf x) (le_of_not_gt fun hx => ?_)
  obtain ⟨r, hPr, hrf⟩ := EReal.lt_iff_exists_real_btwn.mp hx
  have hg : IsThetaPshPotential θ.val (fun y => min (f y) (r : EReal)) :=
    RooftopDimZero.isThetaPshPotential_of_dim_zero hn hP.1.hasSmoothLocalPotentials
      (fun y => ne_top_of_le_ne_top (EReal.coe_ne_top r) (min_le_right _ _))
      (fun y => ne_of_gt (lt_min (bot_lt_iff_ne_bot.mpr (hfbot y)) (EReal.bot_lt_coe r)))
  have hle := le_rooftopEnvelope hg
    (quasiEverywhere_of_forall fun y => min_le_left (f y) (r : EReal)) x
  rw [min_eq_right hrf.le] at hle
  exact hPr.not_ge hle

/-- Original extended-real quasicontinuity and actual two-sided noncollapse
internally give the genuine envelope and both actual contact nullities,
including non-big classes and dimension zero. -/
theorem exists_genuine_envelope_and_contact (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {f : M → EReal}
    (hf : QuasiContinuousERealFor (thetaCapacity omega.form (fun _ => 0)) f)
    (hnb : rooftopEnvelope θ.val f ≠ (fun _ => ⊥))
    (hnt : rooftopEnvelope θ.val f ≠ (fun _ => ⊤)) :
    ∃ hP : IsThetaPshPotential θ.val (rooftopEnvelope θ.val f),
      diagonalPotentialMeasure θ (rooftopEnvelope θ.val f) hP
        {x | rooftopEnvelope θ.val f x < f x} = 0 ∧
      diagonalPotentialMeasure θ (rooftopEnvelope θ.val f) hP
        {x | rooftopEnvelope θ.val f x ≠ f x} = 0 := by
  classical
  have hP := ActualNoncollapsedObstacleEnvelope.isThetaPshPotential_of_ne_infinities
    omega θ hnb hnt
  have hstrict : diagonalPotentialMeasure θ (rooftopEnvelope θ.val f) hP
      {x | rooftopEnvelope θ.val f x < f x} = 0 := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · have heq := envelope_eq_obstacle_of_dim_zero hn omega θ hP
      simp only [heq, lt_self_iff_false, ofPred_false, measure_empty]
    · by_cases hbig : IsBigClass (RealBottChern.ofRepresentative θ)
      · obtain ⟨D, hD⟩ := hP.exists_global_upper_bound
        let C : ℝ := D + 1
        have hPC : ∀ x, rooftopEnvelope θ.val f x < (C : EReal) := fun x =>
          (hD x).trans_lt (EReal.coe_lt_coe_iff.mpr (by dsimp [C]; linarith))
        let F : M → EReal := fun x => min (f x) (C : EReal) + ((-C : ℝ) : EReal)
        obtain ⟨hF0, henv⟩ := rooftopEnvelope_normalization θ.val (fun x => (hPC x).le)
        change rooftopEnvelope θ.val F =
          (fun x => rooftopEnvelope θ.val f x + ((-C : ℝ) : EReal)) at henv
        have hT : Continuous (fun z : EReal => min z (C : EReal) + ((-C : ℝ) : EReal)) := by
          apply continuous_iff_continuousAt.mpr
          intro z
          exact (EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot (-C)))
            (Or.inr (EReal.coe_ne_top (-C)))).comp
              (((continuous_id.inf continuous_const).prodMk continuous_const).continuousAt)
        have hFqc : QuasiContinuousERealFor (thetaCapacity omega.form (fun _ => 0)) F := by
          intro η hη
          obtain ⟨G, hGo, hGc, hfc⟩ := hf η hη
          exact ⟨G, hGo, hGc, hT.comp_continuousOn hfc⟩
        have hFP : IsThetaPshPotential θ.val (rooftopEnvelope θ.val F) := by
          rw [henv]
          exact hP.add_const (-C)
        have hFnb : rooftopEnvelope θ.val F ≠ (fun _ => ⊥) := by
          obtain ⟨y, _hy, hyb⟩ := hFP.2 (Classical.arbitrary M) univ isOpen_univ (mem_univ _)
          intro h
          exact hyb (congrFun h y)
        obtain ⟨hQ, hcontact⟩ :=
          ActualNonpositiveQuasiContinuousEnvelopeContact.exists_genuine_envelope_and_contact
            hn omega θ hbig hF0 hFqc hFnb
        have hμ : diagonalPotentialMeasure θ (rooftopEnvelope θ.val F) hQ =
            diagonalPotentialMeasure θ (rooftopEnvelope θ.val f) hP := by
          simpa only [henv] using DiagonalMeasureRegularity.diagonalPotentialMeasure_add_const
            θ hP (-C) (hP.add_const (-C))
        rw [hμ] at hcontact
        refine measure_mono_null (t := {x | rooftopEnvelope θ.val F x < F x}) ?_ hcontact
        intro x hx
        change rooftopEnvelope θ.val F x < F x
        rw [henv]
        exact EReal.add_lt_add_right_coe (lt_min hx (hPC x)) (-C)
      · exact NonBigPotentialMass.diagonalPotentialMeasure_eq_zero_of_not_isBigClass
          omega θ hP hbig _
  refine ⟨hP, hstrict, ?_⟩
  have hqe := PolydiskPatchBalayageContactQE.rooftopEnvelope_le_quasiEverywhere_of_kahler
    omega θ hP
  have hbad : diagonalPotentialMeasure θ (rooftopEnvelope θ.val f) hP
      {x | ¬ rooftopEnvelope θ.val f x ≤ f x} = 0 :=
    GlobalNonPluripolar.globalMixedMeasure_doesNotChargeManifoldPluripolar
      (fun _ : Fin n => hP.1) _ hqe
  refine measure_mono_null
    (t := {x | rooftopEnvelope θ.val f x < f x} ∪ {x | ¬ rooftopEnvelope θ.val f x ≤ f x})
    ?_ (measure_union_null hstrict hbad)
  intro x hx
  by_cases hle : rooftopEnvelope θ.val f x ≤ f x
  · exact Or.inl (lt_of_le_of_ne hle hx)
  · exact Or.inr hle

end
end SGPT.Foundations.Analysis.Pending.ActualQuasiContinuousEnvelopeContact
