import SGPT.Foundations.Analysis.Pending.ActualLocallyBoundedReferenceCapacity
import SGPT.Foundations.Analysis.Pending.QuasiContinuousMajorantFamily
import SGPT.Foundations.Analysis.Pending.PolydiskPatchBalayageContactQE
import SGPT.Foundations.Analysis.Pending.RooftopMajorantFamilyConcentrationQE
import SGPT.Foundations.Analysis.Pending.MinimalSingularityLelongVanishing
import SGPT.Foundations.Analysis.Pending.GlobalMeasureInvariance
import SGPT.Foundations.Analysis.Pending.RooftopEnvelopeNormalization
import SGPT.Foundations.Analysis.Pending.DominationPrincipleAffineContactProof

set_option autoImplicit false

/-! # Genuine contact for original bounded quasicontinuous obstacles

Xia, PDF 0082, bounded-obstacle Step 2. Actual bad opens, Tietze tail
suprema, genuine envelopes and lower-semicontinuous contact are produced
internally. Unbounded obstacles and dimension zero remain separate.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.ActualBoundedQuasiContinuousEnvelopeContact

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus DiagonalMass ThetaCapacity
  CapacityWeightedConvergence QuasiContinuousMajorantFamily
  PolydiskPatchBalayageContactQE RooftopMajorantFamilyConcentrationQE
  RooftopObstacleQuasiEverywhere ContinuousObstacleEnvelopeContact
  DominationPrincipleAffineContactProof

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

private theorem contact_of_nonpositive (hn : 0 < n)
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {F : M → ℝ} {C : ℝ} (hC : 0 ≤ C) (hF : ∀ x, F x ∈ Icc (-C) 0)
    (hQC : QuasiContinuousFor (thetaCapacity omega.form (fun _ => 0)) F) :
    ∃ hP : IsThetaPshPotential θ.val
      (rooftopEnvelope θ.val (fun x => (F x : EReal))),
      diagonalPotentialMeasure θ (rooftopEnvelope θ.val (fun x => (F x : EReal))) hP
        {x | rooftopEnvelope θ.val (fun y => (F y : EReal)) x < (F x : EReal)} = 0 := by
  classical
  have := DiagonalMeasureRegularity.metrizableSpace_of_isComplexManifold n M
  let r : ℝ≥0∞ := 2⁻¹
  have hr : 0 < r := by norm_num [r]
  have hr1 : r < 1 := by norm_num [r]
  choose G hGo hGc hFG using fun j : ℕ => hQC (r ^ j) (ENNReal.pow_pos hr j)
  let T (j : ℕ) : Set M := ⋃ k : ℕ, G (k + j)
  have hTo : ∀ j, IsOpen (T j) := fun j => isOpen_iUnion fun k => hGo (k + j)
  have hTa : Antitone T := by
    intro i j hij x hx
    obtain ⟨k, hk⟩ := mem_iUnion.mp hx
    have he : k + j - i + i = k + j := by omega
    exact mem_iUnion.mpr ⟨k + j - i, by rwa [he]⟩
  have hTc : ∀ j, thetaCapacity omega.form (fun _ => 0) (T j) ≤ r ^ j * 2 := by
    intro j
    calc thetaCapacity omega.form (fun _ => 0) (T j)
        ≤ ∑' k : ℕ, thetaCapacity omega.form (fun _ => 0) (G (k + j)) :=
          thetaCapacity_iUnion_le _ _ _
      _ ≤ ∑' k : ℕ, r ^ (k + j) := ENNReal.tsum_le_tsum fun k => (hGc (k + j)).le
      _ = r ^ j * 2 := by
          simp only [Nat.add_comm _ j, pow_add, ENNReal.tsum_mul_left, r,
            ENNReal.tsum_geometric_two]
  have hsmall : ∀ ε : ℝ≥0∞, 0 < ε → ∃ j, thetaCapacity omega.form (fun _ => 0) (T j) < ε := by
    intro ε hε
    have ht : Tendsto (fun j : ℕ => r ^ j * 2) atTop (𝓝 0) := by
      simpa only [zero_mul] using ENNReal.Tendsto.mul_const
        (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hr1)
        (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ∞))
    obtain ⟨j, hj⟩ := (ht.eventually_lt_const hε).exists
    exact ⟨j, (hTc j).trans_lt hj⟩
  have hFT : ∀ j, ContinuousOn F (T j)ᶜ := by
    intro j
    exact (hFG j).mono fun x hx hxG => hx (mem_iUnion.mpr ⟨0, by simpa using hxG⟩)
  obtain ⟨H, hHl, hHB, hHa, hHeq, _hHinf⟩ :=
    exists_antitone_lowerSemicontinuous_family hTo hTa hC hF hFT
  let f : M → EReal := fun x => ⨅ j : ℕ, (H j x : EReal)
  have hfB : ∀ x, ((-C : ℝ) : EReal) ≤ f x ∧ f x ≤ 0 := by
    intro x
    exact ⟨le_iInf fun j => EReal.coe_le_coe_iff.mpr (hHB j x).1,
      (iInf_le (fun j => (H j x : EReal)) 0).trans
        (EReal.coe_nonpos.mpr (hHB 0 x).2)⟩
  have hfeq : ∀ j x, x ∉ T j → f x = (F x : EReal) := by
    intro j x hx
    refine le_antisymm ?_ (le_iInf fun k => ?_)
    · exact (iInf_le (fun k => (H k x : EReal)) j).trans
        (by rw [hHeq j x hx])
    · rcases le_total k j with hkj | hjk
      · exact EReal.coe_le_coe_iff.mpr (by rw [← hHeq j x hx]; exact hHa x hkj)
      · rw [hHeq k x (fun hxk => hx (hTa hjk hxk))]
  have hfQC : QuasiContinuousFor (thetaCapacity omega.form (fun _ => 0))
      (fun x => (f x).toReal) := by
    intro ε hε
    obtain ⟨j, hj⟩ := hsmall ε hε
    refine ⟨T j, hTo j, hj, (hFT j).congr ?_⟩
    intro x hx
    change (f x).toReal = F x
    rw [hfeq j x hx, EReal.toReal_coe]
  let Z : Set M := ⋂ j : ℕ, T j
  have hZo : PluripolarCapacityZero.OuterCapacityZero omega Z := by
    intro ε hε
    obtain ⟨j, hj⟩ := hsmall ε hε
    exact ⟨T j, hTo j, iInter_subset T j, hj⟩
  have hZp : ManifoldLocallyPluripolar (n := n) Z :=
    KahlerVolumePositive.manifoldLocallyPluripolar_of_outerCapacityZero' hn omega hZo
  have hfF : QuasiEverywhere (n := n) (fun x => f x = (F x : EReal)) := by
    refine hZp.mono fun x hx => ?_
    by_contra hxZ
    obtain ⟨j, hj⟩ : ∃ j, x ∉ T j := by simpa only [Z, mem_iInter, not_forall] using hxZ
    exact hx (hfeq j x hj)
  have hV := MinimalSingularityLelongVanishing.isThetaPshPotential_thetaPshSupremum θ hbig
  have hV0 := thetaPshSupremum_le_zero θ.val
  have hpot : ∀ a : M → EReal,
      (∀ x, ((-C : ℝ) : EReal) ≤ a x ∧ a x ≤ 0) →
      IsThetaPshPotential θ.val (rooftopEnvelope θ.val a) := by
    intro a ha
    refine isThetaPshPotential_rooftop_of_nonempty ?_ ?_
    · refine ⟨fun x => thetaPshSupremum θ.val x + ((-C : ℝ) : EReal),
        hV.add_const _, quasiEverywhere_of_forall fun x => ?_⟩
      calc thetaPshSupremum θ.val x + ((-C : ℝ) : EReal)
          ≤ 0 + ((-C : ℝ) : EReal) := add_le_add (hV0 x) le_rfl
        _ = ((-C : ℝ) : EReal) := zero_add _
        _ ≤ a x := (ha x).1
    · refine ⟨0, fun g hg => le_coe_of_ae_in_charts_le hg.1.1 continuous_const ?_⟩
      intro e
      filter_upwards [hg.2.ae_in_chart e volume] with z hz
      exact hz.trans (ha _).2
  have hp : ∀ j, IsThetaPshPotential θ.val
      (rooftopEnvelope θ.val (fun x => (H j x : EReal))) :=
    fun j => hpot _ fun x => ⟨EReal.coe_le_coe_iff.mpr (hHB j x).1,
      EReal.coe_nonpos.mpr (hHB j x).2⟩
  have hple := fun j => rooftopEnvelope_le_quasiEverywhere_of_kahler omega θ (hp j)
  have hcstage : ∀ j, diagonalPotentialMeasure θ
      (rooftopEnvelope θ.val (fun x => (H j x : EReal))) (hp j)
      {x | rooftopEnvelope θ.val (fun y => (H j y : EReal)) x < (H j x : EReal)} = 0 := by
    intro j
    exact diagonalPotentialMeasure_rooftopEnvelope_lt_eq_zero_of_lowerSemicontinuous_kahler
      hn omega θ hbig hV (hHl j) (fun x => abs_le.mpr
        ⟨(hHB j x).1, (hHB j x).2.trans hC⟩) (hp j)
  have hw := hpot f hfB
  have hw0 : ∀ x, rooftopEnvelope θ.val f x ≤ 0 := by
    exact le_coe_of_ae_in_charts_le hw.1 continuous_const fun e => by
      filter_upwards [(rooftopEnvelope_le_quasiEverywhere_of_kahler omega θ hw).ae_in_chart e volume]
        with z hz
      exact hz.trans (hfB _).2
  have hfqc : ∀ Ω : Set M, IsOpen Ω →
      PatchLocalBoundedMeasure.IsBoundedPotentialOn (thetaPshSupremum θ.val) Ω →
      ∀ K : Set M, IsCompact K → K ⊆ Ω → ∀ ε : ℝ, 0 < ε →
      ∃ G : Set M, IsOpen G ∧
        thetaCapacity θ (thetaPshSupremum θ.val) G < ENNReal.ofReal ε ∧
        ContinuousOn (fun x => (f x).toReal) (K \ G) := by
    intro Ω hΩ hVb K _hK hKΩ ε hε
    obtain ⟨c, d, hcd⟩ := hVb
    obtain ⟨G, hGo, _hGΩ, hGc, hcont⟩ :=
      ActualLocallyBoundedReferenceCapacity.exists_isOpen_capacity_lt_continuousOn omega θ hV0
        hΩ (fun x hx => (hcd x hx).1) hfQC hε
    exact ⟨G, hGo, hGc, hcont.mono fun x hx => ⟨hKΩ hx.1, hx.2⟩⟩
  have hfc : ∀ x, thetaPshSupremum θ.val x + ((-C : ℝ) : EReal) ≤ f x := by
    intro x
    calc thetaPshSupremum θ.val x + ((-C : ℝ) : EReal)
        ≤ 0 + ((-C : ℝ) : EReal) := add_le_add (hV0 x) le_rfl
      _ = ((-C : ℝ) : EReal) := zero_add _
      _ ≤ f x := (hfB x).1
  have hgap : ∀ δ : ℝ, 0 < δ → diagonalPotentialMeasure θ (rooftopEnvelope θ.val f) hw
      {x | rooftopEnvelope θ.val f x + (δ : EReal) < f x} = 0 := by
    intro δ hδ
    exact diagonalPotentialMeasure_rooftopEnvelope_lt_add_eq_zero_of_majorants_qe hn
      (PluripolarOuterCapacity.countablyStablePluripolar omega)
      hbig hV (fun j x => (hHB j x).2) (fun j x => iInf_le _ j)
      (hHa) (fun _ => rfl) hp hple hcstage hfc (fun x => (hfB x).2) hfqc hw hw0 hδ
  have hstrict : diagonalPotentialMeasure θ (rooftopEnvelope θ.val f) hw
      {x | rooftopEnvelope θ.val f x < f x} = 0 := by
    refine measure_mono_null (RooftopLocalConcentration.lt_subset_union_iUnion_add _ _) ?_
    exact measure_union_null
      (GlobalNonPluripolar.globalMixedMeasure_doesNotChargeManifoldPluripolar
        (fun _ : Fin n => hw.1) _ (quasiPsh_poles_manifoldLocallyPluripolar hw.quasiPshPotential))
      (measure_iUnion_null fun j => hgap _ (by positivity))
  have henv : rooftopEnvelope θ.val f = rooftopEnvelope θ.val (fun x => (F x : EReal)) :=
    rooftopEnvelope_congr_qe hfF
  have hPF := hpot (fun x => (F x : EReal))
    (fun x => ⟨EReal.coe_le_coe_iff.mpr (hF x).1, EReal.coe_nonpos.mpr (hF x).2⟩)
  refine ⟨hPF, ?_⟩
  simp only [← henv]
  refine measure_mono_null (t := {x | rooftopEnvelope θ.val f x < f x} ∪ Z) ?_ ?_
  · intro x hx
    by_cases hxZ : x ∈ Z
    · exact Or.inr hxZ
    · have he : f x = (F x : EReal) := by
        obtain ⟨j, hj⟩ : ∃ j, x ∉ T j := by simpa only [Z, mem_iInter, not_forall] using hxZ
        exact hfeq j x hj
      exact Or.inl (by change rooftopEnvelope θ.val f x < f x; rw [he]; exact hx)
  · exact measure_union_null hstrict
      (GlobalNonPluripolar.globalMixedMeasure_doesNotChargeManifoldPluripolar
        (fun _ : Fin n => hw.1) Z hZp)

/-- The original bounded quasicontinuous real obstacle produces its actual
genuine envelope and contact nullity, without stage/contact certificates. -/
theorem exists_genuine_envelope_and_contact (hn : 0 < n)
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {F : M → ℝ} {C : ℝ} (hC : 0 ≤ C) (hF : ∀ x, |F x| ≤ C)
    (hQC : QuasiContinuousFor (thetaCapacity omega.form (fun _ => 0)) F) :
    ∃ hP : IsThetaPshPotential θ.val
      (rooftopEnvelope θ.val (fun x => (F x : EReal))),
      diagonalPotentialMeasure θ (rooftopEnvelope θ.val (fun x => (F x : EReal))) hP
        {x | rooftopEnvelope θ.val (fun y => (F y : EReal)) x < (F x : EReal)} = 0 := by
  let F₀ : M → ℝ := fun x => F x - C
  have hF₀ : ∀ x, F₀ x ∈ Icc (-(2 * C)) 0 := by
    intro x
    obtain ⟨hl, hu⟩ := abs_le.mp (hF x)
    constructor <;> dsimp [F₀] <;> linarith
  have hQC₀ : QuasiContinuousFor (thetaCapacity omega.form (fun _ => 0)) F₀ := by
    intro ε hε
    obtain ⟨G, hGo, hGc, hcont⟩ := hQC ε hε
    exact ⟨G, hGo, hGc, hcont.sub continuousOn_const⟩
  obtain ⟨hp, hzero⟩ := contact_of_nonpositive hn omega θ hbig (by positivity) hF₀ hQC₀
  let p : M → EReal := rooftopEnvelope θ.val (fun x => (F₀ x : EReal))
  have hFshift : (fun x => (F₀ x : EReal) + (C : EReal)) = fun x => (F x : EReal) := by
    funext x
    rw [← EReal.coe_add]
    exact congrArg ((↑) : ℝ → EReal) (by dsimp [F₀]; ring)
  have he : rooftopEnvelope θ.val (fun x => (F x : EReal)) =
      fun x => p x + (C : EReal) := by
    have h := RooftopEnvelopeNormalization.rooftopEnvelope_add_const θ.val
      (fun x => (F₀ x : EReal)) C
    rw [hFshift] at h
    exact h
  have hP : IsThetaPshPotential θ.val
      (rooftopEnvelope θ.val (fun x => (F x : EReal))) := by
    rw [he]
    exact hp.add_const C
  have hsub : (fun x => rooftopEnvelope θ.val (fun y => (F y : EReal)) x - (C : EReal)) = p := by
    funext x
    rw [he]
    simp only [sub_eq_add_neg, ← EReal.coe_neg, add_assoc, ← EReal.coe_add,
      add_neg_cancel, EReal.coe_zero, add_zero]
  have hmass : diagonalPotentialMeasure θ p hp =
      diagonalPotentialMeasure θ (rooftopEnvelope θ.val (fun x => (F x : EReal))) hP := by
    have h := GlobalMeasureInvariance.globalMixedMeasure_sub_const
      (fun _ : Fin n => hP.1) (fun _ => C)
    have ht : (fun (_i : Fin n) x => rooftopEnvelope θ.val (fun y => (F y : EReal)) x -
        (C : EReal)) = fun _ : Fin n => p := funext fun _ => hsub
    rw [GlobalDiagonalScaling.globalMixedMeasure_congr rfl ht _ (fun _ : Fin n => hp.1)] at h
    exact h
  have hset : {x | rooftopEnvelope θ.val (fun y => (F y : EReal)) x < (F x : EReal)} =
      {x | p x < (F₀ x : EReal)} := by
    ext x
    change rooftopEnvelope θ.val (fun y => (F y : EReal)) x < (F x : EReal) ↔ _
    rw [he, ← congrFun hFshift x]
    constructor
    · intro h
      by_contra hn
      exact (not_le_of_gt h) (add_le_add (not_lt.mp hn) le_rfl)
    · intro h
      exact EReal.add_lt_add_right_coe h C
  refine ⟨hP, ?_⟩
  rw [← hmass, hset]
  exact hzero

end
end SGPT.Foundations.Analysis.Pending.ActualBoundedQuasiContinuousEnvelopeContact
