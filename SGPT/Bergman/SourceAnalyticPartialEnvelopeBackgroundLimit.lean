import SGPT.Bergman.SourcePartialEnvelopeBackgroundMonotone
import SGPT.Bergman.SourceBookKahlerCurrentPositiveMass
import SGPT.Envelopes.SourceAnalyticEnvelopeComparison
import SGPT.Bergman.SourceWeightedSubset
import SGPT.Foundations.Analysis.Pending.TraceFreeLimit

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace SGPT.Bergman.BackgroundEnvelopeLimit

open Set Filter MeasureTheory SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Bergman.PartialEnvelope SGPT.Bergman.PartialEnvelopeRetention
open SGPT.Bergman.PartialEnvelopeSameType SGPT.Bergman.ReferenceEnvelopeConvergence
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending
open scoped Topology

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]

/-- Actual original epsilon-to-zero partial-envelope producer, source866-885.
The SAME analytic phi/current/weighted subset supplies masses, genuine
envelopes, nondegeneracy, singularity order and original admissibility.
No desired limit, output PSH, singularity-type or obstacle certificate enters. -/
theorem analytic_partialEnvelope_background_decreasing
    (omega : KahlerBackground n X) (theta : ClosedRealOneOneForm n X)
    {phi : X → EReal} (hcurrent : IsKahlerCurrentPotential theta phi)
    (han : (ofFixedModel n X).HasRationalAnalyticType phi)
    (W : SGPT.Bergman.WeightedSubset.WeightedSubset n X)
    {eps : ℕ → ℝ} (heps : ∀ j, 0 ≤ eps j) (hanti : Antitone eps)
    (hlim : Tendsto eps atTop (𝓝 0)) :
    (∀ x, Antitone fun j => partialEnvelope
      (nativeClosedFormToAtlas (theta + eps j • omega.form)) phi W.carrier W.erealWeight x) ∧
    (fun x => ⨅ j : ℕ, partialEnvelope
      (nativeClosedFormToAtlas (theta + eps j • omega.form)) phi W.carrier W.erealWeight x) =
      partialEnvelope (nativeClosedFormToAtlas theta) phi W.carrier W.erealWeight ∧
    (∀ x, Tendsto (fun j => partialEnvelope
      (nativeClosedFormToAtlas (theta + eps j • omega.form)) phi W.carrier W.erealWeight x)
      atTop (𝓝 (partialEnvelope (nativeClosedFormToAtlas theta)
        phi W.carrier W.erealWeight x))) := by
  let : Nonempty X := sourceNonPluripolar_ambient_nonempty
    (ofFixedModel n X) W.nonPluripolar_carrier
  let P : ℕ → X → EReal := fun j => partialEnvelope
    (nativeClosedFormToAtlas (theta + eps j • omega.form)) phi W.carrier W.erealWeight
  let Pbase := partialEnvelope (nativeClosedFormToAtlas theta) phi W.carrier W.erealWeight
  let U : X → EReal := fun x => ⨅ j, P j x
  obtain ⟨a, b, ha, hb⟩ := W.partialEnvelope_weight_bounds
  obtain ⟨hphin, hmassn⟩ := exists_source_positiveMass_of_nonPluripolar_and_kahlerCurrent
    omega theta W.nonPluripolar_carrier hcurrent
  have hphi : (ofFixedModel n X).IsThetaPSH (nativeClosedFormToAtlas theta) phi :=
    (isThetaPSH_iff_nativeThetaPotential _ _).mpr (by
      simpa only [sourceNativeAtlasForm_roundTrip] using hphin)
  have hmass : 0 < sourcePotentialNonPluripolarMeasure
      (nativeClosedFormToAtlas theta) phi hphi univ := by
    simpa only [sourcePotentialNonPluripolarMeasure, DiagonalMass.diagonalPotentialMass,
      sourceNativeAtlasForm_roundTrip] using hmassn
  obtain ⟨_C, _D, hbase, _hbaseI, _hCb, _hDb⟩ :=
    partialEnvelopes_genuine_bounded hphi hmass W.nonPluripolar_carrier ⟨a, ha⟩ ⟨b, hb⟩
  have hcurrentj (j : ℕ) : IsKahlerCurrentPotential (theta + eps j • omega.form) phi :=
    sourceKahlerCurrent_perturb_nonneg omega hcurrent (heps j)
  have hdata (j : ℕ) : ∃ hj : (ofFixedModel n X).IsThetaPSH
      (nativeClosedFormToAtlas (theta + eps j • omega.form)) phi,
      0 < sourcePotentialNonPluripolarMeasure
        (nativeClosedFormToAtlas (theta + eps j • omega.form)) phi hj univ := by
    obtain ⟨hn, hm⟩ := exists_source_positiveMass_of_nonPluripolar_and_kahlerCurrent
      omega _ W.nonPluripolar_carrier (hcurrentj j)
    have hj : (ofFixedModel n X).IsThetaPSH
        (nativeClosedFormToAtlas (theta + eps j • omega.form)) phi :=
      (isThetaPSH_iff_nativeThetaPotential _ _).mpr (by
        simpa only [sourceNativeAtlasForm_roundTrip] using hn)
    exact ⟨hj, by simpa only [sourcePotentialNonPluripolarMeasure,
      DiagonalMass.diagonalPotentialMass, sourceNativeAtlasForm_roundTrip] using hm⟩
  have hP (j : ℕ) : (ofFixedModel n X).IsThetaPSH
      (nativeClosedFormToAtlas (theta + eps j • omega.form)) (P j) := by
    obtain ⟨hj, hm⟩ := hdata j
    obtain ⟨_C, _D, hp, _hi, _hC, _hD⟩ :=
      partialEnvelopes_genuine_bounded hj hm W.nonPluripolar_carrier ⟨a, ha⟩ ⟨b, hb⟩
    exact hp
  have hPanti : ∀ x, Antitone fun j => P j x := fun x i j hij =>
    partialEnvelope_perturb_mono omega (hanti hij) phi W.carrier W.erealWeight x
  have hbaseU : Pbase ≤ U := by
    intro x
    apply le_iInf
    intro j
    have h := partialEnvelope_perturb_mono omega (theta := theta) (s := 0)
      (heps j) phi W.carrier W.erealWeight x
    simpa only [zero_smul, add_zero] using h
  have hPn (j : ℕ) : IsThetaPshPotential (theta + eps j • omega.form).val (P j) := by
    have h := (isThetaPSH_iff_nativeThetaPotential _ _).mp (hP j)
    simpa only [sourceNativeAtlasForm_roundTrip] using h
  have htail (i j : ℕ) : IsThetaPshPotential (theta + eps i • omega.form).val (P (i + j)) :=
    SGPT.Envelopes.PerturbedModelLimit.isThetaPshPotential_perturb_mono
      omega (hanti (Nat.le_add_right i j)) (hPn (i + j))
  have htail_eq (i : ℕ) : (fun x => ⨅ j, P (i + j) x) = U :=
    funext fun x => TraceFreeLimit.iInf_add_eq_iInf_of_antitone (hPanti x) i
  have hUi (i : ℕ) : ThetaPlurisubharmonic (theta + eps i • omega.form).val U := by
    rw [← htail_eq i]
    exact ThetaPshDecreasingLimit.thetaPlurisubharmonic_iInf_of_antitone
      (fun j => (htail i j).1)
      (fun x j k hjk => hPanti x (Nat.add_le_add_left hjk i))
  have hUraw : ThetaPlurisubharmonic theta.val U :=
    TraceFreeLimit.thetaPlurisubharmonic_of_forall_add_smul hanti hlim hUi
  have hbasen : IsThetaPshPotential theta.val Pbase := by
    have h := (isThetaPSH_iff_nativeThetaPotential _ _).mp hbase
    simpa only [sourceNativeAtlasForm_roundTrip] using h
  have hUn : IsThetaPshPotential theta.val U := ⟨hUraw, hbasen.2.mono hbaseU⟩
  have hU : (ofFixedModel n X).IsThetaPSH (nativeClosedFormToAtlas theta) U :=
    (isThetaPSH_iff_nativeThetaPotential _ _).mpr (by
      simpa only [sourceNativeAtlasForm_roundTrip] using hUn)
  have hUP : U ≤ P 0 := fun x => iInf_le (fun j => P j x) 0
  have hUobstacle : partialObstacle (n := n) W.carrier W.erealWeight U :=
    partialObstacle_of_le
      (partialEnvelope_obstacle _ phi W.nonPluripolar_carrier ⟨b, hb⟩) hUP
  obtain ⟨hphi0, hmass0⟩ := hdata 0
  obtain ⟨R, _hR, hbound⟩ := W.exists_real_abs_bound
  have htype := partialEnvelope_same_singularity_type omega hphi0 hmass0
    W.nonPluripolar_carrier W.weight ⟨R, hbound⟩
  have hmodel := (sourceAnalytic_envelope_comparison hphi0 han).2.1.2
  have hUphi : SGPT.PSH.SingularityLE U phi :=
    (MoreSingularOn.of_le (fun x _ => hUP x)).trans (htype.1.trans hmodel)
  have heq : U = Pbase := le_antisymm (le_partialEnvelope hU hUobstacle hUphi) hbaseU
  refine ⟨hPanti, heq, ?_⟩
  intro x
  change Tendsto (fun j => P j x) atTop (𝓝 (Pbase x))
  rw [← congrFun heq x]
  exact tendsto_atTop_iInf (hPanti x)

end SGPT.Bergman.BackgroundEnvelopeLimit
