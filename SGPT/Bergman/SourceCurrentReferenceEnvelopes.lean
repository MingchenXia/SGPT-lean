import SGPT.Bergman.SourceBookKahlerCurrentPositiveMass
import SGPT.Bergman.SourceReferenceAdditiveInvariance
import SGPT.Bergman.SourceKahlerCurrentScalingTail
import SGPT.Bergman.SourcePartialEnvelopeMonotoneConvergence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Bergman.ReferenceEnvelopeConvergence

open Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending DiagonalMass
open SGPT.PSH.VariableComplexAtlas SGPT.Bergman.PartialEnvelope
open SGPT.Bergman.ContactConcentration SGPT.Bergman.MonotonePartialEnvelopes
open scoped Topology ENNReal

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]

/-- Actual original alpha-reference envelope infimum for a TRUE Kahler
current and original non-pluripolar weighted subset. Compact normalization,
scaled PSH, strict actual masses, source d_S topology convergence and the
whole original partial-envelope convergence are ALL produced internally.
No incoming PSH/mass/d_S/envelope-limit certificate for scaled references. -/
theorem partialEnvelope_eq_iInf_scaled_references_of_current
    (omega : KahlerBackground n X) (theta : ClosedRealOneOneForm n X)
    {phi : X → EReal} (hcurrent : IsKahlerCurrentPotential theta phi)
    (W : SGPT.Bergman.WeightedSubset.WeightedSubset n X)
    (alpha : ℕ → ℝ) (hmono : Monotone alpha) (hpos : ∀ k, 0 < alpha k)
    (hlt : ∀ k, alpha k < 1) (hlim : Tendsto alpha atTop (𝓝 1)) :
    partialEnvelope (nativeClosedFormToAtlas theta) phi W.carrier W.erealWeight =
      ⨅ k : ℕ, partialEnvelope (nativeClosedFormToAtlas theta)
        (fun x => ((alpha k : ℝ) : EReal) * phi x) W.carrier W.erealWeight := by
  have hnonempty := sourceNonPluripolar_ambient_nonempty (ofFixedModel n X) W.nonPluripolar_carrier
  let : Nonempty X := hnonempty
  obtain ⟨hphi, _hphipos⟩ := exists_source_positiveMass_of_nonPluripolar_and_kahlerCurrent
    omega theta W.nonPluripolar_carrier hcurrent
  obtain ⟨A, hA⟩ := hphi.exists_global_upper_bound
  let u : X → EReal := fun x => phi x - (A : EReal)
  have hu0 : ∀ x, u x ≤ 0 := sub_const_nonpositive_of_le hA
  have hcurrentu : IsKahlerCurrentPotential theta u := by
    obtain ⟨kappa, hstrict⟩ := hcurrent
    exact ⟨kappa, hstrict.sub_const A⟩
  obtain ⟨hun, hupos⟩ := exists_source_positiveMass_of_nonPluripolar_and_kahlerCurrent
    omega theta W.nonPluripolar_carrier hcurrentu
  obtain ⟨N, hscaled, hdist⟩ := exists_native_scaled_tail_distance_tendsto
    omega theta hcurrentu alpha hlt hlim
  let thetaA := nativeClosedFormToAtlas theta
  let ui : ℕ → X → EReal := fun j x => ((alpha (j + N) : ℝ) : EReal) * u x
  have hua : (ofFixedModel n X).IsThetaPSH thetaA u :=
    (isThetaPSH_iff_nativeThetaPotential thetaA u).mpr hun
  have huipos : ∀ j, 0 < sourcePotentialNonPluripolarMeasure thetaA (ui j)
      ((isThetaPSH_iff_nativeThetaPotential thetaA (ui j)).mpr (hscaled j)) univ := by
    intro j
    have hmore : MoreSingularOn u (ui j) univ := by
      apply MoreSingularOn.of_le
      intro x _
      have h := SGPT.PSH.MultiplierIdealInf.coe_mul_le_coe_mul_add
        (p := 1) (q := alpha (j + N)) (A := 0) (hpos (j + N)) (hlt (j + N)).le
        (show u x ≤ ((0 : ℝ) : EReal) from by simpa using hu0 x)
      simpa only [EReal.coe_one, one_mul, mul_zero, EReal.coe_zero, add_zero] using h
    have hp := hupos.trans_le (diagonalPotentialMass_mono_of_kahler omega hun (hscaled j) hmore)
    simpa only [sourcePotentialNonPluripolarMeasure, diagonalPotentialMass,
      thetaA, sourceNativeAtlasForm_roundTrip, ui] using hp
  have hui : ∀ j, (ofFixedModel n X).IsThetaPSH thetaA (ui j) := fun j =>
    (isThetaPSH_iff_nativeThetaPotential thetaA (ui j)).mpr (hscaled j)
  have hposa : 0 < sourcePotentialNonPluripolarMeasure thetaA u hua univ := by
    simpa only [sourcePotentialNonPluripolarMeasure, diagonalPotentialMass,
      thetaA, sourceNativeAtlasForm_roundTrip] using hupos
  have hanti : Antitone ui := by
    intro j k hjk x
    have h := SGPT.PSH.MultiplierIdealInf.coe_mul_le_coe_mul_add
      (hpos (j + N)) (hmono (Nat.add_le_add_right hjk N))
      (show u x ≤ ((0 : ℝ) : EReal) from by simpa using hu0 x)
    simpa only [mul_zero, EReal.coe_zero, add_zero] using h
  let big := sourcePositiveMass_isBig omega hua hposa
  have htends : Tendsto (fun j => (⟨ui j, hui j⟩ : SourceThetaPotentialL1 thetaA)) atTop
      (@nhds (SourceThetaPotentialL1 thetaA) (sourceSingularityTopology omega thetaA big) ⟨u, hua⟩) := by
    let : PseudoMetricSpace (SourceThetaPotentialL1 thetaA) := sourceSingularityPseudoMetricSpace omega thetaA big
    let : UniformSpace (SourceThetaPotentialL1 thetaA) := sourceSingularityUniformSpace omega thetaA big
    let : TopologicalSpace (SourceThetaPotentialL1 thetaA) := sourceSingularityTopology omega thetaA big
    apply (tendsto_iff_dist_tendsto_zero (α := SourceThetaPotentialL1 thetaA)
      (f := fun j => (⟨ui j, hui j⟩ : SourceThetaPotentialL1 thetaA))
      (a := (⟨u, hua⟩ : SourceThetaPotentialL1 thetaA))).mpr
    simpa only [sourceSingularityPseudoMetricSpace_dist, sourceSingularityDistance_eq_native,
      ui, thetaA, sourceNativeAtlasForm_roundTrip] using hdist
  have hconv := (partialEnvelopes_decreasing omega hui huipos hanti hua hposa htends W).1
  have htail : (⨅ j : ℕ, partialEnvelope thetaA
        (fun x => ((alpha (j + N) : ℝ) : EReal) * phi x) W.carrier W.erealWeight) =
      partialEnvelope thetaA phi W.carrier W.erealWeight := by
    calc
      _ = ⨅ j : ℕ, partialEnvelope thetaA (ui j) W.carrier W.erealWeight := by
        apply iInf_congr
        intro j
        exact (sourcePartialEnvelope_scaled_sub_const thetaA phi W.carrier W.erealWeight
          A (alpha (j + N)) (hpos (j + N))).symm
      _ = partialEnvelope thetaA u W.carrier W.erealWeight := hconv.2.1
      _ = _ := sourcePartialEnvelope_sub_const thetaA phi W.carrier W.erealWeight A
  apply le_antisymm
  · apply le_iInf
    intro k
    apply partialEnvelope_mono_singularity
    refine ⟨(1 - alpha k) * A, fun x _ => ?_⟩
    have h := SGPT.PSH.MultiplierIdealInf.coe_mul_le_coe_mul_add
      (p := 1) (hpos k) (hlt k).le (hA x)
    simpa only [EReal.coe_one, one_mul] using h
  · calc
      _ ≤ ⨅ j : ℕ, partialEnvelope thetaA
          (fun x => ((alpha (j + N) : ℝ) : EReal) * phi x) W.carrier W.erealWeight :=
        le_iInf (fun j => iInf_le _ (j + N))
      _ = _ := htail

end SGPT.Bergman.ReferenceEnvelopeConvergence
