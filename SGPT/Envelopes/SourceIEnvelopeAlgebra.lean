import SGPT.PSH.SourceIVolumeGoodness
import SGPT.Envelopes.SourceOrdinaryEnvelopeAlgebra
import SGPT.Foundations.Analysis.Pending.ActualIEnvelopePositiveScaling
import SGPT.Foundations.Analysis.Pending.ActualIEnvelopeAdditionConcavity
import SGPT.Foundations.Analysis.Pending.GlobalQuasiPshMaximumOrders

/-! # All four original I-envelope algebra clauses

Positive scalars are real, addition has independent original closed forms,
and every source ideal comparison retains its genuine QPSH domains.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

private theorem nativeIOrder_max_of_order {θ : SmoothRealForm n M 2}
    {u v w : M → EReal} (hu : IsThetaPshPotential θ u)
    (hv : IsThetaPshPotential θ v) (hw : IsThetaPshPotential θ w)
    (huw : IOrderOnManifold (n := n) u w) (hvw : IOrderOnManifold (n := n) v w) :
    IOrderOnManifold (n := n) (fun x => max (u x) (v x)) w := by
  have hua := (GlobalQuasiPshMaximumOrders.iOrderOnManifold_iff_iEquivalent_max hu hw).mp huw
  have hvb := (GlobalQuasiPshMaximumOrders.iOrderOnManifold_iff_iEquivalent_max hv hw).mp hvw
  have hlarge := IEquivalentMax.iEquivalentMaxClosed θ w
    (fun x => max (u x) (w x)) (fun x => max (v x) (w x)) hw
    (IsThetaPshPotential.max hu hw) (IsThetaPshPotential.max hv hw) hua hvb
  have hle := iOrderOnManifold_of_le
    (IsThetaPshPotential.max (IsThetaPshPotential.max hu hw)
      (IsThetaPshPotential.max hv hw)).1.quasiPlurisubharmonic
    (fun x => max_le_max (le_max_left (u x) (w x)) (le_max_left (v x) (w x)))
  exact hle.trans hlarge.1

/-- Two arbitrary source multiplier equivalences have their SAME genuine
source maximum types, retaining every positive-real chart ideal level. -/
theorem sourceIEquivalent_max
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u v a b : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hv : (ofFixedModel n M).IsThetaPSH θ v)
    (ha : (ofFixedModel n M).IsThetaPSH θ a) (hb : (ofFixedModel n M).IsThetaPSH θ b)
    (hua : sourceIEquivalent (ofFixedModel n M) u a)
    (hvb : sourceIEquivalent (ofFixedModel n M) v b) :
    sourceIEquivalent (ofFixedModel n M) (fun x => max (u x) (v x))
      (fun x => max (a x) (b x)) := by
  have hun := (isThetaPSH_iff_nativeThetaPotential θ u).mp hu
  have hvn := (isThetaPSH_iff_nativeThetaPotential θ v).mp hv
  have han := (isThetaPSH_iff_nativeThetaPotential θ a).mp ha
  have hbn := (isThetaPSH_iff_nativeThetaPotential θ b).mp hb
  have hmaxuv := (isThetaPSH_iff_nativeThetaPotential θ _).mpr
    (IsThetaPshPotential.max hun hvn)
  have hmaxab := (isThetaPSH_iff_nativeThetaPotential θ _).mpr
    (IsThetaPshPotential.max han hbn)
  have hIua := (sourceIEquivalent_iff_native ⟨θ, hu⟩ ⟨θ, ha⟩).mp hua
  have hIvb := (sourceIEquivalent_iff_native ⟨θ, hv⟩ ⟨θ, hb⟩).mp hvb
  apply (sourceIEquivalent_iff_native ⟨θ, hmaxuv⟩ ⟨θ, hmaxab⟩).mpr
  constructor
  · exact nativeIOrder_max_of_order hun hvn (IsThetaPshPotential.max han hbn)
      (hIua.1.trans (iOrderOnManifold_of_le
        (IsThetaPshPotential.max han hbn).1.quasiPlurisubharmonic (fun x => le_max_left _ _)))
      (hIvb.1.trans (iOrderOnManifold_of_le
        (IsThetaPshPotential.max han hbn).1.quasiPlurisubharmonic (fun x => le_max_right _ _)))
  · exact nativeIOrder_max_of_order han hbn (IsThetaPshPotential.max hun hvn)
      (hIua.2.trans (iOrderOnManifold_of_le
        (IsThetaPshPotential.max hun hvn).1.quasiPlurisubharmonic (fun x => le_max_left _ _)))
      (hIvb.2.trans (iOrderOnManifold_of_le
        (IsThetaPshPotential.max hun hvn).1.quasiPlurisubharmonic (fun x => le_max_right _ _)))

variable [CompactSpace M] [Nonempty M]
  {θ σ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u v : M → EReal}

/-- Whole printed positive REAL scaling clause, in the coefficient-scaled
original closed background; no mass or positivity premise is introduced. -/
theorem sourceIEnvelope_positiveScaling
    (hu : (ofFixedModel n M).IsThetaPSH θ u) {a : ℝ} (ha : 0 < a) :
    sourceIEnvelope (nativeClosedFormToAtlas (a • atlasClosedFormToNative θ))
      (fun x => (a : EReal) * u x) =
      fun x => (a : EReal) * sourceIEnvelope θ u x := by
  rw [sourceIEnvelope_eq_native _ _ (sourcePositiveScaling_thetaPSH hu ha),
    sourceNativeAtlasForm_roundTrip,
    ActualIEnvelopePositiveScaling.iSingularityEnvelope_smul (atlasClosedFormToNative θ)
      ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu) ha,
    ← sourceIEnvelope_eq_native θ u hu]

/-- Both independent original backgrounds retain their original chart
coefficients in the whole printed I-envelope addition inequality. -/
theorem sourceIEnvelope_independent_add_le
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hv : (ofFixedModel n M).IsThetaPSH σ v) :
    (fun x => sourceIEnvelope θ u x + sourceIEnvelope σ v x) ≤
      sourceIEnvelope
        (nativeClosedFormToAtlas (atlasClosedFormToNative θ + atlasClosedFormToNative σ))
        (fun x => u x + v x) := by
  rw [sourceIEnvelope_eq_native _ _ (sourceIndependentSum_thetaPSH hu hv),
    sourceNativeAtlasForm_roundTrip, sourceIEnvelope_eq_native θ u hu,
    sourceIEnvelope_eq_native σ v hv]
  exact ActualIEnvelopeAdditionConcavity.iSingularityEnvelope_add_le
    ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu)
    ((isThetaPSH_iff_nativeThetaPotential σ v).mp hv)

/-- Whole printed addition equivalence, including the genuine original
domains of BOTH source sums; all output domains are produced internally. -/
theorem sourceIEnvelope_independent_add_equivalent
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hv : (ofFixedModel n M).IsThetaPSH σ v) :
    sourceIEquivalent (ofFixedModel n M)
      (sourceIEnvelope
        (nativeClosedFormToAtlas (atlasClosedFormToNative θ + atlasClosedFormToNative σ))
        (fun x => u x + v x))
      (fun x => sourceIEnvelope θ u x + sourceIEnvelope σ v x) := by
  have hsum := sourceIndependentSum_thetaPSH hu hv
  have henvsum := sourceIndependentSum_thetaPSH
    (isThetaPSH_sourceIEnvelope hu) (isThetaPSH_sourceIEnvelope hv)
  have hadd : sourceIEquivalent (ofFixedModel n M) (fun x => u x + v x)
      (fun x => sourceIEnvelope θ u x + sourceIEnvelope σ v x) := by
    apply (sourceIEquivalent_iff_native ⟨_, hsum⟩ ⟨_, henvsum⟩).mpr
    exact ActualMultiplierOrderAddition.iEquivalentOnManifold_add
      ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu)
      ((isThetaPSH_iff_nativeThetaPotential σ v).mp hv)
      ((isThetaPSH_iff_nativeThetaPotential θ _).mp (isThetaPSH_sourceIEnvelope hu))
      ((isThetaPSH_iff_nativeThetaPotential σ _).mp (isThetaPSH_sourceIEnvelope hv))
      ((sourceIEquivalent_iff_native ⟨θ, hu⟩ ⟨θ, isThetaPSH_sourceIEnvelope hu⟩).mp
        (sourceIEquivalent_iEnvelope hu))
      ((sourceIEquivalent_iff_native ⟨σ, hv⟩ ⟨σ, isThetaPSH_sourceIEnvelope hv⟩).mp
        (sourceIEquivalent_iEnvelope hv))
  exact sourceIEquivalent_trans (sourceIEquivalent_symm (sourceIEquivalent_iEnvelope hsum)) hadd

/-- Whole original maximum clause, with genuine source maximum and its
all-level projection equivalence manufactured from the input potentials. -/
theorem sourceIEnvelope_max_equivalent
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hv : (ofFixedModel n M).IsThetaPSH θ v) :
    sourceIEquivalent (ofFixedModel n M) (sourceIEnvelope θ (fun x => max (u x) (v x)))
      (fun x => max (sourceIEnvelope θ u x) (sourceIEnvelope θ v x)) := by
  have hmax := (isThetaPSH_iff_nativeThetaPotential θ _).mpr
    (IsThetaPshPotential.max ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu)
      ((isThetaPSH_iff_nativeThetaPotential θ v).mp hv))
  exact sourceIEquivalent_trans (sourceIEquivalent_symm (sourceIEquivalent_iEnvelope hmax))
    (sourceIEquivalent_max hu hv (isThetaPSH_sourceIEnvelope hu) (isThetaPSH_sourceIEnvelope hv)
      (sourceIEquivalent_iEnvelope hu) (sourceIEquivalent_iEnvelope hv))

/-- All FOUR printed original `prop:PIconc` clauses, retaining arbitrary
positive real a, independent addition backgrounds, and the same-background maximum. -/
theorem sourceIEnvelope_algebra
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hv : (ofFixedModel n M).IsThetaPSH σ v)
    {w : M → EReal} (hw : (ofFixedModel n M).IsThetaPSH θ w) {a : ℝ} (ha : 0 < a) :
    (sourceIEnvelope (nativeClosedFormToAtlas (a • atlasClosedFormToNative θ))
      (fun x => (a : EReal) * u x) = fun x => (a : EReal) * sourceIEnvelope θ u x) ∧
      ((fun x => sourceIEnvelope θ u x + sourceIEnvelope σ v x) ≤
        sourceIEnvelope
          (nativeClosedFormToAtlas (atlasClosedFormToNative θ + atlasClosedFormToNative σ))
          (fun x => u x + v x)) ∧
      sourceIEquivalent (ofFixedModel n M)
        (sourceIEnvelope
          (nativeClosedFormToAtlas (atlasClosedFormToNative θ + atlasClosedFormToNative σ))
          (fun x => u x + v x))
        (fun x => sourceIEnvelope θ u x + sourceIEnvelope σ v x) ∧
      sourceIEquivalent (ofFixedModel n M)
        (sourceIEnvelope θ (fun x => max (u x) (w x)))
        (fun x => max (sourceIEnvelope θ u x) (sourceIEnvelope θ w x)) :=
  ⟨sourceIEnvelope_positiveScaling hu ha, sourceIEnvelope_independent_add_le hu hv,
    sourceIEnvelope_independent_add_equivalent hu hv, sourceIEnvelope_max_equivalent hu hw⟩

end SGPT.PSH.VariableComplexAtlas
