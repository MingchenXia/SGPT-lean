import SGPT.Okounkov.SourceValuativeKahlerQEABarrier
import SGPT.Foundations.Analysis.Pending.ActualMultiplierOrderAddition
import SGPT.Foundations.Analysis.Pending.ActualIEnvelopePositiveScaling

set_option autoImplicit false
noncomputable section
namespace SGPT.Okounkov.SourceValuativeClosure
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Foundations.Analysis.Pending ThetaPshConvexCombination
open SGPT.Okounkov.TranscendentalCore

/-- Actual all-positive-exponent multiplier order is preserved by a
genuine REAL convex current mixture; every theta-PSH/scaled domain is
produced on the same original background, with original poles retained. -/
theorem iOrderOnManifold_convexComb {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {θ : ClosedRealOneOneForm n M} {u v a b : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential θ.val v)
    (ha : IsThetaPshPotential θ.val a) (hb : IsThetaPshPotential θ.val b)
    (hua : IOrderOnManifold (n := n) u a) (hvb : IOrderOnManifold (n := n) v b)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    IOrderOnManifold (n := n) (convexComb t u v) (convexComb t a b) := by
  have hs : 0 < 1 - t := sub_pos.mpr ht1
  exact ActualMultiplierOrderAddition.iOrderOnManifold_add
    (isThetaPshPotential_nonneg_smul hu ht0.le)
    (isThetaPshPotential_nonneg_smul hv hs.le)
    (isThetaPshPotential_nonneg_smul ha ht0.le)
    (isThetaPshPotential_nonneg_smul hb hs.le)
    (ActualIEnvelopePositiveScaling.iOrderOnManifold_smul hua ht0)
    (ActualIEnvelopePositiveScaling.iOrderOnManifold_smul hvb hs)

end SGPT.Okounkov.SourceValuativeClosure
