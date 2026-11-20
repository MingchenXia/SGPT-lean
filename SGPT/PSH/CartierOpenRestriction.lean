import SGPT.PSH.LocalIntegralPullbackPresentation
import SGPT.Foundations.Analysis.Pending.OpensRestrictionMeasure
import SGPT.Foundations.Analysis.Pending.BlowupRestrictOpen

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open scoped Topology Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Actual open inclusion geometry supplies the genuine invertible ideal
restriction internally; no nonvanishing or differential certificate is an input. -/
def cartierOpenRestriction (D : EffectiveDivisor n M) (U : Opens M) : EffectiveDivisor n U :=
  GermIdealTotalTransform.EffectiveDivisor.totalTransform (OpensRestriction.contMDiff_val U)
    (by rw [OpensRestrictionMeasure.exceptionalLocus_val, interior_empty]) D

theorem cartierOpenRestriction_ideal (D : EffectiveDivisor n M) (U : Opens M) :
    (cartierOpenRestriction D U).ideal =
      GermIdeal.pullback (m := n) (Subtype.val : U → M) D.ideal := rfl

theorem cartierOpenRestriction_support (D : EffectiveDivisor n M) (U : Opens M) :
    (cartierOpenRestriction D U).support = (Subtype.val : U → M) ⁻¹' D.support :=
  BlowupExceptionalDivisor.zeroLocus_pullback (OpensRestriction.contMDiff_val U)
    (DivisorMetric.isCoherent_of_isInvertible D.isInvertible)

/-- Equality of FULL original reduced ideals at EVERY open-subtype stalk,
obtained from existing actual extension/restriction dictionaries. -/
theorem reducedIdeal_pullback_open_inclusion (U : Opens M) (A : Set M) :
    GermIdeal.pullback (m := n) (Subtype.val : U → M) (vanishingIdeal (n := n) A) =
      vanishingIdeal (n := n) ((Subtype.val : U → M) ⁻¹' A) := by
  calc
    _ = GermIdeal.pullback (m := n) (id : U → U)
        (vanishingIdeal (n := n) ((Subtype.val : U → M) ⁻¹' A)) :=
      (BlowupRestrictOpen.pullback_vanishingIdeal_opens U (id : U → U) A).symm
    _ = _ := GermIdeal.ext (funext fun y => funext fun b => propext
      BlowupExistenceCodimOne.pullback_id_vanishingIdeal_mem_iff)

theorem cartierOpenRestriction_generator (D : EffectiveDivisor n M) (U : Opens M)
    (y : U) (g : M → ℂ) (hg : HolomorphicAt n g (y : M))
    (hgen : ∀ h, D.ideal.mem (y : M) h ↔ IsInSpanAt (n := n) (· = g) (y : M) h)
    (b : U → ℂ) :
    (cartierOpenRestriction D U).ideal.mem y b ↔
      IsInSpanAt (n := n) (· = g ∘ Subtype.val) y b :=
  MemberPullback.pullback_mem_iff_of_generator (OpensRestriction.contMDiff_val U) hg hgen b

section Prime
variable {m : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]

/-- The restriction of a global prime is genuinely reduced on the original
open submanifold. Its local irreducible components are allowed to split. -/
theorem geometricPrimeOpenRestriction_ideal (P : GeometricPrimeCarrier (m + 1) X) (U : Opens X) :
    (cartierOpenRestriction (geometricPrimeCarrierEffectiveDivisor P) U).ideal =
      vanishingIdeal (n := m + 1) ((Subtype.val : U → X) ⁻¹' P.val) := by
  rw [cartierOpenRestriction_ideal, geometricPrimeCarrierEffectiveDivisor_ideal,
    reducedIdeal_pullback_open_inclusion]

end Prime
end SGPT.PSH
