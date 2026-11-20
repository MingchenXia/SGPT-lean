import SGPT.Checks.Comparison.ThinApprox.BJSmallOriginalNets
import SGPT.Checks.Comparison.BJOriginalRegularity
import SGPT.Foundations.Envelope.Source.PSH

namespace SGPT.NAPotential.BJ
end SGPT.NAPotential.BJ
namespace SGPT.NAPotential.BJ.AppSeq
end SGPT.NAPotential.BJ.AppSeq
namespace SGPT.NAPotential.BJ.FixedRay
end SGPT.NAPotential.BJ.FixedRay
namespace SGPT.NAPotential.BJ.MaxClosure
end SGPT.NAPotential.BJ.MaxClosure
namespace SGPT.NAPotential.BJ.Pair3ClassStability
end SGPT.NAPotential.BJ.Pair3ClassStability
namespace SGPT.NAPotential.BJ.Pair3Div
end SGPT.NAPotential.BJ.Pair3Div
namespace SGPT.NAPotential.BJ.Printed
end SGPT.NAPotential.BJ.Printed
namespace SGPT.NAPotential.BJ.RationalPromotion
end SGPT.NAPotential.BJ.RationalPromotion
namespace SGPT.NAPotential.BJ.SourceDXZPositive
end SGPT.NAPotential.BJ.SourceDXZPositive
namespace SGPT.NAPotential.BJ.SourceDivUnique
end SGPT.NAPotential.BJ.SourceDivUnique
namespace SGPT.NAPotential.BJ.SourceNet
end SGPT.NAPotential.BJ.SourceNet
namespace SGPT.NAPotential.BJ.SourceRationalPromotion
end SGPT.NAPotential.BJ.SourceRationalPromotion
namespace SGPT.NAPotential.BJCycle
end SGPT.NAPotential.BJCycle
namespace SGPT.NAPotential.BJModel
end SGPT.NAPotential.BJModel
namespace SGPT.NAPotential.ThinApprox.BJ
end SGPT.NAPotential.ThinApprox.BJ
namespace SGPT.NAPotential.ThinApprox.BJ.AppSeq
end SGPT.NAPotential.ThinApprox.BJ.AppSeq
namespace SGPT.NAPotential.ThinApprox.BJ.FixedRay
end SGPT.NAPotential.ThinApprox.BJ.FixedRay
namespace SGPT.NAPotential.ThinApprox.BJ.MaxClosure
end SGPT.NAPotential.ThinApprox.BJ.MaxClosure
namespace SGPT.NAPotential.ThinApprox.BJ.Pair3ClassStability
end SGPT.NAPotential.ThinApprox.BJ.Pair3ClassStability
namespace SGPT.NAPotential.ThinApprox.BJ.Pair3Div
end SGPT.NAPotential.ThinApprox.BJ.Pair3Div
namespace SGPT.NAPotential.ThinApprox.BJ.Printed
end SGPT.NAPotential.ThinApprox.BJ.Printed
namespace SGPT.NAPotential.ThinApprox.BJ.SourceDXZPositive
end SGPT.NAPotential.ThinApprox.BJ.SourceDXZPositive
namespace SGPT.NAPotential.ThinApprox.BJ.SourceDivUnique
end SGPT.NAPotential.ThinApprox.BJ.SourceDivUnique
namespace SGPT.NAPotential.ThinApprox.BJ.SourceNet
end SGPT.NAPotential.ThinApprox.BJ.SourceNet
namespace SGPT.NAPotential.ThinApprox.BJCycle
end SGPT.NAPotential.ThinApprox.BJCycle
namespace SGPT.NAPotential.ThinApprox.BJModel
end SGPT.NAPotential.ThinApprox.BJModel


/-! Genuine ONE-WAY admission of arbitrary-universe ORIGINAL rational GF
psh metrics into the existing native ample-order/real-weight predicate.
Every point/data/USC/class/size output is produced, not assumed. No inverse
topology/predicate comparison or unrestricted singular PSH2 is asserted. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
namespace SGPT.NAPotential.ThinApprox.BJ.Printed
open SGPT.NAPotential.BJ.Printed
open AlgebraicGeometry CategoryTheory Filter Topology
open SGPT.NAPotential.Berkovich SGPT.NAPotential.BJ.NativePicard
open SGPT.NAPotential.BJ SGPT.NAPotential.ThinApprox.BJ
open SGPT.Foundations.Envelope SGPT.Foundations.Envelope.NativeNumericalFubiniStudy
variable {X : Scheme.{0}} (p : X ⟶ Spec (.of ℂ)) [IsProjective p] [IsIntegral X]
local instance : IsProper p := (ProjectiveFactorizationRingIso.of_isProjective p).isProper

/-- Literal original rational metrics on ALL original points genuinely
satisfy every clause of the existing native predicate, in one direction. -/
theorem IsModuleTopologyPSH.isNativePSH
    {L : RationalPicardSpace X} {φ : BerkovichPoint p → EReal}
    (h : IsModuleTopologyPSH.{u} p L φ) :
    Variety.IsPSH p (SGPT.NAPotential.BJ.NativePicard.numericalClass p L)
      (fun y => φ ((pointEquiv p).symm y)) := by
  obtain ⟨hne,D,hclass,hlim⟩ := SGPT.NAPotential.ThinApprox.BJ.Printed.IsModuleTopologyPSH.shrink p h
  have hEval (i : D.I) (y : Variety.An p) :
      (D.term i).toNative.eval p y=(D.term i).eval p ((pointEquiv p).symm y) := by
    have hi := (D.term i).toNative_eval p ((pointEquiv p).symm y)
    simpa only [Equiv.apply_symm_apply] using hi
  have hneNative : ∃ y : Variety.An p,φ ((pointEquiv p).symm y)≠⊥ := by
    obtain ⟨v,hv⟩ := hne
    exact ⟨pointEquiv p v,by simpa only [Equiv.symm_apply_apply] using hv⟩
  have husc : UpperSemicontinuous (fun y => φ ((pointEquiv p).symm y)) :=
    (h.upperSemicontinuous p).comp (pointHomeomorph p).symm.continuous
  refine ⟨hneNative,husc,D.I,inferInstance,inferInstance,inferInstance,
    (fun i => (D.term i).toNative),(fun i => (D.term i).toNative_nonzero),?_,?_,?_⟩
  · exact (ampleTendsto_of_moduleTopology p hclass).congr'
      (Eventually.of_forall fun i => ((D.term i).toNative_numericalClass p).symm)
  · intro y i j hij
    change (D.term j).toNative.eval p y ≤ (D.term i).toNative.eval p y
    rw [hEval j y,hEval i y]
    exact D.decreasing ((pointEquiv p).symm y) hij
  · intro y
    rw [D.eq_limit_of_tendsto p hlim]
    change (⨅ i : D.I,(D.term i).eval p ((pointEquiv p).symm y))=
      ⨅ i : D.I,(D.term i).toNative.eval p y
    exact iInf_congr fun i => (hEval i y).symm

end SGPT.NAPotential.ThinApprox.BJ.Printed
