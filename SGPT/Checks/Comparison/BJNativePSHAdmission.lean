import SGPT.Checks.Comparison.BJSmallOriginalNets
import SGPT.Checks.Comparison.BJOriginalRegularity
import SGPT.Foundations.Envelope.Source.PSH

/-! Genuine ONE-WAY admission of arbitrary-universe ORIGINAL rational GF
psh metrics into the existing native ample-order/real-weight predicate.
Every point/data/USC/class/size output is produced, not assumed. No inverse
topology/predicate comparison or unrestricted singular PSH2 is asserted. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
namespace SGPT.NAPotential.BJ.Printed
open AlgebraicGeometry CategoryTheory Filter Topology
open SGPT.NAPotential.Berkovich SGPT.NAPotential.BJ.NativePicard
open SGPT.NAPotential.BJ
open SGPT.Foundations.Envelope SGPT.Foundations.Envelope.NativeNumericalFubiniStudy
variable {X : Scheme.{0}} (p : X ⟶ Spec (.of ℂ)) [IsProjective p] [IsIntegral X]
local instance : IsProper p := (ProjectiveFactorizationRingIso.of_isProjective p).isProper

/-- Literal original rational metrics on ALL original points genuinely
satisfy every clause of the existing native predicate, in one direction. -/
theorem IsModuleTopologyPSH.isNativePSH
    {L : RationalPicardSpace X} {φ : BerkovichPoint p → EReal}
    (h : IsModuleTopologyPSH.{u} p L φ) :
    Variety.IsPSH p (NativePicard.numericalClass p L)
      (fun y => φ ((pointEquiv p).symm y)) := by
  obtain ⟨hne,D,hclass,hlim⟩ := h.shrink p
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

end SGPT.NAPotential.BJ.Printed
