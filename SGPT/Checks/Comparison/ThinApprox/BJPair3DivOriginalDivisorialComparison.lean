import SGPT.Checks.Comparison.BJPair3DivNativeOriginalDivisorialReverse
import SGPT.Checks.Comparison.ThinApprox.BJPair3DivFinitePresentation
import SGPT.Checks.Comparison.ThinApprox.BJNativePSHAdmission
import SGPT.Foundations.Envelope.Global.Comparison

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


-- Lane BJ-PAIR (R5/thm:pshdetbydiv bridge): ported from `SGPT.Checks.Literature/SGPT.Checks.Literature/BJDivisorial/OriginalDivisorialComparison.lean`
-- (that library pins another SGPT.Foundations.Envelope revision and cannot be imported here); only the
-- imports, the `Alterations` namespace (now `SGPT.Support.Alterations`) and this file's namespace
-- (`Divisorial` -> `Pair3Div`, `ExternalClassStability` -> `Pair3ClassStability`) are changed.

/-! # Literal original divisorial comparison against an arbitrary usc function
Source SGPT76fde3d1, chapter_NApotential.tex942--944 (unchanged d3f272c3).
The source PSH input uses the unchanged original rational GF packages,
module topology and ALL original Berkovich points. The source test set is
its actual positive-rational divisorial points together with v_triv.
Every original/native dictionary is produced internally. The usc comparison
function is arbitrary, with no PSH condition. The stronger EReal version
uses the true finite bound at v_triv and therefore includes all source poles.
-/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial SGPT.Support.Alterations
open scoped Classical NNReal

universe u
namespace SGPT.NAPotential.ThinApprox.BJ.Pair3Div
open SGPT.NAPotential.BJ.Pair3Div
open SGPT.Foundations.Envelope SGPT.Foundations.Envelope.Berkovich SGPT.NAPotential.Berkovich
open SGPT.NAPotential.BJ SGPT.NAPotential.ThinApprox.BJ SGPT.NAPotential.BJ.NativePicard SGPT.NAPotential.BJ.Printed SGPT.NAPotential.ThinApprox.BJ.Printed

variable {X : Scheme.{0}} [IsIntegral X]
  (p : X ⟶ Spec (.of ℂ)) [IsProjective p]

/-- The WHOLE source theorem thm:pshdetbydiv, with the even stronger arbitrary
usc EReal-valued comparison function. No comparison/correspondence model,
field equivalence, countability or extra geometry is a caller hypothesis. -/
theorem original_le_of_sourceDivisorial_le
    {L : RationalPicardSpace X} {φ ψ : BerkovichPoint p → EReal}
    (hφ : IsModuleTopologyPSH.{u} p L φ) (hψ : UpperSemicontinuous ψ)
    (hle : ∀ v ∈ sourceDivisorialSet p, φ v ≤ ψ v) : φ ≤ ψ := by
  let θ := SGPT.NAPotential.BJ.NativePicard.numericalClass p L
  obtain ⟨r,d,q,hp,hq,a,ha⟩ := SGPT.NAPotential.ThinApprox.BJ.Pair3ClassStability.exists_simultaneous_presentation p
    (fun _ : Fin 1 => θ)
  let := hq
  let := p.stalkAlgebra (genericPoint X)
  let P := FiniteProjectiveNativeFieldModels.model q p hp
  let e := OriginalProjectiveDiagonalNativeComparison.originalNativeModelHomeomorph q p hp
  let back : P.an → BerkovichPoint p := fun v => (pointEquiv p).symm (e.symm v)
  have hback : Continuous back :=
    (pointHomeomorph p).symm.continuous.comp e.symm.continuous
  let Φ : P.an → EReal := φ ∘ back
  have hmodel : P.IsPSH (a 0) Φ := by
    apply (SGPT.NAPotential.ThinApprox.NativeComparison.isPSH_iff_presentation d q p hp (a 0)
      (fun y => φ ((pointEquiv p).symm y))).mp
    rw [← ha 0]
    exact SGPT.NAPotential.ThinApprox.BJ.Printed.IsModuleTopologyPSH.isNativePSH p hφ
  obtain ⟨C,hC⟩ := hφ.trivial_finite p
  have hbound (v : BerkovichPoint p) : φ v ≤ (C : EReal) :=
    (hφ.le_trivial p v).trans_eq hC
  let Ψ : P.an → EReal := fun v => min (ψ (back v)) (C : EReal)
  have husc : UpperSemicontinuous Ψ :=
    (hψ.comp hback).inf upperSemicontinuous_const
  have htop (v : P.an) : Ψ v ≠ ⊤ :=
    ne_of_lt ((min_le_right _ _).trans_lt (EReal.coe_lt_top C))
  have hdiv (v : P.an) (hv : P.IsDivisorial v) : Φ v ≤ Ψ v := by
    exact le_min (hle (back v) (nativeDivisorial_original_mem_source p q hp v hv)) (hbound (back v))
  have hcomp := hmodel.le_of_forall_isDivisorial_le husc htop hdiv
  intro v
  have h := hcomp (e (pointEquiv p v))
  have hh : φ v ≤ min (ψ v) (C : EReal) := by
    simpa only [Φ,Ψ,back,Function.comp_apply,Homeomorph.symm_apply_apply,
      Equiv.symm_apply_apply] using h
  exact hh.trans (min_le_left _ _)

end SGPT.NAPotential.ThinApprox.BJ.Pair3Div
