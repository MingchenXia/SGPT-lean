import SGPT.Checks.Comparison.BJPair3DivNativeOriginalDivisorialReverse
import SGPT.Checks.Comparison.BJPair3DivFinitePresentation
import SGPT.Checks.Comparison.BJNativePSHAdmission
import SGPT.Foundations.Envelope.Global.Comparison

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
namespace SGPT.NAPotential.BJ.Pair3Div
open SGPT.Foundations.Envelope SGPT.Foundations.Envelope.Berkovich SGPT.NAPotential.Berkovich
open SGPT.NAPotential.BJ SGPT.NAPotential.BJ.NativePicard SGPT.NAPotential.BJ.Printed

variable {X : Scheme.{0}} [IsIntegral X]
  (p : X ⟶ Spec (.of ℂ)) [IsProjective p]

/-- The WHOLE source theorem thm:pshdetbydiv, with the even stronger arbitrary
usc EReal-valued comparison function. No comparison/correspondence model,
field equivalence, countability or extra geometry is a caller hypothesis. -/
theorem original_le_of_sourceDivisorial_le
    {L : RationalPicardSpace X} {φ ψ : BerkovichPoint p → EReal}
    (hφ : IsModuleTopologyPSH.{u} p L φ) (hψ : UpperSemicontinuous ψ)
    (hle : ∀ v ∈ sourceDivisorialSet p, φ v ≤ ψ v) : φ ≤ ψ := by
  let θ := NativePicard.numericalClass p L
  obtain ⟨r,d,q,hp,hq,a,ha⟩ := Pair3ClassStability.exists_simultaneous_presentation p
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
    apply (Variety.isPSH_iff_presentation d q p hp (a 0)
      (fun y => φ ((pointEquiv p).symm y))).mp
    rw [← ha 0]
    exact hφ.isNativePSH p
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

end SGPT.NAPotential.BJ.Pair3Div
