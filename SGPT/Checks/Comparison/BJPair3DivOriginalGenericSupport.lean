import SGPT.Foundations.Envelope.Berkovich.SchemeGenericCenterValuations
import Mathlib.AlgebraicGeometry.AffineScheme

-- Lane BJ-PAIR (R5/thm:pshdetbydiv bridge): ported from `SGPT.Checks.Literature/SGPT.Checks.Literature/BJDivisorial/OriginalGenericSupport.lean`
-- (that library pins another SGPT.Foundations.Envelope revision and cannot be imported here); only the
-- imports, the `Alterations` namespace (now `SGPT.Support.Alterations`) and this file's namespace
-- (`Divisorial` -> `Pair3Div`, `ExternalClassStability` -> `Pair3ClassStability`) are changed.

/-!
# Actual generic support from nonzero original affine-chart values
Every open containing the genuine generic point contains a basic open of
the same actual affine chart. Its nonzero defining function has nonzero
evaluation, forcing the original point into that open. Scheme T0 then
gives genuine equality with the original generic point.
-/
noncomputable section
open AlgebraicGeometry TopologicalSpace

namespace SGPT.NAPotential.BJ.Pair3Div
open SGPT.Foundations.Envelope.Berkovich

universe u
variable {X : Scheme.{u}} [IsIntegral X]

/-- Nonvanishing on every nonzero coefficient of one actual affine chart
derives genuine original generic support. -/
theorem original_generic_support_of_eval_ne_zero (y : SchemeValuedPoint X)
    (U : X.Opens) (hU : IsAffineOpen U) (hy : y.point ∈ U)
    (hne : ∀ f : Γ(X, U), f ≠ 0 → SchemeValuedPoint.eval y U hy f ≠ 0) :
    y.point = genericPoint X := by
  have hηU : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
      (by simpa using (show Nonempty U from ⟨⟨y.point, hy⟩⟩))
  have hspecial : y.point ⤳ genericPoint X := by
    apply specializes_iff_forall_open.mpr
    intro O hO hηO
    let W : X.Opens := ⟨O, hO⟩
    obtain ⟨f, hfW, hηf⟩ := hU.exists_basicOpen_le (⟨genericPoint X, hηO⟩ : W) hηU
    have hf0 : f ≠ 0 := by
      intro hf
      subst f
      simp at hηf
    have hyf : y.point ∈ X.basicOpen f := by
      by_contra hh
      exact hne f hf0 ((SchemeValuedPoint.eval_eq_zero_iff y U hy f).mpr hh)
    exact hfW hyf
  exact (hspecial.antisymm (genericPoint_specializes y.point)).eq

end SGPT.NAPotential.BJ.Pair3Div
