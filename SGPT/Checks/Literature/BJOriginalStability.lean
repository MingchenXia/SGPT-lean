import SGPT.Checks.Literature.BJNativeStability
import SGPT.Checks.Literature.BJReverseAdmission

/-! Source: SGPT 76fde3d1, chapter_NApotential.tex:927,952--956.
The explicit unibranch assumption is the updated standing source hypothesis.
The input and output predicates use the actual original rational GF packages,
all original Berkovich points, and the intrinsic numerical module topology.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
namespace SGPT.NAPotential.BJ.ExternalClassStability
open AlgebraicGeometry CategoryTheory Filter Topology
open SGPT.Foundations.PublishedEnvelope
open SGPT.NAPotential.Berkovich SGPT.NAPotential.BJ
open SGPT.NAPotential.BJ.NativePicard SGPT.NAPotential.BJ.Printed
open scoped Classical
variable {X : Scheme.{0}} (p : X ⟶ Spec (.of ℂ)) [IsProjective p] [IsIntegral X]

/-- The literal proposition `prop:BJdecseqstab`, in the corrected standing
unibranch domain, for an arbitrary singular original metric on all points. -/
theorem decreasing_class_stability (hX : Variety.IsUnibranch X)
    (H : X.Modules) (hH : SchemeLineAmpleness.IsAmple p H)
    {L : RationalPicardSpace X} {φ : BerkovichPoint p → EReal}
    (hφ : IsModuleTopologyPSH.{u} p
      (L + rationalPicardClass (atlasOfInvertible hH.isInvertible)) φ)
    (hm : ∀ m : ℕ, 0 < m → IsModuleTopologyPSH.{u} p
      (L + (1 / (m : ℚ)) • rationalPicardClass (atlasOfInvertible hH.isInvertible)) φ) :
    IsModuleTopologyPSH.{0} p L φ := by
  let η := NativeRealNumericalClasses.lineClass p H hH.isInvertible
  have hNative (m : ℕ) (hpos : 0 < m) :
      Variety.IsPSH p (NativePicard.numericalClass p L + (1 / (m : ℝ)) • η)
        (fun y => φ ((pointEquiv p).symm y)) := by
    by_cases hOne : m = 1
    · subst m
      have hi := hφ.isNativePSH p
      simpa only [Nat.cast_one, div_one, one_smul, map_add,
        NativePicard.numericalClass_line] using hi
    · have hi := (hm m hpos).isNativePSH p
      simpa only [map_add, MaxClosure.numericalClass_rat_smul_real,
        NativePicard.numericalClass_line, Rat.cast_div, Rat.cast_one,
        Rat.cast_natCast] using hi
  exact ExternalReverseAdmission.isModuleTopologyPSH_of_nativePSH_with_ample p H hH
    (nativePSH_of_all_positive_perturbations p hX hNative)

end SGPT.NAPotential.BJ.ExternalClassStability
