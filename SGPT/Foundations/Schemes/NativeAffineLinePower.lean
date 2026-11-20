import SGPT.Foundations.Schemes.NativeLineTotalSpace
import Mathlib.AlgebraicGeometry.Morphisms.Finite
/-!
# NativeAffineLinePower

Actual fiber power maps are the native universal affine-space morphisms on the genuine relative affine line. Their projection, coordinate, composition, scaling and arbitrary base-change laws are proved.
-/

open CategoryTheory Limits AlgebraicGeometry Opposite Module
namespace SGPT.Foundations.Schemes
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

/-- Literal fiberwise power on the actual native affine line. -/
def nativeAffineLinePower (U : Scheme.{u}) (q : ℕ) :
    nativeAffineLine U ⟶ nativeAffineLine U :=
  AffineSpace.homOfVector (nativeAffineLineProjection U)
    (fun _ ↦ nativeAffineLineCoordinate U ^ q)

@[reassoc (attr := simp)]
theorem nativeAffineLinePower_projection (U : Scheme.{u}) (q : ℕ) :
    nativeAffineLinePower U q ≫ nativeAffineLineProjection U = nativeAffineLineProjection U :=
  AffineSpace.homOfVector_over _ _

@[simp]
theorem nativeAffineLinePower_coordinate (U : Scheme.{u}) (q : ℕ) :
    (nativeAffineLinePower U q).appTop (nativeAffineLineCoordinate U) =
      nativeAffineLineCoordinate U ^ q := AffineSpace.homOfVector_appTop_coord _ _ _

@[simp]
theorem nativeAffineLinePower_one (U : Scheme.{u}) : nativeAffineLinePower U 1 = 𝟙 _ := by
  apply nativeAffineLine_hom_ext
  · simp
  · simp

/-- Genuine power-map composition, on every actual base scheme. -/
theorem nativeAffineLinePower_comp (U : Scheme.{u}) (q r : ℕ) :
    nativeAffineLinePower U q ≫ nativeAffineLinePower U r = nativeAffineLinePower U (q * r) := by
  apply nativeAffineLine_hom_ext
  · simp
  · simp [pow_mul]

/-- The actual power map transforms a real fiber scaling by the corresponding power. -/
theorem nativeAffineLinePower_scale (U : Scheme.{u}) (q : ℕ) (r : Γ(U, ⊤)) :
    nativeAffineLineScale U r ≫ nativeAffineLinePower U q =
      nativeAffineLinePower U q ≫ nativeAffineLineScale U (r ^ q) := by
  apply nativeAffineLine_hom_ext
  · simp
  · simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      nativeAffineLinePower_coordinate, nativeAffineLineScale_coordinate, map_mul, map_pow]
    have hp := congrArg (fun f ↦ f.appTop r) (nativeAffineLinePower_projection U q)
    change (nativeAffineLinePower U q).appTop ((nativeAffineLineProjection U).appTop r) =
      (nativeAffineLineProjection U).appTop r at hp
    rw [hp, mul_pow]

/-- Literal fiber powers commute with genuine base changes. -/
theorem nativeAffineLinePower_naturality {U V : Scheme.{u}} (f : U ⟶ V) (q : ℕ) :
    nativeAffineLinePower U q ≫ nativeAffineLineMap f =
      nativeAffineLineMap f ≫ nativeAffineLinePower V q := by
  apply nativeAffineLine_hom_ext
  · simp
  · simp

end
end SGPT.Foundations.Schemes
