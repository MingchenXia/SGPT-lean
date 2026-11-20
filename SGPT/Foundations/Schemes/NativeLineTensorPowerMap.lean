import SGPT.Foundations.Schemes.NativeAffineLinePower
import SGPT.Foundations.Schemes.NativeLineTotalSpaceZeroDivisor
/-!
# NativeLineTensorPowerMap

The actual tensor-power frame transitions give genuine powered coordinate multipliers. Actual fiber powers form a natural transformation of the true chart diagrams and descend to their genuine colimit total spaces.
-/

open CategoryTheory Limits AlgebraicGeometry Opposite Module
namespace SGPT.Foundations.Schemes
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
variable {X : Scheme.{u}} {L : X.Modules}

/-- Genuine tensor-power frame transitions are powers of the original actual unit. -/
theorem nativeFrameTransitionUnit_tensorPower {U V W : X.Opens}
    (e : LocalBundleFrame L U) (f : LocalBundleFrame L V)
    (i : W ⟶ U) (j : W ⟶ V) (q : ℕ) :
    nativeFrameTransitionUnit (e.tensorPower q) (f.tensorPower q) i j =
      nativeFrameTransitionUnit e f i j ^ q := by
  simp only [nativeFrameTransitionUnit, localBundleFrameTransition_tensorPower, map_pow]

/-- The true inverse-coordinate multiplier on the tensor-power atlas is the qth power. -/
theorem nativeFramedMultiplier_tensorPower (a : LineBundleAtlas L) (q : ℕ)
    {c d : NativeFramedOpen a} (h : c ⟶ d) :
    nativeFramedMultiplier (a.tensorPower q) h = nativeFramedMultiplier a h ^ q := by
  change (nativeFrameTransitionUnit ((a.frame c.1).tensorPower q) ((a.frame d.1).tensorPower q)
    (homOfLE c.2.2) (homOfLE (h.hom.le.trans d.2.2)))⁻¹ = _
  rw [nativeFrameTransitionUnit_tensorPower, ← inv_pow]
  rfl

/-- Actual fiber powers commute with the true transition-and-inclusion diagram arrows. -/
theorem nativeFramedMap_tensorPower (a : LineBundleAtlas L) (q : ℕ)
    {c d : NativeFramedOpen a} (h : c ⟶ d) :
    nativeFramedMap a h ≫ nativeAffineLinePower d.2.1.toScheme q =
      nativeAffineLinePower c.2.1.toScheme q ≫ nativeFramedMap (a.tensorPower q) h := by
  simp only [nativeFramedMap, nativeFramedMultiplier_tensorPower, Units.val_pow_eq_pow_val]
  rw [Category.assoc, ← nativeAffineLinePower_naturality, ← Category.assoc,
    nativeAffineLinePower_scale, Category.assoc]

/-- The actual componentwise power maps give a genuine natural transformation of line diagrams. -/
def nativeDualLineTensorPowerTransformation (a : LineBundleAtlas L) (q : ℕ) :
    nativeDualLineDiagram a ⟶ nativeDualLineDiagram (a.tensorPower q) where
  app c := nativeAffineLinePower c.2.1.toScheme q
  naturality _ _ h := nativeFramedMap_tensorPower a q h

/-- Literal fiber powers descend to the actual glued total spaces of the dual tensor-power bundles. -/
def nativeDualLineTensorPowerMap (a : LineBundleAtlas L) (q : ℕ) :
    nativeDualLineTotalSpace a ⟶ nativeDualLineTotalSpace (a.tensorPower q) :=
  colimMap (nativeDualLineTensorPowerTransformation a q)

/-- Every actual source chart retains the independently constructed local power map. -/
theorem nativeDualLineTensorPowerMap_on_chart (a : LineBundleAtlas L) (q : ℕ)
    (c : NativeFramedOpen a) :
    nativeFramedChart a c ≫ nativeDualLineTensorPowerMap a q =
      nativeAffineLinePower c.2.1.toScheme q ≫ nativeFramedChart (a.tensorPower q) c := by
  exact ι_colimMap _ _

end
end SGPT.Foundations.Schemes
