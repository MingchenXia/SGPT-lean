import SGPT.Foundations.Schemes.NativePowerSectionRing
import SGPT.Foundations.Schemes.NativeLineTensorPowerFiniteness
import SGPT.Foundations.Schemes.NativeLineTotalSpaceEvaluation
/-!
# NativePowerConeSquare

Genuine coefficient and evaluation comparisons prove the literal commuting square between actual fiber powers, actual full-cone contractions and the actual Spec section-ring power map.
-/

open CategoryTheory Limits AlgebraicGeometry Opposite Module
open scoped DirectSum
namespace SGPT.Foundations.Schemes
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
variable {X : Scheme.{u}} [IsIntegral X] (L : IntrinsicLineBundle X) (q : ℕ)

/-- Actual native framed coefficients agree under the genuine iterated power comparison. -/
theorem IntrinsicLineBundle.nativePowerSection_framedCoefficient (m : ℕ)
    (t : bundlePowerGlobalSections (L.tensorPower q).sheaf m) (c : NativeFramedOpen L.atlas) :
    nativeFramedSectionCoefficient L.atlas (q * m) (L.nativePowerSection q m t) c =
      nativeFramedSectionCoefficient (L.tensorPower q).atlas m t c := by
  unfold nativeFramedSectionCoefficient
  apply congrArg c.2.1.topIso.inv
  change X.sheaf.obj.map (homOfLE c.2.2).op
    (atlasPowerGlobalCoefficients L.atlas (q * m) c.1 (L.nativePowerSection q m t)) =
    X.sheaf.obj.map (homOfLE c.2.2).op
      (atlasPowerGlobalCoefficients (L.tensorPower q).atlas m c.1 t)
  exact (LocalBundleFrame.global_coefficients_restrict (L.atlas.frame c.1) (q * m)
    (homOfLE c.2.2) (L.nativePowerSection q m t)).symm.trans
    ((L.nativePowerSection_coefficients q m c.1 c.2.1 (homOfLE c.2.2) t).trans
      (LocalBundleFrame.global_coefficients_restrict ((L.atlas.frame c.1).tensorPower q) m
        (homOfLE c.2.2) t))

/-- The actual homogeneous evaluation square for real fiber powers and actual regraded sections. -/
theorem IntrinsicLineBundle.nativePowerSection_homogeneousFunction (m : ℕ)
    (t : bundlePowerGlobalSections (L.tensorPower q).sheaf m) (c : NativeFramedOpen L.atlas) :
    (nativeAffineLinePower c.2.1.toScheme q).appTop
      (nativeFramedHomogeneousFunction (L.tensorPower q).atlas m t c) =
      nativeFramedHomogeneousFunction L.atlas (q * m) (L.nativePowerSection q m t) c := by
  unfold nativeFramedHomogeneousFunction
  rw [map_mul, map_pow, nativeAffineLinePower_coordinate,
    L.nativePowerSection_framedCoefficient q m t c, pow_mul]
  have hp := congrArg (fun f ↦ f.appTop (nativeFramedSectionCoefficient (L.tensorPower q).atlas m t c))
    (nativeAffineLinePower_projection c.2.1.toScheme q)
  change (nativeAffineLinePower c.2.1.toScheme q).appTop
    ((nativeAffineLineProjection c.2.1.toScheme).appTop
      (nativeFramedSectionCoefficient (L.tensorPower q).atlas m t c)) =
    (nativeAffineLineProjection c.2.1.toScheme).appTop
      (nativeFramedSectionCoefficient (L.tensorPower q).atlas m t c) at hp
  exact congrArg (fun r ↦ r * (nativeAffineLineCoordinate c.2.1.toScheme ^ q) ^ m) hp

/-- The literal regular coefficient square for the true native chart evaluation maps. -/
theorem IntrinsicLineBundle.nativePowerSection_chartEvaluation (c : NativeFramedOpen L.atlas) :
    (nativeAffineLinePower c.2.1.toScheme q).appTop.hom.comp
      ((L.tensorPower q).nativeChartEvaluation c) =
      (L.nativeChartEvaluation c).comp (L.nativePowerSectionRingHom q) := by
  apply RingHom.ext
  intro x
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of m t =>
      change (nativeAffineLinePower c.2.1.toScheme q).appTop
        ((L.tensorPower q).nativeChartEvaluation c ((L.tensorPower q).ofSection m t)) =
        L.nativeChartEvaluation c (L.nativePowerSectionRingHom q ((L.tensorPower q).ofSection m t))
      rw [(L.tensorPower q).nativeChartEvaluation_ofSection,
        L.nativePowerSectionRingHom_ofSection, L.nativeChartEvaluation_ofSection]
      exact L.nativePowerSection_homogeneousFunction q m t c
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Actual spectra of the genuine section rings retain the power evaluation square on every real chart. -/
theorem IntrinsicLineBundle.nativePowerSection_chartConeMap (c : NativeFramedOpen L.atlas) :
    nativeAffineLinePower c.2.1.toScheme q ≫ (L.tensorPower q).nativeChartConeMap c =
      L.nativeChartConeMap c ≫ Spec.map (CommRingCat.ofHom (L.nativePowerSectionRingHom q)) := by
  unfold IntrinsicLineBundle.nativeChartConeMap
  rw [← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc,
    ← Spec.map_comp, Category.assoc, ← Spec.map_comp]
  congr 1
  apply congrArg Spec.map
  exact CommRingCat.hom_ext (L.nativePowerSection_chartEvaluation q c)

/-- The literal spectrum morphism of the genuine power-section ring homomorphism. -/
def IntrinsicLineBundle.nativePowerConeMap : L.sectionRingCone ⟶ (L.tensorPower q).sectionRingCone :=
  Spec.map (CommRingCat.ofHom (L.nativePowerSectionRingHom q))

/-- The actual total-space fiber power and genuine full section-ring cone maps commute globally. -/
theorem IntrinsicLineBundle.nativePowerConeMap_commutes :
    nativeDualLineTensorPowerMap L.atlas q ≫ (L.tensorPower q).nativeConeMap =
      L.nativeConeMap ≫ L.nativePowerConeMap q := by
  apply colimit.hom_ext
  intro c
  change nativeFramedChart L.atlas c ≫ nativeDualLineTensorPowerMap L.atlas q ≫
      (L.tensorPower q).nativeConeMap =
    nativeFramedChart L.atlas c ≫ L.nativeConeMap ≫ L.nativePowerConeMap q
  have hc := (L.tensorPower q).nativeConeMap_on_open c
  change nativeFramedChart (L.atlas.tensorPower q) c ≫ (L.tensorPower q).nativeConeMap =
    (L.tensorPower q).nativeChartConeMap c at hc
  have hd := L.nativeConeMap_on_open c
  change nativeFramedChart L.atlas c ≫ L.nativeConeMap = L.nativeChartConeMap c at hd
  rw [← Category.assoc, nativeDualLineTensorPowerMap_on_chart, Category.assoc, hc,
    ← Category.assoc, hd]
  exact L.nativePowerSection_chartConeMap q c

end
end SGPT.Foundations.Schemes
