import SGPT.Okounkov.SchemePointSectionGerm
import SGPT.Foundations.Schemes.LineBundleSectionRing

/-!
# One original point frame and its actual tensor powers

The existing tensor-power atlas keeps the identical cover and uses actual
powers of its original frames. The previous actual point-section producer
therefore gives a coherent degreewise family in the SAME original holomorphic
germ ring. Native sheaf-glued products and their genuine coefficient laws
manufacture whole germ/fraction multiplication and nonzero products.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Okounkov

open CategoryTheory AlgebraicGeometry Algebra SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open scoped Topology

section Frames

variable {X : Scheme} (f : X ⟶ Spec (.of ℂ)) (p : SchemeComplexPoint f)

/-- Actual power atlases retain the identical original point-cover choice. -/
theorem schemePointFrameIndex_tensorPower {L : X.Modules} (a : LineBundleAtlas L) (m : ℕ) :
    schemePointFrameIndex f p (a.tensorPower m) = schemePointFrameIndex f p a := rfl

/-- All degrees use the SAME actual original open containing the point. -/
theorem schemePointFrameOpen_tensorPower {L : X.Modules} (a : LineBundleAtlas L) (m : ℕ) :
    schemePointFrameOpen f p (a.tensorPower m) = schemePointFrameOpen f p a := rfl

/-- The chosen power frame is the actual tensor power of ONE original frame. -/
theorem schemePointFrame_tensorPower {L : X.Modules} (a : LineBundleAtlas L) (m : ℕ) :
    schemePointFrame f p (a.tensorPower m) = (schemePointFrame f p a).tensorPower m := rfl

end Frames

variable {X : Scheme} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f] [IsIntegral X]
  (p : SchemeComplexPoint f)

local instance pointPowerSchemeTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f

local instance pointPowerSchemeCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n

local instance pointPowerSchemeManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

local instance pointPowerNativeComplexAlgebra :
    Algebra ℂ (FractionRing (NativeHolGerm n (SchemeComplexPoint f) p)) :=
  schemeNativeFractionComplexAlgebra f n p

/-- Actual original holomorphic coefficients use ONE point frame's true powers. -/
def schemePointPowerSectionNativeGerm {L : X.Modules} (a : LineBundleAtlas L) (m : ℕ)
    (s : bundlePowerGlobalSections L m) : NativeHolGerm n (SchemeComplexPoint f) p :=
  schemePointSectionNativeGerm f n p (a.tensorPower m) s

/-- The exact original structural action gives the actual degreewise linear map. -/
def schemePointPowerGlobalSectionsGerm {L : X.Modules} (a : LineBundleAtlas L) (m : ℕ) :
    letI := schemeGlobalSectionModule f (bundleTensorPower L m)
    bundlePowerGlobalSections L m →ₗ[ℂ] FractionRing (NativeHolGerm n (SchemeComplexPoint f) p) :=
  schemePointGlobalSectionsGerm f n p (a.tensorPower m)

/-- Genuine integral geometry supplies faithfulness at EVERY actual degree. -/
theorem schemePointPowerGlobalSectionsGerm_injective {L : X.Modules}
    (a : LineBundleAtlas L) (m : ℕ) :
    Function.Injective (schemePointPowerGlobalSectionsGerm f n p a m) :=
  schemePointGlobalSectionsGerm_injective f n p (a.tensorPower m)

/-- The full fraction image is inclusion of the SAME original holomorphic germ. -/
theorem schemePointPowerGlobalSectionsGerm_native {L : X.Modules}
    (a : LineBundleAtlas L) (m : ℕ) (s : bundlePowerGlobalSections L m) :
    schemePointPowerGlobalSectionsGerm f n p a m s =
      algebraMap _ (FractionRing (NativeHolGerm n (SchemeComplexPoint f) p))
        (schemePointPowerSectionNativeGerm f n p a m s) :=
  schemePointGlobalSectionsGerm_native f n p (a.tensorPower m) s

/-- No nonvanishing premise is needed for the actual holomorphic coefficients. -/
theorem schemePointPowerSectionNativeGerm_eq_zero_iff {L : X.Modules}
    (a : LineBundleAtlas L) (m : ℕ) (s : bundlePowerGlobalSections L m) :
    schemePointPowerSectionNativeGerm f n p a m s = 0 ↔ s = 0 :=
  schemePointSectionNativeGerm_eq_zero_iff f n p (a.tensorPower m) s

/-- Nonzero actual sections manufacture nonzero actual holomorphic power coefficients. -/
theorem schemePointPowerSectionNativeGerm_ne_zero {L : X.Modules}
    (a : LineBundleAtlas L) (m : ℕ) (s : bundlePowerGlobalSections L m) (hs : s ≠ 0) :
    schemePointPowerSectionNativeGerm f n p a m s ≠ 0 :=
  schemePointSectionNativeGerm_ne_zero f n p (a.tensorPower m) s hs

omit [IsIntegral X] in
/-- Native sheaf gluing and actual coefficient products give WHOLE germ multiplication. -/
theorem schemePointPowerSectionNativeGerm_mul {L : X.Modules} (a : LineBundleAtlas L)
    (m k : ℕ) (s : bundlePowerGlobalSections L m) (t : bundlePowerGlobalSections L k) :
    schemePointPowerSectionNativeGerm f n p a (m + k) (atlasPowerGlobalMul a m k s t) =
      schemePointPowerSectionNativeGerm f n p a m s *
        schemePointPowerSectionNativeGerm f n p a k t := by
  let U := schemePointFrameOpen f p a
  let x := schemeComplexPointImage f p
  let hx : x ∈ U := schemePointFrame_mem f p a
  let i := schemePointFrameIndex f p a
  change schemeNativeStalkGerm f n p (X.presheaf.germ U x hx
      (atlasPowerGlobalCoefficients a (m + k) i (atlasPowerGlobalMul a m k s t))) =
    schemeNativeStalkGerm f n p (X.presheaf.germ U x hx
      (atlasPowerGlobalCoefficients a m i s)) *
    schemeNativeStalkGerm f n p (X.presheaf.germ U x hx
      (atlasPowerGlobalCoefficients a k i t))
  rw [atlasPowerGlobalMul_coefficients, map_mul, map_mul]

omit [IsIntegral X] in
/-- The degree-zero unit is the literal original constant-one germ. -/
theorem schemePointPowerSectionNativeGerm_one {L : X.Modules} (a : LineBundleAtlas L) :
    schemePointPowerSectionNativeGerm f n p a 0 (bundlePowerGlobalOne L) = 1 := by
  change schemeNativeStalkGerm f n p
    (X.presheaf.germ (schemePointFrameOpen f p a) (schemeComplexPointImage f p)
      (schemePointFrame_mem f p a)
      (atlasPowerGlobalCoefficients a 0 (schemePointFrameIndex f p a) (bundlePowerGlobalOne L))) = 1
  rw [atlasPowerGlobalCoefficients_one, map_one, map_one]

/-- The faithful exact-source fraction family preserves actual homogeneous products. -/
theorem schemePointPowerGlobalSectionsGerm_mul {L : X.Modules} (a : LineBundleAtlas L)
    (m k : ℕ) (s : bundlePowerGlobalSections L m) (t : bundlePowerGlobalSections L k) :
    schemePointPowerGlobalSectionsGerm f n p a (m + k) (atlasPowerGlobalMul a m k s t) =
      schemePointPowerGlobalSectionsGerm f n p a m s *
        schemePointPowerGlobalSectionsGerm f n p a k t := by
  rw [schemePointPowerGlobalSectionsGerm_native, schemePointPowerSectionNativeGerm_mul,
    map_mul, schemePointPowerGlobalSectionsGerm_native,
    schemePointPowerGlobalSectionsGerm_native]

/-- The actual degreewise fraction representation retains the actual unit. -/
theorem schemePointPowerGlobalSectionsGerm_one {L : X.Modules} (a : LineBundleAtlas L) :
    schemePointPowerGlobalSectionsGerm f n p a 0 (bundlePowerGlobalOne L) = 1 := by
  rw [schemePointPowerGlobalSectionsGerm_native, schemePointPowerSectionNativeGerm_one, map_one]

include f n p in
/-- True holomorphic coefficient multiplication proves nonzero homogeneous products. -/
theorem schemePointPowerGlobalMul_ne_zero {L : X.Modules} (a : LineBundleAtlas L)
    (m k : ℕ) (s : bundlePowerGlobalSections L m) (t : bundlePowerGlobalSections L k)
    (hs : s ≠ 0) (ht : t ≠ 0) : atlasPowerGlobalMul a m k s t ≠ 0 := by
  intro hz
  have h := (schemePointPowerSectionNativeGerm_eq_zero_iff f n p a (m + k)
    (atlasPowerGlobalMul a m k s t)).mpr hz
  rw [schemePointPowerSectionNativeGerm_mul] at h
  exact mul_ne_zero (schemePointPowerSectionNativeGerm_ne_zero f n p a m s hs)
    (schemePointPowerSectionNativeGerm_ne_zero f n p a k t ht) h

end SGPT.Okounkov
