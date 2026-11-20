import SGPT.Okounkov.SchemeOriginalFunctionFieldValuation
import SGPT.Okounkov.SchemePointPowerGerm

/-!
# Whole original flag vectors of actual tensor-power sections

ONE internally chosen original point frame and its genuine powers give
actual holomorphic coefficient germs. Their whole original recursive
vectors read back the ACTUAL global valuation and preserve actual products
and the degree-zero unit. No global tuple realization or rank is asserted.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Okounkov

open CategoryTheory AlgebraicGeometry Algebra SGPT.Foundations.Schemes Set
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open scoped Topology

variable {X : Scheme} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]

local instance originalSectionValuationTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance originalSectionValuationCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance originalSectionValuationManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n
local instance originalSectionValuationComplexAlgebra (p : SchemeComplexPoint f) :
    Algebra ℂ (FractionRing (NativeHolGerm n (SchemeComplexPoint f) p)) :=
  schemeNativeFractionComplexAlgebra f n p

variable (e : ClosedProjectiveEmbedding f) (ω : KahlerBackground n (SchemeComplexPoint f))
  (Y : Fin (n + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)

private theorem nativeVector_congr {d : ℕ} (F : OriginalFlagGeometry d)
    (x : OriginalFlagGermPoint F) (u v : NativeHolGerm d F.carrier x.val)
    (hu : u ≠ 0) (hv : v ≠ 0) (h : u = v) :
    originalFlagGermVector F x u hu = originalFlagGermVector F x v hv := by
  subst v
  rfl

/-- Actual global point-frame coefficient value, using ONE frame's true powers. -/
def schemeOriginalFlagSectionValue {L : X.Modules} (a : LineBundleAtlas L)
    (m : ℕ) (s : bundlePowerGlobalSections L m) : WithTop (Lex (Fin n → ℤ)) :=
  schemeOriginalFlagFunctionFieldValuation f n e ω Y hY
    (schemePointGlobalSectionsFunctionField f (schemeProjectiveOriginalFlagPoint f n e ω Y hY).val
      (a.tensorPower m) s)

/-- The actual nonzero original holomorphic coefficient manufactures EVERY coordinate. -/
def schemeOriginalFlagSectionVector {L : X.Modules} (a : LineBundleAtlas L)
    (m : ℕ) (s : bundlePowerGlobalSections L m) (hs : s ≠ 0) : Fin n → ℕ :=
  originalFlagGermVector (schemeProjectiveOriginalFlagGeometry f n e ω Y hY)
    (schemeProjectiveOriginalFlagPoint f n e ω Y hY)
    (schemePointPowerSectionNativeGerm f n (schemeProjectiveOriginalFlagPoint f n e ω Y hY).val a m s)
    (schemePointPowerSectionNativeGerm_ne_zero f n
      (schemeProjectiveOriginalFlagPoint f n e ω Y hY).val a m s hs)

/-- WHOLE global value equals the SAME original holomorphic coefficient value. -/
theorem schemeOriginalFlagSectionValue_native {L : X.Modules} (a : LineBundleAtlas L)
    (m : ℕ) (s : bundlePowerGlobalSections L m) :
    schemeOriginalFlagSectionValue f n e ω Y hY a m s =
      originalFlagGermValuation (schemeProjectiveOriginalFlagGeometry f n e ω Y hY)
        (schemeProjectiveOriginalFlagPoint f n e ω Y hY)
        (schemePointPowerSectionNativeGerm f n
          (schemeProjectiveOriginalFlagPoint f n e ω Y hY).val a m s) := by
  let p := (schemeProjectiveOriginalFlagPoint f n e ω Y hY).val
  let := schemeGlobalSectionModule f (bundleTensorPower L m)
  let := schemeFunctionFieldAlgebra f
  change originalFlagGermFractionValuation (schemeProjectiveOriginalFlagGeometry f n e ω Y hY)
    (schemeProjectiveOriginalFlagPoint f n e ω Y hY)
    (schemePointPowerGlobalSectionsGerm f n p a m s) = _
  rw [schemePointPowerGlobalSectionsGerm_native]
  exact originalFlagGermFractionValuation_algebraMap
    (schemeProjectiveOriginalFlagGeometry f n e ω Y hY)
    (schemeProjectiveOriginalFlagPoint f n e ω Y hY)
    (schemePointPowerSectionNativeGerm f n p a m s)

/-- Every nonzero actual section has its full natural vector, cast as a finite lex value. -/
theorem schemeOriginalFlagSectionValue_of_ne_zero {L : X.Modules} (a : LineBundleAtlas L)
    (m : ℕ) (s : bundlePowerGlobalSections L m) (hs : s ≠ 0) :
    schemeOriginalFlagSectionValue f n e ω Y hY a m s =
      ((toLex (fun i => (schemeOriginalFlagSectionVector f n e ω Y hY a m s hs i : ℤ)) :
        Lex (Fin n → ℤ)) : WithTop (Lex (Fin n → ℤ))) := by
  rw [schemeOriginalFlagSectionValue_native]
  exact originalFlagGermValuation_apply_of_ne_zero
    (schemeProjectiveOriginalFlagGeometry f n e ω Y hY)
    (schemeProjectiveOriginalFlagPoint f n e ω Y hY)
    (schemePointPowerSectionNativeGerm f n (schemeProjectiveOriginalFlagPoint f n e ω Y hY).val a m s)
    (schemePointPowerSectionNativeGerm_ne_zero f n
      (schemeProjectiveOriginalFlagPoint f n e ω Y hY).val a m s hs)

/-- Top occurs precisely for the zero ACTUAL section. -/
theorem schemeOriginalFlagSectionValue_eq_top_iff {L : X.Modules} (a : LineBundleAtlas L)
    (m : ℕ) (s : bundlePowerGlobalSections L m) :
    schemeOriginalFlagSectionValue f n e ω Y hY a m s = ⊤ ↔ s = 0 := by
  rw [schemeOriginalFlagSectionValue_native, originalFlagGermValuation_eq_top_iff]
  exact schemePointPowerSectionNativeGerm_eq_zero_iff f n
    (schemeProjectiveOriginalFlagPoint f n e ω Y hY).val a m s

/-- Actual homogeneous products add the WHOLE values, including zero sections. -/
theorem schemeOriginalFlagSectionValue_mul {L : X.Modules} (a : LineBundleAtlas L)
    (m k : ℕ) (s : bundlePowerGlobalSections L m) (t : bundlePowerGlobalSections L k) :
    schemeOriginalFlagSectionValue f n e ω Y hY a (m + k) (atlasPowerGlobalMul a m k s t) =
      schemeOriginalFlagSectionValue f n e ω Y hY a m s +
        schemeOriginalFlagSectionValue f n e ω Y hY a k t := by
  rw [schemeOriginalFlagSectionValue_native, schemePointPowerSectionNativeGerm_mul]
  rw [(originalFlagGermValuation (schemeProjectiveOriginalFlagGeometry f n e ω Y hY)
    (schemeProjectiveOriginalFlagPoint f n e ω Y hY)).map_mul]
  rw [schemeOriginalFlagSectionValue_native, schemeOriginalFlagSectionValue_native]

/-- Actual SAME-frame products add every natural coordinate, with genuine nonzero products. -/
theorem schemeOriginalFlagSectionVector_mul {L : X.Modules} (a : LineBundleAtlas L)
    (m k : ℕ) (s : bundlePowerGlobalSections L m) (t : bundlePowerGlobalSections L k)
    (hs : s ≠ 0) (ht : t ≠ 0) :
    schemeOriginalFlagSectionVector f n e ω Y hY a (m + k) (atlasPowerGlobalMul a m k s t)
        (schemePointPowerGlobalMul_ne_zero f n (schemeProjectiveOriginalFlagPoint f n e ω Y hY).val
          a m k s t hs ht) =
      schemeOriginalFlagSectionVector f n e ω Y hY a m s hs +
        schemeOriginalFlagSectionVector f n e ω Y hY a k t ht := by
  let F := schemeProjectiveOriginalFlagGeometry f n e ω Y hY
  let x := schemeProjectiveOriginalFlagPoint f n e ω Y hY
  let u := schemePointPowerSectionNativeGerm f n x.val a m s
  let v := schemePointPowerSectionNativeGerm f n x.val a k t
  have hu : u ≠ 0 := schemePointPowerSectionNativeGerm_ne_zero f n x.val a m s hs
  have hv : v ≠ 0 := schemePointPowerSectionNativeGerm_ne_zero f n x.val a k t ht
  exact (nativeVector_congr F x _ (u * v) _ (mul_ne_zero hu hv)
    (schemePointPowerSectionNativeGerm_mul f n x.val a m k s t)).trans
    (originalFlagGermVector_mul F x u v hu hv)

include f n e ω Y hY in
/-- Actual degree-zero unit nonvanishing follows from its literal native germ. -/
theorem schemeOriginalFlagSectionOne_ne_zero {L : X.Modules} (a : LineBundleAtlas L) :
    bundlePowerGlobalOne L ≠ 0 := by
  intro hz
  have h := (schemePointPowerSectionNativeGerm_eq_zero_iff f n
    (schemeProjectiveOriginalFlagPoint f n e ω Y hY).val a 0 (bundlePowerGlobalOne L)).mpr hz
  rw [schemePointPowerSectionNativeGerm_one] at h
  exact one_ne_zero h

/-- The actual degree-zero unit has whole value zero. -/
theorem schemeOriginalFlagSectionValue_one {L : X.Modules} (a : LineBundleAtlas L) :
    schemeOriginalFlagSectionValue f n e ω Y hY a 0 (bundlePowerGlobalOne L) = 0 := by
  rw [schemeOriginalFlagSectionValue_native, schemePointPowerSectionNativeGerm_one]
  exact (originalFlagGermValuation (schemeProjectiveOriginalFlagGeometry f n e ω Y hY)
    (schemeProjectiveOriginalFlagPoint f n e ω Y hY)).map_one

/-- The actual degree-zero unit has ZERO in every natural coordinate. -/
theorem schemeOriginalFlagSectionVector_one {L : X.Modules} (a : LineBundleAtlas L) :
    schemeOriginalFlagSectionVector f n e ω Y hY a 0 (bundlePowerGlobalOne L)
      (schemeOriginalFlagSectionOne_ne_zero f n e ω Y hY a) = 0 := by
  let F := schemeProjectiveOriginalFlagGeometry f n e ω Y hY
  let x := schemeProjectiveOriginalFlagPoint f n e ω Y hY
  exact (nativeVector_congr F x _ 1 _ one_ne_zero
    (schemePointPowerSectionNativeGerm_one f n x.val a)).trans
    (originalFlagGermVector_one F x)

end SGPT.Okounkov
