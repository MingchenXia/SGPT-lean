import SGPT.Okounkov.SchemePointPowerGerm
import SGPT.Foundations.Schemes.NativeProjectiveGlobalSectionsFiniteness
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Actual projective sections and their original holomorphic coefficient images

The genuine native closed-projective H0 producer supplies finiteness for the
EXACT original structural action. Its actual faithful point-power section
map then manufactures finite-dimensional original-native fraction image
spaces with the actual section dimension and coherent products/unit.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Okounkov

open CategoryTheory AlgebraicGeometry Algebra SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open scoped Topology

variable {X : Scheme} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f]

section Image

variable [IsSeparated f] [QuasiCompact f] (p : SchemeComplexPoint f)

local instance projectiveSectionTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f

local instance projectiveSectionCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n

local instance projectiveSectionManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

local instance projectiveSectionNativeComplexAlgebra :
    Algebra ℂ (FractionRing (NativeHolGerm n (SchemeComplexPoint f) p)) :=
  schemeNativeFractionComplexAlgebra f n p

/-- The literal actual native fraction image, for ONE frame and its true powers. -/
def schemePointPowerSectionSpace {L : X.Modules} (a : LineBundleAtlas L) (m : ℕ) :
    Submodule ℂ (FractionRing (NativeHolGerm n (SchemeComplexPoint f) p)) := by
  letI := schemeGlobalSectionModule f (bundleTensorPower L m)
  exact LinearMap.range (schemePointPowerGlobalSectionsGerm f n p a m)

/-- Actual injection identifies the original section module with its actual image. -/
def schemePointPowerSectionEquiv {L : X.Modules} (a : LineBundleAtlas L) (m : ℕ) :
    letI := schemeGlobalSectionModule f (bundleTensorPower L m)
    bundlePowerGlobalSections L m ≃ₗ[ℂ] schemePointPowerSectionSpace f n p a m := by
  letI := schemeGlobalSectionModule f (bundleTensorPower L m)
  exact LinearEquiv.ofInjective (schemePointPowerGlobalSectionsGerm f n p a m)
    (schemePointPowerGlobalSectionsGerm_injective f n p a m)

/-- The actual equivalence retains the WHOLE original fraction coefficient. -/
theorem schemePointPowerSectionEquiv_apply {L : X.Modules}
    (a : LineBundleAtlas L) (m : ℕ) (s : bundlePowerGlobalSections L m) :
    (schemePointPowerSectionEquiv f n p a m s :
      FractionRing (NativeHolGerm n (SchemeComplexPoint f) p)) =
      schemePointPowerGlobalSectionsGerm f n p a m s := rfl

/-- The actual native coefficient image has precisely the actual section dimension. -/
theorem schemePointPowerSectionSpace_finrank {L : X.Modules}
    (a : LineBundleAtlas L) (m : ℕ) :
    letI := schemeGlobalSectionModule f (bundleTensorPower L m)
    Module.finrank ℂ (schemePointPowerSectionSpace f n p a m) =
      Module.finrank ℂ (bundlePowerGlobalSections L m) := by
  let := schemeGlobalSectionModule f (bundleTensorPower L m)
  exact (schemePointPowerSectionEquiv f n p a m).finrank_eq.symm

/-- Every constructed ORIGINAL holomorphic coefficient is in the literal actual image. -/
theorem schemePointPowerSectionSpace_native_mem {L : X.Modules}
    (a : LineBundleAtlas L) (m : ℕ) (s : bundlePowerGlobalSections L m) :
    algebraMap _ (FractionRing (NativeHolGerm n (SchemeComplexPoint f) p))
        (schemePointPowerSectionNativeGerm f n p a m s) ∈
      schemePointPowerSectionSpace f n p a m :=
  ⟨s, schemePointPowerGlobalSectionsGerm_native f n p a m s⟩

/-- Actual SAME-frame multiplication puts products in the actual sum-degree image. -/
theorem schemePointPowerSectionSpace_mul_mem {L : X.Modules}
    (a : LineBundleAtlas L) (m k : ℕ)
    {r q : FractionRing (NativeHolGerm n (SchemeComplexPoint f) p)}
    (hr : r ∈ schemePointPowerSectionSpace f n p a m)
    (hq : q ∈ schemePointPowerSectionSpace f n p a k) :
    r * q ∈ schemePointPowerSectionSpace f n p a (m + k) := by
  obtain ⟨s, hs⟩ := hr
  obtain ⟨t, ht⟩ := hq
  refine ⟨atlasPowerGlobalMul a m k s t, ?_⟩
  change schemePointPowerGlobalSectionsGerm f n p a (m + k)
    (atlasPowerGlobalMul a m k s t) = r * q
  rw [schemePointPowerGlobalSectionsGerm_mul, hs, ht]

/-- The actual degree-zero image contains the actual unit. -/
theorem schemePointPowerSectionSpace_one_mem {L : X.Modules}
    (a : LineBundleAtlas L) :
    (1 : FractionRing (NativeHolGerm n (SchemeComplexPoint f) p)) ∈
      schemePointPowerSectionSpace f n p a 0 :=
  ⟨bundlePowerGlobalOne L, schemePointPowerGlobalSectionsGerm_one f n p a⟩

end Image

/-- Genuine projectivity itself supplies source topology hypotheses and actual
section finiteness, hence finite-dimensional ORIGINAL coefficient images. -/
theorem schemeProjectivePointPowerSectionSpace_finiteDimensional
    (e : ClosedProjectiveEmbedding f) (p : SchemeComplexPoint f)
    {L : X.Modules} (a : LineBundleAtlas L) (m : ℕ) :
    letI := e.isSeparated
    letI := e.quasiCompact
    FiniteDimensional ℂ (schemePointPowerSectionSpace f n p a m) := by
  let := e.isSeparated
  let := e.quasiCompact
  let := schemeGlobalSectionModule f (bundleTensorPower L m)
  let := schemeNativeFractionComplexAlgebra f n p
  let : FiniteDimensional ℂ (bundlePowerGlobalSections L m) :=
    e.powerGlobalSections_finite a m
  exact LinearMap.finiteDimensional_range (schemePointPowerGlobalSectionsGerm f n p a m)

end SGPT.Okounkov
