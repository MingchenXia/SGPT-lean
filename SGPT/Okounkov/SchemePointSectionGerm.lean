import SGPT.Okounkov.SchemeNativeFunctionField

/-!
# Actual point-containing frames give original holomorphic section germs

The original atlas cover chooses a genuine frame containing the SAME actual
scheme point. Its literal coefficient-stalk germ maps to an actual original
holomorphic germ. Existing exact-base generic evaluation and the genuine
native field embedding give a faithful complex-linear fraction representation,
with whole readback as inclusion of that actual holomorphic coefficient germ.
No frame, pole, nonvanishing, dimension or valuation certificate is supplied.
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

/-- The actual original cover internally chooses a frame at the SAME point. -/
def schemePointFrameIndex {L : X.Modules} (a : LineBundleAtlas L) : a.I :=
  (a.covers (schemeComplexPointImage f p)).choose

/-- The actual chosen frame open, without a new open or frame input. -/
def schemePointFrameOpen {L : X.Modules} (a : LineBundleAtlas L) : X.Opens :=
  a.opens (schemePointFrameIndex f p a)

/-- The chosen original open genuinely contains the SAME underlying point. -/
theorem schemePointFrame_mem {L : X.Modules} (a : LineBundleAtlas L) :
    schemeComplexPointImage f p ∈ schemePointFrameOpen f p a :=
  (a.covers (schemeComplexPointImage f p)).choose_spec

/-- Actual point membership produces the nonempty frame open. -/
theorem schemePointFrameOpen_nonempty {L : X.Modules} (a : LineBundleAtlas L) :
    Nonempty (schemePointFrameOpen f p a) :=
  ⟨⟨schemeComplexPointImage f p, schemePointFrame_mem f p a⟩⟩

/-- The actual sheaf isomorphism at that actual covering index. -/
def schemePointFrame {L : X.Modules} (a : LineBundleAtlas L) :
    LocalBundleFrame L (schemePointFrameOpen f p a) :=
  a.frame (schemePointFrameIndex f p a)

/-- The literal regular coefficient after actual global-section restriction. -/
def schemePointSectionCoefficient {L : X.Modules} (a : LineBundleAtlas L)
    (s : bundleSections L ⊤) : Γ(X, schemePointFrameOpen f p a) :=
  localFrameCoefficients (schemePointFrame f p a) (L.val.map (homOfLE le_top).op s)

/-- The SAME actual coefficient has its actual original scheme-stalk germ. -/
def schemePointSectionStalk {L : X.Modules} (a : LineBundleAtlas L)
    (s : bundleSections L ⊤) : X.presheaf.stalk (schemeComplexPointImage f p) :=
  X.presheaf.germ (schemePointFrameOpen f p a) (schemeComplexPointImage f p)
    (schemePointFrame_mem f p a) (schemePointSectionCoefficient f p a s)

variable [IsIntegral X]

/-- Reuse the original exact-base linear coefficient map in the manufactured
point-containing frame, with the actual original structural scalar actions. -/
def schemePointGlobalSectionsFunctionField {L : X.Modules} (a : LineBundleAtlas L) :
    letI := schemeGlobalSectionModule f L
    letI := schemeFunctionFieldAlgebra f
    bundleSections L ⊤ →ₗ[ℂ] X.functionField := by
  letI := schemeGlobalSectionModule f L
  letI := schemeFunctionFieldAlgebra f
  letI : Nonempty (schemePointFrameOpen f p a) := schemePointFrameOpen_nonempty f p a
  exact globalSectionToFunctionFieldOverBase f (schemePointFrame f p a)

/-- Actual integral geometry and the actual atlas prove faithfulness. -/
theorem schemePointGlobalSectionsFunctionField_injective {L : X.Modules}
    (a : LineBundleAtlas L) : Function.Injective (schemePointGlobalSectionsFunctionField f p a) := by
  let := schemeGlobalSectionModule f L
  let := schemeFunctionFieldAlgebra f
  let : Nonempty (schemePointFrameOpen f p a) := schemePointFrameOpen_nonempty f p a
  exact globalSectionToFunctionFieldOverBase_injective f a (schemePointFrame f p a)

end Frames

variable {X : Scheme} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f] [IsIntegral X]
  (p : SchemeComplexPoint f)

local instance pointSectionSchemeTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f

local instance pointSectionSchemeCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n

local instance pointSectionSchemeManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

local instance pointSectionNativeComplexAlgebra :
    Algebra ℂ (FractionRing (NativeHolGerm n (SchemeComplexPoint f) p)) :=
  schemeNativeFractionComplexAlgebra f n p

/-- This is an actual ORIGINAL holomorphic germ, not merely a meromorphic coefficient. -/
def schemePointSectionNativeGerm {L : X.Modules} (a : LineBundleAtlas L)
    (s : bundleSections L ⊤) : NativeHolGerm n (SchemeComplexPoint f) p :=
  schemeNativeStalkGerm f n p (schemePointSectionStalk f p a s)

/-- The SAME point-frame coefficients give a faithful actual complex-linear
fraction representation for the EXACT original global-section action. -/
def schemePointGlobalSectionsGerm {L : X.Modules} (a : LineBundleAtlas L) :
    letI := schemeGlobalSectionModule f L
    bundleSections L ⊤ →ₗ[ℂ] FractionRing (NativeHolGerm n (SchemeComplexPoint f) p) := by
  letI := schemeGlobalSectionModule f L
  letI := schemeFunctionFieldAlgebra f
  exact (schemeNativeFunctionFieldAlgHom f n p).toLinearMap.comp
    (schemePointGlobalSectionsFunctionField f p a)

/-- Faithfulness is manufactured by the two existing actual injections. -/
theorem schemePointGlobalSectionsGerm_injective {L : X.Modules} (a : LineBundleAtlas L) :
    Function.Injective (schemePointGlobalSectionsGerm f n p a) := by
  let := schemeGlobalSectionModule f L
  let := schemeFunctionFieldAlgebra f
  exact (schemeNativeFunctionFieldGerm_injective f n p).comp
    (schemePointGlobalSectionsFunctionField_injective f p a)

/-- WHOLE readback: every section's actual fraction is the inclusion of its
actual ORIGINAL point-frame holomorphic coefficient germ. -/
theorem schemePointGlobalSectionsGerm_native {L : X.Modules} (a : LineBundleAtlas L)
    (s : bundleSections L ⊤) :
    schemePointGlobalSectionsGerm f n p a s =
      algebraMap _ (FractionRing (NativeHolGerm n (SchemeComplexPoint f) p))
        (schemePointSectionNativeGerm f n p a s) := by
  let := schemeGlobalSectionModule f L
  let := schemeFunctionFieldAlgebra f
  let : Nonempty (schemePointFrameOpen f p a) := schemePointFrameOpen_nonempty f p a
  change schemeNativeFunctionFieldAlgHom f n p
    (schemePointGlobalSectionsFunctionField f p a s) = _
  rw [schemeNativeFunctionFieldAlgHom_apply]
  change schemeNativeFunctionFieldGerm f n p
    (X.germToFunctionField (schemePointFrameOpen f p a)
      (schemePointSectionCoefficient f p a s)) = _
  rw [← Scheme.algebraMap_germ_eq_germToFunctionField X (schemePointFrame_mem f p a),
    schemeNativeFunctionFieldGerm_stalk]
  rfl

/-- Actual nonzero global sections have actual nonzero ORIGINAL holomorphic
coefficient germs at the manufactured point-containing frame. -/
theorem schemePointSectionNativeGerm_eq_zero_iff {L : X.Modules} (a : LineBundleAtlas L)
    (s : bundleSections L ⊤) : schemePointSectionNativeGerm f n p a s = 0 ↔ s = 0 := by
  let := schemeGlobalSectionModule f L
  constructor
  · intro hs
    apply schemePointGlobalSectionsGerm_injective f n p a
    rw [schemePointGlobalSectionsGerm_native, hs, map_zero, map_zero]
  · intro hs
    subst s
    apply IsFractionRing.injective (NativeHolGerm n (SchemeComplexPoint f) p)
      (FractionRing (NativeHolGerm n (SchemeComplexPoint f) p))
    rw [← schemePointGlobalSectionsGerm_native, map_zero, map_zero]

/-- No nonvanishing certificate is an input to the actual section-germ producer. -/
theorem schemePointSectionNativeGerm_ne_zero {L : X.Modules} (a : LineBundleAtlas L)
    (s : bundleSections L ⊤) (hs : s ≠ 0) : schemePointSectionNativeGerm f n p a s ≠ 0 :=
  mt (schemePointSectionNativeGerm_eq_zero_iff f n p a s).mp hs

end SGPT.Okounkov
