import SGPT.Okounkov.SchemeOriginalFlagGeometry
import SGPT.Okounkov.SchemeNativeFunctionField
import SGPT.Okounkov.NativeFlagGermFiniteLeaves

/-!
# Genuine actual global function-field valuation from the original full flag

The actual original geometry/endpoint and actual K(X) embedding manufacture
the full lexicographic additive valuation by genuine native comap. Constants
retain the EXACT original structure-induced action. Native scalar cancellation
transfers to actual global functions. No field equality, global tuple range,
rank or Fubini–Study-to-TN Kähler transport is asserted.
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

local instance originalFieldValuationTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f

local instance originalFieldValuationCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n

local instance originalFieldValuationManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

local instance originalFieldValuationNativeComplexAlgebra (p : SchemeComplexPoint f) :
    Algebra ℂ (FractionRing (NativeHolGerm n (SchemeComplexPoint f) p)) :=
  schemeNativeFractionComplexAlgebra f n p

/-- Actual projectivity and original geometry internally manufacture the
genuine full lexicographic valuation on the ACTUAL original global field. -/
def schemeOriginalFlagFunctionFieldValuation (e : ClosedProjectiveEmbedding f) :
    letI := e.isSeparated
    letI := e.quasiCompact
    (ω : KahlerBackground n (SchemeComplexPoint f)) →
    (Y : Fin (n + 1) → Set (SchemeComplexPoint f)) →
    IsSmoothFlag Y → AddValuation X.functionField (WithTop (Lex (Fin n → ℤ))) := by
  letI := e.isSeparated
  letI := e.quasiCompact
  intro ω Y hY
  let F := schemeProjectiveOriginalFlagGeometry f n e ω Y hY
  let x := schemeProjectiveOriginalFlagPoint f n e ω Y hY
  exact (originalFlagGermFractionValuation F x).comap
    (schemeNativeFunctionFieldGerm f n x.val)

/-- WHOLE original value readback through the actual original field embedding. -/
theorem schemeOriginalFlagFunctionFieldValuation_apply (e : ClosedProjectiveEmbedding f)
    (ω : KahlerBackground n (SchemeComplexPoint f))
    (Y : Fin (n + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)
    (q : X.functionField) :
    schemeOriginalFlagFunctionFieldValuation f n e ω Y hY q =
      originalFlagGermFractionValuation (schemeProjectiveOriginalFlagGeometry f n e ω Y hY)
        (schemeProjectiveOriginalFlagPoint f n e ω Y hY)
        (schemeNativeFunctionFieldGerm f n (schemeProjectiveOriginalFlagPoint f n e ω Y hY).val q) :=
  rfl

omit [IsIntegral X] in
/-- Both actual fraction actions are the SAME original constant-germ map
followed by the SAME literal fraction inclusion, without a compatibility input. -/
theorem schemeOriginalFlagFractionComplexAlgebra_eq (e : ClosedProjectiveEmbedding f)
    (ω : KahlerBackground n (SchemeComplexPoint f))
    (Y : Fin (n + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y) :
    originalFlagGermFractionComplexAlgebra (schemeProjectiveOriginalFlagGeometry f n e ω Y hY)
        (schemeProjectiveOriginalFlagPoint f n e ω Y hY) =
      schemeNativeFractionComplexAlgebra f n (schemeProjectiveOriginalFlagPoint f n e ω Y hY).val :=
  rfl

/-- Genuine native top criterion and ACTUAL field injection give exactly zero at top. -/
theorem schemeOriginalFlagFunctionFieldValuation_eq_top_iff (e : ClosedProjectiveEmbedding f)
    (ω : KahlerBackground n (SchemeComplexPoint f))
    (Y : Fin (n + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)
    (q : X.functionField) :
    schemeOriginalFlagFunctionFieldValuation f n e ω Y hY q = ⊤ ↔ q = 0 := by
  rw [schemeOriginalFlagFunctionFieldValuation_apply,
    originalFlagGermFractionValuation_eq_top_iff]
  exact map_eq_zero_iff _ (schemeNativeFunctionFieldGerm_injective f n
    (schemeProjectiveOriginalFlagPoint f n e ω Y hY).val)

/-- Every original algebraic stalk element has its WHOLE original germ valuation. -/
theorem schemeOriginalFlagFunctionFieldValuation_stalk (e : ClosedProjectiveEmbedding f)
    (ω : KahlerBackground n (SchemeComplexPoint f))
    (Y : Fin (n + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)
    (a : X.presheaf.stalk
      (schemeComplexPointImage f (schemeProjectiveOriginalFlagPoint f n e ω Y hY).val)) :
    schemeOriginalFlagFunctionFieldValuation f n e ω Y hY (algebraMap _ X.functionField a) =
      originalFlagGermValuation (schemeProjectiveOriginalFlagGeometry f n e ω Y hY)
        (schemeProjectiveOriginalFlagPoint f n e ω Y hY)
        (schemeNativeStalkGerm f n (schemeProjectiveOriginalFlagPoint f n e ω Y hY).val a) := by
  rw [schemeOriginalFlagFunctionFieldValuation_apply,
    schemeNativeFunctionFieldGerm_stalk]
  exact originalFlagGermFractionValuation_algebraMap
    (schemeProjectiveOriginalFlagGeometry f n e ω Y hY)
    (schemeProjectiveOriginalFlagPoint f n e ω Y hY)
    (schemeNativeStalkGerm f n (schemeProjectiveOriginalFlagPoint f n e ω Y hY).val a)

/-- Nonzero complex scalars have zero value for the EXACT original source action. -/
theorem schemeOriginalFlagFunctionFieldValuation_scalar (e : ClosedProjectiveEmbedding f)
    (ω : KahlerBackground n (SchemeComplexPoint f))
    (Y : Fin (n + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)
    (c : ℂ) (hc : c ≠ 0) :
    letI := schemeFunctionFieldAlgebra f
    schemeOriginalFlagFunctionFieldValuation f n e ω Y hY (algebraMap ℂ X.functionField c) = 0 := by
  let := schemeFunctionFieldAlgebra f
  rw [schemeOriginalFlagFunctionFieldValuation_apply, schemeNativeFunctionFieldGerm_const]
  exact originalFlagGermFractionValuation_scalar
    (schemeProjectiveOriginalFlagGeometry f n e ω Y hY)
    (schemeProjectiveOriginalFlagPoint f n e ω Y hY) c hc

/-- Genuine native cancellation remains an ACTUAL global scalar combination,
including a possible zero/top cancellation result. No leaf certificate is supplied. -/
theorem exists_schemeOriginalFlagFunctionField_scalar_cancel (e : ClosedProjectiveEmbedding f)
    (ω : KahlerBackground n (SchemeComplexPoint f))
    (Y : Fin (n + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)
    (q r : X.functionField) (hq : q ≠ 0) (hr : r ≠ 0)
    (hvalue : schemeOriginalFlagFunctionFieldValuation f n e ω Y hY q =
      schemeOriginalFlagFunctionFieldValuation f n e ω Y hY r) :
    letI := schemeFunctionFieldAlgebra f
    ∃ c : ℂ, c ≠ 0 ∧ schemeOriginalFlagFunctionFieldValuation f n e ω Y hY q <
      schemeOriginalFlagFunctionFieldValuation f n e ω Y hY (q + algebraMap ℂ X.functionField c * r) := by
  let := schemeFunctionFieldAlgebra f
  let F := schemeProjectiveOriginalFlagGeometry f n e ω Y hY
  let x := schemeProjectiveOriginalFlagPoint f n e ω Y hY
  let φ := schemeNativeFunctionFieldAlgHom f n x.val
  have hφ : Function.Injective φ := schemeNativeFunctionFieldGerm_injective f n x.val
  have hq' : φ q ≠ 0 := by
    intro hz
    exact hq (hφ (hz.trans (map_zero φ).symm))
  have hr' : φ r ≠ 0 := by
    intro hz
    exact hr (hφ (hz.trans (map_zero φ).symm))
  have hv : originalFlagGermFractionValuation F x (φ q) =
      originalFlagGermFractionValuation F x (φ r) := hvalue
  obtain ⟨c, hc, hcancel⟩ := exists_originalFlagGermFraction_scalar_cancel F x
    (φ q) (φ r) hq' hr' hv
  refine ⟨c, hc, ?_⟩
  change originalFlagGermFractionValuation F x (φ q) <
    originalFlagGermFractionValuation F x (φ (q + algebraMap ℂ X.functionField c * r))
  rw [map_add, map_mul, φ.commutes]
  exact hcancel

end SGPT.Okounkov
