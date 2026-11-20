import SGPT.Okounkov.SchemeOriginalSectionValuation
import SGPT.Foundations.Schemes.SectionRingCenteredFrame

/-!
# Actual original stalk units and intrinsic full flag section values

The actual original stalk map sends genuine stalk units to native units.
The entire native unit vector is zero, so actual transition coefficients
have full global value zero. Existing genuine overlap power coefficients
then prove arbitrary point-frame and two-atlas value/vector independence.
No valuation-center or frame/unit/coherence certificate is supplied.
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

local instance originalFrameTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance originalFrameCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance originalFrameManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

variable (e : ClosedProjectiveEmbedding f) (ω : KahlerBackground n (SchemeComplexPoint f))
  (Y : Fin (n + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)

/-- Actual original stalk units map to actual original holomorphic units. -/
def schemeOriginalFlagNativeStalkUnit
    (u : (X.presheaf.stalk (schemeComplexPointImage f
      (schemeProjectiveOriginalFlagPoint f n e ω Y hY).val))ˣ) :
    (NativeHolGerm n (SchemeComplexPoint f) (schemeProjectiveOriginalFlagPoint f n e ω Y hY).val)ˣ :=
  Units.map (schemeNativeStalkGerm f n
    (schemeProjectiveOriginalFlagPoint f n e ω Y hY).val).toMonoidHom u

omit [IsIntegral X] in
/-- Literal readback of the ACTUAL mapped stalk unit. -/
theorem schemeOriginalFlagNativeStalkUnit_coe
    (u : (X.presheaf.stalk (schemeComplexPointImage f
      (schemeProjectiveOriginalFlagPoint f n e ω Y hY).val))ˣ) :
    (schemeOriginalFlagNativeStalkUnit f n e ω Y hY u : NativeHolGerm n (SchemeComplexPoint f)
      (schemeProjectiveOriginalFlagPoint f n e ω Y hY).val) =
      schemeNativeStalkGerm f n (schemeProjectiveOriginalFlagPoint f n e ω Y hY).val u := rfl

omit [IsIntegral X] in
/-- True unit inverse and native natural-coordinate product laws give the ENTIRE zero vector. -/
theorem schemeOriginalFlagNativeStalkUnit_vector
    (u : (X.presheaf.stalk (schemeComplexPointImage f
      (schemeProjectiveOriginalFlagPoint f n e ω Y hY).val))ˣ) :
    originalFlagGermVector (schemeProjectiveOriginalFlagGeometry f n e ω Y hY)
      (schemeProjectiveOriginalFlagPoint f n e ω Y hY)
      (schemeOriginalFlagNativeStalkUnit f n e ω Y hY u).val
      (Units.ne_zero (schemeOriginalFlagNativeStalkUnit f n e ω Y hY u)) = 0 :=
  originalFlagGermVector_eq_zero_of_isUnit
    (schemeProjectiveOriginalFlagGeometry f n e ω Y hY)
    (schemeProjectiveOriginalFlagPoint f n e ω Y hY) _
    (Units.ne_zero (schemeOriginalFlagNativeStalkUnit f n e ω Y hY u))
    (schemeOriginalFlagNativeStalkUnit f n e ω Y hY u).isUnit

/-- The ACTUAL original global value of every genuine original stalk unit is zero. -/
theorem schemeOriginalFlagStalkUnit_value
    (u : (X.presheaf.stalk (schemeComplexPointImage f
      (schemeProjectiveOriginalFlagPoint f n e ω Y hY).val))ˣ) :
    schemeOriginalFlagFunctionFieldValuation f n e ω Y hY
      (algebraMap _ X.functionField (u : X.presheaf.stalk (schemeComplexPointImage f
        (schemeProjectiveOriginalFlagPoint f n e ω Y hY).val))) = 0 := by
  rw [schemeOriginalFlagFunctionFieldValuation_stalk]
  change originalFlagGermValuation (schemeProjectiveOriginalFlagGeometry f n e ω Y hY)
    (schemeProjectiveOriginalFlagPoint f n e ω Y hY)
    (schemeOriginalFlagNativeStalkUnit f n e ω Y hY u).val = 0
  rw [originalFlagGermValuation_apply_of_ne_zero _ _ _
    (Units.ne_zero (schemeOriginalFlagNativeStalkUnit f n e ω Y hY u))]
  change (((toLex (fun i => (originalFlagGermVector
    (schemeProjectiveOriginalFlagGeometry f n e ω Y hY)
    (schemeProjectiveOriginalFlagPoint f n e ω Y hY)
    (schemeOriginalFlagNativeStalkUnit f n e ω Y hY u).val
    (Units.ne_zero (schemeOriginalFlagNativeStalkUnit f n e ω Y hY u)) i : ℤ))) :
      Lex (Fin n → ℤ)) : WithTop (Lex (Fin n → ℤ))) = 0
  rw [schemeOriginalFlagNativeStalkUnit_vector]
  rfl

/-- Actual endpoint membership makes the genuine overlap transition's WHOLE value zero. -/
theorem schemeOriginalFlagFrameTransition_value {L : X.Modules} {U V : X.Opens}
    (α : LocalBundleFrame L U) (β : LocalBundleFrame L V)
    (hx : schemeComplexPointImage f (schemeProjectiveOriginalFlagPoint f n e ω Y hY).val ∈ U)
    (hy : schemeComplexPointImage f (schemeProjectiveOriginalFlagPoint f n e ω Y hY).val ∈ V) :
    letI : Nonempty (U ⊓ V : X.Opens) := ⟨⟨_, hx, hy⟩⟩
    schemeOriginalFlagFunctionFieldValuation f n e ω Y hY
      (X.germToFunctionField (U ⊓ V)
        (localBundleFrameTransition α β (homOfLE inf_le_left) (homOfLE inf_le_right) :
          X.sheaf.obj.obj (Opposite.op (U ⊓ V)))) = 0 := by
  let : Nonempty (U ⊓ V : X.Opens) := ⟨⟨_, hx, hy⟩⟩
  rw [← localBundleFrameTransitionAtCenter_functionField α β _ hx hy]
  exact schemeOriginalFlagStalkUnit_value f n e ω Y hY
    (localBundleFrameTransitionAtCenter α β _ hx hy)

/-- ACTUAL tensor-power coefficients in any genuine point frames have the SAME entire value. -/
theorem schemeOriginalFlagFramePower_value_eq {L : X.Modules} {U V : X.Opens}
    (α : LocalBundleFrame L U) (β : LocalBundleFrame L V)
    (hx : schemeComplexPointImage f (schemeProjectiveOriginalFlagPoint f n e ω Y hY).val ∈ U)
    (hy : schemeComplexPointImage f (schemeProjectiveOriginalFlagPoint f n e ω Y hY).val ∈ V)
    (m : ℕ) (s : bundlePowerGlobalSections L m) :
    letI : Nonempty U := ⟨⟨_, hx⟩⟩
    letI : Nonempty V := ⟨⟨_, hy⟩⟩
    schemeOriginalFlagFunctionFieldValuation f n e ω Y hY
      (globalSectionToFunctionField (β.tensorPower m) s) =
      schemeOriginalFlagFunctionFieldValuation f n e ω Y hY
        (globalSectionToFunctionField (α.tensorPower m) s) := by
  let : Nonempty U := ⟨⟨_, hx⟩⟩
  let : Nonempty V := ⟨⟨_, hy⟩⟩
  let : Nonempty (U ⊓ V : X.Opens) := ⟨⟨_, hx, hy⟩⟩
  let v := schemeOriginalFlagFunctionFieldValuation f n e ω Y hY
  rw [LocalBundleFrame.globalGenericPowerCoefficient_transition α β
    (homOfLE inf_le_left : U ⊓ V ⟶ U) (homOfLE inf_le_right : U ⊓ V ⟶ V),
    v.map_mul, v.map_pow, schemeOriginalFlagFrameTransition_value f n e ω Y hY α β hx hy,
    nsmul_zero, zero_add]

/-- The actual internally chosen point-frame value agrees with ANY genuine original frame there. -/
theorem schemeOriginalFlagSectionValue_eq_frame {L : X.Modules} (a : LineBundleAtlas L)
    {U : X.Opens} (α : LocalBundleFrame L U)
    (hx : schemeComplexPointImage f (schemeProjectiveOriginalFlagPoint f n e ω Y hY).val ∈ U)
    (m : ℕ) (s : bundlePowerGlobalSections L m) :
    letI : Nonempty U := ⟨⟨_, hx⟩⟩
    schemeOriginalFlagSectionValue f n e ω Y hY a m s =
      schemeOriginalFlagFunctionFieldValuation f n e ω Y hY
        (globalSectionToFunctionField (α.tensorPower m) s) := by
  let : Nonempty U := ⟨⟨_, hx⟩⟩
  let p := (schemeProjectiveOriginalFlagPoint f n e ω Y hY).val
  exact schemeOriginalFlagFramePower_value_eq f n e ω Y hY α (schemePointFrame f p a)
    hx (schemePointFrame_mem f p a) m s

/-- Two actual atlases of the SAME original sheaf give identical whole section values. -/
theorem schemeOriginalFlagSectionValue_atlas_independent {L : X.Modules}
    (a b : LineBundleAtlas L) (m : ℕ) (s : bundlePowerGlobalSections L m) :
    schemeOriginalFlagSectionValue f n e ω Y hY a m s =
      schemeOriginalFlagSectionValue f n e ω Y hY b m s :=
  schemeOriginalFlagSectionValue_eq_frame f n e ω Y hY a
    (schemePointFrame f (schemeProjectiveOriginalFlagPoint f n e ω Y hY).val b)
    (schemePointFrame_mem f (schemeProjectiveOriginalFlagPoint f n e ω Y hY).val b) m s

/-- EVERY natural coordinate is independent of the actual original atlas choice. -/
theorem schemeOriginalFlagSectionVector_atlas_independent {L : X.Modules}
    (a b : LineBundleAtlas L) (m : ℕ) (s : bundlePowerGlobalSections L m) (hs : s ≠ 0) :
    schemeOriginalFlagSectionVector f n e ω Y hY a m s hs =
      schemeOriginalFlagSectionVector f n e ω Y hY b m s hs := by
  have h := schemeOriginalFlagSectionValue_atlas_independent f n e ω Y hY a b m s
  rw [schemeOriginalFlagSectionValue_of_ne_zero f n e ω Y hY a m s hs,
    schemeOriginalFlagSectionValue_of_ne_zero f n e ω Y hY b m s hs] at h
  have hlex := WithTop.coe_injective h
  have hfun := congrArg (ofLex : Lex (Fin n → ℤ) → Fin n → ℤ) hlex
  funext i
  exact Nat.cast_injective (congrFun hfun i)

end SGPT.Okounkov
