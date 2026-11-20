import SGPT.Okounkov.NativeFlagGermCartier
import SGPT.Okounkov.SchemeProjectiveOriginalFlag
import SGPT.Okounkov.SchemeSectionAnalyticDivisor
import SGPT.Okounkov.EffectiveDivisorSectionCompatibility

/-!
# Actual scheme section vectors and Cartier divisor currents

The original point-frame coefficient generates the entire analytic section
divisor ideal.  Its already defined vector therefore satisfies the genuine
Cartier recursion and agrees with the independently constructed divisor-current
vector.  The projective embedding supplies the Kähler background internally.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Okounkov

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open scoped Topology

section GeneralDimension

variable {X : Scheme} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)

local instance sectionCartierPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance sectionCartierPointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n

/-- The original section divisor has the whole principal ideal of the same
point-frame coefficient, for every original function at every point. -/
theorem schemeSectionAnalyticDivisor_native_generator {L : X.Modules}
    (a : LineBundleAtlas L) (k : ℕ) (s : bundlePowerGlobalSections L k) (hs : s ≠ 0)
    (p : SchemeComplexPoint f) (h : SchemeComplexPoint f → ℂ) :
    letI := E.isSeparated
    letI := E.quasiCompact
    (schemeSectionAnalyticDivisor f n E a k s hs).ideal.mem p h ↔
      ∃ hh : HolomorphicAt n h p, NativeHolGerm.mk h hh ∈
        Ideal.span {schemePointPowerSectionNativeGerm f n p a k s} := by
  let := E.isSeparated
  let := E.quasiCompact
  rw [schemeSectionAnalyticDivisor_ideal]
  exact schemeSectionAnalyticIdeal_mem f n E a k s p h

variable (Y : Fin (n + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)

/-- Actual nonzero sections internally supply every local-generator premise
for their entire original Cartier recursion, including dimension zero. -/
theorem schemeFubiniStudySectionVector_cartier {L : X.Modules}
    (a : LineBundleAtlas L) (k : ℕ) (s : bundlePowerGlobalSections L k) (hs : s ≠ 0) :
    letI := E.isSeparated
    letI := E.quasiCompact
    OriginalCartierFlagValuation n (schemeFubiniStudyOriginalFlagGeometry f n E Y hY)
      (schemeSectionAnalyticDivisor f n E a k s hs)
      (schemeFubiniStudySectionVector f n E Y hY a k s hs) := by
  let := E.isSeparated
  let := E.quasiCompact
  let F := schemeFubiniStudyOriginalFlagGeometry f n E Y hY
  let x := schemeProjectiveOriginalFlagPoint f n E
    (schemeProjectiveTNKahlerBackground f n E) Y hY
  exact originalCartierFlagValuation_of_native_generator n F x
    (schemeSectionAnalyticDivisor f n E a k s hs)
    (schemePointPowerSectionNativeGerm f n x.val a k s)
    (schemePointPowerSectionNativeGerm_ne_zero f n x.val a k s hs)
    (schemeSectionAnalyticDivisor_native_generator f n E a k s hs x.val)

/-- The independently chosen Cartier-section vector equals the previously
defined whole section vector on the same actual flag and generated background. -/
theorem schemeFubiniStudySectionVector_eq_cartierSection {L : X.Modules}
    (a : LineBundleAtlas L) (k : ℕ) (s : bundlePowerGlobalSections L k) (hs : s ≠ 0) :
    letI := E.isSeparated
    letI := E.quasiCompact
    schemeFubiniStudySectionVector f n E Y hY a k s hs =
      cartierSectionFlagValuation (schemeFubiniStudyOriginalFlagGeometry f n E Y hY)
        (schemeSectionAnalyticDivisor f n E a k s hs) := by
  let := E.isSeparated
  let := E.quasiCompact
  let F := schemeFubiniStudyOriginalFlagGeometry f n E Y hY
  let D := schemeSectionAnalyticDivisor f n E a k s hs
  exact originalCartierFlagValuation_unique F D
    (schemeFubiniStudySectionVector_cartier f n E Y hY a k s hs)
    ((originalCartierSectionFlagValuation_iff_ideal n F D _).mp
      (cartierSectionFlagValuation_spec F D))

end GeneralDimension

section PositiveDimension

variable {X : Scheme} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) (m : ℕ)
  [SmoothOfRelativeDimension (m + 1) f] (E : ClosedProjectiveEmbedding f)

local instance sectionCurrentPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance sectionCurrentPointCharts :
    ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)

/-- The actual whole section-divisor integration current has exactly the
original section tuple, with the literal natural-to-nonnegative-real cast. -/
theorem schemeFubiniStudySectionVector_current
    (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)
    {L : X.Modules} (a : LineBundleAtlas L) (k : ℕ)
    (s : bundlePowerGlobalSections L k) (hs : s ≠ 0) :
    letI := E.isSeparated
    letI := E.quasiCompact
    let F := schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY
    let D := schemeSectionAnalyticDivisor f (m + 1) E a k s hs
    currentFlagValuation F (effectiveDivisorIntegrationCurrent F D)
      (effectiveDivisorIntegrationCurrent_closed_type_positive F D).1
      (effectiveDivisorIntegrationCurrent_closed_type_positive F D).2.1
      (effectiveDivisorIntegrationCurrent_closed_type_positive F D).2.2 =
      (fun i => (schemeFubiniStudySectionVector f (m + 1) E Y hY a k s hs i : NNReal)) := by
  let := E.isSeparated
  let := E.quasiCompact
  let F := schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY
  let D := schemeSectionAnalyticDivisor f (m + 1) E a k s hs
  have hvec := schemeFubiniStudySectionVector_eq_cartierSection f (m + 1) E Y hY a k s hs
  rw [hvec]
  exact currentFlagValuation_effectiveDivisor_eq_section_vector F D

end PositiveDimension

end SGPT.Okounkov
