import SGPT.Okounkov.SchemeAnalyticTNManifold
import SGPT.Okounkov.NativeFlagGermVector
import SGPT.Foundations.Schemes.NativeProjectiveFano

/-!
# The actual original flag on the SAME scheme point manifold

Genuine projectivity gives compactness of the actual scheme point space.
The actual original smooth flag gives ambient connectedness through its
literal level zero and supplies its actual singleton endpoint internally.
The ordinary ACTUAL Kähler background is retained as source geometry; native
Fubini–Study-to-TN transport is separate and is not claimed by this module.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Okounkov

open CategoryTheory AlgebraicGeometry Algebra SGPT.Foundations.Schemes Set
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open scoped Topology

variable {X : Scheme} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]

local instance originalSchemeFlagTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f

local instance originalSchemeFlagCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n

local instance originalSchemeFlagManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

omit [IsSeparated f] [QuasiCompact f] in
/-- Actual level-zero connectedness gives the original ambient connected space;
algebraic integrality is not used as an analytic connectedness certificate. -/
theorem schemeSmoothFlag_connectedSpace
    (Y : Fin (n + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y) :
    ConnectedSpace (SchemeComplexPoint f) := by
  apply connectedSpace_iff_univ.mpr
  rw [← hY.1]
  exact (hY.level_closed_connected 0).2

/-- Genuine source projectivity and the actual original flag manufacture
compact connected original geometry, preserving the SAME actual objects. -/
def schemeProjectiveOriginalFlagGeometry (e : ClosedProjectiveEmbedding f)
    : letI := e.isSeparated
      letI := e.quasiCompact
      (ω : KahlerBackground n (SchemeComplexPoint f)) →
      (Y : Fin (n + 1) → Set (SchemeComplexPoint f)) →
      IsSmoothFlag Y → OriginalFlagGeometry n := by
  letI := e.isSeparated
  letI := e.quasiCompact
  intro ω Y hY
  letI : CompactSpace (SchemeComplexPoint f) := e.analyticCompact
  letI : ConnectedSpace (SchemeComplexPoint f) := schemeSmoothFlag_connectedSpace f n Y hY
  exact OriginalFlagGeometry.ofOriginal ω Y hY

/-- The actual original carrier is retained literally, without an equality premise. -/
theorem schemeProjectiveOriginalFlagGeometry_carrier (e : ClosedProjectiveEmbedding f)
    (ω : KahlerBackground n (SchemeComplexPoint f))
    (Y : Fin (n + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y) :
    (schemeProjectiveOriginalFlagGeometry f n e ω Y hY).carrier = SchemeComplexPoint f := rfl

/-- The actual manufactured preferred TN atlas is retained literally. -/
theorem schemeProjectiveOriginalFlagGeometry_charts (e : ClosedProjectiveEmbedding f)
    (ω : KahlerBackground n (SchemeComplexPoint f))
    (Y : Fin (n + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y) :
    (schemeProjectiveOriginalFlagGeometry f n e ω Y hY).charts =
      schemeAnalyticTNChartedSpace f n := rfl

/-- Exactly the original flag carriers enter the true dimension recursion. -/
theorem schemeProjectiveOriginalFlagGeometry_flag (e : ClosedProjectiveEmbedding f)
    (ω : KahlerBackground n (SchemeComplexPoint f))
    (Y : Fin (n + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y) :
    (schemeProjectiveOriginalFlagGeometry f n e ω Y hY).flag = Y := rfl

/-- Exactly the original ACTUAL background enters the true restricted-tail geometry. -/
theorem schemeProjectiveOriginalFlagGeometry_background (e : ClosedProjectiveEmbedding f)
    (ω : KahlerBackground n (SchemeComplexPoint f))
    (Y : Fin (n + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y) :
    (schemeProjectiveOriginalFlagGeometry f n e ω Y hY).omega = ω := rfl

/-- The endpoint is internally chosen from actual proved last-carrier nonemptiness. -/
def schemeProjectiveOriginalFlagPoint (e : ClosedProjectiveEmbedding f)
    (ω : KahlerBackground n (SchemeComplexPoint f))
    (Y : Fin (n + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y) :
    OriginalFlagGermPoint (schemeProjectiveOriginalFlagGeometry f n e ω Y hY) :=
  Classical.choice inferInstance

/-- The actual chosen point lies in the SAME original last flag carrier. -/
theorem schemeProjectiveOriginalFlagPoint_mem (e : ClosedProjectiveEmbedding f)
    (ω : KahlerBackground n (SchemeComplexPoint f))
    (Y : Fin (n + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y) :
    (schemeProjectiveOriginalFlagPoint f n e ω Y hY).val ∈ Y (Fin.last n) :=
  (schemeProjectiveOriginalFlagPoint f n e ω Y hY).property

/-- Genuine zero-dimensional connected charts prove that this actual point
is the unique original endpoint; no singleton certificate is an input. -/
theorem schemeProjectiveOriginalFlagPoint_last_eq_singleton (e : ClosedProjectiveEmbedding f)
    (ω : KahlerBackground n (SchemeComplexPoint f))
    (Y : Fin (n + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y) :
    Y (Fin.last n) = {(schemeProjectiveOriginalFlagPoint f n e ω Y hY).val} := by
  obtain ⟨q, hq⟩ := hY.last_eq_singleton
  have hp := schemeProjectiveOriginalFlagPoint_mem f n e ω Y hY
  rw [hq] at hp
  have heq := Set.mem_singleton_iff.mp hp
  exact hq.trans (congrArg (fun z : SchemeComplexPoint f => ({z} : Set (SchemeComplexPoint f)))
    heq.symm)

end SGPT.Okounkov
