import SGPT.Checks.Comparison.BJCanonicalModuleTopology
import Mathlib.Analysis.Convex.Gauge
import Mathlib.Algebra.Module.ULift

/-! Generic genuine gauge producer for the canonical finest real module
topology. The source-facing consumer will internally prove its hypotheses. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.NAPotential.BJ.ModuleGauge
open Topology Filter Set
open scoped Pointwise
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- An arbitrary actual algebraic seminorm is continuous from the canonical
module topology; the auxiliary seminormed module is internally constructed. -/
theorem continuous_seminorm (q : Seminorm ℝ E) :
    @Continuous E ℝ (moduleTopology ℝ E) inferInstance q := by
  let q' : Seminorm ℝ (ULift.{0} E) := q.comp (ULift.moduleEquiv.toLinearMap)
  let hnorm : SeminormedAddCommGroup (ULift.{0} E) :=
    q'.toAddGroupSeminorm.toSeminormedAddCommGroup
  let : NormedSpace ℝ (ULift.{0} E) := {
    norm_smul_le := fun r x => by
      change q' (r•x)≤‖r‖*q' x
      exact (q'.smul' r x).le }
  let := moduleTopology ℝ E
  let : TopologicalSpace (ULift.{0} E) :=
    hnorm.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  have hc : Continuous ((ULift.moduleEquiv : ULift.{0} E ≃ₗ[ℝ] E).symm : E → ULift.{0} E) :=
    IsModuleTopology.continuous_of_linearMap
      (ULift.moduleEquiv : ULift.{0} E ≃ₗ[ℝ] E).symm.toLinearMap
  have hq := continuous_norm.comp hc
  change Continuous q at hq
  exact hq

/-- The actual gauge supplies a real open unit ball inside an arbitrary
balanced convex absorbent set, with no incoming neighborhood certificate. -/
theorem mem_nhds_zero_of_balanced_convex_absorbent {U : Set E}
    (hb : Balanced ℝ U) (hc : Convex ℝ U) (ha : Absorbent ℝ U) :
    U∈@nhds E (moduleTopology ℝ E) 0 := by
  let := moduleTopology ℝ E
  let q : Seminorm ℝ E := gaugeSeminorm hb hc ha
  have hcont : Continuous q := continuous_seminorm q
  have hopen : IsOpen {x : E | q x<1} := isOpen_lt hcont continuous_const
  have h0 : (0:E)∈{x : E | q x<1} := by
    change q 0<1
    rw [map_zero]
    norm_num
  apply Filter.mem_of_superset (hopen.mem_nhds h0)
  exact setOfPred_gauge_lt_one_subset_self hc ha.zero_mem ha

end SGPT.NAPotential.BJ.ModuleGauge
