import SGPT.NAPotential.PointwiseEnvelope
import SGPT.NAPotential.RayEnvelope
import SGPT.PSH.AtlasQPSHAddition
import Mathlib.Data.Fin.VecNotation

/-!
Genuine two-node source curves, their max-tail replacement, and its
unconditional theta-psh slices. The exact literal-envelope comparison under
a pointwise finite last node is proved in `TwoNodeTailExact`.
-/
set_option autoImplicit false
noncomputable section

namespace SGPT.NAPotential.TwoNodeRepair

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH.VariableComplexAtlas
open SGPT.NAPotential.Berkovich

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
variable {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- The actual source two-node data with parameters 0 and -1. -/
def twoNodeData (u v : M → EReal) (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hv : (ofFixedModel n M).IsThetaPSH θ v) : PiecewiseLinearData θ where
  N := 1
  A := ![u, v]
  τ := ![(0 : ℝ), -1]
  strictAnti := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num at *
  isThetaPSH := by
    intro i
    fin_cases i
    · exact hu
    · exact hv

/-- The proposed repair changes the left node to the genuine maximum. -/
def correctedData (u v : M → EReal) (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hv : (ofFixedModel n M).IsThetaPSH θ v) : PiecewiseLinearData θ :=
  twoNodeData u (fun x => max (u x) (v x)) hu (hu.max hv)

/-- The source tail after replacement is exactly the finite maximum. -/
theorem corrected_curve_tail (u v : M → EReal)
    (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hv : (ofFixedModel n M).IsThetaPSH θ v) {s : ℝ} (hs : s ≤ -1) (x : M) :
    (correctedData u v hu hv).curve s x = max (u x) (v x) := by
  have h := (correctedData u v hu hv).curve_of_le_last
    (show s ≤ (correctedData u v hu hv).τ
      (Fin.last (correctedData u v hu hv).N) from hs)
  change (correctedData u v hu hv).curve s = (fun x => max (u x) (v x)) at h
  exact congrFun h x

/-- The initial endpoint remains the original first node. -/
theorem corrected_curve_top (u v : M → EReal)
    (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hv : (ofFixedModel n M).IsThetaPSH θ v) (x : M) :
    (correctedData u v hu hv).curve 0 x = u x := by
  have h := (correctedData u v hu hv).curve_tau 0
  change (correctedData u v hu hv).curve 0 = u at h
  exact congrFun h x

/-- The source cutoff remains literal, including the open upper tail. -/
theorem corrected_curve_above (u v : M → EReal)
    (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hv : (ofFixedModel n M).IsThetaPSH θ v) {s : ℝ} (hs : 0 < s) (x : M) :
    (correctedData u v hu hv).curve s x = ⊥ := by
  have h := (correctedData u v hu hv).curve_of_lt
    (show (correctedData u v hu hv).τ 0 < s from hs)
  exact congrFun h x

/-- The proposed repaired slice is genuinely theta-psh for every s≤0.
This part does not need the extra finite-last-node hypothesis. -/
theorem corrected_curve_thetaPSH (u v : M → EReal)
    (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hv : (ofFixedModel n M).IsThetaPSH θ v) {s : ℝ} (hs : s ≤ 0) :
    (ofFixedModel n M).IsThetaPSH θ ((correctedData u v hu hv).curve s) := by
  apply (correctedData u v hu hv).isThetaPSH_curve
  exact hs

/-- Replacing the last value by the maximum preserves the weighted maximum,
for every ordered pair of real nodes and arbitrary extended-real values.
This is the scalar step relevant to analytification, not an analytification
or section theorem. -/
theorem weighted_max_tail_replacement (a b : EReal) {t₀ t₁ : ℝ} (ht : t₁ ≤ t₀) :
    max (a + (t₀ : EReal)) (max a b + (t₁ : EReal)) =
      max (a + (t₀ : EReal)) (b + (t₁ : EReal)) := by
  have ha : a + (t₁ : EReal) ≤ a + (t₀ : EReal) :=
    by simpa only [add_comm] using add_le_add_left (EReal.coe_le_coe ht) a
  rw [← max_add_add_right, ← max_assoc, max_eq_left ha]

/- The exact literal-envelope comparison is in `TwoNodeTailExact`. -/

end SGPT.NAPotential.TwoNodeRepair
