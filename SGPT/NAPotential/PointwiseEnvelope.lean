import SGPT.NAPotential.BerkovichPiecewiseLinear
import SGPT.Convex.Epigraph

/-!
Order-theoretic properties of the literal, pointwise upper concave envelope
of the source piecewise-linear curve. No assertion of spatial upper
semicontinuity or theta-psh is made.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.NAPotential.Berkovich.PiecewiseLinearData

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH.VariableComplexAtlas

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]
variable {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- The upper concave envelope in the parameter, formed separately at each point. -/
def pointwiseUpperConcaveEnvelope (D : PiecewiseLinearData θ) (s : ℝ) (x : M) : EReal :=
  -SGPT.Convex.lowerConvexEnvelope (fun t : ℝ => -D.curve t x) s

theorem pointwiseUpperConcaveEnvelope_concave (D : PiecewiseLinearData θ) (x : M) :
    SGPT.Convex.IsConvex (fun s : ℝ => -D.pointwiseUpperConcaveEnvelope s x) := by
  simpa only [pointwiseUpperConcaveEnvelope, neg_neg] using
    SGPT.Convex.isConvex_lowerConvexEnvelope (fun t : ℝ => -D.curve t x)

theorem le_pointwiseUpperConcaveEnvelope (D : PiecewiseLinearData θ) (s : ℝ) (x : M) :
    D.curve s x ≤ D.pointwiseUpperConcaveEnvelope s x := by
  have h := SGPT.Convex.lowerConvexEnvelope_le (fun t : ℝ => -D.curve t x) s
  have hn := EReal.neg_le_neg_iff.mpr h
  simpa only [pointwiseUpperConcaveEnvelope, neg_neg] using hn

/-- Every pointwise concave majorant dominates the literal upper envelope. -/
theorem pointwiseUpperConcaveEnvelope_le (D : PiecewiseLinearData θ) (B : ℝ → M → EReal)
    (hconc : ∀ x, SGPT.Convex.IsConvex (fun s : ℝ => -B s x))
    (hdom : ∀ s x, D.curve s x ≤ B s x) (s : ℝ) (x : M) :
    D.pointwiseUpperConcaveEnvelope s x ≤ B s x := by
  have hm : (fun t : ℝ => -B t x) ≤ fun t : ℝ => -D.curve t x := by
    intro t
    exact EReal.neg_le_neg_iff.mpr (hdom t x)
  have h := SGPT.Convex.le_lowerConvexEnvelope (hconc x) hm s
  have hn := EReal.neg_le_neg_iff.mpr h
  simpa only [pointwiseUpperConcaveEnvelope, neg_neg] using hn

end SGPT.NAPotential.Berkovich.PiecewiseLinearData
