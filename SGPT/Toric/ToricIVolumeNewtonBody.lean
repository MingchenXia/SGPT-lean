import SGPT.Toric.Toric5IGood

/-!
Static draft during the cache no-Lean freeze. Not compiled or adopted.

This is the scalar SOURCE I-volume / source Newton body consumer needed by
`thm:mix_vol_newbod`. The I-envelope is manufactured from the actual input;
no equality of volumes, positive mass, I-model or I-goodness is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.Toric

open Set Filter MeasureTheory SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ContDiff BigOperators ENNReal

variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

namespace BigToricMetric

variable {D : ToricDivisor γ hs} (h : BigToricMetric D)

/-- The actual original single I-volume, including vanishing masses and n=0,
equals the normalized Euclidean volume of the original Newton body.

The proof uses the SAME source I-envelope, its genuine torus invariance,
and the proved multiplier-ideal/body dictionary. -/
theorem sourceIVolume_eq_factorial_volume_newtonBody
    {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor) :
    sourceIVolume h.atlasForm u hu.1 =
      (n.factorial : ENNReal) * volume (h.newtonBody u) := by
  have hψ : sourceIEnvelope h.atlasForm u ∈ h.PSHTor :=
    ⟨isThetaPSH_sourceIEnvelope hu.1, h.sourceIEnvelope_invariant hu⟩
  have hbody : h.newtonBody u = h.newtonBody (sourceIEnvelope h.atlasForm u) :=
    (h.sourceIEquivalent_iff_newtonBody_eq hu hψ).mp
      (sourceIEquivalent_iEnvelope hu.1)
  change h.MA hψ univ = _
  rw [h.MA_univ (h.nonempty_toricDivisorPolytope_of_mem hu) hψ, ← hbody]

end BigToricMetric
end SGPT.Toric
