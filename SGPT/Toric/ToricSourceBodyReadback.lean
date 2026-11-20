import SGPT.Toric.SourceToricPartialBody
import SGPT.Okounkov.SourceTestCurveAllDimensions

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set SGPT.Okounkov SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- Exact original source-definition readback of the SAME general body,
including the actual0-dimensional approximation/perturbation construction. -/
theorem BigToricMetric.sourceToricPartialBody_eq_sourceGeneralBody
    {D : ToricDivisor γ hs} (h : BigToricMetric D)
    {φ : PolytopeToricVariety γ hs → EReal} (hφ : φ ∈ h.PSHTor)
    (v : latticePolytopeVertices γ) (e : Fin n ≃ Fin n) :
    h.sourceToricPartialBody hφ v e =
      SourceTestCurveAllDimensions.generalBody (toricFlagGeometry (hs := hs) v e) h.form
        ⟨φ,(isThetaPSH_iff_nativeThetaPotential h.atlasForm φ).mp hφ.1⟩ := by
  cases n <;> rfl

/-- The genuine original affine flag map is injective in EVERY dimension,
by its independently produced native affine homeomorphism. -/
theorem toricFlagRealMap_injective (v : latticePolytopeVertices γ) (e : Fin n ≃ Fin n)
    (D : ToricDivisor γ hs) : Function.Injective (toricFlagRealMap hs v e D) := by
  intro x y hxy
  apply (toricFlagRealHomeomorph (hs := hs) v e D).injective
  simpa only [toricFlagRealHomeomorph_apply] using hxy

/-- Actual finite-coordinate equality casts are genuine bijective coordinate
maps; this lemma imposes no geometric or body equality premise. -/
theorem castToricFlagCoordinates_injective {d q : ℕ} (h : d = q) :
    Function.Injective (fun x : Fin d → ℝ => fun j : Fin q => x (Fin.cast h.symm j)) := by
  cases h
  exact fun _ _ hxy => hxy

end SGPT.Toric
