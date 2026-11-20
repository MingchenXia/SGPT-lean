import SGPT.Toric.SourceToricPartialBodyPositive
import SGPT.Okounkov.ZeroSourcePartialBody

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Filter MeasureTheory SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov SGPT.Okounkov.PartialBody
open scoped Topology ContDiff BigOperators Manifold ENNReal

variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

namespace BigToricMetric
variable {D : ToricDivisor γ hs} (h : BigToricMetric D)

/-- The book's genuine general partial body on the SAME original toric
flag. Positive dimension uses the actual source εω intersection; dimension
zero uses the actual source resolution/approximation/perturbation definition.
This is a dimension dispatch between two independently constructed source
bodies, not a replacement by the desired Newton body. -/
def sourceToricPartialBody {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : φ ∈ h.PSHTor) (v : latticePolytopeVertices γ) (e : Fin n ≃ Fin n) :
    Set (Fin n → ℝ) := by
  cases n with
  | zero =>
    exact ZeroSource.generalBody (toricFlagGeometry (hs := hs) v e) h.form φ
      ((isThetaPSH_iff_nativeThetaPotential h.atlasForm φ).mp hφ.1)
  | succ d => exact generalPartialBody (toricFlagGeometry (hs := hs) v e) h.form φ

/-- Exact source-definition readback in positive dimension. -/
theorem sourceToricPartialBody_pos {d : ℕ} {γ : K → Fin (d + 1) → ℤ}
    {hs : latticePolytopeEdgeSmooth γ} {D : ToricDivisor γ hs} (h : BigToricMetric D)
    {φ : PolytopeToricVariety γ hs → EReal} (hφ : φ ∈ h.PSHTor)
    (v : latticePolytopeVertices γ) (e : Fin (d + 1) ≃ Fin (d + 1)) :
    h.sourceToricPartialBody hφ v e =
      generalPartialBody (toricFlagGeometry (hs := hs) v e) h.form φ := rfl

/-- Exact source-definition readback in dimension zero, retaining the
original source construction and its produced nondegenerate potential. -/
theorem sourceToricPartialBody_zero {γ : K → Fin 0 → ℤ}
    {hs : latticePolytopeEdgeSmooth γ} {D : ToricDivisor γ hs} (h : BigToricMetric D)
    {φ : PolytopeToricVariety γ hs → EReal} (hφ : φ ∈ h.PSHTor)
    (v : latticePolytopeVertices γ) (e : Fin 0 ≃ Fin 0) :
    h.sourceToricPartialBody hφ v e =
      ZeroSource.generalBody (toricFlagGeometry (hs := hs) v e) h.form φ
        ((isThetaPSH_iff_nativeThetaPotential h.atlasForm φ).mp hφ.1) := rfl

/-- Whole source `thm:toricpob`, `eq:toricOkounkovcomp`: the actual
partial Okounkov body is the literal affine image of the original Newton
body, for every original toric PSH potential of positive original mass.
All dimensions, original poles and arbitrary original metric are retained. -/
theorem sourceToricPartialBody_eq_flagImage
    {φ : PolytopeToricVariety γ hs → EReal} (hφ : φ ∈ h.PSHTor)
    (hpos : 0 < h.MA hφ univ) (v : latticePolytopeVertices γ) (e : Fin n ≃ Fin n) :
    toricFlagRealMap hs v e D '' h.newtonBody φ = h.sourceToricPartialBody hφ v e := by
  cases n with
  | zero =>
    have hφn : IsThetaPshPotential h.form.val φ :=
      (isThetaPSH_iff_nativeThetaPotential h.atlasForm _).mp hφ.1
    rw [h.sourceToricPartialBody_zero hφ v e, ZeroSource.generalBody_eq_partial,
      ZeroSource.partialOkounkovBody_eq_univ (toricFlagGeometry (hs := hs) v e) hφn]
    apply eq_univ_of_forall
    intro y
    obtain ⟨p, hp⟩ := (h.newtonBody_properties
      (h.nonempty_toricDivisorPolytope_of_mem hφ) hφ).1
    exact ⟨p, hp, Subsingleton.elim _ _⟩
  | succ d =>
    rw [h.sourceToricPartialBody_pos hφ v e]
    exact h.sourceToricPartialBody_eq_flagImage_pos hφ hpos v e

/-- COMPLETE original `thm:toricpob`, both displayed clauses together.
No strengthened mass, analytic, Kähler-current, or body certificate
hypothesis is supplied. The volume is the actual source I-volume. -/
theorem sourceToricPartialOkounkovComparison
    {φ : PolytopeToricVariety γ hs → EReal} (hφ : φ ∈ h.PSHTor)
    (hpos : 0 < h.MA hφ univ) (v : latticePolytopeVertices γ) (e : Fin n ≃ Fin n) :
    (toricFlagRealMap hs v e D '' h.newtonBody φ = h.sourceToricPartialBody hφ v e) ∧
      (n.factorial : ENNReal) * volume (h.newtonBody φ) =
        sourceIVolume h.atlasForm φ hφ.1 :=
  ⟨h.sourceToricPartialBody_eq_flagImage hφ hpos v e,
    (h.sourceIVolume_eq_factorial_volume_newtonBody hφ).symm⟩

end BigToricMetric
end SGPT.Toric
