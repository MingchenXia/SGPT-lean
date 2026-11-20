import SGPT.Toric.GeodesicSubgeodesic
import SGPT.Toric.GeodesicGeneral

/-! The exact two original source sets of cor:geodG and the actual existing
varying-endpoint toric subgeodesic/profile equivalence. Full duality is
implemented by the adjacent genuine closed-strip producers and consumers. -/

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric

open Set Filter MeasureTheory SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open scoped Topology ContDiff BigOperators

variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

namespace BigToricMetric

variable {D : ToricDivisor γ hs} (h : BigToricMetric D)
variable (omega : KahlerBackground n (PolytopeToricVariety γ hs))

local notation "X" => PolytopeToricVariety γ hs
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Exactly the first set of cor:geodG, including both freely varying
actual toric endpoints and their original pointwise upper bounds. -/
def sourceLowerEndpointToricSubgeodesics (φ₀ φ₁ : X → EReal) :=
  Σ ψ₀ : {ψ : X → EReal // ψ ∈ h.PSHTor ∧ ψ ≤ φ₀},
    Σ ψ₁ : {ψ : X → EReal // ψ ∈ h.PSHTor ∧ ψ ≤ φ₁},
      {c // h.IsToricSubgeodesic omega ψ₀.val ψ₁.val c}

/-- The corresponding actual varying-endpoint finite convex strip profiles. -/
def sourceLowerEndpointToricProfiles (φ₀ φ₁ : X → EReal) :=
  Σ ψ₀ : {ψ : X → EReal // ψ ∈ h.PSHTor ∧ ψ ≤ φ₀},
    Σ ψ₁ : {ψ : X → EReal // ψ ∈ h.PSHTor ∧ ψ ≤ φ₁},
      {F // h.IsToricSubgeodesicProfile ψ₀.val ψ₁.val F}

/-- A genuine existing equivalence handles the ENTIRE first source set.
It does not yet identify that set with the second set of cor:geodG. -/
def sourceLowerEndpointToricProfileEquiv (φ₀ φ₁ : X → EReal) :
    h.sourceLowerEndpointToricSubgeodesics omega φ₀ φ₁ ≃
      h.sourceLowerEndpointToricProfiles φ₀ φ₁ :=
  Equiv.sigmaCongrRight fun ψ₀ => Equiv.sigmaCongrRight fun ψ₁ =>
    h.toricSubgeodesicEquiv omega ψ₀.property.1 ψ₁.property.1

/-- Exactly the second set of cor:geodG. IsProper includes actual convexity;
lower semicontinuity supplies closedness. G is the existential function in
the printed hypothesis, not an assumed proof of the desired bijection. -/
def sourceGeodGDuals (φ₀ φ₁ : X → EReal) :=
  {Ψ : E × ℝ → EReal // IsProper Ψ ∧ LowerSemicontinuous Ψ ∧
    ∃ G : E → EReal, IsProper G ∧ LowerSemicontinuous G ∧
      ∀ (m : E) (s : ℝ),
        max (h.legendre φ₀ m) (h.legendre φ₁ m + (s : EReal)) ≤ Ψ (m, s) ∧
          Ψ (m, s) ≤ G m + ((max s 0 : ℝ) : EReal)}

end BigToricMetric
end SGPT.Toric
