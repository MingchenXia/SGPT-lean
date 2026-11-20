import SGPT.Toric.PolytopeToricNewtonBody
import SGPT.PSH.SourcePMassCharacterization
import SGPT.Foundations.Analysis.Pending.PluripolarCapacityDichotomy

/-!
# Toric energy classes

Source `chapter_toric_ample.tex`:

* `def:toric-ample:L1104`: `𝓔^∞_tor(X, ω)`, `𝓔^1_tor(X, ω)` and `𝓔_tor(X, ω)` are the
  intersections of `PSH_tor(X, ω)` with `𝓔^∞(X, ω)`, `𝓔^1(X, ω)` and `𝓔(X, ω)`; the
  classes are relative to `V_ω` (source `def:envelopes:L906`), and `V_ω = 0`;
* `prop:toric-ample:L990`: for `φ ∈ PSH_tor(X, ω)`, `φ ∈ 𝓔^∞(X, ω)` iff
  `F_φ ∈ 𝓔^∞(N_ℝ, P)` iff `G_φ ∼ G_0`.

Here `X = PolytopeToricVariety γ hs` for an arbitrary Delzant lattice polytope.
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ContDiff BigOperators

variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable (γ : K → Fin n → ℤ) (hs : latticePolytopeEdgeSmooth γ)

/-- `V_ω = 0` for the Kähler form `ω`. -/
theorem polytopeToric_sourceMinimalEnvelope_eq_zero :
    sourceMinimalEnvelope (polytopeToricOmega γ hs) = 0 := by
  apply le_antisymm (sourceMinimalEnvelope_le_zero _)
  intro x
  exact le_iSup (fun v : {v : PolytopeToricVariety γ hs → EReal //
      (ofFixedModel n (PolytopeToricVariety γ hs)).IsThetaPSH (polytopeToricOmega γ hs) v ∧
        v ≤ 0} => v.1 x)
    ⟨0, (zero_mem_polytopeToricPSH γ hs).1, le_rfl⟩

/-- `V_ω` is a model potential (`ω` is Kähler, hence big). -/
theorem polytopeToric_sourceModelPotential_minimalEnvelope :
    SourceModelPotential (polytopeToricOmega γ hs)
      (sourceMinimalEnvelope (polytopeToricOmega γ hs)) :=
  sourceMinimalEnvelope_model (polytopeToricKahlerBackground γ hs) (polytopeToricOmega γ hs)
    (Pending.PluripolarCapacityDichotomy.isBigClass_kahler (polytopeToricKahlerBackground γ hs))

/-- Source `def:toric-ample:L1104`: `𝓔^∞_tor(X, ω) = 𝓔^∞(X, ω) ∩ PSH_tor(X, ω)`. -/
def PolytopeToricEInfinity : Set (PolytopeToricVariety γ hs → EReal) :=
  {u | SourceRelativeEInfinity (polytopeToricOmega γ hs)
    (sourceMinimalEnvelope (polytopeToricOmega γ hs)) u} ∩ PolytopeToricPSH γ hs

/-- Source `def:toric-ample:L1104`: `𝓔_tor(X, ω) = 𝓔(X, ω) ∩ PSH_tor(X, ω)`. -/
def PolytopeToricFullMass : Set (PolytopeToricVariety γ hs → EReal) :=
  {u | SourceRelativeFullMass (polytopeToricOmega γ hs)
    (sourceMinimalEnvelope (polytopeToricOmega γ hs)) u
      (polytopeToric_sourceModelPotential_minimalEnvelope γ hs)} ∩ PolytopeToricPSH γ hs

/-- Source `def:toric-ample:L1104`: `𝓔^1_tor(X, ω) = 𝓔^1(X, ω) ∩ PSH_tor(X, ω)`. -/
def PolytopeToricFiniteEnergy : Set (PolytopeToricVariety γ hs → EReal) :=
  {u | SourceRelativeFiniteEnergy (polytopeToricOmega γ hs)
    (sourceMinimalEnvelope (polytopeToricOmega γ hs)) u
      (polytopeToric_sourceModelPotential_minimalEnvelope γ hs)} ∩ PolytopeToricPSH γ hs

/-- `φ ∼ 0` iff `F_φ ∼ F_0`. -/
theorem polytopeToric_singularityEquiv_zero_iff {u : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ PolytopeToricPSH γ hs) :
    SGPT.PSH.SingularityEquiv u 0 ↔
      SGPT.PSH.SingularityEquiv (polytopeToricProfile γ hs u)
        (fun x => (polytopeToricReference γ hs x : EReal)) := by
  have h0 : (0 : PolytopeToricVariety γ hs → EReal) ∈ PolytopeToricPSH γ hs :=
    zero_mem_polytopeToricPSH γ hs
  have hp0 : polytopeToricProfile γ hs (0 : PolytopeToricVariety γ hs → EReal) =
      fun x => (polytopeToricReference γ hs x : EReal) := polytopeToricProfile_zero γ hs
  rw [SGPT.PSH.singularityEquiv_iff, SGPT.PSH.singularityEquiv_iff,
    polytopeToricPSH_singularityLE_iff γ hs hu h0, polytopeToricPSH_singularityLE_iff γ hs h0 hu,
    hp0]

/-- `φ ∼ 0` iff `G_φ ∼ G_0`. -/
theorem polytopeToric_singularityEquiv_zero_iff_legendre {u : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ PolytopeToricPSH γ hs) :
    SGPT.PSH.SingularityEquiv u 0 ↔
      SGPT.PSH.SingularityEquiv (polytopeToricLegendre γ hs u)
        (polytopeToricLegendre γ hs (fun _ => (0 : EReal))) := by
  have h0 : (0 : PolytopeToricVariety γ hs → EReal) ∈ PolytopeToricPSH γ hs :=
    zero_mem_polytopeToricPSH γ hs
  rw [SGPT.PSH.singularityEquiv_iff, SGPT.PSH.singularityEquiv_iff,
    polytopeToricPSH_singularityLE_iff_legendre γ hs hu h0,
    polytopeToricPSH_singularityLE_iff_legendre γ hs h0 hu]
  exact and_comm

/-- Source `prop:toric-ample:L990`, (1) ⇔ (2): `φ ∈ 𝓔^∞(X, ω)` iff `F_φ ∈ 𝓔^∞(N_ℝ, P)`. -/
theorem polytopeToric_mem_eInfinity_iff_boundedGrowthClass
    {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ PolytopeToricPSH γ hs) :
    SourceRelativeEInfinity (polytopeToricOmega γ hs)
        (sourceMinimalEnvelope (polytopeToricOmega γ hs)) u ↔
      polytopeToricProfile γ hs u ∈
        BoundedGrowthClass (innerₗ (EuclideanSpace ℝ (Fin n))) (polytopeToricMomentPolytope γ) := by
  rw [SourceRelativeEInfinity, polytopeToric_sourceMinimalEnvelope_eq_zero,
    polytopeToric_singularityEquiv_zero_iff γ hs hu]
  have href := polytopeToricReference_singularityEquiv_support γ hs
  constructor
  · rintro ⟨_, h⟩
    exact ⟨isClosedConvex_polytopeToricProfile γ hs hu, singularityEquiv_trans h href⟩
  · rintro ⟨_, h⟩
    exact ⟨hu.1, singularityEquiv_trans h (singularityEquiv_symm href)⟩

/-- Source `prop:toric-ample:L990`, (1) ⇔ (3): `φ ∈ 𝓔^∞(X, ω)` iff `G_φ ∼ G_0`. -/
theorem polytopeToric_mem_eInfinity_iff_legendre
    {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ PolytopeToricPSH γ hs) :
    SourceRelativeEInfinity (polytopeToricOmega γ hs)
        (sourceMinimalEnvelope (polytopeToricOmega γ hs)) u ↔
      SGPT.PSH.SingularityEquiv (polytopeToricLegendre γ hs u)
        (polytopeToricLegendre γ hs (fun _ => (0 : EReal))) := by
  rw [SourceRelativeEInfinity, polytopeToric_sourceMinimalEnvelope_eq_zero,
    polytopeToric_singularityEquiv_zero_iff_legendre γ hs hu]
  exact ⟨fun h => h.2, fun h => ⟨hu.1, h⟩⟩

end SGPT.Toric
