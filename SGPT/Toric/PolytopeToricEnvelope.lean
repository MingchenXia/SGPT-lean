import SGPT.Toric.PolytopeToricNewtonBody
import SGPT.PSH.SourceEnvelopeRooftop
import SGPT.Toric.ToricEnvelopeClosure

/-!
# The envelope `P_ω[φ]` of a toric potential

Source `chapter_toric_ample.tex`, `prop:GPenvelope`: for `φ ∈ PSH_tor(X, ω)`,
`P_ω[φ] ∈ PSH_tor(X, ω)` and `G_{P_ω[φ]} = G_0` on `Δ(ω, φ)` and `+∞` elsewhere
(`eq:toricPenv`).  The proof follows the source: `P_ω[φ] = usc sup_C ((φ + C) ∧ 0)`
(`eq:Penvsups`), the rooftop and constant formulas and the regularized-supremum
formula, then the closure of `inf_C (G_0 ∨ (G_φ - C))` is computed.

Here `X = PolytopeToricVariety γ hs` for an arbitrary Delzant lattice polytope, and
`P_ω[φ]` is the source envelope `sourceSingularityEnvelope` (source `def:Penv`).
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ContDiff BigOperators Classical

variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable (γ : K → Fin n → ℤ) (hs : latticePolytopeEdgeSmooth γ)

/-- The real facet entropy `Σ_ρ (⟨m,u_ρ⟩ + a_ρ) log(⟨m,u_ρ⟩ + a_ρ)` of `eq:G0def`. -/
def polytopeToricEntropyReal (m : EuclideanSpace ℝ (Fin n)) : ℝ :=
  let _ := originalPolytopeFacetFintype γ hs
  facetEntropyReal (fun F => (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n)))
    (originalFacetEuclideanNormal γ hs F)) (fun F => (originalFacetOffset γ hs F : ℝ)) m

theorem continuous_polytopeToricEntropyReal : Continuous (polytopeToricEntropyReal γ hs) := by
  let _ := originalPolytopeFacetFintype γ hs
  exact continuous_facetEntropyReal _ _

/-- On `P`, `G_0` is the real facet entropy. -/
theorem originalCanonicalEntropyEuclidean_eq_real {m : EuclideanSpace ℝ (Fin n)}
    (hm : m ∈ polytopeToricMomentPolytope γ) :
    originalCanonicalEntropyEuclidean γ hs m = (polytopeToricEntropyReal γ hs m : EReal) := by
  let _ := originalPolytopeFacetFintype γ hs
  rw [originalCanonicalEntropyEuclidean_eq_facetEntropy]
  have hm' : m ∈ facetRegion (fun F => (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n)))
      (originalFacetEuclideanNormal γ hs F)) (fun F => (originalFacetOffset γ hs F : ℝ)) := by
    rw [originalEuclideanFacetRegion_eq]
    exact hm
  simp only [facetEntropy, if_pos hm']
  rfl

/-- The rooftop `(φ + C) ∧ 0` of `eq:Penvsups`. -/
def polytopeToricShiftedRooftop (u : PolytopeToricVariety γ hs → EReal) (C : ℝ) :
    PolytopeToricVariety γ hs → EReal :=
  thetaRooftop (polytopeToricOmega γ hs) (fun p => u p + (C : EReal)) 0

/-- Source `prop:GPenvelope` (proof, rooftop step): for each `C ∈ ℝ`, the rooftop
`(φ + C) ∧ 0` is a toric potential with `G = G_0 ∨ (G_φ - C)`. -/
theorem polytopeToric_shiftedRooftop {u : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ PolytopeToricPSH γ hs) (C : ℝ) :
    polytopeToricShiftedRooftop γ hs u C ≠ ⊥ ∧
      polytopeToricShiftedRooftop γ hs u C ∈ PolytopeToricPSH γ hs ∧
      polytopeToricLegendre γ hs (polytopeToricShiftedRooftop γ hs u C) =
        fun m => max (polytopeToricLegendre γ hs (fun _ => 0) m)
          (polytopeToricLegendre γ hs u m - (C : EReal)) := by
  have hus := mem_polytopeToricPSH_add_const γ hs hu C
  have h0 : (0 : PolytopeToricVariety γ hs → EReal) ∈ PolytopeToricPSH γ hs :=
    zero_mem_polytopeToricPSH γ hs
  obtain ⟨B, hB⟩ := exists_upper_bound_polytopeToricPSH γ hs hu.1
  have hw : (ofFixedModel n (PolytopeToricVariety γ hs)).IsThetaPSH (polytopeToricOmega γ hs)
      (fun p => u p + ((C - max (B + C) 0 : ℝ) : EReal)) :=
    hu.1.add_const (C - max (B + C) 0)
  have hwu : (fun p => u p + ((C - max (B + C) 0 : ℝ) : EReal)) ≤
      fun p => u p + (C : EReal) := by
    intro p
    have hc : C - max (B + C) 0 ≤ C := by linarith [le_max_right (B + C) 0]
    exact add_le_add le_rfl (EReal.coe_le_coe_iff.mpr hc)
  have hw0 : (fun p => u p + ((C - max (B + C) 0 : ℝ) : EReal)) ≤ 0 := by
    intro p
    have hc : B + (C - max (B + C) 0) ≤ 0 := by linarith [le_max_left (B + C) 0]
    calc u p + ((C - max (B + C) 0 : ℝ) : EReal)
        ≤ (B : EReal) + ((C - max (B + C) 0 : ℝ) : EReal) := add_le_add (hB p) le_rfl
      _ = ((B + (C - max (B + C) 0) : ℝ) : EReal) := (EReal.coe_add _ _).symm
      _ ≤ ((0 : ℝ) : EReal) := EReal.coe_le_coe_iff.mpr hc
      _ = (0 : PolytopeToricVariety γ hs → EReal) p := by simp
  have hne : polytopeToricShiftedRooftop γ hs u C ≠ ⊥ := by
    intro hR
    obtain ⟨y, _, hy⟩ := hw.locallyNondegenerate (Classical.arbitrary _) (mem_univ _) univ
      isOpen_univ (mem_univ _)
    apply hy
    have hle := le_thetaRooftop hw hwu hw0 y
    change _ ≤ polytopeToricShiftedRooftop γ hs u C y at hle
    rw [hR] at hle
    exact le_bot_iff.mp hle
  refine ⟨hne, mem_polytopeToricPSH_thetaRooftop γ hs hus h0 hne, ?_⟩
  unfold polytopeToricShiftedRooftop
  rw [polytopeToricLegendre_thetaRooftop γ hs hus h0 hne, polytopeToricLegendre_add_const]
  funext m
  exact max_comm _ _

/-- The pointwise infimum `inf_C (G_0 ∨ (G_φ - C))` is `G_0` on `{G_φ < ∞}` and `+∞`
elsewhere; it is convex. -/
theorem polytopeToric_iInf_shifted_legendre {u : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ PolytopeToricPSH γ hs) :
    (fun C : ℝ => polytopeToricLegendre γ hs (polytopeToricShiftedRooftop γ hs u C)) =
      fun (C : ℝ) m => max (polytopeToricEntropyReal γ hs m : EReal)
        (polytopeToricLegendre γ hs u m - (C : EReal)) := by
  have hGu := polytopeToricLegendre_mem_closedProperOnBody γ hs hu
  funext C m
  simp only [(polytopeToric_shiftedRooftop γ hs hu C).2.2, polytopeToricLegendre_zero]
  by_cases hm : m ∈ polytopeToricMomentPolytope γ
  · rw [originalCanonicalEntropyEuclidean_eq_real γ hs hm]
  · have h1 : originalCanonicalEntropyEuclidean γ hs m = ⊤ := by
      by_contra h
      have hlt : m ∈ effectiveDomain (originalCanonicalEntropyEuclidean γ hs) :=
        lt_top_iff_ne_top.mpr h
      rw [effectiveDomain_originalCanonicalEntropyEuclidean] at hlt
      exact hm hlt
    rw [h1, hGu.2.2 m hm]
    simp

/-- Source `prop:GPenvelope`: `P_ω[φ] ∈ PSH_tor(X, ω)` and `eq:toricPenv`:
`G_{P_ω[φ]} = G_0` on `Δ(ω, φ)` and `+∞` outside. -/
theorem polytopeToric_sourceSingularityEnvelope {u : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ PolytopeToricPSH γ hs) :
    sourceSingularityEnvelope (polytopeToricOmega γ hs) u ∈ PolytopeToricPSH γ hs ∧
      ∀ m, polytopeToricLegendre γ hs (sourceSingularityEnvelope (polytopeToricOmega γ hs) u) m =
        if m ∈ polytopeToricNewtonBody γ hs u then polytopeToricLegendre γ hs (fun _ => 0) m
        else ⊤ := by
  have heq : sourceSingularityEnvelope (polytopeToricOmega γ hs) u =
      uscSup (fun C : ℝ => polytopeToricShiftedRooftop γ hs u C) :=
    sourceSingularityEnvelope_eq_uscSup_thetaRooftop (polytopeToricOmega γ hs) u
  have hmem : ∀ C : ℝ, polytopeToricShiftedRooftop γ hs u C ∈ PolytopeToricPSH γ hs :=
    fun C => (polytopeToric_shiftedRooftop γ hs hu C).2.1
  have hbd : ∀ (C : ℝ) p, polytopeToricShiftedRooftop γ hs u C p ≤ ((0 : ℝ) : EReal) := by
    intro C p
    have h := thetaRooftop_le_right (polytopeToricOmega γ hs) (fun q => u q + (C : EReal)) 0 p
    simpa [polytopeToricShiftedRooftop] using h
  refine ⟨by rw [heq]; exact mem_polytopeToricPSH_uscSup γ hs hmem hbd, ?_⟩
  have hGu := polytopeToricLegendre_mem_closedProperOnBody γ hs hu
  have hDP : effectiveDomain (polytopeToricLegendre γ hs u) ⊆ polytopeToricMomentPolytope γ := by
    intro m hm
    by_contra hmP
    exact (ne_of_lt hm) (hGu.2.2 m hmP)
  have hinf := iInf_max_sub_realReference (polytopeToricEntropyReal γ hs)
    (polytopeToricLegendre γ hs u)
  have hconv : IsConvex (realReferenceOnDomain (polytopeToricEntropyReal γ hs)
      (effectiveDomain (polytopeToricLegendre γ hs u))) := by
    have hepi : epigraph (realReferenceOnDomain (polytopeToricEntropyReal γ hs)
        (effectiveDomain (polytopeToricLegendre γ hs u))) =
        epigraph (originalCanonicalEntropyEuclidean γ hs) ∩
          (effectiveDomain (polytopeToricLegendre γ hs u) ×ˢ (univ : Set ℝ)) := by
      ext p
      by_cases hp : p.1 ∈ effectiveDomain (polytopeToricLegendre γ hs u)
      · simp [epigraph, realReferenceOnDomain, hp,
          originalCanonicalEntropyEuclidean_eq_real γ hs (hDP hp)]
      · simp [epigraph, realReferenceOnDomain, hp]
    change Convex ℝ (epigraph _)
    rw [hepi]
    exact (isConvex_of_isClosedConvex (isClosedConvex_originalCanonicalEntropyEuclidean γ hs)).inter
      ((convex_effectiveDomain hGu.1.1).prod convex_univ)
  have hclosure : convexClosure (realReferenceOnDomain (polytopeToricEntropyReal γ hs)
      (effectiveDomain (polytopeToricLegendre γ hs u))) =
      realReferenceOnDomain (polytopeToricEntropyReal γ hs)
        (closure (effectiveDomain (polytopeToricLegendre γ hs u))) := by
    rw [convexClosure_of_forall_ne_bot]
    · exact regularization_realReferenceOnDomain _ _
        (continuous_polytopeToricEntropyReal γ hs).continuousOn
    · intro x
      by_cases hx : x ∈ effectiveDomain (polytopeToricLegendre γ hs u) <;>
        simp [realReferenceOnDomain, hx]
  intro m
  rw [heq, polytopeToricLegendre_uscSup γ hs hmem hbd, polytopeToric_iInf_shifted_legendre γ hs hu]
  change convexClosure (lowerConvexEnvelope (fun m => ⨅ C : ℝ,
    max (polytopeToricEntropyReal γ hs m : EReal)
      (polytopeToricLegendre γ hs u m - (C : EReal)))) m = _
  rw [hinf, lowerConvexEnvelope_eq_self hconv, hclosure]
  by_cases hm : m ∈ closure (effectiveDomain (polytopeToricLegendre γ hs u))
  · have hmP : m ∈ polytopeToricMomentPolytope γ :=
      closure_minimal hDP (isCompact_polytopeToricMomentPolytope γ).isClosed hm
    have hmΔ : m ∈ polytopeToricNewtonBody γ hs u := hm
    simp only [realReferenceOnDomain, if_pos hm, if_pos hmΔ, polytopeToricLegendre_zero,
      originalCanonicalEntropyEuclidean_eq_real γ hs hmP]
  · have hmΔ : m ∉ polytopeToricNewtonBody γ hs u := hm
    simp only [realReferenceOnDomain, if_neg hm, if_neg hmΔ]

end SGPT.Toric
