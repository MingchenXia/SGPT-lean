import SGPT.Toric.PolytopeToricOperations
import SGPT.Toric.ProjectiveToricNewtonBody
import SGPT.Convex.Subgradient

/-!
# The Newton body of a toric potential

Source `chapter_toric_ample.tex`:

* `def:Newtonbody1`: `Δ(ω, φ) = cl {G_φ < ∞} ⊆ P` is a convex body; by
  `prop:gradDomFstar` it is also the closure of the gradient image of `F_φ`;
* `ex:toric-ample:L621` (general clause): `Δ(ω, 0) = P`, since `G_0` is the facet
  entropy of `eq:G0def`, whose effective domain is `P`.

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

/-- Source `thm:toricpsh` (3): `G_φ` is closed proper convex and `+∞` off `P`. -/
theorem polytopeToricLegendre_mem_closedProperOnBody {u : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ PolytopeToricPSH γ hs) :
    polytopeToricLegendre γ hs u ∈ ClosedProperOnBody (polytopeToricMomentPolytope γ) :=
  conjugate_mem_closedProperOnBody_of_mem_growthClass (innerₗ (EuclideanSpace ℝ (Fin n)))
    (isCompact_polytopeToricMomentPolytope γ) (convex_polytopeToricMomentPolytope γ)
    (polytopeToricProfile_mem_growthClass γ hs hu)

/-- Source `def:Newtonbody1`: the Newton body `Δ(ω, φ) = cl {G_φ < ∞}`. -/
def polytopeToricNewtonBody (u : PolytopeToricVariety γ hs → EReal) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  convexNewtonBody (polytopeToricLegendre γ hs u)

/-- Source `def:Newtonbody1`: `Δ(ω, φ)` is a convex body contained in `P`. -/
theorem polytopeToricNewtonBody_properties {u : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ PolytopeToricPSH γ hs) :
    (polytopeToricNewtonBody γ hs u).Nonempty ∧ IsCompact (polytopeToricNewtonBody γ hs u) ∧
      Convex ℝ (polytopeToricNewtonBody γ hs u) ∧
        polytopeToricNewtonBody γ hs u ⊆ polytopeToricMomentPolytope γ := by
  have hG := polytopeToricLegendre_mem_closedProperOnBody γ hs hu
  have hD : effectiveDomain (polytopeToricLegendre γ hs u) ⊆ polytopeToricMomentPolytope γ := by
    intro m hm
    by_contra hmP
    exact (ne_of_lt hm) (hG.2.2 m hmP)
  have hsub : polytopeToricNewtonBody γ hs u ⊆ polytopeToricMomentPolytope γ :=
    closure_minimal hD (isCompact_polytopeToricMomentPolytope γ).isClosed
  refine ⟨hG.1.2.1.closure, (isCompact_polytopeToricMomentPolytope γ).of_isClosed_subset
    isClosed_closure hsub, (convex_effectiveDomain hG.1.1).closure, hsub⟩

/-- Source display after `def:Newtonbody1` (via `prop:gradDomFstar`):
`Δ(ω, φ) = cl ∇F_φ(N_ℝ)`, with the convex subgradient image. -/
theorem polytopeToricNewtonBody_eq_closure_rawSubgradientImage
    {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ PolytopeToricPSH γ hs) :
    polytopeToricNewtonBody γ hs u =
      closure (rawSubgradientImage (innerₗ (EuclideanSpace ℝ (Fin n)))
        (polytopeToricProfile γ hs u)) := by
  have hf := polytopeToricProfile_mem_growthClass γ hs hu
  exact (closure_rawSubgradientImage_eq_closure_effectiveDomain_conjugate _ hf.1
    (lowerSemicontinuous_of_isClosedConvex (isClosedConvex_polytopeToricProfile γ hs hu))).symm

/-! ### The reference potential: `Δ(ω, 0) = P` -/

/-- `G_0` of `eq:G0def` in the Euclidean model. -/
theorem effectiveDomain_originalCanonicalEntropyEuclidean :
    effectiveDomain (originalCanonicalEntropyEuclidean γ hs) = polytopeToricMomentPolytope γ := by
  change (EuclideanSpace.equiv (Fin n) ℝ) ⁻¹' effectiveDomain (originalCanonicalEntropy γ hs) = _
  rw [effectiveDomain_originalCanonicalEntropy]
  rfl

theorem isClosedConvex_originalCanonicalEntropyEuclidean :
    IsClosedConvex (originalCanonicalEntropyEuclidean γ hs) := by
  let _ := originalPolytopeFacetFintype γ hs
  rw [originalCanonicalEntropyEuclidean_eq_facetEntropy]
  apply isClosedConvex_facetEntropy
  rw [originalEuclideanFacetRegion_eq]
  exact nonempty_polytopeToricMomentPolytope γ

/-- `F_0 = G_0^*` in the Euclidean model (source `eq:F0def`). -/
theorem polytopeToricReference_eq_conjugate (x : EuclideanSpace ℝ (Fin n)) :
    (polytopeToricReference γ hs x : EReal) =
      conjugate (innerₗ (EuclideanSpace ℝ (Fin n))).flip
        (originalCanonicalEntropyEuclidean γ hs) x := by
  rw [polytopeToricReference_coe]
  change (⨆ m : Fin n → ℝ,
      ((originalCoordinatePairing n m (EuclideanSpace.equiv (Fin n) ℝ x) : ℝ) : EReal) -
        originalCanonicalEntropy γ hs m) =
    ⨆ m : EuclideanSpace ℝ (Fin n),
      (((innerₗ (EuclideanSpace ℝ (Fin n))).flip m x : ℝ) : EReal) -
        originalCanonicalEntropy γ hs (EuclideanSpace.equiv (Fin n) ℝ m)
  rw [← (EuclideanSpace.equiv (Fin n) ℝ).surjective.iSup_comp]
  congr 1

/-- The profile of the zero potential is `F_0`. -/
theorem polytopeToricProfile_zero :
    polytopeToricProfile γ hs (fun _ => (0 : EReal)) =
      fun x => (polytopeToricReference γ hs x : EReal) := by
  funext x
  simp [polytopeToricProfile]

/-- `G_0` is the facet entropy of `eq:G0def` (Euclidean model). -/
theorem polytopeToricLegendre_zero :
    polytopeToricLegendre γ hs (fun _ => (0 : EReal)) = originalCanonicalEntropyEuclidean γ hs := by
  unfold polytopeToricLegendre
  rw [polytopeToricProfile_zero]
  have h : (fun x => (polytopeToricReference γ hs x : EReal)) =
      conjugate (innerₗ (EuclideanSpace ℝ (Fin n))).flip (originalCanonicalEntropyEuclidean γ hs) :=
    funext (polytopeToricReference_eq_conjugate γ hs)
  rw [h]
  have hb := biconjugate_eq_convexClosure_of_isContPerfPair
    (innerₗ (EuclideanSpace ℝ (Fin n))).flip (f := originalCanonicalEntropyEuclidean γ hs)
    (isConvex_of_isClosedConvex (isClosedConvex_originalCanonicalEntropyEuclidean γ hs))
  rw [LinearMap.flip_flip] at hb
  rw [hb]
  exact convexClosure_eq_self_of_isClosedConvex
    (isClosedConvex_originalCanonicalEntropyEuclidean γ hs)

/-- Source `ex:toric-ample:L621`: `Δ(ω, 0) = P`. -/
theorem polytopeToricNewtonBody_zero :
    polytopeToricNewtonBody γ hs (fun _ => (0 : EReal)) = polytopeToricMomentPolytope γ := by
  rw [polytopeToricNewtonBody, convexNewtonBody, polytopeToricLegendre_zero,
    effectiveDomain_originalCanonicalEntropyEuclidean]
  exact (isCompact_polytopeToricMomentPolytope γ).isClosed.closure_eq

end SGPT.Toric
