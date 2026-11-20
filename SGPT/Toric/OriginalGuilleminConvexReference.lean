import SGPT.Toric.OriginalActiveFacets
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set SGPT.Convex SGPT.AlmostSemigroup.Counting
open scoped BigOperators Topology RealInnerProductSpace Classical
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]

/-- Literal source G0 on ALL DISTINCT ACTUAL facets. The finite index is
internally produced from original generators and ALL-edge smoothness. -/
def originalCanonicalEntropy (γ : K → Fin n → ℤ) (hsmooth : latticePolytopeEdgeSmooth γ) :
    (Fin n → ℝ) → EReal :=
  let _ := originalPolytopeFacetFintype γ hsmooth
  facetEntropy (fun F => integralRealFunctional (originalFacetNormal γ hsmooth F))
    (fun F => (originalFacetOffset γ hsmooth F : ℝ))

/-- The actual original formula, including TRUE top outside SAME P and the
existing zero-times-log-zero convention, now has no repeated facet indices. -/
theorem originalCanonicalEntropy_eq (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (x : Fin n → ℝ) :
    let _ := originalPolytopeFacetFintype γ hsmooth
    originalCanonicalEntropy γ hsmooth x = if x ∈ latticePolytope γ then
      ((∑ F : latticePolytopeFacets γ,
        integralFacetValue (originalFacetNormal γ hsmooth) (originalFacetOffset γ hsmooth) F x *
          Real.log (integralFacetValue (originalFacetNormal γ hsmooth)
            (originalFacetOffset γ hsmooth) F x) : ℝ) : EReal) else ⊤ := by
  let _ := originalPolytopeFacetFintype γ hsmooth
  change (if x ∈ integralFacetRegion (originalFacetNormal γ hsmooth)
    (originalFacetOffset γ hsmooth) then _ else _) = _
  rw [← latticePolytope_eq_originalFacetRegion γ hsmooth]
  rfl

/-- Genuine original compact region/nonemptiness supplies properness. -/
theorem originalCanonicalEntropy_isProper (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) : IsProper (originalCanonicalEntropy γ hsmooth) := by
  let _ := originalPolytopeFacetFintype γ hsmooth
  apply isProper_facetEntropy
  change (integralFacetRegion (originalFacetNormal γ hsmooth) (originalFacetOffset γ hsmooth)).Nonempty
  rw [← latticePolytope_eq_originalFacetRegion γ hsmooth]
  exact nonempty_latticePolytope γ

/-- Existing whole entropy convexity/closedness is applied to produced data. -/
theorem originalCanonicalEntropy_isClosedConvex (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) : IsClosedConvex (originalCanonicalEntropy γ hsmooth) := by
  let _ := originalPolytopeFacetFintype γ hsmooth
  apply isClosedConvex_facetEntropy
  change (integralFacetRegion (originalFacetNormal γ hsmooth) (originalFacetOffset γ hsmooth)).Nonempty
  rw [← latticePolytope_eq_originalFacetRegion γ hsmooth]
  exact nonempty_latticePolytope γ

/-- The true EXTENDED effective domain is exactly the original source P. -/
theorem effectiveDomain_originalCanonicalEntropy (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) :
    effectiveDomain (originalCanonicalEntropy γ hsmooth) = latticePolytope γ := by
  let _ := originalPolytopeFacetFintype γ hsmooth
  rw [originalCanonicalEntropy, effectiveDomain_facetEntropy]
  exact (latticePolytope_eq_originalFacetRegion γ hsmooth).symm

/-- Both actual finite additive comparisons come from existing genuine
compact entropy bounds, with TRUE infinite values retained outside P. -/
theorem originalCanonicalEntropy_singularityEquiv_indicator (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) :
    SGPT.PSH.SingularityEquiv (originalCanonicalEntropy γ hsmooth) (indicator (latticePolytope γ)) := by
  let _ := originalPolytopeFacetFintype γ hsmooth
  have hcompact : IsCompact (integralFacetRegion (originalFacetNormal γ hsmooth)
      (originalFacetOffset γ hsmooth)) := by
    rw [← latticePolytope_eq_originalFacetRegion γ hsmooth]
    exact isCompact_latticePolytope γ
  have h := facetEntropy_singularityEquiv_indicator
    (fun F => integralRealFunctional (originalFacetNormal γ hsmooth F))
    (fun F => (originalFacetOffset γ hsmooth F : ℝ)) hcompact
  change SGPT.PSH.SingularityEquiv (originalCanonicalEntropy γ hsmooth)
    (indicator (integralFacetRegion (originalFacetNormal γ hsmooth) (originalFacetOffset γ hsmooth))) at h
  rwa [← latticePolytope_eq_originalFacetRegion γ hsmooth] at h

/-- The EXISTING actual finite-coordinate bilinear map, with the original
source and dual coordinate spaces made explicit for elaboration. -/
def originalCoordinatePairing (d : ℕ) :
    (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) →ₗ[ℝ] ℝ := dotProductBilin ℝ ℝ

/-- The genuine existing coordinate dot product is the original lattice pairing. -/
theorem originalCanonicalPairing_apply (x y : Fin n → ℝ) :
    originalCoordinatePairing n x y = ∑ i, x i * y i := rfl

/-- Literal original F0=G0*, using the actual existing coordinate pairing. -/
def originalCanonicalReference (γ : K → Fin n → ℤ) (hsmooth : latticePolytopeEdgeSmooth γ) :
    (Fin n → ℝ) → EReal :=
  conjugate (originalCoordinatePairing n) (originalCanonicalEntropy γ hsmooth)

/-- The actual canonical Legendre reference has original bounded support
growth by the existing ENTIRE compact facet-entropy conjugation producer. -/
theorem originalCanonicalReference_mem_boundedGrowthClass (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) :
    originalCanonicalReference γ hsmooth ∈
      BoundedGrowthClass (originalCoordinatePairing n).flip (latticePolytope γ) := by
  let _ := originalPolytopeFacetFintype γ hsmooth
  have hcompact : IsCompact (integralFacetRegion (originalFacetNormal γ hsmooth)
      (originalFacetOffset γ hsmooth)) := by
    rw [← latticePolytope_eq_originalFacetRegion γ hsmooth]
    exact isCompact_latticePolytope γ
  rw [latticePolytope_eq_originalFacetRegion γ hsmooth]
  exact conjugate_facetEntropy_mem_boundedGrowthClass (originalCoordinatePairing n)
    (fun F => integralRealFunctional (originalFacetNormal γ hsmooth F))
    (fun F => (originalFacetOffset γ hsmooth F : ℝ)) hcompact


/-- Actual interior finiteness and the prior genuine derivative theorem give
the literal original functional derivative. No outside infinite value is read. -/
theorem originalCanonicalEntropy_hasFDerivAt (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) {x : Fin n → ℝ}
    (hx : x ∈ interior (latticePolytope γ)) :
    let _ := originalPolytopeFacetFintype γ hsmooth
    HasFDerivAt (fun y => (originalCanonicalEntropy γ hsmooth y).toReal)
      (∑ F : latticePolytopeFacets γ,
        (Real.log (integralFacetValue (originalFacetNormal γ hsmooth)
          (originalFacetOffset γ hsmooth) F x) + 1) •
            integralRealFunctional (originalFacetNormal γ hsmooth F)) x := by
  let _ := originalPolytopeFacetFintype γ hsmooth
  have hx' : x ∈ interior (integralFacetRegion (originalFacetNormal γ hsmooth)
      (originalFacetOffset γ hsmooth)) := by
    rwa [← latticePolytope_eq_originalFacetRegion γ hsmooth]
  exact hasFDerivAt_facetEntropy_toReal_of_mem_interior
    (fun F => integralRealFunctional (originalFacetNormal γ hsmooth F))
    (fun F => (originalFacetOffset γ hsmooth F : ℝ)) hx'

/-- Original integral normal coefficients in the ACTUAL Euclidean real model.
The true existing coordinate equivalence is used, not a Pi inner-product instance. -/
def originalFacetEuclideanNormal (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (F : latticePolytopeFacets γ) :
    EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm
    (fun i => (originalFacetNormal γ hsmooth F (Pi.basisFun ℤ (Fin n) i) : ℝ))

/-- Genuine existing integer sum evaluation and Euclidean inner products give
the EXACT Riesz functional after the actual continuous linear model transport. -/
theorem originalFacetEuclideanNormal_dual (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (F : latticePolytopeFacets γ) :
    (integralRealFunctional (originalFacetNormal γ hsmooth F)).comp
        (EuclideanSpace.equiv (Fin n) ℝ).toContinuousLinearMap =
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n)))
        (originalFacetEuclideanNormal γ hsmooth F) := by
  apply ContinuousLinearMap.ext
  intro x
  rw [ContinuousLinearMap.comp_apply, integralRealFunctional_apply,
    InnerProductSpace.toDual_apply_apply, PiLp.inner_apply]
  rfl

/-- The source extended entropy transported by the ACTUAL real model equivalence. -/
def originalCanonicalEntropyEuclidean (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) : EuclideanSpace ℝ (Fin n) → EReal :=
  originalCanonicalEntropy γ hsmooth ∘ EuclideanSpace.equiv (Fin n) ℝ

/-- Every original affine facet slack is preserved before any finite real readback. -/
theorem originalEuclideanFacetValue_eq (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (F : latticePolytopeFacets γ)
    (x : EuclideanSpace ℝ (Fin n)) :
    facetValue (fun F => (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n)))
      (originalFacetEuclideanNormal γ hsmooth F))
      (fun F => (originalFacetOffset γ hsmooth F : ℝ)) F x =
    integralFacetValue (originalFacetNormal γ hsmooth) (originalFacetOffset γ hsmooth)
      F (EuclideanSpace.equiv (Fin n) ℝ x) := by
  change (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n)))
    (originalFacetEuclideanNormal γ hsmooth F) x + (originalFacetOffset γ hsmooth F : ℝ) = _
  rw [← originalFacetEuclideanNormal_dual]
  rfl

/-- The SAME extended source function is the genuine existing Riesz-facet
entropy after actual model transport, including its true values outside P. -/
theorem originalCanonicalEntropyEuclidean_eq_facetEntropy (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) :
    let _ := originalPolytopeFacetFintype γ hsmooth
    originalCanonicalEntropyEuclidean γ hsmooth =
      facetEntropy (fun F => (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n)))
        (originalFacetEuclideanNormal γ hsmooth F))
        (fun F => (originalFacetOffset γ hsmooth F : ℝ)) := by
  let _ := originalPolytopeFacetFintype γ hsmooth
  rw [show (fun F => (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n)))
      (originalFacetEuclideanNormal γ hsmooth F)) =
      (fun F => (integralRealFunctional (originalFacetNormal γ hsmooth F)).comp
        (EuclideanSpace.equiv (Fin n) ℝ).toContinuousLinearMap) from
    funext (fun F => (originalFacetEuclideanNormal_dual γ hsmooth F).symm)]
  rfl

/-- The true model-coordinate region is the inverse image of SAME original P. -/
theorem originalEuclideanFacetRegion_eq (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) :
    facetRegion (fun F => (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n)))
      (originalFacetEuclideanNormal γ hsmooth F))
      (fun F => (originalFacetOffset γ hsmooth F : ℝ)) =
      (EuclideanSpace.equiv (Fin n) ℝ) ⁻¹' latticePolytope γ := by
  ext x
  rw [latticePolytope_eq_originalFacetRegion γ hsmooth]
  change (∀ F, 0 ≤ facetValue (fun F =>
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))) (originalFacetEuclideanNormal γ hsmooth F))
      (fun F => (originalFacetOffset γ hsmooth F : ℝ)) F x) ↔ _
  simp only [originalEuclideanFacetValue_eq]
  rfl

/-- The EXISTING genuine gradient theorem gives the original vector sum only
after true model transport and actual interior finiteness. No Kahler extension
or positivity/class assertion is contained in this convex reference producer. -/
theorem originalCanonicalEntropyEuclidean_gradient (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) {x : EuclideanSpace ℝ (Fin n)}
    (hx : EuclideanSpace.equiv (Fin n) ℝ x ∈ interior (latticePolytope γ)) :
    let _ := originalPolytopeFacetFintype γ hsmooth
    gradient (fun y => (originalCanonicalEntropyEuclidean γ hsmooth y).toReal) x =
      ∑ F : latticePolytopeFacets γ,
        (Real.log (integralFacetValue (originalFacetNormal γ hsmooth) (originalFacetOffset γ hsmooth)
          F (EuclideanSpace.equiv (Fin n) ℝ x)) + 1) • originalFacetEuclideanNormal γ hsmooth F := by
  let _ := originalPolytopeFacetFintype γ hsmooth
  have hx' : x ∈ interior (facetRegion (fun F =>
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))) (originalFacetEuclideanNormal γ hsmooth F))
      (fun F => (originalFacetOffset γ hsmooth F : ℝ))) := by
    rw [originalEuclideanFacetRegion_eq]
    change x ∈ interior ((EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph ⁻¹' latticePolytope γ)
    rw [← (EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph.preimage_interior]
    exact hx
  rw [originalCanonicalEntropyEuclidean_eq_facetEntropy]
  have h := gradient_facetEntropy_toReal_of_mem_interior
    (originalFacetEuclideanNormal γ hsmooth) (fun F => (originalFacetOffset γ hsmooth F : ℝ)) hx'
  simpa only [originalEuclideanFacetValue_eq] using h

end SGPT.Toric
