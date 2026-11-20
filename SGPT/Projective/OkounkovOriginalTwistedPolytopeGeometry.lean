import SGPT.Projective.OkounkovOriginalBookTwisted

/-! True original raw twisted-value finiteness/compactness, with all geometric inputs produced.
Blueprint: okounkov-original-twisted-polytope-geometry.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalBook
open Set Filter CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open scoped Topology
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov.AlgebraicValuation SGPT.Okounkov.ValGen2
open SGPT.AlmostSemigroup SGPT.AlmostSemigroup.Okounkov

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)
  [Nonempty (SchemeComplexPoint f)] {L : X.Modules} (a : LineBundleAtlas L)
  (hbig : SGPT.LineBundle.IsBig f L n)
  (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ))))
  (hv : Function.Surjective v) (c : X) (hc : IsNonnegAt v c)

local instance twistedGeometryTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance twistedGeometryCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance twistedGeometryManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

include f E a hbig hv hc in
/-- Actual ALL-degree original twisted values finite, no source cone/group/flag certificate input. -/
theorem original_twistedValues_finite_allDimensions {T : X.Modules} (aT : LineBundleAtlas T)
    (m : ℕ) (r : LineBundleAtlas (bundleTensor T (bundleTensorPower L m))) :
    (AlgebraicValuation.twistedValues v c m r).Finite := by
  cases n with
  | zero => exact Set.toFinite _
  | succ l =>
    obtain ⟨Y,hY⟩ := exists_original_smoothFlag_allDimensions f (l+1) E
    obtain ⟨C,hS,hG⟩ := exists_original_admissibleCone_allDimensions f a (l+1) E hbig v hv c
    obtain ⟨k₀,t,ht⟩ := (exists_twisted_section_ne_zero f E Y hY a hbig hbig.volume_pos (dualAtlas aT)).exists
    let rD := pairwiseTensorAtlas (dualAtlas aT) (a.tensorPower k₀)
    let w := plainSectionVector v c rD t ht
    have himage : (fun x : Fin (l+1) → ℤ => x+w) '' (AlgebraicValuation.twistedValues v c m r) ⊆
        slice (sectionSemigroup v c a : Set ((Fin (l+1) → ℤ) × ℤ)) ((m+k₀:ℕ):ℤ) := by
      rintro _ ⟨x,⟨s,hs,hx⟩,rfl⟩
      obtain ⟨hst,hval⟩ := upperProduct_vector a aT v hc m k₀ r rD hs ht
      exact ⟨m+k₀,upperProduct a aT m k₀ s t,hst,Prod.ext ((congrArg (fun z => z+w) hx).trans hval.symm) rfl⟩
    exact ((finite_source_slice C (sectionSemigroup v c a) hS ((m+k₀:ℕ):ℤ)).subset himage).of_finite_image
      (fun _ _ _ _ h => add_right_cancel h)

include f E a hbig hv hc in
/-- Exact original raw twisted degree polytopes are compact in the SAME Euclidean coordinates, all dimensions/degrees. -/
theorem original_twistedDegreePolytope_isCompact_allDimensions {T : X.Modules} (aT : LineBundleAtlas T)
    (m : ℕ) (r : LineBundleAtlas (bundleTensor T (bundleTensorPower L m))) :
    IsCompact ((EuclideanSpace.equiv (Fin n) ℝ).symm '' AlgebraicValuation.twistedDegreePolytope v c m r) := by
  have hfin := original_twistedValues_finite_allDimensions f n E a hbig v hv c hc aT m r
  exact ((hfin.image (fun x => (m:ℝ)⁻¹ • SGPT.AlmostSemigroup.Counting.integerCast x)).isCompact_convexHull ℝ).image
    (EuclideanSpace.equiv (Fin n) ℝ).symm.continuous

end SGPT.Okounkov.OriginalBook
