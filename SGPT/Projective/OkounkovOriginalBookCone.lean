import SGPT.Projective.OkounkovOriginalValuationGeneration
import SGPT.Projective.OkounkovOriginalSectionGrowth
import SGPT.Projective.OkounkovFiniteZeroSlice
import SGPT.Projective.OkounkovOriginalBodyCone
import SGPT.GAGA.SmoothFlagsScheme
import SGPT.Okounkov.ValGenBodies

/-! Source prop:Okounbiglbdl for ANY original surjective valuation, with no cone/flag premise.
Blueprint: okounkov-original-book-cone.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalBook
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter MeasureTheory
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov SGPT.Okounkov.AlgebraicValuation SGPT.AlmostSemigroup
open SGPT.AlmostSemigroup.Okounkov SGPT.AlmostSemigroup.Class
open SGPT.Okounkov.BodyFromGrowth
open scoped Topology
variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))
  (E : ClosedProjectiveEmbedding f) {m : ℕ} [SmoothOfRelativeDimension (m+1) f]
  [Nonempty (SchemeComplexPoint f)]
local instance : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance : ChartedSpace (ComplexModel (m+1)) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f (m+1)
local instance [IsSeparated f] [QuasiCompact f] : IsComplexManifold (m+1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m+1)
variable {L : X.Modules} (a : LineBundleAtlas L) (hbig : SGPT.LineBundle.IsBig f L (m+1))
  (v : AddValuation X.functionField (WithTop (Lex (Fin (m+1) → ℤ))))
  (hv : Function.Surjective v) (c : X)

include f E hbig hv

/-- Actual ORIGINAL source cone and full original lattice, for arbitrary original surjective valuation. -/
theorem exists_original_admissibleCone_of_surjective :
    ∃ C : AdmissibleCone (m+1),
      sectionSemigroup v c a ≤ latticePoints C.cone ∧
      LatticeSlices.generatedGroup (sectionSemigroup v c a) = ⊤ := by
  obtain ⟨Y,hY⟩ := SGPT.GAGA.SmoothFlags.smoothFlagsExist X f E m
  have hG := OriginalRationalPairs.generatedGroup_sectionSemigroup_eq_top_of_surjective
    f E Y hY a hbig v hv c
  have hfinite (k : ℤ) := original_sectionSemigroup_slice_finite f (m+1) E a c v k
  have hpositive := positiveHeight_of_nonnegative_finiteZeroSlice (sectionSemigroup v c a)
    (sectionSemigroup_degree_nonneg (v:=v) c a) (hfinite 0)
  obtain ⟨B,hB,hcount⟩ := exists_original_sectionSemigroup_card_le_pow f (m+1) E a c v Y hY
  obtain ⟨C,hC⟩ := exists_admissibleCone_of_polynomial_growth (sectionSemigroup v c a)
    hpositive hG (fun k => hfinite (k:ℤ)) B hB hcount
  exact ⟨C,hC,hG⟩

/-- ENTIRE source prop:Okounbiglbdl in positive dimension, with SAME existing body and full locus. -/
theorem sectionSemigroup_mem_ownBody_fullSemigroupLocus_of_surjective :
    ∃ (hKc : IsCompact (okounkovBody v c a)) (hKv : Convex ℝ (okounkovBody v c a)),
      (interior (okounkovBody v c a)).Nonempty ∧
      ∃ hS : sectionSemigroup v c a ≤
          latticePoints (SGPT.GAGA.OkoClose.coneOver _ hKc hKv).cone,
        sourceSubset (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) (sectionSemigroup v c a) hS ∈
          fullSemigroupLocus (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) := by
  obtain ⟨C,hC,hG⟩ := exists_original_admissibleCone_of_surjective f E a hbig v hv c
  obtain ⟨hKc,hKv,hS⟩ := ValGen.le_latticePoints_coneOver C (sectionSemigroup v c a) hC hG
  exact ⟨hKc,hKv,BodyGeometry.interior_body_nonempty C _ hC hG,hS,
    sourceSubset_mem_fullSemigroupLocus _ _ hS hG⟩

end SGPT.Okounkov.OriginalBook
