import SGPT.PSH.AtlasLogRangeScalar

/-! Genuine full native prime extension across an actual clopen inclusion. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas.SourceLogReverseDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open scoped Topology Manifold ContDiff
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- A genuine prime on an ACTUAL clopen open has a genuine ambient prime
with its SAME ENTIRE literal carrier image. Actual closed inclusion,
analyticity, irreducibility and regular codimension are all constructed. -/
theorem exists_prime_of_clopen_image (U : Opens M) (hU : IsClopen (U : Set M))
    (P : GeometricPrimeCarrier n U) :
    ∃ Q : GeometricPrimeCarrier n M,Q.val=(Subtype.val : U → M) '' P.val := by
  have hc : IsClosed ((Subtype.val : U → M) '' P.val) := hU.isClosed.isClosedMap_subtype_val _ P.isClosed
  have ha : IsComplexAnalyticSubset (n := n) ((Subtype.val : U → M) '' P.val) := by
    apply AnalyticSubsetOpens.isComplexAnalyticSubset_image_val _ hc
    rw [←P.subvariety_carrier]
    exact P.subvariety.analytic
  have hirr : IsComplexAnalyticallyIrreducible (n := n) ((Subtype.val : U → M) '' P.val) := by
    have h := holomorphic_analytic_image_irreducible
      (contMDiff_subtype_val : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
        (Subtype.val : U → M)) P.subvariety (by rwa [P.subvariety_carrier])
    rwa [P.subvariety_carrier] at h
  obtain ⟨q,hq⟩ := P.subvariety.regularLocus_nonempty
  have hreg : RegularAtDim (n := n) ((Subtype.val : U → M) '' P.val) q.val P.subvariety.dim := by
    apply AnalyticSubsetOpens.regularAtDim_image_val_iff.mpr
    rwa [←P.subvariety_carrier]
  refine ⟨⟨_,⟨{
    carrier := (Subtype.val : U → M) '' P.val
    isClosed_carrier := hc
    irreducible_carrier := hirr
    dim := P.subvariety.dim
    dim_le := P.subvariety.dim_le
    regularLocus_nonempty := ⟨q.val,hreg⟩ },rfl,P.subvariety_codimension⟩⟩,rfl⟩

end SGPT.PSH.VariableComplexAtlas.SourceLogReverseDraft
