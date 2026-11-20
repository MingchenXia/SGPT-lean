import SGPT.Unibranch.OriginalLocalCanonicalResolutionCover
import SGPT.Unibranch.EmbeddedBlowupOverlap

/-!
# Full original base overlaps preserve each regular dimension

The original base-overlap engine is held. This consumer internally supplies
its exact original singular traces and proves every-dimensional regular
transport on the SAME full native isomorphism, for unequal ambient dimensions.
It does not compare independent canonical histories or strict endpoints.

Blueprint FIRST: `original-local-canonical-base-overlap.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace SGPT.Unibranch.OriginalLocalCanonicalBaseOverlap

noncomputable section

open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
  HironakaIntrinsicComplexAnalyticRegularLocus HironakaEmbeddedAnalytic
  SourceReducedComplexSpace OriginalLocalCanonicalStrictResolution

variable {X : SourceReducedComplexSpace}

/-- The native original-window dictionary retains each literal regular
dimension, not only the union of the regular loci. -/
theorem windowRegularAtDim_iff (e : LocalEmbedding X) (U : Opens e.ambient)
    (v : windowCarrier e U) (d : ℕ) :
    RegularAtDim (n := e.dim) (windowCarrier e U) v.val d ↔
      intrinsicRegularAtDim X.obj ((windowMorphism e U).hom.left.base v) d :=
  AnalyticSubsetOpens.regularAtDim_preimage_val_iff.trans
    (OriginalIntrinsicSingularLocus.intrinsicRegularAtDim_localEmbedding_iff
      X e ⟨v.val.val, v.property⟩ d).symm

/-- Arbitrary original embeddings internally produce their actual native
base-overlap iso with exact original singular and every-dimensional regular
traces. No ambient dimension equality or caller trace/comparison is input. -/
theorem exists_original_base_overlap_regular_trace (e f : LocalEmbedding X) :
    ∃ (O : Opens e.ambient) (P : Opens f.ambient)
      (_hO : (Subtype.val : e.carrier → e.ambient) ⁻¹' (O : Set e.ambient) =
        (EmbeddedBlowupOverlap.overlapOpen e f : Set e.carrier))
      (_hP : (Subtype.val : f.carrier → f.ambient) ⁻¹' (P : Set f.ambient) =
        (EmbeddedBlowupOverlap.overlapOpen f e : Set f.carrier))
      (E : windowSpace e O ≅ windowSpace f P),
      E.hom ≫ windowMorphism f P = windowMorphism e O ∧
      (∀ (v : windowCarrier e O) (d : ℕ),
        RegularAtDim (n := e.dim) (windowCarrier e O) v.val d ↔
          RegularAtDim (n := f.dim) (windowCarrier f P) (E.hom.hom.left.base v).val d) ∧
      (∀ v : windowCarrier e O,
        v.val ∈ singularSet (n := e.dim) (windowCarrier e O) ↔
          (E.hom.hom.left.base v).val ∈ singularSet (n := f.dim) (windowCarrier f P)) := by
  have he : ∀ v : e.carrier,
      v.val ∈ singularSet (n := e.dim) e.carrier ↔
        e.toPoint v ∈ intrinsicSingularLocus X.obj := fun v =>
    (Set.ext_iff.mp
      (OriginalIntrinsicSingularLocus.intrinsicSingularLocus_localEmbedding_preimage X e) v).symm
  have hf : ∀ v : f.carrier,
      v.val ∈ singularSet (n := f.dim) f.carrier ↔
        f.toPoint v ∈ intrinsicSingularLocus X.obj := fun v =>
    (Set.ext_iff.mp
      (OriginalIntrinsicSingularLocus.intrinsicSingularLocus_localEmbedding_preimage X f) v).symm
  obtain ⟨O, P, hO, hP, E, hE, hSing⟩ := EmbeddedBlowupOverlap.exists_base_overlap_iso e f he hf
  have hE' : E.hom ≫ windowMorphism f P = windowMorphism e O := hE
  refine ⟨O, P, hO, hP, E, hE', ?_, ?_⟩
  · intro v d
    have hp : (windowMorphism f P).hom.left.base (E.hom.hom.left.base v) =
        (windowMorphism e O).hom.left.base v :=
      congrArg (fun F => F.hom.left.base v) hE'
    rw [windowRegularAtDim_iff, windowRegularAtDim_iff]
    exact iff_of_eq (congrArg (fun z : X.obj.left => intrinsicRegularAtDim X.obj z d) hp).symm
  · intro v
    rw [HironakaResolutionSpaceLocal.singularSet_preimage_val O,
      HironakaResolutionSpaceLocal.singularSet_preimage_val P]
    exact hSing v

end
end SGPT.Unibranch.OriginalLocalCanonicalBaseOverlap
