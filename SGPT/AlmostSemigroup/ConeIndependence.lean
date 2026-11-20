import SGPT.AlmostSemigroup.OkounkovExtension

noncomputable section
namespace SGPT.AlmostSemigroup.ConeIndependence
open Set Filter
open scoped Topology
open Class OkounkovExtension

variable {n : ℕ} {C D : AdmissibleCone n}
variable (hCD : (C.cone : Set ((Fin n → ℝ) × ℝ)) ⊆ D.cone)

/-- Actual lattice-subset inclusion under a genuine admissible ambient-cone enlargement. -/
def includeSubset (S : ConeSubset C) : ConeSubset D :=
  ⟨S.val, fun _ hz ↦ hCD (S.property hz)⟩

/-- Every actual original finite degree slice is unchanged by ambient-cone enlargement. -/
theorem slices_includeSubset (S : ConeSubset C) (k : ℕ) :
    (includeSubset hCD S).slices k = S.slices k := by
  ext x
  simp only [ConeSubset.mem_slices]
  rfl

/-- The exact original source normalized-cardinality volume is unchanged. -/
theorem volume_includeSubset (S : ConeSubset C) :
    (includeSubset hCD S).volume = S.volume := by
  unfold ConeSubset.volume ConeSubset.normalizedCardinality
  simp only [slices_includeSubset]

/-- Actual ambient-cone enlargement preserves the original source pseudometric exactly. -/
theorem isometry_includeSubset : Isometry (includeSubset hCD) := by
  apply Isometry.of_dist_eq
  intro S T
  change ConeSubset.distance (includeSubset hCD S) (includeSubset hCD T) = ConeSubset.distance S T
  unfold ConeSubset.distance
  congr 1

/-- Genuine additive closure and genuine full generated group use the unchanged original carrier. -/
theorem includeSubset_mem_fullSemigroupLocus {S : ConeSubset C}
    (hS : S ∈ fullSemigroupLocus C) : includeSubset hCD S ∈ fullSemigroupLocus D := hS

/-- The genuine original full-source inclusion into the larger-cone full-source locus. -/
def includeFull (S : FullSemigroup C) : FullSemigroup D :=
  ⟨includeSubset hCD S.val, includeSubset_mem_fullSemigroupLocus hCD S.property⟩

/-- Actual continuous inclusion maps the genuine full-source closure into the larger full-source closure, preserving positivity. -/
theorem includeSubset_mem_almostSemigroupLocus {S : ConeSubset C}
    (hS : S ∈ almostSemigroupLocus C) : includeSubset hCD S ∈ almostSemigroupLocus D := by
  refine ⟨?_, ?_⟩
  · have him : includeSubset hCD S ∈ closure (includeSubset hCD '' fullSemigroupLocus C) :=
      mem_closure_image (isometry_includeSubset hCD).continuous.continuousAt hS.1
    apply closure_mono (t := fullSemigroupLocus D) _ him
    rintro _ ⟨T, hT, rfl⟩
    exact includeSubset_mem_fullSemigroupLocus hCD hT
  · change 0 < (includeSubset hCD S).volume
    rw [volume_includeSubset]
    exact hS.2

/-- Actual original almost-semigroup inclusion under ambient-cone enlargement. -/
def includeAlmost (S : AlmostSpace C) : AlmostSpace D :=
  ⟨includeSubset hCD S.val, includeSubset_mem_almostSemigroupLocus hCD S.property⟩

theorem isometry_includeAlmost : Isometry (includeAlmost hCD) := by
  apply Isometry.of_dist_eq
  intro S T
  exact (isometry_includeSubset hCD).dist_eq S.val T.val

/-- The genuine source inclusion square commutes with the actual cone inclusion. -/
theorem includeAlmost_fullToAlmost (S : FullSemigroup C) :
    includeAlmost hCD (fullToAlmost S) = fullToAlmost (includeFull hCD S) := rfl

/-- The actual generated-body carrier does not depend on ambient membership proofs. -/
theorem bodyMap_includeFull (S : FullSemigroup C) : bodyMap (includeFull hCD S) = bodyMap S := by
  apply ConvexBody.ext
  rfl

/-- Exact source rmk:almostsg:L542: the larger-cone actual extension agrees on every original almost semigroup. -/
theorem bodyExtension_includeAlmost (S : AlmostSpace C) :
    bodyExtension (includeAlmost hCD S) = bodyExtension S := by
  have heq := continuous_extension_unique
    (fun T : AlmostSpace C ↦ bodyExtension (includeAlmost hCD T))
    (bodyExtension (C := C))
    ((continuous_bodyExtension D).comp (isometry_includeAlmost hCD).continuous)
    (continuous_bodyExtension C) ?_ bodyExtension_source
  · exact congrFun heq S
  · intro T
    rw [includeAlmost_fullToAlmost, bodyExtension_source, bodyMap_includeFull]

end SGPT.AlmostSemigroup.ConeIndependence
