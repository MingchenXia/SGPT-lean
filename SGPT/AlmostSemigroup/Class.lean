import SGPT.AlmostSemigroup.Decreasing
import Mathlib.Analysis.Convex.Body
import Mathlib.Topology.MetricSpace.Basic

/-!
# Actual full source locus, positive closure and metric classes

The almost-semigroup locus is the source's positive-volume closure. Its members
need not themselves be additively closed. The actual source body descends to
distance-zero classes, and genuine density yields uniqueness of an extension.
The existence and continuity of that extension are separate obligations.
-/

noncomputable section

namespace SGPT.AlmostSemigroup.Class

open Set Filter
open scoped Topology
open Okounkov

/-- SGPT `def:almostsg:L284`: actual additive closure and actual full ambient group generation. -/
def fullSemigroupLocus {n : ℕ} (C : AdmissibleCone n) : Set (ConeSubset C) :=
  {S | S ∈ ConeSubset.semigroupLocus C ∧
    AddSubgroup.closure S.val = (⊤ : AddSubgroup ((Fin n → ℤ) × ℤ))}

/-- The actual full source locus as a subspace of the original source pseudometric space. -/
def FullSemigroup {n : ℕ} (C : AdmissibleCone n) : Type :=
  {S : ConeSubset C // S ∈ fullSemigroupLocus C}

instance fullSemigroupPseudoMetricSpace {n : ℕ} (C : AdmissibleCone n) :
    PseudoMetricSpace (FullSemigroup C) :=
  inferInstanceAs (PseudoMetricSpace {S : ConeSubset C // S ∈ fullSemigroupLocus C})

namespace FullSemigroup

variable {n : ℕ} {C : AdmissibleCone n}

/-- Actual additive closure gives an actual additive subsemigroup, with exactly the original carrier. -/
def semigroup (S : FullSemigroup C) : AddSubsemigroup ((Fin n → ℤ) × ℤ) where
  carrier := S.val.val
  add_mem' hx hy := S.property.1 _ hx _ hy

theorem semigroup_le_source (S : FullSemigroup C) : S.semigroup ≤ latticePoints C.cone :=
  S.val.property

theorem generatedGroup_eq_top (S : FullSemigroup C) :
    LatticeSlices.generatedGroup S.semigroup = ⊤ := S.property.2

theorem sourceSubset_semigroup (S : FullSemigroup C) :
    sourceSubset C S.semigroup S.semigroup_le_source = S.val := rfl

/-- Original full source members have genuine strictly positive source volume. -/
theorem volume_pos (S : FullSemigroup C) : 0 < S.val.volume := by
  rw [← S.sourceSubset_semigroup]
  exact BodyGeometry.volume_source_pos C S.semigroup S.semigroup_le_source S.generatedGroup_eq_top

end FullSemigroup

/-- Any original actual full semigroup is a member of the exact full source locus. -/
theorem sourceSubset_mem_fullSemigroupLocus {n : ℕ} (C : AdmissibleCone n)
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ)) (hS : S ≤ latticePoints C.cone)
    (hG : LatticeSlices.generatedGroup S = ⊤) : sourceSubset C S hS ∈ fullSemigroupLocus C :=
  ⟨fun _ hx _ hy ↦ S.add_mem hx hy, hG⟩

/-- SGPT `def:SpCbarapp`: actual positive-volume closure of the actual full source locus. -/
def almostSemigroupLocus {n : ℕ} (C : AdmissibleCone n) : Set (ConeSubset C) :=
  closure (fullSemigroupLocus C) ∩ {S | 0 < S.volume}

/-- Actual almost semigroups in the source pseudometric topology, with no imposed additive closure. -/
def AlmostSpace {n : ℕ} (C : AdmissibleCone n) : Type :=
  {S : ConeSubset C // S ∈ almostSemigroupLocus C}

instance almostSpacePseudoMetricSpace {n : ℕ} (C : AdmissibleCone n) :
    PseudoMetricSpace (AlmostSpace C) :=
  inferInstanceAs (PseudoMetricSpace {S : ConeSubset C // S ∈ almostSemigroupLocus C})

/-- Positive closure of the full locus lies in the previously defined actual semigroup closure. -/
theorem almostSemigroupLocus_subset_semigroupClosure {n : ℕ} (C : AdmissibleCone n) :
    almostSemigroupLocus C ⊆ ConeSubset.semigroupClosure C := by
  intro S hS
  exact closure_mono (fun _ h ↦ h.1 : fullSemigroupLocus C ⊆ ConeSubset.semigroupLocus C) hS.1

/-- The genuine source inclusion into its positive closure. -/
def fullToAlmost {n : ℕ} {C : AdmissibleCone n} (S : FullSemigroup C) : AlmostSpace C :=
  ⟨S.val, subset_closure S.property, S.volume_pos⟩

/-- The actual source inclusion preserves the original pseudometric exactly. -/
theorem isometry_fullToAlmost {n : ℕ} (C : AdmissibleCone n) :
    Isometry (fullToAlmost (C := C)) := by
  intro S T
  rfl

/-- The actual full source inclusion has dense range in the actual source almost-semigroup space. -/
theorem denseRange_fullToAlmost {n : ℕ} (C : AdmissibleCone n) :
    DenseRange (fullToAlmost (C := C)) := by
  intro S
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨T, hT, hdist⟩ := Metric.mem_closure_iff.mp S.property.1 ε hε
  exact ⟨fullToAlmost (⟨T, hT⟩ : FullSemigroup C), mem_range_self _, hdist⟩

/-- The actual original source body in genuine Euclidean coordinates and the actual Hausdorff metric. -/
def bodyMap {n : ℕ} {C : AdmissibleCone n} (S : FullSemigroup C) :
    ConvexBody (EuclideanSpace ℝ (Fin n)) where
  carrier := BodyGeometry.euclideanBody S.semigroup
  convex' := (convex_body S.semigroup).linear_image
    (EuclideanSpace.equiv (Fin n) ℝ).symm.toLinearMap
  isCompact' := (isCompact_body C S.semigroup S.semigroup_le_source
    (nonempty_of_generatedGroup_eq_top _ S.generatedGroup_eq_top)).image
      (EuclideanSpace.equiv (Fin n) ℝ).symm.continuous
  nonempty' := BodyGeometry.euclideanBody_nonempty C S.semigroup
    S.semigroup_le_source S.generatedGroup_eq_top

/-- Actual source body rigidity makes the actual Euclidean body map constant on distance-zero classes. -/
theorem bodyMap_eq_of_dist_eq_zero {n : ℕ} {C : AdmissibleCone n}
    (S T : FullSemigroup C) (hzero : dist S T = 0) : bodyMap S = bodyMap T := by
  have hzero' : dist (sourceSubset C S.semigroup S.semigroup_le_source)
      (sourceSubset C T.semigroup T.semigroup_le_source) = 0 := hzero
  have heq := Intersection.body_eq_of_distance_eq_zero C S.semigroup T.semigroup
    S.semigroup_le_source T.semigroup_le_source S.generatedGroup_eq_top T.generatedGroup_eq_top hzero'
  apply ConvexBody.ext
  exact congrArg (fun K ↦ (EuclideanSpace.equiv (Fin n) ℝ).symm '' K) heq

/-- The actual body map on the genuine metric separation quotient of the source full locus. -/
def bodyMapOnClasses {n : ℕ} {C : AdmissibleCone n} :
    SeparationQuotient (FullSemigroup C) → ConvexBody (EuclideanSpace ℝ (Fin n)) :=
  SeparationQuotient.lift bodyMap
    (fun S T h ↦ bodyMap_eq_of_dist_eq_zero S T (Metric.inseparable_iff.mp h))

theorem bodyMapOnClasses_mk {n : ℕ} {C : AdmissibleCone n} (S : FullSemigroup C) :
    bodyMapOnClasses (SeparationQuotient.mk S) = bodyMap S := rfl

/-- The uniqueness clause of SGPT `thm:Okocontapp` follows genuine density and the true Euclidean target. -/
theorem continuous_extension_unique {n : ℕ} {C : AdmissibleCone n}
    (F G : AlmostSpace C → ConvexBody (EuclideanSpace ℝ (Fin n)))
    (hF : Continuous F) (hG : Continuous G)
    (hFsource : ∀ S : FullSemigroup C, F (fullToAlmost S) = bodyMap S)
    (hGsource : ∀ S : FullSemigroup C, G (fullToAlmost S) = bodyMap S) : F = G := by
  apply (denseRange_fullToAlmost C).equalizer hF hG
  funext S
  exact (hFsource S).trans (hGsource S).symm

end SGPT.AlmostSemigroup.Class
