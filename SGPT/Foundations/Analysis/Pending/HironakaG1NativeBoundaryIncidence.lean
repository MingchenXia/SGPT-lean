import SGPT.Foundations.Analysis.Pending.HironakaG1QuotientLabelledBoundaryFrame
import SGPT.Foundations.Analysis.Pending.HironakaG1NativeOldBoundaryFactor
import SGPT.Foundations.Analysis.Pending.HironakaIntrinsicReducedCentreIdealModel

/-!
# Genuine old-member incidence from ENTIRE actual native ideal images

The actual surjective quotient/kernel and the whole reduced-centre model
dictionary reflect ideal inclusion. A genuine internally chosen SNC reader
then detects the actual local centre containment, including absent slots.
No comparison of boundary ideals or future histories is input.

Blueprint FIRST: `hironaka-g1-native-boundary-incidence.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Classical TopologicalSpace CategoryTheory
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.HironakaG1NativeBoundaryIncidence

open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.BlowupSequences BlowupTowers
  NormalCrossings BlowupFlatCoordinates HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaActualAnalyticSubspace HironakaActualIntrinsicLabelledBoundaryIdeals
  HironakaIntrinsicReducedCentreIdealModel HironakaG1QuotientLabelledBoundaryFrame
  HironakaSingularSubspaceBlowupCartier HironakaG1NativeOldBoundaryFactor

noncomputable section

variable {n : ℕ} {M : CMfd.{0} n}

private theorem wholeVanishing_le_of_eventually_subset {A B : Set M} (x : M)
    (hBA : ∀ᶠ y in 𝓝 x, y ∈ B → y ∈ A) :
    actualWholeSheafStalkIdeal (vanishingIdeal (n := n) A) x ≤
      actualWholeSheafStalkIdeal (vanishingIdeal (n := n) B) x := by
  apply Ideal.span_le.mpr
  rintro _ ⟨f, hf, hfm, rfl⟩
  apply Ideal.subset_span
  refine ⟨f, hf, ⟨hf, ?_⟩, rfl⟩
  filter_upwards [hfm.2, hBA] with y hy hyBA hyB
  exact hy (hyBA hyB)

/-- Actual LOCAL containment is equivalent to inclusion of the WHOLE
original Cartier IMAGE into the SAME intrinsic reduced-centre stalk image. -/
theorem local_centre_subset_member_iff_native_image_le {C W : Set M}
    (hCW : C ⊆ W) {E : List (Set M)} (hE : IsSNCDivisor n E)
    (i : Fin E.length) (p : W) :
    (∀ᶠ y in 𝓝 p.val, y ∈ C → y ∈ E.get i) ↔
      actualLabelledBoundaryTraceIdeal W E i p ≤
        LinearMap.range (intrinsicReducedCentreStalkInclusion
          (actualSubspaceLocallyRingedSpace (n := n) W)
          ((Subtype.val : W → M) ⁻¹' C) p) := by
  rw [intrinsicReducedCentreStalkInclusion_range_model hCW p]
  constructor
  · intro hCH
    exact Ideal.map_mono (wholeVanishing_le_of_eventually_subset p.val hCH)
  · intro hle
    let q := ((actualSubspaceInclusion (n := n) W).stalkMap p).hom
    let I := actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) p.val
    have hker : Ideal.comap q ⊥ ≤ I := by
      change RingHom.ker ((actualSubspaceInclusion (n := n) W).stalkMap p).hom ≤ I
      rw [actualSubspaceInclusion_stalk_kernel]
      exact wholeVanishing_le_of_eventually_subset p.val
        (Eventually.of_forall fun _ hy => hCW hy)
    have hreflect : actualWholeSheafStalkIdeal (vanishingIdeal (n := n) (E.get i)) p.val ≤ I := by
      calc
        _ ≤ Ideal.comap q (Ideal.map q
            (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) (E.get i)) p.val)) :=
          Ideal.le_comap_map
        _ ≤ Ideal.comap q (Ideal.map q I) := Ideal.comap_mono hle
        _ = I := by
          rw [Ideal.comap_map_of_surjective q
            (actualSubspaceInclusionRingedHom_stalk_surjective (n := n) W p)]
          exact sup_eq_left.mpr hker
    obtain ⟨Φ, κ, _hsrc, _hzero, _hinj, hEq, _hall⟩ :=
      exists_quotient_labelled_boundary_frame hE p.val
    have hp : p.val ∈ flatDomain Φ := mem_flatDomain_self Φ
    cases hslot : κ i with
    | none =>
      have habs : ∀ y ∈ flatDomain Φ, y ∉ E.get i := by
        intro y hy hyH
        obtain ⟨j, hj, _⟩ := (hEq y hy i).mp hyH
        simp [hslot] at hj
      have hf := holomorphicAt_const (n := n) (x := p.val) (1 : ℂ)
      have hH : (vanishingIdeal (n := n) (E.get i)).mem p.val (fun _ => (1 : ℂ)) := by
        refine ⟨hf, ?_⟩
        filter_upwards [(isOpen_flatDomain Φ).mem_nhds hp] with y hy hyH
        exact (habs y hy hyH).elim
      have hC := (actualOriginalGerm_mem_vanishingIdeal_iff C p.val _ hf).mp
        (hreflect (Ideal.subset_span ⟨fun _ => (1 : ℂ), hf, hH, rfl⟩))
      filter_upwards [hC.2] with y hy hyC
      exact (one_ne_zero (hy hyC)).elim
    | some j =>
      have hflat : ∀ y ∈ flatDomain Φ, y ∈ E.get i ↔ flatCoord Φ j y = 0 := by
        intro y hy
        simpa [hslot] using hEq y hy i
      have hf := holomorphicAt_flatCoord Φ j hp
      have hH : (vanishingIdeal (n := n) (E.get i)).mem p.val (flatCoord Φ j) := by
        refine ⟨hf, ?_⟩
        filter_upwards [(isOpen_flatDomain Φ).mem_nhds hp] with y hy hyH
        exact (hflat y hy).mp hyH
      have hC := (actualOriginalGerm_mem_vanishingIdeal_iff C p.val _ hf).mp
        (hreflect (Ideal.subset_span ⟨flatCoord Φ j, hf, hH, rfl⟩))
      filter_upwards [(isOpen_flatDomain Φ).mem_nhds hp, hC.2] with y hy hyC hCy
      exact (hflat y hy).mpr (hyC hCy)

/-- The actual zero/one exponent is read from the SAME entire native old
and intrinsic centre ideal images, with no incidence packet supplied. -/
theorem centreMemberExponent_eq_native_ite {C W : Set M} (hCW : C ⊆ W)
    {E : List (Set M)} (hE : IsSNCDivisor n E) (i : Fin E.length) (p : W) :
    centreMemberExponent C (E.get i) p.val =
      if actualLabelledBoundaryTraceIdeal W E i p ≤
        LinearMap.range (intrinsicReducedCentreStalkInclusion
          (actualSubspaceLocallyRingedSpace (n := n) W)
          ((Subtype.val : W → M) ⁻¹' C) p) then 1 else 0 := by
  simp only [centreMemberExponent,
    ← local_centre_subset_member_iff_native_image_le hCW hE i p]

end
end SGPT.Foundations.Analysis.Pending.HironakaG1NativeBoundaryIncidence
