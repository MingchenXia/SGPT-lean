import SGPT.Foundations.Analysis.Pending.AnalyticModificationStrongPullback

set_option autoImplicit false

/-!
# Fibres through unramified points of an analytic modification

For a proper holomorphic modification, every fibre containing an unramified
point is a singleton.  Its differential exceptional locus is consequently
the full preimage of its image, that image is closed, and the map is an
isomorphism over the image complement.  The analytic exceptional witnesses
in the modification definition are used only for empty-interior avoidance
and genuine inverse equations; the resulting exceptional locus is intrinsic.

The separation argument extends `ExceptionalFibres` from a single blowup
to actual analytic modifications.  Demailly, Chapter II, Section 10 and
Xia, Appendix B.1 supply the modification context.  No compactness or finite
blowup factorization is required.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace SGPT.Foundations.Analysis.Pending.AnalyticModificationExceptionalFibres

open FirstPass FirstPass.BlowupSequences AnalyticModificationLocalDiscrepancy

noncomputable section

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {Y : Type u} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- An actual modification has no second point in a fibre containing a
point where its holomorphic differential is bijective. -/
theorem eq_of_apply_eq_of_not_mem_exceptionalLocus
    {g : Y → X} (hg : IsAnalyticModification (n := n) g) {y y' : Y}
    (hy : y ∉ exceptionalLocus n g) (heq : g y' = g y) : y' = y := by
  obtain ⟨A, B, s, _, _, hAi, _, _, _, hpre, _, _, hleft⟩ := hg.2.2
  by_contra hne
  obtain ⟨U', U, hU', hU, hy'U', hyU, hdisj⟩ := t2_separation hne
  have himg : g '' U ∈ 𝓝 (g y) := by
    rw [← StrictTransformComposition.map_nhds_eq_of_not_mem_exceptionalLocus hg.1 hy]
    exact image_mem_map (hU.mem_nhds hyU)
  have hO : IsOpen (U' ∩ g ⁻¹' interior (g '' U)) :=
    hU'.inter (isOpen_interior.preimage hg.1.continuous)
  have hy'O : y' ∈ U' ∩ g ⁻¹' interior (g '' U) :=
    ⟨hy'U', by rw [mem_preimage, heq]; exact mem_interior_iff_mem_nhds.mpr himg⟩
  have hnot : ¬ U' ∩ g ⁻¹' interior (g '' U) ⊆ A := by
    intro hsub
    have h := interior_maximal hsub hO hy'O
    rw [hAi] at h
    exact h
  obtain ⟨z, ⟨hzU', hz⟩, hzA⟩ := not_subset.mp hnot
  obtain ⟨z₁, hz₁U, hz₁⟩ := interior_subset hz
  have hz₁A : z₁ ∉ A := by
    intro hz₁A
    apply hzA
    rw [← hpre] at hz₁A ⊢
    change g z₁ ∈ B at hz₁A
    change g z ∈ B
    rwa [hz₁] at hz₁A
  have heqz : z₁ = z :=
    (hleft z₁ hz₁A).symm.trans ((congrArg s hz₁).trans (hleft z hzA))
  exact disjoint_left.mp hdisj hzU' (heqz ▸ hz₁U)

/-- The intrinsic differential exceptional locus is the full preimage
of its image under the actual modification. -/
theorem preimage_image_exceptionalLocus
    {g : Y → X} (hg : IsAnalyticModification (n := n) g) :
    g ⁻¹' (g '' exceptionalLocus n g) = exceptionalLocus n g := by
  refine Subset.antisymm ?_ (subset_preimage_image _ _)
  rintro y ⟨z, hz, hzy⟩
  by_contra hy
  exact hy (eq_of_apply_eq_of_not_mem_exceptionalLocus hg hy hzy ▸ hz)

/-- Proper closed-image geometry makes the intrinsic exceptional image
closed, without a compactness hypothesis. -/
theorem isClosed_image_exceptionalLocus
    {g : Y → X} (hg : IsAnalyticModification (n := n) g) :
    IsClosed (g '' exceptionalLocus n g) := by
  exact hg.2.1.isClosedMap _
    (isOpen_compl_iff.mp (StrictTransformComposition.isOpen_compl_exceptionalLocus hg.1))

/-- Over the complement of its intrinsic exceptional image, an actual
modification is bijective and unramified. -/
theorem isIsomorphismOver_compl_image_exceptionalLocus
    {g : Y → X} (hg : IsAnalyticModification (n := n) g) :
    IsIsomorphismOver n g (g '' exceptionalLocus n g)ᶜ := by
  have hnonexc {y : Y} (hy : g y ∉ g '' exceptionalLocus n g) :
      y ∉ exceptionalLocus n g := by
    intro hyE
    exact hy ⟨y, hyE, rfl⟩
  refine ⟨⟨fun y hy => hy, ?_, ?_⟩, ?_⟩
  · intro y _ z hz heq
    exact eq_of_apply_eq_of_not_mem_exceptionalLocus hg (hnonexc hz) heq
  · intro x hx
    obtain ⟨y, hy⟩ := AnalyticModificationStrongPullback.surjective_of_isAnalyticModification hg x
    refine ⟨y, ?_, hy⟩
    change g y ∉ g '' exceptionalLocus n g
    rwa [hy]
  · exact disjoint_left.mpr fun y hy hyE => hnonexc hy hyE

end

end SGPT.Foundations.Analysis.Pending.AnalyticModificationExceptionalFibres
