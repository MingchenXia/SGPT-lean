import SGPT.Foundations.Analysis.FirstPass.ComplexAnalyticSubvarieties
import SGPT.Foundations.Analysis.FirstPass.RegularLocusDense
import SGPT.Foundations.Analysis.Pending.AnalyticSubsetPreimage
import SGPT.Foundations.Analysis.Pending.ProperMappingTheorem
import Mathlib.Geometry.Manifold.ContMDiff.Basic

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Remmert proper-image theorem (formerly a named input; PROVED)

## Source

R. Remmert, *Projektionen analytischer Mengen*, Math. Ann. **130**
(1956), 410--441; R. Remmert, *Holomorphe und meromorphe Abbildungen
komplexer Räume*, Math. Ann. **133** (1957), 328--370.  See also
H. Grauert--R. Remmert, *Coherent Analytic Sheaves*, Ch. 9, and
P. Griffiths--J. Harris, *Principles of Algebraic Geometry*, Ch. 0, §2.

Remmert's proper mapping theorem says that the image of an analytic set
under a proper holomorphic map is analytic.  In the declaration below,
compactness of the source supplies properness.  Closedness follows separately
from compactness, while irreducibility and a regular-dimension witness are
reconstructed below from the analytic image using the already formalized
preimage and regular-locus results.

PROVED (TN.4 #5): `remmert1956_image_isComplexAnalyticSubset` is no longer a
named input.  It follows from `ProperMappingTheorem.isComplexAnalyticSubset_image`,
the proper mapping theorem proved by Demailly's simultaneous induction with the
Remmert--Stein theorem (*Complex analytic and differential geometry*,
II.8.7--8.8; blueprint `rem:proper-mapping`), not by the coherent-sheaf route of
Remmert's papers cited above.
-/

open Set
open scoped Manifold ContDiff

universe u

namespace SGPT.Foundations.Analysis.Pending.ProperImageAnalytic

open FirstPass

noncomputable section

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]
  {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]

/-- **Remmert's proper mapping theorem, compact source** (Remmert 1956, Satz 17;
Remmert 1957, §4, Satz 23 and its compact-source form Satz 24, p. 356 -- PDF page 30 of
`remmert57-holomorphe-abbildungen`).  The image of an analytic set under a holomorphic map with
compact source is analytic.  This asserts analyticity only: topological
closedness is not used as a substitute for it.  PROVED from
`ProperMappingTheorem.isComplexAnalyticSubset_image` (compactness of `Z` makes
`f` proper on the closed set `W`). -/
theorem remmert1956_image_isComplexAnalyticSubset [CompactSpace Z] {f : Z → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    (W : ClosedIrreducibleAnalyticSubvariety n Z) :
    IsComplexAnalyticSubset (n := n) (f '' W.carrier) := by
  refine ProperMappingTheorem.isComplexAnalyticSubset_image hf W.analytic fun K hK => ?_
  exact (W.isClosed_carrier.inter (hK.isClosed.preimage hf.continuous)).isCompact

/-- Once the image is known to be analytic, analytic preimages transport the
irreducibility of `W` across the surjection onto its image. -/
private theorem image_irreducible_of_isComplexAnalyticSubset {f : Z → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    (W : ClosedIrreducibleAnalyticSubvariety n Z)
    (himage : IsComplexAnalyticSubset (n := n) (f '' W.carrier)) :
    IsComplexAnalyticallyIrreducible (n := n) (f '' W.carrier) := by
  refine ⟨himage, ?_, ?_⟩
  · obtain ⟨z, hz⟩ := W.nonempty
    exact ⟨f z, z, hz, rfl⟩
  · intro B C hB hC hBA hCA hBC
    have hpreB : IsComplexAnalyticSubset (n := n) (W.carrier ∩ f ⁻¹' B) :=
      W.analytic.inter (AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hf hB)
    have hpreC : IsComplexAnalyticSubset (n := n) (W.carrier ∩ f ⁻¹' C) :=
      W.analytic.inter (AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hf hC)
    have hpreBC : W.carrier = (W.carrier ∩ f ⁻¹' B) ∪ (W.carrier ∩ f ⁻¹' C) := by
      apply Set.Subset.antisymm
      · intro z hz
        have hzf : f z ∈ f '' W.carrier := ⟨z, hz, rfl⟩
        rw [hBC] at hzf
        rcases hzf with hzB | hzC
        · exact Or.inl ⟨hz, hzB⟩
        · exact Or.inr ⟨hz, hzC⟩
      · rintro z (hzB | hzC)
        · exact hzB.1
        · exact hzC.1
    rcases W.irreducible_carrier.eq_left_or_eq_right hpreB hpreC
      Set.inter_subset_left Set.inter_subset_left hpreBC with hB' | hC'
    · left
      apply Set.Subset.antisymm
      · rintro y ⟨z, hz, rfl⟩
        exact (hB' ▸ hz).2
      · exact hBA
    · right
      apply Set.Subset.antisymm
      · rintro y ⟨z, hz, rfl⟩
        exact (hC' ▸ hz).2
      · exact hCA

/-- The full image-subvariety bundle has no further classical content beyond
the analytic-image statement.  Compactness supplies its closed carrier;
analytic preimages supply irreducibility; and the formal regular-locus theorem
supplies an unconstrained certified dimension. -/
theorem remmert1956_exists_image_subvariety [CompactSpace Z] {f : Z → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    (W : ClosedIrreducibleAnalyticSubvariety n Z) :
    ∃ W' : ClosedIrreducibleAnalyticSubvariety n M, W'.carrier = f '' W.carrier := by
  have himage : IsComplexAnalyticSubset (n := n) (f '' W.carrier) :=
    remmert1956_image_isComplexAnalyticSubset hf W
  obtain ⟨z, hz⟩ := W.nonempty
  have hzimage : f z ∈ f '' W.carrier := ⟨z, hz, rfl⟩
  obtain ⟨y, -, k, hy⟩ :=
    RegularLocusDense.exists_regularAtDim_mem_nhds himage hzimage Filter.univ_mem
  refine ⟨{
    carrier := f '' W.carrier
    isClosed_carrier := (W.isClosed_carrier.isCompact.image hf.continuous).isClosed
    irreducible_carrier := image_irreducible_of_isComplexAnalyticSubset hf W himage
    dim := k
    dim_le := hy.1
    regularLocus_nonempty := ⟨y, hy⟩
  }, rfl⟩

end

end SGPT.Foundations.Analysis.Pending.ProperImageAnalytic
