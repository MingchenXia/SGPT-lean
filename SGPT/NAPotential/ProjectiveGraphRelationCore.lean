import SGPT.NAPotential.ProjectiveGraphRelations

/-!
# The full homogeneous relation ideal of an actual coordinate vector

Mathlib's homogeneous core of the evaluation kernel constructs all homogeneous
relations, for an arbitrary actual vector. Its normalized specialization equals
the checked graph relation ideal exactly. Finite generation retains actual
homogeneous members of the same ideal.

Blueprint: `projective-graph-analytic-zero.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.NAPotential.AlgPrimes3.ProjectiveGraphRelationCore

open MvPolynomial ProjectiveGraphRelations
attribute [local instance] MvPolynomial.gradedAlgebra

variable {I A K : Type*} [CommRing A] [CommRing K] [Algebra A K]

/-- Every homogeneous polynomial relation of the actual coordinate vector. -/
def relationCore (v : I → K) : HomogeneousIdeal (homogeneousSubmodule I A) :=
  (RingHom.ker (aeval (R := A) v)).homogeneousCore (homogeneousSubmodule I A)

theorem relationCore_le_ker (v : I → K) :
    (relationCore (A := A) v).toIdeal ≤ RingHom.ker (aeval (R := A) v) :=
  Ideal.toIdeal_homogeneousCore_le _ _

/-- The general relation construction agrees with the checked normalized graph ideal. -/
theorem relationCore_graphCoordinates (b : I → K) :
    (relationCore (A := A) (graphCoordinates b)).toIdeal = graphRelationIdeal (A := A) b := by
  apply le_antisymm
  · change Ideal.span _ ≤ graphRelationIdeal (A := A) b
    apply Ideal.span_le.mpr
    rintro p ⟨⟨q, ⟨n, hn⟩⟩, hq, rfl⟩
    exact Ideal.subset_span ⟨n, hn, hq⟩
  · apply Ideal.span_le.mpr
    rintro p ⟨n, hn, hp⟩
    exact Ideal.mem_homogeneousCore_of_homogeneous_of_mem ⟨n, hn⟩ hp

section Finite

variable [Finite I] [IsNoetherianRing A]

/-- Finite generators are chosen among the homogeneous elements of the original ideal. -/
theorem exists_finite_homogeneous_generators (J : HomogeneousIdeal (homogeneousSubmodule I A)) :
    ∃ F : Finset (MvPolynomial I A),
      (∀ p ∈ F, (∃ n : ℕ, p.IsHomogeneous n) ∧ p ∈ J.toIdeal) ∧
      Ideal.span (F : Set (MvPolynomial I A)) = J.toIdeal := by
  obtain ⟨S, hS⟩ :=
    (Ideal.IsHomogeneous.iff_exists (homogeneousSubmodule I A) J.toIdeal).mp J.isHomogeneous
  have hfg : (Ideal.span (Subtype.val '' S) : Ideal (MvPolynomial I A)).FG :=
    Ideal.fg_of_isNoetherianRing _
  obtain ⟨F, hF, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).mp hfg
  refine ⟨F, ?_, hspan.symm.trans hS.symm⟩
  intro p hp
  obtain ⟨q, hq, rfl⟩ := hF hp
  refine ⟨q.property, ?_⟩
  rw [hS]
  exact Ideal.subset_span ⟨q, hq, rfl⟩

/-- The finite global equations are actual homogeneous relations of the same vector. -/
theorem exists_finite_relations (v : I → K) :
    ∃ F : Finset (MvPolynomial I A),
      (∀ p ∈ F, ∃ n : ℕ, p.IsHomogeneous n ∧ aeval v p = 0) ∧
      Ideal.span (F : Set (MvPolynomial I A)) = (relationCore (A := A) v).toIdeal := by
  obtain ⟨F, hF, hspan⟩ := exists_finite_homogeneous_generators (relationCore (A := A) v)
  refine ⟨F, ?_, hspan⟩
  intro p hp
  obtain ⟨⟨n, hn⟩, hmem⟩ := hF p hp
  exact ⟨n, hn, relationCore_le_ker v hmem⟩

end Finite

end SGPT.NAPotential.AlgPrimes3.ProjectiveGraphRelationCore
