import SGPT.NAPotential.ProjectiveGraphRelationCore
import SGPT.NAPotential.ProjectiveGraphSegreEquations
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The actual Segre coordinate algebra and original ideal under pivot renaming

Blueprint: `projective-graph-pivot-algebra.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.NAPotential.AlgPrimes3.ProjectiveGraphSegreAlgebra

open MvPolynomial ProjectiveGraphRelations ProjectiveGraphRelationCore ProjectiveGraphSegreEquations

attribute [local instance] MvPolynomial.gradedAlgebra

variable {I J L S A K : Type*} [CommRing A] [CommRing K] [Algebra A K]

/-- The actual normalized Segre coordinates generate exactly the original two families. -/
theorem adjoin_segreVector (e : L ≃ I × J) (c : I → K) (b : J → K)
    (i₀ : I) (j₀ : J) (hc : c i₀ = 1) (hb : b j₀ = 1) :
    Algebra.adjoin A (Set.range (segreVector e c b)) =
      Algebra.adjoin A (Set.range c ∪ Set.range b) := by
  apply le_antisymm
  · apply Algebra.adjoin_le
    rintro _ ⟨l, rfl⟩
    exact mul_mem (Algebra.subset_adjoin (Or.inl ⟨_, rfl⟩))
      (Algebra.subset_adjoin (Or.inr ⟨_, rfl⟩))
  · apply Algebra.adjoin_le
    rintro _ (⟨i, rfl⟩ | ⟨j, rfl⟩)
    · change c i ∈ Algebra.adjoin A (Set.range (segreVector e c b))
      have h : segreVector e c b (e.symm (i, j₀)) ∈ Algebra.adjoin A (Set.range (segreVector e c b)) :=
        Algebra.subset_adjoin ⟨_, rfl⟩
      simpa only [segreVector, Equiv.apply_symm_apply, hb, mul_one] using h
    · change b j ∈ Algebra.adjoin A (Set.range (segreVector e c b))
      have h : segreVector e c b (e.symm (i₀, j)) ∈ Algebra.adjoin A (Set.range (segreVector e c b)) :=
        Algebra.subset_adjoin ⟨_, rfl⟩
      simpa only [segreVector, Equiv.apply_symm_apply, hc, one_mul] using h

/-- The actual remaining coordinates after removing a chosen pivot. -/
def pivotTail {N : ℕ} (v : Fin (N + 1) → K) (p : Fin (N + 1)) : Fin N → K :=
  fun i => v (p.succAbove i)

theorem adjoin_pivotTail {N : ℕ} (v : Fin (N + 1) → K) (p : Fin (N + 1)) (hp : v p = 1) :
    Algebra.adjoin A (Set.range (pivotTail v p)) = Algebra.adjoin A (Set.range v) := by
  apply le_antisymm
  · apply Algebra.adjoin_le
    rintro _ ⟨i, rfl⟩
    exact Algebra.subset_adjoin ⟨p.succAbove i, rfl⟩
  · apply Algebra.adjoin_le
    rintro _ ⟨i, rfl⟩
    refine Fin.succAboveCases p ?_ (fun j => ?_) i
    · rw [hp]
      exact one_mem _
    · exact Algebra.subset_adjoin ⟨j, rfl⟩

/-- Renaming sends every actual full homogeneous relation to an actual full relation of the renamed vector. -/
theorem rename_mem_relationCore (f : S → L) (v : L → K)
    {p : MvPolynomial S A} (hp : p ∈ (relationCore (A := A) (v ∘ f)).toIdeal) :
    rename f p ∈ (relationCore (A := A) v).toIdeal := by
  have hle : (relationCore (A := A) (v ∘ f)).toIdeal ≤
      Ideal.comap (rename f) (relationCore (A := A) v).toIdeal := by
    change Ideal.span _ ≤ _
    apply Ideal.span_le.mpr
    rintro _ ⟨⟨q, ⟨n, hn⟩⟩, hq, rfl⟩
    apply Ideal.mem_homogeneousCore_of_homogeneous_of_mem ⟨n, hn.rename_isHomogeneous⟩
    change aeval v (rename f q) = 0
    rw [aeval_rename]
    exact hq
  exact hle hp

/-- An actual coordinate permutation maps the full original homogeneous relation ideal exactly. -/
theorem map_relationCore_rename (e : S ≃ L) (v : L → K) :
    Ideal.map (rename e) (relationCore (A := A) (v ∘ e)).toIdeal =
      (relationCore (A := A) v).toIdeal := by
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    intro p hp
    exact rename_mem_relationCore e v hp
  · intro p hp
    have heq : (v ∘ e) ∘ e.symm = v := by
      funext i
      simp
    have hmem : rename e.symm p ∈ (relationCore (A := A) (v ∘ e)).toIdeal :=
      rename_mem_relationCore e.symm (v ∘ e) (by simpa only [heq] using hp)
    have hmap := Ideal.mem_map_of_mem (rename e) hmem
    simpa only [rename_rename, e.self_comp_symm, rename_id_apply] using hmap

/-- Moving a normalized actual pivot to the distinguished coordinate gives the actual normalized graph vector. -/
theorem vector_pivotRenaming {N : ℕ} (v : Fin (N + 1) → K) (p : Fin (N + 1)) (hp : v p = 1) :
    v ∘ (finSuccEquiv' p).symm = graphCoordinates (pivotTail v p) := by
  funext o
  cases o <;> simp [finSuccEquiv', graphCoordinates, pivotTail, hp]

/-- The normalized graph ideal is precisely the original global relation ideal in renamed coordinates. -/
theorem map_graphRelationIdeal_pivot {N : ℕ} (v : Fin (N + 1) → K)
    (p : Fin (N + 1)) (hp : v p = 1) :
    Ideal.map (rename (finSuccEquiv' p).symm) (graphRelationIdeal (A := A) (pivotTail v p)) =
      (relationCore (A := A) v).toIdeal := by
  rw [← relationCore_graphCoordinates, ← vector_pivotRenaming v p hp]
  exact map_relationCore_rename (finSuccEquiv' p).symm v

/-- The actual homogeneous graph quotient and the original global relation quotient are canonically isomorphic. -/
def pivotQuotientEquiv {N : ℕ} (v : Fin (N + 1) → K) (p : Fin (N + 1)) (hp : v p = 1) :
    (MvPolynomial (Option (Fin N)) A ⧸ graphRelationIdeal (A := A) (pivotTail v p)) ≃ₐ[A]
      (MvPolynomial (Fin (N + 1)) A ⧸ (relationCore (A := A) v).toIdeal) :=
  Ideal.quotientEquivAlg _ _ (renameEquiv A (finSuccEquiv' p).symm)
    (map_graphRelationIdeal_pivot v p hp).symm

end SGPT.NAPotential.AlgPrimes3.ProjectiveGraphSegreAlgebra
