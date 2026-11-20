import SGPT.Foundations.Schemes.NonemptySubsetCechComparison
import SGPT.Foundations.Schemes.HomogeneousCechDimensionShift
import SGPT.Foundations.Schemes.BoundedCohomologyEulerAdditivity

open CategoryTheory CategoryTheory.Limits

namespace SGPT.Foundations.Schemes

universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000

section Exact
variable {K I : Type u} [CommRing K] [LinearOrder I]
    {F G H : Finset I ⥤ ModuleCat.{u} K}

/-- The actual nonempty map on every original positive intersection component. -/
theorem nonemptySubsetCechCardMap_apply_of_nonempty
    (α : nonemptySubsetDiagram F ⟶ nonemptySubsetDiagram G) (n : ℕ)
    (c : subsetCechCardPiece F n) (S : Finset I) (hS : S.Nonempty) :
    (nonemptySubsetCechCardMap α n c).val S = α.app ⟨S, hS⟩ (c.val S) := by
  change (if h : S.Nonempty then α.app ⟨S, h⟩ (c.val S) else (0 : G.obj S)) = _
  rw [dif_pos hS]

/-- Genuine injectivity on nonempty intersections injects every positive
cardinality term. No assertion is made for the empty/global term. -/
theorem nonemptySubsetCechCardMap_injective
    (α : nonemptySubsetDiagram F ⟶ nonemptySubsetDiagram G)
    (hi : ∀ S, Function.Injective (α.app S)) (n : ℕ) (hn : 0 < n) :
    Function.Injective (nonemptySubsetCechCardMap α n) := by
  intro x y he
  apply Subtype.ext
  funext S
  by_cases hS : S.Nonempty
  · apply hi ⟨S, hS⟩
    have hp := congrArg (fun z : subsetCechCardPiece G n ↦ z.val S) he
    simpa only [nonemptySubsetCechCardMap_apply_of_nonempty α n x S hS,
      nonemptySubsetCechCardMap_apply_of_nonempty α n y S hS] using hp
  · have hc : S.card ≠ n := by
      intro hc
      exact hS (Finset.card_pos.mp (by rw [hc]; exact hn))
    rw [x.property S hc, y.property S hc]

/-- Genuine nonempty-intersection surjectivity surjects each positive term,
without requiring surjectivity of original global sections at the empty set. -/
theorem nonemptySubsetCechCardMap_surjective
    (α : nonemptySubsetDiagram F ⟶ nonemptySubsetDiagram G)
    (hs : ∀ S, Function.Surjective (α.app S)) (n : ℕ) (hn : 0 < n) :
    Function.Surjective (nonemptySubsetCechCardMap α n) := by
  classical
  intro z
  choose a ha using fun S ↦ hs S (z.val S.val)
  let c : subsetCechCardPiece F n := ⟨fun S ↦
    if hc : S.card = n then a ⟨S, Finset.card_pos.mp (by rw [hc]; exact hn)⟩ else 0,
    by intro S hS; simp only [dif_neg hS]⟩
  refine ⟨c, ?_⟩
  apply Subtype.ext
  funext S
  by_cases hS : S.Nonempty
  · rw [nonemptySubsetCechCardMap_apply_of_nonempty α n c S hS]
    change α.app ⟨S, hS⟩
      (if hc : S.card = n then a ⟨S, Finset.card_pos.mp (by rw [hc]; exact hn)⟩ else 0) = _
    by_cases hc : S.card = n
    · rw [dif_pos hc, ha ⟨S, hS⟩]
    · rw [dif_neg hc, map_zero, z.property S hc]
  · have hc : S.card ≠ n := by
      intro hc
      exact hS (Finset.card_pos.mp (by rw [hc]; exact hn))
    change (if h : S.Nonempty then α.app ⟨S, h⟩ (c.val S) else (0 : G.obj S)) = _
    rw [dif_neg hS, z.property S hc]

/-- Genuine exactness only on original nonempty intersections is exactness
of every positive term, including possible localization torsion. -/
theorem nonemptySubsetCechCardMap_exact
    (α : nonemptySubsetDiagram F ⟶ nonemptySubsetDiagram G)
    (β : nonemptySubsetDiagram G ⟶ nonemptySubsetDiagram H)
    (he : ∀ S, Function.Exact (α.app S) (β.app S)) (n : ℕ) (hn : 0 < n) :
    Function.Exact (nonemptySubsetCechCardMap α n) (nonemptySubsetCechCardMap β n) := by
  classical
  intro z
  constructor
  · intro hz
    have hzS (S : {S : Finset I // S.Nonempty}) : β.app S (z.val S.val) = 0 := by
      have hp := congrArg (fun x : subsetCechCardPiece H n ↦ x.val S.val) hz
      change (nonemptySubsetCechCardMap β n z).val S.val = 0 at hp
      rw [nonemptySubsetCechCardMap_apply_of_nonempty β n z S.val S.property] at hp
      exact hp
    choose a ha using fun S ↦ (he S (z.val S.val)).mp (hzS S)
    let c : subsetCechCardPiece F n := ⟨fun S ↦
      if hc : S.card = n then a ⟨S, Finset.card_pos.mp (by rw [hc]; exact hn)⟩ else 0,
      by intro S hS; simp only [dif_neg hS]⟩
    refine ⟨c, ?_⟩
    apply Subtype.ext
    funext S
    by_cases hS : S.Nonempty
    · rw [nonemptySubsetCechCardMap_apply_of_nonempty α n c S hS]
      change α.app ⟨S, hS⟩
        (if hc : S.card = n then a ⟨S, Finset.card_pos.mp (by rw [hc]; exact hn)⟩ else 0) = _
      by_cases hc : S.card = n
      · rw [dif_pos hc, ha ⟨S, hS⟩]
      · rw [dif_neg hc, map_zero, z.property S hc]
    · have hc : S.card ≠ n := by
        intro hc
        exact hS (Finset.card_pos.mp (by rw [hc]; exact hn))
      change (if h : S.Nonempty then α.app ⟨S, h⟩ (c.val S) else (0 : G.obj S)) = _
      rw [dif_neg hS, z.property S hc]
  · rintro ⟨a, rfl⟩
    apply Subtype.ext
    funext S
    by_cases hS : S.Nonempty
    · rw [nonemptySubsetCechCardMap_apply_of_nonempty β n _ S hS,
        nonemptySubsetCechCardMap_apply_of_nonempty α n a S hS]
      exact (he ⟨S, hS⟩).apply_apply_eq_zero (a.val S)
    · change (if h : S.Nonempty then β.app ⟨S, h⟩
        ((nonemptySubsetCechCardMap α n a).val S) else (0 : H.obj S)) = 0
      rw [dif_neg hS]

/-- The original normalized complexes form a genuine short complex using
only their actual nonempty-diagram morphisms and primitive exactness. -/
def actualNonemptySubsetCechShortComplex
    (α : nonemptySubsetDiagram F ⟶ nonemptySubsetDiagram G)
    (β : nonemptySubsetDiagram G ⟶ nonemptySubsetDiagram H)
    (he : ∀ S, Function.Exact (α.app S) (β.app S)) :
    ShortComplex (CochainComplex (ModuleCat.{u} K) ℕ) :=
  ShortComplex.mk (nonemptySubsetCechComplexMap α) (nonemptySubsetCechComplexMap β) (by
    apply HomologicalComplex.Hom.ext
    funext p
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    funext S
    change (nonemptySubsetCechCardMap β (p + 1)
      (nonemptySubsetCechCardMap α (p + 1) a)).val S = 0
    by_cases hS : S.Nonempty
    · rw [nonemptySubsetCechCardMap_apply_of_nonempty β _ _ S hS,
        nonemptySubsetCechCardMap_apply_of_nonempty α _ _ S hS]
      exact (he ⟨S, hS⟩).apply_apply_eq_zero (a.val S)
    · change (if h : S.Nonempty then β.app ⟨S, h⟩
        ((nonemptySubsetCechCardMap α (p + 1) a).val S) else (0 : H.obj S)) = 0
      rw [dif_neg hS])

/-- Primitive exact/injective/surjective maps on NONEMPTY intersections
produce true ShortExact original normalized Cech complexes. No empty/global
section exactness hypothesis is present. -/
theorem actualNonemptySubsetCechShortComplex_shortExact
    (α : nonemptySubsetDiagram F ⟶ nonemptySubsetDiagram G)
    (β : nonemptySubsetDiagram G ⟶ nonemptySubsetDiagram H)
    (he : ∀ S, Function.Exact (α.app S) (β.app S))
    (hi : ∀ S, Function.Injective (α.app S))
    (hs : ∀ S, Function.Surjective (β.app S)) :
    (actualNonemptySubsetCechShortComplex α β he).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro p
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
    exact nonemptySubsetCechCardMap_exact α β he (p + 1) (Nat.zero_lt_succ p)
  · apply (ModuleCat.mono_iff_injective _).mpr
    exact nonemptySubsetCechCardMap_injective α hi (p + 1) (Nat.zero_lt_succ p)
  · apply (ModuleCat.epi_iff_surjective _).mpr
    exact nonemptySubsetCechCardMap_surjective β hs (p + 1) (Nat.zero_lt_succ p)

end Exact

section Euler
variable {K I : Type} [Field K] [LinearOrder I] [Fintype I]
    {F G H : Finset I ⥤ ModuleCat K}

/-- Actual NONEMPTY intersection exactness gives genuine finite-homology
Euler additivity for the SAME original normalized complexes. Empty/global
section surjectivity and finite affine complex terms are never assumed. -/
theorem actualNonemptySubsetCechEuler_additive
    (α : nonemptySubsetDiagram F ⟶ nonemptySubsetDiagram G)
    (β : nonemptySubsetDiagram G ⟶ nonemptySubsetDiagram H)
    (he : ∀ S, Function.Exact (α.app S) (β.app S))
    (hi : ∀ S, Function.Injective (α.app S))
    (hs : ∀ S, Function.Surjective (β.app S))
    [∀ p, Module.Finite K ((subsetCechComplex F).homology p)]
    [∀ p, Module.Finite K ((subsetCechComplex G).homology p)]
    [∀ p, Module.Finite K ((subsetCechComplex H).homology p)] :
    (subsetCechComplex G).homologyEulerChar =
      (subsetCechComplex F).homologyEulerChar + (subsetCechComplex H).homologyEulerChar := by
  let S := actualNonemptySubsetCechShortComplex α β he
  have hS : S.ShortExact := actualNonemptySubsetCechShortComplex_shortExact α β he hi hs
  let : ∀ p, Module.Finite K (S.X₁.homology p) := by
    intro p
    change Module.Finite K ((subsetCechComplex F).homology p)
    infer_instance
  let : ∀ p, Module.Finite K (S.X₂.homology p) := by
    intro p
    change Module.Finite K ((subsetCechComplex G).homology p)
    infer_instance
  let : ∀ p, Module.Finite K (S.X₃.homology p) := by
    intro p
    change Module.Finite K ((subsetCechComplex H).homology p)
    infer_instance
  exact boundedCochain_homologyEulerChar_additive S hS (Fintype.card I)
    (fun p hp ↦ subsetCechComplex_homology_isZero_of_card_le F p hp)
    (fun p hp ↦ subsetCechComplex_homology_isZero_of_card_le G p hp)
    (fun p hp ↦ subsetCechComplex_homology_isZero_of_card_le H p hp)

end Euler

end
end SGPT.Foundations.Schemes
