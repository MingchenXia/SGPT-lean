import SGPT.Checks.Comparison.BJIntersectPositivity

/-!
# The cut formula for intersection numbers (lane BJ-INTERSECT, R2)

On an integral projective scheme `X` of dimension `≤ d + 1`, an invertible sheaf `P` with a
nonzero section `s` and zero scheme `i : D ⟶ X` satisfy

  `(P · a₁ ⋯ a_d)_X = (i^* a₁ ⋯ i^* a_d)_D`

for all Picard classes (`interNum_cut`) and all `ℚ`-line bundles (`interFormQ_cut`). This is the
formula behind [BJ22, `prop:intpairing` (i)] (`(𝒳₀ · L₁ ⋯ L_n) = (𝒳_∞ · L₁ ⋯ L_n) = (L₁ ⋯ L_n)_X`
on a test configuration) and (vi) (restriction to the components of the central fibre).

We also record that the `ℚ`-extension is determined by its values on integral classes
(`MultisetForm.ext_tmul`) and the pull-back `picPullbackQ` of `ℚ`-line bundles.

Blueprint: `claude-bj-intersect.tex` (`claude-bj-intersect:cut`).
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Scheme.Modules TopologicalSpace
open scoped TensorProduct

universe u

namespace SGPT.NAPotential.BJIntersect

open SGPT.Foundations.Envelope SGPT.Foundations.Envelope.SeshadriAmplenessCriterion

attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

/-- Pull-back of `ℚ`-line bundles. -/
def picPullbackQ {X Z : Scheme.{u}} (i : Z ⟶ X) : PicQ X →ₗ[ℚ] PicQ Z :=
  LinearMap.baseChange ℚ (picPullbackAdd i).toIntLinearMap

@[simp] theorem picPullbackQ_tmul {X Z : Scheme.{u}} (i : Z ⟶ X) (a : Additive X.Pic) :
    picPullbackQ i ((1 : ℚ) ⊗ₜ[ℤ] a) = (1 : ℚ) ⊗ₜ[ℤ] picPullbackAdd i a := rfl

variable {k : Type u} [Field k]

/-- **The cut formula** for Picard classes. -/
theorem interNum_cut (d : ℕ) {X : Scheme.{u}} [IsIntegral X] [CompactSpace X] [X.IsSeparated]
    (p : X ⟶ Spec (.of k)) [IsProjective p] (hdim : topologicalKrullDim X ≤ (d + 1 : ℕ))
    (P : X.Modules) (hP : IsInvertible P) (s : unitObj X ⟶ P) (hs : s ≠ 0)
    (t : Multiset (Additive X.Pic)) :
    letI : CompactSpace (LineSectionZeroIdeal.zeroIdeal P hP s).subscheme :=
      QuasiCompact.compactSpace_of_compactSpace (LineSectionZeroIdeal.zeroIdeal P hP s).subschemeι
    interNum p (d + 1) (unitObj X) (lineCls ⟨P, hP⟩ ::ₘ t) =
      interNum ((LineSectionZeroIdeal.zeroIdeal P hP s).subschemeι ≫ p) d
        (unitObj (LineSectionZeroIdeal.zeroIdeal P hP s).subscheme)
        (t.map (picPullbackAdd (LineSectionZeroIdeal.zeroIdeal P hP s).subschemeι)) := by
  let D := LineSectionZeroIdeal.zeroIdeal P hP s
  let i := D.subschemeι
  let : CompactSpace D.subscheme := QuasiCompact.compactSpace_of_compactSpace i
  let : D.subscheme.IsSeparated := isSeparated_of_closed i
  let : IsProjective (i ≫ p) := isProjective_closed_comp i p
  change interNum p (d + 1) (unitObj X) (lineCls ⟨P, hP⟩ ::ₘ t) =
    interNum (i ≫ p) d (unitObj D.subscheme) (t.map (picPullbackAdd i))
  by_cases ht : Multiset.card t = d
  · obtain ⟨l, rfl⟩ : ∃ l : List (Additive X.Pic), (l : Multiset _) = t :=
      ⟨t.toList, Multiset.coe_toList t⟩
    have hl : l.length = d := by simpa using ht
    have hdimD : topologicalKrullDim D.subscheme ≤ d := sectionZero_dimension_drop d hdim P hP s hs
    have hTP : IsInvertible (unitObj X ⊗ P) :=
      (isInvertible_unit.tensorObj hP).of_iso (SGPT.Support.ModularCurves.monoidalTensorObjIso _ P)
    have hT : IsInvertible ((Scheme.Modules.pullback i).obj (unitObj X ⊗ P)) := hTP.pullback i
    rw [← interNum_coefficient (i ≫ p) d hdimD _ hT, Multiset.cons_coe, Multiset.map_coe,
      interNum_coe p (d + 1) _ _ (by simpa using hl), interNum_coe (i ≫ p) d _ _ (by simpa using hl)]
    unfold interList
    have hinv : ∀ K ∈ l.map (fun a => picRep a.toMul), IsInvertible K := by
      intro K hK
      obtain ⟨c, -, rfl⟩ := List.mem_map.mp hK
      exact picRep_isInvertible _
    rw [List.map_cons, mixedEulerDifference_congr p
      (ls := picRep (Additive.toMul (lineCls ⟨P, hP⟩)) :: l.map fun a => picRep a.toMul)
      (ms := P :: l.map fun a => picRep a.toMul)
      (List.Forall₂.cons ⟨picRepLineClassIso P hP⟩
        (List.forall₂_same.mpr fun _ _ => ⟨Iso.refl _⟩)),
      mixedEulerDifference_sectionDifference p P hP s hs _ hinv (unitObj X) isInvertible_unit,
      List.map_map, List.map_map]
    apply mixedEulerDifference_congr
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    refine List.forall₂_same.mpr fun a _ => ?_
    obtain ⟨e⟩ := picRep_picPullback i a.toMul
    exact ⟨e.symm⟩
  · rw [interNum_of_card_ne p (d + 1) _ _ (by simpa using ht),
      interNum_of_card_ne (i ≫ p) d _ _ (by simpa using ht)]

/-- **The cut formula** for `ℚ`-line bundles: `(P · θ₁ ⋯ θ_d)_X = (θ₁|_D ⋯ θ_d|_D)_D` for the
zero scheme `D` of a nonzero section of `P` on an integral projective `X` of dimension `≤ d + 1`. -/
theorem interFormQ_cut (d : ℕ) {X : Scheme.{u}} [IsIntegral X] [CompactSpace X] [X.IsSeparated]
    (p : X ⟶ Spec (.of k)) [IsProjective p] (hdim : topologicalKrullDim X ≤ (d + 1 : ℕ))
    (P : X.Modules) (hP : IsInvertible P) (s : unitObj X ⟶ P) (hs : s ≠ 0)
    (t : Multiset (PicQ X)) :
    letI : CompactSpace (LineSectionZeroIdeal.zeroIdeal P hP s).subscheme :=
      QuasiCompact.compactSpace_of_compactSpace (LineSectionZeroIdeal.zeroIdeal P hP s).subschemeι
    letI : (LineSectionZeroIdeal.zeroIdeal P hP s).subscheme.IsSeparated :=
      isSeparated_of_closed (LineSectionZeroIdeal.zeroIdeal P hP s).subschemeι
    letI : IsProjective ((LineSectionZeroIdeal.zeroIdeal P hP s).subschemeι ≫ p) :=
      isProjective_closed_comp _ p
    interFormQ p (d + 1) hdim (unitObj X) (picQ ⟨P, hP⟩ ::ₘ t) =
      interFormQ ((LineSectionZeroIdeal.zeroIdeal P hP s).subschemeι ≫ p) d
        (sectionZero_dimension_drop d hdim P hP s hs)
        (unitObj (LineSectionZeroIdeal.zeroIdeal P hP s).subscheme)
        (t.map (picPullbackQ (LineSectionZeroIdeal.zeroIdeal P hP s).subschemeι)) := by
  let D := LineSectionZeroIdeal.zeroIdeal P hP s
  let i := D.subschemeι
  let : CompactSpace D.subscheme := QuasiCompact.compactSpace_of_compactSpace i
  let : D.subscheme.IsSeparated := isSeparated_of_closed i
  let : IsProjective (i ≫ p) := isProjective_closed_comp i p
  have hdimD : topologicalKrullDim D.subscheme ≤ d := sectionZero_dimension_drop d hdim P hP s hs
  have key := MultisetForm.ext_tmul ((interFormQ p (d + 1) hdim (unitObj X)).fix {picQ ⟨P, hP⟩})
    ((interFormQ (i ≫ p) d hdimD (unitObj D.subscheme)).comp (picPullbackQ i))
    (by
      intro u
      rw [MultisetForm.fix_apply, MultisetForm.comp_apply, Multiset.singleton_add,
        Multiset.map_map]
      have h1 := interFormQ_tmul p (d + 1) hdim (unitObj X) (lineCls ⟨P, hP⟩ ::ₘ u)
      rw [Multiset.map_cons] at h1
      have h2 := interFormQ_tmul (i ≫ p) d hdimD (unitObj D.subscheme)
        (u.map (picPullbackAdd i))
      rw [Multiset.map_map] at h2
      change interFormQ p (d + 1) hdim (unitObj X) ((1 : ℚ) ⊗ₜ[ℤ] lineCls ⟨P, hP⟩ ::ₘ
          u.map fun a => (1 : ℚ) ⊗ₜ[ℤ] a) = _
      rw [h1]
      have h3 : ((picPullbackQ i) ∘ fun a : Additive X.Pic => (1 : ℚ) ⊗ₜ[ℤ] a) =
          (fun a => (1 : ℚ) ⊗ₜ[ℤ] a) ∘ picPullbackAdd i := rfl
      rw [h3, h2]
      exact_mod_cast interNum_cut d p hdim P hP s hs u) t
  simpa using key

end SGPT.NAPotential.BJIntersect
