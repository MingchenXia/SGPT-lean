import SGPT.Foundations.Envelope.AlgGeom.SeshadriAmplenessCriterionIntersectionPositivity
import SGPT.Foundations.Envelope.AlgGeom.CurvePicardDegrees
import SGPT.NAPotential.BJIntersectForm

/-!
# Intersection numbers of `ℚ`-line bundles on projective schemes (lane BJ-INTERSECT, R2)

Let `p : X ⟶ Spec k` be projective with `dim X ≤ d` and `F` a coherent sheaf. SGPT.Foundations.Envelope
defines the Kleiman–Snapper numbers `mixedEulerDifference p [L₁, …, L_d] F = Δ_{L₁} ⋯ Δ_{L_d} χ(X, F)`
for invertible sheaves `Lᵢ`. We descend them to the Picard group and extend them to
`Pic(X)_ℚ = ℚ ⊗[ℤ] Pic X`:

* `interNum p d F` — the numbers `(a₁ ⋯ a_d · F)` for `aᵢ ∈ Pic X`, as a function of the multiset
  of the `aᵢ`, and `0` on multisets of other cardinality;
* `interForm p d hdim F` — the same as a `ℤ`-valued multiset form (symmetric and additive in each
  argument, `interNum_cons_mul`);
* `interFormQ p d hdim F` — the intersection form on `ℚ`-line bundles (`interFormQ_picQ`:
  it computes `mixedEulerDifference` on classes of invertible sheaves).

We also transport the SGPT.Foundations.Envelope statements: independence of the invertible coefficient
(`interNum_coefficient`), restriction to closed subschemes (`interNum_restrict`) and vanishing
beyond the dimension (`interNum_eq_zero_of_dim_lt`).

Source: Kleiman's intersection theory (Debarre, *Higher-dimensional algebraic geometry*, §1.1);
the intersection numbers of [BJ22, §3.2]. Blueprint: `claude-bj-intersect.tex`.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Scheme.Modules
open scoped TensorProduct

universe u

namespace SGPT.NAPotential.BJIntersect

open SGPT.Foundations.Envelope SGPT.Foundations.Envelope.SeshadriAmplenessCriterion

attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

/-! ### Representatives of Picard classes -/

section picRep

variable {X : Scheme.{u}}

/-- A chosen invertible sheaf in a Picard class. -/
def picRep (a : X.Pic) : X.Modules := a.val.out

theorem toSkeleton_picRep (a : X.Pic) : toSkeleton (picRep a) = a.val := Quotient.out_eq _

theorem picRep_isInvertible (a : X.Pic) : IsInvertible (picRep a) := by
  apply isInvertible_of_isUnit_toSkeleton
  rw [toSkeleton_picRep]
  exact a.isUnit

/-- The representative of a product is the tensor product of the representatives. -/
def picRepMulIso (a b : X.Pic) : picRep (a * b) ≅ picRep a ⊗ picRep b :=
  Skeleton.isoOfEq (by rw [toSkeleton_picRep]; rfl)

/-- The representative of the class of an invertible sheaf is isomorphic to it. -/
def picRepLineClassIso (L : X.Modules) (hL : IsInvertible L) :
    picRep (CurvePicardDegrees.lineClass L hL) ≅ L :=
  Skeleton.isoOfEq (by rw [toSkeleton_picRep, CurvePicardDegrees.lineClass_val])

theorem lineClass_picRep (a : X.Pic) :
    CurvePicardDegrees.lineClass (picRep a) (picRep_isInvertible a) = a := by
  apply Units.ext
  rw [CurvePicardDegrees.lineClass_val, toSkeleton_picRep]

/-- The additive Picard class of an invertible sheaf. -/
def lineCls (L : {L : X.Modules // IsInvertible L}) : Additive X.Pic :=
  Additive.ofMul (CurvePicardDegrees.lineClass L.1 L.2)

end picRep

/-! ### Mixed Euler differences only depend on the isomorphism classes of the entries -/

section isoInvariance

variable {k : Type u} [Field k] {X : Scheme.{u}} [CompactSpace X] (p : X ⟶ Spec (.of k))

theorem mixedEulerDifference_congr {ls ms : List X.Modules}
    (h : List.Forall₂ (fun L M => Nonempty (L ≅ M)) ls ms) (F : X.Modules) :
    mixedEulerDifference p ls F = mixedEulerDifference p ms F := by
  induction h generalizing F with
  | nil => rfl
  | @cons L M ls ms hLM _ ih =>
    obtain ⟨e⟩ := hLM
    change mixedEulerDifference p ls (F ⊗ L) - mixedEulerDifference p ls F =
      mixedEulerDifference p ms (F ⊗ M) - mixedEulerDifference p ms F
    rw [ih, ih, mixedEulerDifference_eq_of_iso p ms (Iso.refl F ⊗ᵢ e)]

end isoInvariance

/-! ### Intersection numbers on the Picard group -/

section numbers

variable {k : Type u} [Field k] {X : Scheme.{u}} [CompactSpace X] (p : X ⟶ Spec (.of k))

/-- The intersection number of a list of Picard classes against `F`. -/
def interList (F : X.Modules) (l : List (Additive X.Pic)) : ℤ :=
  mixedEulerDifference p (l.map fun a => picRep a.toMul) F

theorem interList_perm (F : X.Modules) {l l' : List (Additive X.Pic)} (h : l.Perm l') :
    interList p F l = interList p F l' :=
  mixedEulerDifference_perm p (h.map _) F

/-- **Intersection numbers** `(a₁ ⋯ a_d · F)` of Picard classes against a sheaf `F`, as a function
of the multiset `{a₁, …, a_d}`; the value is `0` on multisets of cardinality different from `d`. -/
def interNum (d : ℕ) (F : X.Modules) (s : Multiset (Additive X.Pic)) : ℤ :=
  if Multiset.card s = d then Quot.liftOn s (interList p F) (fun _ _ h => interList_perm p F h)
  else 0

theorem interNum_coe (d : ℕ) (F : X.Modules) (l : List (Additive X.Pic)) (hl : l.length = d) :
    interNum p d F (l : Multiset (Additive X.Pic)) = interList p F l := by
  rw [interNum, if_pos (by simpa using hl)]
  rfl

theorem interNum_of_card_ne (d : ℕ) (F : X.Modules) (s : Multiset (Additive X.Pic))
    (hs : Multiset.card s ≠ d) : interNum p d F s = 0 := by
  rw [interNum, if_neg hs]

/-- On classes of invertible sheaves, the intersection numbers are the mixed Euler differences. -/
theorem interList_lineCls (F : X.Modules) (ls : List {L : X.Modules // IsInvertible L}) :
    interList p F (ls.map lineCls) = mixedEulerDifference p (ls.map Subtype.val) F := by
  unfold interList
  rw [List.map_map]
  apply mixedEulerDifference_congr
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  refine List.forall₂_same.mpr fun L _ => ⟨picRepLineClassIso L.1 L.2⟩

theorem interNum_ofLines (d : ℕ) (F : X.Modules) (ls : List {L : X.Modules // IsInvertible L})
    (hl : ls.length = d) :
    interNum p d F ((ls.map lineCls : List (Additive X.Pic)) : Multiset (Additive X.Pic)) =
      mixedEulerDifference p (ls.map Subtype.val) F := by
  rw [interNum_coe p d F _ (by simpa using hl), interList_lineCls]

variable [X.IsSeparated] [IsProjective p]

/-- **Additivity in each argument.** In top degree `d ≥ dim X`, `(a b · s) = (a · s) + (b · s)`
(written additively in `Additive (Pic X)`). -/
theorem interNum_cons_mul (d : ℕ) (hdim : topologicalKrullDim X ≤ d)
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (a b : Additive X.Pic)
    (s : Multiset (Additive X.Pic)) :
    interNum p d F ((a + b) ::ₘ s) = interNum p d F (a ::ₘ s) + interNum p d F (b ::ₘ s) := by
  by_cases hs : Multiset.card s + 1 = d
  · obtain ⟨l, rfl⟩ : ∃ l : List (Additive X.Pic), (l : Multiset _) = s :=
      ⟨s.toList, Multiset.coe_toList s⟩
    have hl : l.length + 1 = d := by simpa using hs
    change interNum p d F (((a + b) :: l : List _) : Multiset _) =
      interNum p d F ((a :: l : List _) : Multiset _) +
        interNum p d F ((b :: l : List _) : Multiset _)
    rw [interNum_coe p d F _ (by simpa using hl), interNum_coe p d F _ (by simpa using hl),
      interNum_coe p d F _ (by simpa using hl)]
    unfold interList
    simp only [List.map_cons]
    have hinv : ∀ K ∈ l.map (fun a => picRep a.toMul), IsInvertible K := by
      intro K hK
      obtain ⟨c, -, rfl⟩ := List.mem_map.mp hK
      exact picRep_isInvertible _
    rw [toMul_add, mixedEulerDifference_congr p (ms := (picRep a.toMul ⊗ picRep b.toMul) ::
        l.map (fun a => picRep a.toMul))
      (List.Forall₂.cons ⟨picRepMulIso a.toMul b.toMul⟩
        (List.forall₂_same.mpr fun _ _ => ⟨Iso.refl _⟩)) F]
    exact mixedEulerDifference_tensor_add p d hdim _ _ (picRep_isInvertible _)
      (picRep_isInvertible _) _ (by simpa using hl) hinv F
  · rw [interNum_of_card_ne p d F _ (by simpa using hs), interNum_of_card_ne p d F _
      (by simpa using hs), interNum_of_card_ne p d F _ (by simpa using hs), add_zero]

/-- **The intersection form** on `Pic X` against a coherent sheaf `F`, for `dim X ≤ d`: a
symmetric `ℤ`-multilinear form of degree `d`. -/
def interForm (d : ℕ) (hdim : topologicalKrullDim X ≤ d)
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    MultisetForm ℤ (Additive X.Pic) :=
  MultisetForm.ofAdd (interNum p d F) (interNum_cons_mul p d hdim F)

@[simp] theorem interForm_apply (d : ℕ) (hdim : topologicalKrullDim X ≤ d)
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (s : Multiset (Additive X.Pic)) :
    interForm p d hdim F s = interNum p d F s := rfl

theorem interForm_hasDegree (d : ℕ) (hdim : topologicalKrullDim X ≤ d)
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] : (interForm p d hdim F).HasDegree d :=
  fun s hs => interNum_of_card_ne p d F s hs

/-- **Independence of an invertible coefficient** in top degree. -/
theorem interNum_coefficient (d : ℕ) (hdim : topologicalKrullDim X ≤ d) (T : X.Modules)
    (hT : IsInvertible T) (s : Multiset (Additive X.Pic)) :
    interNum p d T s = interNum p d (unitObj X) s := by
  by_cases hs : Multiset.card s = d
  · obtain ⟨l, rfl⟩ : ∃ l : List (Additive X.Pic), (l : Multiset _) = s :=
      ⟨s.toList, Multiset.coe_toList s⟩
    have hl : l.length = d := by simpa using hs
    rw [interNum_coe p d T l hl, interNum_coe p d _ l hl]
    unfold interList
    refine mixedEulerDifference_eq_unit_of_dimension_le p d hdim _ (by simpa using hl) ?_ T hT
    intro K hK
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hK
    exact picRep_isInvertible _
  · rw [interNum_of_card_ne p d _ _ hs, interNum_of_card_ne p d _ _ hs]

/-- **Vanishing beyond the dimension.** -/
theorem interNum_eq_zero_of_dim_lt (d : ℕ) (hdim : topologicalKrullDim X ≤ d)
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (s : Multiset (Additive X.Pic)) :
    interNum p (d + 1) F s = 0 := by
  by_cases hs : Multiset.card s = d + 1
  · obtain ⟨l, rfl⟩ : ∃ l : List (Additive X.Pic), (l : Multiset _) = s :=
      ⟨s.toList, Multiset.coe_toList s⟩
    have hl : l.length = d + 1 := by simpa using hs
    rw [interNum_coe p (d + 1) F l hl]
    unfold interList
    refine mixedEulerDifference_eq_zero_of_dimension_le d p hdim _ (by simpa using hl) ?_ F
    intro K hK
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hK
    exact picRep_isInvertible _
  · exact interNum_of_card_ne p _ F s hs

end numbers

/-! ### Restriction to closed subschemes -/

section restrict

variable {k : Type u} [Field k] {X Z : Scheme.{u}} [CompactSpace X] [CompactSpace Z]
  [X.IsSeparated] [Z.IsSeparated] (p : X ⟶ Spec (.of k))

/-- The additive pull-back of Picard classes. -/
def picPullbackAdd (i : Z ⟶ X) : Additive X.Pic →+ Additive Z.Pic :=
  (CurvePicardDegrees.picPullback i).toAdditive

omit [CompactSpace X] [CompactSpace Z] [X.IsSeparated] [Z.IsSeparated] in
theorem picRep_picPullback (i : Z ⟶ X) (a : X.Pic) :
    Nonempty (picRep (CurvePicardDegrees.picPullback i a) ≅
      (Scheme.Modules.pullback i).obj (picRep a)) := by
  have h := CurvePicardDegrees.picPullback_lineClass i (picRep a) (picRep_isInvertible a)
  rw [lineClass_picRep] at h
  rw [h]
  exact ⟨picRepLineClassIso _ _⟩

/-- **Restriction.** For an affine morphism `i : Z ⟶ X` (e.g. a closed immersion) and a
quasi-coherent `N` on `Z`, `(a₁ ⋯ a_d · i_* N)_X = (i^* a₁ ⋯ i^* a_d · N)_Z`. -/
theorem interNum_restrict (i : Z ⟶ X) [IsAffineHom i] (d : ℕ) (N : Z.Modules)
    [N.IsQuasicoherent] (s : Multiset (Additive X.Pic)) :
    interNum p d ((Scheme.Modules.pushforward i).obj N) s =
      interNum (i ≫ p) d N (s.map (picPullbackAdd i)) := by
  by_cases hs : Multiset.card s = d
  · obtain ⟨l, rfl⟩ : ∃ l : List (Additive X.Pic), (l : Multiset _) = s :=
      ⟨s.toList, Multiset.coe_toList s⟩
    have hl : l.length = d := by simpa using hs
    rw [Multiset.map_coe]
    rw [interNum_coe p d _ l hl, interNum_coe (i ≫ p) d N _ (by simpa using hl)]
    unfold interList
    rw [mixedEulerDifference_pushforward p i _ (by
      intro K hK
      obtain ⟨c, -, rfl⟩ := List.mem_map.mp hK
      exact picRep_isInvertible _) N, List.map_map, List.map_map]
    apply mixedEulerDifference_congr
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    refine List.forall₂_same.mpr fun a _ => ?_
    obtain ⟨e⟩ := picRep_picPullback i a.toMul
    exact ⟨e.symm⟩
  · rw [interNum_of_card_ne p d _ s hs, interNum_of_card_ne (i ≫ p) d _ _ (by simpa using hs)]

end restrict

/-! ### `ℚ`-line bundles -/

section rational

variable {X : Scheme.{u}}

/-- The rational Picard group `Pic(X)_ℚ = ℚ ⊗[ℤ] Pic X` (classes of `ℚ`-line bundles). -/
abbrev PicQ (X : Scheme.{u}) := ℚ ⊗[ℤ] Additive X.Pic

/-- The class in `Pic(X)_ℚ` of an invertible sheaf. -/
def picQ (L : {L : X.Modules // IsInvertible L}) : PicQ X := 1 ⊗ₜ lineCls L

variable {k : Type u} [Field k] [CompactSpace X] [X.IsSeparated] (p : X ⟶ Spec (.of k))
  [IsProjective p]

/-- **The intersection form on `ℚ`-line bundles** against a coherent sheaf `F`, for
`dim X ≤ d`: the unique `ℚ`-multilinear extension of the intersection numbers. -/
def interFormQ (d : ℕ) (hdim : topologicalKrullDim X ≤ d) (F : X.Modules) [F.IsQuasicoherent]
    [F.IsFiniteType] : MultisetForm ℚ (PicQ X) :=
  MultisetForm.extendRat (interForm p d hdim F)

theorem interFormQ_hasDegree (d : ℕ) (hdim : topologicalKrullDim X ≤ d) (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] : (interFormQ p d hdim F).HasDegree d :=
  MultisetForm.extendRat_hasDegree _ (interForm_hasDegree p d hdim F)

theorem interFormQ_tmul (d : ℕ) (hdim : topologicalKrullDim X ≤ d) (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] (s : Multiset (Additive X.Pic)) :
    interFormQ p d hdim F (s.map fun a => (1 : ℚ) ⊗ₜ[ℤ] a) = interNum p d F s :=
  (MultisetForm.extendRat_tmul _ s).trans rfl

/-- On classes of invertible sheaves the rational form is the mixed Euler difference. -/
theorem interFormQ_picQ (d : ℕ) (hdim : topologicalKrullDim X ≤ d) (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] (ls : List {L : X.Modules // IsInvertible L})
    (hl : ls.length = d) :
    interFormQ p d hdim F ((ls.map picQ : List (PicQ X)) : Multiset (PicQ X)) =
      mixedEulerDifference p (ls.map Subtype.val) F := by
  have h := interFormQ_tmul p d hdim F ((ls.map lineCls : List _) : Multiset _)
  rw [Multiset.map_coe, List.map_map] at h
  rw [show (picQ : {L : X.Modules // IsInvertible L} → PicQ X) =
    (fun a => (1 : ℚ) ⊗ₜ[ℤ] a) ∘ lineCls from rfl, h, interNum_ofLines p d F ls hl]

end rational

end SGPT.NAPotential.BJIntersect
