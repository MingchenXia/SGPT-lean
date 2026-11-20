import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# Admissible flags on complex algebraic varieties

Source `def:admfl` (chapter *The theory of Okounkov bodies*, Section *Flags and valuations*,
algebraic setting). Let `X` be an irreducible (normal projective) complex variety of dimension
`n`. An *admissible flag* is a flag of subvarieties

`X = Y₀ ⊇ Y₁ ⊇ ⋯ ⊇ Yₙ`

such that `Yᵢ` is irreducible of codimension `i` and is smooth at the point `Yₙ`.

We work with an arbitrary scheme `X` together with its structure morphism `f : X ⟶ Spec ℂ`
(the standing hypotheses of the source — irreducible, normal, projective, of dimension `n` —
are hypotheses on `X`, not part of the definition, and are imposed by the consumers).
A subvariety is recorded by its underlying closed irreducible subset `Yᵢ ⊆ X`, which
determines the reduced induced closed subscheme.  Its codimension is the codimension of its
generic point `ηᵢ`, i.e. `Order.coheight ηᵢ = dim 𝒪_{X,ηᵢ}` (mathlib's
`AlgebraicGeometry.ringKrullDim_stalk_eq_coheight`).

Smoothness of the reduced subvariety `Yᵢ` at a point `p ∈ Yᵢ` is smoothness of its local ring:
the local ring of the reduced induced structure on `Yᵢ = closure {ηᵢ}` at `p` is
`𝒪_{X,p} ⧸ 𝔭`, where `𝔭` is the prime of germs vanishing on `Yᵢ`, namely the preimage of the
maximal ideal of `𝒪_{X,ηᵢ}` under the generization map `𝒪_{X,p} → 𝒪_{X,ηᵢ}`.  Following
mathlib (`Algebra.IsSmoothAt`, Stacks 00TB), "smooth over `ℂ` at `p`" means that this local
ring is formally smooth over `ℂ`, with the `ℂ`-algebra structure induced by `f`.

## Main definitions

* `SGPT.Okounkov.stalkComplexAlgebra` : the `ℂ`-algebra structure of a stalk.
* `SGPT.Okounkov.generizationIdeal` : the prime of `𝒪_{X,p}` cut out by a generization of `p`.
* `SGPT.Okounkov.IsSubvarietySmoothAt` : a closed irreducible subset is smooth at a point.
* `SGPT.Okounkov.IsAdmissibleFlag` : source `def:admfl`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov

open AlgebraicGeometry CategoryTheory Topology

variable {X : Scheme.{0}}

/-- The `ℂ`-algebra structure of the stalk `𝒪_{X,x}` induced by the structure morphism
`f : X ⟶ Spec ℂ`: `ℂ ≅ Γ(Spec ℂ) → Γ(X) → 𝒪_{X,x}`. -/
abbrev stalkComplexAlgebra (f : X ⟶ Spec (.of ℂ)) (x : X) : Algebra ℂ (X.presheaf.stalk x) :=
  ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ f.appTop ≫
    X.presheaf.germ ⊤ x trivial).hom.toAlgebra

/-- For a generization `η ⤳ x`, the prime ideal of `𝒪_{X,x}` of germs vanishing on
`closure {η}`: the preimage of the maximal ideal of `𝒪_{X,η}` under the generization map
`𝒪_{X,x} → 𝒪_{X,η}`. -/
def generizationIdeal {η x : X} (h : η ⤳ x) : Ideal (X.presheaf.stalk x) :=
  (IsLocalRing.maximalIdeal (X.presheaf.stalk η)).comap (X.presheaf.stalkSpecializes h).hom

instance generizationIdeal_isPrime {η x : X} (h : η ⤳ x) : (generizationIdeal h).IsPrime :=
  Ideal.comap_isPrime _ _

/-- The generic point of a closed irreducible subset specializes to each of its points. -/
theorem genericPoint_specializes {Z : Set X} (hZ : IsIrreducible Z) (hZc : IsClosed Z) {x : X}
    (hx : x ∈ Z) : hZ.genericPoint ⤳ x :=
  (hZ.isGenericPoint_genericPoint hZc).specializes hx

/-- The generic point of a closed irreducible subset lies in it. -/
theorem genericPoint_mem {Z : Set X} (hZ : IsIrreducible Z) (hZc : IsClosed Z) :
    hZ.genericPoint ∈ Z :=
  (hZ.isGenericPoint_genericPoint hZc).mem

/-- A closed irreducible subset `Z ⊆ X` (with its reduced induced structure) is *smooth at the
point* `x ∈ Z`: its local ring `𝒪_{Z,x} = 𝒪_{X,x} ⧸ 𝔭_Z` is formally smooth over `ℂ`. -/
def IsSubvarietySmoothAt (f : X ⟶ Spec (.of ℂ)) {Z : Set X} (hZ : IsIrreducible Z)
    (hZc : IsClosed Z) {x : X} (hx : x ∈ Z) : Prop :=
  letI := stalkComplexAlgebra f x
  Algebra.FormallySmooth ℂ (X.presheaf.stalk x ⧸ generizationIdeal (genericPoint_specializes hZ hZc hx))

/-- Source `def:admfl`. An *admissible flag* `Y₀ ⊇ ⋯ ⊇ Yₙ` on the complex variety `X`
(with structure morphism `f`): every `Yᵢ` is a closed irreducible subset (a subvariety) of
codimension `i`, `Y₀ = X`, the flag is decreasing, and every `Yᵢ` is smooth at the point
`Yₙ`, i.e. at the generic point `p` of `Yₙ` (which is the unique point of `Yₙ` when `X` has
dimension `n`, see `IsAdmissibleFlag.eq_singleton`). -/
structure IsAdmissibleFlag (f : X ⟶ Spec (.of ℂ)) (n : ℕ) (Y : Fin (n + 1) → Set X) : Prop where
  isClosed : ∀ i, IsClosed (Y i)
  isIrreducible : ∀ i, IsIrreducible (Y i)
  zero_eq : Y 0 = Set.univ
  antitone : Antitone Y
  codim_eq : ∀ i, Order.coheight (isIrreducible i).genericPoint = (i : ℕ)
  smoothAt : ∀ i, IsSubvarietySmoothAt f (isIrreducible i) (isClosed i)
    (antitone (Fin.le_last i) (genericPoint_mem (isIrreducible (Fin.last n))
      (isClosed (Fin.last n))))

namespace IsAdmissibleFlag

variable {f : X ⟶ Spec (.of ℂ)} {n : ℕ} {Y : Fin (n + 1) → Set X}

/-- The point `Yₙ` of an admissible flag: the generic point of the last member. -/
def point (hY : IsAdmissibleFlag f n Y) : X :=
  (hY.isIrreducible (Fin.last n)).genericPoint

theorem point_mem (hY : IsAdmissibleFlag f n Y) (i : Fin (n + 1)) : hY.point ∈ Y i :=
  hY.antitone (Fin.le_last i)
    (genericPoint_mem (hY.isIrreducible (Fin.last n)) (hY.isClosed (Fin.last n)))

/-- Each member of an admissible flag is the closure of its generic point. -/
theorem closure_genericPoint (hY : IsAdmissibleFlag f n Y) (i : Fin (n + 1)) :
    closure {(hY.isIrreducible i).genericPoint} = Y i :=
  (hY.isIrreducible i).closure_genericPoint (hY.isClosed i)

/-- The codimension of `Yᵢ`, i.e. the Krull dimension of the local ring of `X` at its generic
point, is `i`. -/
theorem ringKrullDim_stalk_genericPoint (hY : IsAdmissibleFlag f n Y) (i : Fin (n + 1)) :
    ringKrullDim (X.presheaf.stalk (hY.isIrreducible i).genericPoint) = (i : ℕ) := by
  rw [ringKrullDim_stalk_eq_coheight, hY.codim_eq i]
  rfl

/-- The point `Yₙ` is closed when `X` has Krull dimension `n`: every proper specialization
of the point would increase its codimension beyond `n`. In that case `Yₙ` is the singleton
`{point}`. -/
theorem eq_singleton (hY : IsAdmissibleFlag f n Y)
    (hdim : ∀ x : X, Order.coheight x ≤ n) : Y (Fin.last n) = {hY.point} := by
  have hlast := hY.codim_eq (Fin.last n)
  have hclosed : ∀ y : X, hY.point ⤳ y → y = hY.point := by
    intro y hy
    by_contra hne
    have hle : y ≤ hY.point := hy
    have hlt : y < hY.point :=
      lt_of_le_not_ge hle fun hge => hne (Specializes.antisymm hge hy).eq
    have h1 : Order.coheight hY.point + 1 ≤ Order.coheight y :=
      Order.coheight_add_one_le hlt
    have h2 : Order.coheight hY.point = (n : ℕ∞) := by
      simpa [point] using hlast
    rw [h2] at h1
    have h4 : (n : ℕ∞) + 1 ≤ n := h1.trans (hdim y)
    have h5 : ((n + 1 : ℕ) : ℕ∞) ≤ (n : ℕ∞) := by exact_mod_cast h4
    exact absurd (ENat.natCast_le_natCast.mp h5) (by omega)
  rw [← hY.closure_genericPoint (Fin.last n)]
  ext y
  simp only [Set.mem_singleton_iff]
  constructor
  · intro hy
    exact hclosed y (specializes_iff_mem_closure.mpr hy)
  · rintro rfl
    exact subset_closure rfl

end IsAdmissibleFlag

end SGPT.Okounkov
