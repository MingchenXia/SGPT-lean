import SGPT.NAPotential.BerkovichSpace
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.RingTheory.Valuation.ValuationSubring

/-! # Centres of semi-valuations

Source: `chapter_NApotential.tex`, paragraph after `def:NApotential:L878`: *the centre of a
valuation `v` is the scheme-theoretic point `c = c(v)` of `X` such that `v ≥ 0` on `𝒪_{X,c}` and
`v > 0` on the maximal ideal `𝔪_{X,c}`.  The centre is unique if it exists, and it exists if `X` is
proper.*

For a semi-valuation `v ∈ X^An` with support `Y = closure {y}` (`SGPT.NAPotential.Berkovich`),
the centre is a point `c ∈ Y`, i.e. a specialization `y ⤳ c`, and `v` is evaluated on `𝒪_{X,c}`
through the specialization map `𝒪_{X,c} → 𝒪_{X,y} → κ(y)` (whose image is `𝒪_{Y,c}`, the image of
`𝔪_{X,c}` being `𝔪_{Y,c}`).

## Main definitions and results

* `BerkovichPoint.valuationRing v`: the valuation ring `R_v = {v ≥ 0} ⊆ κ(y)`, with
  `mem_maximalIdeal_valuationRing`: its maximal ideal is `{v > 0}`.
* `BerkovichPoint.IsCenter v c`: `c` is a centre of `v`.
* `BerkovichPoint.IsCenter.unique`: for `X` separated over `ℂ` a centre is unique.
* `BerkovichPoint.exists_isCenter`: for `X` proper over `ℂ` a centre exists.
* `BerkovichPoint.center v` (for proper `X`): the centre `c(v)`, with `isCenter_center`.

The proofs use the valuative criteria of Mathlib (`ValuativeCriterion`): a centre `c` is the same
as a lift `Spec R_v → X` of `Spec κ(y) → X`, namely `Spec R_v → Spec 𝒪_{X,c} → X`.  The existence
argument follows the design of the original construction of Berkovich centres (multiplicative
seminorms over a valued base), re-proved here for additive valuations trivial on `ℂ`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.Berkovich

open AlgebraicGeometry CategoryTheory Topology IsLocalRing

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)}

namespace BerkovichPoint

theorem valAt_neg (v : BerkovichPoint f) (g : X.residueField v.support) :
    v.valAt (-g) = v.valAt g :=
  v.toAddValuation.map_neg g

theorem valAt_inv_add (v : BerkovichPoint f) {g : X.residueField v.support} (hg : g ≠ 0) :
    v.valAt g⁻¹ + v.valAt g = 0 := by
  rw [← valAt_mul, inv_mul_cancel₀ hg, valAt_one]

theorem valAt_algebraMap (v : BerkovichPoint f) {c : ℂ} (hc : c ≠ 0) :
    v.valAt ((residueComplexHom f v.support).hom c) = 0 :=
  @SourceRealValuation.map_complex' _ _ (residueComplexAlgebra f v.support) v.val c hc

/-- The valuation ring `R_v = {g ∈ κ(y) : v(g) ≥ 0}` of `v`. -/
def valuationRing (v : BerkovichPoint f) : ValuationSubring (X.residueField v.support) where
  carrier := {g | 0 ≤ v.valAt g}
  mul_mem' {a b} ha hb := by
    change 0 ≤ v.valAt (a * b)
    rw [valAt_mul]
    exact add_nonneg ha hb
  one_mem' := by
    change 0 ≤ v.valAt 1
    rw [valAt_one]
  add_mem' {a b} ha hb := le_trans (le_min ha hb) (v.min_le_valAt_add a b)
  zero_mem' := by
    change 0 ≤ v.valAt 0
    rw [valAt_zero]
    exact le_top
  neg_mem' {a} ha := by
    change 0 ≤ v.valAt (-a)
    rw [valAt_neg]
    exact ha
  mem_or_inv_mem' a := by
    by_cases ha : a = 0
    · left
      change 0 ≤ v.valAt a
      rw [ha, valAt_zero]
      exact le_top
    · change 0 ≤ v.valAt a ∨ 0 ≤ v.valAt a⁻¹
      have hsum := v.valAt_inv_add ha
      have hne : v.valAt a ≠ ⊤ := fun h => ha ((v.valAt_eq_top_iff a).mp h)
      have hne' : v.valAt a⁻¹ ≠ ⊤ := fun h => (inv_ne_zero ha) ((v.valAt_eq_top_iff _).mp h)
      obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hne
      obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp hne'
      rw [← hr, ← hs] at hsum ⊢
      have hrs : s + r = 0 := by exact_mod_cast hsum
      by_cases h0 : 0 ≤ r
      · left
        exact_mod_cast h0
      · right
        have : 0 ≤ s := by linarith
        exact_mod_cast this

theorem mem_valuationRing_iff (v : BerkovichPoint f) (g : X.residueField v.support) :
    g ∈ v.valuationRing ↔ 0 ≤ v.valAt g := Iff.rfl

/-- The units of `R_v` are the elements of value `0`. -/
theorem isUnit_valuationRing_iff (v : BerkovichPoint f) (r : v.valuationRing) :
    IsUnit r ↔ v.valAt (r : X.residueField v.support) = 0 := by
  constructor
  · rintro ⟨u, rfl⟩
    have h1 : ((u : v.valuationRing) : X.residueField v.support) *
        (((u⁻¹ : (v.valuationRing)ˣ) : v.valuationRing) : X.residueField v.support) = 1 :=
      congrArg Subtype.val u.mul_inv
    have h2 : v.valAt ((u : v.valuationRing) : X.residueField v.support) +
        v.valAt (((u⁻¹ : (v.valuationRing)ˣ) : v.valuationRing) : X.residueField v.support) = 0 := by
      rw [← valAt_mul, h1, valAt_one]
    exact ((add_eq_zero_iff_of_nonneg (u : v.valuationRing).2
      ((u⁻¹ : (v.valuationRing)ˣ) : v.valuationRing).2).mp h2).1
  · intro h
    have hr0 : (r : X.residueField v.support) ≠ 0 := by
      intro h0
      rw [h0, valAt_zero] at h
      exact WithTop.top_ne_zero h
    have hinv : (r : X.residueField v.support)⁻¹ ∈ v.valuationRing := by
      change 0 ≤ v.valAt _
      have := v.valAt_inv_add hr0
      rw [h, add_zero] at this
      rw [this]
    refine isUnit_iff_exists_inv.mpr ⟨⟨_, hinv⟩, ?_⟩
    apply Subtype.ext
    change (r : X.residueField v.support) * (r : X.residueField v.support)⁻¹ = 1
    exact mul_inv_cancel₀ hr0

/-- The maximal ideal of `R_v` is `{v > 0}`. -/
theorem mem_maximalIdeal_valuationRing (v : BerkovichPoint f) (r : v.valuationRing) :
    r ∈ maximalIdeal v.valuationRing ↔ 0 < v.valAt (r : X.residueField v.support) := by
  rw [mem_maximalIdeal, mem_nonunits_iff, isUnit_valuationRing_iff]
  exact ⟨fun h => lt_of_le_of_ne r.2 (Ne.symm h), fun h => (ne_of_gt h)⟩

/-- The specialization map `𝒪_{X,c} → 𝒪_{X,y} → κ(y)` for `y ⤳ c`. -/
def specializationMap {y c : X} (h : y ⤳ c) : X.presheaf.stalk c ⟶ X.residueField y :=
  X.presheaf.stalkSpecializes h ≫ X.residue y

/-- Source: `c` is a *centre* of the semi-valuation `v`: `c` lies on the support of `v`
(`y ⤳ c`), `v ≥ 0` on `𝒪_{X,c}` and `v > 0` on `𝔪_{X,c}`. -/
def IsCenter (v : BerkovichPoint f) (c : X) : Prop :=
  ∃ h : v.support ⤳ c, (∀ g : X.presheaf.stalk c, 0 ≤ v.valAt ((specializationMap h).hom g)) ∧
    ∀ g ∈ maximalIdeal (X.presheaf.stalk c), 0 < v.valAt ((specializationMap h).hom g)

/-- The inclusion `R_v → κ(y)` as a morphism of commutative rings. -/
abbrev valuationRingIncl (v : BerkovichPoint f) :
    CommRingCat.of v.valuationRing ⟶ X.residueField v.support :=
  CommRingCat.ofHom (algebraMap v.valuationRing (X.residueField v.support))

theorem valuationRingIncl_injective (v : BerkovichPoint f) :
    Function.Injective (valuationRingIncl v).hom :=
  Subtype.val_injective

namespace IsCenter

variable {v : BerkovichPoint f} {c : X}

/-- The local homomorphism `𝒪_{X,c} → R_v` of a centre. -/
def stalkHom (hc : v.IsCenter c) : X.presheaf.stalk c ⟶ CommRingCat.of v.valuationRing :=
  CommRingCat.ofHom ((specializationMap hc.choose).hom.codRestrict v.valuationRing
    (fun g => hc.choose_spec.1 g))

theorem stalkHom_comp (hc : v.IsCenter c) :
    hc.stalkHom ≫ valuationRingIncl v = specializationMap hc.choose := by
  ext g
  rfl

instance isLocalHom_stalkHom (hc : v.IsCenter c) : IsLocalHom hc.stalkHom.hom := by
  constructor
  intro g hg
  by_contra hng
  have hm : g ∈ maximalIdeal (X.presheaf.stalk c) := (mem_maximalIdeal g).mpr hng
  have hpos := hc.choose_spec.2 g hm
  have h0 := (isUnit_valuationRing_iff v _).mp hg
  change v.valAt ((specializationMap hc.choose).hom g) = 0 at h0
  rw [h0] at hpos
  exact lt_irrefl _ hpos

/-- The morphism `Spec R_v → Spec 𝒪_{X,c} → X` of a centre. -/
def lift (hc : v.IsCenter c) : Spec (CommRingCat.of v.valuationRing) ⟶ X :=
  Spec.map hc.stalkHom ≫ X.fromSpecStalk c

theorem lift_closedPoint (hc : v.IsCenter c) :
    hc.lift (closedPoint (CommRingCat.of v.valuationRing)) = c := by
  rw [lift, Scheme.Hom.comp_apply, Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]

/-- The lift of a centre extends `Spec κ(y) → X`. -/
theorem spec_map_incl_lift (hc : v.IsCenter c) :
    Spec.map (valuationRingIncl v) ≫ hc.lift = X.fromSpecResidueField v.support := by
  rw [lift, ← Category.assoc, ← Spec.map_comp, stalkHom_comp, specializationMap, Spec.map_comp,
    Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  rfl

end IsCenter

/-- Two morphisms `Spec R_v → Spec ℂ` agreeing after `Spec κ(y) → Spec R_v` are equal. -/
theorem eq_of_spec_map_incl_comp (v : BerkovichPoint f)
    {g₁ g₂ : Spec (CommRingCat.of v.valuationRing) ⟶ Spec (.of ℂ)}
    (h : Spec.map (valuationRingIncl v) ≫ g₁ = Spec.map (valuationRingIncl v) ≫ g₂) : g₁ = g₂ := by
  rw [← Spec.map_preimage g₁, ← Spec.map_preimage g₂] at h ⊢
  rw [← Spec.map_comp, ← Spec.map_comp] at h
  have h' := Spec.map_injective h
  congr 1
  ext a
  exact congrArg (fun φ : CommRingCat.of ℂ ⟶ X.residueField v.support => φ.hom a) h'

/-- Source: *the centre is unique if it exists* (for `X` separated over `ℂ`, e.g. a variety). -/
theorem IsCenter.unique [IsSeparated f] {v : BerkovichPoint f} {c c' : X} (hc : v.IsCenter c)
    (hc' : v.IsCenter c') : c = c' := by
  let S : ValuativeCommSq f :=
    { R := v.valuationRing
      K := X.residueField v.support
      i₁ := X.fromSpecResidueField v.support
      i₂ := hc.lift ≫ f
      commSq := ⟨by rw [← hc.spec_map_incl_lift, Category.assoc]⟩ }
  have hsub : Subsingleton S.commSq.LiftStruct := IsSeparated.valuativeCriterion f S
  let l₁ : S.commSq.LiftStruct := ⟨hc.lift, hc.spec_map_incl_lift, rfl⟩
  have e1 : Spec.map (valuationRingIncl v) ≫ hc'.lift ≫ f = X.fromSpecResidueField v.support ≫ f := by
    rw [← Category.assoc, hc'.spec_map_incl_lift]
  have e2 : Spec.map (valuationRingIncl v) ≫ hc.lift ≫ f = X.fromSpecResidueField v.support ≫ f := by
    rw [← Category.assoc, hc.spec_map_incl_lift]
  let l₂ : S.commSq.LiftStruct :=
    ⟨hc'.lift, hc'.spec_map_incl_lift, eq_of_spec_map_incl_comp v (e1.trans e2.symm)⟩
  have hl : hc.lift = hc'.lift := congrArg (fun l => l.l) (Subsingleton.elim l₁ l₂)
  rw [← hc.lift_closedPoint, ← hc'.lift_closedPoint, hl]

/-- The map `ℂ → R_v` (constants have value `0` or `∞`). -/
def complexToValuationRing (v : BerkovichPoint f) : CommRingCat.of ℂ ⟶ CommRingCat.of v.valuationRing :=
  CommRingCat.ofHom ((residueComplexHom f v.support).hom.codRestrict v.valuationRing (fun c => by
    change 0 ≤ v.valAt _
    by_cases hc : c = 0
    · rw [hc, map_zero, valAt_zero]
      exact le_top
    · rw [v.valAt_algebraMap hc]))

theorem complexToValuationRing_comp (v : BerkovichPoint f) :
    complexToValuationRing v ≫ valuationRingIncl v = residueComplexHom f v.support := by
  ext a
  rfl

/-- The valuative square `Spec κ(y) → X`, `Spec R_v → Spec ℂ` of a semi-valuation. -/
def valuativeSquare (v : BerkovichPoint f) : ValuativeCommSq f where
  R := v.valuationRing
  K := X.residueField v.support
  i₁ := X.fromSpecResidueField v.support
  i₂ := Spec.map (complexToValuationRing v)
  commSq := ⟨by
    rw [← Spec.map_comp]
    exact (spec_map_residueComplexHom f v.support).symm.trans
      (congrArg Spec.map (complexToValuationRing_comp v).symm)⟩

/-- Source: *the centre exists if `X` is proper*. -/
theorem exists_isCenter [IsProper f] (v : BerkovichPoint f) : ∃ c, v.IsCenter c := by
  have hUC : UniversallyClosed f := inferInstance
  rw [UniversallyClosed.eq_valuativeCriterion] at hUC
  obtain ⟨l⟩ := (hUC.1 (valuativeSquare v)).exists_lift
  let L : Spec (CommRingCat.of v.valuationRing) ⟶ X := l.l
  have hL : Spec.map (valuationRingIncl v) ≫ L = X.fromSpecResidueField v.support := l.fac_left
  let R := v.valuationRing
  let c : X := L (closedPoint (CommRingCat.of v.valuationRing))
  -- the support is a generization of `c`
  have hgen : L (Spec.map (valuationRingIncl v) (closedPoint (X.residueField v.support))) =
      v.support := by
    rw [← Scheme.Hom.comp_apply, hL]
    exact Scheme.fromSpecResidueField_apply v.support _
  have hsp : v.support ⤳ c := by
    rw [← hgen]
    exact (specializes_closedPoint _).map L.continuous
  -- the stalk map of the lift
  let φ : X.presheaf.stalk c ⟶ CommRingCat.of R := Scheme.stalkClosedPointTo L
  have hl : Spec.map φ ≫ X.fromSpecStalk c = L := Scheme.Spec_stalkClosedPointTo_fromSpecStalk L
  have hφ : φ ≫ valuationRingIncl v = specializationMap hsp := by
    apply Spec.map_injective
    apply (cancel_mono (X.fromSpecStalk c)).mp
    rw [Spec.map_comp, Category.assoc, hl, specializationMap, Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    exact hL
  refine ⟨c, hsp, fun g => ?_, fun g hg => ?_⟩
  · have := (φ.hom g).2
    rw [← hφ]
    exact this
  · rw [← hφ]
    change 0 < v.valAt ((φ.hom g : R) : X.residueField v.support)
    rw [← mem_maximalIdeal_valuationRing]
    exact map_nonunit φ.hom g hg

variable [IsProper f]

/-- The centre `c(v)` of a semi-valuation on `X` proper over `ℂ`. -/
def center (v : BerkovichPoint f) : X := (exists_isCenter v).choose

theorem isCenter_center (v : BerkovichPoint f) : v.IsCenter v.center :=
  (exists_isCenter v).choose_spec

/-- The centre is characterised by the centre conditions. -/
theorem isCenter_iff_eq_center (v : BerkovichPoint f) (c : X) : v.IsCenter c ↔ c = v.center :=
  ⟨fun hc => hc.unique v.isCenter_center, fun h => h ▸ v.isCenter_center⟩

/-- The support of `v` specializes to its centre: `c(v) ∈ closure {y}`. -/
theorem support_specializes_center (v : BerkovichPoint f) : v.support ⤳ v.center :=
  v.isCenter_center.choose

end BerkovichPoint

end SGPT.NAPotential.Berkovich

end
