import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Centres of `ℤⁿ_lex`-valued valuations of the function field

Source: Section *Algebraic partial Okounkov bodies* of the chapter *The theory of Okounkov
bodies*: "Fix a rank `n` valuation `ν : ℂ(X)^× → ℤⁿ`". The value `ν(s)` of a section `s` of a
line bundle (used throughout the section, e.g. `def:Okounkov:L484`, `def:Okobd`) is the value
of the local coefficient of `s` in a frame at the *centre* of `ν`: the point `c` of `X` such that
`ν ≥ 0` on `𝒪_{X,c}` and `ν > 0` on `𝔪_{X,c}`. This file proves that on an integral scheme `X`
proper over `ℂ` every valuation `v : ℂ(X) → ℤⁿ_lex ∪ {∞}` has a unique centre (valuative criteria
of Mathlib, as in `SGPT.NAPotential.Berkovich.BerkovichPoint.exists_isCenter`), and that such a
valuation is automatically trivial on `ℂ^×` (`ℂ^×` is divisible, `ℤⁿ` has no nonzero divisible
elements).

## Main definitions and results

* `valuation_algebraMap_eq_zero`: a `ℤⁿ_lex`-valued valuation vanishes on the image of `ℂ^×`.
* `IsValuationCenter v c`: `c` is a centre of `v`.
* `IsValuationCenter.unique`: for `X` separated over `ℂ` a centre is unique.
* `exists_isValuationCenter`: for `X` proper over `ℂ` a centre exists.
* `valuationCenter f v`: the centre of `v`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Okounkov.AlgebraicValuation

open AlgebraicGeometry CategoryTheory Topology IsLocalRing

variable {n : ℕ}

/-- An integer vector divisible by every positive integer is zero. -/
theorem lex_eq_zero_of_forall_dvd (w : Lex (Fin n → ℤ))
    (h : ∀ m : ℕ, 0 < m → ∃ u : Lex (Fin n → ℤ), w = m • u) : w = 0 := by
  apply (toLex_ofLex w).symm.trans
  rw [← toLex_zero]
  congr 1
  funext i
  set N : ℕ := (ofLex w i).natAbs + 1 with hN
  obtain ⟨u, hu⟩ := h N (Nat.succ_pos _)
  have hi : ofLex w i = (N : ℤ) * ofLex u i := by
    rw [hu]
    change (N • ofLex u) i = _
    simp
  by_contra hne
  have hu0 : ofLex u i ≠ 0 := by
    rintro h0
    rw [h0, mul_zero] at hi
    exact hne hi
  have h1 : (N : ℤ) ≤ |ofLex w i| := by
    rw [hi, abs_mul, abs_of_nonneg (Nat.cast_nonneg N)]
    exact le_mul_of_one_le_right (Nat.cast_nonneg N) (Int.one_le_abs hu0)
  have h2 : |ofLex w i| = ((ofLex w i).natAbs : ℤ) := Int.abs_eq_natAbs _
  rw [hN] at h1
  push_cast at h1
  omega

/-- A `ℤⁿ_lex`-valued valuation of a field vanishes on the image of `ℂ^×` under any ring
homomorphism. -/
theorem valuation_algebraMap_eq_zero {K : Type*} [Field K]
    (v : AddValuation K (WithTop (Lex (Fin n → ℤ)))) (ψ : ℂ →+* K) {c : ℂ} (hc : c ≠ 0) :
    v (ψ c) = 0 := by
  have hψc : ψ c ≠ 0 := (map_ne_zero ψ).mpr hc
  obtain ⟨w, hw⟩ := WithTop.ne_top_iff_exists.mp ((v.ne_top_iff).mpr hψc)
  rw [← hw]
  have hw0 : w = 0 := by
    apply lex_eq_zero_of_forall_dvd
    intro m hm
    obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq c hm
    have hd0 : d ≠ 0 := by
      rintro rfl
      rw [zero_pow hm.ne'] at hd
      exact hc hd.symm
    obtain ⟨u, hu⟩ := WithTop.ne_top_iff_exists.mp
      ((v.ne_top_iff).mpr ((map_ne_zero ψ).mpr hd0))
    refine ⟨u, ?_⟩
    have := v.map_pow (ψ d) m
    rw [← map_pow, hd, ← hw, ← hu] at this
    exact_mod_cast this
  rw [hw0]
  rfl

variable {X : Scheme.{0}} [IsIntegral X]

/-- Source: `c` is a *centre* of the valuation `v` of `ℂ(X)`: `v ≥ 0` on `𝒪_{X,c}` and `v > 0`
on `𝔪_{X,c}` (through `𝒪_{X,c} → ℂ(X)`). -/
def IsValuationCenter (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) (c : X) :
    Prop :=
  (∀ g : X.presheaf.stalk c, 0 ≤ v (algebraMap (X.presheaf.stalk c) X.functionField g)) ∧
    ∀ g ∈ maximalIdeal (X.presheaf.stalk c),
      0 < v (algebraMap (X.presheaf.stalk c) X.functionField g)

variable (f : X ⟶ Spec (.of ℂ)) (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ))))

/-- The valuation ring `R_v = {g ∈ ℂ(X) : v(g) ≥ 0}`. -/
def valuationRing : ValuationSubring X.functionField where
  carrier := {g | 0 ≤ v g}
  mul_mem' {a b} ha hb := by
    change 0 ≤ v (a * b)
    rw [v.map_mul]
    exact add_nonneg ha hb
  one_mem' := by
    change 0 ≤ v 1
    rw [v.map_one]
  add_mem' {a b} ha hb := le_trans (le_min ha hb) (v.map_add a b)
  zero_mem' := by
    change 0 ≤ v 0
    rw [v.map_zero]
    exact le_top
  neg_mem' {a} ha := by
    change 0 ≤ v (-a)
    rw [v.map_neg]
    exact ha
  mem_or_inv_mem' a := by
    by_cases ha : a = 0
    · left
      change 0 ≤ v a
      rw [ha, v.map_zero]
      exact le_top
    · change 0 ≤ v a ∨ 0 ≤ v a⁻¹
      have hsum : v a + v a⁻¹ = 0 := by rw [← v.map_mul, mul_inv_cancel₀ ha, v.map_one]
      obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp ((v.ne_top_iff).mpr ha)
      obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp ((v.ne_top_iff).mpr (inv_ne_zero ha))
      rw [← hr, ← hs] at hsum ⊢
      have hrs : r + s = 0 := by exact_mod_cast hsum
      by_cases h0 : 0 ≤ r
      · left
        exact_mod_cast h0
      · right
        have hs0 : 0 ≤ s := by
          have : s = -r := eq_neg_of_add_eq_zero_right hrs
          rw [this]
          exact neg_nonneg.mpr (le_of_lt (lt_of_not_ge h0))
        exact_mod_cast hs0

theorem mem_valuationRing_iff (g : X.functionField) : g ∈ valuationRing v ↔ 0 ≤ v g := Iff.rfl

/-- The units of `R_v` are the elements of value `0`. -/
theorem isUnit_valuationRing_iff (r : valuationRing v) :
    IsUnit r ↔ v (r : X.functionField) = 0 := by
  constructor
  · rintro ⟨u, rfl⟩
    have h1 : ((u : valuationRing v) : X.functionField) *
        (((u⁻¹ : (valuationRing v)ˣ) : valuationRing v) : X.functionField) = 1 :=
      congrArg Subtype.val u.mul_inv
    have h2 : v ((u : valuationRing v) : X.functionField) +
        v (((u⁻¹ : (valuationRing v)ˣ) : valuationRing v) : X.functionField) = 0 := by
      rw [← v.map_mul, h1, v.map_one]
    exact ((add_eq_zero_iff_of_nonneg (u : valuationRing v).2
      ((u⁻¹ : (valuationRing v)ˣ) : valuationRing v).2).mp h2).1
  · intro h
    have hr0 : (r : X.functionField) ≠ 0 := by
      intro h0
      rw [h0, v.map_zero] at h
      exact WithTop.top_ne_zero h
    have hinv : (r : X.functionField)⁻¹ ∈ valuationRing v := by
      change 0 ≤ v _
      have : v (r : X.functionField) + v (r : X.functionField)⁻¹ = 0 := by
        rw [← v.map_mul, mul_inv_cancel₀ hr0, v.map_one]
      rw [h, zero_add] at this
      rw [this]
    refine isUnit_iff_exists_inv.mpr ⟨⟨_, hinv⟩, ?_⟩
    apply Subtype.ext
    change (r : X.functionField) * (r : X.functionField)⁻¹ = 1
    exact mul_inv_cancel₀ hr0

/-- The maximal ideal of `R_v` is `{v > 0}`. -/
theorem mem_maximalIdeal_valuationRing (r : valuationRing v) :
    r ∈ maximalIdeal (valuationRing v) ↔ 0 < v (r : X.functionField) := by
  rw [mem_maximalIdeal, mem_nonunits_iff, isUnit_valuationRing_iff]
  exact ⟨fun h => lt_of_le_of_ne r.2 (Ne.symm h), fun h => (ne_of_gt h)⟩

/-- The inclusion `R_v → ℂ(X)` as a morphism of commutative rings. -/
abbrev valuationRingIncl : CommRingCat.of (valuationRing v) ⟶ X.functionField :=
  CommRingCat.ofHom (algebraMap (valuationRing v) X.functionField)

variable {v}

namespace IsValuationCenter

variable {c : X}

/-- The local homomorphism `𝒪_{X,c} → R_v` of a centre. -/
def stalkHom (hc : IsValuationCenter v c) : X.presheaf.stalk c ⟶ CommRingCat.of (valuationRing v) :=
  CommRingCat.ofHom ((X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial)).hom.codRestrict
    (valuationRing v) (fun g => hc.1 g))

theorem stalkHom_comp (hc : IsValuationCenter v c) :
    hc.stalkHom ≫ valuationRingIncl v =
      X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial) := by
  ext g
  rfl

instance isLocalHom_stalkHom (hc : IsValuationCenter v c) : IsLocalHom hc.stalkHom.hom := by
  constructor
  intro g hg
  by_contra hng
  have hm : g ∈ maximalIdeal (X.presheaf.stalk c) := (mem_maximalIdeal g).mpr hng
  have hpos := hc.2 g hm
  have h0 := (isUnit_valuationRing_iff v _).mp hg
  change v (algebraMap (X.presheaf.stalk c) X.functionField g) = 0 at h0
  rw [h0] at hpos
  exact lt_irrefl _ hpos

/-- The morphism `Spec R_v → Spec 𝒪_{X,c} → X` of a centre. -/
def lift (hc : IsValuationCenter v c) : Spec (CommRingCat.of (valuationRing v)) ⟶ X :=
  Spec.map hc.stalkHom ≫ X.fromSpecStalk c

theorem lift_closedPoint (hc : IsValuationCenter v c) :
    hc.lift (closedPoint (CommRingCat.of (valuationRing v))) = c := by
  rw [lift, Scheme.Hom.comp_apply, Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]

/-- The lift of a centre extends `Spec ℂ(X) → X`. -/
theorem spec_map_incl_lift (hc : IsValuationCenter v c) :
    Spec.map (valuationRingIncl v) ≫ hc.lift = X.fromSpecStalk (genericPoint X) := by
  rw [lift, ← Category.assoc, ← Spec.map_comp, stalkHom_comp,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk]

end IsValuationCenter

variable (v) in
/-- Two morphisms `Spec R_v → Spec ℂ` agreeing after `Spec ℂ(X) → Spec R_v` are equal. -/
theorem eq_of_spec_map_incl_comp
    {g₁ g₂ : Spec (CommRingCat.of (valuationRing v)) ⟶ Spec (.of ℂ)}
    (h : Spec.map (valuationRingIncl v) ≫ g₁ = Spec.map (valuationRingIncl v) ≫ g₂) :
    g₁ = g₂ := by
  rw [← Spec.map_preimage g₁, ← Spec.map_preimage g₂] at h ⊢
  rw [← Spec.map_comp, ← Spec.map_comp] at h
  have h' := Spec.map_injective h
  congr 1
  ext a
  exact congrArg (fun φ : CommRingCat.of ℂ ⟶ X.functionField => φ.hom a) h'

/-- Source: *the centre is unique* (for `X` separated over `ℂ`). -/
theorem IsValuationCenter.unique [IsSeparated f] {c c' : X}
    (hc : IsValuationCenter v c) (hc' : IsValuationCenter v c') : c = c' := by
  let S : ValuativeCommSq f :=
    { R := valuationRing v
      K := X.functionField
      i₁ := X.fromSpecStalk (genericPoint X)
      i₂ := hc.lift ≫ f
      commSq := ⟨by rw [← hc.spec_map_incl_lift, Category.assoc]⟩ }
  have hsub : Subsingleton S.commSq.LiftStruct := IsSeparated.valuativeCriterion f S
  let l₁ : S.commSq.LiftStruct := ⟨hc.lift, hc.spec_map_incl_lift, rfl⟩
  have e1 : Spec.map (valuationRingIncl v) ≫ hc'.lift ≫ f =
      X.fromSpecStalk (genericPoint X) ≫ f := by
    rw [← Category.assoc, hc'.spec_map_incl_lift]
  have e2 : Spec.map (valuationRingIncl v) ≫ hc.lift ≫ f =
      X.fromSpecStalk (genericPoint X) ≫ f := by
    rw [← Category.assoc, hc.spec_map_incl_lift]
  let l₂ : S.commSq.LiftStruct :=
    ⟨hc'.lift, hc'.spec_map_incl_lift, eq_of_spec_map_incl_comp v (e1.trans e2.symm)⟩
  have hl : hc.lift = hc'.lift := congrArg (fun l => l.l) (Subsingleton.elim l₁ l₂)
  rw [← hc.lift_closedPoint, ← hc'.lift_closedPoint, hl]

/-- The `ℂ`-algebra map `ℂ → ℂ(X)` of the structure morphism. -/
def complexToFunctionField : CommRingCat.of ℂ ⟶ X.functionField :=
  Spec.preimage (X.fromSpecStalk (genericPoint X) ≫ f)

theorem spec_map_complexToFunctionField :
    Spec.map (complexToFunctionField f) = X.fromSpecStalk (genericPoint X) ≫ f :=
  Spec.map_preimage _

variable (v)

/-- The map `ℂ → R_v` (constants have value `0` or `∞`). -/
def complexToValuationRing : CommRingCat.of ℂ ⟶ CommRingCat.of (valuationRing v) :=
  CommRingCat.ofHom ((complexToFunctionField f).hom.codRestrict (valuationRing v) (fun c => by
    change 0 ≤ v _
    by_cases hc : c = 0
    · rw [hc, map_zero, v.map_zero]
      exact le_top
    · rw [valuation_algebraMap_eq_zero v (complexToFunctionField f).hom hc]))

theorem complexToValuationRing_comp :
    complexToValuationRing f v ≫ valuationRingIncl v = complexToFunctionField f := by
  ext a
  rfl

/-- The valuative square `Spec ℂ(X) → X`, `Spec R_v → Spec ℂ` of a valuation. -/
def valuativeSquare : ValuativeCommSq f where
  R := valuationRing v
  K := X.functionField
  i₁ := X.fromSpecStalk (genericPoint X)
  i₂ := Spec.map (complexToValuationRing f v)
  commSq := ⟨by
    rw [← Spec.map_comp]
    exact (spec_map_complexToFunctionField f).symm.trans
      (congrArg Spec.map (complexToValuationRing_comp f v).symm)⟩

/-- Source: *every valuation of `ℂ(X)` has a centre* if `X` is proper over `ℂ`. -/
theorem exists_isValuationCenter [IsProper f] : ∃ c, IsValuationCenter v c := by
  have hUC : UniversallyClosed f := inferInstance
  rw [UniversallyClosed.eq_valuativeCriterion] at hUC
  obtain ⟨l⟩ := (hUC.1 (valuativeSquare f v)).exists_lift
  let L : Spec (CommRingCat.of (valuationRing v)) ⟶ X := l.l
  have hL : Spec.map (valuationRingIncl v) ≫ L = X.fromSpecStalk (genericPoint X) := l.fac_left
  let R := valuationRing v
  let c : X := L (closedPoint (CommRingCat.of (valuationRing v)))
  have hsp : genericPoint X ⤳ c := (genericPoint_spec X).specializes trivial
  let φ : X.presheaf.stalk c ⟶ CommRingCat.of R := Scheme.stalkClosedPointTo L
  have hl : Spec.map φ ≫ X.fromSpecStalk c = L := Scheme.Spec_stalkClosedPointTo_fromSpecStalk L
  have hφ : φ ≫ valuationRingIncl v = X.presheaf.stalkSpecializes hsp := by
    apply Spec.map_injective
    apply (cancel_mono (X.fromSpecStalk c)).mp
    rw [Spec.map_comp, Category.assoc, hl, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    exact hL
  refine ⟨c, fun g => ?_, fun g hg => ?_⟩
  · have := (φ.hom g).2
    change 0 ≤ v ((X.presheaf.stalkSpecializes hsp).hom g)
    rw [← hφ]
    exact this
  · change 0 < v ((X.presheaf.stalkSpecializes hsp).hom g)
    rw [← hφ]
    change 0 < v ((φ.hom g : R) : X.functionField)
    rw [← mem_maximalIdeal_valuationRing]
    exact map_nonunit φ.hom g hg

/-- The centre `c(v)` of a valuation of `ℂ(X)`, for `X` proper over `ℂ`. -/
def valuationCenter [IsProper f] : X := (exists_isValuationCenter f v).choose

theorem isValuationCenter_valuationCenter [IsProper f] :
    IsValuationCenter v (valuationCenter f v) :=
  (exists_isValuationCenter f v).choose_spec

/-- The centre is characterised by the centre conditions. -/
theorem isValuationCenter_iff_eq [IsProper f] (c : X) :
    IsValuationCenter v c ↔ c = valuationCenter f v :=
  ⟨fun hc => hc.unique f (isValuationCenter_valuationCenter f v),
    fun h => h ▸ isValuationCenter_valuationCenter f v⟩

end SGPT.Okounkov.AlgebraicValuation
