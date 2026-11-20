import SGPT.NAPotential.BerkovichCenter
import Mathlib.AlgebraicGeometry.OrderOfVanishing
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Divisorial valuations `X^Div`

Source: `chapter_NApotential.tex`, Section *Valuations* of the recap of Boucksom–Jonsson's theory:
*a divisorial valuation on `X` is a valuation of the form `t ord_E`, where `t ∈ ℚ_{>0}` and `E` is
a prime divisor over `X`.  The set of divisorial valuations on `X` is denoted by `X^Div`.  When
`ℚ_{>0}` is replaced by `ℝ_{>0}`, we can similarly define a space `X^Div_ℝ`.*

## Formal setting

A *prime divisor over `X`* (`PrimeDivisorOver X`) is a prime divisor `E` on a normal integral
(locally Noetherian) scheme `Y` with a proper birational morphism `π : Y → X`; birational means
dominant with bijective map of function fields `κ(π η_Y) → κ(η_Y)` (`η_Y` the generic point).
`E` is recorded by its generic point `z ∈ Y`, a point of codimension one
(`Order.coheight z = 1`).  Normality makes `𝒪_{Y,E}` a discrete valuation ring
(`PrimeDivisorOver.isDiscreteValuationRing`), and `ord_E` is Mathlib's order of vanishing
`Scheme.ord` at `z`, transported to `κ(π η_Y) = ℂ(X)` along `π`.

## Main definitions and results

* `PrimeDivisorOver.ordVal E t` (`t > 0`): the semi-valuation `t ord_E ∈ X^An`; it is a valuation
  of `ℂ(X)` (`ordVal_support`: its support is the generic point of `X`).  That `t ord_E`
  satisfies the four conditions of `def:NApotential:L878` (in particular it is trivial on `ℂ^×`,
  `ord_algebraMap`) is part of the construction.
* `divisorialSet f = X^Div` (`t ∈ ℚ_{>0}`) and `divisorialSetReal f = X^Div_ℝ` (`t ∈ ℝ_{>0}`),
  with `divisorialSet_subset_real`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.Berkovich

open AlgebraicGeometry CategoryTheory Topology IsLocalRing

/-- A prime divisor over `X`: a prime divisor `E` (generic point `point`, of codimension one) on a
normal integral locally Noetherian scheme `Y` together with a proper birational morphism
`π : Y ⟶ X`. -/
structure PrimeDivisorOver (X : Scheme.{0}) where
  /-- The birational model on which `E` lives. -/
  Y : Scheme.{0}
  /-- The proper birational morphism `π : Y → X`. -/
  π : Y ⟶ X
  [isIntegral : IsIntegral Y]
  [isLocallyNoetherian : IsLocallyNoetherian Y]
  /-- `Y` is normal. -/
  normal : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)
  [isProper : IsProper π]
  [isDominant : IsDominant π]
  /-- `π` induces an isomorphism of function fields. -/
  birational : Function.Bijective (π.residueFieldMap (genericPoint Y)).hom
  /-- The generic point of the prime divisor `E ⊆ Y`. -/
  point : Y
  /-- `E` has codimension one. -/
  coheight_point : Order.coheight point = 1

namespace PrimeDivisorOver

variable {X : Scheme.{0}} (E : PrimeDivisorOver X)

attribute [instance] isIntegral isLocallyNoetherian isProper isDominant

/-- `𝒪_{Y,E}` is a discrete valuation ring (`Y` is normal and `E` has codimension one). -/
instance isDiscreteValuationRing : IsDiscreteValuationRing (E.Y.presheaf.stalk E.point) := by
  have hdim : ringKrullDim (E.Y.presheaf.stalk E.point) = 1 := by
    rw [ringKrullDim_stalk_eq_coheight, E.coheight_point]
    rfl
  have hnf : ¬IsField (E.Y.presheaf.stalk E.point) := by
    intro hF
    rw [ringKrullDim_eq_zero_of_isField hF] at hdim
    exact absurd hdim (by decide)
  have : Ring.KrullDimLE 1 (E.Y.presheaf.stalk E.point) :=
    krullDimLE_of_coheight_le (le_of_eq E.coheight_point)
  have := E.normal E.point
  have hm : maximalIdeal (E.Y.presheaf.stalk E.point) ≠ ⊥ :=
    isField_iff_maximalIdeal_eq.not.mp hnf
  have key := (IsDiscreteValuationRing.TFAE (E.Y.presheaf.stalk E.point) hnf).out 0 3
  refine key.mpr ⟨inferInstance, maximalIdeal _, ⟨hm, inferInstance⟩, fun P hP => ?_⟩
  exact (IsLocalRing.eq_maximalIdeal (hP.2.isMaximal_of_ne_bot hP.1))

/-- The identification `κ(η_Y) ≅ ℂ(Y)` (the residue map of the field `ℂ(Y)`). -/
def residueEquiv : E.Y.functionField ≃+* E.Y.residueField (genericPoint E.Y) :=
  RingEquiv.ofBijective (E.Y.residue (genericPoint E.Y)).hom
    ⟨(E.Y.residue (genericPoint E.Y)).hom.injective, E.Y.residue_surjective _⟩

/-- The pullback `κ(π η_Y) → ℂ(Y)` of rational functions along `π`. -/
def pullback : X.residueField (E.π (genericPoint E.Y)) →+* E.Y.functionField :=
  E.residueEquiv.symm.toRingHom.comp (E.π.residueFieldMap (genericPoint E.Y)).hom

theorem pullback_injective : Function.Injective E.pullback :=
  E.pullback.injective

/-- `ord_E` of a rational function on `X`. -/
def ord (g : X.residueField (E.π (genericPoint E.Y))) : ℤ :=
  Scheme.ord (E.pullback g) E.point

theorem ord_mul {g h : X.residueField (E.π (genericPoint E.Y))} (hg : g ≠ 0) (hh : h ≠ 0) :
    E.ord (g * h) = E.ord g + E.ord h := by
  unfold ord
  rw [map_mul]
  exact Scheme.ord_mul ((map_ne_zero_iff _ E.pullback_injective).mpr hg)
    ((map_ne_zero_iff _ E.pullback_injective).mpr hh)

theorem ord_pow {g : X.residueField (E.π (genericPoint E.Y))} (hg : g ≠ 0) (m : ℕ) :
    E.ord (g ^ m) = m * E.ord g := by
  induction m with
  | zero =>
    simp only [pow_zero, Nat.cast_zero, zero_mul]
    unfold ord
    rw [map_one]
    have := Scheme.ord_mul (X := E.Y) (x := E.point) (one_ne_zero) (one_ne_zero)
    rw [mul_one] at this
    omega
  | succ m ih =>
    rw [pow_succ, E.ord_mul (pow_ne_zero m hg) hg, ih]
    push_cast
    ring

theorem min_le_ord_add {g h : X.residueField (E.π (genericPoint E.Y))} (hgh : g + h ≠ 0) :
    min (E.ord g) (E.ord h) ≤ E.ord (g + h) := by
  unfold ord
  rw [map_add]
  exact Scheme.ord_add (by rwa [← map_add, map_ne_zero_iff _ E.pullback_injective])

/-- `ord_E` vanishes on the nonzero constants: every nonzero integer value would have to be
divisible by every `m ≥ 1`, since `ℂ^×` is divisible. -/
theorem ord_algebraMap (φ : CommRingCat.of ℂ ⟶ X.residueField (E.π (genericPoint E.Y)))
    {c : ℂ} (hc : c ≠ 0) : E.ord (φ.hom c) = 0 := by
  have hdvd : ∀ m : ℕ, 0 < m → (m : ℤ) ∣ E.ord (φ.hom c) := by
    intro m hm
    obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq c hm
    have hd0 : φ.hom d ≠ 0 := by
      intro h0
      apply hc
      rw [← hd]
      have : d = 0 := by
        by_contra hne
        exact (map_ne_zero_iff _ φ.hom.injective).mpr hne h0
      rw [this, zero_pow hm.ne']
    rw [← hd, map_pow, E.ord_pow hd0]
    exact Dvd.intro _ rfl
  set k := E.ord (φ.hom c)
  by_contra hk
  have h1 := hdvd (k.natAbs + 1) (Nat.succ_pos _)
  have h2 := Int.natAbs_dvd_natAbs.mpr h1
  rw [Int.natAbs_natCast] at h2
  have h3 := Nat.le_of_dvd (Int.natAbs_pos.mpr hk) h2
  omega

variable {f : X ⟶ Spec (.of ℂ)}

/-- The function `t ord_E : ℂ(X) → (-∞, ∞]`. -/
def ordFun (t : ℝ) (g : X.residueField (E.π (genericPoint E.Y))) : WithTop ℝ :=
  open Classical in if g = 0 then ⊤ else ((t * E.ord g : ℝ) : WithTop ℝ)

theorem ordFun_of_ne_zero (t : ℝ) {g : X.residueField (E.π (genericPoint E.Y))} (hg : g ≠ 0) :
    E.ordFun t g = ((t * E.ord g : ℝ) : WithTop ℝ) := by
  classical
  simp [ordFun, hg]

variable (f) in
/-- The divisorial semi-valuation `t ord_E ∈ X^An` (`t > 0`): a valuation of `ℂ(X)` in the sense
of `def:NApotential:L878`. -/
def ordVal (t : ℝ) (ht : 0 < t) : BerkovichPoint f where
  support := E.π (genericPoint E.Y)
  val :=
    letI := residueComplexAlgebra f (E.π (genericPoint E.Y))
    { toFun := E.ordFun t
      eq_top_iff' := fun g => by
        by_cases hg : g = 0
        · classical
          simp [ordFun, hg]
        · rw [E.ordFun_of_ne_zero t hg]
          exact ⟨fun h => absurd h WithTop.coe_ne_top, fun h => absurd h hg⟩
      map_mul' := fun g h => by
        classical
        by_cases hg : g = 0
        · simp [ordFun, hg]
        by_cases hh : h = 0
        · simp [ordFun, hh]
        rw [E.ordFun_of_ne_zero t (mul_ne_zero hg hh), E.ordFun_of_ne_zero t hg,
          E.ordFun_of_ne_zero t hh, E.ord_mul hg hh, ← WithTop.coe_add]
        congr 1
        push_cast
        ring
      min_le_map_add' := fun g h => by
        classical
        by_cases hgh : g + h = 0
        · simp [ordFun, hgh]
        by_cases hg : g = 0
        · simp [hg]
        by_cases hh : h = 0
        · simp [hh]
        rw [E.ordFun_of_ne_zero t hgh, E.ordFun_of_ne_zero t hg, E.ordFun_of_ne_zero t hh]
        have hle := E.min_le_ord_add hgh
        rw [← WithTop.coe_min, WithTop.coe_le_coe]
        rcases le_total (E.ord g) (E.ord h) with h1 | h1
        · rw [min_eq_left h1] at hle
          rw [min_eq_left (mul_le_mul_of_nonneg_left (by exact_mod_cast h1) ht.le)]
          exact mul_le_mul_of_nonneg_left (by exact_mod_cast hle) ht.le
        · rw [min_eq_right h1] at hle
          rw [min_eq_right (mul_le_mul_of_nonneg_left (by exact_mod_cast h1) ht.le)]
          exact mul_le_mul_of_nonneg_left (by exact_mod_cast hle) ht.le
      map_complex' := fun c hc => by
        have hne : (residueComplexHom f (E.π (genericPoint E.Y))).hom c ≠ 0 :=
          (map_ne_zero_iff _ (residueComplexHom f _).hom.injective).mpr hc
        change E.ordFun t ((residueComplexHom f (E.π (genericPoint E.Y))).hom c) = 0
        rw [E.ordFun_of_ne_zero t hne, E.ord_algebraMap _ hc]
        simp }

theorem ordVal_support (t : ℝ) (ht : 0 < t) :
    (E.ordVal f t ht).support = E.π (genericPoint E.Y) := rfl

theorem ordVal_valAt (t : ℝ) (ht : 0 < t) {g : X.residueField (E.π (genericPoint E.Y))}
    (hg : g ≠ 0) : (E.ordVal f t ht).valAt g = ((t * E.ord g : ℝ) : WithTop ℝ) := by
  change E.ordFun t g = _
  exact E.ordFun_of_ne_zero t hg

/-- The image of the generic point of `Y` is the generic point of `X` (`π` is dominant). -/
theorem isGenericPoint_image [IrreducibleSpace X] :
    E.π (genericPoint E.Y) = genericPoint X := by
  have hdense : Dense (Set.range E.π) := E.π.denseRange
  have hcl : closure ({E.π (genericPoint E.Y)} : Set X) = Set.univ := by
    apply Set.eq_univ_of_univ_subset
    rw [← hdense.closure_eq]
    apply closure_minimal _ isClosed_closure
    rintro _ ⟨y, rfl⟩
    have hy : genericPoint E.Y ⤳ y := genericPoint_specializes y
    exact specializes_iff_mem_closure.mp (hy.map E.π.continuous)
  exact ((genericPoint_spec X).eq (by exact hcl)).symm

/-- `t ord_E` is a valuation of `ℂ(X)`: its support is the generic point of `X`. -/
theorem ordVal_support_eq_genericPoint [IrreducibleSpace X] (t : ℝ) (ht : 0 < t) :
    (E.ordVal f t ht).support = genericPoint X :=
  E.isGenericPoint_image

end PrimeDivisorOver

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ))

/-- `X^Div`: the divisorial valuations `t ord_E`, `t ∈ ℚ_{>0}`, `E` a prime divisor over `X`. -/
def divisorialSet : Set (BerkovichPoint f) :=
  {v | ∃ (E : PrimeDivisorOver X) (t : ℚ) (ht : (0 : ℝ) < t), v = E.ordVal f t ht}

/-- `X^Div_ℝ`: the valuations `t ord_E`, `t ∈ ℝ_{>0}`. -/
def divisorialSetReal : Set (BerkovichPoint f) :=
  {v | ∃ (E : PrimeDivisorOver X) (t : ℝ) (ht : 0 < t), v = E.ordVal f t ht}

theorem divisorialSet_subset_real : divisorialSet f ⊆ divisorialSetReal f := by
  rintro v ⟨E, t, ht, rfl⟩
  exact ⟨E, t, ht, rfl⟩

end SGPT.NAPotential.Berkovich

end
