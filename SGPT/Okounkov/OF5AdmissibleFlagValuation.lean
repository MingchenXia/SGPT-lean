import SGPT.Okounkov.OF5SuccessiveOrder
import SGPT.Okounkov.OF5CartierChain
import SGPT.Okounkov.AdmissibleFlag
import SGPT.Okounkov.AlgebraicValuationCenter
import SGPT.Projective.AlgebraicStalkCotangentRank
import SGPT.NAPotential.AlgPrimes2Normal
import Mathlib.AlgebraicGeometry.OrderOfVanishing
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.RingTheory.OrderOfVanishing.Noetherian

/-!
# The valuation `ν_{Y•}` of an admissible flag

Source: chapter *The theory of Okounkov bodies*, Section *Flags and valuations*, `def:admfl` and
the definition of `ν_{Y•}` that follows it:

*Given any admissible flag `Y•`, we can define a rank `n` valuation
`ν_{Y•} : ℂ(X)^× → ℤⁿ` … Let `s⁽⁰⁾ = s ∈ ℂ(X)^×`. For `i = 1, …, n`, after localizing around
`Yₙ`, choose a local defining equation `tᵢ` of `Yᵢ` in `Yᵢ₋₁`, and set
`νᵢ = ord_{Yᵢ}(s⁽ⁱ⁻¹⁾)`, `s⁽ⁱ⁾ = (s⁽ⁱ⁻¹⁾ tᵢ^{-νᵢ})|_{Yᵢ}`. Then `ν_{Y•}(s) = (ν₁, …, νₙ)`. It is
easy to verify that `ν_{Y•}` is indeed a rank `n` valuation.*

Setting: `X` an integral scheme, smooth of relative dimension `n` over `ℂ`
(`SmoothOfRelativeDimension n f`), and `Y•` an admissible flag (`SGPT.Okounkov.IsAdmissibleFlag`):
closed irreducible `Yᵢ` of codimension `i`, each smooth at the point `Yₙ`.

## Construction

Localizing around `Yₙ` is passing to the local ring `R = 𝒪_{X,Yₙ}`, in which `Yᵢ` is the prime
`𝔭ᵢ` of germs vanishing on `Yᵢ` (`admissibleIdeal`, the generization ideal of the generic point
`ηᵢ` of `Yᵢ`); `𝔭₀ = 0` and `𝔭₀ ⊊ 𝔭₁ ⊊ ⋯ ⊊ 𝔭ₙ` (the heights are the codimensions). Every
`R ⧸ 𝔭ᵢ = 𝒪_{Yᵢ,Yₙ}` is formally smooth over `ℂ` (admissibility) and `Ω_{R/ℂ}` is free of rank
`n`, so local defining equations exist (`SGPT.Okounkov.OF5.exists_localEquations`):
`𝔭ᵢ = 𝔭ᵢ₋₁ + (tᵢ)`. The successive orders along them (`SGPT.Okounkov.OF5.LocalEquationChain`)
define `ν_{Y•}` on `R`, and on its fraction field `ℂ(X)`.

## Main results

* `admissibleFlagValuation hY : AddValuation ℂ(X) (ℤⁿ_lex ∪ {∞})`: `ν_{Y•}`.
* `admissibleFlagValuation_surjective`: a valuation of rank `n` (value group `ℤⁿ_lex`).
* `admissibleFlagValuation_isValuationCenter`, `valuationCenter_admissibleFlagValuation`: its
  centre is the point `Yₙ`.
* `admissibleFlagValuation_firstCoord`: **the first coordinate of `ν_{Y•}(g)` is `ord_{Y₁}(g)`**,
  the order of vanishing of `g` along the prime divisor `Y₁` (Mathlib's `Scheme.ord` at the
  generic point of `Y₁`, the normalized valuation of the discrete valuation ring `𝒪_{X,Y₁}`).
* `ord_eq_multiplicity`: on a local ring `𝒪_{X,x}` in which `Z = {z}‾` (`z` of codimension one)
  is cut out by `π`, `ord_Z` is the multiplicity of `π`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace SGPT.Okounkov.OF5

open AlgebraicGeometry CategoryTheory Topology IsLocalRing

/-! ### Generization ideals -/

section Generization

variable {X : Scheme.{0}}

/-- Generization ideals are monotone along specialization. -/
theorem generizationIdeal_le_of_specializes {η η' x : X} (h : η ⤳ x) (h' : η' ⤳ x)
    (hηη' : η ⤳ η') : generizationIdeal h ≤ generizationIdeal h' := by
  intro g hg
  have hcomp : (X.presheaf.stalkSpecializes h).hom g =
      (X.presheaf.stalkSpecializes hηη').hom ((X.presheaf.stalkSpecializes h').hom g) := by
    rw [← CommRingCat.comp_apply, TopCat.Presheaf.stalkSpecializes_comp]
  simp only [generizationIdeal, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal,
    mem_nonunits_iff] at hg ⊢
  intro hu
  apply hg
  rw [hcomp]
  exact hu.map _

/-- The generization ideal of the point itself is the maximal ideal. -/
theorem generizationIdeal_eq_maximalIdeal {η x : X} (h : η ⤳ x) (e : η = x) :
    generizationIdeal h = maximalIdeal (X.presheaf.stalk x) := by
  subst e
  ext g
  simp only [generizationIdeal, Ideal.mem_comap]
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  rfl

/-- The coheight of a point of `Spec 𝒪_{X,x}` is its coheight in `X` (after the
Codex module `SGPT.Projective.BDivNov16.original_fromSpecStalk_coheight`). -/
theorem fromSpecStalk_coheight (x : X) (z : Spec (X.presheaf.stalk x)) :
    Order.coheight (X.fromSpecStalk x z) = Order.coheight z := by
  let φ := X.fromSpecStalk x
  let e : Spec (X.presheaf.stalk x) ↪o X :=
    { toFun := φ
      inj' := φ.isEmbedding.injective
      map_rel_iff' := by
        intro a b
        exact φ.isEmbedding.isInducing.specializes_iff }
  have hup : ∀ a : Spec (X.presheaf.stalk x), ∀ b : X,
      e a < b → ∃ a', a < a' ∧ e a' = b := by
    intro a b hab
    have hba : b ⤳ φ a := hab.le
    have hax : φ a ⤳ x := by
      apply (Set.ext_iff.mp (Scheme.range_fromSpecStalk (x := x)) (φ a)).mp
      exact ⟨a, rfl⟩
    have hb : b ∈ Set.range φ := by
      apply (Set.ext_iff.mp (Scheme.range_fromSpecStalk (x := x)) b).mpr
      exact hba.trans hax
    obtain ⟨a', ha'⟩ := hb
    refine ⟨a', ?_, ha'⟩
    apply e.lt_iff_lt.mp
    simpa only [show e a' = b from ha'] using hab
  exact (Order.coheight_eq_of_strictMono e e.strictMono hup z).symm

/-- **The height of the generization ideal is the codimension of the generization.** -/
theorem generizationIdeal_height {η x : X} (h : η ⤳ x) :
    (generizationIdeal h).height = Order.coheight η := by
  let z : Spec (X.presheaf.stalk x) :=
    Spec.map (X.presheaf.stalkSpecializes h) (IsLocalRing.closedPoint (X.presheaf.stalk η))
  have hz : z.asIdeal = generizationIdeal h := rfl
  have himage : X.fromSpecStalk x z = η := by
    change (Spec.map (X.presheaf.stalkSpecializes h) ≫ X.fromSpecStalk x)
      (IsLocalRing.closedPoint (X.presheaf.stalk η)) = η
    rw [Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.fromSpecStalk_closedPoint]
  calc
    _ = Order.coheight z := by rw [← hz]; exact idealHeight_eq_coheight _ z
    _ = Order.coheight (X.fromSpecStalk x z) := (fromSpecStalk_coheight x z).symm
    _ = Order.coheight η := congrArg Order.coheight himage

end Generization

/-! ### Orders of vanishing along a prime divisor cut out by one equation -/

section Ord

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]

omit [IsLocallyNoetherian X] in
/-- The maps of the local rings to `ℂ(X)` are compatible with generization. -/
theorem algebraMap_stalkSpecializes {z x : X} (h : z ⤳ x) (g : X.presheaf.stalk x) :
    algebraMap (X.presheaf.stalk z) X.functionField ((X.presheaf.stalkSpecializes h).hom g) =
      algebraMap (X.presheaf.stalk x) X.functionField g := by
  simp only [RingHom.algebraMap_toAlgebra]
  rw [← CommRingCat.comp_apply, TopCat.Presheaf.stalkSpecializes_comp]

theorem ord_nonneg_of_stalk {z : X} (hz : Order.coheight z = 1) (c : X.presheaf.stalk z) :
    0 ≤ Scheme.ord (algebraMap (X.presheaf.stalk z) X.functionField c) z := by
  by_cases hc : c = 0
  · rw [hc, map_zero, Scheme.ord_zero]
    rfl
  have hc' : algebraMap (X.presheaf.stalk z) X.functionField c ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hc
  rw [Scheme.le_ord_iff hz hc']
  have : Ring.KrullDimLE 1 (X.presheaf.stalk z) := krullDimLE_of_coheight_le hz.le
  exact Ring.ordFrac_ge_one_of_ne_zero hc

theorem ord_eq_zero_of_isUnit {z : X} (hz : Order.coheight z = 1) {c : X.presheaf.stalk z}
    (hc : IsUnit c) : Scheme.ord (algebraMap (X.presheaf.stalk z) X.functionField c) z = 0 := by
  have hc' : algebraMap (X.presheaf.stalk z) X.functionField c ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hc.ne_zero
  rw [Scheme.ord_eq_iff hz hc']
  have : Ring.KrullDimLE 1 (X.presheaf.stalk z) := krullDimLE_of_coheight_le hz.le
  exact Ring.ordFrac_of_isUnit hc

theorem exists_ord_eq_one {z : X} (hz : Order.coheight z = 1)
    [IsDiscreteValuationRing (X.presheaf.stalk z)] :
    ∃ c : X.presheaf.stalk z, c ≠ 0 ∧
      Scheme.ord (algebraMap (X.presheaf.stalk z) X.functionField c) z = 1 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (X.presheaf.stalk z)
  have hw0 : algebraMap (X.presheaf.stalk z) X.functionField ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hϖ.ne_zero
  refine ⟨ϖ, hϖ.ne_zero, ?_⟩
  rw [Scheme.ord_eq_iff hz hw0]
  have : Ring.KrullDimLE 1 (X.presheaf.stalk z) := krullDimLE_of_coheight_le hz.le
  change Ring.ordFrac (X.presheaf.stalk z) _ = _
  rw [Ring.ordFrac_irreducible hϖ]
  rfl

/-- **`ord_Z` is the multiplicity of a local equation.** Let `z` be a point of codimension one
(`Z = {z}‾` a prime divisor, `𝒪_{X,z}` a discrete valuation ring), `z ⤳ x`, and `π ∈ 𝒪_{X,x}` a
nonzero nonunit such that every germ not divisible by `π` is a unit at `z` (i.e. `π` cuts out `Z`
near `x`). Then `ord_Z(g) = mult_π(g)` for every nonzero `g ∈ 𝒪_{X,x}`. -/
theorem ord_eq_multiplicity {z x : X} (hz : Order.coheight z = 1) (hzx : z ⤳ x)
    [IsDiscreteValuationRing (X.presheaf.stalk z)]
    {π : X.presheaf.stalk x} (hπ0 : π ≠ 0) (hπu : ¬IsUnit π)
    (hunit : ∀ h : X.presheaf.stalk x, ¬π ∣ h → IsUnit ((X.presheaf.stalkSpecializes hzx).hom h))
    {g : X.presheaf.stalk x} (hg : g ≠ 0) :
    Scheme.ord (algebraMap (X.presheaf.stalk x) X.functionField g) z = multiplicity π g := by
  classical
  set alg := algebraMap (X.presheaf.stalk x) X.functionField with halg
  have hinj : Function.Injective alg := IsFractionRing.injective _ _
  set d := Scheme.ord (alg π) z with hd
  have hformula : ∀ a : X.presheaf.stalk x, a ≠ 0 →
      Scheme.ord (alg a) z = d * (multiplicity π a : ℤ) := by
    intro a ha
    have hfin : FiniteMultiplicity π a := FiniteMultiplicity.of_not_isUnit hπu ha
    obtain ⟨h, hah, hndvd⟩ := hfin.exists_eq_pow_mul_and_not_dvd
    have hh0 : h ≠ 0 := by
      rintro rfl
      exact hndvd (dvd_zero _)
    have hπ' : alg π ≠ 0 := (map_ne_zero_iff _ hinj).mpr hπ0
    have hh' : alg h ≠ 0 := (map_ne_zero_iff _ hinj).mpr hh0
    have hordh : Scheme.ord (alg h) z = 0 := by
      rw [halg, ← algebraMap_stalkSpecializes hzx]
      exact ord_eq_zero_of_isUnit hz (hunit h hndvd)
    conv_lhs => rw [hah, map_mul, map_pow]
    rw [Scheme.ord_mul (pow_ne_zero _ hπ') hh', hordh, add_zero]
    have hpow : ∀ k : ℕ, Scheme.ord (alg π ^ k) z = k * d := by
      intro k
      induction k with
      | zero =>
        have h1 := Scheme.ord_mul (X := X) (x := z) (one_ne_zero (α := X.functionField))
          (one_ne_zero (α := X.functionField))
        rw [mul_one] at h1
        simp only [pow_zero, Nat.cast_zero, zero_mul]
        omega
      | succ k ih =>
        rw [pow_succ, Scheme.ord_mul (pow_ne_zero _ hπ') hπ', ih]
        push_cast
        ring
    rw [hpow]
    ring
  -- `d = 1`, by a uniformizer of `𝒪_{X,z}`
  have hd1 : d = 1 := by
    obtain ⟨c, hc0, hc1⟩ := exists_ord_eq_one hz (X := X) (z := z)
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := X.presheaf.stalk x)
      (algebraMap (X.presheaf.stalk z) X.functionField c)
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have hb' : alg b ≠ 0 := (map_ne_zero_iff _ hinj).mpr hb0
    have hw0 : algebraMap (X.presheaf.stalk z) X.functionField c ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hc0
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [map_zero, zero_div] at hab
      exact hw0 hab.symm
    have hmul : algebraMap (X.presheaf.stalk z) X.functionField c * alg b = alg a := by
      rw [← hab, div_mul_cancel₀ _ hb']
    have h1 := Scheme.ord_mul (x := z) hw0 hb'
    rw [hmul, hc1, hformula a ha0, hformula b hb0] at h1
    have hdvd : d ∣ 1 := ⟨(multiplicity π a : ℤ) - (multiplicity π b : ℤ), by linarith⟩
    have hdnn : 0 ≤ d := by
      rw [hd, halg, ← algebraMap_stalkSpecializes hzx]
      exact ord_nonneg_of_stalk hz _
    rcases Int.isUnit_iff.mp (isUnit_of_dvd_one hdvd) with h | h <;> omega
  rw [hformula g hg, hd1, one_mul]

end Ord

/-! ### The flag in the local ring of `Yₙ` -/

section Flag

variable {X : Scheme.{0}} [IsIntegral X] {f : X ⟶ Spec (.of ℂ)} {n : ℕ}
  [SmoothOfRelativeDimension n f] {Y : Fin (n + 1) → Set X}

/-- The member index `min i n`. -/
def memberIndex (n i : ℕ) : Fin (n + 1) := ⟨min i n, by omega⟩

variable (hY : IsAdmissibleFlag f n Y)

/-- The generic point `ηᵢ` of `Y_{min(i,n)}`. -/
abbrev memberPoint (i : ℕ) : X := (hY.isIrreducible (memberIndex n i)).genericPoint

omit [IsIntegral X] [SmoothOfRelativeDimension n f] in
theorem memberPoint_specializes (i : ℕ) : memberPoint hY i ⤳ hY.point :=
  genericPoint_specializes (hY.isIrreducible _) (hY.isClosed _) (hY.point_mem _)

/-- **The prime of `Yᵢ` in `𝒪_{X,Yₙ}`** (germs vanishing on `Yᵢ`; `i` clamped to `n`). -/
def admissibleIdeal (i : ℕ) : Ideal (X.presheaf.stalk hY.point) :=
  generizationIdeal (memberPoint_specializes hY i)

instance admissibleIdeal_isPrime (i : ℕ) : (admissibleIdeal hY i).IsPrime :=
  generizationIdeal_isPrime _

omit [IsIntegral X] [SmoothOfRelativeDimension n f] in
theorem coheight_memberPoint (i : ℕ) : Order.coheight (memberPoint hY i) = (min i n : ℕ) :=
  hY.codim_eq (memberIndex n i)

omit [IsIntegral X] [SmoothOfRelativeDimension n f] in
theorem admissibleIdeal_height (i : ℕ) : (admissibleIdeal hY i).height = (min i n : ℕ) := by
  rw [admissibleIdeal, generizationIdeal_height, coheight_memberPoint]

omit [IsIntegral X] [SmoothOfRelativeDimension n f] in
theorem admissibleIdeal_mono {i j : ℕ} (hij : i ≤ j) :
    admissibleIdeal hY i ≤ admissibleIdeal hY j := by
  apply generizationIdeal_le_of_specializes
  apply genericPoint_specializes (hY.isIrreducible _) (hY.isClosed _)
  apply hY.antitone (show memberIndex n i ≤ memberIndex n j from by
    change min i n ≤ min j n
    omega)
  exact genericPoint_mem (hY.isIrreducible _) (hY.isClosed _)

omit [IsIntegral X] [SmoothOfRelativeDimension n f] in
theorem admissibleIdeal_lt {i : ℕ} (hi : i < n) :
    admissibleIdeal hY i < admissibleIdeal hY (i + 1) := by
  refine lt_of_le_of_ne (admissibleIdeal_mono hY (Nat.le_succ i)) fun h => ?_
  have h1 := admissibleIdeal_height hY i
  rw [h, admissibleIdeal_height] at h1
  have : min (i + 1) n = min i n := by exact_mod_cast h1
  omega

omit [SmoothOfRelativeDimension n f] in
theorem admissibleIdeal_zero : admissibleIdeal hY 0 = ⊥ := by
  rw [← Ideal.height_eq_zero_iff_eq_bot, admissibleIdeal_height]
  simp

omit [IsIntegral X] [SmoothOfRelativeDimension n f] in
theorem admissibleIdeal_last : admissibleIdeal hY n = maximalIdeal (X.presheaf.stalk hY.point) :=
  generizationIdeal_eq_maximalIdeal _ (by
    change (hY.isIrreducible (memberIndex n n)).genericPoint =
      (hY.isIrreducible (Fin.last n)).genericPoint
    rw [show memberIndex n n = Fin.last n from Fin.ext (by simp [memberIndex])])

omit [IsIntegral X] in
/-- **Local defining equations of an admissible flag exist**: near `Yₙ`, every `Yᵢ₊₁` is a
Cartier divisor of `Yᵢ`, `𝔭ᵢ₊₁ = 𝔭ᵢ + (tᵢ₊₁)`. -/
theorem exists_admissibleLocalEquationChain :
    ∃ C : LocalEquationChain (X.presheaf.stalk hY.point) n, C.P = admissibleIdeal hY := by
  classical
  let := stalkComplexAlgebra f hY.point
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  have : LocallyOfFiniteType f := inferInstance
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨hfs, -, hfin, hfree⟩ :=
    SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI.originalSmoothStalk_differentials
      f hY.point
  have hrank :=
    SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI.originalStalk_cotangent_finrank
      f n hY.point
  have hsm : ∀ i ≤ n, Algebra.FormallySmooth ℂ (X.presheaf.stalk hY.point ⧸ admissibleIdeal hY i) :=
    fun i _ => hY.smoothAt (memberIndex n i)
  have hT := exists_localEquations (k := ℂ) n (admissibleIdeal hY) (fun i hi => admissibleIdeal_lt hY hi)
    hsm hrank.le
  choose T hT using hT
  refine ⟨{ P := admissibleIdeal hY
            T := fun i => if h : i < n then T i h else 0
            isPrime := fun i => inferInstance
            succ_eq := fun i hi => by simp only [dif_pos hi]; exact hT i hi
            T_notMem := fun i hi => by
              simp only [dif_pos hi]
              intro hmem
              apply (admissibleIdeal_lt hY hi).ne
              rw [hT i hi]
              exact (sup_eq_left.mpr (by
                rw [Ideal.span_le, Set.singleton_subset_iff]
                exact hmem)).symm }, rfl⟩

/-- The chosen local defining equations. -/
def admissibleFlagChain : LocalEquationChain (X.presheaf.stalk hY.point) n :=
  (exists_admissibleLocalEquationChain hY).choose

omit [IsIntegral X] in
theorem admissibleFlagChain_P : (admissibleFlagChain hY).P = admissibleIdeal hY :=
  (exists_admissibleLocalEquationChain hY).choose_spec

theorem admissibleFlagChain_P_zero : (admissibleFlagChain hY).P 0 = ⊥ := by
  rw [admissibleFlagChain_P, admissibleIdeal_zero]

/-- **The valuation `ν_{Y•}` of an admissible flag** (source: the definition after
`def:admfl`): the successive orders of vanishing along local defining equations of the members,
after localizing around `Yₙ`, on `ℂ(X)` with values in `ℤⁿ_lex ∪ {∞}`. -/
def admissibleFlagValuation : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ))) :=
  haveI : Smooth f := SmoothOfRelativeDimension.smooth n f
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  (admissibleFlagChain hY).fractionValuation X.functionField (admissibleFlagChain_P_zero hY)

/-- **Independence of the choices**: every choice of local defining equations of the members
of the flag near `Yₙ` gives the same valuation `ν_{Y•}`. -/
theorem fractionValuation_eq_admissibleFlagValuation
    (C : LocalEquationChain (X.presheaf.stalk hY.point) n) (hC : C.P = admissibleIdeal hY) :
    haveI : Smooth f := SmoothOfRelativeDimension.smooth n f
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    C.fractionValuation X.functionField (by rw [hC]; exact admissibleIdeal_zero hY) =
      admissibleFlagValuation hY := by
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  exact C.fractionValuation_eq_of_P_eq X.functionField (admissibleFlagChain hY)
    (hC.trans (admissibleFlagChain_P hY).symm) _

theorem admissibleFlagValuation_algebraMap (a : X.presheaf.stalk hY.point) :
    admissibleFlagValuation hY (algebraMap _ X.functionField a) =
      (admissibleFlagChain hY).valAt 0 a := by
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  exact LocalEquationChain.fractionValuation_algebraMap _ _ _ a

/-- **`ν_{Y•}` is a valuation of rank `n`**: it is surjective onto `ℤⁿ ∪ {∞}`. -/
theorem admissibleFlagValuation_surjective : Function.Surjective (admissibleFlagValuation hY) := by
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  exact LocalEquationChain.fractionValuation_surjective _ _ _

/-- **The centre of `ν_{Y•}` is the point `Yₙ`**: `ν_{Y•} ≥ 0` on `𝒪_{X,Yₙ}` and `> 0` on its
maximal ideal. -/
theorem admissibleFlagValuation_isValuationCenter :
    AlgebraicValuation.IsValuationCenter (admissibleFlagValuation hY) hY.point := by
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  refine ⟨fun g => ?_, fun g hg => ?_⟩
  · rw [admissibleFlagValuation_algebraMap]
    exact LocalEquationChain.valAt_nonneg _ 0 g
  · rw [admissibleFlagValuation_algebraMap]
    apply LocalEquationChain.valAt_pos _ 0 (Nat.zero_le n)
    rw [admissibleFlagChain_P, admissibleIdeal_last]
    exact hg

theorem valuationCenter_admissibleFlagValuation [IsProper f] :
    AlgebraicValuation.valuationCenter f (admissibleFlagValuation hY) = hY.point :=
  ((AlgebraicValuation.isValuationCenter_iff_eq f _ hY.point).mp
    (admissibleFlagValuation_isValuationCenter hY)).symm

/-- **The first coordinate of `ν_{Y•}` is `ord_{Y₁}`**: for every nonzero `g ∈ ℂ(X)`, the first
coordinate of `ν_{Y•}(g)` is the order of vanishing of `g` along the prime divisor `Y₁` (the
normalized valuation of the discrete valuation ring `𝒪_{X,Y₁}`). -/
theorem admissibleFlagValuation_firstCoord [IsLocallyNoetherian X] [IsSeparated f] [QuasiCompact f]
    (hn : 0 < n) {g : X.functionField} (hg : g ≠ 0) :
    ∃ w : Fin n → ℤ, admissibleFlagValuation hY g =
        ((toLex w : Lex (Fin n → ℤ)) : WithTop (Lex (Fin n → ℤ))) ∧
      w ⟨0, hn⟩ = Scheme.ord g (memberPoint hY 1) := by
  classical
  set C := admissibleFlagChain hY with hC
  set z := memberPoint hY 1 with hz
  have hz1 : Order.coheight z = 1 := by
    rw [hz, coheight_memberPoint]
    simp [Nat.min_eq_left hn]
  have : IsDiscreteValuationRing (X.presheaf.stalk z) :=
    SGPT.NAPotential.AlgPrimes2.isDiscreteValuationRing_stalk f n hz1
  have hzx : z ⤳ hY.point := memberPoint_specializes hY 1
  have hP0 : C.P 0 = ⊥ := admissibleFlagChain_P_zero hY
  have hP1 : C.P 1 = admissibleIdeal hY 1 := by rw [hC, admissibleFlagChain_P]
  -- `P 1 = (T 0)`
  have hspan : C.P 1 = Ideal.span {C.T 0} := by
    rw [C.succ_eq 0 hn, hP0, bot_sup_eq]
  have hT0 : C.T 0 ≠ 0 := fun h => C.T_notMem 0 hn (by rw [hP0, h]; exact Ideal.zero_mem _)
  have hTu : ¬IsUnit (C.T 0) := by
    intro hu
    apply (C.isPrime 1).ne_top
    rw [hspan, Ideal.span_singleton_eq_top]
    exact hu
  have hunit : ∀ h : X.presheaf.stalk hY.point, ¬C.T 0 ∣ h → IsUnit ((X.presheaf.stalkSpecializes hzx).hom h) := by
    intro h hndvd
    have hh : h ∉ admissibleIdeal hY 1 := by
      rw [← hP1, hspan, Ideal.mem_span_singleton]
      exact hndvd
    by_contra hnu
    apply hh
    change h ∈ generizationIdeal hzx
    simp only [generizationIdeal, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact hnu
  -- the first coordinate on `R`
  have hR : ∀ a : X.presheaf.stalk hY.point, a ≠ 0 → ∃ w : Fin n → ℤ,
      admissibleFlagValuation hY (algebraMap (X.presheaf.stalk hY.point) X.functionField a) =
        ((toLex w : Lex (Fin n → ℤ)) : WithTop (Lex (Fin n → ℤ))) ∧
      w ⟨0, hn⟩ = Scheme.ord (algebraMap (X.presheaf.stalk hY.point) X.functionField a) z := by
    intro a ha
    have haP : a ∉ C.P 0 := by rw [hP0]; exact ha
    obtain ⟨w, hw, hw0⟩ := C.valuation_apply_zero_coord hn haP
    refine ⟨w, by rw [admissibleFlagValuation_algebraMap, ← hw]; rfl, ?_⟩
    rw [hw0, ord_eq_multiplicity hz1 hzx hT0 hTu hunit ha]
    congr 1
    -- `ord₀ a` is the multiplicity of `T 0` in `a`
    have hdec := C.residual_spec 0 a
    have hres := C.residual_notMem hn haP
    obtain ⟨k, hk⟩ : ∃ k, k = C.ord 0 a := ⟨_, rfl⟩
    obtain ⟨r, hr⟩ : ∃ r, r = C.residual 0 a := ⟨_, rfl⟩
    rw [← hk, ← hr] at hdec
    rw [← hr] at hres
    rw [← hk]
    have heq : a = C.T 0 ^ k * r := by
      have h1 : a - C.T 0 ^ k * r ∈ C.P 0 := by
        rw [← Ideal.Quotient.eq, map_mul, map_pow]
        exact hdec
      rw [hP0, Ideal.mem_bot, sub_eq_zero] at h1
      exact h1
    symm
    apply multiplicity_eq_of_dvd_of_not_dvd
    · exact ⟨r, heq⟩
    · intro hd
      apply hres
      rw [hspan, Ideal.mem_span_singleton]
      rw [heq, pow_succ] at hd
      exact (mul_dvd_mul_iff_left (pow_ne_zero _ hT0)).mp hd
  -- fractions
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := X.presheaf.stalk hY.point) g
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hb' : algebraMap (X.presheaf.stalk hY.point) X.functionField b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hb0
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div] at hg
    exact hg rfl
  have ha' : algebraMap (X.presheaf.stalk hY.point) X.functionField a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr ha0
  obtain ⟨wa, hwa, hwa0⟩ := hR a ha0
  obtain ⟨wb, hwb, hwb0⟩ := hR b hb0
  refine ⟨wa - wb, ?_, ?_⟩
  · have hmulv : admissibleFlagValuation hY (algebraMap (X.presheaf.stalk hY.point) X.functionField a /
        algebraMap (X.presheaf.stalk hY.point) X.functionField b) +
        admissibleFlagValuation hY (algebraMap (X.presheaf.stalk hY.point) X.functionField b) =
        admissibleFlagValuation hY (algebraMap (X.presheaf.stalk hY.point) X.functionField a) := by
      rw [← AddValuation.map_mul, div_mul_cancel₀ _ hb']
    rw [hwa, hwb] at hmulv
    obtain ⟨y, hy⟩ := WithTop.ne_top_iff_exists.mp ((admissibleFlagValuation hY).ne_top_iff.mpr hg)
    rw [← hy] at hmulv ⊢
    rw [← WithTop.coe_add, WithTop.coe_eq_coe] at hmulv
    congr 1
    rw [toLex_sub]
    exact eq_sub_of_add_eq hmulv
  · have hmul := Scheme.ord_mul (x := z) (div_ne_zero ha' hb') hb'
    rw [div_mul_cancel₀ _ hb'] at hmul
    simp only [Pi.sub_apply, hwa0, hwb0]
    omega

end Flag

end SGPT.Okounkov.OF5
