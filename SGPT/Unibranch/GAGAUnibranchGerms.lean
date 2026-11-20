import SGPT.Unibranch.GAGAUnibranchAlgebra
import SGPT.Foundations.Analysis.Pending.PolynomialPointAnalyticMap
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# Analytic germs descend unibranchness to algebraic local rings

Let `I` be a radical ideal of `ℂ[z₁, …, zₙ]` and `c ∈ ℂⁿ` a common zero of `I`.
The polynomial germ map `p ↦ (germ at 0 of z ↦ p(z + c))` into the actual ring
`HolGerm (ComplexModel n)` of holomorphic germs is flat (this is the existing
`PolynomialPointAnalyticMap.polynomialGermMap_flat`). Base change along
`ℂ[z] → ℂ[z]/I` and localization give a flat local homomorphism
`(ℂ[z]/I)_{m_c} → 𝒪_{ℂⁿ,c}/I𝒪_{ℂⁿ,c}`. The flat descent theorem of
`GAGAUnibranchAlgebra` then shows: if the reduced analytic local ring
`𝒪_{ℂⁿ,c}/W` is unibranch, where `W` is any ideal between `I𝒪` and its radical
(for instance the germ vanishing ideal of `V(I)`, by Rückert's Nullstellensatz),
then the algebraic local ring `(ℂ[z]/I)_{m_c}` is unibranch.

This is the local, closed-point part of the implication
"`𝒳^An` unibranch ⟹ `𝒳` unibranch" of `prop:unibranch_gaga`.

Blueprint: `claude-gaga2.tex`.
-/

set_option autoImplicit false

open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending

namespace SGPT.Unibranch

noncomputable section

variable {n : ℕ}

/-- The literal identification of germ rings in the propositionally equal dimensions. -/
def germDimensionRingEquiv {a b : ℕ} (h : a = b) :
    HolGerm (ComplexModel a) ≃+* HolGerm (ComplexModel b) := by
  subst b
  exact RingEquiv.refl _

theorem germDimensionRingEquiv_eval {a b : ℕ} (h : a = b) (g : HolGerm (ComplexModel a)) :
    HolGerm.eval (germDimensionRingEquiv h g) = HolGerm.eval g := by
  subst b
  rfl

/-- The polynomial germ map at `c`: a polynomial `p` goes to the germ at `0` of
`z ↦ p(z + c)`, in the actual germ ring of `ℂⁿ`. -/
def polynomialPointGerm (c : Fin n → ℂ) : MvPolynomial (Fin n) ℂ →+* HolGerm (ComplexModel n) :=
  (germDimensionRingEquiv (Nat.zero_add n)).toRingHom.comp
    (PolynomialPointAnalyticMap.polynomialGermMap c).toRingHom

/-- The value of the germ of `p` at `0` is `p(c)`. -/
theorem eval_polynomialPointGerm (c : Fin n → ℂ) (p : MvPolynomial (Fin n) ℂ) :
    HolGerm.eval (polynomialPointGerm c p) = MvPolynomial.eval c p := by
  rw [polynomialPointGerm, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    germDimensionRingEquiv_eval]
  exact PolynomialPointAnalyticMap.eval_polynomialGermMap c p

/-- Flatness of the polynomial germ map, from the existing actual flatness theorem. -/
theorem polynomialPointGerm_flat (c : Fin n → ℂ) : (polynomialPointGerm c).Flat :=
  RingHom.Flat.comp (PolynomialPointAnalyticMap.polynomialGermMap_flat c)
    (RingHom.Flat.of_bijective (germDimensionRingEquiv (Nat.zero_add n)).bijective)

/-- The maximal ideal of `ℂ[z]/I` at a common zero `c` of `I`. -/
def pointIdeal (I : Ideal (MvPolynomial (Fin n) ℂ)) (c : Fin n → ℂ)
    (hc : ∀ p ∈ I, MvPolynomial.eval c p = 0) : Ideal (MvPolynomial (Fin n) ℂ ⧸ I) :=
  RingHom.ker (Ideal.Quotient.lift I (MvPolynomial.eval c) hc)

@[instance] theorem pointIdeal_isMaximal (I : Ideal (MvPolynomial (Fin n) ℂ)) (c : Fin n → ℂ)
    (hc : ∀ p ∈ I, MvPolynomial.eval c p = 0) : (pointIdeal I c hc).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ fun a =>
    ⟨Ideal.Quotient.mk I (MvPolynomial.C a), by simp⟩

/-- The dimension identification keeps coordinate germs. -/
theorem germDimensionRingEquiv_coordinateGerm {a b : ℕ} (h : a = b) (j : Fin a) :
    germDimensionRingEquiv h (HironakaHolomorphicJetMonomialSpan.coordinateGerm j) =
      HironakaHolomorphicJetMonomialSpan.coordinateGerm (Fin.cast h j) := by
  subst b
  rfl

/-- The dimension identification keeps constant germs. -/
theorem germDimensionRingEquiv_constHom {a b : ℕ} (h : a = b) (z : ℂ) :
    germDimensionRingEquiv h (HolGerm.constHom z) = HolGerm.constHom z := by
  subst b
  rfl

/-- The polynomial function `z ↦ p(z + c)` on `ℂⁿ`. -/
def translatedPolynomialFunction (c : Fin n → ℂ) (p : MvPolynomial (Fin n) ℂ) :
    ComplexModel n → ℂ :=
  fun z => MvPolynomial.eval (fun i => z i + c i) p

theorem differentiable_translatedPolynomialFunction (c : Fin n → ℂ)
    (p : MvPolynomial (Fin n) ℂ) : Differentiable ℂ (translatedPolynomialFunction c p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    have h : translatedPolynomialFunction c (MvPolynomial.C a) = fun _ => a :=
      funext fun z => by simp [translatedPolynomialFunction]
    rw [h]
    exact differentiable_const (𝕜 := ℂ) (E := ComplexModel n) a
  | add p q hp hq =>
    have h : translatedPolynomialFunction c (p + q) =
        fun z => translatedPolynomialFunction c p z + translatedPolynomialFunction c q z :=
      funext fun z => by simp [translatedPolynomialFunction]
    rw [h]
    exact hp.add hq
  | mul_X p i hp =>
    have hi : Differentiable ℂ (fun z : ComplexModel n => z i + c i) :=
      (EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).differentiable.add_const _
    have h : translatedPolynomialFunction c (p * MvPolynomial.X i) =
        fun z => translatedPolynomialFunction c p z * (z i + c i) :=
      funext fun z => by simp [translatedPolynomialFunction]
    rw [h]
    exact hp.mul hi

theorem eventually_differentiableAt_translatedPolynomialFunction (c : Fin n → ℂ)
    (p : MvPolynomial (Fin n) ℂ) (w : ComplexModel n) :
    ∀ᶠ z in nhds w, DifferentiableAt ℂ (translatedPolynomialFunction c p) z :=
  Filter.Eventually.of_forall fun z => (differentiable_translatedPolynomialFunction c p) z

/-- The polynomial germ map is the germ of the translated polynomial function. -/
theorem polynomialPointGerm_eq_mk (c : Fin n → ℂ) (p : MvPolynomial (Fin n) ℂ) :
    polynomialPointGerm c p = HolGerm.mk (translatedPolynomialFunction c p)
      (eventually_differentiableAt_translatedPolynomialFunction c p 0) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    have h1 : polynomialPointGerm c (MvPolynomial.C a) = HolGerm.constHom a := by
      rw [polynomialPointGerm, RingHom.comp_apply, ← MvPolynomial.algebraMap_eq,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes, RingEquiv.toRingHom_eq_coe,
        RingHom.coe_coe]
      exact germDimensionRingEquiv_constHom _ a
    rw [h1, HolGerm.constHom_apply, HolGerm.mk_eq_mk_iff]
    exact Filter.Eventually.of_forall fun z => by simp [translatedPolynomialFunction]
  | add p q hp hq =>
    rw [map_add, hp, hq, ← HolGerm.mk_add, HolGerm.mk_eq_mk_iff]
    exact Filter.Eventually.of_forall fun z => by simp [translatedPolynomialFunction]
  | mul_X p i hp =>
    have hX : polynomialPointGerm c (MvPolynomial.X i) =
        HolGerm.mk (fun z : ComplexModel n => z i + c i)
          (Filter.Eventually.of_forall fun z =>
            ((EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).differentiable.add_const _) z) := by
      rw [polynomialPointGerm, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        PolynomialPointAnalyticMap.polynomialGermMap_X, RingEquiv.toRingHom_eq_coe,
        RingHom.coe_coe, map_add, germDimensionRingEquiv_constHom,
        HironakaRelativeNormalIdeal.normalCoordinate, germDimensionRingEquiv_coordinateGerm]
      have hi : Fin.cast (Nat.zero_add n) (Fin.natAdd 0 i) = i := Fin.ext (by simp)
      rw [hi]
      rfl
    rw [map_mul, hp, hX, ← HolGerm.mk_mul, HolGerm.mk_eq_mk_iff]
    exact Filter.Eventually.of_forall fun z => by simp [translatedPolynomialFunction]

/-! ### Flatness after base change to a quotient -/

/-- Base change of a flat ring map to quotients: if `g : R → S` is flat, so is
`R ⧸ I → S ⧸ I S`. -/
theorem flat_quotientMap_map {R S : Type*} [CommRing R] [CommRing S] {g : R →+* S}
    (hg : g.Flat) (I : Ideal R) : (Ideal.quotientMap (I.map g) g Ideal.le_comap_map).Flat := by
  let : Algebra R S := g.toAlgebra
  have : Module.Flat R S := hg
  let J := I.map (algebraMap R S)
  change (algebraMap (R ⧸ I) (S ⧸ J)).Flat
  rw [RingHom.flat_algebraMap_iff]
  let f : S →ₗ[R] S ⧸ J := (Ideal.Quotient.mkₐ R J).toLinearMap
  have hbc : IsBaseChange (R ⧸ I) f := by
    apply IsBaseChange.of_lift_unique
    intro Q _ _ _ _ ψ
    -- `ψ` kills `J = I S`
    let K : Ideal S :=
      { carrier := {x | ∀ a : S, ψ (a * x) = 0}
        add_mem' := fun {x y} hx hy a => by rw [mul_add, map_add, hx a, hy a, add_zero]
        zero_mem' := fun a => by rw [mul_zero, map_zero]
        smul_mem' := fun b x hx a => by rw [smul_eq_mul, ← mul_assoc]; exact hx (a * b) }
    have hIK : J ≤ K := by
      rw [Ideal.map_le_iff_le_comap]
      intro r hr
      rw [Ideal.mem_comap]
      intro a
      rw [mul_comm, ← Algebra.smul_def, map_smul, ← algebraMap_smul (R ⧸ I) r (ψ a),
        Ideal.Quotient.algebraMap_eq, (Ideal.Quotient.eq_zero_iff_mem).mpr hr, zero_smul]
    have hker : J.toAddSubgroup ≤ ψ.toAddMonoidHom.ker := fun x hx => by
      have := hIK hx 1
      rwa [one_mul] at this
    let ψ₀ : S ⧸ J →+ Q := QuotientAddGroup.lift J.toAddSubgroup ψ.toAddMonoidHom hker
    have hψ₀ (x : S) : ψ₀ (Ideal.Quotient.mk J x) = ψ x := rfl
    let ψ' : S ⧸ J →ₗ[R ⧸ I] Q :=
      { toFun := ψ₀
        map_add' := map_add ψ₀
        map_smul' := by
          intro a y
          obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
          obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
          have h1 : (Ideal.Quotient.mk I r) • (Ideal.Quotient.mk J x) =
              Ideal.Quotient.mk J (r • x) := by
            rw [Algebra.smul_def, Algebra.smul_def, map_mul]
            rfl
          rw [h1, hψ₀, hψ₀, map_smul, RingHom.id_apply, ← Ideal.Quotient.algebraMap_eq,
            algebraMap_smul] }
    refine ⟨ψ', LinearMap.ext fun x => rfl, ?_⟩
    intro χ hχ
    refine LinearMap.ext fun y => ?_
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact (LinearMap.congr_fun hχ x).trans (hψ₀ x).symm
  exact Module.Flat.isBaseChange (R := R) (S := R ⧸ I) (M := S) (S ⧸ J) hbc

/-! ### The local comparison at a point -/

/-- The quotient of the reduction of `𝒪/I𝒪` by any ideal between `I𝒪` and its radical. -/
private def reductionEquiv {G : Type*} [CommRing G] (J W : Ideal G) (hJW : J ≤ W)
    (hW : W = J.radical) : (G ⧸ J) ⧸ nilradical (G ⧸ J) ≃+* G ⧸ W := by
  have h : nilradical (G ⧸ J) = W.map (Ideal.Quotient.mk J) := by
    ext y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [Ideal.mem_quotient_iff_mem hJW, mem_nilradical, hW, Ideal.mem_radical_iff]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, Ideal.Quotient.eq_zero_iff_mem.mp (by rw [map_pow, hk])⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem.mpr hk]⟩
  exact (Ideal.quotEquivOfEq h).trans (DoubleQuot.quotQuotEquivQuotOfLE hJW)

/-- **Local comparison.** Let `I` be a radical ideal of `ℂ[z₁,…,zₙ]` and `c` a common zero of
`I`. Let `W` be an ideal of the actual germ ring `𝒪_{ℂⁿ,0}` (germs translated to `c`) lying
between `I𝒪` and its radical, for instance the vanishing ideal of the germ of `V(I)` at `c`.
If `𝒪/W` is unibranch, then the algebraic local ring `(ℂ[z]/I)_{m_c}` is unibranch. -/
theorem sourceUnibranchReducedRing_localization_of_germs (I : Ideal (MvPolynomial (Fin n) ℂ))
    (hI : I.IsRadical) (c : Fin n → ℂ) (hc : ∀ p ∈ I, MvPolynomial.eval c p = 0)
    (W : Ideal (HolGerm (ComplexModel n))) (hJW : I.map (polynomialPointGerm c) ≤ W)
    (hWJ : W ≤ (I.map (polynomialPointGerm c)).radical)
    (hW : SourceUnibranchReducedRing (HolGerm (ComplexModel n) ⧸ W)) :
    SourceUnibranchReducedRing (Localization.AtPrime (pointIdeal I c hc)) := by
  classical
  let G := HolGerm (ComplexModel n)
  let g := polynomialPointGerm c
  let J := I.map g
  let B₀ := G ⧸ J
  have : IsReduced (MvPolynomial (Fin n) ℂ ⧸ I) := (Ideal.isRadical_iff_quotient_reduced I).mp hI
  -- `𝒪/I𝒪` is local
  have hJmax : J ≤ IsLocalRing.maximalIdeal G := by
    rw [Ideal.map_le_iff_le_comap]
    intro p hp
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      HolGerm.isUnit_iff_eval_ne_zero, not_not, eval_polynomialPointGerm]
    exact hc p hp
  have hJtop : J ≠ ⊤ := ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal G).ne_top hJmax
  have : Nontrivial B₀ := Ideal.Quotient.nontrivial_iff.mpr hJtop
  have : IsLocalRing B₀ := IsLocalRing.of_surjective' (Ideal.Quotient.mk J)
    Ideal.Quotient.mk_surjective
  have hmk : IsLocalHom (Ideal.Quotient.mk J) := isLocalHom_of_le_jacobson_bot J
    ((IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal G) bot_ne_top).symm ▸ hJmax)
  -- the flat map of quotients and its comparison of maximal ideals
  let φ : MvPolynomial (Fin n) ℂ ⧸ I →+* B₀ := Ideal.quotientMap J g Ideal.le_comap_map
  have hφ : φ.Flat := flat_quotientMap_map (polynomialPointGerm_flat c) I
  have hQ : pointIdeal I c hc = (IsLocalRing.maximalIdeal B₀).comap φ := by
    ext x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [pointIdeal, RingHom.mem_ker, Ideal.Quotient.lift_mk, Ideal.mem_comap,
      Ideal.quotientMap_mk, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      isUnit_map_iff (Ideal.Quotient.mk J), HolGerm.isUnit_iff_eval_ne_zero, not_not,
      eval_polynomialPointGerm]
  have : (pointIdeal I c hc).IsMaximal := pointIdeal_isMaximal I c hc
  let A := Localization.AtPrime (pointIdeal I c hc)
  let B := Localization.AtPrime (IsLocalRing.maximalIdeal B₀)
  let ψ : A →+* B := Localization.localRingHom _ _ φ hQ
  let : Algebra A B := ψ.toAlgebra
  have : IsLocalHom (algebraMap A B) :=
    Localization.isLocalHom_localRingHom _ _ φ hQ
  have : Module.Flat A B := RingHom.Flat.localRingHom hφ _ _ hQ
  -- the unibranch hypothesis on the reduced analytic ring
  have hWprime : W.IsPrime := (Ideal.Quotient.isDomain_iff_prime W).mp hW.1
  have hWrad : W = J.radical := le_antisymm hWJ
    ((Ideal.radical_mono hJW).trans hWprime.isRadical)
  have hB₀ : SourceUnibranchLocalRing B₀ :=
    (sourceUnibranchReducedRing_iff_of_ringEquiv (reductionEquiv J W hJW hWrad)).mpr hW
  have hB : SourceUnibranchLocalRing B := by
    have e : B₀ ≃ₐ[B₀] B := IsLocalization.atUnits B₀ (IsLocalRing.maximalIdeal B₀).primeCompl
      (fun x hx => (IsUnit.mem_submonoid_iff x).mpr (by
        simpa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hx))
    exact (sourceUnibranchLocalRing_iff_of_ringEquiv e.toRingEquiv).mp hB₀
  exact sourceUnibranchReducedRing_of_flat (A := A) (B := B) hB

end

end SGPT.Unibranch
