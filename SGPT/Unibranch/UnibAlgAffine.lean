import SGPT.Unibranch.UnibAlgFormal
import SGPT.Unibranch.GAGA2FormalBridge
import SGPT.Unibranch.GAGAUnibranchAlgebra

/-!
# `prop:unibranch_gaga` for embedded affine varieties

Let `I ⊆ ℂ[z₁, …, zₙ]` and `c ∈ V(I)`.

* `radical_formalPointIdeal_isPrime_of_unibranch` (step U3 of `claude-serre-gaga.tex`): if the
  local ring of `Spec ℂ[z]/I` at `c` is unibranch (Stacks 0BPZ), then `√(I · ℂ⟦z - c⟧)` is prime.
  This is the excellence input (EGA IV 18.9.1) of the book's proof: the unique minimal prime
  `p ⊆ 𝔪_c` of `I` satisfies `√(I ℂ⟦z - c⟧) = √(p ℂ⟦z - c⟧)`, the normalization of `ℂ[z]/p`
  has a single point over `c` (from the locality of the normalization of the local ring), and
  `p ℂ⟦z - c⟧` is prime by `isPrime_map_fpm`.
* `polynomialZeroSetComplexSpace_isUnibranch_iff` (`prop:unibranch_gaga`, affine case): for a
  radical ideal `I`, the complex space `V(I)` is unibranch (`def:unibranch:L21`) if and only if
  the scheme `Spec ℂ[z]/I` is unibranch (Stacks 0BQ2). The direction "algebraic ⟹ analytic"
  combines U3 with the formal bridge of lane SERRE-GAGA; the converse is lane GAGA2's.

Lane UNIB-ALG; blueprint `claude-unib-alg.tex`.
-/

set_option autoImplicit false

open Polynomial

namespace SGPT.Unibranch.UnibAlg

noncomputable section

open SGPT.Unibranch SGPT.Foundations.Analysis.FirstPass

variable {n : ℕ}

theorem formalPointMap_eq_fpm (c : Fin n → ℂ) :
    formalPointMap c = (fpm c : MvPolynomial (Fin n) ℂ →+* MvPowerSeries (Fin n) ℂ) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [formalPointMap, fpm, SGPT.Foundations.Analysis.Pending.PolynomialPointAnalyticMap.polynomialTranslation, transl,
      MvPowerSeries.algebraMap_apply]
  · intro i
    simp [formalPointMap, fpm, SGPT.Foundations.Analysis.Pending.PolynomialPointAnalyticMap.polynomialTranslation, transl]

theorem formalPointIdeal_eq (I : Ideal (MvPolynomial (Fin n) ℂ)) (c : Fin n → ℂ) :
    formalPointIdeal I c = I.map (fpm c) := by
  rw [formalPointIdeal, formalPointMap_eq_fpm]
  rfl

theorem isUnit_fpm {c : Fin n → ℂ} {s : MvPolynomial (Fin n) ℂ}
    (hs : MvPolynomial.eval c s ≠ 0) : IsUnit (fpm c s) := by
  rw [MvPowerSeries.isUnit_iff_constantCoeff, constantCoeff_fpm]
  exact isUnit_iff_ne_zero.mpr hs

/-! ### From a unibranch local ring to the prime case -/

section Unibranch

variable (I : Ideal (MvPolynomial (Fin n) ℂ)) (c : Fin n → ℂ)
  (hc : ∀ q ∈ I, MvPolynomial.eval c q = 0)
  (A : Type*) [CommRing A] [Algebra (MvPolynomial (Fin n) ℂ ⧸ I) A]
  [IsLocalization.AtPrime A (pointIdeal I c hc)]

include hc

/-- `ℂ[z] → A / nil(A)`, `A` the local ring of `ℂ[z]/I` at `c`. -/
def toRed : MvPolynomial (Fin n) ℂ →+* A ⧸ nilradical A :=
  (Ideal.Quotient.mk _).comp ((algebraMap (MvPolynomial (Fin n) ℂ ⧸ I) A).comp
    (Ideal.Quotient.mk I))

theorem mem_pointIdeal_iff (s : MvPolynomial (Fin n) ℂ) :
    Ideal.Quotient.mk I s ∈ pointIdeal I c hc ↔ MvPolynomial.eval c s = 0 := by
  rw [pointIdeal, RingHom.mem_ker, Ideal.Quotient.lift_mk]

/-- Elements of the kernel of `toRed` are nilpotent at `c` modulo `I`. -/
theorem exists_of_toRed_eq_zero {q : MvPolynomial (Fin n) ℂ} (hq : toRed I A q = 0) :
    ∃ s : MvPolynomial (Fin n) ℂ, MvPolynomial.eval c s ≠ 0 ∧ ∃ N : ℕ, s * q ^ N ∈ I := by
  rw [toRed, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, RingHom.comp_apply,
    mem_nilradical] at hq
  obtain ⟨N, hN⟩ := hq
  rw [← map_pow, ← map_pow] at hN
  obtain ⟨⟨m, hm⟩, hmq⟩ :=
    (IsLocalization.map_eq_zero_iff (pointIdeal I c hc).primeCompl A _).mp hN
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective m
  refine ⟨s, fun h => hm ((mem_pointIdeal_iff I c hc s).mpr h), N, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul]
  exact hmq

theorem toRed_vanish (q : MvPolynomial (Fin n) ℂ) (hq : q ∈ RingHom.ker (toRed I A)) :
    MvPolynomial.eval c q = 0 := by
  obtain ⟨s, hs, N, hsN⟩ := exists_of_toRed_eq_zero I c hc A hq
  have := hc _ hsN
  rw [map_mul, map_pow, mul_eq_zero] at this
  rcases this with h | h
  · exact absurd h hs
  · exact pow_eq_zero_iff'.mp h |>.1

omit hc in
theorem le_ker_toRed (_hc : ∀ q ∈ I, MvPolynomial.eval c q = 0) (A : Type*) [CommRing A]
    [Algebra (MvPolynomial (Fin n) ℂ ⧸ I) A] [IsLocalization.AtPrime A (pointIdeal I c _hc)] :
    I ≤ RingHom.ker (toRed I A) := by
  intro q hq
  rw [RingHom.mem_ker, toRed, RingHom.comp_apply, RingHom.comp_apply,
    Ideal.Quotient.eq_zero_iff_mem.mpr hq, map_zero, map_zero]

/-- `√(I ℂ⟦z - c⟧) = √(p ℂ⟦z - c⟧)` for the kernel `p` of `ℂ[z] → A / nil(A)`. -/
theorem radical_formalPointIdeal_eq :
    (formalPointIdeal I c).radical = ((RingHom.ker (toRed I A)).map (fpm c)).radical := by
  rw [formalPointIdeal_eq]
  apply le_antisymm (Ideal.radical_mono (Ideal.map_mono (le_ker_toRed I c hc A)))
  rw [← Ideal.radical_idem (I.map (fpm c))]
  apply Ideal.radical_mono
  rw [Ideal.map_le_iff_le_comap]
  intro q hq
  obtain ⟨s, hs, N, hsN⟩ := exists_of_toRed_eq_zero I c hc A hq
  rw [Ideal.mem_comap]
  refine ⟨N, ?_⟩
  have h1 : fpm c (s * q ^ N) ∈ I.map (fpm c) := Ideal.mem_map_of_mem _ hsN
  rw [map_mul, map_pow] at h1
  obtain ⟨u, hu⟩ := isUnit_fpm hs
  have := Ideal.mul_mem_left _ (↑u⁻¹ : MvPowerSeries (Fin n) ℂ) h1
  rwa [← mul_assoc, ← hu, Units.inv_mul, one_mul] at this

/-- **U3 (excellence step).** If the local ring `A` of `ℂ[z]/I` at `c` is unibranch, then the
radical of `I · ℂ⟦z - c⟧` is prime. -/
theorem radical_formalPointIdeal_isPrime_of_unibranch' (h : SourceUnibranchLocalRing A) :
    (formalPointIdeal I c).radical.IsPrime := by
  classical
  obtain ⟨hdom, hloc⟩ := h
  set S := A ⧸ nilradical A
  set p := RingHom.ker (toRed I A)
  have hp : p.IsPrime := RingHom.ker_isPrime _
  have hcp : ∀ q ∈ p, MvPolynomial.eval c q = 0 := toRed_vanish I c hc A
  set P := MvPolynomial (Fin n) ℂ
  obtain ⟨π, hπdef⟩ : ∃ π : P ⧸ p →+* S, ∀ q, π (Ideal.Quotient.mk p q) = toRed I A q :=
    ⟨Ideal.Quotient.lift p (toRed I A) (fun _ h => h), fun q => rfl⟩
  have hπ : Function.Injective π := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hπdef] at hx
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hx
  let : Algebra (P ⧸ p) S := π.toAlgebra
  have : (ptIdeal p c hcp).IsMaximal := RingHom.ker_isMaximal_of_surjective _ fun a =>
    ⟨Ideal.Quotient.mk p (MvPolynomial.C a), by simp⟩
  have hmemPt : ∀ q : P, Ideal.Quotient.mk p q ∈ ptIdeal p c hcp ↔ MvPolynomial.eval c q = 0 :=
    fun q => by rw [ptIdeal, RingHom.mem_ker, Ideal.Quotient.lift_mk]
  -- `S = A / nil(A)` is the localization of `ℂ[z]/p` at the point
  have hlocS : IsLocalization (ptIdeal p c hcp).primeCompl S := by
    refine ⟨⟨?_, ?_, ?_⟩⟩
    · rintro ⟨x, hx⟩
      obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective x
      have hq : MvPolynomial.eval c q ≠ 0 := fun h0 => hx ((hmemPt q).mpr h0)
      have hu : IsUnit (algebraMap (P ⧸ I) A (Ideal.Quotient.mk I q)) :=
        IsLocalization.map_units A (⟨Ideal.Quotient.mk I q,
          fun h0 => hq ((mem_pointIdeal_iff I c hc q).mp h0)⟩ : (pointIdeal I c hc).primeCompl)
      change IsUnit (π (Ideal.Quotient.mk p q))
      rw [hπdef]
      exact hu.map (Ideal.Quotient.mk (nilradical A))
    · intro z
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
      obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (pointIdeal I c hc).primeCompl a
      obtain ⟨r', rfl⟩ := Ideal.Quotient.mk_surjective r
      obtain ⟨s₀, hs₀⟩ := s
      obtain ⟨s', rfl⟩ := Ideal.Quotient.mk_surjective s₀
      have hs' : MvPolynomial.eval c s' ≠ 0 := fun h0 => hs₀ ((mem_pointIdeal_iff I c hc s').mpr h0)
      refine ⟨⟨Ideal.Quotient.mk p r', ⟨Ideal.Quotient.mk p s', fun h0 =>
        hs' ((hmemPt s').mp h0)⟩⟩, ?_⟩
      change Ideal.Quotient.mk _ a * π (Ideal.Quotient.mk p s') = π (Ideal.Quotient.mk p r')
      simp only [hπdef, toRed, RingHom.comp_apply, ← map_mul]
      exact congrArg _ hrs
    · intro x y hxy
      exact ⟨1, by rw [hπ hxy]⟩
  -- the normalization has a single point over `c`
  set K := FractionRing (P ⧸ p)
  set FS := FractionRing S
  have hinjS : Function.Injective ((algebraMap S FS).comp π) :=
    (IsFractionRing.injective S FS).comp hπ
  set ι : K →+* FS := IsFractionRing.lift hinjS
  have hι : ∀ x : P ⧸ p, ι (algebraMap (P ⧸ p) K x) = algebraMap S FS (π x) :=
    fun x => IsFractionRing.lift_algebraMap hinjS x
  have hcontra : ∀ (𝔫 : Ideal (integralClosure (P ⧸ p) K)), 𝔫.IsMaximal →
      ptIdeal p c hcp ≤ 𝔫.comap (algebraMap _ _) → ∀ v ∈ 𝔫, ∀ Q : S[X],
      aeval (ι (v : K)) Q = 0 → IsUnit (Q.coeff 0) → False := by
    intro 𝔫 h𝔫 hle v hv Q hQ hQu
    obtain ⟨b, hb, hb'⟩ :=
      IsLocalization.integerNormalization_spec (ptIdeal p c hcp).primeCompl Q
    set Q₀ := IsLocalization.integerNormalization (ptIdeal p c hcp).primeCompl Q
    have h0 : aeval (v : K) Q₀ = 0 := by
      apply ι.injective
      rw [map_zero, aeval_def, hom_eval₂]
      have hcomp : ι.comp (algebraMap (P ⧸ p) K) = (algebraMap S FS).comp π :=
        RingHom.ext hι
      rw [hcomp, ← eval₂_map, ← aeval_def]
      change aeval (ι (v : K)) (Q₀.map (algebraMap (P ⧸ p) S)) = 0
      rw [hb', Algebra.smul_def, Polynomial.algebraMap_apply, map_mul, aeval_C, hQ, mul_zero]
    have hu : Ideal.Quotient.mk p 0 = 0 := rfl
    have hcoeff : IsUnit (algebraMap (P ⧸ p) S (Q₀.coeff 0)) := by
      have := congrArg (fun P => P.coeff 0) hb'
      simp only [coeff_map, coeff_smul] at this
      rw [this, Algebra.smul_def]
      exact (IsLocalization.map_units S ⟨b, hb⟩).mul hQu
    have hnot : Q₀.coeff 0 ∉ ptIdeal p c hcp := by
      intro hmem
      have := (IsLocalization.AtPrime.isUnit_to_map_iff S (ptIdeal p c hcp) (Q₀.coeff 0)).mp hcoeff
      exact this hmem
    apply hnot
    have hmaxc : (𝔫.comap (algebraMap (P ⧸ p) (integralClosure (P ⧸ p) K))).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal 𝔫
    have heq := Ideal.IsMaximal.eq_of_le (inferInstance : (ptIdeal p c hcp).IsMaximal)
      hmaxc.ne_top hle
    rw [heq, Ideal.mem_comap]
    have hR' : aeval v Q₀ = 0 := by
      apply Subtype.val_injective
      rw [← aeval_subalgebra_coe] at h0
      exact h0.trans rfl
    have hsplit := congrArg (aeval v) (X_mul_divX_add Q₀)
    rw [map_add, map_mul, aeval_X, aeval_C, hR'] at hsplit
    have : algebraMap (P ⧸ p) (integralClosure (P ⧸ p) K) (Q₀.coeff 0) =
        -(v * aeval v Q₀.divX) := by linear_combination hsplit
    rw [this]
    exact 𝔫.neg_mem (Ideal.mul_mem_right _ _ hv)
  have huni : ∀ 𝔫₁ 𝔫₂ : Ideal (integralClosure (P ⧸ p) K), 𝔫₁.IsMaximal → 𝔫₂.IsMaximal →
      ptIdeal p c hcp ≤ 𝔫₁.comap (algebraMap _ _) → ptIdeal p c hcp ≤ 𝔫₂.comap (algebraMap _ _) →
      𝔫₁ = 𝔫₂ := by
    intro 𝔫₁ 𝔫₂ h₁ h₂ hle₁ hle₂
    by_contra hne
    have htop : 𝔫₁ ⊔ 𝔫₂ = ⊤ := by
      by_contra hne'
      obtain ⟨M, hM, hleM⟩ := Ideal.exists_le_maximal _ hne'
      have e1 := h₁.eq_of_le hM.ne_top (le_sup_left.trans hleM)
      have e2 := h₂.eq_of_le hM.ne_top (le_sup_right.trans hleM)
      exact hne (e1.trans e2.symm)
    have h1 : (1 : integralClosure (P ⧸ p) K) ∈ 𝔫₁ ⊔ 𝔫₂ := htop ▸ Submodule.mem_top
    obtain ⟨z, hz, w, hw, hzw⟩ := Submodule.mem_sup.mp h1
    have hz' : IsIntegral S (ι (z : K)) :=
      IsIntegral.map_of_comp_eq π ι (RingHom.ext hι).symm z.2
    rcases (isLocalRing_integralClosure_iff.mp hloc) (ι (z : K)) hz' with ⟨Q, hQ, hQu⟩ |
      ⟨Q, hQ, hQu⟩
    · exact hcontra 𝔫₁ h₁ hle₁ z hz Q hQ hQu
    · have hwz : w = 1 - z := by rw [← hzw]; ring
      refine hcontra 𝔫₂ h₂ hle₂ w hw Q ?_ hQu
      rw [hwz]
      simpa using hQ
  have hprime := isPrime_map_fpm p c hcp huni
  rw [radical_formalPointIdeal_eq I c hc A, hprime.radical]
  exact hprime

end Unibranch

/-! ### The headline statements -/

/-- **U3.** If the local ring of `Spec ℂ[z]/I` at the closed point `c` is unibranch (Stacks
0BPZ), then `√(I · ℂ⟦z - c⟧)` is prime. -/
theorem radical_formalPointIdeal_isPrime_of_unibranch (I : Ideal (MvPolynomial (Fin n) ℂ))
    (c : Fin n → ℂ) (hc : ∀ q ∈ I, MvPolynomial.eval c q = 0)
    (h : SourceUnibranchLocalRing (Localization.AtPrime (pointIdeal I c hc))) :
    (formalPointIdeal I c).radical.IsPrime :=
  radical_formalPointIdeal_isPrime_of_unibranch' I c hc _ h

open AlgebraicGeometry in
/-- **`prop:unibranch_gaga`, algebraic ⟹ analytic, embedded affine case.** If the scheme
`Spec ℂ[z]/I` is unibranch (Stacks 0BQ2), then the complex space `V(I)` is unibranch
(`def:unibranch:L21`). -/
theorem polynomialZeroSetComplexSpace_isUnibranch_of_schemeIsUnibranch
    (I : Ideal (MvPolynomial (Fin n) ℂ))
    (h : SchemeIsUnibranch (Spec (CommRingCat.of (MvPolynomial (Fin n) ℂ ⧸ I)))) :
    (polynomialZeroSetComplexSpace I).IsUnibranch := by
  apply polynomialZeroSetComplexSpace_isUnibranch_of_formal
  intro x
  have hc : ∀ q ∈ I, MvPolynomial.eval (complexCoordinates (x.val : ComplexModel n)) q = 0 :=
    fun q hq => x.property q hq
  let y : PrimeSpectrum (CommRingCat.of (MvPolynomial (Fin n) ℂ ⧸ I)) :=
    ⟨pointIdeal I (complexCoordinates (x.val : ComplexModel n)) hc, inferInstance⟩
  have hy := (schemeIsUnibranchAt_spec_iff _ y).mp (h y)
  exact radical_formalPointIdeal_isPrime_of_unibranch I _ hc hy

open AlgebraicGeometry in
/-- **`prop:unibranch_gaga` for embedded affine varieties.** For a radical ideal `I` of
`ℂ[z₁, …, zₙ]`, the complex space `V(I)` (the analytification of `Spec ℂ[z]/I`) is unibranch
in the sense of `def:unibranch:L21` if and only if the scheme `Spec ℂ[z]/I` is unibranch in the
algebraic sense (Stacks 0BQ2). -/
theorem polynomialZeroSetComplexSpace_isUnibranch_iff_schemeIsUnibranch
    (I : Ideal (MvPolynomial (Fin n) ℂ)) (hI : I.IsRadical) :
    (polynomialZeroSetComplexSpace I).IsUnibranch ↔
      SchemeIsUnibranch (Spec (CommRingCat.of (MvPolynomial (Fin n) ℂ ⧸ I))) :=
  ⟨schemeIsUnibranch_of_isUnibranch I hI,
    polynomialZeroSetComplexSpace_isUnibranch_of_schemeIsUnibranch I⟩

/-! ### The stalkwise statement in an arbitrary affine chart -/

theorem polynomialZeroSet_vanish {I : Ideal (MvPolynomial (Fin n) ℂ)} (x : polynomialZeroSet I) :
    ∀ q ∈ I, MvPolynomial.eval (complexCoordinates (x.val : ComplexModel n)) q = 0 :=
  x.property

/-- The closed point of `Spec ℂ[z]/I` given by `x ∈ V(I)`. -/
def closedPoint {I : Ideal (MvPolynomial (Fin n) ℂ)} (x : polynomialZeroSet I) :
    PrimeSpectrum (CommRingCat.of (MvPolynomial (Fin n) ℂ ⧸ I)) :=
  ⟨pointIdeal I (complexCoordinates (x.val : ComplexModel n)) (polynomialZeroSet_vanish x),
    inferInstance⟩

/-- **Pointwise `prop:unibranch_gaga` on `V(I)`.** For a radical ideal `I` and `x ∈ V(I)`, the
analytic local ring of the complex space `V(I)` at `x` is unibranch iff the algebraic local
ring of `ℂ[z]/I` at `x` is unibranch (Stacks 0BPZ). -/
theorem modelStalk_unibranch_iff (I : Ideal (MvPolynomial (Fin n) ℂ)) (hI : I.IsRadical)
    (x : polynomialZeroSet I) :
    SourceUnibranchReducedRing
        ((polynomialZeroSetComplexSpace I).obj.left.presheaf.stalk x).carrier ↔
      SourceUnibranchLocalRing (Localization.AtPrime (pointIdeal I
        (complexCoordinates (x.val : ComplexModel n)) (polynomialZeroSet_vanish x))) := by
  have : IsReduced (MvPolynomial (Fin n) ℂ ⧸ I) := (Ideal.isRadical_iff_quotient_reduced I).mp hI
  constructor
  · intro h
    rw [sourceUnibranchLocalRing_iff_of_isReduced]
    exact sourceUnibranchReducedRing_pointLocalization_of_model I hI x h
  · intro h
    exact sourceUnibranchReducedRing_modelStalk_of_formal I x
      (radical_formalPointIdeal_isPrime_of_unibranch I _ _ h)

open AlgebraicGeometry in
/-- **`prop:unibranch_gaga`, stalkwise, for every scheme and every embedded affine chart.**
Let `X` be a scheme and `f : Spec ℂ[z]/I → X` an open immersion with `I` radical (an embedded
affine chart). For every `x ∈ V(I)`, `X` is unibranch at `f(x)` (Stacks 0BQ2) iff the complex
space `V(I)` — the analytification of the chart — is unibranch at `x` (`def:unibranch:L21`).
No separatedness is needed (cf. ERRATA I03). -/
theorem schemeIsUnibranchAt_iff_modelStalk {X : Scheme} (I : Ideal (MvPolynomial (Fin n) ℂ))
    (hI : I.IsRadical) (f : Spec (CommRingCat.of (MvPolynomial (Fin n) ℂ ⧸ I)) ⟶ X)
    [IsOpenImmersion f] (x : polynomialZeroSet I) :
    SchemeIsUnibranchAt X (f (closedPoint x)) ↔
      SourceUnibranchReducedRing
        ((polynomialZeroSetComplexSpace I).obj.left.presheaf.stalk x).carrier :=
  by
    have h1 := schemeIsUnibranchAt_iff_of_isOpenImmersion f (closedPoint x)
    have h2 := schemeIsUnibranchAt_spec_iff (CommRingCat.of (MvPolynomial (Fin n) ℂ ⧸ I))
      (closedPoint x)
    exact h1.trans (h2.trans (modelStalk_unibranch_iff I hI x).symm)

end

end SGPT.Unibranch.UnibAlg
