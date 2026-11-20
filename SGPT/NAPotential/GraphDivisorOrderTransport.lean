import SGPT.NAPotential.AlgPrimes3Algebra
import SGPT.NAPotential.ProjectiveGraphRelations
import Mathlib.RingTheory.OrderOfVanishing.Noetherian
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Original divisorial orders through the actual graph prime localization

Blueprint: `graph-divisor-order-transport.tex`.  Actual localization
isomorphisms and original coefficient squares preserve the entire normalized
fraction-order homomorphism; no order comparison is supplied as an input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.NAPotential.GraphDivisorOrderTransport

open AlgebraicGeometry CategoryTheory IsLocalRing WithZero
open SGPT.NAPotential.Berkovich
open scoped nonZeroDivisors

universe u

section PrincipalOrder

variable {R S : Type u} [CommRing R] [CommRing S]

private theorem length_eq_semilinear {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module S N] (σ : R →+* S) (hσ : Function.Surjective σ)
    (f : M →ₛₗ[σ] N) (hf : Function.Bijective f) :
    Module.length R M = Module.length S N := by
  let : RingHomSurjective σ := ⟨hσ⟩
  rw [Module.length, Module.length, WithBot.unbot_inj,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective f hf)]

private def principalQuotientMap (e : R ≃+* S) (a : R) :
    (R ⧸ Ideal.span {a}) →ₛₗ[e.toRingHom] S ⧸ Ideal.span {e a} := by
  let q := Ideal.quotientEquiv (Ideal.span {a}) (Ideal.span {e a}) e
    (by rw [Ideal.map_span]; simp)
  refine { toFun := q, map_add' := q.map_add, map_smul' := ?_ }
  intro r b
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  change q (Ideal.Quotient.mk _ (r * b)) = Ideal.Quotient.mk _ (e r * e b)
  rw [Ideal.quotientEquiv_mk, map_mul]

/-- The actual original ring isomorphism preserves principal quotient order exactly. -/
theorem ord_ringEquiv (e : R ≃+* S) (a : R) : Ring.ord S (e a) = Ring.ord R a := by
  symm
  exact length_eq_semilinear e.toRingHom e.surjective (principalQuotientMap e a)
    (Ideal.quotientEquiv (Ideal.span {a}) (Ideal.span {e a}) e
      (by rw [Ideal.map_span]; simp)).bijective

variable [IsDomain R] [IsDomain S]

theorem ordMonoidWithZeroHom_ringEquiv (e : R ≃+* S) (a : R) :
    Ring.ordMonoidWithZeroHom S (e a) = Ring.ordMonoidWithZeroHom R a := by
  by_cases ha : a = 0
  · simp [ha]
  have hea : e a ≠ 0 := (map_ne_zero_iff _ e.injective).mpr ha
  rw [Ring.ordMonoidWithZeroHom_eq_ord (mem_nonZeroDivisors_iff_ne_zero.mpr hea),
    Ring.ordMonoidWithZeroHom_eq_ord (mem_nonZeroDivisors_iff_ne_zero.mpr ha),
    ord_ringEquiv e a]

variable [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
  [IsNoetherianRing S] [Ring.KrullDimLE 1 S]
  {K L : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra S L] [IsFractionRing S L]

/-- The entire normalized fraction order survives the original local coefficient square. -/
theorem ordFrac_ringEquiv (e : R ≃+* S) (φ : K →+* L)
    (hcoeff : ∀ a : R, φ (algebraMap R K a) = algebraMap S L (e a)) (g : K) :
    Ring.ordFrac S (φ g) = Ring.ordFrac R g := by
  have hc (a : R) : Ring.ordFrac S (algebraMap S L (e a)) =
      Ring.ordFrac R (algebraMap R K a) := by
    by_cases ha : a = 0
    · simp [ha]
    have hea : e a ≠ 0 := (map_ne_zero_iff _ e.injective).mpr ha
    rw [Ring.ordFrac_eq_ord S hea, Ring.ordFrac_eq_ord R ha]
    exact ordMonoidWithZeroHom_ringEquiv e a
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) g
  rw [map_div₀, hcoeff a, hcoeff b, map_div₀, map_div₀, hc a, hc b]

end PrincipalOrder

section Localization

/-- Clearing the SAME original localization denominators proves the genuine fraction-field
structure on the original base, rather than on an unrelated abstract fraction field. -/
theorem fractionField_of_localization_tower
    {B C F : Type u} [CommRing B] [CommRing C] [Field F]
    [Algebra B C] [Algebra B F] [Algebra C F] [IsScalarTower B C F]
    [FaithfulSMul B F] (M : Submonoid B) [IsLocalization M C] [IsFractionRing C F] :
    IsFractionRing B F := by
  apply IsFractionRing.of_field B F
  intro z
  obtain ⟨f, g, _, hz⟩ := IsFractionRing.div_surjective C z
  obtain ⟨a, b, s, ha, hb⟩ := IsLocalization.surj₂ M C f g
  have hs : algebraMap B F (s : B) ≠ 0 := by
    have h := (IsLocalization.map_units C s).map (algebraMap C F)
    simpa only [IsScalarTower.algebraMap_apply B C F] using h.ne_zero
  have haF : algebraMap C F f * algebraMap B F (s : B) = algebraMap B F a := by
    simpa only [map_mul, IsScalarTower.algebraMap_apply B C F] using
      congrArg (algebraMap C F) ha
  have hbF : algebraMap C F g * algebraMap B F (s : B) = algebraMap B F b := by
    simpa only [map_mul, IsScalarTower.algebraMap_apply B C F] using
      congrArg (algebraMap C F) hb
  refine ⟨a, b, ?_⟩
  rw [← hz, ← haF, ← hbF, mul_div_mul_right _ _ hs]

/-- A prime localization of the original domain has the same original fraction field. -/
theorem fractionField_of_primeLocalization
    (B C F : Type u) [CommRing B] [IsDomain B] [CommRing C] [IsDomain C] [Field F]
    [Algebra B C] [Algebra B F] [Algebra C F] [IsScalarTower B C F]
    (p : Ideal B) [p.IsPrime] [IsLocalization.AtPrime C p] [IsFractionRing C F] :
    IsFractionRing B F := by
  have hBC : Function.Injective (algebraMap B C) :=
    IsLocalization.injective C (Ideal.primeCompl_le_nonZeroDivisors p)
  have hBF : Function.Injective (algebraMap B F) := by
    rw [IsScalarTower.algebraMap_eq B C F]
    exact (IsFractionRing.injective C F).comp hBC
  let : FaithfulSMul B F := (faithfulSMul_iff_algebraMap_injective B F).mpr hBF
  exact fractionField_of_localization_tower (C := C) p.primeCompl

variable {B C R K L : Type u} [CommRing B] [CommRing C] [CommRing R]
  [Field K] [Field L] [Algebra B C] [Algebra B R]
  [Algebra B K] [Algebra C K] [IsScalarTower B C K]
  [Algebra B L] [Algebra R L] [IsScalarTower B R L]
  [IsFractionRing B K] [IsFractionRing B L]

/-- The original coefficient square of the canonical field and prime-localization
isomorphisms is proved by localization uniqueness, not supplied as a hypothesis. -/
theorem primeLocalization_fieldSquare (p : Ideal B) [p.IsPrime]
    [IsLocalization.AtPrime C p] [IsLocalization.AtPrime R p] (c : C) :
    IsLocalization.algEquiv (nonZeroDivisors B) K L (algebraMap C K c) =
      algebraMap R L (IsLocalization.algEquiv p.primeCompl C R c) := by
  have hmaps : (IsLocalization.algEquiv (nonZeroDivisors B) K L).toRingHom.comp
      (algebraMap C K) =
      (algebraMap R L).comp (IsLocalization.algEquiv p.primeCompl C R).toRingHom := by
    apply IsLocalization.ringHom_ext p.primeCompl
    apply RingHom.ext
    intro b
    change IsLocalization.algEquiv (nonZeroDivisors B) K L
        (algebraMap C K (algebraMap B C b)) =
      algebraMap R L (IsLocalization.algEquiv p.primeCompl C R (algebraMap B C b))
    rw [← IsScalarTower.algebraMap_apply B C K, AlgEquiv.commutes, AlgEquiv.commutes,
      ← IsScalarTower.algebraMap_apply B R L]
  exact RingHom.congr_fun hmaps c

/-- The two actual localizations at the SAME prime preserve normalized fraction order. -/
theorem primeLocalization_ordFrac (p : Ideal B) [p.IsPrime]
    [IsLocalization.AtPrime C p] [IsLocalization.AtPrime R p]
    [IsDomain C] [IsDomain R] [IsNoetherianRing C] [IsNoetherianRing R]
    [Ring.KrullDimLE 1 C] [Ring.KrullDimLE 1 R]
    [IsFractionRing C K] [IsFractionRing R L] (g : K) :
    Ring.ordFrac R (IsLocalization.algEquiv (nonZeroDivisors B) K L g) =
      Ring.ordFrac C g :=
  ordFrac_ringEquiv (IsLocalization.algEquiv p.primeCompl C R).toRingEquiv
    (IsLocalization.algEquiv (nonZeroDivisors B) K L).toRingHom
    (primeLocalization_fieldSquare p) g

end Localization

section NativeModel

/-- An actual DVR stalk has codimension one on its native scheme. -/
theorem coheight_eq_one_of_stalk_dvr {M : Scheme.{0}} (z : M)
    [IsDomain (M.presheaf.stalk z)] [IsDiscreteValuationRing (M.presheaf.stalk z)] :
    Order.coheight z = 1 := by
  have h := IsDiscreteValuationRing.ringKrullDim_eq_one (M.presheaf.stalk z)
  rw [ringKrullDim_stalk_eq_coheight] at h
  exact_mod_cast h

variable {X M : Scheme.{0}} [IsIntegral M] [IsLocallyNoetherian M]
  (D : PrimeDivisorOver X) (z : M) {B : Type} [CommRing B] [IsDomain B]
  [Algebra B (M.presheaf.stalk z)] [Algebra B (D.Y.presheaf.stalk D.point)]
  [Algebra B M.functionField] [Algebra B D.Y.functionField]
  [IsScalarTower B (M.presheaf.stalk z) M.functionField]
  [IsScalarTower B (D.Y.presheaf.stalk D.point) D.Y.functionField]

/-- The original divisor and native model stalk, both actual localizations of `B` at `p`,
produce the original coefficient field isomorphism AND the complete original order identity.
The DVR structure and codimension-one statement on the model are conclusions. -/
theorem exists_modelOrder (p : Ideal B) [p.IsPrime]
    [IsLocalization.AtPrime (M.presheaf.stalk z) p]
    [IsLocalization.AtPrime (D.Y.presheaf.stalk D.point) p] :
    IsDiscreteValuationRing (M.presheaf.stalk z) ∧ Order.coheight z = 1 ∧
      ∃ e : M.functionField ≃+* D.Y.functionField,
        (∀ b : B, e (algebraMap B M.functionField b) =
          algebraMap B D.Y.functionField b) ∧
        ∀ g : X.residueField (D.π (genericPoint D.Y)),
          D.ord g = Scheme.ord (e.symm (D.pullback g)) z := by
  let C := M.presheaf.stalk z
  let R := D.Y.presheaf.stalk D.point
  let : IsFractionRing B M.functionField :=
    fractionField_of_primeLocalization B C M.functionField p
  let : IsFractionRing B D.Y.functionField :=
    fractionField_of_primeLocalization B R D.Y.functionField p
  let localEquiv : C ≃ₐ[B] R := IsLocalization.algEquiv p.primeCompl C R
  let : IsDiscreteValuationRing C :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing localEquiv.symm
  have hz : Order.coheight z = 1 := coheight_eq_one_of_stalk_dvr z
  let e : M.functionField ≃ₐ[B] D.Y.functionField :=
    IsLocalization.algEquiv (nonZeroDivisors B) M.functionField D.Y.functionField
  refine ⟨inferInstance, hz, e.toRingEquiv, e.commutes, ?_⟩
  intro g
  rw [PrimeDivisorOver.ord, Scheme.ord_eq_ordHom_of_coheight_eq_one D.coheight_point,
    Scheme.ord_eq_ordHom_of_coheight_eq_one hz]
  have horder := primeLocalization_ordFrac (C := C) (R := R)
    (K := M.functionField) (L := D.Y.functionField) p (e.symm (D.pullback g))
  change Ring.ordFrac R (e (e.symm (D.pullback g))) =
    Ring.ordFrac C (e.symm (D.pullback g)) at horder
  rw [e.apply_symm_apply] at horder
  exact congrArg (fun v : ℤᵐ⁰ => Multiplicative.toAdd (v.unzeroD 1)) horder

/-- A genuine graph projection need only be identified on the original affine coefficients.
Localization uniqueness proves its full rational-function pullback and the original divisor
order comparison.  No equality of orders or field maps is an input. -/
theorem modelOrder_of_projection_coefficients (p : Ideal B) [p.IsPrime]
    [IsLocalization.AtPrime (M.presheaf.stalk z) p]
    [IsLocalization.AtPrime (D.Y.presheaf.stalk D.point) p]
    {A : Type} [CommRing A]
    [Algebra A (X.residueField (D.π (genericPoint D.Y)))]
    [IsFractionRing A (X.residueField (D.π (genericPoint D.Y)))]
    (j : A →+* B)
    (ψ : X.residueField (D.π (genericPoint D.Y)) →+* M.functionField)
    (hψ : ∀ a : A, ψ (algebraMap A _ a) = algebraMap B M.functionField (j a))
    (hD : ∀ a : A, D.pullback (algebraMap A _ a) =
      algebraMap B D.Y.functionField (j a)) :
    IsDiscreteValuationRing (M.presheaf.stalk z) ∧ Order.coheight z = 1 ∧
      ∀ g : X.residueField (D.π (genericPoint D.Y)),
        D.ord g = Scheme.ord (ψ g) z := by
  obtain ⟨hDVR, hz, e, he, hord⟩ := exists_modelOrder D z p
  have hmaps : e.toRingHom.comp ψ = D.pullback := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors A)
    apply RingHom.ext
    intro a
    change e (ψ (algebraMap A _ a)) = D.pullback (algebraMap A _ a)
    rw [hψ, he, hD]
  refine ⟨hDVR, hz, fun g => ?_⟩
  rw [hord g, ← RingHom.congr_fun hmaps g]
  exact congrArg (fun t => Scheme.ord t z) (e.symm_apply_apply (ψ g))

end NativeModel

section ConstructLocalization

open SGPT.NAPotential.AlgPrimes3.PrimeDivisorOver'

variable {X : Scheme.{0}} (D : PrimeDivisorOver X)

/-- Nonnegative original divisor order constructs the actual coefficient map into `R_D`. -/
theorem exists_toDivisorStalk
    (B : Subring (X.residueField (D.π (genericPoint D.Y))))
    (hB : ∀ g ∈ B, g ≠ 0 → 0 ≤ D.ord g) :
    ∃ i : B →+* D.Y.presheaf.stalk D.point,
      ∀ b : B, algebraMap (D.Y.presheaf.stalk D.point) D.Y.functionField (i b) =
        D.pullback b := by
  classical
  let R := D.Y.presheaf.stalk D.point
  have hmem (b : B) : D.pullback b ∈ (algebraMap R D.Y.functionField).range := by
    by_cases hb : (b : X.residueField (D.π (genericPoint D.Y))) = 0
    · simp [hb]
    exact (ord_nonneg_iff_mem_range D hb).mp (hB b b.2 hb)
  let i (b : B) : R := Classical.choose (hmem b)
  have hi (b : B) : algebraMap R D.Y.functionField (i b) = D.pullback b :=
    Classical.choose_spec (hmem b)
  have hinj := IsFractionRing.injective R D.Y.functionField
  refine ⟨{ toFun := i
            map_one' := ?_
            map_mul' := ?_
            map_zero' := ?_
            map_add' := ?_ }, hi⟩
  · apply hinj
    simp only [hi, Subring.coe_one, map_one]
  · intro a b
    apply hinj
    rw [map_mul, hi, hi, hi]
    exact D.pullback.map_mul a b
  · apply hinj
    simp only [hi, Subring.coe_zero, map_zero]
  · intro a b
    apply hinj
    rw [map_add, hi, hi, hi]
    exact D.pullback.map_add a b

/-- The actual order/fraction assertions of the original affine generators construct a
genuine prime localization of the original divisor stalk. -/
theorem exists_primeLocalization_of_orderFractions
    (B : Subring (X.residueField (D.π (genericPoint D.Y))))
    (hB : ∀ g ∈ B, g ≠ 0 → 0 ≤ D.ord g)
    (hfrac : ∀ g : X.residueField (D.π (genericPoint D.Y)), g ≠ 0 → 0 ≤ D.ord g →
      ∃ a ∈ B, ∃ c ∈ B, c ≠ 0 ∧ D.ord c = 0 ∧ g * c = a) :
    ∃ i : B →+* D.Y.presheaf.stalk D.point,
      (∀ b : B, algebraMap (D.Y.presheaf.stalk D.point) D.Y.functionField (i b) =
        D.pullback b) ∧
      letI := i.toAlgebra
      IsLocalization.AtPrime (D.Y.presheaf.stalk D.point)
        ((maximalIdeal (D.Y.presheaf.stalk D.point)).comap i) := by
  classical
  let R := D.Y.presheaf.stalk D.point
  obtain ⟨i, hi⟩ := exists_toDivisorStalk D B hB
  refine ⟨i, hi, ?_⟩
  let : Algebra B R := i.toAlgebra
  let p : Ideal B := (maximalIdeal R).comap i
  have hinj : Function.Injective i := by
    intro a b hab
    apply Subtype.ext
    apply D.pullback_injective
    rw [← hi a, ← hi b, hab]
  change IsLocalization p.primeCompl R
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro c
    exact IsLocalRing.notMem_maximalIdeal.mp c.2
  · intro r
    by_cases hr : r = 0
    · exact ⟨⟨0, 1⟩, by simp [hr]⟩
    let g := (pullbackEquiv D).symm (algebraMap R D.Y.functionField r)
    have hg : g ≠ 0 := by
      apply (map_ne_zero_iff _ (pullbackEquiv D).symm.injective).mpr
      exact (map_ne_zero_iff _ (IsFractionRing.injective R D.Y.functionField)).mpr hr
    have hpg : D.pullback g = algebraMap R D.Y.functionField r :=
      (pullbackEquiv D).apply_symm_apply _
    have hgord : 0 ≤ D.ord g :=
      (ord_nonneg_iff_mem_range D hg).mpr ⟨r, hpg.symm⟩
    obtain ⟨a, ha, c, hc, hc0, hcord, hac⟩ := hfrac g hg hgord
    let a' : B := ⟨a, ha⟩
    let c' : B := ⟨c, hc⟩
    have hcunit : IsUnit (i c') := by
      apply (Ring.isUnit_iff_ordFrac_one_of_isDiscreteValuationRing
        (K := D.Y.functionField)).mpr
      have hpc : D.pullback c ≠ 0 :=
        (map_ne_zero_iff _ D.pullback_injective).mpr hc0
      have hnorm := (Scheme.ord_eq_iff D.coheight_point hpc).mp hcord
      change Ring.ordFrac R (D.pullback c) = 1 at hnorm
      rw [hi c']
      exact hnorm
    have hcprime : c' ∈ p.primeCompl := IsLocalRing.notMem_maximalIdeal.mpr hcunit
    refine ⟨⟨a', ⟨c', hcprime⟩⟩, ?_⟩
    apply IsFractionRing.injective R D.Y.functionField
    change algebraMap R D.Y.functionField (r * i c') = algebraMap R D.Y.functionField (i a')
    rw [map_mul, hi c', hi a', ← hpg, ← map_mul, hac]
  · intro a b hab
    exact ⟨1, by simpa using hinj hab⟩

/-- The original affine generators now yield an ACTUAL localization instance for the
literal subalgebra `A[b]` of the checked native projective graph chart. -/
theorem exists_affine_generators_primeLocalization :
    ∃ (U : X.Opens) (_ : IsAffineOpen U) (hU : D.π (genericPoint D.Y) ∈ U)
      (_ : D.π D.point ∈ U) (s : ℕ)
      (b : Fin s → X.residueField (D.π (genericPoint D.Y))),
      letI := (sectionToField D U hU).toAlgebra
      ∃ i : Algebra.adjoin Γ(X, U) (Set.range b) →+* D.Y.presheaf.stalk D.point,
        (∀ v : Algebra.adjoin Γ(X, U) (Set.range b),
          algebraMap (D.Y.presheaf.stalk D.point) D.Y.functionField (i v) = D.pullback v) ∧
        letI := i.toAlgebra
        IsLocalization.AtPrime (D.Y.presheaf.stalk D.point)
          ((maximalIdeal (D.Y.presheaf.stalk D.point)).comap i) := by
  obtain ⟨U, hUa, hU, hpU, s, b, hB, hfrac⟩ := exists_affine_generators D
  refine ⟨U, hUa, hU, hpU, s, b, ?_⟩
  let : Algebra Γ(X, U) (X.residueField (D.π (genericPoint D.Y))) :=
    (sectionToField D U hU).toAlgebra
  have hd := SGPT.NAPotential.AlgPrimes3.ProjectiveGraphRelations.adjoin_toSubring_eq
    (A := Γ(X, U)) b
  change (Algebra.adjoin Γ(X, U) (Set.range b)).toSubring =
    Subring.closure (Set.range (sectionToField D U hU) ∪ Set.range b) at hd
  have hloc := exists_primeLocalization_of_orderFractions D _ hB hfrac
  rw [← hd] at hloc
  exact hloc

end ConstructLocalization

end SGPT.NAPotential.GraphDivisorOrderTransport
