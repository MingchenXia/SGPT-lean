import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.Smooth.Field
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Artinian.Algebra
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.Polynomial.Ideal

/-!
# Smoothness at a discrete valuation centre

The local algebra for step (d) of `AlgPrimes3`: a separating residue
transcendence basis gives a coefficient field inside the actual local ring,
and a uniformizer gives an unramified flat polynomial parameter.

Blueprint: `regular-prime-smooth.tex`.  This module uses only Mathlib.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.RegularPrimeSmooth

open IsLocalRing
open scoped TensorProduct Polynomial nonZeroDivisors

universe u

section ResidueLifts

variable {k R : Type u} [Field k] [CommRing R] [IsLocalRing R] [Algebra k R]
  {ι : Type u} (u : ι → R)

/-- Reduction of a polynomial in actual lifts is evaluation in their residues. -/
theorem residue_aeval (p : MvPolynomial ι k) :
    residue R (MvPolynomial.aeval u p) = MvPolynomial.aeval (residue R ∘ u) p := by
  exact DFunLike.congr_fun (MvPolynomial.comp_aeval (R := k) (f := u)
    (Ideal.Quotient.mkₐ k (maximalIdeal R))) p

/-- Independent residues force every nonzero polynomial in their lifts to be a unit. -/
theorem isUnit_aeval_of_residue_algebraicIndependent
    (hu : AlgebraicIndependent k (residue R ∘ u)) {p : MvPolynomial ι k} (hp : p ≠ 0) :
    IsUnit (MvPolynomial.aeval u p) := by
  rw [← residue_ne_zero_iff_isUnit, residue_aeval]
  exact fun h => hp (hu (h.trans (map_zero _).symm))

end ResidueLifts

section LocalFlatUnramified

variable (A R : Type u) [CommRing A] [CommRing R] [Algebra A R]
  [IsLocalRing A] [IsLocalRing R] [IsLocalHom (algebraMap A R)]
  [IsNoetherianRing A] [Algebra.EssFiniteType A R]
  [Module.Flat A R] [Algebra.FormallyUnramified A R]

/-- The essentially finite-type local form of flat and unramified implies smooth.
The finite-presentation model and smooth residue fibre are produced internally. -/
theorem formallySmooth_of_flat_unramified_local : Algebra.FormallySmooth A R := by
  let B := Algebra.EssFiniteType.subalgebra A R
  let : Algebra.FinitePresentation A B := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let : Algebra.FormallyEtale (ResidueField A) (ResidueField A ⊗[A] R) :=
    Algebra.FormallyEtale.of_formallyUnramified_of_field _ _
  exact Algebra.FormallySmooth.of_formallySmooth_residueField_tensor
    (Algebra.EssFiniteType.submonoid A R)

end LocalFlatUnramified

section CoefficientLift

variable {k R : Type u} [Field k] [CommRing R] [IsLocalRing R] [Algebra k R]
  {ι : Type u} (u : ι → R) (hu : AlgebraicIndependent k (residue R ∘ u))

/-- The rational function field of a residue-independent family maps into the actual local ring. -/
def rationalCoefficientLift : FractionRing (MvPolynomial ι k) →ₐ[k] R :=
  IsLocalization.liftAlgHom (M := nonZeroDivisors (MvPolynomial ι k))
    (S := FractionRing (MvPolynomial ι k)) (f := MvPolynomial.aeval u)
      fun p => isUnit_aeval_of_residue_algebraicIndependent u hu
        (mem_nonZeroDivisors_iff_ne_zero.mp p.2)

@[simp]
theorem rationalCoefficientLift_algebraMap (p : MvPolynomial ι k) :
    rationalCoefficientLift u hu (algebraMap _ (FractionRing (MvPolynomial ι k)) p) =
      MvPolynomial.aeval u p :=
  IsLocalization.lift_eq _ p

/-- The literal residue coefficient field has an actual lift into the original local ring. -/
def residueCoefficientLift :
    IntermediateField.adjoin k (Set.range (residue R ∘ u)) →ₐ[k] R :=
  (rationalCoefficientLift u hu).comp hu.aevalEquivField.symm.toAlgHom

/-- Every coefficient has exactly its original residue after lifting. -/
theorem residue_residueCoefficientLift
    (x : IntermediateField.adjoin k (Set.range (residue R ∘ u))) :
    residue R (residueCoefficientLift u hu x) = x.1 := by
  let E := IntermediateField.adjoin k (Set.range (residue R ∘ u))
  let φ : R →ₐ[k] ResidueField R := Ideal.Quotient.mkₐ k (maximalIdeal R)
  have heq : (φ.comp (rationalCoefficientLift u hu)).toRingHom =
      (E.val.comp hu.aevalEquivField.toAlgHom).toRingHom := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors (MvPolynomial ι k))
    apply RingHom.ext
    intro p
    change residue R (rationalCoefficientLift u hu
      (algebraMap _ (FractionRing (MvPolynomial ι k)) p)) =
        (hu.aevalEquivField (algebraMap _ (FractionRing (MvPolynomial ι k)) p)).1
    rw [rationalCoefficientLift_algebraMap, residue_aeval]
    exact (hu.aevalEquivField_algebraMap_apply_coe p).symm
  have h := RingHom.congr_fun heq (hu.aevalEquivField.symm x)
  change residue R (rationalCoefficientLift u hu (hu.aevalEquivField.symm x)) = x.1
  change residue R (rationalCoefficientLift u hu (hu.aevalEquivField.symm x)) =
    (hu.aevalEquivField (hu.aevalEquivField.symm x)).1 at h
  simpa only [AlgEquiv.apply_symm_apply] using h

end CoefficientLift


section Uniformizer

variable {E B : Type u} [Field E] [CommRing B] [IsDomain B] [Algebra E B]
  (p : Ideal B) [p.IsPrime] [IsDiscreteValuationRing (Localization.AtPrime p)]

/-- A numerator of an actual uniformizer generates the local maximal ideal. -/
theorem exists_local_parameter :
    ∃ r : B, r ∈ p ∧ r ≠ 0 ∧
      maximalIdeal (Localization.AtPrime p) =
        Ideal.span {algebraMap B (Localization.AtPrime p) r} := by
  let S := Localization.AtPrime p
  obtain ⟨z, hz⟩ := IsDiscreteValuationRing.exists_irreducible S
  obtain ⟨r, s, he⟩ := IsLocalization.exists_mk'_eq p.primeCompl z
  have hs : IsUnit (algebraMap B S s) := IsLocalization.map_units S s
  have hspec : algebraMap B S r = z * algebraMap B S s := by
    rw [← he]
    exact (IsLocalization.mk'_spec S r s).symm
  have hspan : maximalIdeal S = Ideal.span {algebraMap B S r} := by
    rw [hspec, Ideal.span_singleton_mul_right_unit hs]
    exact hz.maximalIdeal_eq
  refine ⟨r, ?_, ?_, hspan⟩
  · apply (IsLocalization.AtPrime.to_map_mem_maximal_iff S p r).mp
    rw [hspan]
    exact Ideal.mem_span_singleton_self _
  · intro hr
    have hz0 : z = 0 := by
      apply hs.mul_right_cancel
      rw [← hspec, hr, map_zero, zero_mul]
    exact hz.ne_zero hz0

/-- A uniformizer numerator produces smoothness, using a separable residue extension. -/
theorem formallySmooth_at_of_dvr_separable_residue [Algebra.FiniteType E B]
    [Algebra.IsSeparable E p.ResidueField] : Algebra.IsSmoothAt E p := by
  obtain ⟨r, hrp, hr0, hgen⟩ := exists_local_parameter p
  have hru : ¬IsUnit r := fun hu => (inferInstance : p.IsPrime).ne_top
    (p.eq_top_of_isUnit_mem hrp hu)
  have htr : Transcendental E r := by
    intro h
    exact hru (IsArtinianRing.isUnit_of_isIntegral_of_nonZeroDivisor h.isIntegral
      (mem_nonZeroDivisors_iff_ne_zero.mpr hr0))
  have hinj := (transcendental_iff_injective (R := E) (x := r)).mp htr
  let A := E[X]
  let f : A →ₐ[E] B := Polynomial.aeval r
  let : Algebra A B := f.toRingHom.toAlgebra
  let : IsScalarTower E A B := .of_algebraMap_eq fun c => (f.commutes c).symm
  let : Module.IsTorsionFree A B := Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  let : Module.Flat A B := inferInstance
  let : Algebra.FiniteType A B := Algebra.FiniteType.of_restrictScalars_finiteType E A B
  let : Algebra.FinitePresentation A B := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let q : Ideal A := Ideal.span {(Polynomial.X : E[X])}
  have hqker : q = RingHom.ker (Polynomial.evalRingHom (0 : E)) := by
    rw [Polynomial.ker_evalRingHom]
    simp only [map_zero, sub_zero]
    rfl
  let : q.IsPrime := hqker.symm ▸ RingHom.ker_isPrime _
  have hres : (Ideal.Quotient.mk p).comp f.toRingHom =
      (algebraMap E (B ⧸ p)).comp (Polynomial.evalRingHom (0 : E)) := by
    apply Polynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        Polynomial.coe_evalRingHom, Polynomial.eval_C]
      rw [show f (Polynomial.C c) = algebraMap E B c from Polynomial.aeval_C r c]
      rfl
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        Polynomial.coe_evalRingHom, Polynomial.eval_X, map_zero]
      rw [show f Polynomial.X = r from Polynomial.aeval_X r]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hrp
  have hcomap : p.comap (algebraMap A B) = q := by
    change p.comap f.toRingHom = q
    rw [← Ideal.mk_ker (I := p), RingHom.comap_ker, hres,
      RingHom.ker_comp_of_injective _ (algebraMap E (B ⧸ p)).injective, ← hqker]
  let : p.LiesOver q := ⟨hcomap.symm⟩
  let locAlg : Algebra (Localization.AtPrime q) (Localization.AtPrime p) :=
    Localization.AtPrime.algebraOfLiesOver q p
  let : Algebra (Localization.AtPrime q) (Localization.AtPrime p) := locAlg
  let locCompat : Localization.AtPrime.IsLiesOverAlgebra (A := A) (B := B) q p := by
    constructor
    exact RingHom.algebraMap_toAlgebra _
  let qLocal : IsLocalRing (Localization.AtPrime q) :=
    IsLocalization.AtPrime.isLocalRing (Localization.AtPrime q) q
  let pLocal : IsLocalRing (Localization.AtPrime p) :=
    IsLocalization.AtPrime.isLocalRing (Localization.AtPrime p) p
  let hlocal : IsLocalHom (@algebraMap (Localization.AtPrime q) (Localization.AtPrime p) _ _ locAlg) := by
    change IsLocalHom (Localization.localRingHom q p (algebraMap A B) Ideal.LiesOver.over)
    infer_instance
  let : Algebra q.ResidueField p.ResidueField :=
    @IsLocalRing.ResidueField.instAlgebra
      (Localization.AtPrime q) (Localization.AtPrime p)
      (inferInstance : CommRing (Localization.AtPrime q)) qLocal
      (inferInstance : CommRing (Localization.AtPrime p)) pLocal locAlg hlocal
  let hELoc : @IsScalarTower E (Localization.AtPrime q) (Localization.AtPrime p)
      (inferInstance : SMul E (Localization.AtPrime q)) locAlg.toSMul
      (inferInstance : SMul E (Localization.AtPrime p)) := by
    apply IsScalarTower.of_algebraMap_eq
    intro c
    simp only [IsScalarTower.algebraMap_apply E A (Localization.AtPrime q),
      IsScalarTower.algebraMap_apply E B (Localization.AtPrime p),
      RingHom.algebraMap_toAlgebra, Localization.localRingHom_to_map,
      AlgHom.toRingHom_eq_coe]
    exact congrArg (algebraMap B (Localization.AtPrime p)) (f.commutes c).symm
  let : IsScalarTower E q.ResidueField p.ResidueField :=
    @IsLocalRing.ResidueField.instIsScalarTower
      (Localization.AtPrime q) (Localization.AtPrime p)
      (inferInstance : CommRing (Localization.AtPrime q)) qLocal
      (inferInstance : CommRing (Localization.AtPrime p)) pLocal locAlg hlocal E _ _ _ hELoc
  let hsep : Algebra.IsSeparable q.ResidueField p.ResidueField :=
    ⟨fun x => IsSeparable.tower_top q.ResidueField (Algebra.IsSeparable.isSeparable E x)⟩
  have hqgen : q.map (algebraMap A (Localization.AtPrime p)) = maximalIdeal (Localization.AtPrime p) := by
    rw [Ideal.map_span, Set.image_singleton]
    have hX : algebraMap A (Localization.AtPrime p) Polynomial.X =
        algebraMap B (Localization.AtPrime p) r := by
      rw [IsScalarTower.algebraMap_apply A B (Localization.AtPrime p)]
      congr 1
      exact Polynomial.aeval_X r
    rw [hX]
    exact hgen.symm
  have hcrit := @Algebra.isUnramifiedAt_iff_map_eq A B _ _
    (inferInstance : Algebra A B) (inferInstance : Algebra.EssFiniteType A B)
    q inferInstance p inferInstance inferInstance locAlg locCompat
  let : Algebra.IsUnramifiedAt A p := hcrit.mpr ⟨hsep, hqgen⟩
  let : Algebra.IsEtaleAt A p := Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat p
  exact Algebra.FormallySmooth.comp E A (Localization.AtPrime p)

end Uniformizer

section LocalDVR

variable (E R : Type u) [Field E] [CommRing R] [IsDomain R] [Algebra E R]
  [IsDiscreteValuationRing R] [Algebra.EssFiniteType E R]
  [Algebra.IsSeparable E (ResidueField R)]

/-- An actual DVR with algebraic separable residue extension is formally smooth. -/
theorem formallySmooth_of_dvr_separable_residue : Algebra.FormallySmooth E R := by
  let B := Algebra.EssFiniteType.subalgebra E R
  let p : Ideal B := (maximalIdeal R).comap (algebraMap B R)
  have hM : Algebra.EssFiniteType.submonoid E R = p.primeCompl := by
    ext a
    change IsUnit (algebraMap B R a) ↔ algebraMap B R a ∉ maximalIdeal R
    simp only [mem_maximalIdeal, mem_nonunits_iff, not_not]
  have : IsLocalization.AtPrime R p := by
    change IsLocalization p.primeCompl R
    rw [← hM]
    infer_instance
  let e := (IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p) R).restrictScalars E
  let : IsDiscreteValuationRing (Localization.AtPrime p) :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e.symm
  let : Algebra.IsSeparable E p.ResidueField :=
    (AlgEquiv.Algebra.isSeparable_iff (ResidueField.mapAlgEquiv e)).mpr inferInstance
  let : Algebra.IsSmoothAt E p := formallySmooth_at_of_dvr_separable_residue p
  exact Algebra.FormallySmooth.of_equiv e

end LocalDVR


section PerfectDVR

/-- A DVR essentially of finite type over a perfect field is formally smooth. -/
theorem formallySmooth_of_dvr (k R : Type u) [Field k] [PerfectField k]
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Algebra k R]
    [Algebra.EssFiniteType k R] : Algebra.FormallySmooth k R := by
  let : Algebra.EssFiniteType k (ResidueField R) :=
    inferInstanceAs (Algebra.EssFiniteType k (R ⧸ maximalIdeal R))
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField k (ResidueField R)
  choose u hu using fun x : s => residue_surjective (R := R) (x : ResidueField R)
  have hres : residue R ∘ u = ((↑) : s → ResidueField R) := funext hu
  have hind : AlgebraicIndependent k (residue R ∘ u) := hres ▸ hs.1
  let E := IntermediateField.adjoin k (Set.range (residue R ∘ u))
  let residueAction : Algebra E (ResidueField R) := inferInstance
  have hsepE : @Algebra.IsSeparable E (ResidueField R) _ _ residueAction := by
    have hE : E = IntermediateField.adjoin k (s : Set (ResidueField R)) := by
      dsimp only [E]
      rw [hres, Subtype.range_coe]
    let e := IntermediateField.equivOfEq hE
    let : Algebra.IsSeparable (IntermediateField.adjoin k (s : Set (ResidueField R)))
        (ResidueField R) := hsep
    exact Algebra.IsSeparable.of_equiv_equiv e.symm.toRingEquiv
      (RingEquiv.refl (ResidueField R)) (by ext x; rfl)
  let c : E →ₐ[k] R := residueCoefficientLift u hind
  let : Algebra E R := c.toAlgebra
  let : IsScalarTower k E R := IsScalarTower.of_algebraMap_eq fun a => (c.commutes a).symm
  let nativeResidueAction : Algebra E (ResidueField R) :=
    @IsLocalRing.ResidueField.algebra R _ _ E _ c.toAlgebra
  have haction : nativeResidueAction = residueAction := by
    apply Algebra.algebra_ext
    intro x
    exact residue_residueCoefficientLift u hind x
  let : @Algebra.IsSeparable E (ResidueField R) _ _ nativeResidueAction := by
    rw [haction]
    exact hsepE
  let : Algebra.EssFiniteType E R := Algebra.EssFiniteType.of_comp k E R
  let : Algebra.FormallySmooth E R := formallySmooth_of_dvr_separable_residue E R
  let : Algebra.FormallySmooth k E :=
    Algebra.FormallySmooth.adjoin_of_algebraicIndependent hind
  exact Algebra.FormallySmooth.comp k E R

end PerfectDVR

section SmoothPrincipal

variable (k B : Type u) [Field k] [PerfectField k] [CommRing B] [IsDomain B]
  [Algebra k B] [Algebra.FiniteType k B]

/-- The actual finite-type model is smooth at its original discrete valuation centre. -/
theorem isSmoothAt_of_dvr (p : Ideal B) [p.IsPrime]
    [IsDiscreteValuationRing (Localization.AtPrime p)] : Algebra.IsSmoothAt k p := by
  let : Algebra.EssFiniteType k (Localization.AtPrime p) := Algebra.EssFiniteType.comp k B _
  exact formallySmooth_of_dvr k (Localization.AtPrime p)

/-- The smooth affine principal open meeting the original divisorial centre. -/
theorem exists_notMem_smooth_of_dvr (p : Ideal B) [p.IsPrime]
    [IsDiscreteValuationRing (Localization.AtPrime p)] :
    ∃ s ∉ p, Algebra.Smooth k (Localization.Away s) := by
  let : Algebra.FinitePresentation k B := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let : Algebra.IsSmoothAt k p := isSmoothAt_of_dvr k B p
  exact Algebra.IsSmoothAt.exists_notMem_smooth k p

end SmoothPrincipal

end SGPT.NAPotential.RegularPrimeSmooth
