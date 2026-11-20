import SGPT.Unibranch.UnibAlgPowerSeries
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Adjoin.PowerBasis
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Base change of a finite domain along `ℂ[w] → ℂ⟦w⟧`: the primitive-element model

Let `A` be a domain, finite and torsion-free over `P₀ = ℂ[w₁, …, w_d]`, and `D = ℂ⟦w⟧ ⊗_{P₀} A`.
Choose `θ ∈ A` generating the fraction field `L` of `A` over `F = ℂ(w)` (primitive element,
characteristic zero) with minimal polynomial `f ∈ P₀[X]`, and let `K₀` be the fraction field of
`ℂ⟦w⟧` and `f_K` the image of `f` in `K₀[X]`.

* `PrimData.Φ`: the ring map `D → K₀[X] / (f_K)`, `t ⊗ a ↦ t · a(root)`;
* `PrimData.Φ_injective`: it is injective. The proof uses the discriminant `δ` of the power
  basis (`δ A ⊆ P₀[θ]`), the flatness of `ℂ⟦w⟧` over `P₀` and the basis `1, …, Xʳ⁻¹`;
* `PrimData.squarefree_fK`: `f_K` is squarefree (Bezout relation `A f + B f' = δ'` over `P₀`);
* `isReduced_tensor`: hence `D` is reduced (analytic unramifiedness for finite extensions of the
  polynomial ring).

Lane UNIB-ALG, step U3 (d) of `claude-serre-gaga.tex`; blueprint `claude-unib-alg.tex`.
-/

set_option autoImplicit false

open Polynomial TensorProduct

namespace SGPT.Unibranch.UnibAlg

noncomputable section

variable {d : ℕ}

local notation "P₀" => MvPolynomial (Fin d) ℂ
local notation "T₀" => MvPowerSeries (Fin d) ℂ

/-- The fraction field of `ℂ⟦w⟧`. -/
abbrev K₀ (d : ℕ) := FractionRing (MvPowerSeries (Fin d) ℂ)

/-- `ℂ[w] → Frac ℂ⟦w⟧`. -/
def ιK : P₀ →+* K₀ d := (algebraMap T₀ (K₀ d)).comp (algebraMap P₀ T₀)

theorem algebraMap_mvPolynomial_injective :
    Function.Injective (algebraMap P₀ T₀) :=
  MvPolynomial.coe_injective (Fin d) ℂ

theorem ιK_injective : Function.Injective (ιK (d := d)) :=
  (IsFractionRing.injective T₀ (K₀ d)).comp algebraMap_mvPolynomial_injective

/-- `ℂ(w) → Frac ℂ⟦w⟧`. -/
def ιF : FractionRing P₀ →+* K₀ d := IsFractionRing.lift (ιK_injective (d := d))

theorem ιF_algebraMap (p : P₀) : ιF (algebraMap P₀ (FractionRing P₀) p) = ιK p :=
  IsFractionRing.lift_algebraMap _ _

attribute [local instance] FractionRing.liftAlgebra

section Model

variable (A : Type*) [CommRing A] [IsDomain A] [Algebra (MvPolynomial (Fin d) ℂ) A]
  [Module.Finite (MvPolynomial (Fin d) ℂ) A] [FaithfulSMul (MvPolynomial (Fin d) ℂ) A]

instance : FaithfulSMul P₀ (FractionRing A) :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr (by
    rw [IsScalarTower.algebraMap_eq P₀ A (FractionRing A)]
    exact (IsFractionRing.injective A _).comp (FaithfulSMul.algebraMap_injective P₀ A))

instance : IsScalarTower P₀ (FractionRing P₀) (FractionRing A) :=
  FractionRing.isScalarTower_liftAlgebra _ _

instance : IsLocalization (Algebra.algebraMapSubmonoid A (nonZeroDivisors P₀))
    (FractionRing A) := by
  have : Algebra.IsIntegral P₀ A := Algebra.IsIntegral.of_finite P₀ A
  infer_instance

instance : FiniteDimensional (FractionRing P₀) (FractionRing A) :=
  Module.Finite.of_isLocalization P₀ A (nonZeroDivisors P₀)

instance : CharZero (FractionRing P₀) :=
  charZero_of_injective_algebraMap (algebraMap ℂ (FractionRing P₀)).injective

instance : Algebra.IsSeparable (FractionRing P₀) (FractionRing A) := by
  have : Algebra.IsIntegral (FractionRing P₀) (FractionRing A) := Algebra.IsIntegral.of_finite _ _
  exact Algebra.IsSeparable.of_integral _ _

variable (d) in
/-- A primitive element of `Frac A` over `ℂ(w)`, taken in `A`. -/
structure PrimData where
  θ : A
  adjoin_eq_top :
    Algebra.adjoin (FractionRing P₀) {algebraMap A (FractionRing A) θ} = ⊤

theorem exists_primData : Nonempty (PrimData d A) := by
  set F := FractionRing (MvPolynomial (Fin d) ℂ)
  set L := FractionRing A
  set pb := Field.powerBasisOfFiniteOfSeparable F L
  obtain ⟨⟨a, t⟩, hα⟩ := IsLocalization.mk'_surjective
    (Algebra.algebraMapSubmonoid A (nonZeroDivisors (MvPolynomial (Fin d) ℂ))) pb.gen
  obtain ⟨s, hs, hst⟩ := t.2
  simp only at hα
  refine ⟨⟨a, ?_⟩⟩
  rw [eq_top_iff, ← pb.adjoin_gen_eq_top, Algebra.adjoin_le_iff, Set.singleton_subset_iff]
  have hs0 : algebraMap (MvPolynomial (Fin d) ℂ) F s ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ F)).mpr (nonZeroDivisors.ne_zero hs)
  have h1 : pb.gen * algebraMap F L (algebraMap (MvPolynomial (Fin d) ℂ) F s) =
      algebraMap A L a := by
    rw [← hα, ← IsScalarTower.algebraMap_apply (MvPolynomial (Fin d) ℂ) F L,
      IsScalarTower.algebraMap_apply (MvPolynomial (Fin d) ℂ) A L]
    have := IsLocalization.mk'_spec L a t
    rwa [← hst] at this
  have h2 : algebraMap F L (algebraMap (MvPolynomial (Fin d) ℂ) F s) ≠ 0 :=
    (_root_.map_ne_zero _).mpr hs0
  have : pb.gen = (algebraMap (MvPolynomial (Fin d) ℂ) F s)⁻¹ • algebraMap A L a := by
    rw [Algebra.smul_def, map_inv₀, ← h1, mul_comm, mul_assoc, mul_inv_cancel₀ h2, mul_one]
  rw [SetLike.mem_coe, this]
  exact Subalgebra.smul_mem _ (Algebra.self_mem_adjoin_singleton _ _) _

namespace PrimData

variable {A} (Θ : PrimData d A)

local notation "F" => FractionRing P₀
local notation "L" => FractionRing A

/-- The primitive element in `L`. -/
abbrev θL : L := algebraMap A L Θ.θ

theorem isIntegral_θ : IsIntegral P₀ Θ.θ := IsIntegral.of_finite P₀ Θ.θ

theorem isIntegral_θL : IsIntegral P₀ Θ.θL := Θ.isIntegral_θ.algebraMap

/-- The power basis of `L / F` generated by `θ`. -/
def pb : PowerBasis F L :=
  PowerBasis.ofAdjoinEqTop (Algebra.IsIntegral.isIntegral _) Θ.adjoin_eq_top

theorem pb_gen : Θ.pb.gen = Θ.θL := PowerBasis.ofAdjoinEqTop_gen _ _

/-- The minimal polynomial of `θ` over `P₀`. -/
def f : P₀[X] := minpoly P₀ Θ.θ

theorem f_monic : Θ.f.Monic := minpoly.monic Θ.isIntegral_θ

omit [Module.Finite P₀ A] in
theorem aeval_θL_f : aeval Θ.θL Θ.f = 0 := by
  rw [f, aeval_algebraMap_apply, minpoly.aeval, map_zero]

theorem minpoly_F : minpoly F Θ.θL = Θ.f.map (algebraMap P₀ F) := by
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' F Θ.isIntegral_θL, f,
    minpoly.algebraMap_eq (IsFractionRing.injective A L)]

/-- The image `f_K` of `f` in `K₀[X]`. -/
def fK : (K₀ d)[X] := Θ.f.map ιK

theorem fK_monic : Θ.fK.Monic := Θ.f_monic.map _

/-- `L ≅ F[X] / (minpoly)`. -/
def equivL : AdjoinRoot (minpoly F Θ.θL) ≃ₐ[F] L :=
  AdjoinRoot.equiv' (minpoly F Θ.θL) Θ.pb
    (by rw [Θ.pb_gen]; exact AdjoinRoot.eval₂_root _)
    (by rw [Θ.pb_gen]; exact minpoly.aeval _ _)

theorem hlift : eval₂ ((AdjoinRoot.of Θ.fK).comp (ιF (d := d))) (AdjoinRoot.root Θ.fK)
    (minpoly F Θ.θL) = 0 := by
  rw [Θ.minpoly_F, eval₂_map]
  have h : ((AdjoinRoot.of Θ.fK).comp (ιF (d := d))).comp (algebraMap P₀ F) =
      (AdjoinRoot.of Θ.fK).comp ιK := by
    ext p <;> simp [ιF_algebraMap]
  rw [h, ← eval₂_map]
  exact AdjoinRoot.eval₂_root _

/-- The ring map `L → K₀[X] / (f_K)`, `θ ↦ root`. -/
def Ψ : L →+* AdjoinRoot Θ.fK :=
  (AdjoinRoot.lift ((AdjoinRoot.of Θ.fK).comp (ιF (d := d))) (AdjoinRoot.root Θ.fK)
    Θ.hlift).comp Θ.equivL.symm.toRingEquiv.toRingHom

theorem Ψ_θL : Θ.Ψ Θ.θL = AdjoinRoot.root Θ.fK := by
  have h1 : Θ.equivL.symm Θ.θL = AdjoinRoot.root (minpoly F Θ.θL) := by
    have e : Θ.θL = Θ.pb.gen := Θ.pb_gen.symm
    calc Θ.equivL.symm Θ.θL = Θ.equivL.symm Θ.pb.gen := by rw [← e]
      _ = AdjoinRoot.root (minpoly F Θ.θL) := by
        rw [equivL, AdjoinRoot.equiv'_symm_apply]
        exact PowerBasis.lift_gen _ _ _
  simp only [Ψ, RingHom.comp_apply]
  erw [h1]
  exact AdjoinRoot.lift_root _

theorem Ψ_algebraMap (p : P₀) : Θ.Ψ (algebraMap P₀ L p) = AdjoinRoot.of Θ.fK (ιK p) := by
  rw [IsScalarTower.algebraMap_apply P₀ F L]
  simp only [Ψ, RingHom.comp_apply]
  erw [AlgEquiv.commutes]
  rw [AdjoinRoot.algebraMap_eq, AdjoinRoot.lift_of, RingHom.comp_apply, ιF_algebraMap]

theorem Ψ_aeval (q : P₀[X]) : Θ.Ψ (aeval Θ.θL q) = AdjoinRoot.mk Θ.fK (q.map ιK) := by
  rw [aeval_def, hom_eval₂, Ψ_θL, ← AdjoinRoot.aeval_eq, aeval_def, eval₂_map]
  congr 1
  ext p
  · simp [Ψ_algebraMap]
  · simp [Ψ_algebraMap]

/-- `A → K₀[X] / (f_K)`. -/
def ΦA : A →+* AdjoinRoot Θ.fK := Θ.Ψ.comp (algebraMap A L)

/-- `ℂ⟦w⟧ → K₀[X] / (f_K)`. -/
def ΦT : T₀ →+* AdjoinRoot Θ.fK := (AdjoinRoot.of Θ.fK).comp (algebraMap T₀ (K₀ d))

theorem compat (p : P₀) : Θ.ΦA (algebraMap P₀ A p) = Θ.ΦT (algebraMap P₀ T₀ p) := by
  rw [ΦA, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply P₀ A L, Ψ_algebraMap]
  rfl

omit [Module.Finite P₀ A] in
/-- **The model map** `Φ : ℂ⟦w⟧ ⊗_{P₀} A → K₀[X] / (f_K)`. -/
theorem ΦT_algebraMap (p : P₀) :
    Θ.ΦT (algebraMap P₀ T₀ p) = algebraMap P₀ (AdjoinRoot Θ.fK) p := by
  rw [ΦT, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply P₀ (K₀ d) (AdjoinRoot Θ.fK), AdjoinRoot.algebraMap_eq]

def Φ : T₀ ⊗[P₀] A →+* AdjoinRoot Θ.fK :=
  (Algebra.TensorProduct.lift
    ({ Θ.ΦT with commutes' := fun p => Θ.ΦT_algebraMap p } : T₀ →ₐ[P₀] AdjoinRoot Θ.fK)
    ({ Θ.ΦA with commutes' := fun p => (Θ.compat p).trans (Θ.ΦT_algebraMap p) } :
      A →ₐ[P₀] AdjoinRoot Θ.fK)
    (fun _ _ => Commute.all _ _)).toRingHom

theorem Φ_tmul (t : T₀) (a : A) : Θ.Φ (t ⊗ₜ a) = Θ.ΦT t * Θ.ΦA a := by
  simp [Φ, Algebra.TensorProduct.lift_tmul]

/-! ### The conductor and injectivity -/

theorem isIntegral_discr : IsIntegral P₀ (Algebra.discr F Θ.pb.basis) := by
  refine Algebra.discr_isIntegral F fun i => ?_
  rw [PowerBasis.coe_basis, Θ.pb_gen]
  exact Θ.isIntegral_θL.pow _

/-- The discriminant `δ ∈ P₀` of the power basis of `θ`. -/
def δc : P₀ := (IsIntegrallyClosed.isIntegral_iff.mp Θ.isIntegral_discr).choose

theorem algebraMap_δc : algebraMap P₀ F Θ.δc = Algebra.discr F Θ.pb.basis :=
  (IsIntegrallyClosed.isIntegral_iff.mp Θ.isIntegral_discr).choose_spec

theorem δc_ne_zero : Θ.δc ≠ 0 := by
  intro h
  have := Θ.algebraMap_δc
  rw [h, map_zero] at this
  exact Algebra.discr_not_zero_of_basis F Θ.pb.basis this.symm

/-- The degree `r` of `f`. -/
abbrev r : ℕ := Θ.f.natDegree

theorem f_ne_one : Θ.f ≠ 1 := by
  intro h
  have := minpoly.natDegree_pos Θ.isIntegral_θ
  rw [← f, h, natDegree_one] at this
  exact lt_irrefl 0 this

theorem exists_coeffPoly (a : A) : ∃ q : P₀[X], q.natDegree < Θ.r ∧
    aeval Θ.θL q = algebraMap P₀ L Θ.δc * algebraMap A L a := by
  have hmem := Algebra.discr_mul_isIntegral_mem_adjoin F (B := Θ.pb)
    (by rw [Θ.pb_gen]; exact Θ.isIntegral_θL) (z := algebraMap A L a)
    ((IsIntegral.of_finite P₀ a).algebraMap)
  rw [← Θ.algebraMap_δc, Algebra.smul_def, ← IsScalarTower.algebraMap_apply,
    Θ.pb_gen, Algebra.adjoin_singleton_eq_range_aeval] at hmem
  obtain ⟨q, hq⟩ := hmem
  refine ⟨q %ₘ Θ.f, natDegree_modByMonic_lt _ Θ.f_monic Θ.f_ne_one, ?_⟩
  rw [aeval_modByMonic_eq_self_of_root Θ.aeval_θL_f]
  exact hq

theorem eq_of_aeval_eq {q₁ q₂ : P₀[X]} (h₁ : q₁.natDegree < Θ.r) (h₂ : q₂.natDegree < Θ.r)
    (h : aeval Θ.θL q₁ = aeval Θ.θL q₂) : q₁ = q₂ := by
  rw [← sub_eq_zero]
  set p := q₁ - q₂
  have hp : aeval Θ.θL (p.map (algebraMap P₀ F)) = 0 := by
    rw [aeval_map_algebraMap, map_sub, h, sub_self]
  by_contra hne
  have hpF : p.map (algebraMap P₀ F) ≠ 0 :=
    fun h0 => hne (map_injective _ (IsFractionRing.injective P₀ F) (by rw [h0, Polynomial.map_zero]))
  have h1 := minpoly.degree_le_of_ne_zero F Θ.θL hpF hp
  rw [Θ.minpoly_F, degree_map_eq_of_injective (IsFractionRing.injective P₀ F),
    degree_map_eq_of_injective (IsFractionRing.injective P₀ F), degree_eq_natDegree Θ.f_monic.ne_zero]
    at h1
  have h2 : p.degree < Θ.r := by
    calc p.degree ≤ max q₁.degree q₂.degree := degree_sub_le _ _
      _ < Θ.r := max_lt (degree_lt_iff_coeff_zero _ _ |>.mpr fun m hm =>
          coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le h₁ (by exact_mod_cast hm)))
        (degree_lt_iff_coeff_zero _ _ |>.mpr fun m hm =>
          coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le h₂ (by exact_mod_cast hm)))
  exact absurd h1 (not_le.mpr h2)

/-- The coefficients of `δ a` in the basis `1, θ, …, θʳ⁻¹`. -/
def coeffPoly (a : A) : P₀[X] := (Θ.exists_coeffPoly a).choose

theorem coeffPoly_natDegree (a : A) : (Θ.coeffPoly a).natDegree < Θ.r :=
  (Θ.exists_coeffPoly a).choose_spec.1

theorem aeval_coeffPoly (a : A) :
    aeval Θ.θL (Θ.coeffPoly a) = algebraMap P₀ L Θ.δc * algebraMap A L a :=
  (Θ.exists_coeffPoly a).choose_spec.2

theorem coeffPoly_add (a b : A) : Θ.coeffPoly (a + b) = Θ.coeffPoly a + Θ.coeffPoly b :=
  Θ.eq_of_aeval_eq (Θ.coeffPoly_natDegree _)
    (lt_of_le_of_lt (natDegree_add_le _ _) (max_lt (Θ.coeffPoly_natDegree _)
      (Θ.coeffPoly_natDegree _)))
    (by rw [aeval_coeffPoly, map_add, map_add, aeval_coeffPoly, aeval_coeffPoly, mul_add])

theorem coeffPoly_smul (p : P₀) (a : A) : Θ.coeffPoly (p • a) = C p * Θ.coeffPoly a :=
  Θ.eq_of_aeval_eq (Θ.coeffPoly_natDegree _)
    (lt_of_le_of_lt (natDegree_C_mul_le _ _) (Θ.coeffPoly_natDegree _))
    (by
      rw [aeval_coeffPoly, map_mul, aeval_C, aeval_coeffPoly, Algebra.smul_def, map_mul,
        ← IsScalarTower.algebraMap_apply P₀ A L]
      ring)

/-- The coordinate map `κ : A → P₀ʳ`. -/
def κ : A →ₗ[P₀] (Fin Θ.r → P₀) where
  toFun a k := (Θ.coeffPoly a).coeff k
  map_add' a b := by funext k; simp [coeffPoly_add]
  map_smul' p a := by funext k; simp [coeffPoly_smul]

theorem κ_injective : Function.Injective Θ.κ := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro a ha
  rw [LinearMap.mem_ker] at ha
  have h0 : Θ.coeffPoly a = 0 := by
    refine Polynomial.ext fun k => ?_
    rw [coeff_zero]
    by_cases hk : k < Θ.r
    · exact congrFun ha ⟨k, hk⟩
    · exact coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (Θ.coeffPoly_natDegree a)
        (not_lt.mp hk))
  have := Θ.aeval_coeffPoly a
  rw [h0, map_zero, eq_comm, mul_eq_zero] at this
  rcases this with h | h
  · exfalso
    rw [map_eq_zero_iff _ (by
      rw [IsScalarTower.algebraMap_eq P₀ A L]
      exact (IsFractionRing.injective A L).comp (FaithfulSMul.algebraMap_injective P₀ A))] at h
    exact Θ.δc_ne_zero h
  · rw [Submodule.mem_bot]
    exact (map_eq_zero_iff _ (IsFractionRing.injective A L)).mp h

/-- `κ` after base change: `ℂ⟦w⟧ ⊗ A → ℂ⟦w⟧ʳ`. -/
def κT : T₀ ⊗[P₀] A →ₗ[P₀] (Fin Θ.r → T₀) :=
  ((TensorProduct.piScalarRight P₀ T₀ T₀ (Fin Θ.r)).toLinearMap.restrictScalars P₀).comp
    (Θ.κ.lTensor T₀)

theorem κT_injective : Function.Injective Θ.κT :=
  (TensorProduct.piScalarRight P₀ T₀ T₀ (Fin Θ.r)).injective.comp
    (Module.Flat.lTensor_preserves_injective_linearMap _ Θ.κ_injective)

theorem κT_tmul (t : T₀) (a : A) (k : Fin Θ.r) :
    Θ.κT (t ⊗ₜ a) k = algebraMap P₀ T₀ ((Θ.coeffPoly a).coeff k) * t := by
  simp [κT, κ, TensorProduct.piScalarRight_apply, Algebra.smul_def]

omit [Module.Finite P₀ A] in
theorem mk_eq_sum (q : P₀[X]) (hq : q.natDegree < Θ.r) :
    AdjoinRoot.mk Θ.fK (q.map ιK) =
      ∑ k : Fin Θ.r, AdjoinRoot.of Θ.fK (ιK (q.coeff k)) * AdjoinRoot.root Θ.fK ^ (k : ℕ) := by
  rw [← AdjoinRoot.aeval_eq, aeval_def, eval₂_map, eval₂_eq_sum_range' _ hq, Finset.sum_range]
  rfl

theorem ΦA_mul_δc (a : A) : Θ.ΦA a * AdjoinRoot.of Θ.fK (ιK Θ.δc) =
    ∑ k : Fin Θ.r, AdjoinRoot.of Θ.fK (ιK ((Θ.coeffPoly a).coeff k)) *
      AdjoinRoot.root Θ.fK ^ (k : ℕ) := by
  rw [← Θ.mk_eq_sum _ (Θ.coeffPoly_natDegree a), ← Ψ_aeval, aeval_coeffPoly, map_mul,
    Ψ_algebraMap, ΦA, RingHom.comp_apply, mul_comm]

theorem Φ_mul_δc (x : T₀ ⊗[P₀] A) : Θ.Φ x * AdjoinRoot.of Θ.fK (ιK Θ.δc) =
    ∑ k : Fin Θ.r, AdjoinRoot.of Θ.fK (algebraMap T₀ (K₀ d) (Θ.κT x k)) *
      AdjoinRoot.root Θ.fK ^ (k : ℕ) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul t a =>
    rw [Φ_tmul, mul_assoc, ΦA_mul_δc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [κT_tmul, map_mul, map_mul, ΦT, RingHom.comp_apply]
    change _ = AdjoinRoot.of Θ.fK (ιK _) * _ * _
    ring
  | add x y hx hy =>
    rw [map_add, add_mul, hx, hy, map_add, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.add_apply, map_add, map_add, add_mul]

theorem natDegree_fK : Θ.fK.natDegree = Θ.r :=
  Θ.f_monic.natDegree_map _

/-- **The model map is injective.** -/
theorem Φ_injective : Function.Injective Θ.Φ := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h := Θ.Φ_mul_δc x
  rw [hx, zero_mul] at h
  set c : Fin Θ.r → K₀ d := fun k => algebraMap T₀ (K₀ d) (Θ.κT x k)
  set Pc : (K₀ d)[X] := ∑ k : Fin Θ.r, C (c k) * X ^ (k : ℕ)
  have hmk : AdjoinRoot.mk Θ.fK Pc = 0 := by
    rw [h]
    simp only [Pc, map_sum, map_mul, AdjoinRoot.mk_C, map_pow, AdjoinRoot.mk_X, c]
  rw [AdjoinRoot.mk_eq_zero] at hmk
  have hPc : Pc = 0 := by
    refine eq_zero_of_dvd_of_degree_lt hmk ?_
    rw [degree_eq_natDegree Θ.fK_monic.ne_zero, natDegree_fK]
    exact degree_sum_fin_lt _
  have hc : ∀ k, c k = 0 := by
    intro k
    have := congrArg (fun P : (K₀ d)[X] => P.coeff k) hPc
    simp only [Pc, finsetSum_coeff, coeff_C_mul_X_pow, coeff_zero] at this
    rw [Finset.sum_eq_single k (fun j _ hj => if_neg (fun h => hj (Fin.ext h.symm)))
      (by simp)] at this
    simpa using this
  apply Θ.κT_injective
  rw [map_zero]
  funext k
  exact (map_eq_zero_iff _ (IsFractionRing.injective T₀ (K₀ d))).mp (hc k)

/-! ### Separability -/

theorem separable_minpoly_F : (Θ.f.map (algebraMap P₀ F)).Separable := by
  rw [← Θ.minpoly_F]
  exact Algebra.IsSeparable.isSeparable F Θ.θL

theorem exists_bezout : ∃ (Az Bz : P₀[X]) (δ : P₀), δ ≠ 0 ∧
    Az * Θ.f + Bz * derivative Θ.f = C δ := by
  obtain ⟨a, b, hab⟩ := Θ.separable_minpoly_F
  obtain ⟨s₁, hs₁, ha⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors P₀) a
  obtain ⟨s₂, hs₂, hb⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors P₀) b
  refine ⟨C s₂ * IsLocalization.integerNormalization (nonZeroDivisors P₀) a,
    C s₁ * IsLocalization.integerNormalization (nonZeroDivisors P₀) b, s₁ * s₂,
    mul_ne_zero (nonZeroDivisors.ne_zero hs₁) (nonZeroDivisors.ne_zero hs₂), ?_⟩
  apply map_injective _ (IsFractionRing.injective P₀ F)
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, ← derivative_map, ha, hb,
    map_mul, Algebra.smul_def, Polynomial.algebraMap_apply]
  linear_combination (C (algebraMap P₀ F s₁) * C (algebraMap P₀ F s₂)) * hab

/-- The Bezout data `A f + B f' = δ'`. -/
def bezA : P₀[X] := Θ.exists_bezout.choose
def bezB : P₀[X] := Θ.exists_bezout.choose_spec.choose
def δ' : P₀ := Θ.exists_bezout.choose_spec.choose_spec.choose

theorem δ'_ne_zero : Θ.δ' ≠ 0 := Θ.exists_bezout.choose_spec.choose_spec.choose_spec.1

theorem bezout : Θ.bezA * Θ.f + Θ.bezB * derivative Θ.f = C Θ.δ' :=
  Θ.exists_bezout.choose_spec.choose_spec.choose_spec.2

theorem bezout_K : Θ.bezA.map ιK * Θ.fK + Θ.bezB.map ιK * derivative Θ.fK = C (ιK Θ.δ') := by
  have := congrArg (Polynomial.map ιK) Θ.bezout
  simpa [fK, derivative_map] using this

theorem ιK_δ'_ne_zero : ιK Θ.δ' ≠ 0 :=
  (map_ne_zero_iff _ ιK_injective).mpr Θ.δ'_ne_zero

theorem separable_fK : Θ.fK.Separable := by
  rw [separable_def]
  refine ⟨C (ιK Θ.δ')⁻¹ * Θ.bezA.map ιK, C (ιK Θ.δ')⁻¹ * Θ.bezB.map ιK, ?_⟩
  rw [mul_assoc, mul_assoc, ← mul_add, Θ.bezout_K, ← C_mul, inv_mul_cancel₀ Θ.ιK_δ'_ne_zero, C_1]

theorem squarefree_fK : Squarefree Θ.fK := Θ.separable_fK.squarefree

instance isReduced_Q : IsReduced (AdjoinRoot Θ.fK) := by
  refine ⟨fun x ⟨m, hm⟩ => ?_⟩
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · subst h0
    rw [pow_zero] at hm
    have : Subsingleton (AdjoinRoot Θ.fK) := subsingleton_of_zero_eq_one hm.symm
    exact Subsingleton.elim _ _
  · rw [← map_pow, AdjoinRoot.mk_eq_zero] at hm
    exact AdjoinRoot.mk_eq_zero.mpr ((Θ.squarefree_fK.dvd_pow_iff_dvd hpos.ne').mp hm)

/-! ### Splitting idempotents (uses that `ℂ⟦w⟧` is integrally closed) -/

theorem Φ_algebraMap (t : T₀) :
    Θ.Φ (algebraMap T₀ (T₀ ⊗[P₀] A) t) = AdjoinRoot.of Θ.fK (algebraMap T₀ (K₀ d) t) := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, Φ_tmul,
    map_one, mul_one]
  rfl

theorem Φ_θ : Θ.Φ (1 ⊗ₜ Θ.θ) = AdjoinRoot.root Θ.fK := by
  rw [Φ_tmul, map_one, one_mul, ΦA, RingHom.comp_apply, Ψ_θL]

theorem Φ_aeval (P : T₀[X]) :
    Θ.Φ (aeval ((1 : T₀) ⊗ₜ[P₀] Θ.θ) P) = AdjoinRoot.mk Θ.fK (P.map (algebraMap T₀ (K₀ d))) := by
  rw [aeval_def, hom_eval₂, Φ_θ, ← AdjoinRoot.aeval_eq, aeval_def, eval₂_map]
  congr 1
  ext t
  rw [RingHom.comp_apply, Φ_algebraMap]
  rfl

omit [Module.Finite P₀ A] in
theorem fK_eq_map : Θ.fK = (Θ.f.map (algebraMap P₀ T₀)).map (algebraMap T₀ (K₀ d)) := by
  rw [fK, Polynomial.map_map]
  rfl

theorem isCoprime_of_isRelPrime_poly {K : Type*} [Field K] {a b : K[X]} (h : IsRelPrime a b) :
    IsCoprime a b :=
  h.isCoprime

/-- A monic factor of `f_K` comes from `ℂ⟦w⟧[X]`. -/
theorem exists_lift_of_dvd [IsIntegrallyClosed T₀] {g : (K₀ d)[X]} (hg : g.Monic)
    (hdvd : g ∣ Θ.fK) : ∃ gT : T₀[X], gT.map (algebraMap T₀ (K₀ d)) = g := by
  rw [fK_eq_map] at hdvd
  obtain ⟨gT, hgT⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd (K₀ d) (Θ.f_monic.map _) hdvd
  refine ⟨gT, ?_⟩
  rw [hg.leadingCoeff, C_1, mul_one] at hgT
  exact hgT

/-- The polynomial identities behind , over an arbitrary commutative ring. -/
theorem split_dvd {K : Type*} [CommRing K] {fK g h AK BK p : K[X]} {δ : K}
    (hg : fK = h * g) (hb : AK * fK + BK * derivative fK = C δ) :
    fK ∣ BK * derivative g * h * (BK * derivative g * h) - C δ * (BK * derivative g * h) ∧
    (h ∣ p → fK ∣ p * (C δ - BK * derivative g * h)) ∧
    (IsCoprime g p → ∀ q, fK ∣ p * q → fK ∣ q * (BK * derivative g * h)) := by
  have hgE : g ∣ BK * derivative g * h - C δ := by
    refine ⟨-(AK * h) - BK * derivative h, ?_⟩
    rw [← hb, hg, derivative_mul]
    ring
  have hhE : h ∣ BK * derivative g * h := ⟨BK * derivative g, by ring⟩
  refine ⟨?_, fun hp => ?_, fun hgp q hpq => ?_⟩
  · rw [hg, show BK * derivative g * h * (BK * derivative g * h) - C δ * (BK * derivative g * h) =
      (BK * derivative g * h) * (BK * derivative g * h - C δ) by ring]
    exact mul_dvd_mul hhE hgE
  · rw [hg, show p * (C δ - BK * derivative g * h) = -(p * (BK * derivative g * h - C δ)) by ring,
      dvd_neg]
    exact mul_dvd_mul hp hgE
  · have hgq : g ∣ q := hgp.dvd_of_dvd_mul_left (dvd_trans ⟨h, by rw [hg, mul_comm]⟩ hpq)
    rw [hg, mul_comm h g]
    exact mul_dvd_mul hgq hhE

/-- **Splitting.** Every element `x` of `K₀[X] / (f_K)` admits `e ∈ ℂ⟦w⟧ ⊗ A` such that
`Φ e / δ'` is an idempotent with `x (1 - Φ e / δ') = 0` and `y Φ e = 0` whenever `x y = 0`. -/
theorem exists_split [IsIntegrallyClosed T₀] (x : AdjoinRoot Θ.fK) :
    ∃ e : T₀ ⊗[P₀] A,
      Θ.Φ e * Θ.Φ e = AdjoinRoot.of Θ.fK (ιK Θ.δ') * Θ.Φ e ∧
      x * (AdjoinRoot.of Θ.fK (ιK Θ.δ') - Θ.Φ e) = 0 ∧
      ∀ y, x * y = 0 → y * Θ.Φ e = 0 := by
  classical
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
  have hfK0 : Θ.fK ≠ 0 := Θ.fK_monic.ne_zero
  have hh0 : gcd Θ.fK p ≠ 0 := fun h0 => hfK0 ((gcd_eq_zero_iff Θ.fK p).mp h0).1
  have hhm : (gcd Θ.fK p).Monic := by
    rw [← normalize_gcd Θ.fK p]
    exact monic_normalize hh0
  have hdvdl := gcd_dvd_left Θ.fK p
  have hdvdr := gcd_dvd_right Θ.fK p
  have hgcd : ∀ c, c ∣ Θ.fK → c ∣ p → c ∣ gcd Θ.fK p := fun c h1 h2 => dvd_gcd h1 h2
  generalize gcd Θ.fK p = h at hh0 hhm hdvdl hdvdr hgcd
  obtain ⟨g, hg⟩ := hdvdl
  have hgm : g.Monic := Polynomial.Monic.of_mul_monic_left hhm (hg ▸ Θ.fK_monic)
  have hrel : IsRelPrime h g := (squarefree_mul_iff.mp (hg ▸ Θ.squarefree_fK)).1
  have hgp : IsCoprime g p := by
    refine isCoprime_of_isRelPrime_poly fun c hcg hcp => ?_
    have hch : c ∣ h := hgcd c (hcg.trans ⟨h, by rw [hg, mul_comm]⟩) hcp
    exact hrel hch hcg
  obtain ⟨gT, hgT⟩ := Θ.exists_lift_of_dvd hgm ⟨h, by rw [hg, mul_comm]⟩
  obtain ⟨hT, hhT⟩ := Θ.exists_lift_of_dvd hhm ⟨g, hg⟩
  set BK := Θ.bezB.map ιK
  set AK := Θ.bezA.map ιK
  set δK := ιK Θ.δ'
  set E : (K₀ d)[X] := BK * derivative g * h
  refine ⟨aeval ((1 : T₀) ⊗ₜ[P₀] Θ.θ) (Θ.bezB.map (algebraMap P₀ T₀) * derivative gT * hT), ?_⟩
  have hΦe : Θ.Φ (aeval ((1 : T₀) ⊗ₜ[P₀] Θ.θ)
      (Θ.bezB.map (algebraMap P₀ T₀) * derivative gT * hT)) = AdjoinRoot.mk Θ.fK E := by
    rw [Φ_aeval]
    congr 1
    simp only [Polynomial.map_mul, Polynomial.map_map, ← derivative_map, hgT, hhT, E, BK]
    rfl
  rw [hΦe]
  obtain ⟨h1, h2, h3⟩ := split_dvd (p := p) (hg.trans (mul_comm _ _) |>.trans (mul_comm _ _))
    Θ.bezout_K
  refine ⟨?_, ?_, ?_⟩
  · rw [← AdjoinRoot.mk_C, ← map_mul, ← map_mul, ← sub_eq_zero, ← map_sub, AdjoinRoot.mk_eq_zero]
    exact h1
  · rw [← AdjoinRoot.mk_C, ← map_sub, ← map_mul, AdjoinRoot.mk_eq_zero]
    exact h2 hdvdr
  · intro y hy
    obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective y
    rw [← map_mul, AdjoinRoot.mk_eq_zero] at hy
    rw [← map_mul, AdjoinRoot.mk_eq_zero]
    exact h3 hgp q hy

end PrimData

/-- **Analytic unramifiedness.** If `A` is a domain, finite and torsion-free over
`ℂ[w₁, …, w_d]`, then `ℂ⟦w⟧ ⊗_{ℂ[w]} A` is reduced. -/
theorem isReduced_tensor : IsReduced (T₀ ⊗[P₀] A) := by
  obtain ⟨Θ⟩ := exists_primData (d := d) A
  exact isReduced_of_injective Θ.Φ Θ.Φ_injective

end Model

end

end SGPT.Unibranch.UnibAlg
