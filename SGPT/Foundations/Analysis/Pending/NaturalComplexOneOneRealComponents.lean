import SGPT.Foundations.Analysis.Pending.NaturalComplexPureExteriorExpansion
import SGPT.Foundations.Analysis.Pending.NaturalRealPPSubmodule

/-!
# Genuine continuous real components of mixed complex two-form generators

The actual continuous coordinate product is alternatized and then composed
with real and imaginary parts. Its two real forms are genuinely of type
`(1,1)`, and their unique actual complexifications exactly reconstruct the
original mixed generator. No general-degree span or usual-class theorem is
asserted.
-/

noncomputable section

namespace SGPT.Foundations.Analysis.Pending.NaturalComplexOneOneRealComponents

open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open NaturalComplexBidegreeTransport NaturalComplexCoordinateEigenbasis
open NaturalComplexCovectors NaturalComplexPureExteriorExpansion
open NaturalRealAlternatingComplexification

def mixedGenerator {n : ℕ} (j k : Fin n) :
    complexification n [⋀^Fin 2]→ₗ[ℂ] ℂ :=
  exteriorMonomial ![(0, j), (1, k)]

private def coordinateProduct {n : ℕ} (j k : Fin n) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 2 => ComplexModel n) ℂ :=
  (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2) ℂ).compContinuousLinearMap
    ![(EuclideanSpace.proj j).restrictScalars ℝ,
      Complex.conjCLE.toContinuousLinearMap.comp ((EuclideanSpace.proj k).restrictScalars ℝ)]

def restrictedGenerator {n : ℕ} (j k : Fin n) :
    ComplexModel n [⋀^Fin 2]→L[ℝ] ℂ :=
  ContinuousMultilinearMap.alternatization (coordinateProduct j k)

def realComponent {n : ℕ} (j k : Fin n) :
    ComplexModel n [⋀^Fin 2]→L[ℝ] ℝ :=
  Complex.reCLM.compContinuousAlternatingMap (restrictedGenerator j k)

def imagComponent {n : ℕ} (j k : Fin n) :
    ComplexModel n [⋀^Fin 2]→L[ℝ] ℝ :=
  Complex.imCLM.compContinuousAlternatingMap (restrictedGenerator j k)

private theorem coordinateProduct_eq {n : ℕ} (j k : Fin n)
    (v : Fin 2 → ComplexModel n) :
    coordinateProduct j k v =
      coordinateMonomial ![(0, j), (1, k)] (fun i => realEmbedding n (v i)) := by
  simp [coordinateProduct, coordinateMonomial, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebra_apply, MultilinearMap.mkPiRing_apply,
    Fin.prod_univ_two, eigenCovector, holomorphicCovector, antiholomorphicCovector,
    extendRealCovector_realEmbedding, EuclideanSpace.proj, EuclideanSpace.projₗ,
    PiLp.proj, PiLp.projₗ]

theorem restrictedGenerator_eq {n : ℕ} (j k : Fin n)
    (v : Fin 2 → ComplexModel n) :
    restrictedGenerator j k v = mixedGenerator j k (fun i => realEmbedding n (v i)) := by
  classical
  simp only [restrictedGenerator, mixedGenerator, exteriorMonomial,
    ContinuousMultilinearMap.alternatization_apply_apply, MultilinearMap.alternatization_apply,
    MultilinearMap.domDomCongr_apply]
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  exact coordinateProduct_eq j k (v ∘ σ)

private theorem coordinateMonomial_extendedJ {n : ℕ} (j k : Fin n)
    (v : Fin 2 → complexification n) :
    coordinateMonomial ![(0, j), (1, k)] (fun i => extendedJ n (v i)) =
      coordinateMonomial ![(0, j), (1, k)] v := by
  simp only [coordinateMonomial, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiRing_apply, Fin.prod_univ_two, eigenCovector,
    Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue,
    if_pos, if_false, one_ne_zero,
    holomorphicCovector_extendedJ, antiholomorphicCovector_extendedJ,
    smul_eq_mul, mul_one]
  ring_nf
  simp [Complex.I_sq]

private theorem mixedGenerator_extendedJ {n : ℕ} (j k : Fin n)
    (v : Fin 2 → complexification n) :
    mixedGenerator j k (fun i => extendedJ n (v i)) = mixedGenerator j k v := by
  classical
  simp only [mixedGenerator, exteriorMonomial, MultilinearMap.alternatization_apply,
    MultilinearMap.domDomCongr_apply]
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  exact coordinateMonomial_extendedJ j k (v ∘ σ)

private theorem extendedJ_realEmbedding {n : ℕ} (v : ComplexModel n) :
    extendedJ n (realEmbedding n v) = realEmbedding n (Complex.I • v) := by
  change ((Complex.I • (LinearMap.id : ComplexModel n →ₗ[ℝ] ComplexModel n)).baseChange ℂ)
    (realEmbedding n v) = _
  simp [realEmbedding]

private theorem restrictedGenerator_J {n : ℕ} (j k : Fin n)
    (v : Fin 2 → ComplexModel n) :
    restrictedGenerator j k (fun i => Complex.I • v i) = restrictedGenerator j k v := by
  rw [restrictedGenerator_eq, restrictedGenerator_eq]
  simp only [← extendedJ_realEmbedding]
  exact mixedGenerator_extendedJ j k _

theorem realComponent_isOneOne {n : ℕ} (j k : Fin n) :
    IsOneOne (realComponent j k) := by
  intro u v
  change (restrictedGenerator j k ![Complex.I • u, Complex.I • v]).re =
    (restrictedGenerator j k ![u, v]).re
  have h : (fun i : Fin 2 => Complex.I • (![u, v] i)) = ![Complex.I • u, Complex.I • v] := by
    ext i
    fin_cases i <;> rfl
  rw [← h, restrictedGenerator_J]

theorem imagComponent_isOneOne {n : ℕ} (j k : Fin n) :
    IsOneOne (imagComponent j k) := by
  intro u v
  change (restrictedGenerator j k ![Complex.I • u, Complex.I • v]).im =
    (restrictedGenerator j k ![u, v]).im
  have h : (fun i : Fin 2 => Complex.I • (![u, v] i)) = ![Complex.I • u, Complex.I • v] := by
    ext i
    fin_cases i <;> rfl
  rw [← h, restrictedGenerator_J]

theorem realComponent_mem_formSpan {n : ℕ} (j k : Fin n) :
    realComponent j k ∈ LocalProductCurrents.formSpan n 1 :=
  LocalProductCurrents.oneOne_mem_formSpan (realComponent_isOneOne j k)

theorem imagComponent_mem_formSpan {n : ℕ} (j k : Fin n) :
    imagComponent j k ∈ LocalProductCurrents.formSpan n 1 :=
  LocalProductCurrents.oneOne_mem_formSpan (imagComponent_isOneOne j k)

theorem mixedGenerator_eq_complexify_components {n : ℕ} (j k : Fin n) :
    mixedGenerator j k = complexify (realComponent j k).toAlternatingMap +
      Complex.I • complexify (imagComponent j k).toAlternatingMap := by
  apply AlternatingMap.coe_multilinearMap_injective
  apply Module.Basis.ext_multilinear (fun _ => (coordinateRealBasis n).baseChange ℂ)
  intro w
  simp only [Module.Basis.baseChange_apply]
  change mixedGenerator j k (fun i => realEmbedding n (coordinateRealBasis n (w i))) =
    (complexify (realComponent j k).toAlternatingMap +
      Complex.I • complexify (imagComponent j k).toAlternatingMap)
        (fun i => realEmbedding n (coordinateRealBasis n (w i)))
  simp only [AlternatingMap.add_apply, AlternatingMap.smul_apply, complexify_realEmbedding,
    smul_eq_mul]
  rw [← restrictedGenerator_eq]
  change restrictedGenerator j k (fun i => coordinateRealBasis n (w i)) =
    ((restrictedGenerator j k (fun i => coordinateRealBasis n (w i))).re : ℂ) +
      Complex.I * ((restrictedGenerator j k (fun i => coordinateRealBasis n (w i))).im : ℂ)
  simpa [mul_comm] using
    (Complex.re_add_im (restrictedGenerator j k (fun i => coordinateRealBasis n (w i)))).symm

end SGPT.Foundations.Analysis.Pending.NaturalComplexOneOneRealComponents
