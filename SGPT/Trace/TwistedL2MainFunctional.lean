import SGPT.Trace.TwistedL2MainFamily
import SGPT.Foundations.Analysis.Pending.HormanderL2Translate

/-!
# The finite-family functional bound in the actual weighted Hilbert space

The first step is to identify the `L²` representative of a finite sum of
local adjoint pieces with the unit-frame coordinate of the corresponding
pointwise sum of scaled sections. This is only support for the functional
estimate: no Bochner--Kodaira inequality or main correction theorem is assumed
or proved here.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter MeasureTheory Bundle
open scoped Topology ENNReal ContDiff Manifold ComplexConjugate InnerProductSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

namespace TwistedDatum

variable (T : TwistedDatum n X)

/-- The pointwise finite sum of the original actual local adjoint sections. -/
def familyAdjointSection (α : T.TestFamilies) (x : X) : T.L.Fiber x :=
  ∑ p ∈ α.support, T.localTStar p.chart p.frame p.density (α p • p.field) x

/-- The `L²` adjoint image and the unit-frame reading of the actual finite
section sum agree almost everywhere on the original open set. -/
theorem familyAdjoint_ae_eq_coord (α : T.TestFamilies) :
    ∀ᵐ x ∂(T.μ.restrict T.U), (T.familyAdjoint α : X → ℂ) x =
      T.H1coord (T.familyAdjointSection α) x := by
  classical
  have heach : ∀ p ∈ α.support, ∀ᵐ x ∂(T.μ.restrict T.U),
      ((α p • p.adjoint : Lp ℂ 2 (T.μ.restrict T.U)) : X → ℂ) x =
        T.H1coord (T.localTStar p.chart p.frame p.density (α p • p.field)) x := by
    intro p _
    rw [← LocalTestPiece.adjoint_scale T p (α p)]
    exact (T.memLp_H1coord_localTStar p.density_spec
      (LocalTestPiece.scale T p (α p)).field_spec).coeFn_toLp
  have heach' := (eventually_all_finset α.support).2 heach
  have hsum := Lp.coeFn_fun_finsetSum α.support (fun p => α p • p.adjoint)
  filter_upwards [hsum, heach'] with x hsumx heachx
  have hfam : T.familyAdjoint α = ∑ p ∈ α.support, α p • p.adjoint := by
    simp [familyAdjoint, Finsupp.linearCombination_apply, Finsupp.sum]
  rw [hfam] at ⊢
  rw [hsumx]
  change (∑ p ∈ α.support, (α p • p.adjoint : Lp ℂ 2 (T.μ.restrict T.U)) x) =
    T.H1coord (fun y => ∑ p ∈ α.support,
      T.localTStar p.chart p.frame p.density (α p • p.field) y) x
  rw [T.H1coord_sum]
  exact Finset.sum_congr rfl fun p hp => heachx p hp

/-- The literal weighted lintegral of the finite section sum is the squared
norm of its actual `L²` class. -/
theorem lintegral_familyAdjointSection_eq_norm_sq (α : T.TestFamilies) :
    (∫⁻ x in T.U, ENNReal.ofReal
      (‖T.familyAdjointSection α x‖ ^ 2 * T.H1weight x) ∂T.μ) =
      ENNReal.ofReal (‖T.familyAdjoint α‖ ^ 2) := by
  let A : Lp ℂ 2 (T.μ.restrict T.U) := T.familyAdjoint α
  have hint : Integrable (fun x => ‖(A : X → ℂ) x‖ ^ 2) (T.μ.restrict T.U) :=
    (memLp_two_iff_integrable_sq_norm (Lp.memLp A).1).mp (Lp.memLp A)
  have hnorm : ‖A‖ ^ 2 = ∫ x, ‖(A : X → ℂ) x‖ ^ 2 ∂(T.μ.restrict T.U) := by
    have h : ⟪A, A⟫_ℂ =
        ∫ x, ⟪(A : X → ℂ) x, (A : X → ℂ) x⟫_ℂ ∂(T.μ.restrict T.U) :=
      MeasureTheory.L2.inner_def A A
    rw [inner_self_eq_norm_sq_to_K] at h
    have h2 : (∫ x, ⟪(A : X → ℂ) x, (A : X → ℂ) x⟫_ℂ ∂(T.μ.restrict T.U)) =
        ∫ x, ((‖(A : X → ℂ) x‖ ^ 2 : ℝ) : ℂ) ∂(T.μ.restrict T.U) := by
      simp only [inner_self_eq_norm_sq_to_K]
      push_cast
      rfl
    rw [h2, integral_complex_ofReal] at h
    exact Complex.ofReal_injective (by rw [Complex.ofReal_pow]; exact h)
  calc
    (∫⁻ x in T.U, ENNReal.ofReal
        (‖T.familyAdjointSection α x‖ ^ 2 * T.H1weight x) ∂T.μ)
        = ∫⁻ x, ENNReal.ofReal (‖(A : X → ℂ) x‖ ^ 2) ∂(T.μ.restrict T.U) := by
          apply lintegral_congr_ae
          filter_upwards [T.familyAdjoint_ae_eq_coord α,
            ae_restrict_mem T.isOpen_U.measurableSet] with x hcoord hx
          change ENNReal.ofReal _ = ENNReal.ofReal (‖(T.familyAdjoint α : X → ℂ) x‖ ^ 2)
          rw [hcoord, T.norm_H1coord_sq _ hx]
    _ = ENNReal.ofReal (∫ x, ‖(A : X → ℂ) x‖ ^ 2 ∂(T.μ.restrict T.U)) :=
      (ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun x => sq_nonneg _)).symm
    _ = ENNReal.ofReal (‖T.familyAdjoint α‖ ^ 2) := by rw [← hnorm]

/-- The finite-family functional estimate, when proved, yields its quantitative
real Hilbert-space bound. This theorem is conditional on that analytic
estimate; it does not assert the Bochner--Kodaira or density producers. -/
theorem family_norm_bound_of_functional
    (hfunctional : TwistedFunctionalBoundStatement n X)
    (hfinite : ∫⁻ x in T.U, ENNReal.ofReal (T.D x * Real.exp (-T.φ x)) ∂T.μ < ⊤)
    (α : T.TestFamilies) :
    ‖∑ p ∈ α.support, conj (α p) * p.pairing‖ ≤
      Real.sqrt (∫⁻ x in T.U, ENNReal.ofReal (T.D x * Real.exp (-T.φ x)) ∂T.μ).toReal *
        ‖T.familyAdjoint α‖ := by
  classical
  let m : ℝ≥0∞ := ∫⁻ x in T.U, ENNReal.ofReal (T.D x * Real.exp (-T.φ x)) ∂T.μ
  have hmain := hfunctional T hfinite T.LocalTestPiece α.support
    (fun p => p.chart) (fun p => p.frame) (fun p => p.density)
    (fun p => α p • p.field)
    (fun p _ => p.density_spec)
    (fun p _ => T.isLocalTestField_smul p.field_spec (α p))
  have hmain' : ENNReal.ofReal (‖∑ p ∈ α.support, conj (α p) * p.pairing‖ ^ 2) ≤
      m * ENNReal.ofReal (‖T.familyAdjoint α‖ ^ 2) := by
    simp_rw [T.localDataPairing_smul] at hmain
    change ENNReal.ofReal (‖∑ p ∈ α.support, conj (α p) * p.pairing‖ ^ 2) ≤
      m * (∫⁻ x in T.U, ENNReal.ofReal
        (‖T.familyAdjointSection α x‖ ^ 2 * T.H1weight x) ∂T.μ) at hmain
    rw [T.lintegral_familyAdjointSection_eq_norm_sq] at hmain
    exact hmain
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top hfinite.ne ENNReal.ofReal_ne_top) hmain'
  have hreal' : ‖∑ p ∈ α.support, conj (α p) * p.pairing‖ ^ 2 ≤
      m.toReal * ‖T.familyAdjoint α‖ ^ 2 := by
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _)] using hreal
  calc
    ‖∑ p ∈ α.support, conj (α p) * p.pairing‖ =
        Real.sqrt (‖∑ p ∈ α.support, conj (α p) * p.pairing‖ ^ 2) :=
      (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (m.toReal * ‖T.familyAdjoint α‖ ^ 2) := Real.sqrt_le_sqrt hreal'
    _ = Real.sqrt m.toReal * ‖T.familyAdjoint α‖ := by
      rw [Real.sqrt_mul ENNReal.toReal_nonneg, Real.sqrt_sq (norm_nonneg _)]

/-- Conditional Hilbert-space solution on all actual local adjoint pieces.
The quoted functional estimate is an explicit outstanding input. -/
theorem exists_local_test_solution_of_functional
    (hfunctional : TwistedFunctionalBoundStatement n X)
    (hfinite : ∫⁻ x in T.U, ENNReal.ofReal (T.D x * Real.exp (-T.φ x)) ∂T.μ < ⊤) :
    ∃ u : Lp ℂ 2 (T.μ.restrict T.U),
      ‖u‖ ≤ Real.sqrt (∫⁻ x in T.U, ENNReal.ofReal (T.D x * Real.exp (-T.φ x)) ∂T.μ).toReal ∧
      ∀ p : T.LocalTestPiece, ⟪p.adjoint, u⟫_ℂ = p.pairing := by
  obtain ⟨u, _, hnorm, htest⟩ := exists_riesz_of_finite_test_bound
    (fun p : T.LocalTestPiece => p.adjoint) (fun p : T.LocalTestPiece => p.pairing)
    (Real.sqrt_nonneg _) (fun α => by
      simpa [familyAdjoint, Finsupp.linearCombination_apply, Finsupp.sum] using
        T.family_norm_bound_of_functional hfunctional hfinite α)
  exact ⟨u, hnorm, htest⟩

end TwistedDatum
end SGPT.Trace.TwistedL2
