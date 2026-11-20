import SGPT.Foundations.Schemes.ValuationFiltration
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic

/-! # Homogeneity from the actual scalar degree action

An invariant valuation threshold subspace contains every homogeneous
component of a finite graded sum. The extraction argument is proved here:
apply a separating linear functional to the quotient by the subspace, and
use vanishing of a literal polynomial at every nonzero base-field scalar.
No homogeneous-subspace or minimum formula is assumed.
-/

open scoped BigOperators Polynomial Classical

namespace SGPT.Foundations.Schemes

section CoefficientExtraction

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The actual polynomial obtained by testing a scalar degree orbit with a
linear functional. Distinct degrees are its distinct monomials. -/
noncomputable def scalarOrbitPolynomial (φ : V →ₗ[K] K) (s : Finset ℕ)
    (u : ℕ → V) : K[X] :=
  ∑ k ∈ s, Polynomial.monomial k (φ (u k))

theorem scalarOrbitPolynomial_eval (φ : V →ₗ[K] K) (s : Finset ℕ)
    (u : ℕ → V) (c : K) :
    (scalarOrbitPolynomial φ s u).eval c = φ (∑ k ∈ s, c ^ k • u k) := by
  change (Polynomial.evalRingHom c) (∑ k ∈ s, Polynomial.monomial k (φ (u k))) = _
  rw [map_sum]
  simp [Polynomial.eval_monomial, mul_comm]

theorem scalarOrbitPolynomial_coeff (φ : V →ₗ[K] K) (s : Finset ℕ)
    (u : ℕ → V) {d : ℕ} (hd : d ∈ s) :
    (scalarOrbitPolynomial φ s u).coeff d = φ (u d) := by
  simp [scalarOrbitPolynomial, Polynomial.coeff_monomial, hd]

/-- If every nonzero degree scaling of a finite vector sum belongs to a
subspace, each degree component belongs to it. This is the character
independence argument needed for invariant valuation filtrations. -/
theorem homogeneous_component_mem_of_scalar_orbit_mem [Infinite K] (S : Submodule K V)
    (s : Finset ℕ) (u : ℕ → V)
    (horbit : ∀ c : K, c ≠ 0 → (∑ k ∈ s, c ^ k • u k) ∈ S)
    {d : ℕ} (hd : d ∈ s) : u d ∈ S := by
  by_contra hnot
  obtain ⟨φ, hφ, hSφ⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot
    (inferInstance : Module.Projective K (V ⧸ S))
  have heval : ∀ c : K, c ≠ 0 → (scalarOrbitPolynomial φ s u).eval c = 0 := by
    intro c hc
    rw [scalarOrbitPolynomial_eval]
    have hmem : φ (∑ k ∈ s, c ^ k • u k) ∈ S.map φ :=
      Submodule.mem_map_of_mem (horbit c hc)
    rw [hSφ] at hmem
    exact hmem
  have hroots : Set.Infinite {c : K | (scalarOrbitPolynomial φ s u).IsRoot c} := by
    apply (Set.finite_singleton (0 : K)).infinite_compl.mono
    intro c hc
    exact heval c (by simpa using hc)
  have hp := Polynomial.eq_zero_of_infinite_isRoot (scalarOrbitPolynomial φ s u) hroots
  have hcoeff := scalarOrbitPolynomial_coeff φ s u hd
  rw [hp, Polynomial.coeff_zero] at hcoeff
  exact hφ hcoeff.symm

end CoefficientExtraction

section ValuationHomogeneity

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- The literal additive-valuation threshold subspace, including the threshold
`⊤`. The top threshold is the kernel of the valuation, so it is needed to
retain the case of a vanishing finite homogeneous sum. -/
def invariantValuationFiltration (v : AddValuation F (WithTop ℝ))
    (htrivial : ∀ c : K, c ≠ 0 → v (algebraMap K F c) = 0)
    (b : WithTop ℝ) : Submodule K F where
  carrier := {f | b ≤ v f}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    exact v.map_le_add hf hg
  smul_mem' := by
    intro c f hf
    by_cases hc : c = 0
    · subst c
      simp
    · change b ≤ v (c • f)
      rw [Algebra.smul_def, v.map_mul, htrivial c hc, zero_add]
      exact hf

theorem invariantValuationFiltration_eq_real_threshold
    (v : AddValuation F (WithTop ℝ))
    (htrivial : ∀ c : K, c ≠ 0 → v (algebraMap K F c) = 0) (a : ℝ) :
    invariantValuationFiltration v htrivial (a : WithTop ℝ) =
      valuationFiltration v (LinearMap.id : F →ₗ[K] F) htrivial a := by
  ext f
  rfl

/-- Actual degree invariance forces the value of a finite sum to be at most
the value of each of its homogeneous components. The coefficient-extraction
argument also rules out cancellation to zero among nonzero components. -/
theorem valuation_sum_le_component_of_scalar_invariance [Infinite K]
    (v : AddValuation F (WithTop ℝ))
    (htrivial : ∀ c : K, c ≠ 0 → v (algebraMap K F c) = 0)
    (s : Finset ℕ) (u : ℕ → F)
    (hinvariant : ∀ c : K, c ≠ 0 →
      v (∑ k ∈ s, c ^ k • u k) = v (∑ k ∈ s, u k))
    {d : ℕ} (hd : d ∈ s) : v (∑ k ∈ s, u k) ≤ v (u d) := by
  let S := invariantValuationFiltration v htrivial (v (∑ k ∈ s, u k))
  have horbit : ∀ c : K, c ≠ 0 → (∑ k ∈ s, c ^ k • u k) ∈ S := by
    intro c hc
    change v (∑ k ∈ s, u k) ≤ v (∑ k ∈ s, c ^ k • u k)
    rw [hinvariant c hc]
  exact homogeneous_component_mem_of_scalar_orbit_mem S s u horbit hd

/-- The Gauss minimum law is a conclusion of the genuine degree-action
invariance and scalar-triviality hypotheses, including zero coefficients. -/
theorem valuation_sum_eq_inf_of_scalar_invariance [Infinite K]
    (v : AddValuation F (WithTop ℝ))
    (htrivial : ∀ c : K, c ≠ 0 → v (algebraMap K F c) = 0)
    (s : Finset ℕ) (hs : s.Nonempty) (u : ℕ → F)
    (hinvariant : ∀ c : K, c ≠ 0 →
      v (∑ k ∈ s, c ^ k • u k) = v (∑ k ∈ s, u k)) :
    v (∑ k ∈ s, u k) = s.inf' hs (fun k => v (u k)) := by
  apply le_antisymm
  · apply (Finset.le_inf'_iff _ _).mpr
    intro d hd
    exact valuation_sum_le_component_of_scalar_invariance v htrivial s u hinvariant hd
  · exact v.map_le_sum (fun k hk => Finset.inf'_le _ hk)

/-- The same minimum law with the usual empty-minimum convention `⊤`.
It therefore applies uniformly to the zero polynomial as well. -/
theorem valuation_sum_eq_finset_inf_of_scalar_invariance [Infinite K]
    (v : AddValuation F (WithTop ℝ))
    (htrivial : ∀ c : K, c ≠ 0 → v (algebraMap K F c) = 0)
    (s : Finset ℕ) (u : ℕ → F)
    (hinvariant : ∀ c : K, c ≠ 0 →
      v (∑ k ∈ s, c ^ k • u k) = v (∑ k ∈ s, u k)) :
    v (∑ k ∈ s, u k) = s.inf (fun k => v (u k)) := by
  apply le_antisymm
  · apply Finset.le_inf_iff.mpr
    intro d hd
    exact valuation_sum_le_component_of_scalar_invariance v htrivial s u hinvariant hd
  · exact v.map_le_sum (fun k hk => Finset.inf_le hk)

variable {A : Type*} [CommRing A]

/-- Evaluating an actual polynomial after scaling its fiber variable is the
literal scalar degree orbit of its homogeneous monomial terms. -/
theorem polynomial_eval₂_degree_scaling (f : A →+* F) (p : A[X]) (z : F) (c : K) :
    p.eval₂ f (algebraMap K F c * z) =
      ∑ k ∈ p.support, c ^ k • (f (p.coeff k) * z ^ k) := by
  rw [Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Algebra.smul_def, map_pow, mul_pow]
  ring

/-- Source Gauss formula for an actual polynomial represented in an extension
field. It follows from invariance under every nonzero scalar scaling of the
fiber variable, not from an assumed coefficient minimum law. -/
theorem valuation_polynomial_eval₂_eq_inf_of_degree_invariance [Infinite K]
    (v : AddValuation F (WithTop ℝ))
    (htrivial : ∀ c : K, c ≠ 0 → v (algebraMap K F c) = 0)
    (f : A →+* F) (p : A[X]) (z : F)
    (hinvariant : ∀ c : K, c ≠ 0 →
      v (p.eval₂ f (algebraMap K F c * z)) = v (p.eval₂ f z)) :
    v (p.eval₂ f z) = p.support.inf
      (fun k => v (f (p.coeff k)) + k • v z) := by
  have heval : p.eval₂ f z = ∑ k ∈ p.support, f (p.coeff k) * z ^ k := by
    rw [Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  have horbit : ∀ c : K, c ≠ 0 →
      v (∑ k ∈ p.support, c ^ k • (f (p.coeff k) * z ^ k)) =
        v (∑ k ∈ p.support, f (p.coeff k) * z ^ k) := by
    intro c hc
    rw [← polynomial_eval₂_degree_scaling f p z c, ← heval]
    exact hinvariant c hc
  have hGauss := valuation_sum_eq_finset_inf_of_scalar_invariance v htrivial p.support
    (fun k => f (p.coeff k) * z ^ k) horbit
  rw [← heval] at hGauss
  simpa only [v.map_mul, v.map_pow] using hGauss

end ValuationHomogeneity

end SGPT.Foundations.Schemes
