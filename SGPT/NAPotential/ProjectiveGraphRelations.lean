import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# All homogeneous relations of a rational graph

For actual elements `bᵢ` of an `A`-algebra `K`, the graph relation ideal is generated
by **all** homogeneous polynomials vanishing at `(1, b)`. Multivariate
homogenization proves that its `Y₀ = 1` chart has exactly the affine relation
ideal `ker (aeval b)`. Its coordinate algebra is therefore the actual subalgebra
`A[b]`, including at poles of the original rational map.

This is the affine-chart algebra in step (b) of `claude-alg-primes3:remaining`.
The global bihomogeneous scheme construction and analytic trace bridge remain
separate obligations; this file does not assert `HighCodimProductGraphData`.
Blueprint: `projective-graph-relations.tex`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.NAPotential.AlgPrimes3.ProjectiveGraphRelations

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {σ A K : Type*} [CommRing A] [CommRing K] [Algebra A K]

/-- The normalized homogeneous coordinates of the rational graph. -/
def graphCoordinates (b : σ → K) : Option σ → K
  | none => 1
  | some i => b i

/-- Setting the distinguished homogeneous coordinate to one. -/
def dehomogenize : MvPolynomial (Option σ) A →ₐ[A] MvPolynomial σ A :=
  aeval (fun i => match i with | none => 1 | some j => X j)

@[simp]
theorem dehomogenize_X_none :
    dehomogenize (A := A) (σ := σ) (X none) = 1 := by
  simp [dehomogenize]

@[simp]
theorem dehomogenize_X_some (i : σ) :
    dehomogenize (A := A) (X (some i)) = X i := by
  simp [dehomogenize]

@[simp]
theorem dehomogenize_rename (p : MvPolynomial σ A) :
    dehomogenize (rename some p) = p := by
  simp [dehomogenize, aeval_rename, Function.comp_def, aeval_X_left_apply]

theorem dehomogenize_surjective :
    Function.Surjective (dehomogenize (A := A) (σ := σ)) :=
  fun p => ⟨rename some p, dehomogenize_rename p⟩

/-- Homogenization in a new variable, at the polynomial's actual total degree. -/
def homogenize (p : MvPolynomial σ A) : MvPolynomial (Option σ) A :=
  ∑ d ∈ p.support,
    rename some (monomial d (coeff d p)) * X none ^ (p.totalDegree - d.degree)

theorem isHomogeneous_homogenize (p : MvPolynomial σ A) :
    (homogenize p).IsHomogeneous p.totalDegree := by
  classical
  apply IsHomogeneous.sum
  intro d hd
  have hdN : d.degree ≤ p.totalDegree := le_totalDegree hd
  have hmon : (rename some (monomial d (coeff d p))).IsHomogeneous d.degree :=
    (isHomogeneous_monomial _ rfl).rename_isHomogeneous
  simpa only [Nat.add_sub_of_le hdN] using
    hmon.mul (isHomogeneous_X_pow none (p.totalDegree - d.degree))

@[simp]
theorem dehomogenize_homogenize (p : MvPolynomial σ A) :
    dehomogenize (homogenize p) = p := by
  classical
  simp only [homogenize, map_sum, map_mul, map_pow, dehomogenize_rename,
    dehomogenize_X_none, one_pow, mul_one]
  exact p.as_sum.symm

/-- Evaluation at `(1,b)` is affine evaluation after dehomogenization. -/
theorem aeval_graphCoordinates (b : σ → K) (p : MvPolynomial (Option σ) A) :
    aeval (graphCoordinates b) p = aeval b (dehomogenize p) := by
  have h : aeval (R := A) (graphCoordinates b) = (aeval b).comp dehomogenize := by
    ext i
    cases i <;> simp [graphCoordinates, dehomogenize]
  exact DFunLike.congr_fun h p

/-- All homogeneous polynomial relations of the actual rational functions. -/
def homogeneousRelations (b : σ → K) : Set (MvPolynomial (Option σ) A) :=
  {p | ∃ n : ℕ, p.IsHomogeneous n ∧ aeval (graphCoordinates b) p = 0}

/-- The full graph relation ideal, rather than the naive cross-multiplication ideal. -/
def graphRelationIdeal (b : σ → K) : Ideal (MvPolynomial (Option σ) A) :=
  Ideal.span (homogeneousRelations (A := A) b)

theorem graphRelationIdeal_isHomogeneous (b : σ → K) :
    (graphRelationIdeal (A := A) b).IsHomogeneous
      (homogeneousSubmodule (Option σ) A) := by
  apply Ideal.homogeneous_span
  rintro p ⟨n, hn, _⟩
  exact ⟨n, hn⟩

theorem graphRelationIdeal_le_ker (b : σ → K) :
    graphRelationIdeal (A := A) b ≤ RingHom.ker (aeval (graphCoordinates b)) := by
  apply Ideal.span_le.mpr
  rintro p ⟨_, _, hp⟩
  exact hp

theorem homogenize_mem_graphRelationIdeal (b : σ → K) {p : MvPolynomial σ A}
    (hp : aeval b p = 0) : homogenize p ∈ graphRelationIdeal (A := A) b := by
  apply Ideal.subset_span
  refine ⟨p.totalDegree, isHomogeneous_homogenize p, ?_⟩
  rw [aeval_graphCoordinates, dehomogenize_homogenize, hp]

/-- Scaling every variable of a homogeneous polynomial scales its value by its degree. -/
theorem eval₂Hom_scale_of_isHomogeneous {τ L : Type*} [CommRing L]
    {p : MvPolynomial τ A} {n : ℕ} (hp : p.IsHomogeneous n)
    (f : A →+* L) (x : τ → L) (t : L) :
    eval₂Hom f (fun i => t * x i) p = t ^ n * eval₂Hom f x p := by
  classical
  change p.eval₂ f (fun i => t * x i) = t ^ n * p.eval₂ f x
  rw [eval₂_eq, eval₂_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdeg : d.degree = n := by
    rw [Finsupp.degree_eq_weight_one]
    exact hp (mem_support_iff.mp hd)
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    ← Finsupp.degree_apply, hdeg]
  ac_rfl

/-- The genuine cone substitution, with an independent polynomial variable:
`Y₀ ↦ t`, `Yᵢ ↦ bᵢ t`. Its kernel retains every relation at the base locus. -/
def coneEval (b : σ → K) : MvPolynomial (Option σ) A →+* Polynomial K :=
  eval₂Hom (Polynomial.C.comp (algebraMap A K))
    (fun i => Polynomial.X * Polynomial.C (graphCoordinates b i))

theorem coneEval_of_isHomogeneous (b : σ → K) {p : MvPolynomial (Option σ) A}
    {n : ℕ} (hp : p.IsHomogeneous n) :
    coneEval b p = Polynomial.X ^ n * Polynomial.C (aeval (graphCoordinates b) p) := by
  rw [coneEval, eval₂Hom_scale_of_isHomogeneous hp]
  congr 1
  exact (map_eval₂Hom (algebraMap A K) (graphCoordinates b) Polynomial.C p).symm

/-- Extracting the coefficient of `tⁿ` extracts the corresponding homogeneous relation. -/
theorem coeff_coneEval (b : σ → K) (p : MvPolynomial (Option σ) A) (n : ℕ) :
    (coneEval b p).coeff n = aeval (graphCoordinates b) (homogeneousComponent n p) := by
  classical
  have hsum : coneEval b p = ∑ i ∈ Finset.range (p.totalDegree + 1),
      Polynomial.C (aeval (graphCoordinates b) (homogeneousComponent i p)) * Polynomial.X ^ i := by
    conv_lhs => rw [← sum_homogeneousComponent p]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [coneEval_of_isHomogeneous b (homogeneousComponent_isHomogeneous i p), mul_comm]
  rw [hsum, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  by_cases hn : n < p.totalDegree + 1
  · simp [hn]
  · have hpn : p.totalDegree < n :=
      lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_of_not_gt hn)
    simp [hn, homogeneousComponent_eq_zero n p hpn]

/-- The all-relations ideal is exactly the kernel of the actual polynomial cone map. -/
theorem graphRelationIdeal_eq_ker_coneEval (b : σ → K) :
    graphRelationIdeal (A := A) b = RingHom.ker (coneEval b) := by
  classical
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro p ⟨n, hp, hzero⟩
    change coneEval b p = 0
    rw [coneEval_of_isHomogeneous b hp, hzero, map_zero, mul_zero]
  · intro p hp
    rw [← sum_homogeneousComponent p]
    apply Ideal.sum_mem
    intro n _
    apply Ideal.subset_span
    refine ⟨n, homogeneousComponent_isHomogeneous n p, ?_⟩
    rw [← coeff_coneEval b p n, show coneEval b p = 0 from hp, Polynomial.coeff_zero]

/-- Over a domain, the full graph relation ideal is prime. -/
theorem graphRelationIdeal_isPrime [IsDomain K] (b : σ → K) :
    (graphRelationIdeal (A := A) b).IsPrime := by
  rw [graphRelationIdeal_eq_ker_coneEval]
  exact RingHom.ker_isPrime (coneEval b)

/-- **Exact affine chart**: dehomogenizing all homogeneous relations gives every
relation of `A[b]`, with no additional components over the original base locus. -/
theorem map_dehomogenize_graphRelationIdeal (b : σ → K) :
    Ideal.map dehomogenize (graphRelationIdeal (A := A) b) =
      RingHom.ker (aeval b) := by
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    intro p hp
    change aeval b (dehomogenize p) = 0
    rw [← aeval_graphCoordinates]
    exact graphRelationIdeal_le_ker b hp
  · intro p hp
    rw [← dehomogenize_homogenize p]
    exact Ideal.mem_map_of_mem dehomogenize (homogenize_mem_graphRelationIdeal b hp)

/-- The affine relation quotient is the subalgebra actually generated by the `bᵢ`. -/
def affineRelationQuotientEquiv (b : σ → K) :
    (MvPolynomial σ A ⧸ RingHom.ker (aeval (R := A) b)) ≃ₐ[A]
      Algebra.adjoin A (Set.range b) :=
  (Ideal.quotientKerEquivRange (aeval (R := A) b)).trans
    (Subalgebra.equivOfEq _ _ (aeval_range (R := A) b))

/-- The `Y₀=1` equation algebra of the full homogeneous graph is canonically `A[b]`. -/
def graphChartQuotientEquiv (b : σ → K) :
    (MvPolynomial σ A ⧸ Ideal.map dehomogenize (graphRelationIdeal (A := A) b)) ≃ₐ[A]
      Algebra.adjoin A (Set.range b) :=
  (Ideal.quotientEquivAlgOfEq A (map_dehomogenize_graphRelationIdeal b)).trans
    (affineRelationQuotientEquiv b)

/-- This is exactly the underlying subring `A[b]` used by `exists_affine_generators`. -/
theorem adjoin_toSubring_eq (b : σ → K) :
    (Algebra.adjoin A (Set.range b)).toSubring =
      Subring.closure (Set.range (algebraMap A K) ∪ Set.range b) :=
  Algebra.adjoin_eq_ring_closure (Set.range b)

/-- The elementary denominator relations are members of the full ideal; they are
used only to identify its fibers where the common denominator is nonzero. -/
theorem denominator_relation_mem (b : σ → K) (d a : A) (i : σ)
    (h : algebraMap A K d * b i = algebraMap A K a) :
    C d * X (some i) - C a * X none ∈ graphRelationIdeal (A := A) b := by
  apply Ideal.subset_span
  refine ⟨1, (isHomogeneous_C_mul_X d (some i)).sub (isHomogeneous_C_mul_X a none), ?_⟩
  simpa only [map_sub, map_mul, aeval_C, aeval_X, graphCoordinates, mul_one,
    sub_eq_zero] using h

/-- Every projective solution over the locus of a nonzero denominator has the
actual normalized graph coordinates. The full graph ideal remains in the hypothesis. -/
theorem coordinates_eq_of_vanishing {L : Type*} [Field L] (b : σ → K)
    (d : A) (a : σ → A) (hba : ∀ i, algebraMap A K d * b i = algebraMap A K (a i))
    (χ : A →+* L) (hd : χ d ≠ 0) (y : Option σ → L) (hy : y ≠ 0)
    (hzero : ∀ p ∈ graphRelationIdeal (A := A) b, eval₂Hom χ y p = 0) :
    y none ≠ 0 ∧ y = fun j => y none * graphCoordinates (fun i => χ (a i) / χ d) j := by
  have hlinear (i : σ) : χ d * y (some i) = χ (a i) * y none := by
    have h := hzero _ (denominator_relation_mem b d (a i) i (hba i))
    simpa only [map_sub, map_mul, eval₂Hom_C, eval₂Hom_X', sub_eq_zero] using h
  have hnone : y none ≠ 0 := by
    intro h0
    apply hy
    funext j
    cases j with
    | none => exact h0
    | some i =>
      have h := hlinear i
      rw [h0, mul_zero] at h
      exact (mul_eq_zero.mp h).resolve_left hd
  refine ⟨hnone, ?_⟩
  funext j
  cases j with
  | none => simp [graphCoordinates]
  | some i =>
    change y (some i) = y none * (χ (a i) / χ d)
    calc
      y (some i) = (χ d)⁻¹ * (χ d * y (some i)) := by
        rw [← mul_assoc, inv_mul_cancel₀ hd, one_mul]
      _ = (χ d)⁻¹ * (χ (a i) * y none) := by rw [hlinear]
      _ = y none * (χ (a i) / χ d) := by rw [div_eq_mul_inv]; ac_rfl

section FiniteEquations

variable [Finite σ] [IsNoetherianRing A]

/-- Noetherianity chooses actual homogeneous relations, with their vanishing
property retained, rather than an unrelated finite family of equations. -/
theorem exists_finite_homogeneous_relations (b : σ → K) :
    ∃ F : Finset (MvPolynomial (Option σ) A),
      (∀ p ∈ F, ∃ n : ℕ, p.IsHomogeneous n ∧ aeval (graphCoordinates b) p = 0) ∧
      Ideal.span (F : Set (MvPolynomial (Option σ) A)) = graphRelationIdeal (A := A) b := by
  obtain ⟨F, hF, hspan⟩ :=
    (Submodule.fg_span_iff_fg_span_finset_subset (homogeneousRelations (A := A) b)).mp
      (graphRelationIdeal (A := A) b).fg_of_isNoetherianRing
  exact ⟨F, fun p hp => hF hp, hspan.symm⟩

/-- The same finite equations cut out the common zero set of the full graph ideal
over every coefficient ring, hence also on complex affine charts. -/
theorem exists_finite_equations (b : σ → K) :
    ∃ F : Finset (MvPolynomial (Option σ) A),
      (∀ p ∈ F, ∃ n : ℕ, p.IsHomogeneous n ∧ aeval (graphCoordinates b) p = 0) ∧
      ∀ {L : Type*} [CommRing L] (χ : MvPolynomial (Option σ) A →+* L),
        (∀ p ∈ F, χ p = 0) ↔ ∀ p ∈ graphRelationIdeal (A := A) b, χ p = 0 := by
  obtain ⟨F, hF, hspan⟩ := exists_finite_homogeneous_relations (A := A) b
  refine ⟨F, hF, ?_⟩
  intro L _ χ
  constructor
  · intro h p hp
    have hle : graphRelationIdeal (A := A) b ≤ RingHom.ker χ := by
      rw [← hspan]
      exact Ideal.span_le.mpr h
    exact hle hp
  · intro h p hp
    apply h p
    rw [← hspan]
    exact Ideal.subset_span hp

end FiniteEquations

end SGPT.NAPotential.AlgPrimes3.ProjectiveGraphRelations
