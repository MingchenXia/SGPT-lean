import SGPT.NAPotential.ProjectiveGraphRelationCore

/-!
# Actual bihomogeneous Segre equations

The actual polynomial substitution `Z_(i,j) ↦ X_i Y_j` preserves both separate
degrees and commutes with evaluation. Finite actual homogeneous relations of an
actual Segre vector therefore produce actual bihomogeneous relations of the
original pair. No BiProj framework or equation certificate is assumed.

Blueprint: `projective-graph-bihomogeneous.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.NAPotential.AlgPrimes3.ProjectiveGraphSegreEquations

open MvPolynomial ProjectiveGraphRelationCore

attribute [local instance] MvPolynomial.gradedAlgebra

variable {I J L A K : Type*} [CommRing A] [CommRing K] [Algebra A K]

/-- The left projective degree assigns weight one exactly to the original `X` variables. -/
def leftWeight : Sum I J → ℕ := Sum.elim (fun _ => 1) (fun _ => 0)

/-- The right projective degree assigns weight one exactly to the original `Y` variables. -/
def rightWeight : Sum I J → ℕ := Sum.elim (fun _ => 0) (fun _ => 1)

/-- The actual Segre coordinate vector in the original coefficient algebra. -/
def segreVector (e : L → I × J) (a : I → K) (b : J → K) : L → K :=
  fun k => a (e k).1 * b (e k).2

/-- The actual Segre polynomial substitution, retaining both original variable groups. -/
def segreSubstitution (e : L → I × J) : MvPolynomial L A →ₐ[A] MvPolynomial (Sum I J) A :=
  aeval (fun k => X (Sum.inl (e k).1) * X (Sum.inr (e k).2))

/-- Substitution by weighted-degree-one polynomials retains the original total degree. -/
theorem weightedHomogeneous_aeval_of_degree_one {T : Type*} (w : T → ℕ)
    (g : L → MvPolynomial T A) (hg : ∀ i, (g i).IsWeightedHomogeneous w 1)
    {p : MvPolynomial L A} {n : ℕ} (hp : p.IsHomogeneous n) :
    (aeval g p).IsWeightedHomogeneous w n := by
  classical
  induction hp using IsWeightedHomogeneous.induction_on with
  | zero => simpa using isWeightedHomogeneous_zero A w n
  | add p q hp hq ihp ihq => simpa only [map_add] using ihp.add ihq
  | monomial d r hd =>
    have hdeg : ∑ i ∈ d.support, d i = n := by
      change d.degree = n
      rw [Finsupp.degree_eq_weight_one]
      exact hd
    rw [aeval_monomial]
    have hprod : (∏ i ∈ d.support, g i ^ d i).IsWeightedHomogeneous w n := by
      rw [← hdeg]
      apply IsWeightedHomogeneous.prod
      intro i _
      simpa using (hg i).pow (d i)
    simpa only [MvPolynomial.algebraMap_eq, Finsupp.prod] using hprod.C_mul r

/-- A degree-`n` Segre equation has the true original left degree `n`. -/
theorem segreSubstitution_left {p : MvPolynomial L A} {n : ℕ}
    (hp : p.IsHomogeneous n) (e : L → I × J) :
    (segreSubstitution e p).IsWeightedHomogeneous (leftWeight (I := I) (J := J)) n := by
  apply weightedHomogeneous_aeval_of_degree_one _ _ _ hp
  intro k
  simpa only [leftWeight, Sum.elim_inl, Sum.elim_inr, add_zero] using
    (isWeightedHomogeneous_X A (leftWeight (I := I) (J := J)) (Sum.inl (e k).1)).mul
      (isWeightedHomogeneous_X A (leftWeight (I := I) (J := J)) (Sum.inr (e k).2))

/-- A degree-`n` Segre equation has the true original right degree `n`. -/
theorem segreSubstitution_right {p : MvPolynomial L A} {n : ℕ}
    (hp : p.IsHomogeneous n) (e : L → I × J) :
    (segreSubstitution e p).IsWeightedHomogeneous (rightWeight (I := I) (J := J)) n := by
  apply weightedHomogeneous_aeval_of_degree_one _ _ _ hp
  intro k
  simpa only [rightWeight, Sum.elim_inl, Sum.elim_inr, zero_add] using
    (isWeightedHomogeneous_X A (rightWeight (I := I) (J := J)) (Sum.inl (e k).1)).mul
      (isWeightedHomogeneous_X A (rightWeight (I := I) (J := J)) (Sum.inr (e k).2))

/-- Evaluation of the original product equation is exactly evaluation on the actual Segre vector. -/
theorem aeval_segreSubstitution (e : L → I × J) (a : I → K) (b : J → K)
    (p : MvPolynomial L A) :
    aeval (Sum.elim a b) (segreSubstitution e p) = aeval (segreVector e a b) p := by
  have h : (aeval (R := A) (Sum.elim a b)).comp (segreSubstitution e) =
      aeval (segreVector e a b) := by
    ext k
    simp [segreSubstitution, segreVector]
  exact DFunLike.congr_fun h p

section Finite

variable [Finite L] [IsNoetherianRing A]

/-- Finite actual relations of the Segre vector produce actual bihomogeneous equations
of the original pair, retaining their exact original rational vanishing. -/
theorem exists_finite_bihomogeneous_relations (e : L → I × J) (a : I → K) (b : J → K) :
    ∃ F : Finset (MvPolynomial L A),
      Ideal.span (F : Set (MvPolynomial L A)) = (relationCore (A := A) (segreVector e a b)).toIdeal ∧
      ∀ p ∈ F, ∃ n : ℕ,
        p.IsHomogeneous n ∧
        (segreSubstitution e p).IsWeightedHomogeneous (leftWeight (I := I) (J := J)) n ∧
        (segreSubstitution e p).IsWeightedHomogeneous (rightWeight (I := I) (J := J)) n ∧
        aeval (Sum.elim a b) (segreSubstitution e p) = 0 := by
  obtain ⟨F, hF, hspan⟩ := exists_finite_relations (A := A) (segreVector e a b)
  refine ⟨F, hspan, ?_⟩
  intro p hp
  obtain ⟨n, hn, hzero⟩ := hF p hp
  exact ⟨n, hn, segreSubstitution_left hn e, segreSubstitution_right hn e,
    by rw [aeval_segreSubstitution, hzero]⟩

end Finite

end SGPT.NAPotential.AlgPrimes3.ProjectiveGraphSegreEquations
