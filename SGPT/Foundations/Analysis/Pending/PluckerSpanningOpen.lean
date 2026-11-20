import Mathlib.Topology.Instances.Matrix
import SGPT.Foundations.Analysis.Pending.PluckerSpanningBound
import SGPT.Foundations.Analysis.Pending.LinearProjectionJacobian

set_option autoImplicit false

/-!
# Spanning is an open condition on the family

Demailly's proof of CADG III.2.6 (`\source{demailly-cadg:III.2.6}`,
`agbook.tex:8704`) moves each decomposable basis form `β_s` a little:

> After a slight perturbation of the `β_{s,j}`, we may assume that each
> projection `π_s` defines a ramified covering of `A ∩ (Δ'×Δ'')`, and that
> `(β_s)` remains a basis of `Λ^{p,p}T^⋆Ω`.

The perturbation is legitimate because the two clauses of that sentence are of
opposite natures: being a ramified covering of a fixed germ holds on a DENSE set
of directions, while remaining a basis holds on an OPEN one.  Only the second is
pure linear algebra, and it is what this module proves:

`isOpen_setOf_spansPlucker` — the set of families `B : σ → (ℂⁿ →L[ℂ] ℂ^k)` whose
Plücker functionals separate points of `Λ^k ℂⁿ` is open;

`exists_dist_lt_spansPlucker` — its `δ`-ball form, which is what an argument
perturbing one `β_s` at a time consumes.

The route is short because both halves are already abstract.  `SpansPlucker B`
says exactly that the Plücker pairing `pluckerMap B` is injective
(`spansPlucker_iff_injective`), that pairing depends LINEARLY on the array of
Plücker coordinates (`pairingCLM`), the array depends continuously — indeed
polynomially, through `k × k` minors — on the family, and the set of injective
continuous linear maps out of a finite-dimensional space is open
(`ContinuousLinearMap.isOpen_injective`).

Nothing here is specific to the decomposable-form application: the statements are
about an arbitrary finite family of `k × n` complex matrices.
-/

noncomputable section

open Function
open scoped Matrix

namespace SGPT.Foundations.Analysis.Pending.PluckerSpanningOpen

open FirstPass
open SGPT.Foundations.Analysis.Pending.CauchyBinet
  SGPT.Foundations.Analysis.Pending.PluckerSpanningBound
  SGPT.Foundations.Analysis.Pending.LinearProjectionJacobian

variable {k n : ℕ} {σ : Type*} [Fintype σ]

/-! ## The pairing as a linear function of the Plücker coordinates -/

/-- The pairing of an arbitrary array of "Plücker coordinates" `P s I` with a
vector of `Λ^k ℂⁿ`.  For `P s I = plucker (B s) I` this is `pluckerMap B`. -/
def pairingLin (P : σ → CardSubset k n → ℂ) :
    EuclideanSpace ℂ (CardSubset k n) →ₗ[ℂ] EuclideanSpace ℂ σ where
  toFun ξ := WithLp.toLp 2 fun s => ∑ I : CardSubset k n, P s I * ξ I
  map_add' := by
    intro x y
    ext s
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro c x
    ext s
    simp [Finset.mul_sum, mul_left_comm]

omit [Fintype σ] in
@[simp]
theorem pairingLin_apply (P : σ → CardSubset k n → ℂ)
    (ξ : EuclideanSpace ℂ (CardSubset k n)) (s : σ) :
    pairingLin P ξ s = ∑ I : CardSubset k n, P s I * ξ I := rfl

theorem pairingLin_plucker (B : σ → Matrix (Fin k) (Fin n) ℂ) :
    pairingLin (fun s I => plucker (B s) I) = pluckerMap B := rfl

/-- The pairing, bundled as a `ℂ`-LINEAR map from the array of Plücker
coordinates to continuous linear maps.  Linearity in the array is the only
reason the openness argument below needs no estimate. -/
def pairingCLM : (σ → CardSubset k n → ℂ) →ₗ[ℂ]
    (EuclideanSpace ℂ (CardSubset k n) →L[ℂ] EuclideanSpace ℂ σ) where
  toFun P := LinearMap.toContinuousLinearMap (pairingLin P)
  map_add' := by
    intro P Q
    ext ξ s
    simp [pairingLin, add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro c P
    ext ξ s
    simp [pairingLin, Finset.mul_sum, mul_assoc]

@[simp]
theorem pairingCLM_apply (P : σ → CardSubset k n → ℂ)
    (ξ : EuclideanSpace ℂ (CardSubset k n)) (s : σ) :
    pairingCLM P ξ s = ∑ I : CardSubset k n, P s I * ξ I := rfl

/-! ## Spanning is injectivity of the pairing -/

/-- **`SpansPlucker` is the injectivity of the Plücker pairing.** -/
theorem spansPlucker_iff_injective (B : σ → Matrix (Fin k) (Fin n) ℂ) :
    SpansPlucker B ↔ Injective (pairingCLM (fun s I => plucker (B s) I)) := by
  constructor
  · intro hB x y hxy
    have h : ∀ s, ∑ I : CardSubset k n, plucker (B s) I * (x I - y I) = 0 := by
      intro s
      have h1 := congrArg (fun z : EuclideanSpace ℂ σ => z s) hxy
      simp only [pairingCLM_apply] at h1
      have hsplit : ∑ I : CardSubset k n, plucker (B s) I * (x I - y I)
          = (∑ I : CardSubset k n, plucker (B s) I * x I)
            - ∑ I : CardSubset k n, plucker (B s) I * y I := by
        simp [mul_sub, Finset.sum_sub_distrib]
      rw [hsplit, h1, sub_self]
    have hz := hB (fun I => x I - y I) h
    ext I
    have := congrFun hz I
    simpa [sub_eq_zero] using this
  · intro hinj ξ hξ
    have h : pairingCLM (fun s I => plucker (B s) I)
        (WithLp.toLp 2 ξ : EuclideanSpace ℂ (CardSubset k n))
        = pairingCLM (fun s I => plucker (B s) I) 0 := by
      rw [map_zero]
      ext s
      simpa using hξ s
    have h0 := hinj h
    funext I
    simpa using congrArg (fun z : EuclideanSpace ℂ (CardSubset k n) => z I) h0

/-! ## Continuity of the Plücker coordinates in the family -/

/-- `rectMatrix` as a `ℂ`-linear map. -/
def rectMatrixLin : (ComplexModel n →L[ℂ] ComplexModel k) →ₗ[ℂ] Matrix (Fin k) (Fin n) ℂ where
  toFun := rectMatrix
  map_add' := by
    intro B B'
    ext i j
    simp [rectMatrix_apply]
  map_smul' := by
    intro c B
    ext i j
    simp [rectMatrix_apply]

/-- The family of matrices of a family of linear maps, as a `ℂ`-linear map. -/
def familyRectMatrixLin :
    (σ → (ComplexModel n →L[ℂ] ComplexModel k)) →ₗ[ℂ] (σ → Matrix (Fin k) (Fin n) ℂ) :=
  LinearMap.pi fun s => rectMatrixLin.comp (LinearMap.proj s)

theorem continuous_familyRectMatrix :
    Continuous fun B : σ → (ComplexModel n →L[ℂ] ComplexModel k) =>
      fun s => rectMatrix (B s) :=
  (familyRectMatrixLin (σ := σ) (k := k) (n := n)).continuous_of_finiteDimensional

omit [Fintype σ] in
/-- The Plücker coordinates are `k × k` minors, hence continuous in the family. -/
theorem continuous_pluckerArray :
    Continuous fun M : σ → Matrix (Fin k) (Fin n) ℂ =>
      fun s I => plucker (M s) I := by
  refine continuous_pi fun s => continuous_pi fun I => ?_
  exact ((continuous_apply s).matrix_submatrix id I.emb).matrix_det

/-! ## Openness -/

/-- **Spanning is an open condition.**  The families of `ℂ`-linear maps
`ℂⁿ → ℂ^k` whose Plücker functionals separate points of `Λ^k ℂⁿ` form an open
subset of `σ → (ℂⁿ →L[ℂ] ℂ^k)`.

This is Demailly's "`(β_s)` remains a basis of `Λ^{p,p}`", and it is exactly the
clause of his perturbation step that costs nothing: a family that spans keeps
spanning after every sufficiently small move of the `β_{s,j}`, each `s`
independently. -/
theorem isOpen_setOf_spansPlucker :
    IsOpen {B : σ → (ComplexModel n →L[ℂ] ComplexModel k) |
      SpansPlucker fun s => rectMatrix (B s)} := by
  have hcont : Continuous fun B : σ → (ComplexModel n →L[ℂ] ComplexModel k) =>
      pairingCLM (fun s I => plucker (rectMatrix (B s)) I) :=
    (pairingCLM (σ := σ) (k := k) (n := n)).continuous_of_finiteDimensional.comp
      (continuous_pluckerArray.comp continuous_familyRectMatrix)
  have hset : {B : σ → (ComplexModel n →L[ℂ] ComplexModel k) |
      SpansPlucker fun s => rectMatrix (B s)} =
      (fun B => pairingCLM (fun s I => plucker (rectMatrix (B s)) I)) ⁻¹'
        {L : EuclideanSpace ℂ (CardSubset k n) →L[ℂ] EuclideanSpace ℂ σ | Injective L} := by
    ext B
    exact spansPlucker_iff_injective _
  rw [hset]
  exact ContinuousLinearMap.isOpen_injective.preimage hcont

/-- **The `δ`-ball form of openness**, in the shape a per-`s` perturbation
consumes: a spanning family has a radius within which every family still spans,
uniformly over the members. -/
theorem exists_dist_lt_spansPlucker
    (B : σ → (ComplexModel n →L[ℂ] ComplexModel k))
    (hB : SpansPlucker fun s => rectMatrix (B s)) :
    ∃ δ > 0, ∀ B' : σ → (ComplexModel n →L[ℂ] ComplexModel k),
      (∀ s, ‖B' s - B s‖ < δ) → SpansPlucker fun s => rectMatrix (B' s) := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 isOpen_setOf_spansPlucker B hB
  refine ⟨δ, hδ, fun B' hB' => ?_⟩
  refine hball ?_
  rw [Metric.mem_ball, dist_pi_lt_iff hδ]
  intro s
  rw [dist_eq_norm]
  exact hB' s

end SGPT.Foundations.Analysis.Pending.PluckerSpanningOpen
