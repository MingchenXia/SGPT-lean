import SGPT.Trace.BertiniCanonicalJacobianCocycle
import SGPT.Trace.BertiniNormalDivisionDensity
import Mathlib.LinearAlgebra.Alternating.Curry
import Mathlib.LinearAlgebra.Basis.Fin

/-! Actual conormal residue: choice independence and bijectivity.

The final construction manufactures the normalized normal from the original
SliceChart incidence derivative. It produces the actual top-covector residue
on that derivative's kernel, before transporting to the native member tangent
bundle or claiming a global Hodge normalization.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace SGPT.Trace.Bertini

open Bundle Set Filter
open scoped Manifold ContDiff Topology BigOperators
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open scoped ProductComplexManifold
open ProductComplexManifold

variable {d : ℕ}

/-- Actual ambient top covectors kill any tuple contained in the kernel
of a genuinely normalized nonzero original conormal. -/
theorem topForm_eq_zero_on_conormalKernel
    (ℓ : ComplexModel (d + 1) →ₗ[ℂ] ℂ) (ν : ComplexModel (d + 1)) (hν : ℓ ν = 1)
    (α : (ComplexModel (d + 1)) [⋀^Fin (d + 1)]→ₗ[ℂ] ℂ)
    (v : Fin (d + 1) → ComplexModel (d + 1)) (hv : ∀ i, ℓ (v i) = 0) : α v = 0 := by
  apply α.map_linearDependent
  intro hli
  have htop := hli.span_eq_top_of_card_eq_finrank (by simp)
  have hle : Submodule.span ℂ (Set.range v) ≤ LinearMap.ker ℓ :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hv i)
  rw [htop] at hle
  have hn : ℓ ν = 0 := hle (Submodule.mem_top : ν ∈ (⊤ : Submodule ℂ _))
  exact one_ne_zero (hν.symm.trans hn)

/-- Contraction of the actual ambient alternating covector with the given
normal, restricted to the literal conormal kernel. -/
def conormalResidueLinearMap (ℓ : ComplexModel (d + 1) →ₗ[ℂ] ℂ)
    (ν : ComplexModel (d + 1)) :
    ((ComplexModel (d + 1)) [⋀^Fin (d + 1)]→ₗ[ℂ] ℂ) →ₗ[ℂ]
      ((LinearMap.ker ℓ) [⋀^Fin d]→ₗ[ℂ] ℂ) where
  toFun α := (α.curryLeft ν).compLinearMap (LinearMap.ker ℓ).subtype
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem conormalResidueLinearMap_apply (ℓ : ComplexModel (d + 1) →ₗ[ℂ] ℂ)
    (ν : ComplexModel (d + 1))
    (α : (ComplexModel (d + 1)) [⋀^Fin (d + 1)]→ₗ[ℂ] ℂ)
    (v : Fin d → LinearMap.ker ℓ) :
    conormalResidueLinearMap ℓ ν α v = α (Matrix.vecCons ν (fun i => (v i).val)) := rfl

/-- The actual residue does not depend on any choice of normalized normal. -/
theorem conormalResidueLinearMap_independent (ℓ : ComplexModel (d + 1) →ₗ[ℂ] ℂ)
    (ν ν' : ComplexModel (d + 1)) (hν : ℓ ν = 1) (hν' : ℓ ν' = 1) :
    conormalResidueLinearMap ℓ ν = conormalResidueLinearMap ℓ ν' := by
  apply LinearMap.ext
  intro α
  apply AlternatingMap.ext
  intro v
  have hz := topForm_eq_zero_on_conormalKernel ℓ ν hν α
    (Matrix.vecCons (ν - ν') (fun i => (v i).val)) (by
      intro i
      cases i using Fin.cases with
      | zero => simp [map_sub, hν, hν']
      | succ i => exact (v i).property)
  have hsub : α (Matrix.vecCons (ν - ν') (fun i => (v i).val)) =
      α (Matrix.vecCons ν (fun i => (v i).val)) - α (Matrix.vecCons ν' (fun i => (v i).val)) :=
    congrArg (fun β : (ComplexModel (d + 1)) [⋀^Fin d]→ₗ[ℂ] ℂ =>
      β (fun i => (v i).val)) ((α.curryLeft).map_sub ν ν')
  exact sub_eq_zero.mp (hsub.symm.trans hz)

private def conormalExtendedBasis (ℓ : ComplexModel (d + 1) →ₗ[ℂ] ℂ)
    (ν : ComplexModel (d + 1)) (hν : ℓ ν = 1) {q : ℕ}
    (b : Module.Basis (Fin q) ℂ (LinearMap.ker ℓ)) :
    Module.Basis (Fin (q + 1)) ℂ (ComplexModel (d + 1)) :=
  Module.Basis.mkFinCons ν b
    (by
      intro a x hx hax
      have h := congrArg ℓ hax
      simpa only [map_add, map_smul, hν, LinearMap.mem_ker.mp hx, smul_eq_mul,
        mul_one, add_zero, map_zero] using h)
    (by
      intro z
      refine ⟨-ℓ z, ?_⟩
      change ℓ (z + (-ℓ z) • ν) = 0
      simp [hν])

private theorem conormalKernel_finrank (ℓ : ComplexModel (d + 1) →ₗ[ℂ] ℂ)
    (ν : ComplexModel (d + 1)) (hν : ℓ ν = 1) :
    Module.finrank ℂ (LinearMap.ker ℓ) = d := by
  have hdim := Module.finrank_eq_card_basis
    (conormalExtendedBasis ℓ ν hν (Module.finBasis ℂ (LinearMap.ker ℓ)))
  simpa using Nat.add_right_cancel (show Module.finrank ℂ (LinearMap.ker ℓ) + 1 = d + 1 by
    simpa using hdim.symm)

/-- The actual choice-independent conormal residue is an isomorphism on
the actual original kernel, proved using genuine kernel/normal bases. -/
def conormalResidueLinearEquiv (ℓ : ComplexModel (d + 1) →ₗ[ℂ] ℂ)
    (ν : ComplexModel (d + 1)) (hν : ℓ ν = 1) :
    ((ComplexModel (d + 1)) [⋀^Fin (d + 1)]→ₗ[ℂ] ℂ) ≃ₗ[ℂ]
      ((LinearMap.ker ℓ) [⋀^Fin d]→ₗ[ℂ] ℂ) := by
  let b := (Module.finBasis ℂ (LinearMap.ker ℓ)).reindex
    (finCongr (conormalKernel_finrank ℓ ν hν))
  let B := conormalExtendedBasis ℓ ν hν b
  have hB : (B : Fin (d + 1) → ComplexModel (d + 1)) =
      Matrix.vecCons ν (fun i => (b i).val) := Module.Basis.coe_mkFinCons _ _ _ _
  apply LinearEquiv.ofBijective (conormalResidueLinearMap ℓ ν)
  constructor
  · apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro α hα
    apply (α.map_basis_eq_zero_iff B).mp
    have hz := congrArg (fun β : (LinearMap.ker ℓ) [⋀^Fin d]→ₗ[ℂ] ℂ => β b) hα
    change α (Matrix.vecCons ν (fun i => (b i).val)) = 0 at hz
    rw [hB]
    exact hz
  · intro β
    refine ⟨β b • B.det, ?_⟩
    have hval : conormalResidueLinearMap ℓ ν (β b • B.det) b = β b := by
      rw [conormalResidueLinearMap_apply, ← hB, AlternatingMap.smul_apply, Module.Basis.det_self]
      exact mul_one _
    calc
      conormalResidueLinearMap ℓ ν (β b • B.det) =
          (conormalResidueLinearMap ℓ ν (β b • B.det) b) • b.det :=
        (conormalResidueLinearMap ℓ ν (β b • B.det)).eq_smul_basis_det b
      _ = β b • b.det := by rw [hval]
      _ = β := (β.eq_smul_basis_det b).symm

namespace SliceChart

variable {N : ℕ} {Y : Type} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (d + 1)) Y] [IsComplexManifold (d + 1) Y]
  {p : Y → SGPT.Projective.ComplexProjectiveSpace N} {φ : Y → EReal}
  (c : SliceChart (d + 1) p φ)

/-- The derivative of the ORIGINAL member equation, in the original X
directions at the original actual inverse-chart slice point. -/
def originalMemberConormal (q : (Metric.ball c.ζ₀ c.r) × c.tangentPatch) :
    ComplexModel (d + 1) →L[ℂ] ℂ :=
  (fderiv ℂ (conormalGenerator p c.i c.e c.j 0)
    (c.Φ.invFun (flatProj c.m (prodModelEquiv N (d + 1)
      (q.1.val, c.tangentLift q.2.val))))).comp
    (((prodModelEquiv N (d + 1)) : _ →L[ℂ] _).comp
      (ContinuousLinearMap.inr ℂ (ComplexModel N) (ComplexModel (d + 1))))

theorem originalMemberConormal_normal
    (hp : ContMDiff 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) ∞ p)
    (q : (Metric.ball c.ζ₀ c.r) × c.tangentPatch) :
    c.originalMemberConormal q (EuclideanSpace.single c.m 1) = c.tangentNormalDenominator q := by
  change fderiv ℂ (conormalGenerator p c.i c.e c.j 0) _ (slDir c.m) = _
  exact fderiv_conormalGenerator_zero_slDir p hp
    (c.source_subset (c.Φ.mapsTo_invFun (c.mapsTo_target q.1.val q.1.property
      (c.tangentLift q.2.val) q.2.property))) c.m

/-- The normalized original ambient vector is manufactured from the
actual proved nonzero original conormal denominator. -/
def originalNormalizedNormal (q : (Metric.ball c.ζ₀ c.r) × c.tangentPatch) :
    ComplexModel (d + 1) :=
  (c.tangentNormalDenominator q)⁻¹ • EuclideanSpace.single c.m 1

theorem originalNormalizedNormal_spec
    (hp : ContMDiff 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) ∞ p)
    (q : (Metric.ball c.ζ₀ c.r) × c.tangentPatch) :
    c.originalMemberConormal q (c.originalNormalizedNormal q) = 1 := by
  rw [originalNormalizedNormal, map_smul, originalMemberConormal_normal c hp q,
    smul_eq_mul, inv_mul_cancel₀ (c.tangentNormalDenominator_ne_zero hp q)]

/-- Actual residue isomorphism for the actual original moving member
conormal, with no incoming normal or adjunction isomorphism certificate. -/
def originalConormalResidueEquiv
    (hp : ContMDiff 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) ∞ p)
    (q : (Metric.ball c.ζ₀ c.r) × c.tangentPatch) :
    ((ComplexModel (d + 1)) [⋀^Fin (d + 1)]→ₗ[ℂ] ℂ) ≃ₗ[ℂ]
      ((LinearMap.ker (c.originalMemberConormal q).toLinearMap) [⋀^Fin d]→ₗ[ℂ] ℂ) :=
  conormalResidueLinearEquiv (c.originalMemberConormal q).toLinearMap
    (c.originalNormalizedNormal q) (c.originalNormalizedNormal_spec hp q)

end SliceChart

end SGPT.Trace.Bertini
