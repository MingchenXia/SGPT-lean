import SGPT.Projective.Maps
import SGPT.BDivisor.Modification

/-! Genuine whole projective linear automorphisms and the actual moving-centre translations. -/

set_option autoImplicit false
noncomputable section

namespace SGPT.BDivisor.MovingCentresNext

open Set SGPT.Projective
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open scoped Manifold ContDiff

variable {N : ℕ}

def projectiveLinearHomeomorph
    (e : (Fin (N + 1) → ℂ) ≃ₗ[ℂ] (Fin (N + 1) → ℂ)) :
    ComplexProjectiveSpace N ≃ₜ ComplexProjectiveSpace N where
  toFun := ComplexProjectiveSpace.linearMap e.toLinearMap e.injective
  invFun := ComplexProjectiveSpace.linearMap e.symm.toLinearMap e.symm.injective
  left_inv p := by
    induction p using ComplexProjectiveSpace.ind with
    | h v hv =>
      rw [ComplexProjectiveSpace.linearMap_mk, ComplexProjectiveSpace.linearMap_mk]
      apply (ComplexProjectiveSpace.mk_eq_mk_iff _ _).mpr
      exact ⟨1, by simp⟩
  right_inv p := by
    induction p using ComplexProjectiveSpace.ind with
    | h v hv =>
      rw [ComplexProjectiveSpace.linearMap_mk, ComplexProjectiveSpace.linearMap_mk]
      apply (ComplexProjectiveSpace.mk_eq_mk_iff _ _).mpr
      exact ⟨1, by simp⟩
  continuous_toFun := (ComplexProjectiveSpace.contMDiff_linearMap e.toLinearMap e.injective).continuous
  continuous_invFun := (ComplexProjectiveSpace.contMDiff_linearMap e.symm.toLinearMap e.symm.injective).continuous

theorem projectiveLinearHomeomorph_contMDiff
    (e : (Fin (N + 1) → ℂ) ≃ₗ[ℂ] (Fin (N + 1) → ℂ)) :
    ContMDiff 𝓘(ℂ, ComplexModel N) 𝓘(ℂ, ComplexModel N) ∞ (projectiveLinearHomeomorph e) :=
  ComplexProjectiveSpace.contMDiff_linearMap e.toLinearMap e.injective

theorem projectiveLinearHomeomorph_symm_contMDiff
    (e : (Fin (N + 1) → ℂ) ≃ₗ[ℂ] (Fin (N + 1) → ℂ)) :
    ContMDiff 𝓘(ℂ, ComplexModel N) 𝓘(ℂ, ComplexModel N) ∞ (projectiveLinearHomeomorph e).symm :=
  ComplexProjectiveSpace.contMDiff_linearMap e.symm.toLinearMap e.symm.injective

theorem projectiveLinearHomeomorph_isAnalyticModification
    (e : (Fin (N + 1) → ℂ) ≃ₗ[ℂ] (Fin (N + 1) → ℂ)) :
    IsAnalyticModification (n := N) (projectiveLinearHomeomorph e) :=
  ⟨projectiveLinearHomeomorph_contMDiff e, (projectiveLinearHomeomorph e).isProperMap,
    ∅, ∅, (projectiveLinearHomeomorph e).symm, isClosed_empty,
    isComplexAnalyticSubset_empty, interior_empty, isClosed_empty,
    isComplexAnalyticSubset_empty, interior_empty, preimage_empty,
    (projectiveLinearHomeomorph_symm_contMDiff e).contMDiffOn,
    (fun x _ => (projectiveLinearHomeomorph e).apply_symm_apply x),
    (fun y _ => (projectiveLinearHomeomorph e).symm_apply_apply y)⟩

def pointTranslationLinearEquiv (a b : ℂ) : (Fin 3 → ℂ) ≃ₗ[ℂ] (Fin 3 → ℂ) where
  toFun v := ![v 0, v 1 + a * v 0, v 2 + b * v 0]
  invFun v := ![v 0, v 1 - a * v 0, v 2 - b * v 0]
  left_inv v := by ext i; fin_cases i <;> simp
  right_inv v := by ext i; fin_cases i <;> simp
  map_add' v w := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c v := by ext i; fin_cases i <;> simp <;> ring

def pointTranslation (a b : ℂ) : ComplexProjectiveSpace 2 ≃ₜ ComplexProjectiveSpace 2 :=
  projectiveLinearHomeomorph (pointTranslationLinearEquiv a b)

theorem pointTranslation_affinePoint (a b : ℂ) (z : ComplexModel 2) :
    pointTranslation a b (ComplexProjectiveSpace.affinePoint 0 z) =
      ComplexProjectiveSpace.affinePoint 0
        (WithLp.toLp 2 ![z 0 + a, z 1 + b]) := by
  change ComplexProjectiveSpace.linearMap (pointTranslationLinearEquiv a b).toLinearMap
    (pointTranslationLinearEquiv a b).injective
      (ComplexProjectiveSpace.mk (ComplexProjectiveSpace.affineLift 0 z) _) = _
  rw [ComplexProjectiveSpace.linearMap_mk]
  apply (ComplexProjectiveSpace.mk_eq_mk_iff _ _).mpr
  refine ⟨1, ?_⟩
  ext i
  fin_cases i <;> simp [pointTranslationLinearEquiv, ComplexProjectiveSpace.affineLift]
  rfl

theorem pointTranslation_contMDiff (a b : ℂ) :
    ContMDiff 𝓘(ℂ, ComplexModel 2) 𝓘(ℂ, ComplexModel 2) ∞ (pointTranslation a b) :=
  projectiveLinearHomeomorph_contMDiff _

theorem pointTranslation_isAnalyticModification (a b : ℂ) :
    IsAnalyticModification (n := 2) (pointTranslation a b) :=
  projectiveLinearHomeomorph_isAnalyticModification _

end SGPT.BDivisor.MovingCentresNext
