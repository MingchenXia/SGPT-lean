import SGPT.Foundations.Schemes.ProjectiveSectionExtension

/-! # Actual principal-open overlap annihilation

True quasicoherent localization clears overlap errors before sheaf gluing.
The actual principal-open restriction need not be injective.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace SGPT.Foundations.Schemes

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : CommRingCat.{u}}

/-- The actual R-linear restriction from D(g) to D(gf). -/
def affinePrincipalRestriction (M : (Spec R).Modules) (g f : R) :
    Γ(M, PrimeSpectrum.basicOpen g) →ₗ[R] Γ(M, PrimeSpectrum.basicOpen (g * f)) :=
  ((modulesSpecToSheaf.obj M).obj.map
    (homOfLE (PrimeSpectrum.basicOpen_mul_le_left g f)).op).hom

/-- Genuine global restriction factors through the actual principal-open overlap. -/
theorem affinePrincipalRestriction_global (M : (Spec R).Modules) (g f : R)
    (s : Γ(M, ⊤)) :
    affinePrincipalRestriction M g f (affineSectionRestriction M g s) =
      affineSectionRestriction M (g * f) s := by
  change M.presheaf.map _ (M.presheaf.map _ s) = M.presheaf.map _ s
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- A genuine overlap error vanishing on D(gf) is killed by a power of f on D(g). -/
theorem affinePrincipalSection_zero_after_power (M : (Spec R).Modules)
    [M.IsQuasicoherent] (g f : R) {t : Γ(M, PrimeSpectrum.basicOpen g)}
    (h : affinePrincipalRestriction M g f t = 0) :
    ∃ b : ℕ, f ^ b • t = 0 := by
  obtain ⟨a, s, hs⟩ := affineSection_clearDenominator M g t
  have hz : affineSectionRestriction M (g * f) s = 0 := by
    rw [← affinePrincipalRestriction_global M g f s, hs,
      (affinePrincipalRestriction M g f).map_smul, h, smul_zero]
  obtain ⟨b, hb⟩ := affineSection_zero_after_power M (g * f) hz
  have hr : (g * f) ^ b • (g ^ a • t) = 0 := by
    rw [← hs, ← (affineSectionRestriction M g).map_smul, hb, map_zero]
  refine ⟨b, ((M.isSMulRegular_of_le_basicOpen (f := g) le_rfl).pow (a + b)).right_eq_zero_of_smul ?_⟩
  simpa only [mul_pow, pow_add, ← mul_smul, mul_assoc, mul_comm, mul_left_comm] using hr

/-- Actual sections equal on the overlap become equal after a genuine coordinate power. -/
theorem affinePrincipalSection_eq_after_power (M : (Spec R).Modules)
    [M.IsQuasicoherent] (g f : R) {s t : Γ(M, PrimeSpectrum.basicOpen g)}
    (h : affinePrincipalRestriction M g f s = affinePrincipalRestriction M g f t) :
    ∃ b : ℕ, f ^ b • s = f ^ b • t := by
  obtain ⟨b, hb⟩ := affinePrincipalSection_zero_after_power M g f (t := s - t) (by
    rw [map_sub, h, sub_self])
  exact ⟨b, sub_eq_zero.mp (by simpa only [smul_sub] using hb)⟩

end

end SGPT.Foundations.Schemes
