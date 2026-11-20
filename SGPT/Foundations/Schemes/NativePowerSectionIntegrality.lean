import SGPT.Foundations.Schemes.NativePowerConeSquare
import Mathlib.AlgebraicGeometry.Morphisms.Integral
/-!
# NativePowerSectionIntegrality

Actual tensor comparisons give homogeneous preimages. Positive powers place every homogeneous element in the genuine power-ring image and prove integral ring and cone maps. The actual cone square reduces properness to a positive tensor power.
-/

open CategoryTheory Limits AlgebraicGeometry Opposite Module
open scoped DirectSum
namespace SGPT.Foundations.Schemes
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
variable {X : Scheme.{u}} [IsIntegral X] (L : IntrinsicLineBundle X) (q : ℕ)

/-- Every genuine degree-qm section has an actual preimage under the iterated tensor comparison. -/
theorem IntrinsicLineBundle.nativePowerSection_bijective (m : ℕ) :
    Function.Bijective (L.nativePowerSection q m) := by
  let E := nativeLineTensorPowerMulIso L.atlas q m
  have : IsIso (E.inv.val.app (.op ⊤)) :=
    inferInstanceAs (IsIso ((SheafOfModules.evaluation _ (.op ⊤)).map E.inv))
  exact (ConcreteCategory.isIso_iff_bijective (E.inv.val.app (.op ⊤))).mp inferInstance

/-- The true power-section ring image contains every actual homogeneous section of degree divisible by q. -/
theorem IntrinsicLineBundle.nativePowerSectionRingHom_exists_degree (n : ℕ)
    (s : bundlePowerGlobalSections L.sheaf n) (hn : q ∣ n) :
    ∃ y, L.nativePowerSectionRingHom q y = L.ofSection n s := by
  obtain ⟨m, rfl⟩ := hn
  obtain ⟨t, ht⟩ := (L.nativePowerSection_bijective q m).surjective s
  exact ⟨(L.tensorPower q).ofSection m t,
    (L.nativePowerSectionRingHom_ofSection q m t).trans (congrArg (L.ofSection (q * m)) ht)⟩

/-- The actual qth power of every genuine homogeneous section belongs to the true power-section ring image. -/
theorem IntrinsicLineBundle.nativePowerSectionRingHom_exists_homogeneous_pow (n : ℕ)
    (s : bundlePowerGlobalSections L.sheaf n) :
    ∃ y, L.nativePowerSectionRingHom q y = (L.ofSection n s) ^ q := by
  let := atlasPowerGradedCommRing L.atlas
  change ∃ y, L.nativePowerSectionRingHom q y =
    (DirectSum.of (bundlePowerGlobalSections L.sheaf) n s) ^ q
  rw [DirectSum.ofPow]
  exact L.nativePowerSectionRingHom_exists_degree q (q • n) _
    ⟨n, by simp⟩

/-- The literal positive-power section-ring homomorphism is integral, without a finite-generation premise. -/
theorem IntrinsicLineBundle.nativePowerSectionRingHom_isIntegral (hq : 0 < q) :
    (L.nativePowerSectionRingHom q).IsIntegral := by
  let f := L.nativePowerSectionRingHom q
  let := f.toAlgebra
  intro x
  change _root_.IsIntegral (L.tensorPower q).sectionRing x
  induction x using DirectSum.induction_on with
  | zero => exact isIntegral_zero
  | of n s =>
      change _root_.IsIntegral (L.tensorPower q).sectionRing (L.ofSection n s)
      apply IsIntegral.of_pow hq
      obtain ⟨y, hy⟩ := L.nativePowerSectionRingHom_exists_homogeneous_pow q n s
      rw [← hy]
      change _root_.IsIntegral (L.tensorPower q).sectionRing
        (algebraMap (L.tensorPower q).sectionRing L.sectionRing y)
      exact isIntegral_algebraMap
  | add x y hx hy => exact hx.add hy

/-- The actual full section-ring cone power morphism is integral for every positive power. -/
theorem IntrinsicLineBundle.nativePowerConeMap_isIntegralHom (hq : 0 < q) :
    IsIntegralHom (L.nativePowerConeMap q) := by
  apply IsIntegralHom.SpecMap_iff.mpr
  exact L.nativePowerSectionRingHom_isIntegral q hq

/-- Properness of the true q-power contraction yields properness of the true full-cone contraction. -/
theorem IntrinsicLineBundle.nativeConeMap_isProper_of_power (hq : 0 < q)
    [IsProper (L.tensorPower q).nativeConeMap] : IsProper L.nativeConeMap := by
  have : IsSeparated (L.nativePowerConeMap q) := by
    dsimp [IntrinsicLineBundle.nativePowerConeMap]
    infer_instance
  have : IsProper (L.nativeConeMap ≫ L.nativePowerConeMap q) := by
    rw [← L.nativePowerConeMap_commutes q]
    have := nativeDualLineTensorPowerMap_isProper L.atlas q hq
    infer_instance
  exact IsProper.of_comp L.nativeConeMap (L.nativePowerConeMap q)

end
end SGPT.Foundations.Schemes
