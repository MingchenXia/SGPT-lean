import SGPT.Checks.Comparison.BJRationalPicardPresentations
import Mathlib.RingTheory.Localization.BaseChange

/-! Genuine positive tensor-power identifications produced internally from
actual rational Picard equality, with no common-line certificate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.NAPotential.BJ.NativePicard
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory SGPT.Foundations.Schemes
open Scheme.Modules
open scoped TensorProduct

/-- Rational scalar extension kills EXACTLY torsion; its localization
criterion produces a genuine positive common multiplier internally. -/
theorem exists_pos_nsmul_eq_of_rationalize_eq {G : Type*} [AddCommGroup G]
    {a b : G} (h : (1:ℚ)⊗ₜ[ℤ] a=(1:ℚ)⊗ₜ[ℤ] b) :
    ∃ k : ℕ,0<k ∧ k•a=k•b := by
  let t : G →ₗ[ℤ] ℚ⊗[ℤ] G := TensorProduct.mk ℤ ℚ G 1
  have ht : t a=t b := h
  obtain ⟨s,hs⟩ := (IsLocalizedModule.eq_iff_exists (nonZeroDivisors ℤ) t).mp ht
  have hz : s.val≠0 := mem_nonZeroDivisors_iff_ne_zero.mp s.property
  obtain ⟨z,hz,hsmul⟩ : ∃ z : ℤ,z≠0 ∧ z•a=z•b := ⟨s.val,hz,hs⟩
  cases z with
  | ofNat k =>
    refine ⟨k,Nat.pos_of_ne_zero ?_,?_⟩
    · intro hk
      exact hz (by simp [hk])
    · change (k:ℤ)•a=(k:ℤ)•b at hsmul
      simpa only [natCast_zsmul] using hsmul
  | negSucc k =>
    refine ⟨k+1,Nat.succ_pos _,?_⟩
    simpa only [Int.negSucc_eq,neg_smul,add_smul,one_smul,Nat.cast_smul_eq_nsmul,add_nsmul,one_nsmul,neg_inj] using hsmul

attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory
variable {X : Scheme.{0}}

/-- The actual rational line-class equality produces an actual tensor-power
isomorphism of the SAME original sheaves, in every dimension. -/
theorem exists_pos_tensorPower_iso_of_rationalPicardClass_eq
    {L M : X.Modules} (a : LineBundleAtlas L) (b : LineBundleAtlas M)
    (h : rationalPicardClass a=rationalPicardClass b) :
    ∃ k : ℕ,0<k ∧ Nonempty (bundleTensorPower L k≅bundleTensorPower M k) := by
  obtain ⟨k,hk,hkclass⟩ := exists_pos_nsmul_eq_of_rationalize_eq h
  refine ⟨k,hk,toSkeleton_eq_toSkeleton_iff.mp ?_⟩
  have hp : (linePicardClass a)^k=(linePicardClass b)^k :=
    congrArg Additive.toMul hkclass
  rw [← linePicardClass_val (SGPT.NAPotential.Berkovich.BJSections.powerAtlas a k),
    ← linePicardClass_val (SGPT.NAPotential.Berkovich.BJSections.powerAtlas b k),
    linePicardClass_power,linePicardClass_power,hp]

/-- Two actual denominator presentations of the SAME rational Picard class
produce a positive common tensor-power isomorphism internally. -/
theorem exists_pos_tensorPower_iso_of_normalized_class_eq
    {L M : X.Modules} (a : LineBundleAtlas L) (b : LineBundleAtlas M)
    {m n : ℕ} (hm : 0<m) (hn : 0<n)
    (h : (m:ℚ)⁻¹•rationalPicardClass a=(n:ℚ)⁻¹•rationalPicardClass b) :
    ∃ k : ℕ,0<k ∧ Nonempty (bundleTensorPower L (n*k)≅bundleTensorPower M (m*k)) := by
  have hmQ : (m:ℚ)≠0 := by exact_mod_cast hm.ne'
  have hnQ : (n:ℚ)≠0 := by exact_mod_cast hn.ne'
  have hc := congrArg (fun z : RationalPicardSpace X => ((m:ℚ)*(n:ℚ))•z) h
  simp only [smul_smul] at hc
  have hcL : ((m:ℚ)*(n:ℚ))*(m:ℚ)⁻¹=(n:ℚ) := by field_simp [hmQ]
  have hcM : ((m:ℚ)*(n:ℚ))*(n:ℚ)⁻¹=(m:ℚ) := by field_simp [hnQ]
  rw [hcL,hcM] at hc
  have hpow : rationalPicardClass (SGPT.NAPotential.Berkovich.BJSections.powerAtlas a n)=
      rationalPicardClass (SGPT.NAPotential.Berkovich.BJSections.powerAtlas b m) := by
    simpa only [rationalPicardClass_power,← Nat.cast_smul_eq_nsmul ℚ] using hc
  obtain ⟨k,hk,hkclass⟩ := exists_pos_nsmul_eq_of_rationalize_eq hpow
  refine ⟨k,hk,toSkeleton_eq_toSkeleton_iff.mp ?_⟩
  have hp := congrArg Additive.toMul hkclass
  change (linePicardClass (SGPT.NAPotential.Berkovich.BJSections.powerAtlas a n))^k=
    (linePicardClass (SGPT.NAPotential.Berkovich.BJSections.powerAtlas b m))^k at hp
  rw [linePicardClass_power,linePicardClass_power,← pow_mul,← pow_mul] at hp
  rw [← linePicardClass_val (SGPT.NAPotential.Berkovich.BJSections.powerAtlas a (n*k)),
    ← linePicardClass_val (SGPT.NAPotential.Berkovich.BJSections.powerAtlas b (m*k)),
    linePicardClass_power,linePicardClass_power,hp]

end SGPT.NAPotential.BJ.NativePicard
