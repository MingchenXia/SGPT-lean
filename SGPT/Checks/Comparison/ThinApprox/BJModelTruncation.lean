import SGPT.Checks.Comparison.BJModelSectionIdeal
import SGPT.Checks.Comparison.BJPrintedDefinition
import SGPT.Checks.Comparison.SourceNumericalAmpleness
import SGPT.Foundations.Envelope.AlgGeom.SchemeAmpleLineGlobalGeneration
import SGPT.Foundations.Envelope.AlgGeom.GeneratedLineBaseIdealUnit
import SGPT.Foundations.Envelope.AlgGeom.InvertibleBaseIdealTransport

namespace SGPT.NAPotential.BJ
end SGPT.NAPotential.BJ
namespace SGPT.NAPotential.BJ.AppSeq
end SGPT.NAPotential.BJ.AppSeq
namespace SGPT.NAPotential.BJ.FixedRay
end SGPT.NAPotential.BJ.FixedRay
namespace SGPT.NAPotential.BJ.MaxClosure
end SGPT.NAPotential.BJ.MaxClosure
namespace SGPT.NAPotential.BJ.Pair3ClassStability
end SGPT.NAPotential.BJ.Pair3ClassStability
namespace SGPT.NAPotential.BJ.Pair3Div
end SGPT.NAPotential.BJ.Pair3Div
namespace SGPT.NAPotential.BJ.Printed
end SGPT.NAPotential.BJ.Printed
namespace SGPT.NAPotential.BJ.RationalPromotion
end SGPT.NAPotential.BJ.RationalPromotion
namespace SGPT.NAPotential.BJ.SourceDXZPositive
end SGPT.NAPotential.BJ.SourceDXZPositive
namespace SGPT.NAPotential.BJ.SourceDivUnique
end SGPT.NAPotential.BJ.SourceDivUnique
namespace SGPT.NAPotential.BJ.SourceNet
end SGPT.NAPotential.BJ.SourceNet
namespace SGPT.NAPotential.BJ.SourceRationalPromotion
end SGPT.NAPotential.BJ.SourceRationalPromotion
namespace SGPT.NAPotential.BJCycle
end SGPT.NAPotential.BJCycle
namespace SGPT.NAPotential.BJModel
end SGPT.NAPotential.BJModel
namespace SGPT.NAPotential.ThinApprox.BJ
end SGPT.NAPotential.ThinApprox.BJ
namespace SGPT.NAPotential.ThinApprox.BJ.AppSeq
end SGPT.NAPotential.ThinApprox.BJ.AppSeq
namespace SGPT.NAPotential.ThinApprox.BJ.FixedRay
end SGPT.NAPotential.ThinApprox.BJ.FixedRay
namespace SGPT.NAPotential.ThinApprox.BJ.MaxClosure
end SGPT.NAPotential.ThinApprox.BJ.MaxClosure
namespace SGPT.NAPotential.ThinApprox.BJ.Pair3ClassStability
end SGPT.NAPotential.ThinApprox.BJ.Pair3ClassStability
namespace SGPT.NAPotential.ThinApprox.BJ.Pair3Div
end SGPT.NAPotential.ThinApprox.BJ.Pair3Div
namespace SGPT.NAPotential.ThinApprox.BJ.Printed
end SGPT.NAPotential.ThinApprox.BJ.Printed
namespace SGPT.NAPotential.ThinApprox.BJ.SourceDXZPositive
end SGPT.NAPotential.ThinApprox.BJ.SourceDXZPositive
namespace SGPT.NAPotential.ThinApprox.BJ.SourceDivUnique
end SGPT.NAPotential.ThinApprox.BJ.SourceDivUnique
namespace SGPT.NAPotential.ThinApprox.BJ.SourceNet
end SGPT.NAPotential.ThinApprox.BJ.SourceNet
namespace SGPT.NAPotential.ThinApprox.BJCycle
end SGPT.NAPotential.ThinApprox.BJCycle
namespace SGPT.NAPotential.ThinApprox.BJModel
end SGPT.NAPotential.ThinApprox.BJModel


/-!
# Truncations of rational GF functions of an ample class are Fubini–Study functions

Source: `chapter_NApotential.tex`, `thm:BJappseq` and the definition of `𝓗^gf_ℚ(L^An)`;
Boucksom–Jonsson ([BJ22], `references/bj22-trivval`), §2.5, Proposition `prop:FSideal` and
Corollary `cor:FSideal`. Step R9 of `claude-bj-energy:plan`; blueprint
`claude-bj-model.tex`.

Let `ω ∈ Pic(X)_ℚ` have ample numerical class and let `φ ∈ 𝓗^gf_ℚ(ω)`, presented by a package
`E` (`E.picardClass = ω`): `φ = m⁻¹ max_j (log|s_j| + λ_j)`, `s_j ∈ H⁰(X, L^{⊗n})`,
`ω = (n/m) [L]`. For `c ∈ ℚ` the truncation `max(φ, c)` is a Fubini–Study function of `ω` in the
sense of [BJ22, `prop:FSideal`]: there are `d ≥ 1` and a flag ideal `𝔞` such that

* `max(φ, c) = (m d)⁻¹ φ_𝔞`,
* `M ⊗ 𝔞_λ` is globally generated for all `λ`, where `M = L^{⊗nd}`,
* `[M] = (m d) ω` in `Pic(X)_ℚ`

(`exists_generated_flagIdeal_truncation`, `rationalPicardClass_power_eq_smul_picardClass`).
The proof: `L^{⊗n}` is ample by Kleiman's criterion (SGPT.Foundations.Envelope), so `L^{⊗nd}` is globally
generated for `d ≫ 0`; then `max_rationalGFFunction_eq_phi` and
`isGeneratedBy_sectionFlagIdeal` apply to `𝔞 = (t^{-dmc}) + ∑_j 𝔟_{s_j^d} t^{-dλ_j}`.

Without ampleness the truncations are still in `PL⁺(X)` (`isPLPos_truncation_package`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.NAPotential.ThinApprox.BJModel
open SGPT.NAPotential.BJModel

open AlgebraicGeometry CategoryTheory
open Scheme.Modules SGPT.Foundations.Schemes
open scoped ENNReal
open SGPT.NAPotential.Berkovich SGPT.NAPotential.Berkovich.BJSections
open SGPT.NAPotential.BJ SGPT.NAPotential.ThinApprox.BJ SGPT.NAPotential.BJ.NativePicard SGPT.NAPotential.BJ.Printed SGPT.NAPotential.ThinApprox.BJ.Printed
open SGPT.Foundations.Envelope SGPT.Foundations.Envelope.InvertibleSheafBaseIdeal

attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

variable {X : Scheme.{0}}

/-! ### Tensor powers -/

/-- The skeleton class of the canonical tensor power used by `SGPT.Foundations.Envelope`. -/
theorem toSkeleton_canonicalTensorPower (M : X.Modules) (n : ℕ) :
    toSkeleton (CanonicalGeometry.bundleTensorPower M n) = (toSkeleton M) ^ n := by
  induction n with
  | zero => exact toSkeleton_unitObj
  | succ n ih =>
    change toSkeleton (CanonicalGeometry.bundleTensor
      (CanonicalGeometry.bundleTensorPower M n) M) = _
    have he : CanonicalGeometry.bundleTensor (CanonicalGeometry.bundleTensorPower M n) M =
        Scheme.Modules.tensorObj (CanonicalGeometry.bundleTensorPower M n) M := rfl
    rw [he, toSkeleton_tensorObj_eq, ih, pow_succ]

/-- `(L^{⊗n})^{⊗r} ≅ L^{⊗nr}` for the two tensor power constructions in use. -/
theorem nonempty_canonicalPower_iso (L : X.Modules) (n r : ℕ) :
    Nonempty (CanonicalGeometry.bundleTensorPower (SGPT.Foundations.Schemes.bundleTensorPower L n) r ≅
      SGPT.Foundations.Schemes.bundleTensorPower L (n * r)) := by
  apply toSkeleton_eq_toSkeleton_iff.mp
  rw [toSkeleton_canonicalTensorPower, toSkeleton_power, toSkeleton_power, pow_mul]

/-- The rational Picard class of `L^{⊗nd}` is `(m d) ω` for `ω = (n/m) [L]` the class of a
rational GF package. -/
theorem rationalPicardClass_power_eq_smul_picardClass (E : RationalGFPackage X) (d : ℕ) :
    rationalPicardClass (powerAtlas E.atlas (E.n * d)) =
      ((E.m * d : ℕ) : ℚ) • E.picardClass := by
  have hm : (E.m : ℚ) ≠ 0 := by exact_mod_cast E.data.denominator_pos.ne'
  rw [RationalGFPackage.picardClass, gfPicardClass, rationalPicardClass_power,
    ← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
  congr 1
  push_cast
  field_simp

variable (p : X ⟶ Spec (.of ℂ)) [IsProjective p]

local instance : IsProper p := (ProjectiveFactorizationRingIso.of_isProjective p).isProper

/-! ### Truncations -/

/-- **Truncations of rational GF functions are in `PL⁺(X)`**: for `φ ∈ 𝓗^gf_ℚ(L)` (any class)
and `c ∈ ℚ`, `max(φ, c) ∈ PL⁺(X)`. -/
theorem isPLPos_truncation_package (E : RationalGFPackage X) (c : ℚ) :
    IsPLPos p fun v => (max (E.eval p v) ((c : ℝ) : EReal)).toReal :=
  isPLPos_truncation E.atlas E.data c

omit [IsProjective p] in
/-- Sufficiently large tensor powers of an ample invertible sheaf are globally generated. -/
theorem exists_forall_baseIdeal_eq_top {T : X.Modules} (hT : SchemeLineAmpleness.IsAmple p T) :
    ∃ N : ℕ, ∀ r : ℕ, N ≤ r → ∀ hr : IsInvertible (CanonicalGeometry.bundleTensorPower T r),
      baseIdeal hr = ⊤ := by
  obtain ⟨N, hN⟩ := SchemeAmpleLineGlobalGeneration.exists_eventual_generatingSections p T hT
  refine ⟨N, fun r hr hinv => ?_⟩
  obtain ⟨G, -⟩ := hN r hr
  exact GeneratedLineBaseIdealUnit.baseIdeal_eq_top_of_generatingSections hinv G

/-- **Truncations of rational GF functions of an ample class are Fubini–Study functions**
(step R9; [BJ22, `prop:FSideal`]). Let `E` be a rational GF package whose rational Picard class
`ω = (n/m) [L]` has ample numerical class, and `c ∈ ℚ`. Then there are `d ≥ 1` and a flag ideal
`𝔞` such that `L^{⊗nd} ⊗ 𝔞_λ` is globally generated for every `λ` and
`max(φ_E, c) = (m d)⁻¹ φ_𝔞` on `X^An`. -/
theorem exists_generated_flagIdeal_truncation [IsIntegral X] (E : RationalGFPackage X)
    (hω : SGPT.NAPotential.BJ.NativePicard.numericalClass p E.picardClass ∈ NativeRealNumericalClasses.ampleCone p)
    (c : ℚ) :
    ∃ (d : ℕ) (_ : 0 < d) (𝔞 : FlagIdeal X),
      𝔞.IsGeneratedBy (isInvertible_of_atlas (powerAtlas E.atlas (E.n * d))) ∧
      ∀ v : BerkovichPoint p, max (E.eval p v) ((c : ℝ) : EReal) =
        ((((E.m * d : ℕ) : ℝ)⁻¹ * 𝔞.phi v : ℝ) : EReal) := by
  set T := SGPT.Foundations.Schemes.bundleTensorPower E.line E.n with hTdef
  have hT : IsInvertible T := isInvertible_of_atlas (powerAtlas E.atlas E.n)
  have hm : (0 : ℝ) < E.m := by exact_mod_cast E.data.denominator_pos
  -- `L^{⊗n}` is ample
  have hclass : NativeRealNumericalClasses.lineClass p T hT ∈
      NativeRealNumericalClasses.ampleCone p := by
    have h1 : SGPT.NAPotential.BJ.NativePicard.numericalClass p E.picardClass =
        ((E.m : ℚ)⁻¹ : ℚ) • NativeRealNumericalClasses.lineClass p T hT := by
      rw [RationalGFPackage.picardClass, gfPicardClass_eq_powerClass,
        SGPT.NAPotential.BJ.NativePicard.numericalClass_rat_smul, SGPT.NAPotential.BJ.NativePicard.numericalClass_line]
    have h2 := (NativeRealNumericalClasses.ampleCone p).smul_mem hm hω
    rw [h1, ← Rat.cast_smul_eq_qsmul ℝ, smul_smul] at h2
    have h3 : (E.m : ℝ) * (((E.m : ℚ)⁻¹ : ℚ) : ℝ) = 1 := by
      push_cast
      exact mul_inv_cancel₀ hm.ne'
    rwa [h3, one_smul] at h2
  have hample : SchemeLineAmpleness.IsAmple p T :=
    SGPT.NAPotential.BJ.SourceNumericalAmpleness.isAmple_of_lineClass_mem_ampleCone p T hT hclass
  obtain ⟨N, hN⟩ := exists_forall_baseIdeal_eq_top p hample
  -- a common denominator, large enough for global generation
  obtain ⟨d, hd, hdvd, ⟨κ, hκ⟩, hw⟩ :=
    exists_common_denominator E.data.weight (E.m * c) (N + 1) (Nat.succ_pos N)
  choose w hw using hw
  have hNd : N ≤ d := (Nat.le_succ N).trans (Nat.le_of_dvd hd hdvd)
  have hbase : baseIdeal (isInvertible_of_atlas (powerAtlas E.atlas (E.n * d))) = ⊤ := by
    obtain ⟨e⟩ := nonempty_canonicalPower_iso E.line E.n d
    have hinv : IsInvertible (CanonicalGeometry.bundleTensorPower T d) :=
      TensorPowerBaseIdealGrading.tensorPower_isInvertible hT d
    rw [← InvertibleBaseIdealTransport.baseIdeal_eq_of_iso hinv
      (isInvertible_of_atlas (powerAtlas E.atlas (E.n * d))) e]
    exact hN d hNd hinv
  have hw' : ∀ j, (w j : ℝ) = d * (E.data.weight j : ℝ) := fun j => by exact_mod_cast hw j
  have hκ' : (κ : ℝ) = E.m * d * c := by
    have : (κ : ℚ) = E.m * d * c := by rw [hκ]; ring
    exact_mod_cast this
  exact ⟨d, hd, _, isGeneratedBy_sectionFlagIdeal _ _ w κ hbase,
    fun v => max_rationalGFFunction_eq_phi E.atlas E.data c hd w hw' κ hκ' v⟩

/-! ### Fubini–Study functions of a rational class in flag-ideal form -/

/-- **Fubini–Study functions of a rational class `ω`, in the flag-ideal form of [BJ22,
`prop:FSideal`]**: `φ = k⁻¹ φ_𝔞` for an integer `k ≥ 1`, an invertible sheaf `M` with
`[M] = k ω` in `Pic(X)_ℚ` and a flag ideal `𝔞` such that `M ⊗ 𝔞_λ` is globally generated for every
weight `λ` (equivalently, `M_triv ⊗ 𝔞` is globally generated on `X × 𝔸¹`). By [BJ22,
`prop:FSideal`] these are exactly the rational Fubini–Study functions `𝓗(ω)`. -/
def IsFlagFS (ω : RationalPicardSpace X) (φ : BerkovichPoint p → ℝ) : Prop :=
  ∃ (M : X.Modules) (a : LineBundleAtlas M) (k : ℕ) (_ : 0 < k) (𝔞 : FlagIdeal X),
    𝔞.IsGeneratedBy (isInvertible_of_atlas a) ∧ rationalPicardClass a = (k : ℚ) • ω ∧
      ∀ v, φ v = (k : ℝ)⁻¹ * 𝔞.phi v

/-- **Step R9**: the truncations `max(φ, c)`, `c ∈ ℚ`, of the rational GF functions `φ` of a
rational class `ω` with ample numerical class are Fubini–Study functions of `ω`. -/
theorem isFlagFS_truncation [IsIntegral X] {ω : RationalPicardSpace X}
    (hω : SGPT.NAPotential.BJ.NativePicard.numericalClass p ω ∈ NativeRealNumericalClasses.ampleCone p)
    (E : RationalGFPackage X) (hE : E.picardClass = ω) (c : ℚ) :
    IsFlagFS p ω fun v => (max (E.eval p v) ((c : ℝ) : EReal)).toReal := by
  subst hE
  obtain ⟨d, hd, 𝔞, h𝔞, hφ⟩ := exists_generated_flagIdeal_truncation p E hω c
  refine ⟨_, powerAtlas E.atlas (E.n * d), E.m * d, Nat.mul_pos E.data.denominator_pos hd, 𝔞,
    h𝔞, rationalPicardClass_power_eq_smul_picardClass E d, fun v => ?_⟩
  show (max (E.eval p v) ((c : ℝ) : EReal)).toReal = _
  rw [hφ v, EReal.toReal_coe]

end SGPT.NAPotential.ThinApprox.BJModel
