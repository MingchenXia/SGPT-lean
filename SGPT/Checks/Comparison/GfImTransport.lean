import SGPT.Checks.Comparison.GfImSections
import SGPT.Checks.Comparison.BJNativeLogNorm
import SGPT.Checks.Comparison.BJSectionPowers

/-!
# Rational GF packages of class `m⁻¹ [M]` as sections of a power of `M`

Infrastructure for `lma:gfinimage` (`chapter_NApotential.tex`, *The comparison theorem*). The book
writes `φ ∈ H^gf_ℚ(L^An)` as `m⁻¹ max_i (log |s_i| + λ_i)` with sections `s_i` of a power of `L`
itself. A rational GF package of the workspace (`RationalGFPackage`, the recalled
`def:BJpshmetric` data) consists of sections `s_i` of `A^{⊗ n_D}` for some line bundle `A` with
`(n_D / m_D) [A] = L` in `Pic(X) ⊗ ℚ`. For `L = m⁻¹ [M]`:

* `exists_tensorPower_iso`: there is `k > 0` with `A^{⊗ n_D m k} ≅ M^{⊗ m_D k}` (rational
  equality of Picard classes kills only torsion);
* `exists_sections_of_picardClass`: the images `t_i ∈ H⁰(X, M^{⊗ m_D k})` of the powers
  `s_i^{m k}` are nonzero and `v(t_i) = m k · v(s_i)` at every `v ∈ X^An` (the true model norms of
  global sections are invariant under module isomorphisms).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.NAPotential.BJ.GfIm

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory SGPT.Foundations.Schemes
open Scheme.Modules
open SGPT.NAPotential.Berkovich SGPT.NAPotential.Berkovich.BJSections
open SGPT.NAPotential.BJ SGPT.NAPotential.BJ.NativePicard SGPT.NAPotential.BJ.Printed
open SGPT.Foundations.Envelope SGPT.Foundations.Envelope.SchemeGlobalSectionModelNormIsometries
open SGPT.Foundations.Envelope.SchemeModuleIsoGlobalSections

attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

variable {X : Scheme.{0}}

/-- A rational GF package of class `m⁻¹ [M]`: some power of its line bundle is a power of `M`. -/
theorem exists_tensorPower_iso (D : RationalGFPackage X) {M : X.Modules} (b : LineBundleAtlas M)
    {m : ℕ} (hm : 0 < m) (hD : D.picardClass = (m : ℚ)⁻¹ • rationalPicardClass b) :
    ∃ k : ℕ, 0 < k ∧
      Nonempty (bundleTensorPower D.line (D.n * (m * k)) ≅ bundleTensorPower M (D.m * k)) := by
  have hmD : (D.m : ℚ) ≠ 0 := by exact_mod_cast D.data.denominator_pos.ne'
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hc := congrArg (fun z : RationalPicardSpace X => ((m : ℚ) * (D.m : ℚ)) • z) hD
  simp only [RationalGFPackage.picardClass, gfPicardClass, smul_smul] at hc
  have h1 : (m : ℚ) * (D.m : ℚ) * ((D.n : ℚ) / (D.m : ℚ)) = ((D.n * m : ℕ) : ℚ) := by
    push_cast
    field_simp
  have h2 : (m : ℚ) * (D.m : ℚ) * (m : ℚ)⁻¹ = ((D.m : ℕ) : ℚ) := by
    field_simp
  rw [h1, h2] at hc
  have hpow : rationalPicardClass (powerAtlas D.atlas (D.n * m)) =
      rationalPicardClass (powerAtlas b D.m) := by
    rw [rationalPicardClass_power, rationalPicardClass_power, ← Nat.cast_smul_eq_nsmul ℚ,
      ← Nat.cast_smul_eq_nsmul ℚ]
    exact hc
  obtain ⟨k, hk, hkclass⟩ := exists_pos_nsmul_eq_of_rationalize_eq hpow
  refine ⟨k, hk, toSkeleton_eq_toSkeleton_iff.mp ?_⟩
  have hp := congrArg Additive.toMul hkclass
  change (linePicardClass (powerAtlas D.atlas (D.n * m))) ^ k =
    (linePicardClass (powerAtlas b D.m)) ^ k at hp
  rw [linePicardClass_power, linePicardClass_power, ← pow_mul, ← pow_mul] at hp
  rw [← linePicardClass_val (powerAtlas D.atlas (D.n * (m * k))),
    ← linePicardClass_val (powerAtlas b (D.m * k)), linePicardClass_power, linePicardClass_power,
    ← mul_assoc, hp]

theorem negativeValue_injective : Function.Injective negativeValue := by
  intro a c h
  induction a using WithTop.recTopCoe with
  | top =>
    induction c using WithTop.recTopCoe with
    | top => rfl
    | coe s => exact absurd h.symm (EReal.coe_ne_bot _)
  | coe r =>
    induction c using WithTop.recTopCoe with
    | top => exact absurd h (EReal.coe_ne_bot _)
    | coe s =>
      have h' : ((-r : ℝ) : EReal) = ((-s : ℝ) : EReal) := h
      have := EReal.coe_injective h'
      rw [neg_inj] at this
      rw [this]

section Transport

variable (p : X ⟶ Spec (.of ℂ)) [IsProjective p] [IsIntegral X]

local instance gfImTransportProper : IsProper p :=
  (ProjectiveFactorizationRingIso.of_isProjective p).isProper

/-- **The sections of a rational GF package of class `m⁻¹ [M]`, as sections of a power of `M`**:
there are `k > 0` and nonzero `t_i ∈ H⁰(X, M^{⊗ m_D k})` with `v(t_i) = m k · v(s_i)` at every
point of `X^An`. -/
theorem exists_sections_of_picardClass (D : RationalGFPackage X) {M : X.Modules}
    (b : LineBundleAtlas M) {m : ℕ} (hm : 0 < m)
    (hD : D.picardClass = (m : ℚ)⁻¹ • rationalPicardClass b) :
    ∃ k : ℕ, 0 < k ∧ ∃ t : D.data.I → bundlePowerGlobalSections M (D.m * k), (∀ i, t i ≠ 0) ∧
      ∀ i (v : BerkovichPoint p), powerSectionValue b (D.m * k) (t i) v =
        (m * k) • powerSectionValue D.atlas D.n (D.data.sections i) v := by
  obtain ⟨k, hk, ⟨e⟩⟩ := exists_tensorPower_iso D b hm hD
  have hval : ∀ i (v : BerkovichPoint p), powerSectionValue b (D.m * k)
      (moduleIsoTopEquiv e (tensorPowerSection D.atlas D.n (D.data.sections i) (m * k))) v =
        (m * k) • powerSectionValue D.atlas D.n (D.data.sections i) v := by
    intro i v
    have h1 := nativeGlobalSectionLogNorm_eq_source p b (D.m * k)
      (moduleIsoTopEquiv e (tensorPowerSection D.atlas D.n (D.data.sections i) (m * k))) v
    have h2 := nativeGlobalSectionLogNorm_eq_source p D.atlas (D.n * (m * k))
      (tensorPowerSection D.atlas D.n (D.data.sections i) (m * k)) v
    have h3 := globalSectionNorm_moduleIso Valuation.one_apply_le_one (pointEquiv p v)
      (isInvertible_of_atlas (powerAtlas D.atlas (D.n * (m * k))))
      (isInvertible_of_atlas (powerAtlas b (D.m * k))) e
      (tensorPowerSection D.atlas D.n (D.data.sections i) (m * k))
    have h : sectionLogNorm D.atlas (D.n * (m * k))
        (tensorPowerSection D.atlas D.n (D.data.sections i) (m * k)) v =
        sectionLogNorm b (D.m * k)
          (moduleIsoTopEquiv e (tensorPowerSection D.atlas D.n (D.data.sections i) (m * k))) v := by
      rw [← h2, h3, h1]
    have h4 := negativeValue_injective h
    rw [← h4]
    exact tensorPowerSection_value D.atlas D.n (D.data.sections i) (m * k) v
  refine ⟨k, hk, fun i => moduleIsoTopEquiv e
    (tensorPowerSection D.atlas D.n (D.data.sections i) (m * k)), fun i hti => ?_, hval⟩
  have h := hval i (BerkovichPoint.trivial p)
  simp only at hti
  rw [hti, powerSectionValue_zero, powerSectionValue_trivial D.atlas D.n _
    (D.data.sections_ne_zero i), smul_zero] at h
  exact WithTop.top_ne_zero h

end Transport

end SGPT.NAPotential.BJ.GfIm
