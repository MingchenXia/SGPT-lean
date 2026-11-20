import SGPT.Checks.Comparison.BJAsmSectionGF

/-!
# Weighted maxima of section families as rational GF functions

Infrastructure for the existence clause of `cor:testcurvegivepshme` (`chapter_NApotential.tex`,
*The algebraic setting*). The upper grid maxima of the proof are finite maxima
`max_g (-N⁻¹ v(𝔞_g) + λ_g)` of translated functions `-N⁻¹ v(𝔞_g)`, where each ideal
`𝔞_g = ∑_i 𝔟_{σ_{g,i}}` is the sum of the zero ideals of finitely many global sections of the same
power `M^{⊗ k}` and `λ_g ∈ ℚ`. Writing `v(𝔞_g) = min_i v(σ_{g,i})`, this is
`N⁻¹ max_{g,i} (log|σ_{g,i}|(v) + N λ_g)`, a rational generically finite Fubini–Study function
of class `(k/N) [M]` (`def:BJpshmetric`, the set `H^gf_ℚ`).

## Main results

* `idealVal_iSup_sectionZeroIdealSheaf`: `v(∑_i 𝔟_{σ_i}) = min_i v(σ_i)`.
* `exists_package_of_weighted_families`: the weighted maximum above is the function of a rational
  GF package of class `(k/N) [M]`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.BJ.Exist

open AlgebraicGeometry CategoryTheory
open SGPT.Foundations.Schemes
open scoped ENNReal
open SGPT.NAPotential.Berkovich SGPT.NAPotential.Berkovich.BJSections
open SGPT.NAPotential.BJ SGPT.NAPotential.BJ.NativePicard SGPT.NAPotential.BJ.Printed
open SGPT.NAPotential.BJ.Assembly SGPT.NAPotential.BJModel
open SGPT.Foundations.Envelope

variable {X : Scheme.{0}}

/-! ### Elementary `EReal` identities -/

/-- `N⁻¹ (-(c) + N r) = -(c/N) + r`. -/
theorem inv_mul_neg_add_mul {N : ℕ} (hN : 0 < N) (c : ℝ≥0∞) (r : ℚ) :
    (((1 / (N : ℝ)) : ℝ) : EReal) * (-((c : ℝ≥0∞) : EReal) + ((((N : ℚ) * r : ℚ) : ℝ) : EReal)) =
      -(((c / N : ℝ≥0∞)) : EReal) + ((r : ℝ) : EReal) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  induction c using ENNReal.recTopCoe with
  | top =>
    rw [ENNReal.top_div_of_ne_top (ENNReal.natCast_ne_top N), EReal.coe_ennreal_top,
      EReal.neg_top, EReal.bot_add, EReal.bot_add,
      EReal.mul_bot_of_pos (by exact_mod_cast one_div_pos.mpr hNR)]
  | coe r' =>
    have hc : ((r' : ℝ≥0∞) / N : ℝ≥0∞) = ENNReal.ofReal ((r' : ℝ) / N) := by
      rw [ENNReal.ofReal_div_of_pos hNR, ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_natCast]
    rw [hc, EReal.coe_ennreal_ofReal, max_eq_left (div_nonneg r'.coe_nonneg hNR.le),
      show ((r' : ℝ≥0∞) : EReal) = ((r' : ℝ) : EReal) from rfl, ← EReal.coe_neg, ← EReal.coe_add,
      ← EReal.coe_mul, ← EReal.coe_neg, ← EReal.coe_add]
    congr 1
    push_cast
    field_simp

/-- Multiplication by a nonnegative real commutes with finite nonempty suprema in `EReal`. -/
theorem coe_mul_iSup_of_finite {ι : Type*} [Finite ι] [Nonempty ι] {c : ℝ} (hc : 0 ≤ c)
    (a : ι → EReal) : ((c : ℝ) : EReal) * (⨆ i, a i) = ⨆ i, ((c : ℝ) : EReal) * a i := by
  obtain ⟨i₀, hi₀⟩ := exists_eq_ciSup_of_finite (f := a)
  apply le_antisymm
  · rw [← hi₀]
    exact le_iSup (fun i => ((c : ℝ) : EReal) * a i) i₀
  · refine iSup_le fun i => ?_
    exact mul_le_mul_of_nonneg_left (le_iSup a i) (EReal.coe_nonneg.mpr hc)

/-- `max_i (-(c_i/N) + w) = -(min_i c_i / N) + w` over a finite index (both sides are `-∞` for the
empty index). -/
theorem iSup_neg_div_add {ι : Type*} [Finite ι] (c : ι → ℝ≥0∞) (N : ℕ) (w : ℝ) :
    ⨆ i, (-(((c i / N : ℝ≥0∞)) : EReal) + (w : EReal)) =
      -((((⨅ i, c i) / N : ℝ≥0∞)) : EReal) + (w : EReal) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · rw [iSup_of_empty, iInf_of_empty, ENNReal.top_div_of_ne_top (ENNReal.natCast_ne_top N),
      EReal.coe_ennreal_top, EReal.neg_top, EReal.bot_add]
  · obtain ⟨i₀, hi₀⟩ := exists_eq_ciInf_of_finite (f := c)
    apply le_antisymm
    · refine iSup_le fun i => add_le_add ?_ le_rfl
      rw [EReal.neg_le_neg_iff, EReal.coe_ennreal_le_coe_ennreal_iff]
      exact ENNReal.div_le_div_right (iInf_le c i) _
    · rw [← hi₀]
      exact le_iSup (fun i => (-(((c i / N : ℝ≥0∞)) : EReal) + (w : EReal))) i₀

/-! ### Ideal values of sums of zero ideals -/

section Values

variable {p : X ⟶ Spec (.of ℂ)} [IsProper p]

/-- `v(∑_i 𝔟_{σ_i}) = min_i v(σ_i)` (zero sections have value `+∞`). -/
theorem idealVal_iSup_sectionZeroIdealSheaf {M : X.Modules} (b : LineBundleAtlas M) (k : ℕ)
    {ι : Type} (σ : ι → bundlePowerGlobalSections M k) (v : BerkovichPoint p) :
    v.idealVal (⨆ i, sectionZeroIdealSheaf (b.tensorPower k) (σ i)) =
      ⨅ i, toENNReal (powerSectionValue b k (σ i) v) := by
  rw [idealVal_iSup]
  exact iInf_congr fun i => idealVal_sectionZeroIdealSheaf b k (σ i) v

end Values

/-! ### The package -/

section Package

variable (p : X ⟶ Spec (.of ℂ)) [IsProjective p]

local instance : IsProper p := (ProjectiveFactorizationRingIso.of_isProjective p).isProper

/-- **Weighted maxima of section families are rational GF functions.** Let `σ_{g,i}`
(`g ∈ G`, `i ∈ ι_g`, finite) be global sections of `M^{⊗ k}` (`k ≥ 1`), `N ≥ 1` and `w_g ∈ ℚ`.
If the ideal `∑_i 𝔟_{σ_{g₀,i}}` of one family is not the zero ideal at one point `v₀`, then
`v ↦ max_g (-N⁻¹ v(∑_i 𝔟_{σ_{g,i}}) + w_g)` is the function of a rational GF package of class
`(k/N) [M]`. -/
theorem exists_package_of_weighted_families {M : X.Modules} (b : LineBundleAtlas M) {k N : ℕ}
    (hk : 0 < k) (hN : 0 < N) {G : Type} [Fintype G] {ι : G → Type} [∀ g, Fintype (ι g)]
    (σ : ∀ g, ι g → bundlePowerGlobalSections M k) (w : G → ℚ) (v₀ : BerkovichPoint p) (g₀ : G)
    (h₀ : v₀.idealVal (⨆ i, sectionZeroIdealSheaf (b.tensorPower k) (σ g₀ i)) ≠ ⊤) :
    ∃ D : RationalGFPackage X, D.picardClass = ((k : ℚ) / (N : ℚ)) • rationalPicardClass b ∧
      ∀ v : BerkovichPoint p, D.eval p v =
        ⨆ g, (-(((v.idealVal (⨆ i, sectionZeroIdealSheaf (b.tensorPower k) (σ g i)) / N :
          ℝ≥0∞)) : EReal) + ((w g : ℝ) : EReal)) := by
  classical
  let ι' : Type := Σ g, {i : ι g // σ g i ≠ 0}
  have hne : Nonempty ι' := by
    by_contra hcon
    apply h₀
    rw [idealVal_iSup_sectionZeroIdealSheaf]
    refine eq_top_iff.mpr (le_iInf fun i => ?_)
    by_cases hi : σ g₀ i = 0
    · rw [hi, powerSectionValue_zero, toENNReal_top]
    · exact absurd ⟨⟨g₀, ⟨i, hi⟩⟩⟩ hcon
  let D : RationalGFData M k N :=
    { I := ι'
      fintype := inferInstance
      nonempty := hne
      sections := fun x => σ x.1 x.2.1
      sections_ne_zero := fun x => x.2.2
      weight := fun x => (N : ℚ) * w x.1
      power_pos := hk
      denominator_pos := hN }
  refine ⟨⟨M, b, k, N, D⟩, rfl, fun v => ?_⟩
  change rationalGFFunction b D v = _
  -- termwise: `N⁻¹ (log|σ| + N w) = -(v(σ)/N) + w`
  have hterm : ∀ x : ι', (((1 / (N : ℝ)) : ℝ) : EReal) *
      (sectionLogNorm b k (D.sections x) v + (((D.weight x : ℚ) : ℝ) : EReal)) =
        -(((toENNReal (powerSectionValue b k (σ x.1 x.2.1) v) / N : ℝ≥0∞)) : EReal) +
          ((w x.1 : ℝ) : EReal) := by
    intro x
    change (((1 / (N : ℝ)) : ℝ) : EReal) *
      (negativeValue (powerSectionValue b k (σ x.1 x.2.1) v) +
        ((((N : ℚ) * w x.1 : ℚ) : ℝ) : EReal)) = _
    rw [negativeValue_eq_neg_toENNReal (powerSectionValue_nonneg b k _ v)]
    exact inv_mul_neg_add_mul hN _ _
  unfold rationalGFFunction finiteMaximum
  rw [coe_mul_iSup_of_finite (one_div_nonneg.mpr (Nat.cast_nonneg N))]
  simp only [hterm]
  change (⨆ x : (Σ g, {i : ι g // σ g i ≠ 0}), (-(((toENNReal
    (powerSectionValue b k (σ x.1 x.2.1) v) / N : ℝ≥0∞)) : EReal) + ((w x.1 : ℝ) : EReal))) = _
  rw [iSup_sigma]
  refine iSup_congr fun g => ?_
  rw [idealVal_iSup_sectionZeroIdealSheaf, ← iSup_neg_div_add]
  apply le_antisymm
  · exact iSup_le fun i => le_iSup (fun i : ι g => (-(((toENNReal
      (powerSectionValue b k (σ g i) v) / N : ℝ≥0∞)) : EReal) + ((w g : ℝ) : EReal))) i.1
  · refine iSup_le fun i => ?_
    by_cases hi : σ g i = 0
    · rw [hi, powerSectionValue_zero, toENNReal_top,
        ENNReal.top_div_of_ne_top (ENNReal.natCast_ne_top N), EReal.coe_ennreal_top,
        EReal.neg_top, EReal.bot_add]
      exact bot_le
    · exact le_iSup (fun i : {i : ι g // σ g i ≠ 0} => (-(((toENNReal
        (powerSectionValue b k (σ g i.1) v) / N : ℝ≥0∞)) : EReal) + ((w g : ℝ) : EReal)))
        ⟨i, hi⟩

end Package

end SGPT.NAPotential.BJ.Exist
