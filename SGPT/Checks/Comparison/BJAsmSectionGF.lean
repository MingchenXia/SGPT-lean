import SGPT.Checks.Comparison.BJModelSectionIdeal
import SGPT.Checks.Comparison.BJCompareGFSequences
import SGPT.Foundations.Schemes.LineSectionZeroSubscheme
import SGPT.Okounkov.AlgebraicBodyOperations

/-!
# Generically finite Fubini–Study functions from finite families of sections

Infrastructure for `lma:varphian` (`chapter_NApotential.tex`, *The algebraic setting*). The book's
proof writes `v(𝓘(kφ)) = min_i v(s_i)` for finitely many global sections `s_i` generating
`H^b ⊗ L^k ⊗ 𝓘(kφ)`, and concludes that `v ↦ -k⁻¹ v(𝓘(kφ))` is a rational generically finite
Fubini–Study function. Here:

* `idealVal_sectionZeroIdealSheaf`: for a global section `σ` of `L^{⊗ j}`, the value of a
  semi-valuation on the zero ideal sheaf of `σ` (Bing–Wang's `sectionZeroIdealSheaf`, the ideal
  sheaf used by the algebraic models of multiplier ideals) is the value `v(σ)` of the section.
* `rationalPicardClass_pairwiseTensor`: `[L ⊗ N] = [L] + [N]` in `Pic(X) ⊗ ℚ`.
* `exists_package_of_sections`: for finitely many global sections `σ_i` of `M^{⊗ k}` and `N ≥ 1`,
  `v ↦ -N⁻¹ v(∑_i 𝔟_{σ_i})` is the function of a rational GF package of class `(k/N) [M]`
  (as soon as the ideal sum is not the zero ideal at one point).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.BJ.Assembly

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Scheme.Modules SGPT.Foundations.Schemes
open scoped ENNReal
open SGPT.NAPotential.Berkovich SGPT.NAPotential.Berkovich.BJSections
open SGPT.NAPotential.BJ SGPT.NAPotential.BJ.NativePicard SGPT.NAPotential.BJ.Printed
open SGPT.NAPotential.BJModel
open SGPT.Foundations.Envelope

attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

variable {X : Scheme.{0}}

/-! ### Values on zero ideals of sections -/

section Values

variable {p : X ⟶ Spec (.of ℂ)} [IsProper p]

/-- **`v(𝔟_σ) = v(σ)`** for the zero ideal sheaf `𝔟_σ = sectionZeroIdealSheaf σ` (the image of
`σ : L^{-j} → 𝒪_X`) of a global section `σ` of `L^{⊗ j}`. -/
theorem idealVal_sectionZeroIdealSheaf {L : X.Modules} (a : LineBundleAtlas L) (j : ℕ)
    (σ : bundlePowerGlobalSections L j) (v : BerkovichPoint p) :
    v.idealVal (sectionZeroIdealSheaf (a.tensorPower j) σ) =
      toENNReal (powerSectionValue a j σ v) := by
  let i := centerIndex a v
  obtain ⟨W, hW, hcW, hWU⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (U := a.opens i) (x := v.center) (center_mem_open a v)
  let U : X.affineOpens := ⟨W, hW⟩
  let e : SGPT.Foundations.Schemes.LocalBundleFrame L W :=
    SGPT.Support.ModularCurves.SheafOfModules.restrictOverTrivialization X.ringCatSheaf L (a.opens i)
      (a.frame i) (Over.mk (homOfLE hWU))
  have hideal : (sectionZeroIdealSheaf (a.tensorPower j) σ).ideal U =
      Ideal.span {(e.tensorPower j).coefficients (𝟙 W)
        ((bundleTensorPower L j).presheaf.map W.leTop.op σ)} :=
    sectionZeroIdeal_eq_span_frame σ (e.tensorPower j) (𝟙 W)
  rw [idealVal_eq_iInf_of_ideal_eq_span v _ U hcW hideal,
    powerSectionValue_eq_local a j σ v e hcW]
  simp only [Set.mem_singleton_iff, iInf_iInf_eq_left]
  rfl

/-- `-(a : EReal)` for `a = v(σ) ≥ 0` is the logarithmic norm `log|σ|(v)`. -/
theorem negativeValue_eq_neg_toENNReal {x : WithTop ℝ} (hx : 0 ≤ x) :
    negativeValue x = -((toENNReal x : ℝ≥0∞) : EReal) := by
  induction x using WithTop.recTopCoe with
  | top => simp [negativeValue, toENNReal]
  | coe r =>
    have hr : 0 ≤ r := by exact_mod_cast hx
    change ((-r : ℝ) : EReal) = -((ENNReal.ofReal r : ℝ≥0∞) : EReal)
    rw [EReal.coe_ennreal_ofReal, max_eq_left hr, EReal.coe_neg]

/-- `N⁻¹ · (-(c : EReal)) = -((c / N : ℝ≥0∞) : EReal)`. -/
theorem inv_mul_neg_coe_ennreal {N : ℕ} (hN : 0 < N) (c : ℝ≥0∞) :
    (((1 / (N : ℝ)) : ℝ) : EReal) * -((c : ℝ≥0∞) : EReal) = -(((c / N : ℝ≥0∞)) : EReal) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  induction c using ENNReal.recTopCoe with
  | top =>
    rw [ENNReal.top_div_of_ne_top (ENNReal.natCast_ne_top N), EReal.coe_ennreal_top,
      EReal.neg_top, EReal.mul_bot_of_pos (by exact_mod_cast one_div_pos.mpr hNR)]
  | coe r =>
    have hc : ((r : ℝ≥0∞) / N : ℝ≥0∞) = ENNReal.ofReal ((r : ℝ) / N) := by
      rw [ENNReal.ofReal_div_of_pos hNR, ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_natCast]
    rw [hc, EReal.coe_ennreal_ofReal, max_eq_left (div_nonneg r.coe_nonneg hNR.le),
      show ((r : ℝ≥0∞) : EReal) = ((r : ℝ) : EReal) from rfl, ← EReal.coe_neg, ← EReal.coe_mul,
      ← EReal.coe_neg]
    congr 1
    ring

end Values

/-! ### Rational Picard class of a tensor product -/

/-- `[L ⊗ N] = [L] + [N]` in `Pic(X) ⊗ ℚ`. -/
theorem rationalPicardClass_pairwiseTensor {L N : X.Modules} (a : LineBundleAtlas L)
    (b : LineBundleAtlas N) :
    rationalPicardClass (SGPT.Okounkov.pairwiseTensorAtlas a b) =
      rationalPicardClass a + rationalPicardClass b := by
  have h : linePicardClass (SGPT.Okounkov.pairwiseTensorAtlas a b) =
      linePicardClass a * linePicardClass b := by
    apply Units.ext
    rw [linePicardClass_val, Units.val_mul, linePicardClass_val, linePicardClass_val]
    have he : SGPT.Foundations.Schemes.bundleTensor L N = Scheme.Modules.tensorObj L N := rfl
    rw [he, toSkeleton_tensorObj_eq]
  unfold rationalPicardClass
  rw [h, ofMul_mul, map_add]

/-! ### The package of a finite family of sections -/

section Package

variable (p : X ⟶ Spec (.of ℂ)) [IsProjective p]

local instance : IsProper p := (ProjectiveFactorizationRingIso.of_isProjective p).isProper

/-- **Finite families of sections give rational GF functions.** For finitely many global
sections `σ_i` of `M^{⊗ k}` (`k ≥ 1`) and `N ≥ 1`, the function
`v ↦ -N⁻¹ v(∑_i 𝔟_{σ_i}) = N⁻¹ max_i log|σ_i|(v)` is the function of a rational GF package of
rational Picard class `(k/N) [M]`, provided `∑_i 𝔟_{σ_i}` is not the zero ideal at one point
`v₀` (equivalently, some `σ_i` is non-zero). -/
theorem exists_package_of_sections {M : X.Modules} (b : LineBundleAtlas M) {k N : ℕ}
    (hk : 0 < k) (hN : 0 < N) {ι : Type} [Fintype ι] (σ : ι → bundlePowerGlobalSections M k)
    (v₀ : BerkovichPoint p)
    (h₀ : v₀.idealVal (⨆ i, sectionZeroIdealSheaf (b.tensorPower k) (σ i)) ≠ ⊤) :
    ∃ D : RationalGFPackage X, D.picardClass = ((k : ℚ) / (N : ℚ)) • rationalPicardClass b ∧
      ∀ v : BerkovichPoint p, D.eval p v =
        -(((v.idealVal (⨆ i, sectionZeroIdealSheaf (b.tensorPower k) (σ i)) / N : ℝ≥0∞)) :
          EReal) := by
  classical
  let ι' := {i : ι // σ i ≠ 0}
  have hval : ∀ (v : BerkovichPoint p),
      v.idealVal (⨆ i, sectionZeroIdealSheaf (b.tensorPower k) (σ i)) =
        ⨅ i : ι', toENNReal (powerSectionValue b k (σ i.1) v) := by
    intro v
    rw [idealVal_iSup]
    apply le_antisymm
    · refine le_iInf fun i => ?_
      rw [← idealVal_sectionZeroIdealSheaf b k (σ i.1) v]
      exact iInf_le (fun j : ι => v.idealVal (sectionZeroIdealSheaf (b.tensorPower k) (σ j))) i.1
    · refine le_iInf fun i => ?_
      rw [idealVal_sectionZeroIdealSheaf b k (σ i) v]
      by_cases hi : σ i = 0
      · rw [hi, powerSectionValue_zero]
        exact le_top
      · exact iInf_le (fun j : ι' => toENNReal (powerSectionValue b k (σ j.1) v)) ⟨i, hi⟩
  have hne : Nonempty ι' := by
    by_contra hcon
    rw [not_nonempty_iff] at hcon
    apply h₀
    rw [hval]
    exact iInf_of_empty _
  let D : RationalGFData M k N :=
    { I := ι'
      fintype := Fintype.ofFinite ι'
      nonempty := hne
      sections := fun i => σ i.1
      sections_ne_zero := fun i => i.2
      weight := fun _ => 0
      power_pos := hk
      denominator_pos := hN }
  refine ⟨⟨M, b, k, N, D⟩, rfl, fun v => ?_⟩
  change rationalGFFunction b D v = _
  unfold rationalGFFunction finiteMaximum
  rw [hval v]
  obtain ⟨i₀, hi₀⟩ := exists_eq_ciInf_of_finite (f := fun i : ι' =>
    toENNReal (powerSectionValue b k (σ i.1) v))
  have hsup : (⨆ i : D.I, sectionLogNorm b k (D.sections i) v + (((D.weight i : ℚ) : ℝ) : EReal)) =
      -((toENNReal (powerSectionValue b k (σ i₀.1) v) : ℝ≥0∞) : EReal) := by
    have hterm : ∀ i : ι', sectionLogNorm b k (D.sections i) v +
        (((D.weight i : ℚ) : ℝ) : EReal) =
          -((toENNReal (powerSectionValue b k (σ i.1) v) : ℝ≥0∞) : EReal) := by
      intro i
      change negativeValue (powerSectionValue b k (σ i.1) v) + (((0 : ℚ) : ℝ) : EReal) = _
      rw [Rat.cast_zero, EReal.coe_zero, add_zero,
        negativeValue_eq_neg_toENNReal (powerSectionValue_nonneg b k _ v)]
    apply le_antisymm
    · refine iSup_le fun i => ?_
      rw [hterm i, EReal.neg_le_neg_iff, EReal.coe_ennreal_le_coe_ennreal_iff]
      rw [hi₀]
      exact ciInf_le (Finite.bddBelow_range _) i
    · exact (hterm i₀).symm.le.trans (le_iSup (fun i : D.I => sectionLogNorm b k (D.sections i) v +
        (((D.weight i : ℚ) : ℝ) : EReal)) i₀)
  rw [hsup, ← hi₀]
  exact inv_mul_neg_coe_ennreal hN _

end Package

end SGPT.NAPotential.BJ.Assembly
