import SGPT.IGood.LogVolume
import SGPT.PSH.SourceIGoodOperations
import SGPT.PSH.SourceAnalyticIGood
import SGPT.NPP.DimensionZero
import SGPT.Foundations.Analysis.Pending.EndpointMixedMassConvexCombination

/-!
# Log-concavity of non-pluripolar masses: `𝓘`-good potentials

Source `thm:logconc` (chapter on non-pluripolar products). Its two assertions are

1. for `φ₀, φ₁ ∈ PSH(X, θ)` the map `[0, 1] ∋ t ↦ log ∫_X θ_{tφ₁ + (1-t)φ₀}ⁿ` is concave;
2. for closed positive `(1,1)`-currents `T₁, …, Tₙ`,
   `∫_X ⟨T₁ ∧ ⋯ ∧ Tₙ⟩ ≥ ∏ᵢ (∫_X ⟨Tᵢⁿ⟩)^{1/n}`.

This file proves

* the second assertion when every potential `uᵢ` of `Tᵢ = θᵢ + ddᶜuᵢ` is `𝓘`-good
  (`def:Igoodpot`, `sourceIGood`): `prod_sourceMass_rpow_le_sourceMixedMass_of_iGood`.
  For `𝓘`-good potentials the (mixed) masses are the (mixed) volumes, so this is
  `prop:logvol` (`SGPT.IGood.LogVolume`). This class contains all potentials with analytic
  singularities in the chartwise sense of SGPT (`ex:analyIgood`, `sourceAnalytic_iGood`;
  `prod_sourceMass_rpow_le_sourceMixedMass_of_hasAnalyticType`), the `𝓘`-model potentials of
  positive mass and the potentials of full mass;
* the first assertion when `φ₀` and `φ₁` are `𝓘`-good (`𝓘`-goodness is stable under convex
  combinations, `prop:Igoodlinear`), in the form `m(t₀)^{1-s} m(t₁)^s ≤ m((1-s)t₀ + st₁)` for
  `m(t) = ∫_X θ_{tφ₁+(1-t)φ₀}ⁿ` (this is the concavity of `log m` with `log 0 = -∞`), together with
  the concavity of `m^{1/n}` and, for positive endpoint masses, the concavity of `log m`;
* the first assertion when `φ₀` and `φ₁` are bounded (then `m` is constant);
* both assertions in full generality in dimension `0` (`rmk:npp:L275`: all masses are `1`).

The general case (arbitrary currents of positive mass in dimension `n ≥ 1`) is not covered: FPT's
proof needs Monge–Ampère equations with prescribed singularities and Dinew's mixed inequality for
non-pluripolar products against a smooth measure.

The proof of the first assertion from the second is FPT's (`thm:ordinary-mixed-mass-geometric-mean`):
expand all masses multilinearly into the mixed masses of the endpoints
(TN `globalMixedMass_sumPot_expand_toReal`) and apply the second assertion to the tuples built
from `t₀` and `t₁`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal

universe u

namespace SGPT.NPP.LogConcavity

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination
open SGPT.PSH.VariableComplexAtlas

/-! ### The second assertion for `𝓘`-good potentials -/

section IGood

variable {q : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel (q + 1)) M]
  [IsComplexManifold (q + 1) M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  [ConnectedSpace M]

/-- **`thm:logconc`, mixed-mass inequality, `𝓘`-good potentials.** On a compact connected Kähler
manifold of dimension `n = q + 1`, for closed real `(1,1)`-forms `θᵢ` and `𝓘`-good `θᵢ`-psh
functions `uᵢ`,
`∏ᵢ (∫ ⟨(θᵢ + ddᶜuᵢ)ⁿ⟩)^{1/n} ≤ ∫ ⟨(θ₁ + ddᶜu₁) ∧ ⋯ ∧ (θₙ + ddᶜuₙ)⟩`
for the source non-pluripolar masses (all finite, read as real numbers). -/
theorem prod_sourceMass_rpow_le_sourceMixedMass_of_iGood (ω : KahlerBackground (q + 1) M)
    (θ : Fin (q + 1) → AtlasClosedRealOneOneForm (ofFixedModel (q + 1) M))
    (u : Fin (q + 1) → M → EReal) (hu : ∀ i, (ofFixedModel (q + 1) M).IsThetaPSH (θ i) (u i))
    (hg : ∀ i, sourceIGood (n := q + 1) (u i)) :
    ∏ i, ((sourceMixedNonPluripolarMass (fun _ => θ i) (fun _ => u i) (fun _ => hu i)).toReal) ^
        (((q + 1 : ℕ) : ℝ)⁻¹) ≤
      (sourceMixedNonPluripolarMass θ u hu).toReal := by
  by_cases hpos : ∀ i, 0 < sourcePotentialNonPluripolarMeasure (θ i) (u i) (hu i) univ
  · have hgw : ∀ i, sourceIGoodWith (θ i) (u i) (hu i) := fun i =>
      (sourceIGood_iff_with_positive_background ω (hu i) (hpos i)).mp (hg i)
    rw [← SGPT.IGood.LogVolume.sourceGeneralMixedIVolume_eq_mass_of_iGoodWith ω θ u hu hgw]
    refine le_of_eq_of_le ?_
      (SGPT.IGood.LogVolume.prod_sourceIVolume_rpow_le_sourceGeneralMixedIVolume ω θ u hu)
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [sourceMixedNonPluripolarMass_diagonal,
      SGPT.IGood.LogVolume.sourceIVolume_eq_mass_of_iGoodWith ω (hu i) (hgw i)]
  · push Not at hpos
    obtain ⟨i, hi⟩ := hpos
    have h0 : sourcePotentialNonPluripolarMeasure (θ i) (u i) (hu i) univ = 0 :=
      le_antisymm hi zero_le
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by
      rw [sourceMixedNonPluripolarMass_diagonal, h0, ENNReal.toReal_zero,
        Real.zero_rpow (by positivity)])]
    exact ENNReal.toReal_nonneg

/-- **`thm:logconc`, mixed-mass inequality, analytic singularities (chartwise).** The second
assertion for potentials `uᵢ` with analytic singularities in the chartwise sense of SGPT
(`HasManifoldAnalyticSingularityType`: in every chart `c log ∑|gⱼ|² + O(1)` with `c ∈ ℚ_{>0}`);
these are `𝓘`-good (`ex:analyIgood`). This contains the TN-global analytic case
`prod_sourceMass_rpow_le_sourceMixedMass_of_analytic`. -/
theorem prod_sourceMass_rpow_le_sourceMixedMass_of_hasAnalyticType
    (ω : KahlerBackground (q + 1) M)
    (θ : Fin (q + 1) → AtlasClosedRealOneOneForm (ofFixedModel (q + 1) M))
    (u : Fin (q + 1) → M → EReal) (hu : ∀ i, (ofFixedModel (q + 1) M).IsThetaPSH (θ i) (u i))
    (hA : ∀ i, HasManifoldAnalyticSingularityType (n := q + 1) (u i)) :
    ∏ i, ((sourceMixedNonPluripolarMass (fun _ => θ i) (fun _ => u i) (fun _ => hu i)).toReal) ^
        (((q + 1 : ℕ) : ℝ)⁻¹) ≤
      (sourceMixedNonPluripolarMass θ u hu).toReal :=
  prod_sourceMass_rpow_le_sourceMixedMass_of_iGood ω θ u hu fun i =>
    sourceAnalytic_iGood ω (u i) ⟨θ i, hu i⟩ (hA i)

end IGood

/-! ### Convex combinations -/

section Convex

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
theorem convexComb_zero (u v : M → EReal) : convexComb 0 u v = v := by
  funext x
  simp only [convexComb, EReal.coe_zero, zero_mul, sub_zero, EReal.coe_one, one_mul, zero_add]

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
theorem convexComb_one (u v : M → EReal) : convexComb 1 u v = u := by
  funext x
  simp only [convexComb, EReal.coe_one, one_mul, sub_self, EReal.coe_zero, zero_mul, add_zero]

/-- Convex combinations of source `θ`-psh functions are `θ`-psh. -/
theorem isThetaPSH_convexComb {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    {u v : M → EReal} (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hv : (ofFixedModel n M).IsThetaPSH θ v) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    (ofFixedModel n M).IsThetaPSH θ (convexComb t u v) :=
  (isThetaPSH_iff_nativeThetaPotential _ _).mpr
    (EndpointMixedMassConvexCombination.isThetaPshPotential_convexComb_closed
      ((isThetaPSH_iff_nativeThetaPotential _ _).mp hu)
      ((isThetaPSH_iff_nativeThetaPotential _ _).mp hv) h0 h1)

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- Convex combinations of `𝓘`-good potentials are `𝓘`-good (`prop:Igoodlinear`). -/
theorem sourceIGood_convexComb [ConnectedSpace M] (ω : KahlerBackground n M) {u v : M → EReal}
    (hu : sourceIGood (n := n) u) (hv : sourceIGood (n := n) v) {t : ℝ} (h0 : 0 ≤ t)
    (h1 : t ≤ 1) : sourceIGood (n := n) (convexComb t u v) := by
  rcases h0.eq_or_lt with rfl | h0
  · rw [convexComb_zero]
    exact hv
  rcases h1.eq_or_lt with rfl | h1
  · rw [convexComb_one]
    exact hu
  exact sourceIGood_add ω (sourceIGood_pos_mul hu h0) (sourceIGood_pos_mul hv (sub_pos.mpr h1))

/-- **Multilinear expansion of mixed masses of convex combinations** (slotwise coefficients):
`∫⟨⋀ᵢ (θ + ddᶜ(tᵢu + (1-tᵢ)p))⟩ = ∑_σ ∏ᵢ cᵢ(σᵢ) ∫⟨⋀ᵢ (θ + ddᶜ(σᵢ ? u : p))⟩` with
`cᵢ(true) = tᵢ`, `cᵢ(false) = 1 - tᵢ`. -/
theorem globalMixedMass_convexComb_eq_sum (ω : KahlerBackground n M)
    {θ : ClosedRealOneOneForm n M} {u p : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (hp : IsThetaPshPotential θ.val p)
    (t : Fin n → ℝ) (ht0 : ∀ i, 0 ≤ t i) (ht1 : ∀ i, t i ≤ 1) :
    (MixedMass.globalMixedMass (fun _ : Fin n => θ) (fun i => convexComb (t i) u p)
      (fun i => (EndpointMixedMassConvexCombination.isThetaPshPotential_convexComb_closed hu hp
        (ht0 i) (ht1 i)).1)).toReal =
      ∑ σ : Fin n → Bool, (∏ i, if σ i then t i else 1 - t i) *
        (MixedMass.globalMixedMass (fun _ : Fin n => θ) (fun i => if σ i then u else p)
          (fun i => by split_ifs <;> first | exact hu.1 | exact hp.1)).toReal := by
  classical
  let pots : Bool → M → EReal := fun b => if b then u else p
  let c : Fin n → Bool → ℝ := fun i b => if b then t i else 1 - t i
  have hpots (b : Bool) : IsThetaPshPotential θ.val (pots b) := by
    cases b
    · exact hp
    · exact hu
  have hc : ∀ i b, 0 ≤ c i b := by
    intro i b
    cases b
    · exact sub_nonneg.mpr (ht1 i)
    · exact ht0 i
  have hF : (fun i : Fin n => GlobalMultilinearExpansion.sumForm Finset.univ (c i)
      (fun _ : Bool => θ)) = fun _ : Fin n => θ := by
    funext i
    simp only [GlobalMultilinearExpansion.sumForm, Fintype.sum_bool, c, if_true,
      Bool.false_eq_true, if_false]
    rw [← add_smul, show t i + (1 - t i) = 1 by ring, one_smul]
  have hQ : (fun i => GlobalMultilinearExpansion.sumPot Finset.univ (c i) pots) =
      fun i => convexComb (t i) u p := by
    funext i x
    simp only [GlobalMultilinearExpansion.sumPot, Fintype.sum_bool, c, pots, if_true,
      Bool.false_eq_true, if_false, convexComb]
  have h := MixedMassProductCalculus.globalMixedMass_sumPot_expand_toReal ω hc hpots
  unfold MixedMass.globalMixedMass at h ⊢
  rw [GlobalDiagonalScaling.globalMixedMeasure_congr hF hQ _
    (fun i => (EndpointMixedMassConvexCombination.isThetaPshPotential_convexComb_closed hu hp
      (ht0 i) (ht1 i)).1)] at h
  rw [h]

/-- The function `m(t) = ∫_X θ_{tφ₁+(1-t)φ₀}ⁿ` of the first assertion of `thm:logconc`, for
`t ∈ [0, 1]` (real-valued, the masses being finite; set to `0` outside `[0, 1]`, where it is not
used). Here `tφ₁ + (1-t)φ₀` is TN's `convexComb t φ₁ φ₀`, which at `t = 0, 1` is `φ₀`, `φ₁`
(`rmk:linearcompsh`). -/
def sourceConvexCombMass (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) {φ₀ φ₁ : M → EReal}
    (h₀ : (ofFixedModel n M).IsThetaPSH θ φ₀) (h₁ : (ofFixedModel n M).IsThetaPSH θ φ₁)
    (t : ℝ) : ℝ :=
  if ht : 0 ≤ t ∧ t ≤ 1 then
    (sourcePotentialNonPluripolarMeasure θ (convexComb t φ₁ φ₀)
      (isThetaPSH_convexComb h₁ h₀ ht.1 ht.2) univ).toReal
  else 0

omit [BorelSpace M] in
theorem sourceConvexCombMass_eq (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    {φ₀ φ₁ : M → EReal} (h₀ : (ofFixedModel n M).IsThetaPSH θ φ₀)
    (h₁ : (ofFixedModel n M).IsThetaPSH θ φ₁) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    sourceConvexCombMass θ h₀ h₁ t =
      (sourcePotentialNonPluripolarMeasure θ (convexComb t φ₁ φ₀)
        (isThetaPSH_convexComb h₁ h₀ ht0 ht1) univ).toReal := by
  rw [sourceConvexCombMass, dif_pos ⟨ht0, ht1⟩]

omit [BorelSpace M] in
theorem sourceConvexCombMass_nonneg (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    {φ₀ φ₁ : M → EReal} (h₀ : (ofFixedModel n M).IsThetaPSH θ φ₀)
    (h₁ : (ofFixedModel n M).IsThetaPSH θ φ₁) (t : ℝ) : 0 ≤ sourceConvexCombMass θ h₀ h₁ t := by
  unfold sourceConvexCombMass
  split_ifs
  · exact ENNReal.toReal_nonneg
  · exact le_rfl

/-- The source form of the multilinear expansion: the mixed mass of the tuple
`(tᵢφ₁ + (1-tᵢ)φ₀)ᵢ` in the background `θ`. -/
theorem sourceMixedMass_convexComb_eq_sum (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) {φ₀ φ₁ : M → EReal}
    (h₀ : (ofFixedModel n M).IsThetaPSH θ φ₀) (h₁ : (ofFixedModel n M).IsThetaPSH θ φ₁)
    (t : Fin n → ℝ) (ht0 : ∀ i, 0 ≤ t i) (ht1 : ∀ i, t i ≤ 1) :
    (sourceMixedNonPluripolarMass (fun _ => θ) (fun i => convexComb (t i) φ₁ φ₀)
      (fun i => isThetaPSH_convexComb h₁ h₀ (ht0 i) (ht1 i))).toReal =
      ∑ σ : Fin n → Bool, (∏ i, if σ i then t i else 1 - t i) *
        (sourceMixedNonPluripolarMass (fun _ => θ) (fun i => if σ i then φ₁ else φ₀)
          (fun i => by split_ifs <;> first | exact h₁ | exact h₀)).toReal :=
  globalMixedMass_convexComb_eq_sum ω ((isThetaPSH_iff_nativeThetaPotential θ φ₁).mp h₁)
    ((isThetaPSH_iff_nativeThetaPotential θ φ₀).mp h₀) t ht0 ht1

/-- The mass function as an endpoint polynomial. -/
theorem sourceConvexCombMass_eq_sum (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) {φ₀ φ₁ : M → EReal}
    (h₀ : (ofFixedModel n M).IsThetaPSH θ φ₀) (h₁ : (ofFixedModel n M).IsThetaPSH θ φ₁)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    sourceConvexCombMass θ h₀ h₁ t =
      ∑ σ : Fin n → Bool, (∏ i, if σ i then t else 1 - t) *
        (sourceMixedNonPluripolarMass (fun _ => θ) (fun i => if σ i then φ₁ else φ₀)
          (fun i => by split_ifs <;> first | exact h₁ | exact h₀)).toReal := by
  rw [sourceConvexCombMass_eq θ h₀ h₁ ht0 ht1, ← sourceMixedNonPluripolarMass_diagonal]
  exact sourceMixedMass_convexComb_eq_sum ω θ h₀ h₁ (fun _ => t) (fun _ => ht0) (fun _ => ht1)

end Convex

/-! ### The algebra of the first assertion -/

section Algebra

/-- **From mixed inequalities to concavity.** Let `Mix t = ∑_σ ∏ᵢ cᵢ(σᵢ) M_σ` be a polynomial
in slotwise weights as above. If `Mix` satisfies the mixed inequality for all tuples built from
`t₀` and `t₁`, then `((1-s) Mix(t₀)^{1/n} + s Mix(t₁)^{1/n})ⁿ ≤ Mix((1-s)t₀ + st₁)`. -/
theorem pow_le_of_mixed_inequality {n : ℕ} (M : (Fin n → Bool) → ℝ)
    {t₀ t₁ s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hmix : ∀ τ : Fin n → Bool,
      ∏ i, (∑ σ : Fin n → Bool, (∏ k, if σ k then (if τ i then t₁ else t₀)
          else 1 - (if τ i then t₁ else t₀)) * M σ) ^ (n : ℝ)⁻¹ ≤
        ∑ σ : Fin n → Bool, (∏ k, if σ k then (if τ k then t₁ else t₀)
          else 1 - (if τ k then t₁ else t₀)) * M σ) :
    ((1 - s) * (∑ σ : Fin n → Bool, (∏ k, if σ k then t₀ else 1 - t₀) * M σ) ^ (n : ℝ)⁻¹ +
        s * (∑ σ : Fin n → Bool, (∏ k, if σ k then t₁ else 1 - t₁) * M σ) ^ (n : ℝ)⁻¹) ^ n ≤
      ∑ σ : Fin n → Bool, (∏ k, if σ k then (1 - s) * t₀ + s * t₁
        else 1 - ((1 - s) * t₀ + s * t₁)) * M σ := by
  classical
  let tb : Bool → ℝ := fun b => if b then t₁ else t₀
  let w : Bool → ℝ := fun b => if b then s else 1 - s
  let mix : Bool → ℝ := fun b =>
    ∑ σ : Fin n → Bool, (∏ k, if σ k then tb b else 1 - tb b) * M σ
  let a : Bool → ℝ := fun b => mix b ^ (n : ℝ)⁻¹
  have hw : ∀ b, 0 ≤ w b := fun b => by
    cases b
    · exact sub_nonneg.mpr hs1
    · exact hs0
  have hlhs : (1 - s) * (∑ σ : Fin n → Bool, (∏ k, if σ k then t₀ else 1 - t₀) * M σ) ^
        (n : ℝ)⁻¹ + s * (∑ σ : Fin n → Bool, (∏ k, if σ k then t₁ else 1 - t₁) * M σ) ^
        (n : ℝ)⁻¹ = ∑ b, w b * a b := by
    simp only [Fintype.sum_bool, w, a, mix, tb, if_true, Bool.false_eq_true, if_false]
    ring
  rw [hlhs, Fintype.sum_pow]
  -- `∑_τ ∏ᵢ w(τᵢ) a(τᵢ) ≤ ∑_τ ∏ᵢ w(τᵢ) · Mix(τ)`
  have hstep : ∀ τ : Fin n → Bool, (∏ i, w (τ i) * a (τ i)) ≤
      (∏ i, w (τ i)) * ∑ σ : Fin n → Bool, (∏ k, if σ k then tb (τ k) else 1 - tb (τ k)) *
        M σ := by
    intro τ
    rw [Finset.prod_mul_distrib]
    refine mul_le_mul_of_nonneg_left ?_ (Finset.prod_nonneg fun i _ => hw (τ i))
    exact hmix τ
  refine (Finset.sum_le_sum fun τ _ => hstep τ).trans (le_of_eq ?_)
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  congr 1
  have hprod : ∀ τ : Fin n → Bool, (∏ i, w (τ i)) *
      (∏ k, if σ k then tb (τ k) else 1 - tb (τ k)) =
      ∏ i, (w (τ i) * if σ i then tb (τ i) else 1 - tb (τ i)) := fun τ =>
    (Finset.prod_mul_distrib).symm
  simp_rw [hprod]
  rw [← Fintype.prod_sum (fun i b => w b * if σ i then tb b else 1 - tb b)]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [Fintype.sum_bool, w, tb, if_true, Bool.false_eq_true, if_false]
  split_ifs <;> ring

end Algebra

/-! ### The first assertion -/

section FirstAssertion

variable {q : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel (q + 1)) M]
  [IsComplexManifold (q + 1) M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  [ConnectedSpace M]

/-- The key inequality: `((1-s) m(t₀)^{1/n} + s m(t₁)^{1/n})ⁿ ≤ m((1-s)t₀ + st₁)` for
`𝓘`-good endpoints. -/
theorem pow_le_sourceConvexCombMass_of_iGood (ω : KahlerBackground (q + 1) M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel (q + 1) M)) {φ₀ φ₁ : M → EReal}
    (h₀ : (ofFixedModel (q + 1) M).IsThetaPSH θ φ₀) (h₁ : (ofFixedModel (q + 1) M).IsThetaPSH θ φ₁)
    (hg₀ : sourceIGood (n := q + 1) φ₀) (hg₁ : sourceIGood (n := q + 1) φ₁)
    {t₀ t₁ s : ℝ} (ht₀ : t₀ ∈ Icc (0 : ℝ) 1) (ht₁ : t₁ ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    ((1 - s) * sourceConvexCombMass θ h₀ h₁ t₀ ^ (((q + 1 : ℕ) : ℝ)⁻¹) +
        s * sourceConvexCombMass θ h₀ h₁ t₁ ^ (((q + 1 : ℕ) : ℝ)⁻¹)) ^ (q + 1) ≤
      sourceConvexCombMass θ h₀ h₁ ((1 - s) * t₀ + s * t₁) := by
  classical
  have hr0 : 0 ≤ (1 - s) * t₀ + s * t₁ := by nlinarith [ht₀.1, ht₁.1, hs.1, hs.2]
  have hr1 : (1 - s) * t₀ + s * t₁ ≤ 1 := by nlinarith [ht₀.2, ht₁.2, hs.1, hs.2]
  rw [sourceConvexCombMass_eq_sum ω θ h₀ h₁ ht₀.1 ht₀.2,
    sourceConvexCombMass_eq_sum ω θ h₀ h₁ ht₁.1 ht₁.2,
    sourceConvexCombMass_eq_sum ω θ h₀ h₁ hr0 hr1]
  apply pow_le_of_mixed_inequality _ hs.1 hs.2
  intro τ
  let tb : Fin (q + 1) → ℝ := fun i => if τ i then t₁ else t₀
  have htb0 : ∀ i, 0 ≤ tb i := fun i => by
    dsimp only [tb]; split_ifs
    · exact ht₁.1
    · exact ht₀.1
  have htb1 : ∀ i, tb i ≤ 1 := fun i => by
    dsimp only [tb]; split_ifs
    · exact ht₁.2
    · exact ht₀.2
  have hmixed := prod_sourceMass_rpow_le_sourceMixedMass_of_iGood ω (fun _ => θ)
    (fun i => convexComb (tb i) φ₁ φ₀) (fun i => isThetaPSH_convexComb h₁ h₀ (htb0 i) (htb1 i))
    (fun i => sourceIGood_convexComb ω hg₁ hg₀ (htb0 i) (htb1 i))
  rw [sourceMixedMass_convexComb_eq_sum ω θ h₀ h₁ tb htb0 htb1] at hmixed
  refine le_of_eq_of_le (Finset.prod_congr rfl fun i _ => ?_) hmixed
  rw [sourceMixedMass_convexComb_eq_sum ω θ h₀ h₁ (fun _ => tb i) (fun _ => htb0 i)
    (fun _ => htb1 i)]

/-- **`thm:logconc`, first assertion, `𝓘`-good endpoints: concavity of `m^{1/n}`.** For
`𝓘`-good `φ₀, φ₁ ∈ PSH(X, θ)`, `t ↦ (∫_X θ_{tφ₁+(1-t)φ₀}ⁿ)^{1/n}` is concave on `[0, 1]`. -/
theorem concaveOn_sourceConvexCombMass_rpow_of_iGood (ω : KahlerBackground (q + 1) M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel (q + 1) M)) {φ₀ φ₁ : M → EReal}
    (h₀ : (ofFixedModel (q + 1) M).IsThetaPSH θ φ₀) (h₁ : (ofFixedModel (q + 1) M).IsThetaPSH θ φ₁)
    (hg₀ : sourceIGood (n := q + 1) φ₀) (hg₁ : sourceIGood (n := q + 1) φ₁) :
    ConcaveOn ℝ (Icc (0 : ℝ) 1)
      (fun t => sourceConvexCombMass θ h₀ h₁ t ^ (((q + 1 : ℕ) : ℝ)⁻¹)) := by
  refine ⟨convex_Icc 0 1, fun x hx y hy a b ha hb hab => ?_⟩
  have hs : b ∈ Icc (0 : ℝ) 1 := ⟨hb, by linarith⟩
  have ha' : a = 1 - b := by linarith
  subst ha'
  have h := pow_le_sourceConvexCombMass_of_iGood ω θ h₀ h₁ hg₀ hg₁ hx hy hs
  simp only [smul_eq_mul]
  have hnn : 0 ≤ (1 - b) * sourceConvexCombMass θ h₀ h₁ x ^ (((q + 1 : ℕ) : ℝ)⁻¹) +
      b * sourceConvexCombMass θ h₀ h₁ y ^ (((q + 1 : ℕ) : ℝ)⁻¹) := by
    have := sourceConvexCombMass_nonneg θ h₀ h₁ x
    have := sourceConvexCombMass_nonneg θ h₀ h₁ y
    positivity
  calc (1 - b) * sourceConvexCombMass θ h₀ h₁ x ^ (((q + 1 : ℕ) : ℝ)⁻¹) +
        b * sourceConvexCombMass θ h₀ h₁ y ^ (((q + 1 : ℕ) : ℝ)⁻¹)
      = (((1 - b) * sourceConvexCombMass θ h₀ h₁ x ^ (((q + 1 : ℕ) : ℝ)⁻¹) +
          b * sourceConvexCombMass θ h₀ h₁ y ^ (((q + 1 : ℕ) : ℝ)⁻¹)) ^ (q + 1)) ^
          (((q + 1 : ℕ) : ℝ)⁻¹) := (Real.pow_rpow_inv_natCast hnn (Nat.succ_ne_zero q)).symm
    _ ≤ sourceConvexCombMass θ h₀ h₁ ((1 - b) * x + b * y) ^ (((q + 1 : ℕ) : ℝ)⁻¹) :=
        Real.rpow_le_rpow (by positivity) h (by positivity)

/-- **`thm:logconc`, first assertion, `𝓘`-good endpoints: log-concavity.** For `𝓘`-good
`φ₀, φ₁ ∈ PSH(X, θ)` and `m(t) = ∫_X θ_{tφ₁+(1-t)φ₀}ⁿ`,
`m(t₀)^{1-s} m(t₁)^s ≤ m((1-s)t₀ + st₁)` for all `t₀, t₁, s ∈ [0, 1]`;
i.e. `log m` is concave on `[0, 1]` with the convention `log 0 = -∞`. -/
theorem sourceConvexCombMass_logConcave_of_iGood (ω : KahlerBackground (q + 1) M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel (q + 1) M)) {φ₀ φ₁ : M → EReal}
    (h₀ : (ofFixedModel (q + 1) M).IsThetaPSH θ φ₀) (h₁ : (ofFixedModel (q + 1) M).IsThetaPSH θ φ₁)
    (hg₀ : sourceIGood (n := q + 1) φ₀) (hg₁ : sourceIGood (n := q + 1) φ₁)
    {t₀ t₁ s : ℝ} (ht₀ : t₀ ∈ Icc (0 : ℝ) 1) (ht₁ : t₁ ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    sourceConvexCombMass θ h₀ h₁ t₀ ^ (1 - s) * sourceConvexCombMass θ h₀ h₁ t₁ ^ s ≤
      sourceConvexCombMass θ h₀ h₁ ((1 - s) * t₀ + s * t₁) := by
  set m := sourceConvexCombMass θ h₀ h₁ with hm
  set e : ℝ := ((q + 1 : ℕ) : ℝ)⁻¹ with he
  have hm0 : ∀ t, 0 ≤ m t := sourceConvexCombMass_nonneg θ h₀ h₁
  set a := m t₀ ^ e
  set b := m t₁ ^ e
  have ha : 0 ≤ a := Real.rpow_nonneg (hm0 _) _
  have hb : 0 ≤ b := Real.rpow_nonneg (hm0 _) _
  have hapow : m t₀ = a ^ (q + 1) := (Real.rpow_inv_natCast_pow (hm0 _) (Nat.succ_ne_zero q)).symm
  have hbpow : m t₁ = b ^ (q + 1) := (Real.rpow_inv_natCast_pow (hm0 _) (Nat.succ_ne_zero q)).symm
  have hamgm : a ^ (1 - s) * b ^ s ≤ (1 - s) * a + s * b :=
    Real.geom_mean_le_arith_mean2_weighted (sub_nonneg.mpr hs.2) hs.1 ha hb (by ring)
  have hkey := pow_le_sourceConvexCombMass_of_iGood ω θ h₀ h₁ hg₀ hg₁ ht₀ ht₁ hs
  refine le_trans (le_of_eq ?_) ((pow_le_pow_left₀ (by positivity) hamgm (q + 1)).trans hkey)
  rw [hapow, hbpow, mul_pow, ← Real.rpow_natCast (a ^ (1 - s)), ← Real.rpow_natCast (b ^ s),
    ← Real.rpow_mul ha, ← Real.rpow_mul hb, ← Real.rpow_natCast a, ← Real.rpow_natCast b,
    ← Real.rpow_mul ha, ← Real.rpow_mul hb, mul_comm (1 - s), mul_comm s]

/-- **`thm:logconc`, first assertion, `𝓘`-good endpoints, positive masses.** If moreover the
endpoint masses are positive, all masses `m(t)`, `t ∈ [0, 1]`, are positive and `log m` is
concave on `[0, 1]`. -/
theorem concaveOn_log_sourceConvexCombMass_of_iGood (ω : KahlerBackground (q + 1) M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel (q + 1) M)) {φ₀ φ₁ : M → EReal}
    (h₀ : (ofFixedModel (q + 1) M).IsThetaPSH θ φ₀) (h₁ : (ofFixedModel (q + 1) M).IsThetaPSH θ φ₁)
    (hg₀ : sourceIGood (n := q + 1) φ₀) (hg₁ : sourceIGood (n := q + 1) φ₁)
    (hpos₀ : 0 < sourceConvexCombMass θ h₀ h₁ 0) (hpos₁ : 0 < sourceConvexCombMass θ h₀ h₁ 1) :
    (∀ t ∈ Icc (0 : ℝ) 1, 0 < sourceConvexCombMass θ h₀ h₁ t) ∧
      ConcaveOn ℝ (Icc (0 : ℝ) 1) (fun t => Real.log (sourceConvexCombMass θ h₀ h₁ t)) := by
  set m := sourceConvexCombMass θ h₀ h₁ with hm
  have hm0 : ∀ t, 0 ≤ m t := sourceConvexCombMass_nonneg θ h₀ h₁
  have hpos : ∀ t ∈ Icc (0 : ℝ) 1, 0 < m t := by
    intro t ht
    have h := sourceConvexCombMass_logConcave_of_iGood ω θ h₀ h₁ hg₀ hg₁
      (t₀ := 0) (t₁ := 1) (s := t) ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ ht
    simp only [mul_zero, zero_add, mul_one] at h
    exact lt_of_lt_of_le (mul_pos (Real.rpow_pos_of_pos hpos₀ _) (Real.rpow_pos_of_pos hpos₁ _)) h
  refine ⟨hpos, convex_Icc 0 1, fun x hx y hy a b ha hb hab => ?_⟩
  have hs : b ∈ Icc (0 : ℝ) 1 := ⟨hb, by linarith⟩
  have ha' : a = 1 - b := by linarith
  subst ha'
  have h := sourceConvexCombMass_logConcave_of_iGood ω θ h₀ h₁ hg₀ hg₁ hx hy hs
  simp only [smul_eq_mul]
  have hx' := hpos x hx
  have hy' := hpos y hy
  calc (1 - b) * Real.log (m x) + b * Real.log (m y)
      = Real.log (m x ^ (1 - b) * m y ^ b) := by
        rw [Real.log_mul (Real.rpow_pos_of_pos hx' _).ne' (Real.rpow_pos_of_pos hy' _).ne',
          Real.log_rpow hx', Real.log_rpow hy']
    _ ≤ Real.log (m ((1 - b) * x + b * y)) :=
        Real.log_le_log (mul_pos (Real.rpow_pos_of_pos hx' _) (Real.rpow_pos_of_pos hy' _)) h

/-! ### The first assertion for bounded potentials -/

section Bounded

open BoundedGlobalProduct

omit [TopologicalSpace M] [ChartedSpace (ComplexModel (q + 1)) M]
  [IsComplexManifold (q + 1) M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  [ConnectedSpace M] in
/-- Convex combinations of bounded potentials are bounded. -/
theorem isBoundedPotential_convexComb {u v : M → EReal} (hu : IsBoundedPotential u)
    (hv : IsBoundedPotential v) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    IsBoundedPotential (convexComb t u v) := by
  obtain ⟨a, b, hab⟩ := hu
  obtain ⟨c, d, hcd⟩ := hv
  refine ⟨min a c, max b d, fun x => ?_⟩
  obtain ⟨hax, hxb⟩ := hab x
  obtain ⟨hcx, hxd⟩ := hcd x
  have hu1 : u x ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot a) hax
  have hu2 : u x ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top b) hxb
  have hv1 : v x ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot c) hcx
  have hv2 : v x ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top d) hxd
  have hur : u x = ((u x).toReal : EReal) := (EReal.coe_toReal hu2 hu1).symm
  have hvr : v x = ((v x).toReal : EReal) := (EReal.coe_toReal hv2 hv1).symm
  set r := (u x).toReal
  set r' := (v x).toReal
  rw [hur] at hax hxb
  rw [hvr] at hcx hxd
  have hax' : a ≤ r := EReal.coe_le_coe_iff.mp hax
  have hxb' : r ≤ b := EReal.coe_le_coe_iff.mp hxb
  have hcx' : c ≤ r' := EReal.coe_le_coe_iff.mp hcx
  have hxd' : r' ≤ d := EReal.coe_le_coe_iff.mp hxd
  have he : convexComb t u v x = ((t * r + (1 - t) * r' : ℝ) : EReal) := by
    rw [convexComb_apply, hur, hvr, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
  rw [he]
  have hmin1 := min_le_left a c
  have hmin2 := min_le_right a c
  have hmax1 := le_max_left b d
  have hmax2 := le_max_right b d
  constructor
  · exact EReal.coe_le_coe_iff.mpr (by nlinarith)
  · exact EReal.coe_le_coe_iff.mpr (by nlinarith)

omit [ConnectedSpace M] in
/-- For bounded `φ₀, φ₁` the mass `m(t)` is the intersection number `∫_X θⁿ`, independent of
`t`. -/
theorem sourceConvexCombMass_eq_slotIntegral_of_bounded (ω : KahlerBackground (q + 1) M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel (q + 1) M)) {φ₀ φ₁ : M → EReal}
    (h₀ : (ofFixedModel (q + 1) M).IsThetaPSH θ φ₀) (h₁ : (ofFixedModel (q + 1) M).IsThetaPSH θ φ₁)
    (hb₀ : IsBoundedPotential φ₀) (hb₁ : IsBoundedPotential φ₁) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    sourceConvexCombMass θ h₀ h₁ t =
      NefMixedMass.slotIntegral ω (fun _ : Fin (q + 1) => atlasClosedFormToNative θ) := by
  rw [sourceConvexCombMass_eq θ h₀ h₁ ht0 ht1, ← sourceMixedNonPluripolarMass_diagonal,
    sourceMixedNonPluripolarMass_eq_native]
  exact DominationIntersectionNumbers.globalMixedMass_toReal_eq_slotIntegral_of_isBoundedPotential
    ω _ (fun _ => isBoundedPotential_convexComb hb₁ hb₀ ht0 ht1)

omit [ConnectedSpace M] in
/-- **`thm:logconc`, first assertion, bounded endpoints.** For bounded `φ₀, φ₁ ∈ PSH(X, θ)` the
mass `m(t) = ∫_X θ_{tφ₁+(1-t)φ₀}ⁿ` is constant on `[0, 1]`, so
`m(t₀)^{1-s} m(t₁)^s ≤ m((1-s)t₀ + st₁)` and `m^{1/n}` is concave. -/
theorem sourceConvexCombMass_logConcave_of_bounded (ω : KahlerBackground (q + 1) M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel (q + 1) M)) {φ₀ φ₁ : M → EReal}
    (h₀ : (ofFixedModel (q + 1) M).IsThetaPSH θ φ₀) (h₁ : (ofFixedModel (q + 1) M).IsThetaPSH θ φ₁)
    (hb₀ : IsBoundedPotential φ₀) (hb₁ : IsBoundedPotential φ₁) :
    (∀ {t₀ t₁ s : ℝ}, t₀ ∈ Icc (0 : ℝ) 1 → t₁ ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 →
      sourceConvexCombMass θ h₀ h₁ t₀ ^ (1 - s) * sourceConvexCombMass θ h₀ h₁ t₁ ^ s ≤
        sourceConvexCombMass θ h₀ h₁ ((1 - s) * t₀ + s * t₁)) ∧
    ConcaveOn ℝ (Icc (0 : ℝ) 1)
      (fun t => sourceConvexCombMass θ h₀ h₁ t ^ (((q + 1 : ℕ) : ℝ)⁻¹)) := by
  set C := NefMixedMass.slotIntegral ω (fun _ : Fin (q + 1) => atlasClosedFormToNative θ)
  have hC : ∀ t ∈ Icc (0 : ℝ) 1, sourceConvexCombMass θ h₀ h₁ t = C := fun t ht =>
    sourceConvexCombMass_eq_slotIntegral_of_bounded ω θ h₀ h₁ hb₀ hb₁ ht.1 ht.2
  have hC0 : 0 ≤ C := (hC 0 ⟨le_rfl, zero_le_one⟩) ▸ sourceConvexCombMass_nonneg θ h₀ h₁ 0
  refine ⟨fun {t₀ t₁ s} ht₀ ht₁ hs => ?_, ?_⟩
  · have hr : (1 - s) * t₀ + s * t₁ ∈ Icc (0 : ℝ) 1 :=
      ⟨by nlinarith [ht₀.1, ht₁.1, hs.1, hs.2], by nlinarith [ht₀.2, ht₁.2, hs.1, hs.2]⟩
    rw [hC _ ht₀, hC _ ht₁, hC _ hr, ← Real.rpow_add' hC0 (by ring_nf; exact one_ne_zero),
      show 1 - s + s = 1 by ring, Real.rpow_one]
  · exact (concaveOn_const (C ^ (((q + 1 : ℕ) : ℝ)⁻¹)) (convex_Icc 0 1)).congr
      fun t ht => by simp only [hC t ht]

end Bounded

end FirstAssertion

/-! ### Dimension zero: both assertions in general -/

section DimZero

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel 0) M]
  [IsComplexManifold 0 M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

/-- **`thm:logconc`, mixed-mass inequality, dimension `0`** (`rmk:npp:L275`: `X` is a point).
For the empty tuple both sides are `1`. -/
theorem prod_sourceMass_rpow_le_sourceMixedMass_of_dim_zero
    (θ : Fin 0 → AtlasClosedRealOneOneForm (ofFixedModel 0 M)) (u : Fin 0 → M → EReal)
    (hu : ∀ i, (ofFixedModel 0 M).IsThetaPSH (θ i) (u i)) :
    ∏ i, ((sourceMixedNonPluripolarMass (fun _ => θ i) (fun _ => u i) (fun _ => hu i)).toReal) ^
        (((0 : ℕ) : ℝ)⁻¹) ≤
      (sourceMixedNonPluripolarMass θ u hu).toReal := by
  have : Subsingleton M := SGPT.NPP.subsingleton_of_dim_zero
  obtain ⟨x₀⟩ := (inferInstance : Nonempty M)
  have : Unique M := uniqueOfSubsingleton x₀
  rw [sourceMixedNonPluripolarMass_eq_native]
  unfold MixedMass.globalMixedMass
  rw [(ZeroDimensionalGlobalMixedMass.global_empty_mixed_measure_eq_count _ _ _).2.1,
    Nat.card_unique, Nat.cast_one]
  simp

/-- **`thm:logconc`, first assertion, dimension `0`.** All masses `m(t)` equal `1`, so `log m = 0`
is concave and `m(t₀)^{1-s} m(t₁)^s ≤ m((1-s)t₀ + st₁)`. -/
theorem sourceConvexCombMass_logConcave_of_dim_zero
    (θ : AtlasClosedRealOneOneForm (ofFixedModel 0 M)) {φ₀ φ₁ : M → EReal}
    (h₀ : (ofFixedModel 0 M).IsThetaPSH θ φ₀) (h₁ : (ofFixedModel 0 M).IsThetaPSH θ φ₁) :
    (∀ t ∈ Icc (0 : ℝ) 1, sourceConvexCombMass θ h₀ h₁ t = 1) ∧
    (∀ {t₀ t₁ s : ℝ}, t₀ ∈ Icc (0 : ℝ) 1 → t₁ ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 →
      sourceConvexCombMass θ h₀ h₁ t₀ ^ (1 - s) * sourceConvexCombMass θ h₀ h₁ t₁ ^ s ≤
        sourceConvexCombMass θ h₀ h₁ ((1 - s) * t₀ + s * t₁)) ∧
    ConcaveOn ℝ (Icc (0 : ℝ) 1) (fun t => Real.log (sourceConvexCombMass θ h₀ h₁ t)) := by
  have h1 : ∀ t ∈ Icc (0 : ℝ) 1, sourceConvexCombMass θ h₀ h₁ t = 1 := by
    intro t ht
    rw [sourceConvexCombMass_eq θ h₀ h₁ ht.1 ht.2,
      SGPT.NPP.sourcePotentialNonPluripolarMass_eq_one_of_dim_zero, ENNReal.toReal_one]
  refine ⟨h1, fun {t₀ t₁ s} ht₀ ht₁ hs => ?_, ?_⟩
  · have hr : (1 - s) * t₀ + s * t₁ ∈ Icc (0 : ℝ) 1 :=
      ⟨by nlinarith [ht₀.1, ht₁.1, hs.1, hs.2], by nlinarith [ht₀.2, ht₁.2, hs.1, hs.2]⟩
    rw [h1 _ ht₀, h1 _ ht₁, h1 _ hr, Real.one_rpow, Real.one_rpow, one_mul]
  · exact (concaveOn_const (0 : ℝ) (convex_Icc 0 1)).congr
      fun t ht => by simp only [h1 t ht, Real.log_one]

end DimZero

end SGPT.NPP.LogConcavity
