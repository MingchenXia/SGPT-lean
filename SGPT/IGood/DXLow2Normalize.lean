import SGPT.Foundations.Analysis.Pending.GlobalSlotLinear
import SGPT.Foundations.Analysis.Pending.ZeroDimensionalGlobalMixedMass
import SGPT.Foundations.Analysis.Pending.BoundedGlobalTruncation
import SGPT.Foundations.Analysis.Pending.IntegrationCurrent
import SGPT.NPP.DimensionZero
import SGPT.Foundations.Analysis.Pending.GlobalDiagonalScaling
import SGPT.Foundations.Analysis.Pending.KahlerLaplacianSolvability

/-!
# Normalized Kähler forms

Blueprint `claude-dx-low2`, node `claude-dx-low2:normalize`. The Bergman chapter fixes a Kähler form
`ω` with `∫_X ωⁿ = 1`. On a compact Kähler manifold such a form exists: `∫_X (cω)ⁿ = cⁿ ∫_X ωⁿ`
(`kahlerVolume_smul`, by one-slot linearity of the global mixed measures), so
`ω/(∫_X ωⁿ)^{1/n}` is normalized (`exists_normalized_kahlerBackground`); in dimension `0` the
Kähler volume of a connected manifold is already `1`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.IGood.DXLow2

open Set MeasureTheory
open scoped ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.IntegrationCurrent
open SGPT.Foundations.Analysis.Pending.GlobalNonPluripolar
open SGPT.Foundations.Analysis.Pending.GlobalDiagonalScaling

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

/-- The forms `θ_m i = ω` for `i < m` and `c ω` otherwise. -/
def mixForms (ω : KahlerBackground n X) (c : ℝ) (m : ℕ) : Fin n → ClosedRealOneOneForm n X :=
  fun i => if (i : ℕ) < m then ω.form else c • ω.form

theorem mixForms_semipositive (ω : KahlerBackground n X) {c : ℝ} (hc : 0 < c) (m : ℕ)
    (i : Fin n) : (mixForms ω c m i).val.IsSemipositive := by
  unfold mixForms
  split_ifs
  · exact ω.isSemipositive
  · exact KahlerDomination.isSemipositive_smul ω.isSemipositive hc.le

theorem mixForms_psh (ω : KahlerBackground n X) {c : ℝ} (hc : 0 < c) (m : ℕ) (i : Fin n) :
    ThetaPlurisubharmonic (mixForms ω c m i).val (fun _ : X => (0 : EReal)) := by
  have := BoundedGlobalProduct.thetaPlurisubharmonic_const _ (mixForms_semipositive ω hc m i) 0
  simpa using this

/-- The global mixed measure of `θ_m` with zero potentials. -/
def mixMeasure (ω : KahlerBackground n X) {c : ℝ} (hc : 0 < c) (m : ℕ) : Measure X :=
  globalMixedMeasure (mixForms ω c m) (fun _ _ => (0 : EReal)) (mixForms_psh ω hc m)

/-- One step: replacing `c ω` by `ω` in the slot `m` divides the measure by `c`. -/
theorem mixMeasure_step (ω : KahlerBackground n X) {c : ℝ} (hc : 0 < c) {m : ℕ} (hm : m < n) :
    mixMeasure ω hc m = ENNReal.ofReal c • mixMeasure ω hc (m + 1) := by
  set i₀ : Fin n := ⟨m, hm⟩
  have hc2 : 0 < c / 2 := half_pos hc
  have hθ : mixForms ω c m i₀ = (c / 2) • ω.form + (c / 2) • ω.form := by
    simp only [mixForms, i₀, lt_irrefl, if_false]
    rw [← add_smul, add_halves]
  have hupd : Function.update (mixForms ω c m) i₀ ω.form = mixForms ω c (m + 1) := by
    funext i
    by_cases hi : i = i₀
    · subst hi; simp [mixForms, i₀]
    · rw [Function.update_of_ne hi]
      have : (i : ℕ) ≠ m := fun h => hi (Fin.ext h)
      simp only [mixForms]
      split_ifs with h1 h2 h2 <;> first | rfl | omega
  have hx0 : ∀ (f : X → EReal), f = (fun _ => (0 : EReal)) →
      Function.update (fun _ : Fin n => fun _ : X => (0 : EReal)) i₀ f =
        fun _ : Fin n => fun _ : X => (0 : EReal) := by
    intro f hf
    subst hf
    exact Function.update_eq_self _ _
  have hsr : (fun p : X => ((c / 2 : ℝ) : EReal) * (0 : EReal) + ((c / 2 : ℝ) : EReal) * 0) =
      fun _ => (0 : EReal) := by
    funext p; simp
  have hpsh1 : ∀ i, ThetaPlurisubharmonic (mixForms ω c m i).val
      (Function.update (fun _ : Fin n => fun _ : X => (0 : EReal)) i₀
        (fun p => ((c / 2 : ℝ) : EReal) * (0 : EReal) + ((c / 2 : ℝ) : EReal) * 0) i) := by
    intro i
    rw [hsr, hx0 _ rfl]
    exact mixForms_psh ω hc m i
  have hpsh2 : ∀ i, ThetaPlurisubharmonic (Function.update (mixForms ω c m) i₀ ω.form i).val
      (Function.update (fun _ : Fin n => fun _ : X => (0 : EReal)) i₀ (fun _ => 0) i) := by
    intro i
    rw [hx0 _ rfl, hupd]
    exact mixForms_psh ω hc (m + 1) i
  have hmain := GlobalSlotLinear.globalMixedMeasure_update_add_smul i₀ hc2 hc2 hθ hpsh1 hpsh2 hpsh2
    (by simp) (by simp)
  have e1 : globalMixedMeasure (mixForms ω c m)
      (Function.update (fun _ : Fin n => fun _ : X => (0 : EReal)) i₀
        (fun p => ((c / 2 : ℝ) : EReal) * (0 : EReal) + ((c / 2 : ℝ) : EReal) * 0)) hpsh1 =
      mixMeasure ω hc m :=
    globalMixedMeasure_congr rfl (by rw [hsr, hx0 _ rfl]) _ _
  have e2 : globalMixedMeasure (Function.update (mixForms ω c m) i₀ ω.form)
      (Function.update (fun _ : Fin n => fun _ : X => (0 : EReal)) i₀ (fun _ => 0)) hpsh2 =
      mixMeasure ω hc (m + 1) :=
    globalMixedMeasure_congr hupd (hx0 _ rfl) _ _
  rw [e1, e2, ← add_smul, ← ENNReal.ofReal_add hc2.le hc2.le, add_halves] at hmain
  exact hmain

/-- **Homogeneity of the Kähler volume**: `∫_X (cω)ⁿ = cⁿ ∫_X ωⁿ`. -/
theorem kahlerVolume_smul (ω : KahlerBackground n X) {c : ℝ} (hc : 0 < c) :
    kahlerVolume (KahlerBackground.smul hc ω) = ENNReal.ofReal c ^ n • kahlerVolume ω := by
  have hall : ∀ j, j ≤ n → mixMeasure ω hc (n - j) = ENNReal.ofReal c ^ j • mixMeasure ω hc n := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have hstep := mixMeasure_step ω hc (m := n - (j + 1)) (by omega)
      rw [show n - (j + 1) + 1 = n - j by omega, ih (by omega), smul_smul, ← pow_succ'] at hstep
      exact hstep
  have h0 := hall n le_rfl
  rw [Nat.sub_self] at h0
  have hl : kahlerVolume (KahlerBackground.smul hc ω) = mixMeasure ω hc 0 := by
    unfold kahlerVolume DiagonalMass.diagonalPotentialMeasure mixMeasure
    refine globalMixedMeasure_congr ?_ rfl _ _
    funext i
    simp [mixForms, KahlerBackground.smul_form]
  have hr : kahlerVolume ω = mixMeasure ω hc n := by
    unfold kahlerVolume DiagonalMass.diagonalPotentialMeasure mixMeasure
    refine globalMixedMeasure_congr ?_ rfl _ _
    funext i
    simp [mixForms, i.isLt]
  rw [hl, hr, h0]

/-- **Normalized Kähler forms exist**: on a connected compact Kähler manifold there is a Kähler
background with `∫_X ωⁿ = 1`. -/
theorem exists_normalized_kahlerBackground [ConnectedSpace X] (κ : KahlerBackground n X) :
    ∃ ω : KahlerBackground n X, kahlerVolume ω univ = 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨κ, ?_⟩
    let : Subsingleton X := SGPT.NPP.subsingleton_of_dim_zero
    have h := (ZeroDimensionalGlobalMixedMass.global_empty_mixed_measure_eq_count
      (M := X) (fun _ => κ.form) (fun _ _ => (0 : EReal))
      (fun _ => ((LocalPotentials.isThetaPshPotential_zero_iff κ.form).mpr κ.isSemipositive).1)).2.1
    unfold kahlerVolume DiagonalMass.diagonalPotentialMeasure
    rw [h]
    obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
    have : Unique X := uniqueOfSubsingleton x₀
    simp
  · set V : ℝ := (kahlerVolume κ).real univ with hVdef
    have hV : 0 < V := KahlerLaplacianSolvability.kahlerVolume_real_univ_pos κ
    set c : ℝ := V ^ (-(n : ℝ)⁻¹) with hcdef
    have hc : 0 < c := Real.rpow_pos_of_pos hV _
    refine ⟨KahlerBackground.smul hc κ, ?_⟩
    rw [kahlerVolume_smul, Measure.smul_apply, smul_eq_mul,
      ← ENNReal.ofReal_toReal (measure_ne_top (kahlerVolume κ) univ)]
    change ENNReal.ofReal c ^ n * ENNReal.ofReal V = 1
    rw [← ENNReal.ofReal_pow hc.le, ← ENNReal.ofReal_mul (by positivity)]
    have hcn : c ^ n = V⁻¹ := by
      rw [hcdef, ← Real.rpow_natCast, ← Real.rpow_mul hV.le,
        show -(n : ℝ)⁻¹ * (n : ℝ) = -1 by field_simp, Real.rpow_neg_one]
    rw [hcn, inv_mul_cancel₀ hV.ne', ENNReal.ofReal_one]

end SGPT.IGood.DXLow2
