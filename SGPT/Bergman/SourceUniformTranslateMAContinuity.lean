import SGPT.Envelopes.SourceMixedEnergyIntegrability
import SGPT.Foundations.Analysis.Pending.ActualMixedCapacityWeakConvergence
import Mathlib.Topology.Sequences

/-! Weak Monge–Ampère continuity from finite-translation control and equal total masses. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.PartialEnergyDifferentiability

open Set Filter MeasureTheory
open SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending GlobalNonPluripolar ThetaCapacity
open scoped Topology ENNReal

/-- Actual scalar readback is used ONLY at points where both genuine
potentials are finite. The original inequalities still retain all poles. -/
theorem abs_toReal_sub_le_of_translate_sandwich {a b : EReal} {d : ℝ}
    (hat : a ≠ ⊤) (hab : a ≠ ⊥) (hbt : b ≠ ⊤) (hbb : b ≠ ⊥)
    (hlo : a + ((-d : ℝ) : EReal) ≤ b) (hup : b ≤ a + (d : EReal)) :
    |b.toReal - a.toReal| ≤ d := by
  have ha : a = (a.toReal : EReal) := (EReal.coe_toReal hat hab).symm
  have hb : b = (b.toReal : EReal) := (EReal.coe_toReal hbt hbb).symm
  rw [ha, hb, ← EReal.coe_add, EReal.coe_le_coe_iff] at hlo hup
  exact abs_le.mpr ⟨by linarith, by linarith⟩

universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- The actual native capacity exceptions are eventually EMPTY, hence the
actual signed continuous MA integrals converge. No desired MA limit is input. -/
theorem tendsto_integral_of_translate_sandwich (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u : ℕ → M → EReal} {v : M → EReal}
    (hu : ∀ j, (ofFixedModel n M).IsThetaPSH θ (u j))
    (hv : (ofFixedModel n M).IsThetaPSH θ v)
    {d : ℕ → ℝ} (hd : Tendsto d atTop (𝓝 0))
    (hsand : ∀ j x, v x + ((-d j : ℝ) : EReal) ≤ u j x ∧ u j x ≤ v x + (d j : EReal))
    (hmass : ∀ j, sourcePotentialNonPluripolarMeasure θ (u j) (hu j) univ =
      sourcePotentialNonPluripolarMeasure θ v hv univ)
    {F : M → ℝ} (hF : Continuous F) :
    Tendsto (fun j => ∫ x, F x ∂sourcePotentialNonPluripolarMeasure θ (u j) (hu j)) atTop
      (𝓝 (∫ x, F x ∂sourcePotentialNonPluripolarMeasure θ v hv)) := by
  have hcap (i : Fin n) (a : ℝ) (ha : 0 < a) :
      Tendsto (fun j => thetaCapacity ω.form (fun _ => 0)
        {x | u j x ≠ ⊥ ∧ v x ≠ ⊥ ∧ a < |(u j x).toReal - (v x).toReal|}) atTop (𝓝 0) := by
    have hdsmall := hd.eventually (Iio_mem_nhds ha)
    have heq : (fun j => thetaCapacity ω.form (fun _ => 0)
        {x | u j x ≠ ⊥ ∧ v x ≠ ⊥ ∧ a < |(u j x).toReal - (v x).toReal|}) =ᶠ[atTop]
        fun _ => 0 := by
      filter_upwards [hdsmall] with j hj
      have hempty : {x | u j x ≠ ⊥ ∧ v x ≠ ⊥ ∧ a < |(u j x).toReal - (v x).toReal|} = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro x hx
        have hb := abs_toReal_sub_le_of_translate_sandwich (hv.1 x) hx.2.1
          ((hu j).1 x) hx.1 (hsand j x).1 (hsand j x).2
        exact (not_lt_of_ge (hb.trans hj.le)) hx.2.2
      rw [hempty, thetaCapacity_empty]
    exact tendsto_const_nhds.congr' heq.symm
  have hupper : limsup (fun j => sourcePotentialNonPluripolarMeasure θ (u j) (hu j) univ) atTop ≤
      sourcePotentialNonPluripolarMeasure θ v hv univ := by
    simp only [hmass, limsup_const, le_refl]
  exact ActualMixedCapacityWeakConvergence.tendsto_integral ω
    (fun j (_ : Fin n) => (isThetaPSH_iff_nativeThetaPotential θ _).mp (hu j))
    (fun _ : Fin n => (isThetaPSH_iff_nativeThetaPotential θ _).mp hv) hcap hupper hF

/-- A genuine real-parameter family with actual finite-translation control
and actual constant masses has continuous signed continuous MA reads at
EVERY real parameter, by the existing actual capacity theorem. -/
theorem continuous_integral_of_translate_control (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u : ℝ → M → EReal}
    (hu : ∀ t, (ofFixedModel n M).IsThetaPSH θ (u t)) (R : ℝ)
    (hsand : ∀ s t x, u s x + ((-|t - s| * R : ℝ) : EReal) ≤ u t x ∧
      u t x ≤ u s x + ((|t - s| * R : ℝ) : EReal))
    (hmass : ∀ s t, sourcePotentialNonPluripolarMeasure θ (u t) (hu t) univ =
      sourcePotentialNonPluripolarMeasure θ (u s) (hu s) univ)
    {F : M → ℝ} (hF : Continuous F) :
    Continuous (fun t => ∫ x, F x ∂sourcePotentialNonPluripolarMeasure θ (u t) (hu t)) := by
  apply continuous_iff_continuousAt.mpr
  intro s
  apply tendsto_nhds_iff_seq_tendsto.mpr
  intro t ht
  have hd : Tendsto (fun j => |t j - s| * R) atTop (𝓝 0) := by
    simpa only [sub_self, abs_zero, zero_mul] using (ht.sub_const s).abs.mul_const R
  have hs (j) (x) : u s x + ((-(|t j - s| * R) : ℝ) : EReal) ≤ u (t j) x ∧
      u (t j) x ≤ u s x + ((|t j - s| * R : ℝ) : EReal) := by
    simpa only [neg_mul] using hsand s (t j) x
  exact tendsto_integral_of_translate_sandwich ω (fun j => hu (t j)) (hu s) hd hs
    (fun j => hmass s (t j)) hF

end SGPT.Bergman.PartialEnergyDifferentiability
