import SGPT.Foundations.Analysis.Pending.BedfordTaylorFibreSlicing
import SGPT.Foundations.Analysis.Pending.VaguePortmanteau
import Mathlib.Topology.MetricSpace.ThickenedIndicator
import Mathlib.MeasureTheory.Function.SimpleFuncDense
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

/-! # Borel tests in actual Bedford--Taylor fibre slicing

A measure-theoretic extension of actual continuous-test slicing used in
SGPT (2.11)/(4.29), PDF0171. No Borel fibre identity or kernel is an input.
Non-pluripolar increasing limits remain a separate producer.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.BedfordTaylorBorelFibreSlicing

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere BedfordTaylor
  BedfordTaylorFibreSlicing MixedDensityRankOneSlot

noncomputable section

variable {n : ℕ} {Ω : Opens (ComplexModel (n + 1))}
  {u : Fin (n + 1) → ComplexModel (n + 1) → ℝ}
  {ν : Measure (ComplexModel (n + 1))} {μ : ℂ → Measure (ComplexModel n)}
  {χ : ComplexModel (n + 1) → ℝ}

private theorem integrable_test (hν : IsBTLimit Ω u ν)
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hχΩ : tsupport χ ⊆ Ω) :
    Integrable χ ν :=
  VaguePortmanteau.integrable_of_tsupport_subset hν.2.1 hχ hχc hχΩ

private theorem integrable_fibre_test
    (hμ : ∀ τ, IsBTLimit (fibreOpens Ω τ) (fibreTuple u τ) (μ τ))
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hχΩ : tsupport χ ⊆ Ω) (τ : ℂ) :
    Integrable (fibreRestrict χ τ) (μ τ) := by
  have hsupp := tsupport_fibreRestrict_subset χ τ
  have hc : HasCompactSupport (fibreRestrict χ τ) :=
    (isCompact_preimage_fibreMap hχc τ).of_isClosed_subset (isClosed_tsupport _) hsupp
  exact VaguePortmanteau.integrable_of_tsupport_subset (hμ τ).2.1
    (hχ.comp (continuous_fibreMap τ)) hc (fun y hy => hχΩ (hsupp hy))

private theorem integrable_test_mul (hν : IsBTLimit Ω u ν)
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hχΩ : tsupport χ ⊆ Ω)
    {F : ComplexModel (n + 1) → ℝ} (hFm : Measurable F) {C : ℝ}
    (hFb : ∀ q, ‖F q‖ ≤ C) : Integrable (fun q => χ q * F q) ν :=
  (integrable_test hν hχ hχc hχΩ).mul_bdd hFm.aestronglyMeasurable
    (Eventually.of_forall hFb)

private theorem integrable_fibre_test_mul
    (hμ : ∀ τ, IsBTLimit (fibreOpens Ω τ) (fibreTuple u τ) (μ τ))
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hχΩ : tsupport χ ⊆ Ω)
    {F : ComplexModel (n + 1) → ℝ} (hFm : Measurable F) {C : ℝ}
    (hFb : ∀ q, ‖F q‖ ≤ C) (τ : ℂ) :
    Integrable (fun y => fibreRestrict χ τ y * fibreRestrict F τ y) (μ τ) :=
  (integrable_fibre_test hμ hχ hχc hχΩ τ).mul_bdd
    (hFm.comp (continuous_fibreMap τ).measurable).aestronglyMeasurable
    (Eventually.of_forall fun y => hFb (fibreMap n τ y))

private theorem slicing_sub (hν : IsBTLimit Ω u ν)
    (hμ : ∀ τ, IsBTLimit (fibreOpens Ω τ) (fibreTuple u τ) (μ τ))
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hχΩ : tsupport χ ⊆ Ω)
    {F G : ComplexModel (n + 1) → ℝ} (hFm : Measurable F) (hGm : Measurable G)
    {C D : ℝ} (hFb : ∀ q, ‖F q‖ ≤ C) (hGb : ∀ q, ‖G q‖ ≤ D)
    (hF : Integrable (fun τ : ℂ => ∫ y, fibreRestrict χ τ y * fibreRestrict F τ y ∂(μ τ)) ∧
      (∫ q, χ q * F q ∂ν) = (∫ τ : ℂ,
        ∫ y, fibreRestrict χ τ y * fibreRestrict F τ y ∂(μ τ)) / Real.pi)
    (hG : Integrable (fun τ : ℂ => ∫ y, fibreRestrict χ τ y * fibreRestrict G τ y ∂(μ τ)) ∧
      (∫ q, χ q * G q ∂ν) = (∫ τ : ℂ,
        ∫ y, fibreRestrict χ τ y * fibreRestrict G τ y ∂(μ τ)) / Real.pi) :
    Integrable (fun τ : ℂ => ∫ y, fibreRestrict χ τ y * fibreRestrict (F - G) τ y ∂(μ τ)) ∧
      (∫ q, χ q * (F - G) q ∂ν) = (∫ τ : ℂ,
        ∫ y, fibreRestrict χ τ y * fibreRestrict (F - G) τ y ∂(μ τ)) / Real.pi := by
  have heq : (fun q => χ q * (F - G) q) = fun q => χ q * F q - χ q * G q := by
    funext q
    simp only [Pi.sub_apply, mul_sub]
  have hinner (τ : ℂ) :
      (∫ y, fibreRestrict χ τ y * fibreRestrict (F - G) τ y ∂(μ τ)) =
      (∫ y, fibreRestrict χ τ y * fibreRestrict F τ y ∂(μ τ)) -
      (∫ y, fibreRestrict χ τ y * fibreRestrict G τ y ∂(μ τ)) := by
    simp only [fibreRestrict, Pi.sub_apply, mul_sub]
    exact integral_sub (integrable_fibre_test_mul hμ hχ hχc hχΩ hFm hFb τ)
      (integrable_fibre_test_mul hμ hχ hχc hχΩ hGm hGb τ)
  have hout : (fun τ : ℂ => ∫ y, fibreRestrict χ τ y * fibreRestrict (F - G) τ y ∂(μ τ)) =
      fun τ => (∫ y, fibreRestrict χ τ y * fibreRestrict F τ y ∂(μ τ)) -
        (∫ y, fibreRestrict χ τ y * fibreRestrict G τ y ∂(μ τ)) := funext hinner
  refine ⟨?_, ?_⟩
  · rw [hout]
    exact hF.1.sub hG.1
  · rw [heq, integral_sub (integrable_test_mul hν hχ hχc hχΩ hFm hFb)
      (integrable_test_mul hν hχ hχc hχΩ hGm hGb), hout,
      integral_sub hF.1 hG.1, hF.2, hG.2, sub_div]

private theorem slicing_of_bounded_limit
    (hlast : u (Fin.last n) = lastNormSq n) (hν : IsBTLimit Ω u ν)
    (hμ : ∀ τ, IsBTLimit (fibreOpens Ω τ) (fibreTuple u τ) (μ τ))
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hχΩ : tsupport χ ⊆ Ω)
    (hχ0 : ∀ q, 0 ≤ χ q) {F : ComplexModel (n + 1) → ℝ}
    {Fk : ℕ → ComplexModel (n + 1) → ℝ} {C : ℝ}
    (hFkm : ∀ k, Measurable (Fk k))
    (hFkb : ∀ k q, ‖Fk k q‖ ≤ C)
    (hlim : ∀ q, Tendsto (fun k => Fk k q) atTop (𝓝 (F q)))
    (hk : ∀ k, Integrable (fun τ : ℂ =>
        ∫ y, fibreRestrict χ τ y * fibreRestrict (Fk k) τ y ∂(μ τ)) ∧
      (∫ q, χ q * Fk k q ∂ν) = (∫ τ : ℂ,
        ∫ y, fibreRestrict χ τ y * fibreRestrict (Fk k) τ y ∂(μ τ)) / Real.pi) :
    Integrable (fun τ : ℂ => ∫ y, fibreRestrict χ τ y * fibreRestrict F τ y ∂(μ τ)) ∧
      (∫ q, χ q * F q ∂ν) = (∫ τ : ℂ,
        ∫ y, fibreRestrict χ τ y * fibreRestrict F τ y ∂(μ τ)) / Real.pi := by
  let B : ℂ → ℝ := fun τ => ∫ y, fibreRestrict χ τ y ∂(μ τ)
  let J : ℕ → ℂ → ℝ := fun k τ =>
    ∫ y, fibreRestrict χ τ y * fibreRestrict (Fk k) τ y ∂(μ τ)
  let L : ℂ → ℝ := fun τ => ∫ y, fibreRestrict χ τ y * fibreRestrict F τ y ∂(μ τ)
  have hBint : Integrable B :=
    (integral_isBTLimit_eq_fibre hlast hν hμ hχ hχc hχΩ).1
  have hχν : Integrable χ ν := integrable_test hν hχ hχc hχΩ
  have hχτ (τ : ℂ) : Integrable (fibreRestrict χ τ) (μ τ) :=
    integrable_fibre_test hμ hχ hχc hχΩ τ
  have hnorm (k : ℕ) (q : ComplexModel (n + 1)) : ‖χ q * Fk k q‖ ≤ C * χ q := by
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hχ0 q)]
    exact (mul_le_mul_of_nonneg_left (hFkb k q) (hχ0 q)).trans_eq (mul_comm _ _)
  have hJlim (τ : ℂ) : Tendsto (fun k => J k τ) atTop (𝓝 (L τ)) := by
    apply tendsto_integral_of_dominated_convergence (fun y => C * fibreRestrict χ τ y)
    · intro k
      exact ((hχ.comp (continuous_fibreMap τ)).measurable.mul
        ((hFkm k).comp (continuous_fibreMap τ).measurable)).aestronglyMeasurable
    · exact (hχτ τ).const_mul C
    · intro k
      exact Eventually.of_forall fun y => hnorm k (fibreMap n τ y)
    · exact Eventually.of_forall fun y => tendsto_const_nhds.mul (hlim (fibreMap n τ y))
  have hJbound (k : ℕ) (τ : ℂ) : ‖J k τ‖ ≤ C * B τ := by
    have hb := norm_integral_le_of_norm_le ((hχτ τ).const_mul C)
      (Eventually.of_forall fun y => hnorm k (fibreMap n τ y))
    simpa only [J, B, fibreRestrict, integral_const_mul] using hb
  have hLmeas : AEStronglyMeasurable L :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun k => (hk k).1.aestronglyMeasurable)
      (Eventually.of_forall hJlim)
  have hLbound (τ : ℂ) : ‖L τ‖ ≤ C * B τ :=
    le_of_tendsto ((continuous_norm.tendsto _).comp (hJlim τ))
      (Eventually.of_forall fun k => hJbound k τ)
  have hLint : Integrable L := (hBint.const_mul C).mono' hLmeas
    (Eventually.of_forall hLbound)
  have houter := tendsto_integral_of_dominated_convergence (fun τ => C * B τ)
    (fun k => (hk k).1.aestronglyMeasurable) (hBint.const_mul C)
    (fun k => Eventually.of_forall fun τ => hJbound k τ) (Eventually.of_forall hJlim)
  have hjoint := tendsto_integral_of_dominated_convergence (fun q => C * χ q)
    (fun k => (hχ.measurable.mul (hFkm k)).aestronglyMeasurable) (hχν.const_mul C)
    (fun k => Eventually.of_forall fun q => hnorm k q)
    (Eventually.of_forall fun q => tendsto_const_nhds.mul (hlim q))
  refine ⟨hLint, tendsto_nhds_unique hjoint ?_⟩
  exact (houter.div_const Real.pi).congr'
    (Eventually.of_forall fun k => (hk k).2.symm)

private theorem slicing_finsetSum {ι : Type*} (s : Finset ι)
    (hν : IsBTLimit Ω u ν)
    (hμ : ∀ τ, IsBTLimit (fibreOpens Ω τ) (fibreTuple u τ) (μ τ))
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hχΩ : tsupport χ ⊆ Ω)
    {F : ι → ComplexModel (n + 1) → ℝ} {C : ι → ℝ}
    (hFm : ∀ i ∈ s, Measurable (F i)) (hFb : ∀ i ∈ s, ∀ q, ‖F i q‖ ≤ C i)
    (hF : ∀ i ∈ s,
      Integrable (fun τ : ℂ => ∫ y, fibreRestrict χ τ y * fibreRestrict (F i) τ y ∂(μ τ)) ∧
      (∫ q, χ q * F i q ∂ν) = (∫ τ : ℂ,
        ∫ y, fibreRestrict χ τ y * fibreRestrict (F i) τ y ∂(μ τ)) / Real.pi) :
    Integrable (fun τ : ℂ => ∫ y, fibreRestrict χ τ y *
      fibreRestrict (fun q => ∑ i ∈ s, F i q) τ y ∂(μ τ)) ∧
      (∫ q, χ q * (∑ i ∈ s, F i q) ∂ν) = (∫ τ : ℂ,
        ∫ y, fibreRestrict χ τ y *
          fibreRestrict (fun q => ∑ i ∈ s, F i q) τ y ∂(μ τ)) / Real.pi := by
  have hleft : (fun q => χ q * (∑ i ∈ s, F i q)) =
      fun q => ∑ i ∈ s, χ q * F i q := by
    funext q
    exact Finset.mul_sum _ _ _
  have hinner (τ : ℂ) : (∫ y, fibreRestrict χ τ y *
      fibreRestrict (fun q => ∑ i ∈ s, F i q) τ y ∂(μ τ)) =
      ∑ i ∈ s, ∫ y, fibreRestrict χ τ y * fibreRestrict (F i) τ y ∂(μ τ) := by
    simp only [fibreRestrict, Finset.mul_sum]
    exact integral_finsetSum s (fun i hi =>
      integrable_fibre_test_mul hμ hχ hχc hχΩ (hFm i hi) (hFb i hi) τ)
  have hout : (fun τ : ℂ => ∫ y, fibreRestrict χ τ y *
      fibreRestrict (fun q => ∑ i ∈ s, F i q) τ y ∂(μ τ)) =
      fun τ => ∑ i ∈ s, ∫ y, fibreRestrict χ τ y * fibreRestrict (F i) τ y ∂(μ τ) :=
    funext hinner
  refine ⟨?_, ?_⟩
  · rw [hout]
    exact integrable_finsetSum s (fun i hi => (hF i hi).1)
  · rw [hleft, integral_finsetSum s (fun i hi =>
      integrable_test_mul hν hχ hχc hχΩ (hFm i hi) (hFb i hi)),
      hout, integral_finsetSum s (fun i hi => (hF i hi).1), Finset.sum_div]
    exact Finset.sum_congr rfl fun i hi => (hF i hi).2

private theorem slicing_open_indicator
    (hlast : u (Fin.last n) = lastNormSq n) (hν : IsBTLimit Ω u ν)
    (hμ : ∀ τ, IsBTLimit (fibreOpens Ω τ) (fibreTuple u τ) (μ τ))
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hχΩ : tsupport χ ⊆ Ω)
    (hχ0 : ∀ q, 0 ≤ χ q) {E : Set (ComplexModel (n + 1))} (hE : IsOpen E) :
    Integrable (fun τ : ℂ => ∫ y, fibreRestrict χ τ y *
      fibreRestrict (E.indicator (fun _ => (1 : ℝ))) τ y ∂(μ τ)) ∧
      (∫ q, χ q * E.indicator (fun _ => (1 : ℝ)) q ∂ν) = (∫ τ : ℂ,
        ∫ y, fibreRestrict χ τ y *
          fibreRestrict (E.indicator (fun _ => (1 : ℝ))) τ y ∂(μ τ)) / Real.pi := by
  have hδ (k : ℕ) : 0 < (1 : ℝ) / ((k : ℝ) + 1) := by positivity
  let Fk : ℕ → ComplexModel (n + 1) → ℝ :=
    fun k q => 1 - (thickenedIndicator (hδ k) Eᶜ q : ℝ)
  have hFc (k : ℕ) : Continuous (Fk k) :=
    continuous_const.sub (NNReal.continuous_coe.comp (thickenedIndicator (hδ k) Eᶜ).continuous)
  have hFb (k : ℕ) (q : ComplexModel (n + 1)) : ‖Fk k q‖ ≤ 1 := by
    have hlo : 0 ≤ (thickenedIndicator (hδ k) Eᶜ q : ℝ) := NNReal.coe_nonneg _
    have hup : (thickenedIndicator (hδ k) Eᶜ q : ℝ) ≤ 1 := by
      exact_mod_cast thickenedIndicator_le_one (hδ k) Eᶜ q
    change ‖1 - (thickenedIndicator (hδ k) Eᶜ q : ℝ)‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hup)]
    linarith
  have hFlim (q : ComplexModel (n + 1)) :
      Tendsto (fun k => Fk k q) atTop (𝓝 (E.indicator (fun _ => (1 : ℝ)) q)) := by
    have hs := thickenedIndicator_tendsto_indicator_closure hδ
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) Eᶜ
    have hq := (NNReal.continuous_coe.tendsto _).comp ((tendsto_pi_nhds.mp hs) q)
    have ht := (tendsto_const_nhds (x := (1 : ℝ))).sub hq
    by_cases h : q ∈ E
    · simpa [Fk, hE.isClosed_compl.closure_eq, h] using ht
    · simpa [Fk, hE.isClosed_compl.closure_eq, h] using ht
  apply slicing_of_bounded_limit hlast hν hμ hχ hχc hχΩ hχ0
    (fun k => (hFc k).measurable) hFb hFlim
  intro k
  have hsupp : tsupport (fun q => χ q * Fk k q) ⊆ tsupport χ := tsupport_mul_subset_left
  have hc : HasCompactSupport (fun q => χ q * Fk k q) :=
    hχc.of_isClosed_subset (isClosed_tsupport _) hsupp
  have hs := integral_isBTLimit_eq_fibre hlast hν hμ (hχ.mul (hFc k)) hc (hsupp.trans hχΩ)
  simpa only [fibreRestrict, Pi.mul_apply] using hs

/-- Actual Borel-indicator slicing, with every joint and fibre integrability
produced from the genuine Bedford--Taylor products. -/
theorem integral_indicator_isBTLimit_eq_fibre
    (hlast : u (Fin.last n) = lastNormSq n) (hν : IsBTLimit Ω u ν)
    (hμ : ∀ τ, IsBTLimit (fibreOpens Ω τ) (fibreTuple u τ) (μ τ))
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hχΩ : tsupport χ ⊆ Ω)
    (hχ0 : ∀ q, 0 ≤ χ q) {E : Set (ComplexModel (n + 1))} (hE : MeasurableSet E) :
    Integrable (fun q => χ q * E.indicator (fun _ => (1 : ℝ)) q) ν ∧
    (∀ τ : ℂ, Integrable (fun y => fibreRestrict χ τ y *
      fibreRestrict (E.indicator (fun _ => (1 : ℝ))) τ y) (μ τ)) ∧
    Integrable (fun τ : ℂ => ∫ y, fibreRestrict χ τ y *
      fibreRestrict (E.indicator (fun _ => (1 : ℝ))) τ y ∂(μ τ)) ∧
      (∫ q, χ q * E.indicator (fun _ => (1 : ℝ)) q ∂ν) = (∫ τ : ℂ,
        ∫ y, fibreRestrict χ τ y *
          fibreRestrict (E.indicator (fun _ => (1 : ℝ))) τ y ∂(μ τ)) / Real.pi := by
  classical
  let W : Set (ComplexModel (n + 1)) → ComplexModel (n + 1) → ℝ :=
    fun S => S.indicator (fun _ => 1)
  have hWb (S : Set (ComplexModel (n + 1))) (q : ComplexModel (n + 1)) : ‖W S q‖ ≤ 1 := by
    by_cases h : q ∈ S <;> simp [W, h]
  have hWm (S : Set (ComplexModel (n + 1))) (hS : MeasurableSet S) : Measurable (W S) :=
    measurable_const.indicator hS
  refine ⟨integrable_test_mul hν hχ hχc hχΩ (hWm E hE) (hWb E),
    fun τ => integrable_fibre_test_mul hμ hχ hχc hχΩ (hWm E hE) (hWb E) τ, ?_⟩
  let P : Set (ComplexModel (n + 1)) → Prop := fun S =>
    Integrable (fun τ : ℂ => ∫ y, fibreRestrict χ τ y * fibreRestrict (W S) τ y ∂(μ τ)) ∧
      (∫ q, χ q * W S q ∂ν) = (∫ τ : ℂ,
        ∫ y, fibreRestrict χ τ y * fibreRestrict (W S) τ y ∂(μ τ)) / Real.pi
  change P E
  refine MeasurableSet.induction_on_open (C := fun S _ => P S) ?_ ?_ ?_ E hE
  · intro S hS
    exact slicing_open_indicator hlast hν hμ hχ hχc hχΩ hχ0 hS
  · intro S hS ih
    have htotal :
        Integrable (fun τ : ℂ => ∫ y, fibreRestrict χ τ y * fibreRestrict (fun _ => (1 : ℝ)) τ y ∂(μ τ)) ∧
        (∫ q, χ q * (1 : ℝ) ∂ν) = (∫ τ : ℂ,
          ∫ y, fibreRestrict χ τ y * fibreRestrict (fun _ => (1 : ℝ)) τ y ∂(μ τ)) / Real.pi := by
      simpa only [indicator_univ] using
        slicing_open_indicator hlast hν hμ hχ hχc hχΩ hχ0 isOpen_univ
    have hcomp : W Sᶜ = (fun _ => (1 : ℝ)) - W S := by
      funext q
      by_cases h : q ∈ S <;> simp [W, h]
    dsimp only [P]
    rw [hcomp]
    exact slicing_sub (C := 1) (D := 1) hν hμ hχ hχc hχΩ measurable_const (hWm S hS)
      (fun _ => by simp) (hWb S) htotal ih
  · intro S hd hS ih
    let H : ℕ → Set (ComplexModel (n + 1)) := fun k => ⋃ i ∈ Finset.range k, S i
    have hHm (k : ℕ) : MeasurableSet (H k) :=
      MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => hS i
    have hHlim (q : ComplexModel (n + 1)) :
        Tendsto (fun k => W (H k) q) atTop (𝓝 (W (⋃ i, S i) q)) := by
      by_cases hq : q ∈ ⋃ i, S i
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hq
        have hevent : ∀ᶠ k : ℕ in atTop, W (H k) q = 1 := by
          filter_upwards [eventually_ge_atTop (i + 1)] with k hk
          have hmem : q ∈ H k := mem_iUnion.mpr ⟨i, mem_iUnion.mpr
            ⟨Finset.mem_range.mpr (by omega), hi⟩⟩
          simp only [W, indicator_of_mem hmem]
        simpa only [W, indicator_of_mem hq] using
          (tendsto_const_nhds (x := (1 : ℝ))).congr' (hevent.mono fun _ hk => hk.symm)
      · have hnot (k : ℕ) : q ∉ H k := by
          intro hy
          obtain ⟨i, hi⟩ := mem_iUnion.mp hy
          obtain ⟨_, hqi⟩ := mem_iUnion.mp hi
          exact hq (mem_iUnion.mpr ⟨i, hqi⟩)
        have heq : (fun k => W (H k) q) = fun _ => (0 : ℝ) := by
          funext k
          simp only [W, indicator_of_notMem (hnot k)]
        rw [heq]
        simpa only [W, indicator_of_notMem hq] using tendsto_const_nhds (x := (0 : ℝ))
    apply slicing_of_bounded_limit hlast hν hμ hχ hχc hχΩ hχ0
      (fun k => hWm (H k) (hHm k)) (fun k q => hWb (H k) q) hHlim
    intro k
    have hs : (↑(Finset.range k) : Set ℕ).PairwiseDisjoint S := by
      intro i _ j _ hij
      exact hd hij
    have hsum : W (H k) = fun q => ∑ i ∈ Finset.range k, W (S i) q := by
      funext q
      exact Finset.indicator_biUnion_apply (Finset.range k) S hs q
    rw [hsum]
    exact slicing_finsetSum (Finset.range k) hν hμ hχ hχc hχΩ
      (fun i _ => hWm (S i) (hS i)) (fun i _ q => hWb (S i) q) (fun i _ => ih i)

private theorem slicing_const_mul (c : ℝ) {F : ComplexModel (n + 1) → ℝ}
    (hF : Integrable (fun τ : ℂ => ∫ y, fibreRestrict χ τ y * fibreRestrict F τ y ∂(μ τ)) ∧
      (∫ q, χ q * F q ∂ν) = (∫ τ : ℂ,
        ∫ y, fibreRestrict χ τ y * fibreRestrict F τ y ∂(μ τ)) / Real.pi) :
    Integrable (fun τ : ℂ => ∫ y, fibreRestrict χ τ y *
      fibreRestrict (fun q => c * F q) τ y ∂(μ τ)) ∧
      (∫ q, χ q * (c * F q) ∂ν) = (∫ τ : ℂ,
        ∫ y, fibreRestrict χ τ y *
          fibreRestrict (fun q => c * F q) τ y ∂(μ τ)) / Real.pi := by
  have hleft : (fun q => χ q * (c * F q)) = fun q => c * (χ q * F q) := by
    funext q
    ring
  have hinner (τ : ℂ) : (∫ y, fibreRestrict χ τ y *
      fibreRestrict (fun q => c * F q) τ y ∂(μ τ)) =
      c * (∫ y, fibreRestrict χ τ y * fibreRestrict F τ y ∂(μ τ)) := by
    have heq : (fun y => fibreRestrict χ τ y * fibreRestrict (fun q => c * F q) τ y) =
        fun y => c * (fibreRestrict χ τ y * fibreRestrict F τ y) := by
      funext y
      dsimp only [fibreRestrict]
      ring
    rw [heq, integral_const_mul]
  have hout : (fun τ : ℂ => ∫ y, fibreRestrict χ τ y *
      fibreRestrict (fun q => c * F q) τ y ∂(μ τ)) =
      fun τ => c * (∫ y, fibreRestrict χ τ y * fibreRestrict F τ y ∂(μ τ)) := funext hinner
  refine ⟨?_, ?_⟩
  · rw [hout]
    exact hF.1.const_mul c
  · rw [hleft, integral_const_mul, hout, integral_const_mul, hF.2]
    ring

private theorem slicing_simpleFunc
    (hlast : u (Fin.last n) = lastNormSq n) (hν : IsBTLimit Ω u ν)
    (hμ : ∀ τ, IsBTLimit (fibreOpens Ω τ) (fibreTuple u τ) (μ τ))
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hχΩ : tsupport χ ⊆ Ω)
    (hχ0 : ∀ q, 0 ≤ χ q) (sf : SimpleFunc (ComplexModel (n + 1)) ℝ) :
    Integrable (fun τ : ℂ => ∫ y, fibreRestrict χ τ y * fibreRestrict sf τ y ∂(μ τ)) ∧
      (∫ q, χ q * sf q ∂ν) = (∫ τ : ℂ,
        ∫ y, fibreRestrict χ τ y * fibreRestrict sf τ y ∂(μ τ)) / Real.pi := by
  classical
  let F : ℝ → ComplexModel (n + 1) → ℝ :=
    fun c q => c * (sf ⁻¹' {c}).indicator (fun _ => (1 : ℝ)) q
  have hFm (c : ℝ) : Measurable (F c) :=
    measurable_const.mul (measurable_const.indicator (sf.measurableSet_preimage {c}))
  have hFb (c : ℝ) (q : ComplexModel (n + 1)) : ‖F c q‖ ≤ ‖c‖ := by
    by_cases h : q ∈ sf ⁻¹' {c} <;> simp [F, h]
  have hF (c : ℝ) :
      Integrable (fun τ : ℂ => ∫ y, fibreRestrict χ τ y * fibreRestrict (F c) τ y ∂(μ τ)) ∧
      (∫ q, χ q * F c q ∂ν) = (∫ τ : ℂ,
        ∫ y, fibreRestrict χ τ y * fibreRestrict (F c) τ y ∂(μ τ)) / Real.pi :=
    slicing_const_mul c (integral_indicator_isBTLimit_eq_fibre hlast hν hμ hχ hχc hχΩ hχ0
      (sf.measurableSet_preimage {c})).2.2
  have hsum : (fun q => ∑ c ∈ sf.range, F c q) = sf := by
    funext q
    rw [Finset.sum_eq_single (sf q)]
    · simp [F]
    · intro c _ hne
      have hnot : q ∉ sf ⁻¹' {c} := by simpa only [mem_preimage, mem_singleton_iff] using hne.symm
      simp [F, hnot]
    · intro hn
      exact (hn (sf.mem_range_self q)).elim
  have hs := slicing_finsetSum sf.range hν hμ hχ hχc hχΩ
    (fun c _ => hFm c) (fun c _ q => hFb c q) (fun c _ => hF c)
  have hsum_apply (q : ComplexModel (n + 1)) : (∑ c ∈ sf.range, F c q) = sf q :=
    congrFun hsum q
  simpa only [hsum, hsum_apply] using hs

/-- Actual bounded Borel signed slicing, including genuinely produced
integrability on the joint space, every fibre and the base. -/
theorem integral_mul_borel_isBTLimit_eq_fibre
    (hlast : u (Fin.last n) = lastNormSq n) (hν : IsBTLimit Ω u ν)
    (hμ : ∀ τ, IsBTLimit (fibreOpens Ω τ) (fibreTuple u τ) (μ τ))
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hχΩ : tsupport χ ⊆ Ω)
    (hχ0 : ∀ q, 0 ≤ χ q) {F : ComplexModel (n + 1) → ℝ}
    (hFm : Measurable F) {C : ℝ} (hFb : ∀ q, ‖F q‖ ≤ C) :
    Integrable (fun q => χ q * F q) ν ∧
    (∀ τ : ℂ, Integrable (fun y => fibreRestrict χ τ y * fibreRestrict F τ y) (μ τ)) ∧
    Integrable (fun τ : ℂ => ∫ y, fibreRestrict χ τ y * fibreRestrict F τ y ∂(μ τ)) ∧
      (∫ q, χ q * F q ∂ν) = (∫ τ : ℂ,
        ∫ y, fibreRestrict χ τ y * fibreRestrict F τ y ∂(μ τ)) / Real.pi := by
  refine ⟨integrable_test_mul hν hχ hχc hχΩ hFm hFb,
    fun τ => integrable_fibre_test_mul hμ hχ hχc hχΩ hFm hFb τ, ?_⟩
  have hC : 0 ≤ C := (norm_nonneg (F 0)).trans (hFb 0)
  have hFs := hFm.stronglyMeasurable
  exact slicing_of_bounded_limit hlast hν hμ hχ hχc hχΩ hχ0
    (fun k => (hFs.approxBounded C k).measurable)
    (fun k q => hFs.norm_approxBounded_le hC k q)
    (fun q => hFs.tendsto_approxBounded_of_norm_le (hFb q))
    (fun k => slicing_simpleFunc hlast hν hμ hχ hχc hχΩ hχ0 (hFs.approxBounded C k))

end

end SGPT.Foundations.Analysis.Pending.BedfordTaylorBorelFibreSlicing
