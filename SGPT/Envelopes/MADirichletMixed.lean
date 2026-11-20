import SGPT.Envelopes.MADirichletSubsolution

/-!
# Dinew's inequality for bounded functions with continuous densities on open sets

Xia, *Foundations of pluripotential theory* (FPT), `cor:bounded-multifactor-continuous-density`:
let `u₁, …, uₙ` be locally bounded plurisubharmonic on an open set `Ω ⊆ ℂⁿ`, `n ≥ 1`, and
`f₁, …, fₙ ≥ 0` continuous on `Ω` with `(ddᶜuᵢ)ⁿ ≥ fᵢ ηⁿ` (`η = ddᶜ|z|²`, `ηⁿ = n!/πⁿ dV`). Then
`ddᶜu₁ ∧ ⋯ ∧ ddᶜuₙ ≥ (∏ᵢ fᵢ^{1/n}) ηⁿ` on `Ω` (`mixed_ge_withDensity`).

S57 (`SGPT.NPP.LogConcavityDinew.mixedBedfordTaylor_ge_on_ball`) proves the case of constant
positive densities on a ball `B(x₀, R/4)` with `B̄(x₀, R) ⊆ Ω`. Near a point where all `fᵢ` are
positive the densities are bounded below by constants close to their values, the constant case
applies on a small ball, and the local bounds glue (`withDensity_le_of_forall_lt`); where some
`fᵢ` vanishes the bound is trivial. In particular, constant densities on an arbitrary open set
(for instance the interior of a cube, as in FPT's proof of
`thm:bounded-multifactor-common-measure`, Step 2) are covered.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal

namespace SGPT.Envelopes.MADirichlet

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.MixedMongeAmpere
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.MongeAmpere
open SGPT.Foundations.Analysis.Pending.MixedMongeAmpere SGPT.Foundations.Analysis.Pending.MixedNonPluripolar
open SGPT.NPP.LogConcavityDinew

variable {n : ℕ}

/-- **Dinew's inequality for bounded functions with continuous densities** (FPT
`cor:bounded-multifactor-continuous-density`). -/
theorem mixed_ge_withDensity (hn : 0 < n) {Ω : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → ℝ} (hu : IsLocallyBoundedMixedPshOn Ω u)
    {f : Fin n → ComplexModel n → ℝ} (hf : ∀ i, ContinuousOn (f i) Ω)
    (hf0 : ∀ i, ∀ z ∈ Ω, 0 ≤ f i z)
    (hμ : ∀ i, (volume.restrict (Ω : Set (ComplexModel n))).withDensity
        (fun z => ENNReal.ofReal (mongeAmpereConst n * f i z)) ≤
      canonicalBedfordTaylorMeasure Ω (u i) (hu i)) :
    (volume.restrict (Ω : Set (ComplexModel n))).withDensity
        (fun z => ENNReal.ofReal (mongeAmpereConst n * ∏ i, f i z ^ ((n : ℝ)⁻¹))) ≤
      canonicalMixedBedfordTaylorMeasure Ω u hu := by
  have hninv : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
  have hg : ContinuousOn (fun z => mongeAmpereConst n * ∏ i, f i z ^ ((n : ℝ)⁻¹)) Ω :=
    continuousOn_const.mul (continuousOn_finsetProd _ fun i _ =>
      (hf i).rpow_const fun _ _ => Or.inr hninv)
  refine withDensity_le_of_forall_lt hg fun x hx t ht => ?_
  obtain ⟨ε, hε, hεΩ⟩ := Metric.isOpen_iff.mp Ω.isOpen x hx
  rcases le_or_gt t 0 with ht0 | ht0
  · refine ⟨ε, hε, hεΩ, ?_⟩
    rw [ENNReal.ofReal_of_nonpos ht0, zero_smul]
    exact Measure.zero_le _
  -- all densities are positive at `x`
  have hpos : ∀ i, 0 < f i x := by
    intro i
    by_contra hi
    have h0 : f i x = 0 := le_antisymm (not_lt.mp hi) (hf0 i x hx)
    have : ∏ j, f j x ^ ((n : ℝ)⁻¹) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by
        rw [h0, Real.zero_rpow (inv_ne_zero (by exact_mod_cast hn.ne'))])
    rw [this, mul_zero] at ht
    linarith
  -- constants slightly below the values at `x`
  set φ : ℝ → ℝ := fun δ => mongeAmpereConst n * ∏ i, (f i x - δ) ^ ((n : ℝ)⁻¹) with hφ
  have hφc : ContinuousAt φ 0 := by
    refine continuousAt_const.mul ?_
    have h : ContinuousOn (fun δ : ℝ => ∏ i, (f i x - δ) ^ ((n : ℝ)⁻¹)) univ :=
      continuousOn_finsetProd _ fun i _ =>
        ((continuous_const.sub continuous_id).continuousOn).rpow_const fun _ _ => Or.inr hninv
    exact h.continuousAt univ_mem
  have hφ0 : φ 0 = mongeAmpereConst n * ∏ i, f i x ^ ((n : ℝ)⁻¹) := by simp [hφ]
  have hev : ∀ᶠ δ in 𝓝 (0 : ℝ), t < φ δ ∧ ∀ i, δ < f i x := by
    refine (hφc.eventually (lt_mem_nhds (by rw [hφ0]; exact ht))).and ?_
    exact eventually_all.mpr fun i => eventually_lt_nhds (hpos i)
  have hev' : ∀ᶠ δ in 𝓝[Ioi (0 : ℝ)] 0, (t < φ δ ∧ ∀ i, δ < f i x) ∧ δ ∈ Ioi (0 : ℝ) :=
    (hev.filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
  obtain ⟨δ, ⟨hδt, hδf⟩, hδ⟩ := hev'.exists
  have hδ0 : (0 : ℝ) < δ := hδ
  set c : Fin n → ℝ := fun i => f i x - δ with hc
  have hcpos : ∀ i, 0 < c i := fun i => sub_pos.mpr (hδf i)
  -- a ball on which `fᵢ > cᵢ`
  have hnear : ∀ᶠ z in 𝓝 x, ∀ i, c i < f i z :=
    eventually_all.mpr fun i => ((hf i).continuousAt (Ω.isOpen.mem_nhds hx)).eventually
      (lt_mem_nhds (by simp only [hc]; linarith))
  obtain ⟨ρ₀, hρ₀, hρball⟩ := Metric.eventually_nhds_iff_ball.mp hnear
  set ρ : ℝ := min ρ₀ ε with hρdef
  have hρ : 0 < ρ := lt_min hρ₀ hε
  set Ω' : Opens (ComplexModel n) := ⟨Metric.ball x ρ, Metric.isOpen_ball⟩ with hΩ'
  have hΩ'Ω : Ω' ≤ Ω := fun z hz => hεΩ (Metric.ball_subset_ball (min_le_right _ _) hz)
  have hu' : IsLocallyBoundedMixedPshOn Ω' u := fun i => ⟨(hu i).1.mono hΩ'Ω, fun z hz => by
    obtain ⟨V, hzV, hVΩ, C, hC⟩ := (hu i).2 z (hΩ'Ω hz)
    exact ⟨V ⊓ Ω', ⟨hzV, hz⟩, inf_le_right, C, fun y hy => hC y hy.1⟩⟩
  have hμ' : ∀ i, ENNReal.ofReal (mongeAmpereConst n * c i) •
      volume.restrict (Ω' : Set (ComplexModel n)) ≤ canonicalBedfordTaylorMeasure Ω' (u i) (hu' i) := by
    intro i
    rw [← canonicalBedfordTaylorMeasure_restrict hΩ'Ω (hu i) (hu' i)]
    calc ENNReal.ofReal (mongeAmpereConst n * c i) • volume.restrict (Ω' : Set (ComplexModel n))
        = (volume.restrict (Ω' : Set (ComplexModel n))).withDensity
            (fun _ => ENNReal.ofReal (mongeAmpereConst n * c i)) := by rw [withDensity_const]
      _ ≤ (volume.restrict (Ω' : Set (ComplexModel n))).withDensity
            (fun z => ENNReal.ofReal (mongeAmpereConst n * f i z)) := by
          refine withDensity_mono ?_
          filter_upwards [ae_restrict_mem Ω'.isOpen.measurableSet] with z hz
          refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ mongeAmpereConst_pos.le)
          exact (hρball _ (Metric.ball_subset_ball (min_le_left _ _) hz) i).le
      _ = ((volume.restrict (Ω : Set (ComplexModel n))).withDensity
            (fun z => ENNReal.ofReal (mongeAmpereConst n * f i z))).restrict Ω' := by
          rw [restrict_withDensity Ω'.isOpen.measurableSet,
            Measure.restrict_restrict_of_subset hΩ'Ω]
      _ ≤ (canonicalBedfordTaylorMeasure Ω (u i) (hu i)).restrict Ω' :=
          Measure.restrict_mono subset_rfl (hμ i)
  have hcl : Metric.closedBall x (ρ / 2) ⊆ Ω' := Metric.closedBall_subset_ball (by linarith)
  have hloc := mixedBedfordTaylor_ge_on_ball hn hu' hcpos hμ' (by positivity : (0 : ℝ) < ρ / 2) hcl
  have hsub : Metric.ball x (ρ / 2 / 4) ⊆ (Ω' : Set (ComplexModel n)) :=
    Metric.ball_subset_ball (by linarith)
  rw [← canonicalMixedBedfordTaylorMeasure_restrict hΩ'Ω hu hu',
    Measure.restrict_restrict_of_subset hsub] at hloc
  refine ⟨ρ / 2 / 4, by positivity, hsub.trans hΩ'Ω, le_trans ?_ hloc⟩
  have hle : ENNReal.ofReal t ≤ ENNReal.ofReal (mongeAmpereConst n * ∏ i, c i ^ ((n : ℝ)⁻¹)) :=
    ENNReal.ofReal_le_ofReal hδt.le
  refine Measure.le_iff.mpr fun s hs => ?_
  rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
  exact mul_le_mul_of_nonneg_right hle zero_le

end SGPT.Envelopes.MADirichlet
