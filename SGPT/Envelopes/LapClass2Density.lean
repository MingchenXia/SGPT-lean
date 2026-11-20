import SGPT.Foundations.Analysis.Pending.SmoothTestMeasureSeparation
import SGPT.Foundations.Analysis.TestLeviPairing
import SGPT.Foundations.Analysis.FirstPass.ComplexManifold

/-!
# Bounded distributions of order zero have bounded densities

Lane LAP-CLASS2 (`claude-lap-class2`, node `lap-class2:density`).  Let `U ⊆ ℂⁿ` be open, `g`
continuous on `U` and `v ∈ ℂⁿ`.  If the distributional Levi form `∂_v∂̄_v g` is dominated by a
continuous weight `m ≥ 0`,

  `|∫ g ∂_v∂̄_v φ| ≤ ∫ m φ` for every smooth `φ ≥ 0` with compact support in `U`,

then `∂_v∂̄_v g` is a measurable function `ρ` with `|ρ| ≤ m` on `U`
(`exists_levi_density_of_abs_le`).  This is the step "an `L^∞` density for a bounded
distribution" used to compare the book's `C^{1,1̄}(X)` with the class of bounded complex Hessians
in dimension one (`SGPT.Envelopes.LapClass2Chart`, `SGPT.Envelopes.LapClass2Dim1`).

## Proof (Riesz–Markov and Radon–Nikodym, no Calderón–Zygmund theory)

`S = m + ∂_v∂̄_v g` is a positive distribution on `U`, so it is integration against a locally
finite measure `ν` (TN `PositiveDistribution.exists_regular_measure`, Riesz–Markov–Kakutani).
Since also `S ≤ 2m`, the smooth-test comparison of TN (`Measure.le_of_testFunction_integral_le`)
gives `ν ≤ 2m · dV` on `U`; hence `ν = r dV` with `0 ≤ r ≤ 2m` almost everywhere (Radon–Nikodym),
and `ρ = r - m` (clamped to `[-m, m]` on the null set where this fails) is the density.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff ENNReal Distributions

namespace SGPT.Envelopes.LapClass

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass

variable {n : ℕ}

/-- **A dominated Levi distribution has a bounded density.**  If `|∫ g ∂_v∂̄_v φ| ≤ ∫ m φ` for all
smooth `φ ≥ 0` with compact support in the open set `U` (`g`, `m` continuous on `U`, `m ≥ 0`), then
there is a measurable `ρ` with `|ρ| ≤ m` on `U` and `∫ g ∂_v∂̄_v φ = ∫ ρ φ` for every smooth `φ`
with compact support in `U`. -/
theorem exists_levi_density_of_abs_le {U : Set (ComplexModel n)} (hU : IsOpen U)
    {g m : ComplexModel n → ℝ} (hg : ContinuousOn g U) (hm : ContinuousOn m U)
    (hm0 : ∀ z ∈ U, 0 ≤ m z) (v : ComplexModel n)
    (hb : ∀ φ : ComplexModel n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      (∀ z, 0 ≤ φ z) → |∫ z, g z * leviForm φ z v| ≤ ∫ z, m z * φ z) :
    ∃ ρ : ComplexModel n → ℝ, Measurable ρ ∧ (∀ z ∈ U, |ρ z| ≤ m z) ∧
      ∀ φ : ComplexModel n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
        ∫ z, g z * leviForm φ z v = ∫ z, ρ z * φ z := by
  classical
  set Ω : Opens (ComplexModel n) := ⟨U, hU⟩ with hΩ
  have hΩU : (Ω : Set (ComplexModel n)) = U := rfl
  have hgl : LocallyIntegrableOn g (Ω : Set (ComplexModel n)) volume :=
    hg.locallyIntegrableOn hU.measurableSet
  have hml : LocallyIntegrableOn m (Ω : Set (ComplexModel n)) volume :=
    hm.locallyIntegrableOn hU.measurableSet
  set T : 𝓓'(Ω, ℝ) := distributionalLeviCLM v (regularDistribution volume g hgl) with hTdef
  set Tm : 𝓓'(Ω, ℝ) := regularDistribution volume m hml with hTmdef
  have hT : ∀ φ : 𝓓(Ω, ℝ), T φ = ∫ z, g z * leviForm φ z v := fun φ =>
    distributionalLeviCLM_regularDistribution_apply hgl φ v
  have hTm : ∀ φ : 𝓓(Ω, ℝ), Tm φ = ∫ z, m z * φ z := fun φ => by
    rw [hTmdef, regularDistribution_apply]
    exact integral_congr_ae (Eventually.of_forall fun z => mul_comm _ _)
  have hbφ : ∀ φ : 𝓓(Ω, ℝ), (∀ z, 0 ≤ φ z) → |T φ| ≤ Tm φ := fun φ hφ => by
    rw [hT, hTm]
    exact hb φ φ.contDiff φ.hasCompactSupport φ.tsupport_subset hφ
  -- the positive distribution `m + ∂_v∂̄_v g` and its Riesz measure
  have hpos : PositiveDistribution (Tm + T) := by
    intro φ hφ
    rw [add_apply]
    have := hbφ φ hφ
    linarith [neg_abs_le (T φ)]
  obtain ⟨ν, -, hνloc, hν⟩ := hpos.exists_regular_measure
  have := hνloc
  -- the comparison measure `2m · dV` on `U`
  set m' : ComplexModel n → ℝ := U.piecewise m 0 with hm'def
  have hm'meas : Measurable m' := hm.measurable_piecewise continuousOn_const hU.measurableSet
  have hm'U : ∀ z ∈ U, m' z = m z := fun z hz => Set.piecewise_eq_of_mem _ _ _ hz
  have hm'0 : ∀ z, 0 ≤ m' z := fun z => by
    by_cases hz : z ∈ U
    · rw [hm'U z hz]; exact hm0 z hz
    · show U.piecewise m 0 z ≥ 0
      rw [Set.piecewise_eq_of_notMem _ _ _ hz]; rfl
  set d : ComplexModel n → ℝ≥0∞ := U.indicator fun z => ENNReal.ofReal (2 * m' z) with hddef
  have hdmeas : Measurable d :=
    ((hm'meas.const_mul 2).ennreal_ofReal).indicator hU.measurableSet
  set μE : Measure (ComplexModel n) := volume.withDensity d with hμEdef
  have hμE' : μE = (volume.restrict U).withDensity fun z => ENNReal.ofReal (2 * m' z) :=
    withDensity_indicator hU.measurableSet _
  have hemb : MeasurableEmbedding (Subtype.val : Ω → ComplexModel n) :=
    MeasurableEmbedding.subtype_coe hU.measurableSet
  have hμEU : μE.restrict U = μE := by
    refine Measure.restrict_eq_self_of_ae_mem ?_
    rw [hμE']
    exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hU.measurableSet)
  -- `μE` is finite on compact subsets of `U`
  have hμEK : ∀ K : Set (ComplexModel n), IsCompact K → K ⊆ U → μE K < ⊤ := by
    intro K hK hKU
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hm.mono hKU)
    rw [hμEdef, withDensity_apply' _ K]
    calc ∫⁻ z in K, d z ≤ ∫⁻ _z in K, ENNReal.ofReal (2 * C) := by
          refine setLIntegral_mono measurable_const fun z hz => ?_
          rw [hddef, indicator_of_mem (hKU hz), hm'U z (hKU hz)]
          refine ENNReal.ofReal_le_ofReal ?_
          have := hC z hz
          rw [Real.norm_eq_abs] at this
          linarith [le_abs_self (m z)]
      _ = ENNReal.ofReal (2 * C) * volume K := setLIntegral_const _ _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top
  set μΩ : Measure Ω := μE.comap Subtype.val with hμΩdef
  have hμΩloc : IsLocallyFiniteMeasure μΩ := by
    have : LocallyCompactSpace Ω := Ω.isOpen.locallyCompactSpace
    refine ⟨fun x => ?_⟩
    obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds x
    refine ⟨K, hKn, ?_⟩
    rw [hμΩdef, hemb.comap_apply]
    exact hμEK _ (hK.image continuous_subtype_val) (image_subset_iff.mpr fun y _ => y.2)
  have := hμΩloc
  have hmapΩ : μΩ.map Subtype.val = μE := by
    rw [hμΩdef, hemb.map_comap, Subtype.range_coe]
    exact hμEU
  -- integrals against `μE`
  have hint_μE : ∀ φ : ComplexModel n → ℝ, tsupport φ ⊆ U →
      ∫ z, φ z ∂μE = ∫ z, 2 * m z * φ z := by
    intro φ hφU
    rw [hμE', integral_withDensity_eq_integral_toReal_smul
      ((hm'meas.const_mul 2).ennreal_ofReal)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
      rw [image_eq_zero_of_notMem_tsupport fun h => hz (hφU h), smul_zero]]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [smul_eq_mul]
    by_cases hz : z ∈ U
    · rw [ENNReal.toReal_ofReal (by linarith [hm'0 z]), hm'U z hz]
    · rw [image_eq_zero_of_notMem_tsupport fun h => hz (hφU h), mul_zero, mul_zero]
  -- `ν ≤ 2m · dV` on `U`
  have hle : ν ≤ μΩ := by
    refine SGPT.Foundations.Analysis.Pending.SmoothTestMeasureSeparation.Measure.le_of_testFunction_integral_le
      μΩ ν fun φ hφ => ?_
    rw [hν φ, ← hemb.integral_map, hmapΩ, hint_μE φ φ.tsupport_subset,
      add_apply]
    have h1 := hbφ φ hφ
    have h2 : ∫ z, 2 * m z * φ z = 2 * Tm φ := by
      rw [hTm, ← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun z => by ring)
    rw [h2]
    linarith [le_abs_self (T φ)]
  -- the measure on `ℂⁿ` and its Radon–Nikodym density
  set νE : Measure (ComplexModel n) := ν.map Subtype.val with hνEdef
  have hνEle : νE ≤ μE := hmapΩ ▸ Measure.map_mono hle measurable_subtype_coe
  have : SigmaFinite μE := by
    rw [hμE']
    exact SigmaFinite.withDensity_ofReal _
  have : SigmaFinite νE := Measure.sigmaFinite_of_le μE hνEle
  have hνEac : νE ≪ volume :=
    (Measure.absolutelyContinuous_of_le hνEle).trans (withDensity_absolutelyContinuous _ _)
  set r : ComplexModel n → ℝ≥0∞ := νE.rnDeriv volume with hrdef
  have hrmeas : Measurable r := Measure.measurable_rnDeriv _ _
  have hrd : r ≤ᵐ[volume] d := by
    refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite hrmeas fun s hs _ => ?_
    rw [hrdef, Measure.setLIntegral_rnDeriv hνEac, ← withDensity_apply _ hs]
    exact hνEle s
  have hrfin : ∀ᵐ z ∂volume, r z < ⊤ := Measure.rnDeriv_lt_top _ _
  -- the clamped density
  set ρ : ComplexModel n → ℝ := U.piecewise
    (fun z => max (-m' z) (min ((r z).toReal - m' z) (m' z))) 0 with hρdef
  have hρmeas : Measurable ρ :=
    ((hm'meas.neg.max ((hrmeas.ennreal_toReal.sub hm'meas).min hm'meas))).piecewise
      hU.measurableSet measurable_const
  have hρU : ∀ z ∈ U, |ρ z| ≤ m z := by
    intro z hz
    rw [hρdef, piecewise_eq_of_mem _ _ _ hz, ← hm'U z hz, abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith [hm'0 z]) (min_le_right _ _)⟩
  have hρae : ∀ᵐ z ∂volume, z ∈ U → ρ z = (r z).toReal - m' z := by
    filter_upwards [hrd, hrfin] with z hz hzfin hzU
    rw [hρdef, piecewise_eq_of_mem _ _ _ hzU]
    have hd : d z = ENNReal.ofReal (2 * m' z) := by rw [hddef, indicator_of_mem hzU]
    have h1 : (r z).toReal ≤ 2 * m' z := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hz.trans_eq hd)
      rwa [ENNReal.toReal_ofReal (by linarith [hm'0 z])] at this
    have h0 : 0 ≤ (r z).toReal := ENNReal.toReal_nonneg
    rw [min_eq_left (by linarith), max_eq_right (by linarith)]
  refine ⟨ρ, hρmeas, hρU, fun φ hφ hφc hφU => ?_⟩
  set ψ : 𝓓(Ω, ℝ) := ⟨φ, hφ, hφc, hφU⟩ with hψdef
  -- bounds on the support of `φ`
  obtain ⟨C, hC⟩ := hφc.isCompact.exists_bound_of_continuousOn (hm.mono hφU)
  have hφcont : Continuous φ := hφ.continuous
  have hφint : Integrable φ := hφcont.integrable_of_hasCompactSupport hφc
  have hbd : ∀ (h : ComplexModel n → ℝ), (∀ z ∈ U, |h z| ≤ m z) → Measurable h →
      Integrable (fun z => h z * φ z) := by
    intro h hh hhm
    refine (hφint.norm.const_mul C).mono' (hhm.aestronglyMeasurable.mul
      hφcont.aestronglyMeasurable) (Eventually.of_forall fun z => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    by_cases hz : z ∈ tsupport φ
    · have h1 := hh z (hφU hz)
      have h2 := hC z hz
      rw [Real.norm_eq_abs] at h2
      exact mul_le_mul_of_nonneg_right (h1.trans ((le_abs_self _).trans h2)) (abs_nonneg _)
    · rw [image_eq_zero_of_notMem_tsupport hz, abs_zero, mul_zero, mul_zero]
  have hm'int : Integrable (fun z => m' z * φ z) := hbd m'
    (fun z hz => by rw [hm'U z hz, abs_of_nonneg (hm0 z hz)]) hm'meas
  -- `∂_v∂̄_v g = ν - m` on `φ`
  have hνφ : ∫ x : Ω, ψ x ∂ν = ∫ z, (r z).toReal * φ z := by
    rw [← hemb.integral_map]
    change ∫ z, ψ z ∂νE = _
    rw [← Measure.withDensity_rnDeriv_eq νE volume hνEac,
      integral_withDensity_eq_integral_toReal_smul hrmeas hrfin]
    rfl
  have hsplit : ∫ z, (r z).toReal * φ z = (∫ z, ρ z * φ z) + ∫ z, m' z * φ z := by
    have h1 : ∫ z, (r z).toReal * φ z = ∫ z, (ρ z * φ z + m' z * φ z) := by
      refine integral_congr_ae ?_
      filter_upwards [hρae] with z hz
      by_cases hzU : z ∈ U
      · rw [hz hzU]; ring
      · rw [image_eq_zero_of_notMem_tsupport fun h => hzU (hφU h)]; ring
    rw [h1, integral_add (hbd ρ hρU hρmeas) hm'int]
  have hmm' : ∫ z, m' z * φ z = ∫ z, m z * φ z := by
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    show m' z * φ z = m z * φ z
    by_cases hzU : z ∈ U
    · rw [hm'U z hzU]
    · rw [image_eq_zero_of_notMem_tsupport fun h => hzU (hφU h), mul_zero, mul_zero]
  have hS := hν ψ
  have hψφ' : (⇑ψ : ComplexModel n → ℝ) = φ := rfl
  rw [add_apply, hT, hTm, hνφ, hsplit, hmm', hψφ'] at hS
  linarith

end SGPT.Envelopes.LapClass
