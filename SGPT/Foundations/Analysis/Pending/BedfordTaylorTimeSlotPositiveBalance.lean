import SGPT.Foundations.Analysis.Pending.BedfordTaylorTimeSlot
import SGPT.Foundations.Analysis.Pending.VaguePortmanteau

set_option autoImplicit false

/-! # Positive measure balance from the actual bounded BT time-slot defect -/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff

namespace SGPT.Foundations.Analysis.Pending.BedfordTaylorTimeSlotPositiveBalance

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere BedfordTaylor
  BedfordTaylorTimeSlot BedfordTaylorFibreSlicing MixedMongeAmpere MixedDensityRankOneSlot

noncomputable section

variable {n : ℕ}

/-- A continuous real density preserves genuine finite mass on the compact subsets of an open domain. -/
theorem withDensity_ofReal_finiteOnCompacts {Ω : Opens (ComplexModel n)}
    {ν : Measure (ComplexModel n)}
    (hν : ∀ K, IsCompact K → K ⊆ Ω → ν K < ⊤)
    {c : ComplexModel n → ℝ} (hc : Continuous c) :
    ∀ K, IsCompact K → K ⊆ Ω → (ν.withDensity (fun q => ENNReal.ofReal (c q))) K < ⊤ := by
  intro K hK hKΩ
  obtain ⟨R, hR⟩ := (hK.image hc).bddAbove
  have hb : ∀ q ∈ K, c q ≤ R := fun q hq => hR ⟨q, hq, rfl⟩
  rw [withDensity_apply _ hK.measurableSet]
  refine (lintegral_mono_ae (g := fun _ => ENNReal.ofReal R) ?_).trans_lt ?_
  · exact (ae_restrict_mem hK.measurableSet).mono fun q hq => ENNReal.ofReal_le_ofReal (hb q hq)
  · rw [setLIntegral_const]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hν K hK hKΩ)

private theorem integrable_test_mul_continuous {Ω : Opens (ComplexModel n)}
    {ν : Measure (ComplexModel n)}
    (hν : ∀ K, IsCompact K → K ⊆ Ω → ν K < ⊤)
    (φ : 𝓓(Ω, ℝ)) {c : ComplexModel n → ℝ} (hc : Continuous c) :
    Integrable (fun q => φ q * c q) ν := by
  have hs : tsupport (fun q => φ q * c q) ⊆ tsupport φ := tsupport_mul_subset_left
  exact VaguePortmanteau.integrable_of_tsupport_subset hν
    (φ.continuous.mul hc)
    (φ.hasCompactSupport.of_isClosed_subset (isClosed_tsupport _) hs)
    (hs.trans φ.tsupport_subset)

private theorem integral_density_test {Ω : Opens (ComplexModel n)}
    {ν : Measure (ComplexModel n)} {c : ComplexModel n → ℝ} (hc : Continuous c)
    (φ : 𝓓(Ω, ℝ)) :
    (∫ q, φ q ∂ν.withDensity (fun q => ENNReal.ofReal (c q))) =
      ∫ q, φ q * max (c q) 0 ∂ν := by
  rw [integral_withDensity_eq_integral_toReal_smul hc.measurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal', smul_eq_mul, mul_comm]

/-- Replacing the last slot by an actual locally bounded PSH function produces an actual locally bounded mixed tuple. -/
theorem isLocallyBoundedMixedPshOn_update_last
    {Ω : Opens (ComplexModel (n + 1))}
    {v : Fin (n + 1) → ComplexModel (n + 1) → ℝ}
    (hv : IsLocallyBoundedMixedPshOn Ω v)
    {s : ComplexModel (n + 1) → ℝ} (hs : IsLocallyBoundedPshOn Ω s) :
    IsLocallyBoundedMixedPshOn Ω (Function.update v (Fin.last n) s) := by
  classical
  intro i
  by_cases hi : i = Fin.last n
  · subst i
    simpa using hs
  · simpa [Function.update_of_ne hi] using hv i

/-- Genuine bounded BT limits satisfy a positive measure balance; no signed measure or target balance is assumed. -/
theorem restrict_add_withDensity_eq_of_isBTLimit_timeLift
    {Ω : Opens (ComplexModel (n + 1))}
    {v : Fin (n + 1) → ComplexModel (n + 1) → ℝ}
    {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    {p : ComplexModel (n + 1) → ℝ} (hp : IsSmoothPsdOn Ω p)
    (hψp : IsSmoothPsdOn Ω fun q => timeLift n ψ q + p q)
    {νa νb νE : Measure (ComplexModel (n + 1))}
    (ha : IsBTLimit Ω (Function.update v (Fin.last n) fun q => timeLift n ψ q + p q) νa)
    (hb : IsBTLimit Ω (Function.update v (Fin.last n) p) νb)
    (hE : IsBTLimit Ω (Function.update v (Fin.last n) (lastNormSq n)) νE) :
    (νa + νE.withDensity (fun q => ENNReal.ofReal (-timeLaplacian ψ (q (Fin.last n))))).restrict Ω =
      (νb + νE.withDensity (fun q => ENNReal.ofReal (timeLaplacian ψ (q (Fin.last n))))).restrict Ω := by
  let c : ComplexModel (n + 1) → ℝ := fun q => timeLaplacian ψ (q (Fin.last n))
  have hc : Continuous c := (continuous_timeLaplacian hψ).comp (lastCoordinate n).continuous
  have hcn : Continuous (fun q => -c q) := hc.neg
  have hfplus := withDensity_ofReal_finiteOnCompacts hE.2.1 hc
  have hfminus := withDensity_ofReal_finiteOnCompacts hE.2.1 hcn
  refine restrict_eq_of_testFunction_integral_eq ?_ ?_ ?_
  · intro K hK hKΩ
    rw [Measure.add_apply]
    exact ENNReal.add_lt_top.mpr ⟨ha.2.1 K hK hKΩ, hfminus K hK hKΩ⟩
  · intro K hK hKΩ
    rw [Measure.add_apply]
    exact ENNReal.add_lt_top.mpr ⟨hb.2.1 K hK hKΩ, hfplus K hK hKΩ⟩
  intro φ
  have hia : Integrable (fun q => φ q) νa :=
    VaguePortmanteau.integrable_of_tsupport_subset ha.2.1 φ.continuous φ.hasCompactSupport φ.tsupport_subset
  have hib : Integrable (fun q => φ q) νb :=
    VaguePortmanteau.integrable_of_tsupport_subset hb.2.1 φ.continuous φ.hasCompactSupport φ.tsupport_subset
  have hip : Integrable (fun q => φ q) (νE.withDensity (fun q => ENNReal.ofReal (c q))) :=
    VaguePortmanteau.integrable_of_tsupport_subset hfplus φ.continuous φ.hasCompactSupport φ.tsupport_subset
  have him : Integrable (fun q => φ q) (νE.withDensity (fun q => ENNReal.ofReal (-c q))) :=
    VaguePortmanteau.integrable_of_tsupport_subset hfminus φ.continuous φ.hasCompactSupport φ.tsupport_subset
  have hcp := integrable_test_mul_continuous hE.2.1 φ (hc.max (continuous_const (y := (0 : ℝ))))
  have hcm := integrable_test_mul_continuous hE.2.1 φ (hcn.max (continuous_const (y := (0 : ℝ))))
  have hd := integral_isBTLimit_timeLift_sub hψ hp hψp ha hb hE
    (w := fun _ => 1)
    (fun V _ => ⟨fun _ _ => 1, isDecApprox_const (isSmoothPsdOn_const V 1)⟩)
    φ.continuous φ.hasCompactSupport φ.tsupport_subset
  simp only [mul_one] at hd
  have hparts : (∫ q, φ q * max (c q) 0 ∂νE) -
      (∫ q, φ q * max (-c q) 0 ∂νE) = ∫ q, φ q * c q ∂νE := by
    rw [← integral_sub hcp hcm]
    congr 1
    funext q
    by_cases h : 0 ≤ c q
    · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h), mul_zero, sub_zero]
    · rw [max_eq_right (le_of_not_ge h), max_eq_left (neg_nonneg.mpr (le_of_not_ge h))]
      ring
  rw [integral_add_measure hia him, integral_add_measure hib hip,
    integral_density_test hcn φ, integral_density_test hc φ]
  change (∫ q, φ q ∂νa) + (∫ q, φ q * max (-c q) 0 ∂νE) =
    (∫ q, φ q ∂νb) + (∫ q, φ q * max (c q) 0 ∂νE)
  change (∫ q, φ q ∂νa) - (∫ q, φ q ∂νb) = ∫ q, φ q * c q ∂νE at hd
  linarith

/-- The genuine canonical bounded measures satisfy the positive time-slot balance, with all three measures independently constructed from actual PSH inputs. -/
theorem canonical_restrict_add_withDensity_timeLift
    {Ω : Opens (ComplexModel (n + 1))}
    {v : Fin (n + 1) → ComplexModel (n + 1) → ℝ}
    (hv : IsLocallyBoundedMixedPshOn Ω v)
    {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    {p : ComplexModel (n + 1) → ℝ} (hp : IsSmoothPsdOn Ω p)
    (hψp : IsSmoothPsdOn Ω fun q => timeLift n ψ q + p q) :
    ((canonicalMixedBedfordTaylorMeasure Ω
        (Function.update v (Fin.last n) fun q => timeLift n ψ q + p q)
        (isLocallyBoundedMixedPshOn_update_last hv hψp.isLocallyBoundedPshOn)) +
      (canonicalMixedBedfordTaylorMeasure Ω
        (Function.update v (Fin.last n) (lastNormSq n))
        (isLocallyBoundedMixedPshOn_update_last hv
          (isSmoothPsdOn_lastNormSq Ω).isLocallyBoundedPshOn)).withDensity
        (fun q => ENNReal.ofReal (-timeLaplacian ψ (q (Fin.last n))))).restrict Ω =
    ((canonicalMixedBedfordTaylorMeasure Ω
        (Function.update v (Fin.last n) p)
        (isLocallyBoundedMixedPshOn_update_last hv hp.isLocallyBoundedPshOn)) +
      (canonicalMixedBedfordTaylorMeasure Ω
        (Function.update v (Fin.last n) (lastNormSq n))
        (isLocallyBoundedMixedPshOn_update_last hv
          (isSmoothPsdOn_lastNormSq Ω).isLocallyBoundedPshOn)).withDensity
        (fun q => ENNReal.ofReal (timeLaplacian ψ (q (Fin.last n))))).restrict Ω :=
  restrict_add_withDensity_eq_of_isBTLimit_timeLift hψ hp hψp
    (IsLocalMixedBedfordTaylorMeasure.isBTLimit (canonicalMixedBedfordTaylorMeasure_spec Ω _ _))
    (IsLocalMixedBedfordTaylorMeasure.isBTLimit (canonicalMixedBedfordTaylorMeasure_spec Ω _ _))
    (IsLocalMixedBedfordTaylorMeasure.isBTLimit (canonicalMixedBedfordTaylorMeasure_spec Ω _ _))

end

end SGPT.Foundations.Analysis.Pending.BedfordTaylorTimeSlotPositiveBalance
