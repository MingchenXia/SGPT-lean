import SGPT.Foundations.Analysis.Pending.DistributionPotentialSmoothOverlap
import SGPT.Foundations.Analysis.Pending.LocalSmoothFormDensityGluing
import SGPT.Foundations.Analysis.Pending.LocalPotentials

set_option autoImplicit false

/-! Genuine local smooth regularity of any original signed scalar LF
with smooth closed native curvature. ENTIRE BP precedes this source.
All dimensions and actual Haar bases; no incoming regular/L1/class certificate. -/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Distributions ContDiff Topology
namespace SGPT.Foundations.Analysis.Pending.DistributionSmoothDdcRegularity
open FirstPass _root_.SGPT.Foundations.Analysis.LocalCurrents LelongPoincareDivisor
  FiniteGlobalCurrentSmoothLocalDensity LocalSmoothFormDensityGluing

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Genuine full calibration for ANY dimension/basis, including n0. -/
theorem restrict_smoothFormDistribution_eq_ddC_of_local_potential
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
    (θ : SmoothRealForm n M 2) (e : ComplexChart n M)
    {W : Opens (ComplexModel n)} (hW : W ≤ chartTarget e)
    (ρ : ComplexModel n → ℝ) (hpot : IsSmoothLocalPotential θ e W ρ) :
    restrictForm (smoothFormDistribution b θ e) hW =
      ddC (regularDistribution b.addHaar ρ
        (hpot.2.2.1.continuousOn.locallyIntegrableOn W.isOpen.measurableSet)) := by
  ext v φ
  have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
  have hint : Integrable (fun x => (TestFunction.monoCLM ℝ φ : 𝓓(chartTarget e, ℝ)) x •
      θ.coeff e x) b.addHaar :=
    TestFunction.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ)
      (smoothForm_coeff_locallyIntegrable b θ e) _
  rw [restrictForm_apply, hv, ddC_regularDistribution_apply_of_contDiffOn hpot.2.2.1,
    smoothFormDistribution_apply, ← formEvaluationCLM_apply,
    ← (formEvaluationCLM _).integral_comp_comm hint]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [formEvaluationCLM_apply]
  rw [congrFun (testFunction_inclusion_coe hW φ) x]
  by_cases hx : x ∈ W
  · rw [hpot.2.2.2 hx]
    rfl
  · rw [image_eq_zero_of_notMem_tsupport (fun h => hx (φ.tsupport_subset h))]
    simp

private theorem restrictForm_trans {Ω U V : Opens (ComplexModel n)} {r : ℕ}
    (hVU : V ≤ U) (hUΩ : U ≤ Ω) (A : DistributionForm Ω r) :
    restrictForm (restrictForm A hUΩ) hVU = restrictForm A (hVU.trans hUΩ) := by
  ext v φ
  change restrictDistribution (restrictDistribution (A v) hUΩ) hVU φ = _
  rw [restrictDistribution_trans]
  rfl

private theorem restrict_sub {Ω V : Opens (ComplexModel n)}
    (R Q : 𝓓'(Ω, ℝ)) (hV : V ≤ Ω) :
    restrictDistribution (R-Q) hV = restrictDistribution R hV - restrictDistribution Q hV := by
  ext φ
  rfl

private theorem restrict_regularForm {r : ℕ} {Ω V : Opens (ComplexModel n)}
    (μ : Measure (ComplexModel n))
    {a : ComplexModel n → (ComplexModel n) [⋀^Fin r]→L[ℝ] ℝ}
    (ha : LocallyIntegrableOn a Ω μ) (hV : V ≤ Ω) :
    restrictForm (regularFormDistribution μ a ha) hV =
      regularFormDistribution μ a (ha.mono_set hV) := by
  ext v φ
  rw [restrictForm_apply, regularFormDistribution_apply, regularFormDistribution_apply,
    testFunction_inclusion_coe hV φ]

/-- From actual smooth closed curvature, internally produce a local smooth
regular density AND its full pointwise curvature, ANY n including zero. -/
theorem exists_local_smooth_representative_of_smooth_ddC
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
    (σ : ClosedRealOneOneForm n M) (e : ComplexChart n M)
    {Ω : Opens (ComplexModel n)} (hΩ : Ω ≤ chartTarget e)
    (R : 𝓓'(Ω, ℝ))
    (hR : ddC R = restrictForm (smoothFormDistribution b σ.val e) hΩ)
    (x : ComplexModel n) (hx : x ∈ Ω) :
    ∃ (V : Opens (ComplexModel n)) (hV : V ≤ Ω) (k : ComplexModel n → ℝ),
      x ∈ V ∧ ContDiffOn ℝ ∞ k V ∧
      ∃ hk : LocallyIntegrableOn k V b.addHaar,
        restrictDistribution R hV = regularDistribution b.addHaar k hk ∧
        EqOn (smoothDDC k) (σ.val.coeff e) V := by
  obtain ⟨W, ρ, hxW, hpot⟩ :=
    LocalPotentials.closedRealOneOne_hasLocalPotentials σ e x (hΩ hx)
  let U : Opens (ComplexModel n) := ⟨Ω ∩ W, Ω.isOpen.inter hpot.1⟩
  have hUΩ : U ≤ Ω := fun _ hz => hz.1
  have hUW : (U : Set (ComplexModel n)) ⊆ W := fun _ hz => hz.2
  have hUe : U ≤ chartTarget e := hUΩ.trans hΩ
  have hpU : IsSmoothLocalPotential σ.val e U ρ :=
    ⟨U.isOpen, hUe, hpot.2.2.1.mono hUW, fun z hz => hpot.2.2.2 (hUW hz)⟩
  have hρ : LocallyIntegrableOn ρ U b.addHaar :=
    hpU.2.2.1.continuousOn.locallyIntegrableOn U.isOpen.measurableSet
  have hdd : ddC (restrictDistribution R hUΩ) =
      ddC (regularDistribution b.addHaar ρ hρ) := by
    rw [← restrictForm_ddC, hR, restrictForm_trans]
    exact restrict_smoothFormDistribution_eq_ddC_of_local_potential b σ.val e hUe ρ hpU
  obtain ⟨V, hVU, h, hxV, hsm, hh, hdiff, _hlevi⟩ :=
    DistributionPotentialSmoothOverlap.exists_smooth_difference_of_equal_ddC b.addHaar
      (restrictDistribution R hUΩ) (regularDistribution b.addHaar ρ hρ) hdd x ⟨hx, hxW⟩
  have hVΩ : V ≤ Ω := hVU.trans hUΩ
  have hVe : V ≤ chartTarget e := hVΩ.trans hΩ
  have hρV : LocallyIntegrableOn ρ V b.addHaar := hρ.mono_set hVU
  let k : ComplexModel n → ℝ := fun z => h z + ρ z
  have hks : ContDiffOn ℝ ∞ k V := hsm.contDiffOn.add (hpU.2.2.1.mono hVU)
  have hk : LocallyIntegrableOn k V b.addHaar :=
    hks.continuousOn.locallyIntegrableOn V.isOpen.measurableSet
  have hreg : restrictDistribution R hVΩ = regularDistribution b.addHaar k hk := by
    rw [restrict_sub, restrictDistribution_trans, restrictDistribution_regularDistribution] at hdiff
    exact (sub_eq_iff_eq_add.mp hdiff).trans (regularDistribution_add' hh hρV hk).symm
  refine ⟨V, hVΩ, k, hxV, hks, hk, hreg, ?_⟩
  have hσL : LocallyIntegrableOn (σ.val.coeff e) V b.addHaar :=
    (smoothForm_coeff_locallyIntegrable b σ.val e).mono_set hVe
  have hcoeff : ddC (regularDistribution b.addHaar k hk) =
      regularFormDistribution b.addHaar (σ.val.coeff e) hσL := by
    rw [← hreg, ← restrictForm_ddC, hR, restrictForm_trans]
    exact restrict_regularForm b.addHaar (smoothForm_coeff_locallyIntegrable b σ.val e) hVe
  rw [ddC_regular_eq_regularForm b.addHaar hks] at hcoeff
  exact eqOn_of_regularForm_eq b.addHaar
    (LogWeightFactorization.smoothDDC_contDiffOn V.isOpen hks).continuousOn
    ((σ.val.smooth e).continuousOn.mono hVe) _ hσL hcoeff

end SGPT.Foundations.Analysis.Pending.DistributionSmoothDdcRegularity
