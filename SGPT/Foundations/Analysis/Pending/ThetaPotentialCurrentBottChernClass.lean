import SGPT.Foundations.Analysis.Pending.CurrentBottChernClass
import SGPT.Foundations.Analysis.Pending.NaturalThetaPshClosedCurrent

set_option autoImplicit false

/-! Actual regular scalar overlap compatibility and calibration of the
ORIGINAL theta potential current in the smooth Bott--Chern quotient.
Full mathematical BP statements and ENTIRE proofs precede this source.
No incoming class, compatibility, positivity test or density certificate. -/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Distributions Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.ThetaPotentialCurrentBottChernClass
open FirstPass _root_.SGPT.Foundations.Analysis.LocalCurrents
  FiniteScalarDistributionGluing ThetaPshChartLimitGluing
  CurrentBottChernClass CanonicalCurrentFrame NaturalThetaPshGeometricCurrent
  NaturalThetaPshClosedCurrent

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- A single arbitrary global locally L1 real scalar internally supplies the
full scalar density overlap law, including n=0 and arbitrary signed values. -/
theorem scalarFamilyCompatible_regular
    (μ : Measure (ComplexModel n)) [μ.IsAddHaarMeasure]
    (h : M → ℝ)
    (hL : ∀ e : ComplexChart n M,
      LocallyIntegrableOn (fun z => h (e.val.symm z)) (chartTarget e) μ) :
    ScalarFamilyCompatible
      (fun e => regularDistribution μ (fun z => h (e.val.symm z)) (hL e)) := by
  intro e f η ψ hrel
  let ψf : 𝓓(chartTarget f, ℝ) := TestFunction.monoCLM ℝ ψ
  have hψ : tsupport ψf ⊆ (chartTransition e f).target := by
    change tsupport (TestFunction.monoCLM ℝ ψ : 𝓓(chartTarget f, ℝ)) ⊆ _
    rw [testFunction_inclusion_coe (overlapTarget_le e f) ψ]
    exact ψ.tsupport_subset
  have he : (TestFunction.monoCLM ℝ η : 𝓓(chartTarget e, ℝ)) =
      pullTest e f ψf hψ (image_tsupport_subset_chartTarget e f hψ) := by
    ext z
    rw [congrFun (testFunction_inclusion_coe (overlapSource_le e f) η) z,
      pullTest_apply]
    by_cases hz : z ∈ (chartTransition e f).source
    · rw [pullFun_of_mem e f ψf hz,hrel z hz]
      change transitionJac e f z * ψ ((chartTransition e f) z) =
        transitionJac e f z * (TestFunction.monoCLM ℝ ψ : 𝓓(chartTarget f, ℝ))
          ((chartTransition e f) z)
      rw [congrFun (testFunction_inclusion_coe (overlapTarget_le e f) ψ)
        ((chartTransition e f) z)]
    · rw [pullFun_of_notMem e f ψf hz]
      exact image_eq_zero_of_notMem_tsupport (fun ht => hz (η.tsupport_subset ht))
  change regularDistribution μ (fun z => h (e.val.symm z)) (hL e)
      (TestFunction.monoCLM ℝ η) =
    regularDistribution μ (fun z => h (f.val.symm z)) (hL f) ψf
  rw [he,regularDistribution_apply,regularDistribution_apply,
    integral_mul_eq_integral_pullFun μ e f hψ]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [pullTest_apply]
  by_cases hz : z ∈ (chartTransition e f).source
  · rw [symm_chartTransition_apply hz]
  · rw [pullFun_of_notMem e f ψf hz]
    simp

variable {m : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]

/-- The original thetaPotentialCurrent is a natural closed type-(1,1)
subspace element, with both properties generated internally from genuine u. -/
def thetaClosedCurrent (θ : ClosedRealOneOneForm (m + 1) X)
    (u : X → EReal) (hu : IsThetaPshPotential θ.val u) :
    ClosedOneOneCurrent (M := X) (canonicalBasis (m + 1)) (Nat.succ_pos m) :=
  ⟨thetaPotentialCurrent θ.val u hu,
    (thetaPotentialCurrent_closed_type_positive θ.val u hu).1,
    (thetaPotentialCurrent_closed_type_positive θ.val u hu).2.1⟩

variable [CompactSpace X]

/-- The class map of the ORIGINAL full theta current is precisely the
prescribed original smooth class, with compatibility and L1 generated inside. -/
theorem bottChernClass_thetaClosedCurrent
    (θ : ClosedRealOneOneForm (m + 1) X)
    (u : X → EReal) (hu : IsThetaPshPotential θ.val u) :
    bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m)
      (thetaClosedCurrent θ u hu) = RealBottChern.ofRepresentative θ := by
  let b := canonicalBasis (m + 1)
  have hL := GlobalCurrentPotentials.quasiPsh_chart_locallyIntegrable b
    (Nat.succ_pos m) u hu.quasiPshPotential
  apply bottChernClass_eq_of_native_reading b (Nat.succ_pos m)
    (thetaClosedCurrent θ u hu) θ
    (fun e => regularDistribution b.addHaar
      (fun z => (chartFunction u e z).toReal) (hL e))
  · exact scalarFamilyCompatible_regular b.addHaar (fun x => (u x).toReal) hL
  · intro e
    change (GlobalCurrents.smoothGlobalCurrent b (k := degreeTwo (Nat.succ_pos m)) θ.val +
      GlobalCurrentPotentials.globalDDC b (Nat.succ_pos m) u hu.quasiPshPotential).coefficients b e = _
    rw [GlobalCurrent.coefficients_add,
      LelongPoincareDivisor.coefficients_smoothGlobalCurrent b (Nat.succ_pos m),
      GlobalCurrentPotentials.globalDDC_coefficients]
    rfl

end SGPT.Foundations.Analysis.Pending.ThetaPotentialCurrentBottChernClass
