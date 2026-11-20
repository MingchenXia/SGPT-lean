import SGPT.Foundations.Analysis.Pending.CanonicalComplementaryCurrentTests
import SGPT.Foundations.Analysis.Pending.FullGeometricCurrentPositivityGluing
import SGPT.Foundations.Analysis.Pending.NaturalThetaPshFullCurrentTests
import SGPT.Foundations.Analysis.Pending.GlobalCurrentPotentials

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff Manifold

namespace SGPT.Foundations.Analysis.Pending.NaturalThetaPshGeometricCurrent

open FirstPass _root_.SGPT.Foundations.Analysis.LocalCurrents StronglyPositiveForms
  TopDegreeDensity ConstantFormProducts CanonicalCurrentFrame CanonicalComplementaryCurrentTests
  CanonicalDDCFullTestTranspose DDCOverlap ScalarFullTestTranspose FullLocalSmoothCurrentDensity
  LocalProductCurrents LocalBedfordTaylorProducts LocalBedfordTaylorSmooth
  LocalCurrentLebesgue CompactVariableCurrentTests
  GlobalCurrentPotentials NaturalThetaPshFullCurrentTests FullGeometricCurrentPositivityGluing

private def castTestCLM {n a b : ℕ} {U : Opens (ComplexModel n)} (h : a = b) :
    TestForm U a →L[ℝ] TestForm U b := h ▸ ContinuousLinearMap.id ℝ (TestForm U a)

private theorem castTestCLM_apply {n a b : ℕ} {U : Opens (ComplexModel n)}
    (h : a = b) (α : TestForm U a) : castTestCLM h α = castTestDegree h α := by
  subst b
  rfl

private theorem castTestDegree_mono {n a b : ℕ} {U V : Opens (ComplexModel n)}
    (h : a = b) (_hUV : U ≤ V) (α : TestForm U a) :
    castTestDegree h (TestFunction.monoCLM ℝ α : TestForm V a) =
      (TestFunction.monoCLM ℝ (castTestDegree h α) : TestForm V b) := by
  subst b
  rfl

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- A genuine theta potential defines an actual compatible geometric current. -/
def thetaPotentialCurrent (θ : SmoothRealForm (m + 1) M 2) (u : M → EReal)
    (hu : IsThetaPshPotential θ u) : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)) :=
  GlobalCurrents.smoothGlobalCurrent (canonicalBasis (m + 1)) θ +
    globalDDC (canonicalBasis (m + 1)) (Nat.succ_pos m) u hu.quasiPshPotential

/-- Every full chart span test evaluates the unbounded potential by the literal adjoint. -/
theorem globalDDC_restrictChart_castTestDegree_eq_integral
    (u : M → EReal) (hu : IsGlobalQuasiPshPotential (n := m + 1) u)
    (e : ComplexChart (m + 1) M) {W : Opens (ComplexModel (m + 1))}
    (hW : W ≤ chartTarget e) (α : TestForm W (2 * m))
    (hα : ∀ x, α x ∈ formSpan (m + 1) m) :
    (globalDDC (canonicalBasis (m + 1)) (Nat.succ_pos m) u hu).restrictChart e hW
      (castTestDegree (by rw [complexModel_real_finrank]; omega :
        2 * m = Module.finrank ℝ (ComplexModel (m + 1)) - 2) α) =
      ∫ x in (W : Set (ComplexModel (m + 1))),
        scalarAdjointTest α x * (chartFunction u e x).toReal := by
  let β : TestForm (chartTarget e) (2 * m) := TestFunction.monoCLM ℝ α
  have hβ : ∀ x, β x ∈ formSpan (m + 1) m := by
    intro x
    simpa only [β, testForm_inclusion_apply hW] using hα x
  change toLocalCurrent (canonicalBasis (m + 1)) (degreeTwo (Nat.succ_pos m))
    (chartDDC (canonicalBasis (m + 1)) u e
      (quasiPsh_chart_locallyIntegrable (canonicalBasis (m + 1)) (Nat.succ_pos m) u hu e))
    (TestFunction.monoCLM ℝ (castTestDegree _ α)) = _
  rw [← castTestDegree_mono _ hW α, toLocalCurrent_castTestDegree]
  unfold chartDDC
  rw [(wedgePairing_ddC_eq_scalar_full_test _ β hβ).1, regularDistribution_apply,
    addHaar_canonicalBasis]
  have hadj : ∀ x, scalarAdjointTest β x = scalarAdjointTest α x := by
    intro x
    rw [← ddcAdjoint_eq_scalarAdjointTest β hβ,
      ← ddcAdjoint_eq_scalarAdjointTest α hα]
    exact ddcAdjoint_monoCLM_apply hW _ α x
  simp_rw [hadj]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hz : scalarAdjointTest α x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hx ((scalarAdjointTest α).tsupport_subset h))
  rw [hz, zero_mul]

private theorem smooth_restrictChart_eq_correction
    (θ : SmoothRealForm (m + 1) M 2) (e : ComplexChart (m + 1) M)
    {W : Opens (ComplexModel (m + 1))} (hW : W ≤ chartTarget e)
    (ρ : ComplexModel (m + 1) → ℝ) (hpot : IsSmoothLocalPotential θ e W ρ)
    (α : TestForm W (2 * m)) (hα : ∀ x, α x ∈ formSpan (m + 1) m) :
    (GlobalCurrents.smoothGlobalCurrent (canonicalBasis (m + 1))
      (k := degreeTwo (Nat.succ_pos m)) θ).restrictChart e hW
      (castTestDegree (by rw [complexModel_real_finrank]; omega :
        2 * m = Module.finrank ℝ (ComplexModel (m + 1)) - 2) α) =
      ∑ i, ddcWedge (oneCurrent W) hpot.2.2.1
        (formBasis (m + 1) m i) (coeffTest α i) := by
  change (GlobalCurrents.smoothGlobalCurrent (canonicalBasis (m + 1))
    (k := degreeTwo (Nat.succ_pos m)) θ).inChart e
    (TestFunction.monoCLM ℝ (castTestDegree _ α)) = _
  rw [← castTestDegree_mono _ hW α, smoothGlobalCurrent_castTestDegree_eq_integral,
    ddcWedge_oneCurrent_full_test_integral hpot.2.2.1 α hα]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [testForm_inclusion_apply hW]
  change topDensity (wedgeTo (by omega : 2 + 2 * m = 2 * (m + 1))
    (θ.coeff e x) (α x)) =
    topDensity (wedgeTo (rfl : 2 * m + 2 = 2 * (m + 1)) (α x) (smoothDDC ρ x))
  rw [wedgeTo_comm_of_mem_formSpan (hα x) (smoothDDC ρ x) rfl
    (by omega : 2 + 2 * m = 2 * (m + 1))]
  by_cases hx : x ∈ W
  · rw [hpot.2.2.2 hx]
  · have ha : α x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hx (α.tsupport_subset h))
    have hzero (A : RealForm (m + 1) 2) :
        wedgeTo (by omega : 2 + 2 * m = 2 * (m + 1)) A
          (0 : RealForm (m + 1) (2 * m)) = 0 := by
      simpa only [zero_smul] using wedgeTo_smul_right
        (by omega : 2 + 2 * m = 2 * (m + 1)) (0 : ℝ) A
        (0 : RealForm (m + 1) (2 * m))
    rw [ha, hzero, hzero]

/-- Natural local positivity holds for every full strong test of the actual current. -/
theorem exists_thetaPotentialCurrent_full_local_positive
    (θ : SmoothRealForm (m + 1) M 2) (u : M → EReal) (hu : IsThetaPshPotential θ u)
    (e : ComplexChart (m + 1) M) (z : ComplexModel (m + 1)) (hz : z ∈ e.val.target) :
    ∃ (W : Opens (ComplexModel (m + 1))) (hW : W ≤ chartTarget e), z ∈ W ∧
      ∀ α : TestForm W (2 * m), (∀ x, α x ∈ spCone m) →
        0 ≤ (thetaPotentialCurrent θ u hu).restrictChart e hW
          (castTestDegree (by rw [complexModel_real_finrank]; omega :
            2 * m = Module.finrank ℝ (ComplexModel (m + 1)) - 2) α) := by
  obtain ⟨W, hW, ρ, hpot, hzW, hpos⟩ :=
    exists_full_compact_test_integral_nonnegative θ u hu e z hz
  refine ⟨W, hW, hzW, ?_⟩
  intro α hα
  have hspan : ∀ x, α x ∈ formSpan (m + 1) m :=
    fun x => Submodule.subset_span (hα x)
  change 0 ≤ (GlobalCurrents.smoothGlobalCurrent (canonicalBasis (m + 1))
    (k := degreeTwo (Nat.succ_pos m)) θ).restrictChart e hW (castTestDegree _ α) +
    (globalDDC (canonicalBasis (m + 1)) (Nat.succ_pos m) u hu.quasiPshPotential).restrictChart
      e hW (castTestDegree _ α)
  rw [smooth_restrictChart_eq_correction θ e hW ρ hpot α hspan,
    globalDDC_restrictChart_castTestDegree_eq_integral u hu.quasiPshPotential e hW α hspan]
  simpa only [add_comm] using hpos α hα

/-- Every full variable strongly positive chart test is nonnegative. -/
theorem thetaPotentialCurrent_full_positive
    (θ : SmoothRealForm (m + 1) M 2) (u : M → EReal) (hu : IsThetaPshPotential θ u)
    (e : ComplexChart (m + 1) M) (α : TestForm (chartTarget e) (2 * m))
    (hα : ∀ x, α x ∈ spCone m) :
    0 ≤ (thetaPotentialCurrent θ u hu).inChart e
      (castTestDegree (by rw [complexModel_real_finrank]; omega :
        2 * m = Module.finrank ℝ (ComplexModel (m + 1)) - 2) α) := by
  let hdegree : 2 * m = Module.finrank ℝ (ComplexModel (m + 1)) - 2 := by
    rw [complexModel_real_finrank]
    omega
  let S : TestForm (chartTarget e) (2 * m) →L[ℝ] ℝ :=
    ((thetaPotentialCurrent θ u hu).inChart e).comp (castTestCLM hdegree)
  have hloc : ∀ z ∈ chartTarget e, ∃ (W : Opens (ComplexModel (m + 1)))
      (_hW : W ≤ chartTarget e), z ∈ W ∧
      ∀ β : TestForm W (2 * m), (∀ x, β x ∈ spCone m) →
        0 ≤ S (TestFunction.monoCLM ℝ β : TestForm (chartTarget e) (2 * m)) := by
    intro z hz
    obtain ⟨W, hW, hzW, hpos⟩ :=
      exists_thetaPotentialCurrent_full_local_positive θ u hu e z hz
    refine ⟨W, hW, hzW, ?_⟩
    intro β hβ
    change 0 ≤ (thetaPotentialCurrent θ u hu).inChart e
      (castTestCLM hdegree (TestFunction.monoCLM ℝ β))
    rw [castTestCLM_apply, castTestDegree_mono hdegree hW β]
    exact hpos β hβ
  have hp := nonnegative_of_local_full_tests S hloc α hα
  change 0 ≤ (thetaPotentialCurrent θ u hu).inChart e (castTestCLM hdegree α) at hp
  rw [castTestCLM_apply] at hp
  exact hp

end SGPT.Foundations.Analysis.Pending.NaturalThetaPshGeometricCurrent
