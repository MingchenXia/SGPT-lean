import SGPT.PSH.HermitianBackground
import SGPT.Foundations.Analysis.FirstPass.QuasiPshChartL1
import SGPT.Foundations.Analysis.Pending.CanonicalComplementaryCurrentTests
import SGPT.Foundations.Analysis.Pending.CurrentPairing

/-!
# Plurisubharmonicity relative to a possibly nonclosed Hermitian form

For a genuine local quasi-plurisubharmonic potential `u`, the current
`θ + ddᶜu` is the sum of the smooth geometric current of `θ` and the actual
distributional differential of `u`. Positivity is tested against every
variable strongly positive compactly supported complementary form.

This is the definition used for a nonclosed Hermitian background in FPT,
Section 14.8. It imposes neither closedness nor the existence of local
potentials for the background form. The existing local-potential definition
embeds into this one in the separate module `HermitianClosedBridge`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.PSH.Hermitian

open Set MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.LocalCurrents
open SGPT.Foundations.Analysis.Pending
open StronglyPositiveForms CanonicalCurrentFrame GlobalCurrents
  CanonicalComplementaryCurrentTests TopDegreeDensity ConstantFormProducts
  LocalProductCurrents ScalarFullTestTranspose DDCOverlap CanonicalDDCFullTestTranspose

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- Full positivity of a degree-two geometric current: all strongly positive
variable compact tests are retained, in every holomorphic chart. -/
def IsPositiveCurrent
    (T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m))) : Prop :=
  ∀ (e : ComplexChart (m + 1) M)
    (α : TestForm (chartTarget e) (2 * m)),
    (∀ x, α x ∈ spCone m) →
    0 ≤ T.inChart e (castTestDegree
      (by rw [complexModel_real_finrank]; omega :
        2 * m = Module.finrank ℝ (ComplexModel (m + 1)) - 2) α)

theorem IsPositiveCurrent.add
    {S T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m))}
    (hS : IsPositiveCurrent S) (hT : IsPositiveCurrent T) :
    IsPositiveCurrent (S + T) := by
  intro e α hα
  exact add_nonneg (hS e α hα) (hT e α hα)

theorem IsPositiveCurrent.smul
    {T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m))}
    (hT : IsPositiveCurrent T) {c : ℝ} (hc : 0 ≤ c) :
    IsPositiveCurrent (c • T) := by
  intro e α hα
  exact mul_nonneg hc (hT e α hα)

/-- Chartwise local integrability is produced from genuine local quasi-PSH
regularity, for the canonical complex-oriented Haar normalization. -/
theorem chartIntegrability (u : M → EReal)
    (hu : IsGlobalQuasiPshPotential (n := m + 1) u) :
    ChartLocallyIntegrable (canonicalBasis (m + 1)) u := by
  intro e
  rw [addHaar_canonicalBasis]
  exact hu.locallyIntegrableOn_chart_toReal e

/-- The actual canonical `ddᶜu` current. Its overlap law is the proved
holomorphic covariance for distributions; no positive or closed background
is needed to construct it. -/
def ddcCurrent (u : M → EReal)
    (hu : IsGlobalQuasiPshPotential (n := m + 1) u) :
    GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)) :=
  ⟨ddCCurrentFamily (canonicalBasis (m + 1)) (Nat.succ_pos m) u (chartIntegrability u hu),
    fun e f η ζ h => ddCCurrentFamily_overlap (canonicalBasis (m + 1)) (Nat.succ_pos m)
      u (chartIntegrability u hu) e f η ζ h⟩

@[simp] theorem ddcCurrent_inChart (u : M → EReal)
    (hu : IsGlobalQuasiPshPotential (n := m + 1) u) (e : ComplexChart (m + 1) M) :
    (ddcCurrent u hu).inChart e = ddCCurrentFamily (canonicalBasis (m + 1))
      (Nat.succ_pos m) u (chartIntegrability u hu) e := rfl

/-- The literal geometric current `θ + ddᶜu`; `θ` need not be closed. -/
def potentialCurrent (θ : SmoothRealForm (m + 1) M 2) (u : M → EReal)
    (hu : IsGlobalQuasiPshPotential (n := m + 1) u) :
    GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)) :=
  smoothGlobalCurrent (canonicalBasis (m + 1)) θ +
    ddcCurrent u hu

/-- The current inequality `θ + ddᶜu ≥ 0` for an actual, locally nondegenerate
quasi-PSH potential. This applies also to smooth backgrounds that are not
positive; the Hermitian specialization is `IsHermitianPSH`. -/
def IsFormPSH (θ : SmoothRealForm (m + 1) M 2) (u : M → EReal) : Prop :=
  ∃ hu : IsGlobalQuasiPshPotential (n := m + 1) u,
    IsPositiveCurrent (potentialCurrent θ u hu)

/-- FPT's `omega`-plurisubharmonicity for a Hermitian form that need not be closed. -/
def IsHermitianPSH (omega : Background (m + 1) M) (u : M → EReal) : Prop :=
  IsFormPSH omega.form u

private theorem castTestDegree_mono {n a b : ℕ} {U V : Opens (ComplexModel n)}
    (h : a = b) (_hUV : U ≤ V) (α : TestForm U a) :
    castTestDegree h (TestFunction.monoCLM ℝ α : TestForm V a) =
      (TestFunction.monoCLM ℝ (castTestDegree h α) : TestForm V b) := by
  subst b
  rfl

/-- The canonical weak Hessian retains its full compact-test adjoint formula. -/
theorem ddcCurrent_restrictChart_eq_integral (u : M → EReal)
    (hu : IsGlobalQuasiPshPotential (n := m + 1) u)
    (e : ComplexChart (m + 1) M) {W : Opens (ComplexModel (m + 1))}
    (hW : W ≤ chartTarget e) (α : TestForm W (2 * m))
    (hα : ∀ x, α x ∈ formSpan (m + 1) m) :
    (ddcCurrent u hu).restrictChart e hW
      (castTestDegree (by rw [complexModel_real_finrank]; omega :
        2 * m = Module.finrank ℝ (ComplexModel (m + 1)) - 2) α) =
      ∫ x in (W : Set (ComplexModel (m + 1))),
        scalarAdjointTest α x * (chartFunction u e x).toReal := by
  let β : TestForm (chartTarget e) (2 * m) := TestFunction.monoCLM ℝ α
  have hβ : ∀ x, β x ∈ formSpan (m + 1) m := by
    intro x
    simpa only [β, testForm_inclusion_apply hW] using hα x
  change toLocalCurrent (canonicalBasis (m + 1)) (degreeTwo (Nat.succ_pos m))
    (chartDDC (canonicalBasis (m + 1)) u e (chartIntegrability u hu e))
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
  have hz : scalarAdjointTest α x = 0 := image_eq_zero_of_notMem_tsupport
    (fun hs => hx ((scalarAdjointTest α).tsupport_subset hs))
  rw [hz, zero_mul]

/-- Full positivity persists on every actual open chart subdomain. -/
theorem IsPositiveCurrent.restrictChart
    {T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m))}
    (hT : IsPositiveCurrent T) (e : ComplexChart (m + 1) M)
    {W : Opens (ComplexModel (m + 1))} (hW : W ≤ chartTarget e)
    (α : TestForm W (2 * m)) (hα : ∀ x, α x ∈ spCone m) :
    0 ≤ T.restrictChart e hW (castTestDegree
      (by rw [complexModel_real_finrank]; omega :
        2 * m = Module.finrank ℝ (ComplexModel (m + 1)) - 2) α) := by
  have hp := hT e (TestFunction.monoCLM ℝ α)
    (fun x => by simpa only [testForm_inclusion_apply hW] using hα x)
  rw [castTestDegree_mono _ hW α] at hp
  exact hp

/-- The actual background current and weak Hessian retain their literal full
compact-test formula on any chart subdomain. -/
theorem potentialCurrent_restrictChart_eq_integral
    (θ : SmoothRealForm (m + 1) M 2) (u : M → EReal)
    (hu : IsGlobalQuasiPshPotential (n := m + 1) u)
    (e : ComplexChart (m + 1) M) {W : Opens (ComplexModel (m + 1))}
    (hW : W ≤ chartTarget e) (α : TestForm W (2 * m))
    (hα : ∀ x, α x ∈ formSpan (m + 1) m) :
    (potentialCurrent θ u hu).restrictChart e hW
      (castTestDegree (by rw [complexModel_real_finrank]; omega :
        2 * m = Module.finrank ℝ (ComplexModel (m + 1)) - 2) α) =
      (∫ x, topDensity (wedgeTo (by omega : 2 + 2 * m = 2 * (m + 1))
        (θ.coeff e x) (α x))) +
      ∫ x in (W : Set (ComplexModel (m + 1))),
        scalarAdjointTest α x * (chartFunction u e x).toReal := by
  have hs : (smoothGlobalCurrent (canonicalBasis (m + 1))
      (k := degreeTwo (Nat.succ_pos m)) θ).restrictChart e hW
      (castTestDegree (by rw [complexModel_real_finrank]; omega :
        2 * m = Module.finrank ℝ (ComplexModel (m + 1)) - 2) α) =
      ∫ x, topDensity (wedgeTo (by omega : 2 + 2 * m = 2 * (m + 1))
        (θ.coeff e x) (α x)) := by
    change (smoothGlobalCurrent (canonicalBasis (m + 1))
      (k := degreeTwo (Nat.succ_pos m)) θ).inChart e
      (TestFunction.monoCLM ℝ (castTestDegree _ α)) = _
    rw [← castTestDegree_mono _ hW α,
      smoothGlobalCurrent_castTestDegree_eq_integral]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [testForm_inclusion_apply hW]
  change (smoothGlobalCurrent (canonicalBasis (m + 1))
      (k := degreeTwo (Nat.succ_pos m)) θ).restrictChart e hW
      (castTestDegree _ α) +
    (ddcCurrent u hu).restrictChart
      e hW (castTestDegree _ α) = _
  rw [hs, ddcCurrent_restrictChart_eq_integral u hu e hW α hα]

/-- The local PSH-plus-smooth predicate is part of the mathematical domain,
independently of any global closed background. -/
theorem IsFormPSH.quasiPshPotential {θ : SmoothRealForm (m + 1) M 2}
    {u : M → EReal} (hu : IsFormPSH θ u) :
    IsGlobalQuasiPshPotential (n := m + 1) u := hu.choose

theorem IsFormPSH.isPositiveCurrent {θ : SmoothRealForm (m + 1) M 2}
    {u : M → EReal} (hu : IsFormPSH θ u) :
    IsPositiveCurrent (potentialCurrent θ u hu.quasiPshPotential) := hu.choose_spec

theorem IsHermitianPSH.quasiPshPotential {omega : Background (m + 1) M}
    {u : M → EReal} (hu : IsHermitianPSH omega u) :
    IsGlobalQuasiPshPotential (n := m + 1) u :=
  IsFormPSH.quasiPshPotential hu

theorem IsHermitianPSH.isPositiveCurrent {omega : Background (m + 1) M}
    {u : M → EReal} (hu : IsHermitianPSH omega u) :
    IsPositiveCurrent (potentialCurrent omega.form u hu.quasiPshPotential) :=
  IsFormPSH.isPositiveCurrent hu

/-- The extended-real potential never takes the value positive infinity. -/
theorem IsHermitianPSH.ne_top {omega : Background (m + 1) M}
    {u : M → EReal} (hu : IsHermitianPSH omega u) (x : M) : u x ≠ ⊤ :=
  hu.quasiPshPotential.1.ne_top x

/-- Every actual chart representative has a locally integrable real density. -/
theorem IsHermitianPSH.locallyIntegrableOn_chart_toReal
    {omega : Background (m + 1) M} {u : M → EReal} (hu : IsHermitianPSH omega u)
    (e : ComplexChart (m + 1) M) :
    LocallyIntegrableOn (fun z => (chartFunction u e z).toReal) e.val.target volume :=
  hu.quasiPshPotential.locallyIntegrableOn_chart_toReal e

/-- A semipositive smooth background gives a positive current without any
closedness assumption. -/
theorem isPositiveCurrent_smooth (θ : SmoothRealForm (m + 1) M 2)
    (hθ₁ : θ.IsTypeOneOne) (hθ : θ.IsSemipositive) :
    IsPositiveCurrent (smoothGlobalCurrent (canonicalBasis (m + 1))
      (k := degreeTwo (Nat.succ_pos m)) θ) := by
  intro e α hα
  rw [smoothGlobalCurrent_castTestDegree_eq_integral]
  apply integral_nonneg
  intro z
  change 0 ≤ topDensity (wedgeTo _ (θ.coeff e z) (α z))
  by_cases hz : z ∈ e.val.target
  · exact topDensity_nonneg_of_mem_spCone
      (wedgeTo_mem_spCone m 1 (m + 1)
        (mem_spCone_one ⟨hθ₁ e z hz, hθ e z hz⟩) (hα z) (by omega))
  · have hzero : α z = 0 := image_eq_zero_of_notMem_tsupport
        (fun hs => hz (α.tsupport_subset hs))
    rw [hzero, wedgeTo_zero_right, topDensity_zero]

/-- The actual global differential of the zero potential vanishes. -/
theorem ddcCurrent_zero
    (hu : IsGlobalQuasiPshPotential (n := m + 1) (M := M) (fun _ => 0)) :
    ddcCurrent (fun _ => 0) hu = 0 := by
  apply GlobalCurrent.ext
  intro e η
  have hreg : regularDistribution (canonicalBasis (m + 1)).addHaar
      (fun z => (chartFunction (fun _ : M => (0 : EReal)) e z).toReal)
      (chartIntegrability (fun _ => 0) hu e) = 0 := by
    ext φ
    simp [regularDistribution_apply, chartFunction]
  have hddc : chartDDC (canonicalBasis (m + 1)) (fun _ : M => (0 : EReal)) e
      (chartIntegrability (fun _ => 0) hu e) = 0 := by
    unfold chartDDC
    rw [hreg]
    ext v : 1
    have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
    rw [hv, ddC_apply]
    simp
  change toLocalCurrent (canonicalBasis (m + 1)) (degreeTwo (Nat.succ_pos m))
    (chartDDC (canonicalBasis (m + 1)) (fun _ : M => (0 : EReal)) e
      (chartIntegrability (fun _ => 0) hu e)) η = 0
  rw [hddc]
  rw [toLocalCurrent, wedgePairing_apply]
  simp


end SGPT.PSH.Hermitian
