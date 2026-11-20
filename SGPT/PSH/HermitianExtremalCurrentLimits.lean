import SGPT.PSH.HermitianPSH
import SGPT.PSH.HermitianExtremalLimits
import SGPT.Foundations.Analysis.Pending.GlobalCurrentPotentials
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Decreasing limits of nonclosed-background positive currents

A decreasing family of genuine local quasi-PSH functions converges against
all compact scalar tests by dominated convergence between its first member
and its genuine limit. The differential is transferred to the test form,
so every degree-two current pairing converges. Positivity survives this
limit for an arbitrary fixed smooth background, without closedness.

The scalar-test proof is the analytic argument of
`Pending.OriginalCurrentAnalyticWeakRegularization`, isolated here without
its closed-current regularization hypotheses.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianExtremalCurrentLimits

open Set Filter MeasureTheory TopologicalSpace
open scoped Distributions Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.LocalCurrents
open SGPT.Foundations.Analysis.Pending
open CanonicalCurrentFrame GlobalCurrents DDCOverlap CanonicalComplementaryCurrentTests
open Hermitian HermitianExtremalL1Bound HermitianExtremalLimits

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

theorem tendsto_regular_of_antitone
    (u : M → EReal) (hu : IsGlobalQuasiPshPotential (n := m + 1) u)
    (v : ℕ → M → EReal) (hv : ∀ k, IsGlobalQuasiPshPotential (n := m + 1) (v k))
    (hanti : ∀ x, Antitone fun k => v k x) (hinf : ∀ x, ⨅ k, v k x = u x)
    (e : ComplexChart (m + 1) M) (φ : 𝓓(chartTarget e, ℝ)) :
    Tendsto (fun k => regularDistribution (canonicalBasis (m + 1)).addHaar
      (fun z => (chartFunction (v k) e z).toReal)
      (chartIntegrability (v k) (hv k) e) φ) atTop
      (𝓝 (regularDistribution (canonicalBasis (m + 1)).addHaar
        (fun z => (chartFunction u e z).toReal)
        (chartIntegrability u hu e) φ)) := by
  let μ := (canonicalBasis (m + 1)).addHaar
  let f (k : ℕ) (z : ComplexModel (m + 1)) := φ z * (chartFunction (v k) e z).toReal
  let g (z : ComplexModel (m + 1)) := φ z * (chartFunction u e z).toReal
  have hf (k : ℕ) : Integrable (f k) μ :=
    φ.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ)
      (chartIntegrability (v k) (hv k) e)
  have hg : Integrable g μ := φ.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ)
    (chartIntegrability u hu e)
  have hfin : ∀ᵐ z ∂μ, z ∈ chartTarget e →
      (chartFunction u e z ≠ ⊤ ∧ chartFunction u e z ≠ ⊥) ∧
      (chartFunction (v 0) e z ≠ ⊤ ∧ chartFunction (v 0) e z ≠ ⊥) :=
    (ae_restrict_iff' e.val.open_target.measurableSet).mp
      ((GlobalCurrentPotentials.quasiPsh_chart_ae_finite (canonicalBasis (m + 1))
        (Nat.succ_pos m) u hu e).and
        (GlobalCurrentPotentials.quasiPsh_chart_ae_finite (canonicalBasis (m + 1))
          (Nat.succ_pos m) (v 0) (hv 0) e))
  have hlow (k : ℕ) (z : ComplexModel (m + 1)) :
      chartFunction u e z ≤ chartFunction (v k) e z := by
    change u (e.val.symm z) ≤ v k (e.val.symm z)
    rw [← hinf]
    exact iInf_le _ k
  have hhigh (k : ℕ) (z : ComplexModel (m + 1)) :
      chartFunction (v k) e z ≤ chartFunction (v 0) e z :=
    hanti (e.val.symm z) (Nat.zero_le k)
  let B (z : ComplexModel (m + 1)) := |g z| + |f 0 z|
  have hB : Integrable B μ := hg.abs.add (hf 0).abs
  have hbound (k : ℕ) : ∀ᵐ z ∂μ, ‖f k z‖ ≤ B z := by
    filter_upwards [hfin] with z hz
    by_cases hzU : z ∈ chartTarget e
    · obtain ⟨huz,hv0z⟩ := hz hzU
      have hvbot : chartFunction (v k) e z ≠ ⊥ := by
        intro h
        exact huz.2 (bot_unique (h ▸ hlow k z))
      have hl := EReal.toReal_le_toReal (hlow k z) huz.2 (by
        intro h
        exact hv0z.1 (top_unique (h ▸ hhigh k z)))
      have hh := EReal.toReal_le_toReal (hhigh k z) hvbot hv0z.1
      have ha : |(chartFunction (v k) e z).toReal| ≤
          |(chartFunction u e z).toReal| + |(chartFunction (v 0) e z).toReal| := by
        apply abs_le.mpr
        constructor
        · linarith [neg_abs_le (chartFunction u e z).toReal,
            abs_nonneg (chartFunction (v 0) e z).toReal]
        · linarith [le_abs_self (chartFunction (v 0) e z).toReal,
            abs_nonneg (chartFunction u e z).toReal]
      simpa only [f,g,B,Real.norm_eq_abs,abs_mul,mul_add] using
        mul_le_mul_of_nonneg_left ha (abs_nonneg (φ z))
    · have hφ : φ z = 0 := image_eq_zero_of_notMem_tsupport
        (fun ht => hzU (φ.tsupport_subset ht))
      simp [f,g,B,hφ]
  have ht : ∀ᵐ z ∂μ, Tendsto (fun k => f k z) atTop (𝓝 (g z)) := by
    filter_upwards [hfin] with z hz
    by_cases hzU : z ∈ chartTarget e
    · have hpoint : Tendsto (fun k => chartFunction (v k) e z) atTop
          (𝓝 (chartFunction u e z)) := by
        change Tendsto (fun k => v k (e.val.symm z)) atTop (𝓝 (u (e.val.symm z)))
        rw [← hinf]
        exact tendsto_atTop_iInf (hanti _)
      exact ((EReal.tendsto_toReal (hz hzU).1.1 (hz hzU).1.2).comp hpoint).const_mul (φ z)
    · have hφ : φ z = 0 := image_eq_zero_of_notMem_tsupport
        (fun hs => hzU (φ.tsupport_subset hs))
      simp only [f,g,hφ,zero_mul]
      exact tendsto_const_nhds
  simpa only [regularDistribution_apply,f,g] using
    tendsto_integral_of_dominated_convergence B (fun k => (hf k).aestronglyMeasurable) hB hbound ht

theorem tendsto_ddcCurrent_of_antitone
    (u : M → EReal) (hu : IsGlobalQuasiPshPotential (n := m + 1) u)
    (v : ℕ → M → EReal) (hv : ∀ k, IsGlobalQuasiPshPotential (n := m + 1) (v k))
    (hanti : ∀ x, Antitone fun k => v k x) (hinf : ∀ x, ⨅ k, v k x = u x)
    (e : ComplexChart (m + 1) M)
    (η : TestForm (chartTarget e) (Module.finrank ℝ (ComplexModel (m + 1)) - 2)) :
    Tendsto (fun k => (ddcCurrent (v k) (hv k)).inChart e η) atTop
      (𝓝 ((ddcCurrent u hu).inChart e η)) := by
  have hcoeff (w : Fin 2 → ComplexModel (m + 1)) (φ : 𝓓(chartTarget e, ℝ)) :
      Tendsto (fun k => chartDDC (canonicalBasis (m + 1)) (v k) e
        (chartIntegrability (v k) (hv k) e) w φ) atTop
        (𝓝 (chartDDC (canonicalBasis (m + 1)) u e
          (chartIntegrability u hu e) w φ)) := by
    have hw : w = ![w 0,w 1] := by ext i; fin_cases i <;> rfl
    have eval (R : 𝓓'(chartTarget e, ℝ)) : ddC R w φ =
        R (DDCOverlap.ddcAdjointCoeff (w 0) (w 1) φ) :=
      (congrArg (fun t => ddC R t φ) hw).trans (DDCOverlap.ddC_apply_eq R _ _ φ)
    change Tendsto (fun k => ddC (regularDistribution (canonicalBasis (m + 1)).addHaar
      (fun z => (chartFunction (v k) e z).toReal) _) w φ) atTop
      (𝓝 (ddC (regularDistribution (canonicalBasis (m + 1)).addHaar
        (fun z => (chartFunction u e z).toReal) _) w φ))
    simp only [eval]
    exact tendsto_regular_of_antitone u hu v hv hanti hinf e _
  simp only [ddcCurrent, GlobalCurrent.inChart, ddCCurrentFamily, toLocalCurrent, wedgePairing_apply]
  exact tendsto_finsetSum _ fun s _ => (hcoeff _ _).const_smul (Equiv.Perm.sign s.out)

/-- A genuine nondegenerate decreasing limit preserves the actual full
current inequality for any smooth fixed background. -/
theorem isFormPSH_iInf_of_quasiPshPotential
    {θ : SmoothRealForm (m + 1) M 2} {w : ℕ → M → EReal}
    (hw : ∀ j, IsFormPSH θ (w j)) (hanti : ∀ x, Antitone fun j => w j x)
    (hlim : IsGlobalQuasiPshPotential (n := m + 1) (fun x => ⨅ j, w j x)) :
    IsFormPSH θ (fun x => ⨅ j, w j x) := by
  refine ⟨hlim, ?_⟩
  intro e α hα
  let η := castTestDegree
    (by rw [complexModel_real_finrank]; omega :
      2 * m = Module.finrank ℝ (ComplexModel (m + 1)) - 2) α
  have hdd := tendsto_ddcCurrent_of_antitone (fun x => ⨅ j, w j x) hlim w
    (fun j => (hw j).quasiPshPotential) hanti (fun _ => rfl) e η
  let c : ℝ := (smoothGlobalCurrent (canonicalBasis (m + 1))
    (k := degreeTwo (Nat.succ_pos m)) θ).inChart e η
  have hcurrent : Tendsto (fun j => c + (ddcCurrent (w j) (hw j).quasiPshPotential).inChart e η)
      atTop (𝓝 (c + (ddcCurrent (fun x => ⨅ j, w j x) hlim).inChart e η)) :=
    tendsto_const_nhds.add hdd
  have hnonneg : ∀ j, 0 ≤ (potentialCurrent θ (w j) (hw j).quasiPshPotential).inChart e η :=
    fun j => (hw j).isPositiveCurrent e α hα
  exact isClosed_Ici.mem_of_tendsto hcurrent (Eventually.of_forall hnonneg)

/-- Actual common local corrections and one genuine nonpole manufacture
both local regularity and full current positivity of the decreasing limit. -/
theorem isHermitianPSH_iInf_of_exists_ne_bot [ConnectedSpace M]
    (ω : Background (m + 1) M)
    (hcorrection : HasCommonLocalCorrections (n := m + 1) (IsHermitianPSH ω))
    {w : ℕ → M → EReal} (hw : ∀ j, IsHermitianPSH ω (w j))
    (hanti : ∀ x, Antitone fun j => w j x) (hne : ∃ y, (⨅ j, w j y) ≠ ⊥) :
    IsHermitianPSH ω (fun x => ⨅ j, w j x) :=
  isFormPSH_iInf_of_quasiPshPotential hw hanti
    (isGlobalQuasiPshPotential_iInf_of_exists_ne_bot hcorrection hw hanti hne)

end SGPT.PSH.HermitianExtremalCurrentLimits
