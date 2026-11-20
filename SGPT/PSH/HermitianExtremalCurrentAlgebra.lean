import SGPT.PSH.HermitianPSH
import SGPT.PSH.HermitianExtremalQuasiAlgebra
import SGPT.Foundations.Analysis.Pending.GlobalCurrentPotentials

/-!
# Finite convex sums in the actual nonclosed-background domain

The distributional differential is linear on genuine local quasi-PSH
finite combinations. Its proof retains every full compact current test and
uses real representatives only on the simultaneous almost-everywhere finite
locus. A nonnegative coefficient budget at most one then yields a positive
combination of the original positive currents and the smooth Hermitian
background current.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianExtremalCurrentAlgebra

open Set Filter MeasureTheory TopologicalSpace
open scoped Distributions Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.LocalCurrents
open SGPT.Foundations.Analysis.Pending
open CanonicalCurrentFrame GlobalCurrents DDCOverlap
open Hermitian HermitianExtremalQuasiAlgebra

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- The actual full degree-two current is linear on a finite combination
whose functions and output are genuine local quasi-PSH potentials. -/
theorem ddcCurrent_fintypeSum {ι : Type*} [Fintype ι] (a : ι → ℝ)
    (u : ι → M → EReal)
    (hu : ∀ i, IsGlobalQuasiPshPotential (n := m + 1) (u i))
    (hF : IsGlobalQuasiPshPotential (n := m + 1)
      (fun x => ∑ i, (a i : EReal) * u i x)) :
    ddcCurrent (fun x => ∑ i, (a i : EReal) * u i x) hF =
      ∑ i, a i • ddcCurrent (u i) (hu i) := by
  classical
  apply GlobalCurrent.ext
  intro e η
  let φ := ddcAdjoint
    (currentPairingBasis (canonicalBasis (m + 1)) (degreeTwo (Nat.succ_pos m))) η
  let μ := (canonicalBasis (m + 1)).addHaar
  have hpair (v : M → EReal) (hv : IsGlobalQuasiPshPotential (n := m + 1) v) :
      (ddcCurrent v hv).inChart e η = ∫ z, φ z * (chartFunction v e z).toReal ∂μ := by
    change wedgePairing _ (chartDDC _ v e (chartIntegrability v hv e)) η = _
    rw [chartDDC, wedgePairing_ddC, regularDistribution_apply]
  rw [hpair]
  simp only [GlobalCurrent.inChart, Submodule.coe_sum, Submodule.coe_smul,
    Finset.sum_apply, Pi.smul_apply, sum_apply, smul_apply]
  change (∫ z, φ z * (chartFunction (fun x => ∑ i, (a i : EReal) * u i x) e z).toReal ∂μ) =
    ∑ i, a i * (ddcCurrent (u i) (hu i)).inChart e η
  simp_rw [hpair]
  have hi (i : ι) : Integrable (fun z => φ z * (chartFunction (u i) e z).toReal) μ :=
    φ.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ) (chartIntegrability (u i) (hu i) e)
  have hfinite : ∀ᵐ z ∂μ.restrict (chartTarget e),
      ∀ i, chartFunction (u i) e z ≠ ⊤ ∧ chartFunction (u i) e z ≠ ⊥ :=
    ae_all_iff.mpr fun i => GlobalCurrentPotentials.quasiPsh_chart_ae_finite
      (canonicalBasis (m + 1)) (Nat.succ_pos m) (u i) (hu i) e
  have hreal : (fun z => (chartFunction (fun x => ∑ i, (a i : EReal) * u i x) e z).toReal)
      =ᵐ[μ.restrict (chartTarget e)]
        (fun z => ∑ i, a i * (chartFunction (u i) e z).toReal) := by
    filter_upwards [hfinite] with z hz
    have hcoe : ∀ s : Finset ι,
        (∑ i ∈ s, (a i : EReal) * chartFunction (u i) e z) =
          ((∑ i ∈ s, a i * (chartFunction (u i) e z).toReal : ℝ) : EReal) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert i s his ih =>
        rw [Finset.sum_insert his, Finset.sum_insert his, ih]
        nth_rewrite 1 [← EReal.coe_toReal (hz i).1 (hz i).2]
        rw [← EReal.coe_mul, ← EReal.coe_add]
    change (∑ i, (a i : EReal) * chartFunction (u i) e z).toReal = _
    rw [hcoe Finset.univ, EReal.toReal_coe]
  have hrealμ := (ae_restrict_iff' e.val.open_target.measurableSet).mp hreal
  calc
    (∫ z, φ z * (chartFunction (fun x => ∑ i, (a i : EReal) * u i x) e z).toReal ∂μ)
        = ∫ z, ∑ i, a i * (φ z * (chartFunction (u i) e z).toReal) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hrealμ] with z hz
      by_cases hzt : z ∈ chartTarget e
      · rw [hz hzt, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      · have hφ : φ z = 0 := image_eq_zero_of_notMem_tsupport
          (fun hs => hzt (φ.tsupport_subset hs))
        simp only [hφ, zero_mul, mul_zero, Finset.sum_const_zero]
    _ = ∑ i, a i * ∫ z, φ z * (chartFunction (u i) e z).toReal ∂μ := by
      rw [integral_finsetSum _ (fun i _ => (hi i).const_mul (a i))]
      exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _

/-- The differential of every finite real constant is the zero full current. -/
theorem ddcCurrent_const (c : ℝ)
    (hc : IsGlobalQuasiPshPotential (n := m + 1) (M := M) (fun _ => (c : EReal))) :
    ddcCurrent (fun _ => (c : EReal)) hc = 0 := by
  apply GlobalCurrent.ext
  intro e η
  have hddc : chartDDC (canonicalBasis (m + 1)) (fun _ : M => (c : EReal)) e
      (chartIntegrability (fun _ => (c : EReal)) hc e) = 0 := by
    ext v φ
    have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
    change ddC (regularDistribution (canonicalBasis (m + 1)).addHaar
      (fun _ : ComplexModel (m + 1) => c) _) v φ = 0
    rw [hv, ddC_regularDistribution_apply (contDiff_const :
      ContDiff ℝ 2 (fun _ : ComplexModel (m + 1) => c))]
    have hfd : fderiv ℝ (fun _ : ComplexModel (m + 1) => c) = fun _ => 0 :=
      funext fun z => fderiv_const_apply (x := z) c
    simp only [smoothDDC_apply_eq_realHessian (contDiffAt_const :
      ContDiffAt ℝ 2 (fun _ : ComplexModel (m + 1) => c) _),
      realHessian_eq_fderiv, hfd, fderiv_const_apply, zero_apply,
      sub_self, zero_div, mul_zero, integral_zero]
  change toLocalCurrent (canonicalBasis (m + 1)) (degreeTwo (Nat.succ_pos m))
    (chartDDC (canonicalBasis (m + 1)) (fun _ : M => (c : EReal)) e
      (chartIntegrability (fun _ => (c : EReal)) hc e)) η = 0
  rw [hddc, toLocalCurrent, wedgePairing_apply]
  simp

/-- Full distributional differentials add for genuine quasi-PSH functions. -/
theorem ddcCurrent_add {u v : M → EReal}
    (hu : IsGlobalQuasiPshPotential (n := m + 1) u)
    (hv : IsGlobalQuasiPshPotential (n := m + 1) v)
    (hsum : IsGlobalQuasiPshPotential (n := m + 1) (fun x => u x + v x)) :
    ddcCurrent (fun x => u x + v x) hsum = ddcCurrent u hu + ddcCurrent v hv := by
  have hF : IsGlobalQuasiPshPotential (n := m + 1)
      (fun x => ∑ i : Fin 2, ((1 : ℝ) : EReal) * (![u, v] i) x) := by
    simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, EReal.coe_one, one_mul] using hsum
  have h := ddcCurrent_fintypeSum (fun _ : Fin 2 => (1 : ℝ)) ![u, v]
    (by intro i; fin_cases i; exact hu; exact hv) hF
  simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, EReal.coe_one, one_mul, one_smul] using h

/-- Finite real translation preserves the literal full differential current. -/
theorem ddcCurrent_add_const {u : M → EReal}
    (hu : IsGlobalQuasiPshPotential (n := m + 1) u) (c : ℝ)
    (huc : IsGlobalQuasiPshPotential (n := m + 1) (fun x => u x + (c : EReal))) :
    ddcCurrent (fun x => u x + (c : EReal)) huc = ddcCurrent u hu := by
  rw [ddcCurrent_add hu (isGlobalQuasiPshPotential_const c) huc,
    ddcCurrent_const, add_zero]

/-- Actual current positivity survives every finite real translation,
without any change of the smooth background or its closedness. -/
theorem isFormPSH_add_const {θ : SmoothRealForm (m + 1) M 2} {u : M → EReal}
    (hu : IsFormPSH θ u) (c : ℝ) : IsFormPSH θ (fun x => u x + (c : EReal)) := by
  obtain ⟨huq, hpos⟩ := hu
  have huc : IsGlobalQuasiPshPotential (n := m + 1) (fun x => u x + (c : EReal)) := huq.add_smooth
    (show ChartSmooth (n := m + 1) (M := M) (fun _ => c) from fun _ => contDiffOn_const)
  have heq : potentialCurrent θ (fun x => u x + (c : EReal)) huc =
      potentialCurrent θ u huq :=
    congrArg (fun (T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m))) =>
      smoothGlobalCurrent (canonicalBasis (m + 1)) (k := degreeTwo (Nat.succ_pos m)) θ + T)
      (ddcCurrent_add_const huq c huc)
  refine ⟨huc, ?_⟩
  intro e α hα
  have h := hpos e α hα
  simpa only [heq] using h

/-- A finite sum of actual positive currents is positive on every full
variable strongly positive compact test. -/
theorem isPositiveCurrent_finset_sum {ι : Type*} (s : Finset ι)
    (T : ι → GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (hT : ∀ i ∈ s, IsPositiveCurrent (T i)) : IsPositiveCurrent (∑ i ∈ s, T i) := by
  classical
  induction s using Finset.induction_on with
  | empty => intro e α hα; simp
  | insert i s his ih =>
    rw [Finset.sum_insert his]
    exact (hT i (Finset.mem_insert_self i s)).add
      (ih (fun j hj => hT j (Finset.mem_insert_of_mem hj)))

/-- Every actual nonnegative finite combination with coefficient sum at
most one belongs to the same nonclosed Hermitian PSH class. -/
theorem isHermitianPSH_fintype_nonnegSum (ω : Background (m + 1) M)
    {ι : Type*} [Fintype ι] (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hbudget : ∑ i, a i ≤ 1)
    (u : ι → M → EReal) (hu : ∀ i, IsHermitianPSH ω (u i)) :
    IsHermitianPSH ω (fun x => ∑ i, (a i : EReal) * u i x) := by
  classical
  have hF := isGlobalQuasiPshPotential_finset_nonnegSum Finset.univ a
    (fun i _ => ha i) u (fun i _ => (hu i).quasiPshPotential)
  refine ⟨hF, ?_⟩
  let S := smoothGlobalCurrent (canonicalBasis (m + 1))
    (k := degreeTwo (Nat.succ_pos m)) ω.form
  have heq : potentialCurrent ω.form (fun x => ∑ i, (a i : EReal) * u i x) hF =
      (1 - ∑ i, a i) • S +
        ∑ i, a i • potentialCurrent ω.form (u i) (hu i).quasiPshPotential := by
    rw [potentialCurrent, ddcCurrent_fintypeSum a u (fun i => (hu i).quasiPshPotential) hF]
    simp only [potentialCurrent, smul_add, Finset.sum_add_distrib, ← Finset.sum_smul]
    dsimp [S]
    module
  rw [heq]
  exact ((isPositiveCurrent_smooth ω.form ω.isTypeOneOne ω.isSemipositive).smul
    (sub_nonneg.mpr hbudget)).add
    (isPositiveCurrent_finset_sum Finset.univ _
      (fun i _ => (hu i).isPositiveCurrent.smul (ha i)))

end SGPT.PSH.HermitianExtremalCurrentAlgebra
