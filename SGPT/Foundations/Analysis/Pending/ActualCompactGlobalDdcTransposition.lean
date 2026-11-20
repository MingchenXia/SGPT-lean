import SGPT.Foundations.Analysis.Pending.ActualGlobalBidimensionOneDdc
import SGPT.Foundations.Analysis.Pending.ActualCompactGlobalDdcCalibration
import SGPT.Foundations.Analysis.Pending.GenuineFullStrongGlobalPairing

set_option autoImplicit false

/-! # Full compact normalized second transposition of arbitrary signed currents

The mathematical statements and entire proofs precede this source.
-/

noncomputable section
open Set Filter TopologicalSpace
open scoped Distributions Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.ActualCompactGlobalDdcTransposition

open FirstPass FirstPass.MongeAmpere StronglyPositiveForms ProductTestForms ChartPartition
  ActualBorelWeightedPatchGlobalCurrent ActualGlobalBidimensionOneDdc
  ActualCompactGlobalDdcCalibration ActualCompactGlobalPairingCalibration
  ActualCompactGlobalPairingGeometricEquality SingularTopFormLocalization
  CompactDifferentialTests XiaoComplexDifferential GenuineFullStrongGlobalPairing

theorem bidimensionOne_complement (n : ℕ) :
    Module.finrank ℝ (ComplexModel (n + 1)) - (borelBidimensionOneDegree n).val = 2 := by
  change Module.finrank ℝ (ComplexModel (n + 1)) - 2 * n = 2
  rw [complexModel_real_finrank]
  omega

theorem top_complement (n : ℕ) :
    Module.finrank ℝ (ComplexModel (n + 1)) - (topDegree (n + 1)).val = 0 := by
  change Module.finrank ℝ (ComplexModel (n + 1)) - 2 * (n + 1) = 0
  rw [complexModel_real_finrank]
  omega

private theorem clm_cast_apply {N a b : ℕ} {U : Opens (ComplexModel N)} (h : a = b)
    (F : _root_.SGPT.Foundations.Analysis.LocalCurrents.TestForm U a →L[ℝ] ℝ)
    (G : _root_.SGPT.Foundations.Analysis.LocalCurrents.TestForm U b →L[ℝ] ℝ)
    (hFG : HEq F G) (α : _root_.SGPT.Foundations.Analysis.LocalCurrents.TestForm U b) :
    F (h.symm ▸ α) = G α := by
  cases h
  rw [eq_of_heq hFG]

private theorem realForm_cast_smul {N a b : ℕ} (h : a = b) (c : ℝ) (α : RealForm N a) :
    (h ▸ (c • α) : RealForm N b) = c • (h ▸ α : RealForm N b) := by
  cases h
  rfl

private theorem realForm_cast_zero {N a b : ℕ} (h : a = b) :
    (h ▸ (0 : RealForm N a) : RealForm N b) = 0 := by
  cases h
  rfl

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (n + 1)) M] [IsComplexManifold (n + 1) M]

private theorem form_cast_coeff {a b : ℕ} (h : a = b)
    (α : SmoothRealForm (n + 1) M a) (e : ComplexChart (n + 1) M)
    (z : ComplexModel (n + 1)) :
    (h ▸ α : SmoothRealForm (n + 1) M b).coeff e z =
      (h ▸ α.coeff e z : RealForm (n + 1) b) := by
  cases h
  rfl

private theorem test_cast_apply {a b : ℕ} {U : Opens (ComplexModel (n + 1))} (h : a = b)
    (τ : _root_.SGPT.Foundations.Analysis.LocalCurrents.TestForm U a)
    (z : ComplexModel (n + 1)) :
    (h ▸ τ : _root_.SGPT.Foundations.Analysis.LocalCurrents.TestForm U b) z =
      (h ▸ τ z : RealForm (n + 1) b) := by
  cases h
  rfl

private theorem form_cast_sum {a b m : ℕ} (h : a = b)
    (A : Fin m → SmoothRealForm (n + 1) M a) :
    (h ▸ ∑ i, A i : SmoothRealForm (n + 1) M b) = ∑ i, (h ▸ A i) := by
  cases h
  rfl

private theorem geometricallyEq_cast {a b : ℕ} (h : a = b)
    {α β : SmoothRealForm (n + 1) M a} (hαβ : α.GeometricallyEq β) :
    (h ▸ α : SmoothRealForm (n + 1) M b).GeometricallyEq
      (h ▸ β : SmoothRealForm (n + 1) M b) := by
  cases h
  exact hαβ

private theorem form_cast_zero {a b : ℕ} (h : a = b) :
    (h ▸ (0 : SmoothRealForm (n + 1) M a) : SmoothRealForm (n + 1) M b) = 0 := by
  cases h
  rfl

private theorem ddc_unitForm_zero :
    (ddc (unitForm : SmoothRealForm (n + 1) M 0)).GeometricallyEq 0 := by
  have hdc (e : ComplexChart (n + 1) M) :
      (dc (unitForm : SmoothRealForm (n + 1) M 0)).coeff e = fun _ => 0 := by
    funext z
    have htw : (complexTwist (unitForm : SmoothRealForm (n + 1) M 0)).coeff e =
        fun _ => (coordinateWedgeUnit : RealForm (n + 1) 0).compContinuousLinearMap
          (modelComplexStructure (n + 1)) := rfl
    have hd : extDeriv ((complexTwist (unitForm : SmoothRealForm (n + 1) M 0)).coeff e) z = 0 := by
      rw [htw]
      change (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (ComplexModel (n + 1)) ℝ)
        (fderiv ℝ (fun _ : ComplexModel (n + 1) =>
          (coordinateWedgeUnit : RealForm (n + 1) 0).compContinuousLinearMap
            (modelComplexStructure (n + 1))) z) = 0
      rw [fderiv_const_apply, map_zero]
    simp only [dc, coeff_smul, complexTwist_coeff, SmoothRealForm.exteriorDerivative_coeff, hd]
    ext v
    simp [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  intro e z _
  change extDeriv ((dc (unitForm : SmoothRealForm (n + 1) M 0)).coeff e) z = 0
  rw [hdc]
  change (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (ComplexModel (n + 1)) ℝ)
    (fderiv ℝ (fun _ : ComplexModel (n + 1) => (0 : RealForm (n + 1) 1)) z) = 0
  rw [fderiv_const_apply, map_zero]

variable [CompactSpace M]

/-- Every genuine smooth zero-form has the full actual compact second-transpose pairing. -/
theorem pairing_globalDdc (S : GlobalCurrent (n + 1) M (borelBidimensionOneDegree n))
    (β : SmoothRealForm (n + 1) M 0) :
    pairingLM (globalDdc S) ((top_complement n).symm ▸ β) =
      pairingLM S ((bidimensionOne_complement n).symm ▸
        (ddc β : SmoothRealForm (n + 1) M 2)) := by
  classical
  obtain ⟨m, χ, idx, hχ, -, hχs, hχc, hχ1⟩ :=
    exists_chartSmooth_partitionOfUnity (n := n + 1)
      (fun x : M => (⟨(complexChartAt (n := n + 1) x).val.source,
        (complexChartAt (n := n + 1) x).val.open_source⟩ : Opens M))
      (fun x => ⟨x, mem_complexChartAt_source x⟩)
  let e : Fin m → ComplexChart (n + 1) M := fun i => complexChartAt (idx i)
  let τ (i : Fin m) := localizedTensorTest (e i) (χ i) (hχ i) β (hχc i) (hχs i)
  let η (i : Fin m) : _root_.SGPT.Foundations.Analysis.LocalCurrents.TestForm (chartTarget (e i))
      (Module.finrank ℝ (ComplexModel (n + 1)) - (topDegree (n + 1)).val) :=
    (top_complement n).symm ▸ τ i
  have hη (i : Fin m) (z : ComplexModel (n + 1)) :
      η i z = (e i).val.target.indicator
        (fun y => χ i ((e i).val.symm y) •
          (((top_complement n).symm ▸ β : SmoothRealForm (n + 1) M _).coeff (e i) y)) z := by
    change ((top_complement n).symm ▸ τ i :
      _root_.SGPT.Foundations.Analysis.LocalCurrents.TestForm (chartTarget (e i)) _) z = _
    rw [test_cast_apply]
    by_cases hz : z ∈ (e i).val.target
    · rw [indicator_of_mem hz, form_cast_coeff]
      change ((top_complement n).symm ▸
        (e i).val.target.indicator (fun y => χ i ((e i).val.symm y) • β.coeff (e i) y) z) = _
      rw [indicator_of_mem hz]
      exact realForm_cast_smul _ _ _
    · rw [indicator_of_notMem hz]
      change ((top_complement n).symm ▸
        (e i).val.target.indicator (fun y => χ i ((e i).val.symm y) • β.coeff (e i) y) z) = _
      rw [indicator_of_notMem hz]
      exact realForm_cast_zero _
  have hpieces (i : Fin m) :
      (globalDdc S).inChart (e i) (η i) =
        pairingLM S ((bidimensionOne_complement n).symm ▸
          (ddc (smulFun (χ i) (hχ i) β) : SmoothRealForm (n + 1) M 2)) := by
    calc
      (globalDdc S).inChart (e i) (η i) =
          (bidimensionOneChartFunctional S (e i)) (localDdcTestCLM (τ i)) :=
        clm_cast_apply (top_complement n) _ _ (globalDdc_inChart S (e i)) (τ i)
      _ = S.inChart (e i) ((bidimensionOne_complement n).symm ▸
          localDdcTestCLM (τ i)) :=
        (clm_cast_apply (bidimensionOne_complement n) _ _
          (bidimensionOneChartFunctional_actualChart S (e i)).symm _).symm
      _ = pairingLM S ((bidimensionOne_complement n).symm ▸
          (ddc (smulFun (χ i) (hχ i) β) : SmoothRealForm (n + 1) M 2)) :=
        (localized_ddc_pairing S (bidimensionOne_complement n) β (e i)
          (χ i) (hχ i) (hχc i) (hχs i)).symm
  let A (i : Fin m) := smulFun (χ i) (hχ i) β
  have hsplit : (∑ i, A i) = β := by
    apply smoothRealForm_ext
    intro d z
    let ev : SmoothRealForm (n + 1) M 0 →+ RealForm (n + 1) 0 :=
      { toFun := fun α => α.coeff d z
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    have hsum : (∑ i, A i).coeff d z = ∑ i, (A i).coeff d z := map_sum ev _ _
    rw [hsum]
    simp only [A, smulFun_coeff, ← Finset.sum_smul, hχ1, one_smul]
  have hddc : (ddc β).GeometricallyEq (∑ i, ddc (A i)) := by
    simpa only [hsplit] using ddc_finset_sum_geometricallyEq Finset.univ A
  let Dβ : SmoothRealForm (n + 1) M 2 := ddc β
  let DA (i : Fin m) : SmoothRealForm (n + 1) M 2 := ddc (A i)
  have hcast : ((bidimensionOne_complement n).symm ▸ Dβ :
      SmoothRealForm (n + 1) M _).GeometricallyEq
      (∑ i, ((bidimensionOne_complement n).symm ▸ DA i)) := by
    have hD : Dβ.GeometricallyEq (∑ i, DA i) := hddc
    have hg := geometricallyEq_cast (bidimensionOne_complement n).symm hD
    rw [form_cast_sum] at hg
    exact hg
  calc
    pairingLM (globalDdc S) ((top_complement n).symm ▸ β) =
        ∑ i, (globalDdc S).inChart (e i) (η i) :=
      pairing_eq_sum (globalDdc S) _ m e χ hχ hχc hχs hχ1 η hη
    _ = ∑ i, pairingLM S ((bidimensionOne_complement n).symm ▸
        (ddc (A i) : SmoothRealForm (n + 1) M 2)) :=
      Finset.sum_congr rfl fun i _ => hpieces i
    _ = pairingLM S ((bidimensionOne_complement n).symm ▸
        (ddc β : SmoothRealForm (n + 1) M 2)) := by
      rw [pairing_eq_of_geometricallyEq S hcast, map_sum]

/-- The differentiated signed current cancels the actual constant unit zero-form. -/
theorem pairing_globalDdc_unit_eq_zero
    (S : GlobalCurrent (n + 1) M (borelBidimensionOneDegree n)) :
    pairingLM (globalDdc S) ((top_complement n).symm ▸
      (unitForm : SmoothRealForm (n + 1) M 0)) = 0 := by
  rw [pairing_globalDdc]
  have hg := geometricallyEq_cast (a := 2) (bidimensionOne_complement n).symm
    (ddc_unitForm_zero (n := n) (M := M))
  rw [form_cast_zero] at hg
  rw [pairing_eq_of_geometricallyEq S hg, map_zero]

end SGPT.Foundations.Analysis.Pending.ActualCompactGlobalDdcTransposition
