import SGPT.Foundations.Analysis.Pending.ActualCompactGlobalExteriorStokes
import SGPT.Foundations.Analysis.Pending.LocalizedFullDdcBridge

set_option autoImplicit false
noncomputable section
open Set Filter TopologicalSpace
open scoped Distributions Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.ActualCompactGlobalDdcCalibration

open FirstPass StronglyPositiveForms ProductTestForms ChartPartition
  ActualCompactGlobalPairingCalibration ActualCompactGlobalPairingGeometricEquality
  CompactDifferentialTests FiniteGeodesicStripCharts SingularTopFormLocalization
  LocalizedFullDdcBridge XiaoComplexDifferential

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {k : CurrentDegree n}

private theorem form_cast_coeff {a b : ℕ} (h : a = b)
    (α : SmoothRealForm n M a) (e : ComplexChart n M) (z : ComplexModel n) :
    (h ▸ α : SmoothRealForm n M b).coeff e z = (h ▸ α.coeff e z : RealForm n b) := by
  cases h
  rfl

private theorem test_cast_apply {a b : ℕ} {U : Opens (ComplexModel n)} (h : a = b)
    (τ : _root_.SGPT.Foundations.Analysis.LocalCurrents.TestForm U a) (z : ComplexModel n) :
    (h ▸ τ : _root_.SGPT.Foundations.Analysis.LocalCurrents.TestForm U b) z = (h ▸ τ z : RealForm n b) := by
  cases h
  rfl

private theorem form_cast_smulFun {a b : ℕ} (h : a = b) (σ : M → ℝ)
    (hσ : ChartSmooth (n := n) σ) (α : SmoothRealForm n M a) :
    (h ▸ smulFun σ hσ α : SmoothRealForm n M b) =
      smulFun σ hσ (h ▸ α : SmoothRealForm n M b) := by
  cases h
  rfl

private theorem geometricallyEq_cast {a b : ℕ} (h : a = b)
    {α β : SmoothRealForm n M a} (hαβ : α.GeometricallyEq β) :
    (h ▸ α : SmoothRealForm n M b).GeometricallyEq
      (h ▸ β : SmoothRealForm n M b) := by
  cases h
  exact hαβ

variable [CompactSpace M]

/-- Natural localized zero-form data give the genuine normalized second-order chart pairing.
T is an arbitrary signed genuine global current. hdegree is only a degree equality;
it supplies no pairing, density, compatibility or closedness identity. -/
theorem localized_ddc_pairing (T : GlobalCurrent n M k)
    (hdegree : Module.finrank ℝ (ComplexModel n) - k.val = 2)
    (β : SmoothRealForm n M 0) (e : ComplexChart n M) (χ : M → ℝ)
    (hχ : ChartSmooth (n := n) χ) (hc : IsCompact (tsupport χ))
    (hs : tsupport χ ⊆ e.val.source) :
    pairingLM T (hdegree.symm ▸ ddc (smulFun χ hχ β)) =
      T.inChart e (hdegree.symm ▸
        localDdcTestCLM (localizedTensorTest e χ hχ β hc hs)) := by
  classical
  let τ := localizedTensorTest e χ hχ β hc hs
  obtain ⟨σ, hσ, hσc, hσs, N, -, hχN, hσ1⟩ :=
    exists_chartSmooth_eq_one_nhds (n := n) hc
      (⟨e.val.source, e.val.open_source⟩ : Opens M) hs
  let δ₀ : SmoothRealForm n M 2 := ddc (smulFun χ hχ β)
  have hgeo₀ : δ₀.GeometricallyEq (smulFun σ hσ δ₀) := by
    intro f z hz
    by_cases hx : f.val.symm z ∈ tsupport χ
    · rw [smulFun_coeff, hσ1 _ (hχN hx), one_smul]
    · have hzero : δ₀.coeff f z = 0 :=
        ddc_coeff_eq_zero_of_notMem_cutoff_support f χ hχ β hz hx
      rw [smulFun_coeff, hzero, smul_zero]
  let δ : SmoothRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val) :=
    hdegree.symm ▸ δ₀
  have hgeo : δ.GeometricallyEq (smulFun σ hσ δ) := by
    have hg := geometricallyEq_cast hdegree.symm hgeo₀
    rw [form_cast_smulFun] at hg
    exact hg
  obtain ⟨η, hη, -, hread⟩ := exists_testForm_with_pairing T δ e σ hσ hσc hσs
  have hηD : η = (hdegree.symm ▸ localDdcTestCLM τ) := by
    apply TestFunction.ext
    intro z
    by_cases hz : z ∈ e.val.target
    · rw [hη z, indicator_of_mem hz]
      change σ (e.val.symm z) • δ.coeff e z = _
      rw [← smulFun_coeff σ hσ δ, ← hgeo e hz]
      change (hdegree.symm ▸ δ₀ : SmoothRealForm n M _).coeff e z = _
      rw [form_cast_coeff, test_cast_apply]
      exact congrArg (fun A : RealForm n 2 =>
        (hdegree.symm ▸ A : RealForm n (Module.finrank ℝ (ComplexModel n) - k.val)))
        (localDdc_localizedTensorTest_eq_global_coeff e χ hχ β hc hs hz).symm
    · rw [hη z, indicator_of_notMem hz]
      let Dτ : _root_.SGPT.Foundations.Analysis.LocalCurrents.TestForm (chartTarget e)
          (Module.finrank ℝ (ComplexModel n) - k.val) :=
        hdegree.symm ▸ localDdcTestCLM τ
      exact (image_eq_zero_of_notMem_tsupport (fun h => hz (Dτ.tsupport_subset h))).symm
  calc
    pairingLM T (hdegree.symm ▸ δ₀) = pairingLM T (smulFun σ hσ δ) :=
      pairing_eq_of_geometricallyEq T hgeo
    _ = T.inChart e η := hread
    _ = T.inChart e (hdegree.symm ▸ localDdcTestCLM τ) := congrArg _ hηD

end SGPT.Foundations.Analysis.Pending.ActualCompactGlobalDdcCalibration
