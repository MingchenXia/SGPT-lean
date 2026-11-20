import SGPT.Foundations.Analysis.Pending.ActualCompactGlobalPairingGeometricEquality
import SGPT.Foundations.Analysis.Pending.CompactDifferentialTests
import SGPT.Foundations.Analysis.Pending.FiniteGeodesicStripCharts

set_option autoImplicit false

/-!
# Exterior Stokes for the actual compact current pairing

Native chart closedness implies exterior Stokes on all actual global smooth
forms of the preceding complementary degree. The proof constructs the chart
tests, their true exterior derivatives and a genuine compact partition of unity.
-/

noncomputable section

open Set Filter TopologicalSpace
open scoped Distributions Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.ActualCompactGlobalExteriorStokes

open FirstPass StronglyPositiveForms ProductTestForms ChartPartition
  ActualCompactGlobalPairingCalibration ActualCompactGlobalPairingGeometricEquality
  ActualWeightedGlobalFormChartTests CompactDifferentialTests FiniteGeodesicStripCharts

variable {n q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {k : CurrentDegree n}

private theorem form_cast_coeff {a b : ℕ} (h : a = b)
    (α : SmoothRealForm n M a) (e : ComplexChart n M) (z : ComplexModel n) :
    (h ▸ α : SmoothRealForm n M b).coeff e z = (h ▸ α.coeff e z : RealForm n b) := by
  cases h
  rfl

private theorem test_cast_apply {a b : ℕ} {U : Opens (ComplexModel n)} (h : a = b)
    (τ : _root_.SGPT.Foundations.Analysis.LocalCurrents.TestForm U a) (z : ComplexModel n) :
    (h ▸ τ : _root_.SGPT.Foundations.Analysis.LocalCurrents.TestForm U b) z =
      (h ▸ τ z : RealForm n b) := by
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
    (h ▸ α : SmoothRealForm n M b).GeometricallyEq (h ▸ β) := by
  cases h
  exact hαβ

private theorem form_cast_sum {a b m : ℕ} (h : a = b)
    (α : Fin m → SmoothRealForm n M a) :
    (h ▸ ∑ i, α i : SmoothRealForm n M b) = ∑ i, (h ▸ α i) := by
  cases h
  rfl

variable [CompactSpace M]

/-- Localized exterior derivatives internally produce the exact native chart pairing. -/
theorem exists_exteriorTest_with_pairing (T : GlobalCurrent n M k)
    (hdegree : Module.finrank ℝ (ComplexModel n) - k.val = q + 1)
    (α : SmoothRealForm n M q) (e : ComplexChart n M) (χ : M → ℝ)
    (hχ : ChartSmooth (n := n) χ) (hcompact : IsCompact (tsupport χ))
    (hsource : tsupport χ ⊆ e.val.source) :
    ∃ τ : _root_.SGPT.Foundations.Analysis.LocalCurrents.TestForm (chartTarget e) q,
      (∀ z, τ z = e.val.target.indicator
        (fun y => χ (e.val.symm y) • α.coeff e y) z) ∧
      tsupport (τ : ComplexModel n → RealForm n q) ⊆ e.val '' tsupport χ ∧
      pairingLM T (hdegree.symm ▸ (smulFun χ hχ α).exteriorDerivative) =
        T.inChart e (hdegree.symm ▸ exteriorTestCLM τ) := by
  classical
  obtain ⟨τ, hτ, hsτ⟩ := exists_testForm e α χ hχ hcompact hsource
  change _root_.SGPT.Foundations.Analysis.LocalCurrents.TestForm (chartTarget e) q at τ
  obtain ⟨σ, hσ, hσc, hσs, N, -, hχN, hσ1⟩ :=
    exists_chartSmooth_eq_one_nhds (n := n) hcompact
      (⟨e.val.source, e.val.open_source⟩ : Opens M) hsource
  let δ₀ := (smulFun χ hχ α).exteriorDerivative
  have hzero (f : ComplexChart n M) (z : ComplexModel n) (hz : z ∈ f.val.target)
      (hx : f.val.symm z ∉ tsupport χ) : δ₀.coeff f z = 0 := by
    have hχzero : (fun y => χ (f.val.symm y)) =ᶠ[𝓝 z] fun _ => 0 :=
      (notMem_tsupport_iff_eventuallyEq.mp hx).comp_tendsto
        (f.val.continuousAt_symm hz).tendsto
    have hfield : (smulFun χ hχ α).coeff f =ᶠ[𝓝 z] fun _ => 0 := by
      filter_upwards [hχzero] with y hy
      simp only [smulFun_coeff, hy, zero_smul]
    change extDeriv ((smulFun χ hχ α).coeff f) z = 0
    rw [hfield.extDeriv_eq]
    change (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (ComplexModel n) ℝ)
      (fderiv ℝ (fun _ : ComplexModel n => (0 : RealForm n q)) z) = 0
    rw [fderiv_const_apply, map_zero]
  have hgeo₀ : δ₀.GeometricallyEq (smulFun σ hσ δ₀) := by
    intro f z hz
    by_cases hx : f.val.symm z ∈ tsupport χ
    · rw [smulFun_coeff, hσ1 _ (hχN hx), one_smul]
    · rw [smulFun_coeff, hzero f z hz hx, smul_zero]
  let δ : SmoothRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val) :=
    hdegree.symm ▸ δ₀
  have hgeo : δ.GeometricallyEq (smulFun σ hσ δ) := by
    have hg := geometricallyEq_cast hdegree.symm hgeo₀
    rw [form_cast_smulFun] at hg
    exact hg
  obtain ⟨η, hη, -, hread⟩ := exists_testForm_with_pairing T δ e σ hσ hσc hσs
  have hηD : η = (hdegree.symm ▸ exteriorTestCLM τ) := by
    apply TestFunction.ext
    intro z
    by_cases hz : z ∈ e.val.target
    · rw [hη z, indicator_of_mem hz]
      change σ (e.val.symm z) • δ.coeff e z = _
      rw [← smulFun_coeff σ hσ δ, ← hgeo e hz]
      change (hdegree.symm ▸ δ₀ : SmoothRealForm n M _).coeff e z = _
      rw [form_cast_coeff, test_cast_apply]
      have hτloc : (τ : ComplexModel n → RealForm n q) =ᶠ[𝓝 z]
          (smulFun χ hχ α).coeff e := by
        filter_upwards [e.val.open_target.mem_nhds hz] with y hy
        exact (hτ y).trans (indicator_of_mem hy _)
      exact congrArg (fun A : RealForm n (q + 1) =>
        (hdegree.symm ▸ A : RealForm n (Module.finrank ℝ (ComplexModel n) - k.val)))
        (hτloc.extDeriv_eq.symm.trans (exteriorTestCLM_apply τ z).symm)
    · rw [hη z, indicator_of_notMem hz]
      let Dτ : _root_.SGPT.Foundations.Analysis.LocalCurrents.TestForm (chartTarget e)
          (Module.finrank ℝ (ComplexModel n) - k.val) := hdegree.symm ▸ exteriorTestCLM τ
      exact (image_eq_zero_of_notMem_tsupport (fun h => hz (Dτ.tsupport_subset h))).symm
  refine ⟨τ, hτ, hsτ, ?_⟩
  calc
    pairingLM T (hdegree.symm ▸ δ₀) = pairingLM T (smulFun σ hσ δ) :=
      pairing_eq_of_geometricallyEq T hgeo
    _ = T.inChart e η := hread
    _ = T.inChart e (hdegree.symm ▸ exteriorTestCLM τ) := congrArg _ hηD

/-- Genuine local chart closedness gives Stokes for every actual global smooth form. -/
theorem pairing_exteriorDerivative_eq_zero (T : GlobalCurrent n M k)
    (hdegree : Module.finrank ℝ (ComplexModel n) - k.val = q + 1)
    (hclosed : ∀ (e : ComplexChart n M)
      (τ : _root_.SGPT.Foundations.Analysis.LocalCurrents.TestForm (chartTarget e) q),
        T.inChart e (hdegree.symm ▸ exteriorTestCLM τ) = 0)
    (α : SmoothRealForm n M q) :
    pairingLM T (hdegree.symm ▸ α.exteriorDerivative) = 0 := by
  classical
  obtain ⟨m, χ, idx, hχ, -, hχs, hχc, hχ1⟩ :=
    exists_chartSmooth_partitionOfUnity (n := n)
      (fun x : M => (⟨(complexChartAt (n := n) x).val.source,
        (complexChartAt (n := n) x).val.open_source⟩ : Opens M))
      (fun x => ⟨x, mem_complexChartAt_source x⟩)
  let e : Fin m → ComplexChart n M := fun i => complexChartAt (idx i)
  have hpieces (i : Fin m) :
      pairingLM T (hdegree.symm ▸ (smulFun (χ i) (hχ i) α).exteriorDerivative) = 0 := by
    obtain ⟨τ, -, -, hp⟩ :=
      exists_exteriorTest_with_pairing T hdegree α (e i) (χ i) (hχ i) (hχc i) (hχs i)
    exact hp.trans (hclosed (e i) τ)
  have hsplit₀ : α.exteriorDerivative.GeometricallyEq
      (∑ i, (smulFun (χ i) (hχ i) α).exteriorDerivative) := by
    intro f z hz
    have hfun : α.coeff f = fun y => ∑ i, (smulFun (χ i) (hχ i) α).coeff f y := by
      funext y
      simp only [smulFun_coeff, ← Finset.sum_smul, hχ1, one_smul]
    have hcoeffsum : (∑ i, (smulFun (χ i) (hχ i) α).exteriorDerivative).coeff f z =
        ∑ i, (smulFun (χ i) (hχ i) α).exteriorDerivative.coeff f z := by
      let ev : SmoothRealForm n M (q + 1) →+ RealForm n (q + 1) :=
        { toFun := fun β => β.coeff f z
          map_zero' := rfl
          map_add' := fun _ _ => rfl }
      exact map_sum ev _ _
    rw [hcoeffsum]
    change ContinuousAlternatingMap.alternatizeUncurryFin (fderiv ℝ (α.coeff f) z) =
      ∑ i, ContinuousAlternatingMap.alternatizeUncurryFin
        (fderiv ℝ ((smulFun (χ i) (hχ i) α).coeff f) z)
    rw [hfun, fderiv_fun_sum fun i _ =>
      (((smulFun (χ i) (hχ i) α).smooth f).contDiffAt
        (f.val.open_target.mem_nhds hz)).differentiableAt (by simp)]
    exact map_sum (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ
      (ComplexModel n) ℝ) _ _
  have hsplit : SmoothRealForm.GeometricallyEq
      (hdegree.symm ▸ α.exteriorDerivative : SmoothRealForm n M _)
      (∑ i, (hdegree.symm ▸
        (smulFun (χ i) (hχ i) α).exteriorDerivative)) := by
    have hg := geometricallyEq_cast hdegree.symm hsplit₀
    rw [form_cast_sum] at hg
    exact hg
  rw [pairing_eq_of_geometricallyEq T hsplit, map_sum]
  exact Finset.sum_eq_zero fun i _ => hpieces i

end SGPT.Foundations.Analysis.Pending.ActualCompactGlobalExteriorStokes
