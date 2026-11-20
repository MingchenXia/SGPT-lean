import SGPT.Foundations.Analysis.Pending.NaturalNativeCurrentCoefficientDifferential
import SGPT.Foundations.Analysis.Pending.ActualCompactGlobalExteriorStokes
import SGPT.Foundations.Analysis.Pending.FullSmoothNativeCurrentDifferential

/-! # Original closed currents and genuine full native Stokes

All seven complete mathematical statements and ENTIRE proofs precede this
source. Compactness is used only for the actual global smooth pairing.
-/

noncomputable section

open Set Function TopologicalSpace
open scoped Distributions

namespace SGPT.Foundations.Analysis.Pending.NaturalClosedCurrentStokes

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses
  _root_.SGPT.Foundations.Analysis.LocalCurrents
  NaturalNativeCurrentCoefficientDifferential NaturalNativeCurrentDifferentials
  NaturalFullCurrentTranspose CompactDifferentialTests GlobalCurrents StronglyPositiveForms
  ProductTestForms

variable {n q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

private theorem nativeChartFunctional_cast_apply {k : CurrentDegree n} {a : ℕ}
    (h : Module.finrank ℝ (ComplexModel n) - k.val = a)
    (T : GlobalCurrent n M k) (e : ComplexChart n M) (η : TestForm (chartTarget e) a) :
    nativeChartFunctional h T e η = T.inChart e (h.symm ▸ η) := by
  subst a
  rfl

/-- Original coefficient closedness is precisely annihilation of every actual native exterior chart test. -/
theorem isClosed_iff_native_chart_exterior_eq_zero
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
    (q : ℕ) (hq : q + 1 ≤ Module.finrank ℝ (ComplexModel n))
    (T : GlobalCurrent n M (complementDegree n (q + 1) hq)) :
    T.IsClosed b ↔ ∀ (e : ComplexChart n M) (τ : TestForm (chartTarget e) q),
      nativeChartFunctional (complementDegree_complement n (q + 1) hq) T e
        (exteriorTestCLM τ) = 0 := by
  rw [isClosed_iff_exteriorCurrentCLM_eq_zero b q hq]
  constructor
  · intro hT e τ
    have hz : nativeChartFunctional (complementDegree_complement n q (by omega))
        (exteriorCurrentCLM q hq T) e τ = 0 := by
      rw [hT]
      unfold nativeChartFunctional
      rw [map_zero]
      rfl
    rw [exteriorCurrentCLM_chart] at hz
    exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ (by norm_num))
  · intro hT
    apply (nativeDegreeEquiv (complementDegree_complement n q (by omega))).injective
    rw [map_zero]
    apply Subtype.ext
    funext e
    apply DFunLike.ext
    intro τ
    change nativeChartFunctional (complementDegree_complement n q (by omega))
      (exteriorCurrentCLM q hq T) e τ = 0
    rw [exteriorCurrentCLM_chart, hT e τ, mul_zero]

/-- Original coefficient closedness internally gives the exact original chart Stokes condition. -/
theorem native_chart_exterior_eq_zero_of_isClosed
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
    {k : CurrentDegree n} (T : GlobalCurrent n M k)
    (hdegree : Module.finrank ℝ (ComplexModel n) - k.val = q + 1)
    (hT : T.IsClosed b) (e : ComplexChart n M) (τ : TestForm (chartTarget e) q) :
    T.inChart e (hdegree.symm ▸ exteriorTestCLM τ) = 0 := by
  have hq : q + 1 ≤ Module.finrank ℝ (ComplexModel n) := by omega
  have hk : k = complementDegree n (q + 1) hq := by
    apply Fin.ext
    simp only [complementDegree]
    omega
  subst k
  rw [← nativeChartFunctional_cast_apply hdegree]
  exact (isClosed_iff_native_chart_exterior_eq_zero b q hq T).mp hT e τ

/-- Original coefficient closedness is independent of any choice of ordered model basis. -/
theorem isClosed_iff_of_basis
    (b c : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
    {k : CurrentDegree n} (T : GlobalCurrent n M k) : T.IsClosed b ↔ T.IsClosed c := by
  by_cases hk : k.val = Module.finrank ℝ (ComplexModel n)
  · exact iff_of_true (isClosed_topDegree b hk T) (isClosed_topDegree c hk T)
  · obtain ⟨q, hdef⟩ : ∃ q : ℕ, Module.finrank ℝ (ComplexModel n) - (k.val + 1) = q :=
      ⟨_, rfl⟩
    have hq : q + 1 ≤ Module.finrank ℝ (ComplexModel n) := by omega
    have hkeq : k = complementDegree n (q + 1) hq := by
      apply Fin.ext
      simp only [complementDegree]
      omega
    subst k
    exact (isClosed_iff_exteriorCurrentCLM_eq_zero b q hq T).trans
      (isClosed_iff_exteriorCurrentCLM_eq_zero c q hq T).symm

/-- The actual original closed-current submodule does not depend on its ordered coefficient basis. -/
theorem closedSubmodule_eq_of_basis
    (b c : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
    {k : CurrentDegree n} :
    GlobalCurrent.closedSubmodule (M := M) (k := k) b = GlobalCurrent.closedSubmodule c := by
  apply Submodule.ext
  intro T
  exact isClosed_iff_of_basis b c T

/-- Actual whole compact-test exterior differentiation squares to zero everywhere. -/
theorem exteriorTestCLM_sq {q : ℕ} {U : Opens (ComplexModel n)} (η : TestForm U q) :
    exteriorTestCLM (exteriorTestCLM η) = 0 := by
  apply TestFunction.ext
  intro x
  rw [exteriorTestCLM_apply]
  have hη : (exteriorTestCLM η : ComplexModel n → RealForm n (q + 1)) = extDeriv η :=
    funext (exteriorTestCLM_apply η)
  rw [hη]
  exact extDeriv_extDeriv_apply η.contDiff.contDiffAt
    (by simpa using ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)

/-- The same original native exterior current CLMs square to zero on any complex manifold. -/
theorem exteriorCurrentCLM_squared_eq_zero (q : ℕ)
    (hq : q + 1 + 1 ≤ Module.finrank ℝ (ComplexModel n)) :
    (exteriorCurrentCLM (n := n) (M := M) q (by omega)).comp
      (exteriorCurrentCLM (q + 1) hq) = 0 := by
  apply ContinuousLinearMap.ext
  intro T
  change exteriorCurrentCLM q (by omega) (exteriorCurrentCLM (q + 1) hq T) = 0
  apply (nativeDegreeEquiv (complementDegree_complement n q (by omega))).injective
  rw [map_zero]
  apply Subtype.ext
  funext e
  apply DFunLike.ext
  intro η
  change nativeChartFunctional (complementDegree_complement n q (by omega))
    (exteriorCurrentCLM q (by omega) (exteriorCurrentCLM (q + 1) hq T)) e η = 0
  rw [exteriorCurrentCLM_chart, exteriorCurrentCLM_chart, exteriorTestCLM_sq, map_zero,
    mul_zero, mul_zero]

/-- Every actual native exterior image is originally coefficient closed without compactness. -/
theorem isClosed_exteriorCurrentCLM
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
    (q : ℕ) (hq : q + 1 + 1 ≤ Module.finrank ℝ (ComplexModel n))
    (T : GlobalCurrent n M (complementDegree n (q + 1 + 1) hq)) :
    (exteriorCurrentCLM (q + 1) hq T).IsClosed b := by
  apply (isClosed_iff_exteriorCurrentCLM_eq_zero b q (by omega) _).mpr
  have h := congrArg (fun A => A T) (exteriorCurrentCLM_squared_eq_zero (M := M) q hq)
  simpa only [ContinuousLinearMap.comp_apply, zero_apply] using h

/-- Original coefficient closedness internally supplies all chart hypotheses for genuine global Stokes. -/
theorem pairing_exteriorDerivative_eq_zero_of_isClosed [CompactSpace M]
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
    {k : CurrentDegree n} (T : GlobalCurrent n M k)
    (hdegree : Module.finrank ℝ (ComplexModel n) - k.val = q + 1)
    (hT : T.IsClosed b) (a : SmoothRealForm n M q) :
    ActualCompactGlobalPairingCalibration.pairingLM T (hdegree.symm ▸ a.exteriorDerivative) = 0 :=
  ActualCompactGlobalExteriorStokes.pairing_exteriorDerivative_eq_zero T hdegree
    (native_chart_exterior_eq_zero_of_isClosed b T hdegree hT) a

/-- Actual smooth closed powers supply their own original current closedness and full global Stokes. -/
theorem pairing_exteriorDerivative_smoothCurrent_formPow_eq_zero [CompactSpace M]
    [MeasurableSpace (ComplexModel n)] [BorelSpace (ComplexModel n)]
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
    (C : ClosedRealOneOneForm n M) (p : ℕ) (hp : 2 * p < 2 * n + 1)
    (hdegree : Module.finrank ℝ (ComplexModel n) - 2 * p = q + 1)
    (a : SmoothRealForm n M q) :
    ActualCompactGlobalPairingCalibration.pairingLM
      (smoothGlobalCurrent b (k := ⟨2 * p, by rw [complexModel_real_finrank]; exact hp⟩)
        (formPow C.val p)) (hdegree.symm ▸ a.exteriorDerivative) = 0 :=
  pairing_exteriorDerivative_eq_zero_of_isClosed b _ hdegree
    (FullSmoothNativeCurrentDifferential.isClosed_smoothGlobalCurrent_formPow b C p hp) a

end SGPT.Foundations.Analysis.Pending.NaturalClosedCurrentStokes
