import SGPT.Foundations.Analysis.Pending.NaturalNativeCurrentDifferentials
import SGPT.Foundations.Analysis.Pending.NaturalChartExtensionDifferentials
import SGPT.Foundations.Analysis.Pending.NaturalFullCurrentDdcTranspose
import SGPT.Foundations.Analysis.Pending.NaturalFullCurrentDComplex

/-! # The same native continuous and globally paired current differentials

All five complete mathematical statements and ENTIRE proofs precede source.
Full LF chart-test calibration identifies the actual original operators;
the concrete pairing theorems use internally proved compact transposes.
-/

noncomputable section

open Set TopologicalSpace
open scoped Topology Distributions

namespace SGPT.Foundations.Analysis.Pending.NaturalNativeCurrentPairingDifferentials

open FirstPass _root_.SGPT.Foundations.Analysis.LocalCurrents
  NaturalFullCurrentTranspose NaturalFullCurrentDdcTranspose NaturalFullCurrentDComplex
  NaturalNativeCurrentDifferentials NaturalChartExtensionDifferentials
  NaturalChartTestGeometricExtension NaturalFullNativeSmoothDuality XiaoComplexDifferential

variable {n q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The original complete chart-test pairing is unchanged by exact complementary-degree identification. -/
theorem pairingInDegree_testExtension [CompactSpace M] {k : CurrentDegree n}
    (hk : Module.finrank ℝ (ComplexModel n) - k.val = q)
    (T : GlobalCurrent n M k) (e : ComplexChart n M) (η : TestForm (chartTarget e) q) :
    pairingInDegree hk T (testExtension e η) = nativeChartFunctional hk T e η := by
  subst q
  exact pairing_testExtension T e η

/-- Every entire original native chart test detects the actual current in its exact complementary degree. -/
theorem eq_of_nativeChartFunctional_eq {k : CurrentDegree n}
    (hk : Module.finrank ℝ (ComplexModel n) - k.val = q) {T U : GlobalCurrent n M k}
    (h : ∀ e η, nativeChartFunctional hk T e η = nativeChartFunctional hk U e η) : T = U := by
  apply (nativeDegreeEquiv hk).injective
  apply Subtype.ext
  funext e
  exact ContinuousLinearMap.ext (h e)

/-- Full original global exterior calibration identifies the same original native continuous map. -/
theorem eq_native_exterior_of_pairing [CompactSpace M] (q : ℕ)
    (hq : q + 1 ≤ Module.finrank ℝ (ComplexModel n))
    (δ : GlobalCurrent n M (complementDegree n (q + 1) hq) →ₗ[ℝ]
      GlobalCurrent n M (complementDegree n q (by omega)))
    (hδ : ∀ T γ, pairingInDegree (complementDegree_complement n q (by omega)) (δ T) γ =
      (-1 : ℝ) ^ ((complementDegree n (q + 1) hq).val + 1) *
        pairingInDegree (complementDegree_complement n (q + 1) hq) T γ.exteriorDerivative) :
    δ = (exteriorCurrentCLM q hq).toLinearMap := by
  apply LinearMap.ext
  intro T
  apply eq_of_nativeChartFunctional_eq (complementDegree_complement n q (by omega))
  intro e η
  rw [← pairingInDegree_testExtension, hδ]
  rw [pairingInDegree_congr (complementDegree_complement n (q + 1) hq) T
    (exterior_testExtension_geometricallyEq e η), pairingInDegree_testExtension]
  exact (exteriorCurrentCLM_chart q hq T e η).symm

/-- Compactness alone gives the entire original global pairing for the actual native exterior CLM. -/
theorem exteriorCurrentCLM_pairing [CompactSpace M] (q : ℕ)
    (hq : q + 1 ≤ Module.finrank ℝ (ComplexModel n))
    (T : GlobalCurrent n M (complementDegree n (q + 1) hq)) (γ : SmoothRealForm n M q) :
    pairingInDegree (complementDegree_complement n q (by omega)) (exteriorCurrentCLM q hq T) γ =
      (-1 : ℝ) ^ ((complementDegree n (q + 1) hq).val + 1) *
        pairingInDegree (complementDegree_complement n (q + 1) hq) T γ.exteriorDerivative := by
  obtain ⟨g0, v0, u0, g1, v1, u1, h⟩ := exists_complete_current_d_dc_transposes (n := n) (M := M) q hq
  let _ := g0
  let _ := v0
  let _ := u0
  let _ := g1
  let _ := v1
  let _ := u1
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, Φ0, Φ1, -, -, D, C, Td, Tc, δ, δc,
    -, -, -, -, -, -, hδ, -, -, -⟩ := h
  have heq := eq_native_exterior_of_pairing q hq δ hδ
  rw [heq] at hδ
  exact hδ T γ

/-- The normalized full original complex pairing identifies the same original native continuous map. -/
theorem eq_native_dc_of_pairing [CompactSpace M] (q : ℕ)
    (hq : q + 1 ≤ Module.finrank ℝ (ComplexModel n))
    (δc : GlobalCurrent n M (complementDegree n (q + 1) hq) →ₗ[ℝ]
      GlobalCurrent n M (complementDegree n q (by omega)))
    (hδc : ∀ T γ, pairingInDegree (complementDegree_complement n q (by omega)) (δc T) γ =
      (-1 : ℝ) ^ ((complementDegree n (q + 1) hq).val + 1) *
        pairingInDegree (complementDegree_complement n (q + 1) hq) T (dc γ)) :
    δc = (dcCurrentCLM q hq).toLinearMap := by
  apply LinearMap.ext
  intro T
  apply eq_of_nativeChartFunctional_eq (complementDegree_complement n q (by omega))
  intro e η
  rw [← pairingInDegree_testExtension, hδc]
  rw [pairingInDegree_congr (complementDegree_complement n (q + 1) hq) T
    (dc_testExtension_geometricallyEq e η), pairingInDegree_testExtension]
  exact (dcCurrentCLM_chart q hq T e η).symm

/-- The actual native normalized complex CLM has every original full smooth pairing calibration. -/
theorem dcCurrentCLM_pairing [CompactSpace M] (q : ℕ)
    (hq : q + 1 ≤ Module.finrank ℝ (ComplexModel n))
    (T : GlobalCurrent n M (complementDegree n (q + 1) hq)) (γ : SmoothRealForm n M q) :
    pairingInDegree (complementDegree_complement n q (by omega)) (dcCurrentCLM q hq T) γ =
      (-1 : ℝ) ^ ((complementDegree n (q + 1) hq).val + 1) *
        pairingInDegree (complementDegree_complement n (q + 1) hq) T (dc γ) := by
  obtain ⟨g0, v0, u0, g1, v1, u1, h⟩ := exists_complete_current_d_dc_transposes (n := n) (M := M) q hq
  let _ := g0
  let _ := v0
  let _ := u0
  let _ := g1
  let _ := v1
  let _ := u1
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, Φ0, Φ1, -, -, D, C, Td, Tc, δ, δc,
    -, -, -, -, -, -, -, hδc, -, -⟩ := h
  have heq := eq_native_dc_of_pairing q hq δc hδc
  rw [heq] at hδc
  exact hδc T γ

/-- Positive whole original second pairing identifies the same original native continuous map. -/
theorem eq_native_ddc_of_pairing [CompactSpace M] (q : ℕ)
    (hq : q + 1 + 1 ≤ Module.finrank ℝ (ComplexModel n))
    (Q : GlobalCurrent n M (complementDegree n (q + 1 + 1) hq) →ₗ[ℝ]
      GlobalCurrent n M (complementDegree n q (by omega)))
    (hQ : ∀ T γ, pairingInDegree (complementDegree_complement n q (by omega)) (Q T) γ =
      pairingInDegree (complementDegree_complement n (q + 1 + 1) hq) T (ddc γ)) :
    Q = (ddcCurrentCLM q hq).toLinearMap := by
  apply LinearMap.ext
  intro T
  apply eq_of_nativeChartFunctional_eq (complementDegree_complement n q (by omega))
  intro e η
  rw [← pairingInDegree_testExtension, hQ]
  rw [pairingInDegree_congr (complementDegree_complement n (q + 1 + 1) hq) T
    (ddc_testExtension_geometricallyEq e η), pairingInDegree_testExtension]
  exact (ddcCurrentCLM_chart q hq T e η).symm

/-- The positive original native second CLM has all entire original global smooth pairings. -/
theorem ddcCurrentCLM_pairing [CompactSpace M] (q : ℕ)
    (hq : q + 1 + 1 ≤ Module.finrank ℝ (ComplexModel n))
    (T : GlobalCurrent n M (complementDegree n (q + 1 + 1) hq)) (γ : SmoothRealForm n M q) :
    pairingInDegree (complementDegree_complement n q (by omega)) (ddcCurrentCLM q hq T) γ =
      pairingInDegree (complementDegree_complement n (q + 1 + 1) hq) T (ddc γ) := by
  obtain ⟨g0, v0, u0, g2, v2, u2, h⟩ := exists_complete_current_ddc_transpose (n := n) (M := M) q hq
  let _ := g0
  let _ := v0
  let _ := u0
  let _ := g2
  let _ := v2
  let _ := u2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, Φ0, Φ2, -, -, C, B, Q, -, -, -, hQ, -⟩ := h
  have heq := eq_native_ddc_of_pairing q hq Q hQ
  rw [heq] at hQ
  exact hQ T γ

/-- Genuine global exterior nilpotence holds for the same actual original native continuous operators. -/
theorem exteriorCurrentCLM_squared_eq_zero [CompactSpace M] (q : ℕ)
    (hq : q + 1 + 1 ≤ Module.finrank ℝ (ComplexModel n)) :
    (exteriorCurrentCLM (n := n) (M := M) q (by omega)).comp
      (exteriorCurrentCLM (q + 1) hq) = 0 := by
  have h := transpose_d_squared_eq_zero q hq
    (exteriorCurrentCLM (n := n) (M := M) q (by omega)).toLinearMap
    (exteriorCurrentCLM (q + 1) hq).toLinearMap
    (exteriorCurrentCLM_pairing q (by omega)) (exteriorCurrentCLM_pairing (q + 1) hq)
  apply ContinuousLinearMap.ext
  intro T
  exact congrArg (fun A => A T) h

end SGPT.Foundations.Analysis.Pending.NaturalNativeCurrentPairingDifferentials
