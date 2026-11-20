import SGPT.Foundations.Analysis.Pending.NaturalConstantTestStokes
import SGPT.Foundations.Analysis.Pending.NaturalNativeCurrentDifferentials
import SGPT.Foundations.Analysis.Pending.CurrentPairing
import SGPT.Foundations.Analysis.FirstPass.GlobalCurrentPotentials

/-! # Original coefficients and the full native exterior current differential

All five complete mathematical statements and ENTIRE proofs precede this
source. The concrete original native operator supplies its own calibration.
-/

noncomputable section

open Function Set TopologicalSpace
open scoped Distributions

namespace SGPT.Foundations.Analysis.Pending.NaturalNativeCurrentCoefficientDifferential

open FirstPass _root_.SGPT.Foundations.Analysis.LocalCurrents
  NaturalConstantTestStokes NaturalNativeCurrentDifferentials NaturalFullCurrentTranspose
  CompactDifferentialTests

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The actual original coefficient is unchanged by its natural whole native test-degree identification. -/
theorem coefficient_block_apply
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
    {k : CurrentDegree n} {q : ℕ}
    (hk : Module.finrank ℝ (ComplexModel n) - k.val = q)
    (T : GlobalCurrent n M k) (e : ComplexChart n M)
    (v : Fin k.val → ComplexModel n) (φ : 𝓓(chartTarget e, ℝ)) :
    T.coefficients b e v φ = nativeChartFunctional hk T e
      (constantTestFormCLM
        (contractVolume (basisVolume
          ((b.reindex (finCongr (show Module.finrank ℝ (ComplexModel n) = k.val + q by omega))).reindex
            finSumFinEquiv.symm)) v) φ) := by
  subst q
  rfl

/-- Whole distribution-valued coefficient differentiation equals the actual signed LF transpose. -/
theorem block_coefficient_exterior {r s : ℕ} {U : Opens (ComplexModel n)}
    (b : Module.Basis (Fin ((r + 1) + s)) ℝ (ComplexModel n))
    (T : TestForm U (s + 1) →L[ℝ] ℝ) :
    currentCoefficients (basisVolume (b.reindex finSumFinEquiv.symm))
        ((-1 : ℤ) ^ (r + 1) • T.comp exteriorTestCLM) =
      exteriorDerivative (currentCoefficients
        (basisVolume (b.reindex
          (finSumFinEquiv.trans (finCongr (show r + (s + 1) = (r + 1) + s by omega))).symm)) T) := by
  apply AlternatingMap.ext
  intro v
  apply DFunLike.ext
  intro φ
  have h := congrArg T (constantTest_signed_exterior b v φ)
  simpa only [currentCoefficients_apply, exteriorDerivative_apply,
    Distribution.lineDerivCLM_apply, sum_apply, smul_apply, map_zsmul, map_neg, map_sum,
    ContinuousLinearMap.comp_apply, nextBlockContraction, precedingBlockContraction,
    Finset.sum_neg_distrib, smul_neg] using h

private theorem coefficients_of_native_signed_calibration
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
    {k0 k1 : CurrentDegree n} {q : ℕ}
    (h0 : Module.finrank ℝ (ComplexModel n) - k0.val = q + 1)
    (h1 : Module.finrank ℝ (ComplexModel n) - k1.val = q)
    (hd : k1.val = k0.val + 1)
    (T : GlobalCurrent n M k0) (U : GlobalCurrent n M k1)
    (hcal : ∀ (e : ComplexChart n M) (η : TestForm (chartTarget e) q),
      nativeChartFunctional h1 U e η =
        (-1 : ℝ) ^ (k0.val + 1) * nativeChartFunctional h0 T e (exteriorTestCLM η))
    (e : ComplexChart n M) (v : Fin k1.val → ComplexModel n) (φ : 𝓓(chartTarget e, ℝ)) :
    U.coefficients b e v φ = exteriorDerivative (T.coefficients b e)
      (v ∘ Fin.cast hd.symm) φ := by
  rcases k0 with ⟨r, hr⟩
  rcases k1 with ⟨t, ht⟩
  change t = r + 1 at hd
  subst t
  dsimp only at h0 h1
  change U.coefficients b e v φ = exteriorDerivative (T.coefficients b e) v φ
  let B := b.reindex (finCongr (show Module.finrank ℝ (ComplexModel n) = (r + 1) + q by omega))
  let F := nativeChartFunctional h0 T e
  let G := nativeChartFunctional h1 U e
  have hG : G = (-1 : ℤ) ^ (r + 1) • F.comp exteriorTestCLM := by
    apply DFunLike.ext
    intro η
    simpa only [smul_apply, ContinuousLinearMap.comp_apply, zsmul_eq_mul,
      Int.cast_pow, Int.cast_neg, Int.cast_one] using hcal e η
  have hinput : T.coefficients b e = currentCoefficients
      (basisVolume (B.reindex
        (finSumFinEquiv.trans (finCongr (show r + (q + 1) = (r + 1) + q by omega))).symm)) F := by
    apply AlternatingMap.ext
    intro u
    apply DFunLike.ext
    intro ψ
    rw [coefficient_block_apply b h0]
    rfl
  rw [coefficient_block_apply b h1, hinput]
  change G (constantTestFormCLM (nextBlockContraction B v) φ) = _
  rw [hG]
  have h := congrArg (fun A => A v φ) (block_coefficient_exterior B F)
  simpa only [currentCoefficients_apply, smul_apply,
    ContinuousLinearMap.comp_apply, nextBlockContraction, Fin.cast_eq_self, comp_id] using h

/-- Every original coefficient and scalar test sees the actual native differential of the original coefficient form. -/
theorem coefficients_exteriorCurrentCLM_apply
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
    (q : ℕ) (hq : q + 1 ≤ Module.finrank ℝ (ComplexModel n))
    (T : GlobalCurrent n M (complementDegree n (q + 1) hq)) (e : ComplexChart n M)
    (v : Fin (complementDegree n q (by omega)).val → ComplexModel n)
    (φ : 𝓓(chartTarget e, ℝ)) :
    (exteriorCurrentCLM q hq T).coefficients b e v φ =
      exteriorDerivative (T.coefficients b e)
        (v ∘ Fin.cast (show (complementDegree n (q + 1) hq).val + 1 =
          (complementDegree n q (by omega)).val by simp only [complementDegree]; omega)) φ := by
  exact coefficients_of_native_signed_calibration b
    (complementDegree_complement n (q + 1) hq)
    (complementDegree_complement n q (by omega))
    (by simp only [complementDegree]; omega) T (exteriorCurrentCLM q hq T)
    (exteriorCurrentCLM_chart q hq T) e v φ

/-- Original coefficient closedness is exactly the kernel condition for this same concrete native current differential. -/
theorem isClosed_iff_exteriorCurrentCLM_eq_zero
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
    (q : ℕ) (hq : q + 1 ≤ Module.finrank ℝ (ComplexModel n))
    (T : GlobalCurrent n M (complementDegree n (q + 1) hq)) :
    T.IsClosed b ↔ exteriorCurrentCLM q hq T = 0 := by
  constructor
  · intro hT
    apply GlobalCurrent.ext
    intro e η
    have hc : (exteriorCurrentCLM q hq T).coefficients b e =
        (0 : GlobalCurrent n M (complementDegree n q (by omega))).coefficients b e := by
      rw [GlobalCurrent.coefficients_zero]
      apply AlternatingMap.ext
      intro v
      apply DFunLike.ext
      intro φ
      rw [coefficients_exteriorCurrentCLM_apply b q hq]
      rw [hT e]
      rfl
    have h := congrArg (fun A => toLocalCurrent b (complementDegree n q (by omega)) A η) hc
    simpa only [GlobalCurrent.coefficients, CurrentPairing.toLocalCurrent_fromLocalCurrent] using h
  · intro hT e
    change exteriorDerivative (T.coefficients b e) = 0
    apply AlternatingMap.ext
    intro w
    apply DFunLike.ext
    intro φ
    let v := w ∘ Fin.cast (show (complementDegree n q (by omega)).val =
      (complementDegree n (q + 1) hq).val + 1 by simp only [complementDegree]; omega)
    have h := coefficients_exteriorCurrentCLM_apply b q hq T e v φ
    have hv : v ∘ Fin.cast (show (complementDegree n (q + 1) hq).val + 1 =
        (complementDegree n q (by omega)).val by simp only [complementDegree]; omega) = w := by
      funext i
      rfl
    rw [hT, GlobalCurrent.coefficients_zero, hv] at h
    exact h.symm

/-- The original closed-current submodule equals the kernel of the same original native exterior CLM. -/
theorem closedSubmodule_eq_exteriorCurrentCLM_ker
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
    (q : ℕ) (hq : q + 1 ≤ Module.finrank ℝ (ComplexModel n)) :
    GlobalCurrent.closedSubmodule (M := M) (k := complementDegree n (q + 1) hq) b =
      (exteriorCurrentCLM (M := M) q hq).ker := by
  apply Submodule.ext
  intro T
  exact isClosed_iff_exteriorCurrentCLM_eq_zero b q hq T

/-- The genuine original top-degree coefficient derivative vanishes, including real dimension zero. -/
theorem isClosed_topDegree
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
    {k : CurrentDegree n} (hk : k.val = Module.finrank ℝ (ComplexModel n))
    (T : GlobalCurrent n M k) : T.IsClosed b := by
  intro e
  change exteriorDerivative (T.coefficients b e) = 0
  apply Module.Basis.ext_alternating b
  intro v hv
  have h := Fintype.card_le_of_injective v hv
  simp only [Fintype.card_fin] at h
  omega

end SGPT.Foundations.Analysis.Pending.NaturalNativeCurrentCoefficientDifferential
