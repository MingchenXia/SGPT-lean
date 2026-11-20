import SGPT.Foundations.Analysis.Pending.PositiveDistributionWeakCompactness
import SGPT.Foundations.Analysis.Pending.CurrentPairing
import SGPT.Foundations.Analysis.FirstPass.GlobalCurrentPotentials

set_option autoImplicit false

/-! Full native current limits from natural positive coefficient domination.
The entire mathematical route and proofs were physically captured before SOURCE.
Class closure and convergence of signed primitives remain separate obligations. -/

noncomputable section
open Set Filter TopologicalSpace
open scoped Topology Distributions
namespace SGPT.Foundations.Analysis.Pending.DominatedFullCurrentWeakCompactness
open FirstPass _root_.SGPT.Foundations.Analysis.LocalCurrents

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {Ω : Opens E}

/-- Natural positive domination gives an actual signed LF limit, not merely
an algebraic functional on a selected test family. -/
theorem exists_tendsto_dominatedDistribution {ι : Type*} (U : Ultrafilter ι)
    (T M : ι → 𝓓'(Ω, ℝ)) (hM : ∀ i, PositiveDistribution (M i))
    (hbound : ∀ χ : 𝓓(Ω, ℝ), (∀ x, 0 ≤ χ x) → ∃ B : ℝ, ∀ i, M i χ ≤ B)
    (C : ℝ) (hC : 0 ≤ C)
    (hdom : ∀ i (φ : 𝓓(Ω, ℝ)), (∀ x, 0 ≤ φ x) → |T i φ| ≤ C * M i φ) :
    ∃ S : 𝓓'(Ω, ℝ), ∀ φ : 𝓓(Ω, ℝ),
      Tendsto (fun i => T i φ) (U : Filter ι) (𝓝 (S φ)) := by
  obtain ⟨τ, _hτ, hτ⟩ :=
    PositiveDistributionWeakCompactness.exists_tendsto_positiveDistribution U M hM hbound
  let P : ι → 𝓓'(Ω, ℝ) := fun i => C • M i + T i
  have hP (i : ι) : PositiveDistribution (P i) := by
    intro φ hφ
    have hd := (abs_le.mp (hdom i φ hφ)).1
    change 0 ≤ C * M i φ + T i φ
    linarith
  have hPb : ∀ χ : 𝓓(Ω, ℝ), (∀ x, 0 ≤ χ x) →
      ∃ B : ℝ, ∀ i, P i χ ≤ B := by
    intro χ hχ
    obtain ⟨B, hB⟩ := hbound χ hχ
    refine ⟨2 * C * B, fun i => ?_⟩
    have hd := (abs_le.mp (hdom i χ hχ)).2
    have hb := mul_le_mul_of_nonneg_left (hB i) hC
    change C * M i χ + T i χ ≤ 2 * C * B
    linarith
  obtain ⟨σ, _hσ, hσ⟩ :=
    PositiveDistributionWeakCompactness.exists_tendsto_positiveDistribution U P hP hPb
  refine ⟨σ - C • τ, fun φ => ?_⟩
  have heq : (fun i => T i φ) = (fun i => P i φ - C * M i φ) := by
    funext i
    change T i φ = (C * M i φ + T i φ) - C * M i φ
    ring
  rw [heq]
  simpa only [_root_.sub_apply, _root_.smul_apply, smul_eq_mul] using
    (hσ φ).sub ((hτ φ).const_smul C)

/-- Every signed full coefficient is an actual LF distribution; uniqueness
internally supplies the entire alternating-map structure of the limit. -/
theorem exists_tendsto_dominatedForm {ι : Type*} {k : ℕ} (U : Ultrafilter ι)
    (A : ι → DistributionForm Ω k) (M : ι → 𝓓'(Ω, ℝ))
    (hM : ∀ i, PositiveDistribution (M i))
    (hbound : ∀ χ : 𝓓(Ω, ℝ), (∀ x, 0 ≤ χ x) → ∃ B : ℝ, ∀ i, M i χ ≤ B)
    (hdom : ∀ v : Fin k → E, ∃ C : ℝ, 0 ≤ C ∧
      ∀ i (φ : 𝓓(Ω, ℝ)), (∀ x, 0 ≤ φ x) → |A i v φ| ≤ C * M i φ) :
    ∃ B : DistributionForm Ω k, ∀ v φ,
      Tendsto (fun i => A i v φ) (U : Filter ι) (𝓝 (B v φ)) := by
  classical
  have hcoeff (v : Fin k → E) : ∃ D : 𝓓'(Ω, ℝ), ∀ φ : 𝓓(Ω, ℝ),
      Tendsto (fun i => A i v φ) (U : Filter ι) (𝓝 (D φ)) := by
    obtain ⟨C, hC, hCv⟩ := hdom v
    exact exists_tendsto_dominatedDistribution U (fun i => A i v) M hM hbound C hC hCv
  choose D hD using hcoeff
  let B : DistributionForm Ω k :=
    { toFun := D
      map_update_add' := fun v j x y => by
        ext φ
        exact tendsto_nhds_unique (hD (Function.update v j (x + y)) φ)
          (((hD (Function.update v j x) φ).add (hD (Function.update v j y) φ)).congr
            fun i => congrArg (fun d : 𝓓'(Ω, ℝ) => d φ)
              ((A i).map_update_add v j x y).symm)
      map_update_smul' := fun v j c x => by
        ext φ
        exact tendsto_nhds_unique (hD (Function.update v j (c • x)) φ)
          (((hD (Function.update v j x) φ).const_smul c).congr
            fun i => congrArg (fun d : 𝓓'(Ω, ℝ) => d φ)
              ((A i).map_update_smul v j c x).symm)
      map_eq_zero_of_eq' := fun v j l hvl hjl => by
        ext φ
        have hz : Tendsto (fun i => A i v φ) (U : Filter ι) (𝓝 0) := by
          have heq : (fun i => A i v φ) = fun _ => (0 : ℝ) := by
            funext i
            rw [(A i).map_eq_zero_of_eq v hvl hjl]
            rfl
          rw [heq]
          exact tendsto_const_nhds
        exact tendsto_nhds_unique (hD v φ) hz }
  exact ⟨B, hD⟩

private theorem tendsto_toLocalCurrent {ι : Type*} (U : Ultrafilter ι)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (k : Fin (Module.finrank ℝ E + 1)) (A : ι → DistributionForm Ω k.val)
    (B : DistributionForm Ω k.val)
    (hlim : ∀ v φ, Tendsto (fun i => A i v φ) (U : Filter ι) (𝓝 (B v φ)))
    (η : TestForm Ω (Module.finrank ℝ E - k.val)) :
    Tendsto (fun i => toLocalCurrent b k (A i) η) (U : Filter ι)
      (𝓝 (toLocalCurrent b k B η)) := by
  simp only [toLocalCurrent, wedgePairing_apply]
  exact tendsto_finsetSum _ fun s _ => (hlim _ _).const_smul (Equiv.Perm.sign s.out)

omit [FiniteDimensional ℝ E] in
private theorem isClosed_of_coefficient_limits {ι : Type*} {k : ℕ} (U : Ultrafilter ι)
    (A : ι → DistributionForm Ω k) (B : DistributionForm Ω k)
    (hA : ∀ i, _root_.SGPT.Foundations.Analysis.LocalCurrents.IsClosed (A i))
    (hlim : ∀ v φ, Tendsto (fun i => A i v φ) (U : Filter ι) (𝓝 (B v φ))) :
    _root_.SGPT.Foundations.Analysis.LocalCurrents.IsClosed B := by
  unfold _root_.SGPT.Foundations.Analysis.LocalCurrents.IsClosed
  ext v φ
  have hd : Tendsto (fun i => exteriorDerivative (A i) v φ) (U : Filter ι)
      (𝓝 (exteriorDerivative B v φ)) := by
    simp only [exteriorDerivative_apply, _root_.sum_apply, _root_.smul_apply,
      Distribution.lineDerivCLM_apply]
    exact tendsto_finsetSum _ fun j _ => ((hlim _ _).neg).const_smul
      ((-1 : ℤ) ^ (j : ℕ))
  have hzero : (fun i => exteriorDerivative (A i) v φ) = fun _ => (0 : ℝ) := by
    funext i
    rw [hA i]
    rfl
  have hz : Tendsto (fun i => exteriorDerivative (A i) v φ) (U : Filter ι) (𝓝 0) := by
    rw [hzero]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hd hz

/-- ANY original closed degree admits a full-test global limit from natural
local positive domination. All chart compatibility and closedness are internal. -/
theorem exists_tendsto_closedGlobalCurrent {n : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {ι : Type*} (U : Ultrafilter ι)
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
    (k : CurrentDegree n) (T : ι → GlobalCurrent n M k)
    (hT : ∀ i, (T i).IsClosed b)
    (Mtrace : (e : ComplexChart n M) → ι → 𝓓'(chartTarget e, ℝ))
    (hM : ∀ e i, PositiveDistribution (Mtrace e i))
    (hbound : ∀ (e : ComplexChart n M) (χ : 𝓓(chartTarget e, ℝ)),
      (∀ x, 0 ≤ χ x) → ∃ B : ℝ, ∀ i, Mtrace e i χ ≤ B)
    (hdom : ∀ (e : ComplexChart n M) (v : Fin k.val → ComplexModel n),
      ∃ C : ℝ, 0 ≤ C ∧ ∀ i (φ : 𝓓(chartTarget e, ℝ)),
        (∀ x, 0 ≤ φ x) → |(T i).coefficients b e v φ| ≤ C * Mtrace e i φ) :
    ∃ S : GlobalCurrent n M k, S.IsClosed b ∧
      ∀ (e : ComplexChart n M)
        (η : TestForm (chartTarget e) (Module.finrank ℝ (ComplexModel n) - k.val)),
        Tendsto (fun i => (T i).inChart e η) (U : Filter ι) (𝓝 (S.inChart e η)) := by
  classical
  have hloc (e : ComplexChart n M) : ∃ A : DistributionForm (chartTarget e) k.val,
      ∀ v φ, Tendsto (fun i => (T i).coefficients b e v φ)
        (U : Filter ι) (𝓝 (A v φ)) :=
    exists_tendsto_dominatedForm U (fun i => (T i).coefficients b e)
      (Mtrace e) (hM e) (hbound e) (hdom e)
  choose A hcoeff using hloc
  let C : ChartCurrentFamily n M k := fun e => toLocalCurrent b k (A e)
  have hfull (e : ComplexChart n M)
      (η : TestForm (chartTarget e) (Module.finrank ℝ (ComplexModel n) - k.val)) :
      Tendsto (fun i => (T i).inChart e η) (U : Filter ι) (𝓝 (C e η)) := by
    have h := tendsto_toLocalCurrent U b k (fun i => (T i).coefficients b e)
      (A e) (hcoeff e) η
    simpa only [GlobalCurrent.coefficients, CurrentPairing.toLocalCurrent_fromLocalCurrent]
      using h
  have hcompat : CurrentFamilyCompatible C := by
    intro e f η θ hrel
    have he := hfull e (TestFunction.monoCLM ℝ η)
    have hf := hfull f (TestFunction.monoCLM ℝ θ)
    have heq : (fun i => (T i).inChart e (TestFunction.monoCLM ℝ η)) =
        (fun i => (T i).inChart f (TestFunction.monoCLM ℝ θ)) := by
      funext i
      exact (T i).overlap e f η θ hrel
    rw [heq] at he
    exact tendsto_nhds_unique he hf
  let S : GlobalCurrent n M k := ⟨C, hcompat⟩
  have hSA (e : ComplexChart n M) : S.coefficients b e = A e :=
    CurrentPairing.fromLocalCurrent_toLocalCurrent b k (A e)
  have hclosed : S.IsClosed b := by
    intro e
    rw [hSA]
    exact isClosed_of_coefficient_limits U (fun i => (T i).coefficients b e)
      (A e) (fun i => hT i e) (hcoeff e)
  exact ⟨S, hclosed, hfull⟩

end SGPT.Foundations.Analysis.Pending.DominatedFullCurrentWeakCompactness
