import SGPT.Foundations.Analysis.Pending.DistributionRegularization
import Mathlib.Analysis.Calculus.ContDiff.Bounds

set_option autoImplicit false

noncomputable section
open Set Filter TopologicalSpace
open scoped Topology Distributions ContDiff

namespace SGPT.Foundations.Analysis.Pending.DistributionCutoffExtension

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {U Ω : Opens E}

private def cutoffCompact (χ : 𝓓(U, ℝ)) : Compacts E :=
  ⟨tsupport χ, χ.hasCompactSupport⟩

private def fixedCutoffCLM (χ : 𝓓(U, ℝ)) (K : Compacts E) :
    ContDiffMapSupportedIn E ℝ ⊤ K →L[ℝ]
      ContDiffMapSupportedIn E ℝ ⊤ (cutoffCompact χ) := by
  refine ContDiffMapSupportedIn.mkCLM ℝ (fun φ x => φ x * χ x)
    (fun φ ψ x => by simp [add_mul])
    (fun c φ x => by simp [mul_assoc])
    (fun φ => φ.contDiff.mul χ.contDiff)
    (fun φ x hx => ?_) (fun m _ => ?_)
  · have hχ : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
    simp [hχ]
  · have hc : Continuous fun x => (Finset.range (m+1)).sup'
        Finset.nonempty_range_add_one (fun i => ‖iteratedFDeriv ℝ i χ x‖) :=
      Continuous.finset_sup'_apply Finset.nonempty_range_add_one fun i _ =>
        (χ.contDiff.continuous_iteratedFDeriv (by exact WithTop.coe_le_coe.mpr le_top)).norm
    obtain ⟨C₀, hC₀⟩ := (cutoffCompact χ).isCompact.exists_bound_of_continuousOn
      hc.continuousOn
    have hb : ∀ i ≤ m, ∀ x ∈ cutoffCompact χ,
        ‖iteratedFDeriv ℝ i χ x‖ ≤ ‖C₀‖ := fun i hi x hx =>
      (Finset.le_sup' _ (Finset.mem_range_succ_iff.mpr hi)).trans
        ((Real.le_norm_self _).trans ((hC₀ x hx).trans (Real.le_norm_self C₀)))
    let B := ContinuousLinearMap.mul ℝ ℝ
    refine ⟨Finset.Iic m, ‖B‖ * 2^m * ‖C₀‖, by positivity, fun φ x hx => ?_⟩
    let P := ((Finset.Iic m).sup fun i =>
      ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K i) φ
    calc
      ‖iteratedFDeriv ℝ m (fun y => φ y * χ y) x‖ ≤
          ‖B‖ * ∑ i ∈ Finset.range (m+1), (m.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i φ x‖ * ‖iteratedFDeriv ℝ (m-i) χ x‖ := by
        simpa [B] using (B.bilinearRestrictScalars ℝ).norm_iteratedFDeriv_le_of_bilinear
          φ.contDiff χ.contDiff x (by exact WithTop.coe_le_coe.mpr le_top : (m : ℕ∞ω) ≤ ∞)
      _ ≤ ‖B‖ * ∑ i ∈ Finset.range (m+1), (m.choose i : ℝ) * P * ‖C₀‖ := by
        gcongr with i hi
        · exact (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℝ).trans
            (Seminorm.le_finset_sup_apply (Finset.mem_Iic.mpr
              (Finset.mem_range_succ_iff.mp hi)))
        · exact hb (m-i) (Nat.sub_le m i) x hx
      _ = ‖B‖ * 2^m * ‖C₀‖ * P := by
        simp_rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
        push_cast
        ring

/-- The original LF cutoff map, even when its two open domains are unrelated. -/
def cutoffTestCLM (χ : 𝓓(U, ℝ)) : 𝓓(Ω, ℝ) →L[ℝ] 𝓓(U, ℝ) :=
  TestFunction.limitCLM ℝ
    (fun φ => ⟨fun x => φ x * χ x, φ.contDiff.mul χ.contDiff,
      φ.hasCompactSupport.mul_right, tsupport_mul_subset_right.trans χ.tsupport_subset⟩)
    (fun K _ => (TestFunction.ofSupportedInCLM ℝ χ.tsupport_subset).comp
      (fixedCutoffCLM χ K))
    (fun _ _ _ => by apply TestFunction.ext; intro x; rfl)

/-- Actual extension by the continuous cutoff transpose, for arbitrary signed S. -/
def cutoffExtend (S : 𝓓'(U, ℝ)) (χ : 𝓓(U, ℝ)) : 𝓓'(Ω, ℝ) :=
  S.comp (cutoffTestCLM χ)

/-- Every original local distribution has an internally supplied chart-domain
extension near each point; no extension or equality certificate is an input. -/
theorem exists_extension_near [FiniteDimensional ℝ E]
    (S : 𝓓'(U, ℝ)) (hUΩ : U ≤ Ω) (x : E) (hx : x ∈ U) :
    ∃ (W : Opens E) (hWU : W ≤ U) (R : 𝓓'(Ω, ℝ)),
      x ∈ W ∧ restrictDistribution R (hWU.trans hUΩ) =
        restrictDistribution S hWU := by
  obtain ⟨χ, hχ1, _⟩ := exists_testFunction_eq_one_nhds_compact
    (Ω := U) isCompact_singleton (singleton_subset_iff.mpr hx)
  have he : ∀ᶠ y in 𝓝 x, χ y = 1 := by simpa only [nhdsSet_singleton] using hχ1
  obtain ⟨V, hV1, hVo, hxV⟩ := mem_nhds_iff.mp he
  let W : Opens E := ⟨V ∩ U, hVo.inter U.isOpen⟩
  have hWU : W ≤ U := inter_subset_right
  refine ⟨W, hWU, cutoffExtend S χ, ⟨hxV, hx⟩, ?_⟩
  ext φ
  rw [restrictDistribution_apply, restrictDistribution_apply]
  change S (cutoffTestCLM χ (TestFunction.monoCLM ℝ φ)) =
    S (TestFunction.monoCLM ℝ φ)
  congr 1
  apply TestFunction.ext
  intro y
  change (TestFunction.monoCLM ℝ φ : 𝓓(Ω, ℝ)) y * χ y =
    (TestFunction.monoCLM ℝ φ : 𝓓(U, ℝ)) y
  rw [congrFun (testFunction_inclusion_coe (hWU.trans hUΩ) φ) y,
    congrFun (testFunction_inclusion_coe hWU φ) y]
  by_cases hy : y ∈ W
  · rw [hV1 hy.1, mul_one]
  · have hφ : φ y = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hy (φ.tsupport_subset ht))
    simp [hφ]

end SGPT.Foundations.Analysis.Pending.DistributionCutoffExtension
