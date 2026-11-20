import SGPT.Foundations.Analysis.Pending.PositiveTestFunctional
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Topology.Instances.Real.Lemmas

set_option autoImplicit false

/-! # Actual LF positive weak distribution limits

The positive functional limit is reconstructed as a genuine continuous
functional on original LF tests, without a supplied continuity or regular
representative. Natural bounds on nonnegative compact tests give limits
along ANY one ultrafilter at ALL original tests. CADG III.1.14/III.1.23;
scalar local step, not global closed-current or class compactness. -/

noncomputable section
open Set Filter TopologicalSpace
open scoped Topology Distributions CompactlySupported
namespace SGPT.Foundations.Analysis.Pending.PositiveDistributionWeakCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {Ω : Opens E}

omit [FiniteDimensional ℝ E] in
private theorem abs_apply_le_of_abs_le (L : 𝓓(Ω, ℝ) →ₗ[ℝ] ℝ)
    (hL : ∀ φ : 𝓓(Ω, ℝ), (∀ x, 0 ≤ φ x) → 0 ≤ L φ)
    (φ χ : 𝓓(Ω, ℝ)) (hdom : ∀ x, |φ x| ≤ χ x) : |L φ| ≤ L χ := by
  have hminus := hL (χ - φ) fun x => by
    change 0 ≤ χ x - φ x
    exact sub_nonneg.mpr ((le_abs_self (φ x)).trans (hdom x))
  have hplus := hL (χ + φ) fun x => by
    change 0 ≤ χ x + φ x
    have := (neg_le_abs (φ x)).trans (hdom x)
    linarith
  rw [map_sub] at hminus
  rw [map_add] at hplus
  exact abs_le.mpr ⟨by linarith,by linarith⟩

/-- Positivity alone internally proves continuity on the actual LF tests.
No measure or desired continuous representative is a hypothesis. -/
theorem continuous_of_positive (L : 𝓓(Ω, ℝ) →ₗ[ℝ] ℝ)
    (hL : ∀ φ : 𝓓(Ω, ℝ), (∀ x, 0 ≤ φ x) → 0 ≤ L φ) : Continuous L := by
  rw [TestFunction.continuous_iff_continuous_comp]
  intro K hKΩ
  obtain ⟨χ,hχ0,hχK⟩ := exists_nonneg_testFunction_one_le_on_compact K.isCompact hKΩ
  let F : ContDiffMapSupportedIn E ℝ ⊤ K →ₗ[ℝ] ℝ :=
    L.comp (TestFunction.ofSupportedInCLM ℝ hKΩ).toLinearMap
  let s : ContDiffMapSupportedIn E ℝ ⊤ K → ℝ := fun g =>
    ‖TestFunction.toBoundedContinuousFunctionCLM ℝ (TestFunction.ofSupportedIn hKΩ g)‖
  have hsn : Continuous s := continuous_norm.comp
    ((TestFunction.toBoundedContinuousFunctionCLM ℝ).continuous.comp
      (TestFunction.ofSupportedInCLM ℝ hKΩ).continuous)
  have hs0 : s 0 = 0 := by
    change ‖TestFunction.toBoundedContinuousFunctionCLM ℝ
      ((TestFunction.ofSupportedInCLM ℝ hKΩ) 0)‖ = 0
    rw [map_zero,map_zero,norm_zero]
  have hbound (g : ContDiffMapSupportedIn E ℝ ⊤ K) : |F g| ≤ s g * L χ := by
    let φ := TestFunction.ofSupportedIn hKΩ g
    have hdom : ∀ x, |φ x| ≤ (s g • χ) x := by
      intro x
      change |φ x| ≤ s g * χ x
      have hs : 0 ≤ s g := norm_nonneg _
      by_cases hx : x ∈ (K : Set E)
      · have hφ : |φ x| ≤ s g := by
          exact (Real.norm_eq_abs _).symm ▸
            (TestFunction.toBoundedContinuousFunctionCLM ℝ φ).norm_coe_le_norm x
        exact hφ.trans (le_mul_of_one_le_right hs (hχK x hx))
      · have hzero : φ x = 0 := image_eq_zero_of_notMem_tsupport
          (fun ht => hx (g.tsupport_subset ht))
        rw [hzero,abs_zero]
        exact mul_nonneg hs (hχ0 x)
    have h := abs_apply_le_of_abs_le L hL φ (s g • χ) hdom
    change |L φ| ≤ s g * L χ
    simpa only [map_smul,smul_eq_mul] using h
  have hF : Continuous F := by
    apply continuous_of_continuousAt_zero F
    rw [ContinuousAt,map_zero]
    refine squeeze_zero_norm (fun g => ?_) (?_ : Tendsto
      (fun g => s g * |L χ|) (𝓝 0) (𝓝 0))
    · rw [Real.norm_eq_abs]
      exact (hbound g).trans (mul_le_mul_of_nonneg_left (le_abs_self _) (norm_nonneg _))
    · simpa only [hs0,zero_mul] using (hsn.tendsto 0).mul_const |L χ|
  exact hF

/-- The SAME positive linear map, now bundled using internally proved LF
continuity, with all original test readings unchanged. -/
def distributionOfPositive (L : 𝓓(Ω, ℝ) →ₗ[ℝ] ℝ)
    (hL : ∀ φ : 𝓓(Ω, ℝ), (∀ x, 0 ≤ φ x) → 0 ≤ L φ) : 𝓓'(Ω, ℝ) :=
  { toLinearMap := L, cont := continuous_of_positive L hL }

/-- Natural bounds on nonnegative compact tests yield an actual LF positive
distribution limit along ANY single ultrafilter at ALL original tests. -/
theorem exists_tendsto_positiveDistribution {ι : Type*} (U : Ultrafilter ι)
    (T : ι → 𝓓'(Ω, ℝ)) (hT : ∀ i, PositiveDistribution (T i))
    (hbound : ∀ χ : 𝓓(Ω, ℝ), (∀ x, 0 ≤ χ x) →
      ∃ B : ℝ, ∀ i, T i χ ≤ B) :
    ∃ S : 𝓓'(Ω, ℝ), PositiveDistribution S ∧ ∀ φ : 𝓓(Ω, ℝ),
      Tendsto (fun i => T i φ) (U : Filter ι) (𝓝 (S φ)) := by
  have hlim (φ : 𝓓(Ω, ℝ)) : ∃ a : ℝ,
      Tendsto (fun i => T i φ) (U : Filter ι) (𝓝 a) := by
    obtain ⟨χ,hχ0,hdom⟩ := exists_nonneg_testFunction_abs_le
      (testFunctionToCompactlySupportedLM Ω φ)
    obtain ⟨B,hB⟩ := hbound χ hχ0
    have hφdom : ∀ x, |φ x| ≤ χ x := by
      intro x
      by_cases hx : x ∈ Ω
      · exact hdom ⟨x,hx⟩
      · rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (φ.tsupport_subset ht)),abs_zero]
        exact hχ0 x
    have hmem (i : ι) : T i φ ∈ Icc (-B) B := abs_le.mp
      ((abs_apply_le_of_abs_le (T i).toLinearMap (hT i) φ χ hφdom).trans (hB i))
    obtain ⟨a,_ha,hlim⟩ := (isCompact_Icc (a := -B) (b := B)).ultrafilter_le_nhds
      (U.map (fun i => T i φ)) (by
        rw [Ultrafilter.coe_map,le_principal_iff]
        exact Filter.mem_map.mpr (Filter.univ_mem' fun i => hmem i))
    exact ⟨a,by simpa only [Tendsto,Ultrafilter.coe_map] using hlim⟩
  choose a ha using hlim
  let L : 𝓓(Ω, ℝ) →ₗ[ℝ] ℝ :=
    { toFun := a
      map_add' := fun φ ψ => tendsto_nhds_unique (ha (φ + ψ))
        (((ha φ).add (ha ψ)).congr fun i => ((T i).map_add φ ψ).symm)
      map_smul' := fun c φ => tendsto_nhds_unique (ha (c • φ))
        (((ha φ).const_smul c).congr fun i => ((T i).map_smul c φ).symm) }
  have hL : ∀ φ : 𝓓(Ω, ℝ), (∀ x, 0 ≤ φ x) → 0 ≤ L φ := by
    intro φ hφ
    exact ge_of_tendsto (ha φ) (Eventually.of_forall fun i => hT i φ hφ)
  exact ⟨distributionOfPositive L hL,hL,ha⟩

end SGPT.Foundations.Analysis.Pending.PositiveDistributionWeakCompactness
