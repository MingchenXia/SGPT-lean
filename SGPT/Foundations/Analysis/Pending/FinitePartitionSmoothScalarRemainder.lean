import SGPT.Foundations.Analysis.Pending.SignedPotentialWeightedSmoothDifference
import SGPT.Foundations.Analysis.Pending.FiniteGlobalScalarCurrent

set_option autoImplicit false

/-! SAME original signed current, its literal finite scalar distribution gluing,
and internally smooth local remainders. Entire BP precedes this source.
No global Bott--Chern representative or incoming regularity certificate. -/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Distributions ContDiff Topology

namespace SGPT.Foundations.Analysis.Pending.FinitePartitionSmoothScalarRemainder
open FirstPass _root_.SGPT.Foundations.Analysis.LocalCurrents
  DistributionFullChartCutoffTransport FiniteScalarDistributionGluing
  SignedPotentialWeightedSmoothDifference LocalBedfordTaylorSmooth LelongPoincareDivisor
  ClosedCurrentLocalPotentialPartition

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

private theorem restrict_mul {Ω V : Opens (ComplexModel n)} (hV : V ≤ Ω)
    (R : 𝓓'(Ω, ℝ)) {a : ComplexModel n → ℝ} (ha : ContDiffOn ℝ ∞ a Ω) :
    restrictDistribution (precompLM (mulSmoothOnCLM ha) R) hV =
      precompLM (mulSmoothOnCLM (ha.mono hV)) (restrictDistribution R hV) := by
  ext φ
  change R (mulSmoothOnCLM ha (TestFunction.monoCLM ℝ φ)) =
    R (TestFunction.monoCLM ℝ (mulSmoothOnCLM (ha.mono hV) φ))
  congr 1
  apply TestFunction.ext
  intro z
  rw [mulSmoothOnCLM_apply, testFunction_inclusion_coe hV,
    testFunction_inclusion_coe hV, mulSmoothOnCLM_apply]

private theorem restrict_sub {Ω V : Opens (ComplexModel n)} (hV : V ≤ Ω)
    (R S : 𝓓'(Ω, ℝ)) :
    restrictDistribution (R - S) hV =
      restrictDistribution R hV - restrictDistribution S hV := by
  ext φ
  rfl

private theorem weighted_zero_of_weight_zero (e f : ComplexChart n M)
    (χ : M → ℝ) (hχ : ChartSmooth (n := n) χ) (hc : IsCompact (tsupport χ))
    (hs : tsupport χ ⊆ f.val.source) {V : Opens (ComplexModel n)}
    (hVe : V ≤ chartTarget e) (R : 𝓓'(chartTarget e, ℝ))
    (S : 𝓓'(chartTarget f, ℝ)) (hzero : ∀ z ∈ V, χ (e.val.symm z) = 0) :
    precompLM (mulSmoothOnCLM ((hχ e).mono hVe)) (restrictDistribution R hVe) -
        restrictDistribution (weightedChartDistribution e f χ hχ hc hs S) hVe = 0 := by
  ext φ
  have hm : mulSmoothOnCLM ((hχ e).mono hVe) φ = 0 := by
    apply TestFunction.ext
    intro z
    rw [mulSmoothOnCLM_apply]
    by_cases hz : z ∈ V
    · rw [hzero z hz, mul_zero]
      rfl
    · have hφ : φ z = 0 := image_eq_zero_of_notMem_tsupport
        (fun h => hz (φ.tsupport_subset h))
      simp [hφ]
  have ht : fullChartTestCLM e f χ hχ hc hs (TestFunction.monoCLM ℝ φ) = 0 := by
    apply TestFunction.ext
    intro z
    rw [fullChartTestCLM_value]
    by_cases hz : z ∈ (chartTransition f e).source
    · rw [if_pos hz, testFunction_inclusion_coe hVe]
      by_cases hφ : φ ((chartTransition f e) z) = 0
      · simp [hφ]
      have hy : (chartTransition f e) z ∈ V :=
        φ.tsupport_subset (subset_tsupport _ hφ)
      have heinv : e.val.symm ((chartTransition f e) z) = f.val.symm z :=
        e.val.left_inv hz.2
      have hχzero : χ (f.val.symm z) = 0 := by
        rw [← heinv]
        exact hzero _ hy
      simp [hχzero]
    · simp [hz]
  change R (TestFunction.monoCLM ℝ (mulSmoothOnCLM ((hχ e).mono hVe) φ)) -
      S (fullChartTestCLM e f χ hχ hc hs (TestFunction.monoCLM ℝ φ)) = 0
  rw [hm, ht]
  simp

variable (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
  (hn : 0 < n)

/-- The SAME actual finite scalar family has internally smooth local remainders
against every natural local scalar potential of the original signed current. -/
theorem exists_smooth_remainder {ι : Type*} [Fintype ι]
    (μ : Measure (ComplexModel n)) [μ.IsAddHaarMeasure]
    (T : GlobalCurrent n M (degreeTwo hn))
    (g : ι → ComplexChart n M) (P : ι → Opens (ComplexModel n))
    (hP : ∀ j, P j ≤ chartTarget (g j))
    (R : ∀ j, 𝓓'(chartTarget (g j), ℝ))
    (χ : ι → M → ℝ) (hχ : ∀ j, ChartSmooth (n := n) (χ j))
    (hc : ∀ j, IsCompact (tsupport (χ j)))
    (hs : ∀ j, tsupport (χ j) ⊆ (g j).val.source)
    (hsP : ∀ j, tsupport (χ j) ⊆ {y | y ∈ (g j).val.source ∧ (g j).val y ∈ P j})
    (hsum : ∀ y, ∑ j, χ j y = 1)
    (hR : ∀ j, ddC (restrictDistribution (R j) (hP j)) =
      restrictForm (T.coefficients b (g j)) (hP j))
    (e : ComplexChart n M) {Ω : Opens (ComplexModel n)} (hΩ : Ω ≤ chartTarget e)
    (R₀ : 𝓓'(chartTarget e, ℝ))
    (hR₀ : ddC (restrictDistribution R₀ hΩ) = restrictForm (T.coefficients b e) hΩ)
    (x : ComplexModel n) (hx : x ∈ Ω) :
    ∃ (V : Opens (ComplexModel n)) (hVe : V ≤ chartTarget e) (k : ComplexModel n → ℝ),
      x ∈ V ∧ V ≤ Ω ∧ ContDiffOn ℝ ∞ k V ∧
      ∃ hk : LocallyIntegrableOn k V μ,
        restrictDistribution (R₀ - finiteScalarFamily g χ hχ hc hs R e) hVe =
          regularDistribution μ k hk := by
  classical
  have hlocal : ∀ j, ∃ (V : Opens (ComplexModel n)) (hVe : V ≤ chartTarget e)
      (ha : ContDiffOn ℝ ∞ (fun z => χ j (e.val.symm z)) V) (k : ComplexModel n → ℝ),
      x ∈ V ∧ V ≤ Ω ∧ ContDiffOn ℝ ∞ k V ∧
      ∃ hk : LocallyIntegrableOn k V μ,
        precompLM (mulSmoothOnCLM ha) (restrictDistribution R₀ hVe) -
            restrictDistribution (weightedChartDistribution e (g j) (χ j) (hχ j)
              (hc j) (hs j) (R j)) hVe = regularDistribution μ k hk := by
    intro j
    by_cases hsupport : e.val.symm x ∈ tsupport (χ j)
    · have hxe : x ∈ e.val.target := hΩ hx
      have hxs := (hsP j) hsupport
      have hxf : x ∈ (chartTransition e (g j)).source := ⟨hxe, hxs.1⟩
      have hxp : (chartTransition e (g j)) x ∈ P j := hxs.2
      obtain ⟨V, hVe, ha, k, hxV, hVΩ, _hsub, hk, hL, hreg⟩ :=
        exists_weighted_smooth_difference b hn μ T e (g j) hΩ (hP j) R₀ (R j)
          hR₀ (hR j) (χ j) (hχ j) (hc j) (hs j) x hx hxf hxp
      exact ⟨V, hVe, ha, k, hxV, hVΩ, hk, hL, hreg⟩
    · let V : Opens (ComplexModel n) :=
        ⟨Ω ∩ (e.val.target ∩ e.val.symm ⁻¹' (tsupport (χ j))ᶜ),
          Ω.isOpen.inter (e.val.symm.isOpen_inter_preimage
            (isClosed_tsupport (χ j)).isOpen_compl)⟩
      have hxV : x ∈ V := ⟨hx, hΩ hx, hsupport⟩
      have hVe : V ≤ chartTarget e := fun z hz => hΩ hz.1
      have ha : ContDiffOn ℝ ∞ (fun z => χ j (e.val.symm z)) V := (hχ j e).mono hVe
      have hzero : ∀ z ∈ V, χ j (e.val.symm z) = 0 :=
        fun z hz => image_eq_zero_of_notMem_tsupport hz.2.2
      have hk : ContDiffOn ℝ ∞ (fun _ : ComplexModel n => (0 : ℝ)) V := contDiffOn_const
      have hL : LocallyIntegrableOn (fun _ : ComplexModel n => (0 : ℝ)) V μ :=
        hk.continuousOn.locallyIntegrableOn V.isOpen.measurableSet
      refine ⟨V, hVe, ha, (fun _ => 0), hxV, (fun z hz => hz.1), hk, hL, ?_⟩
      rw [weighted_zero_of_weight_zero e (g j) (χ j) (hχ j) (hc j) (hs j)
        hVe R₀ (R j) hzero]
      ext φ
      rw [regularDistribution_apply]
      simp
  choose V hVe ha k hxV hVΩ hk hL hreg using hlocal
  let U : Opens (ComplexModel n) := Ω ⊓ ⨅ j, V j
  have hUΩ : U ≤ Ω := inf_le_left
  have hUV : ∀ j, U ≤ V j := fun j => inf_le_right.trans (iInf_le V j)
  have hUe : U ≤ chartTarget e := hUΩ.trans hΩ
  have hxU : x ∈ U := by
    change x ∈ (Ω : Set (ComplexModel n)) ∩
      ((⨅ j, V j : Opens (ComplexModel n)) : Set (ComplexModel n))
    rw [Opens.coe_iInf]
    exact ⟨hx, mem_iInter.mpr hxV⟩
  let f : ComplexModel n → ℝ := fun z => ∑ j, k j z
  have hf : ContDiffOn ℝ ∞ f U := ContDiffOn.sum fun j _ => (hk j).mono (hUV j)
  have hLf : LocallyIntegrableOn f U μ :=
    locallyIntegrableOn_finsetSum Finset.univ fun j _ => (hL j).mono_set (hUV j)
  have hj : ∀ j,
      precompLM (mulSmoothOnCLM ((hχ j e).mono hUe)) (restrictDistribution R₀ hUe) -
          restrictDistribution (weightedChartDistribution e (g j) (χ j) (hχ j)
            (hc j) (hs j) (R j)) hUe =
        regularDistribution μ (k j) ((hL j).mono_set (hUV j)) := by
    intro j
    have h := congrArg (fun D : 𝓓'(V j, ℝ) => restrictDistribution D (hUV j)) (hreg j)
    rw [restrict_sub, restrict_mul, restrictDistribution_trans,
      restrictDistribution_trans, restrictDistribution_regularDistribution] at h
    exact h
  refine ⟨U, hUe, f, hxU, hUΩ, hf, hLf, ?_⟩
  have hsumD : restrictDistribution (R₀ - finiteScalarFamily g χ hχ hc hs R e) hUe =
      ∑ j, (precompLM (mulSmoothOnCLM ((hχ j e).mono hUe))
          (restrictDistribution R₀ hUe) -
        restrictDistribution (weightedChartDistribution e (g j) (χ j) (hχ j)
          (hc j) (hs j) (R j)) hUe) := by
    ext φ
    have hm : (∑ j, mulSmoothOnCLM ((hχ j e).mono hUe) φ) = φ := by
      apply TestFunction.ext
      intro z
      simp only [_root_.sum_apply, mulSmoothOnCLM_apply]
      rw [← Finset.mul_sum, hsum, mul_one]
    have hi : (TestFunction.monoCLM ℝ φ : 𝓓(chartTarget e, ℝ)) =
        ∑ j, (TestFunction.monoCLM ℝ (mulSmoothOnCLM ((hχ j e).mono hUe) φ) :
          𝓓(chartTarget e, ℝ)) := by
      rw [← map_sum, hm]
    simp only [restrictDistribution_apply, finiteScalarFamily, _root_.sum_apply,
      _root_.sub_apply]
    rw [hi, map_sum, Finset.sum_sub_distrib]
    rfl
  rw [hsumD]
  calc
    (∑ j, (precompLM (mulSmoothOnCLM ((hχ j e).mono hUe)) (restrictDistribution R₀ hUe) -
        restrictDistribution (weightedChartDistribution e (g j) (χ j) (hχ j)
          (hc j) (hs j) (R j)) hUe)) =
        ∑ j, regularDistribution μ (k j) ((hL j).mono_set (hUV j)) :=
      Finset.sum_congr rfl fun j _ => hj j
    _ = regularDistribution μ f hLf :=
      (regularDistribution_sum Finset.univ (fun j => (hL j).mono_set (hUV j)) hLf).symm

/-- Compactness selects the actual original finite family BEFORE all later
local scalar potentials; their smooth remainders are then internally supplied. -/
theorem exists_partition_with_smooth_remainders [CompactSpace M]
    (μ : Measure (ComplexModel n)) [μ.IsAddHaarMeasure]
    (T : GlobalCurrent n M (degreeTwo hn)) (hclosed : T.IsClosed b)
    (h11 : T.IsTypeOneOne b hn) :
    ∃ (m : ℕ) (g : Fin m → ComplexChart n M) (P : Fin m → Opens (ComplexModel n))
      (hP : ∀ j, P j ≤ chartTarget (g j)) (R : ∀ j, 𝓓'(chartTarget (g j), ℝ))
      (χ : Fin m → M → ℝ) (hχ : ∀ j, ChartSmooth (n := n) (χ j))
      (hc : ∀ j, IsCompact (tsupport (χ j)))
      (hs : ∀ j, tsupport (χ j) ⊆ (g j).val.source),
      (∀ j y, 0 ≤ χ j y) ∧
      (∀ j, tsupport (χ j) ⊆ {y | y ∈ (g j).val.source ∧ (g j).val y ∈ P j}) ∧
      (∀ y, ∑ j, χ j y = 1) ∧
      (∀ j, ddC (restrictDistribution (R j) (hP j)) =
        restrictForm (T.coefficients b (g j)) (hP j)) ∧
      ∀ (e : ComplexChart n M) (Ω : Opens (ComplexModel n))
        (hΩ : Ω ≤ chartTarget e) (R₀ : 𝓓'(chartTarget e, ℝ)),
        ddC (restrictDistribution R₀ hΩ) = restrictForm (T.coefficients b e) hΩ →
        ∀ x ∈ Ω, ∃ (V : Opens (ComplexModel n)) (hVe : V ≤ chartTarget e)
          (k : ComplexModel n → ℝ), x ∈ V ∧ V ≤ Ω ∧ ContDiffOn ℝ ∞ k V ∧
          ∃ hk : LocallyIntegrableOn k V μ,
            restrictDistribution (R₀ - finiteScalarFamily g χ hχ hc hs R e) hVe =
              regularDistribution μ k hk := by
  obtain ⟨m, g, P, hP, R, χ, hχ, hnon, hsP, hc, hsum, hR⟩ :=
    exists_local_potential_partition b hn T hclosed h11
  have hs : ∀ j, tsupport (χ j) ⊆ (g j).val.source := fun j y hy => (hsP j hy).1
  refine ⟨m, g, P, hP, R, χ, hχ, hc, hs, hnon, hsP, hsum, hR, ?_⟩
  intro e Ω hΩ R₀ hR₀ x hx
  exact exists_smooth_remainder b hn μ T g P hP R χ hχ hc hs hsP hsum hR
    e hΩ R₀ hR₀ x hx

end SGPT.Foundations.Analysis.Pending.FinitePartitionSmoothScalarRemainder
