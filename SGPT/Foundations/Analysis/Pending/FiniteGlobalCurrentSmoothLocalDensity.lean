import SGPT.Foundations.Analysis.Pending.FinitePartitionSmoothScalarRemainder
import SGPT.Foundations.Analysis.Pending.FiniteGlobalScalarDdc
import SGPT.Foundations.Analysis.Pending.LogWeightFactorization

set_option autoImplicit false

/-! Actual full smooth local coefficients of the SAME global remainder
T - native ddC of its internally chosen finite scalar partition.
No prescribed coefficient density, class or global form. ENTIRE BP preceded source. -/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Distributions ContDiff Topology

namespace SGPT.Foundations.Analysis.Pending.FiniteGlobalCurrentSmoothLocalDensity
open FirstPass _root_.SGPT.Foundations.Analysis.LocalCurrents
  LelongPoincareDivisor ClosedCurrentLocalPotentialPartition
  FinitePartitionSmoothScalarRemainder FiniteScalarDistributionGluing FiniteGlobalScalarDdc

variable {n : ℕ}

/-- The original smooth scalar has the COMPLETE smooth alternating form as its
native ddC density, for any actual Haar measure and all dimensions. -/
theorem ddC_regular_eq_regularForm (μ : Measure (ComplexModel n)) [μ.IsAddHaarMeasure]
    {V : Opens (ComplexModel n)} {k : ComplexModel n → ℝ} (hk : ContDiffOn ℝ ∞ k V) :
    ddC (regularDistribution μ k
      (hk.continuousOn.locallyIntegrableOn V.isOpen.measurableSet)) =
      regularFormDistribution μ (smoothDDC k)
        ((LogWeightFactorization.smoothDDC_contDiffOn V.isOpen hk).continuousOn.locallyIntegrableOn
          V.isOpen.measurableSet) := by
  ext v φ
  have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
  have hdL : LocallyIntegrableOn (smoothDDC k) V μ :=
    (LogWeightFactorization.smoothDDC_contDiffOn V.isOpen hk).continuousOn.locallyIntegrableOn
      V.isOpen.measurableSet
  have hdint : Integrable (fun z => φ z • smoothDDC k z) μ :=
    φ.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ) hdL
  rw [hv, ddC_regularDistribution_apply_of_contDiffOn hk,
    regularFormDistribution_apply]
  rw [← formEvaluationCLM_apply,
    ← (formEvaluationCLM ![v 0, v 1]).integral_comp_comm hdint]
  rfl

private theorem ddC_sub {V : Opens (ComplexModel n)} (R S : 𝓓'(V, ℝ)) :
    ddC (R - S) = ddC R - ddC S := by
  ext v : 1
  have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
  rw [hv, AlternatingMap.sub_apply, ddC_apply, ddC_apply, ddC_apply]
  simp only [map_sub, smul_sub]
  abel

private theorem restrict_sub {Ω V : Opens (ComplexModel n)} (hV : V ≤ Ω)
    (R S : 𝓓'(Ω, ℝ)) :
    restrictDistribution (R - S) hV =
      restrictDistribution R hV - restrictDistribution S hV := by
  ext φ
  rfl

private theorem restrictForm_sub {Ω V : Opens (ComplexModel n)} {r : ℕ}
    (hV : V ≤ Ω) (A B : DistributionForm Ω r) :
    restrictForm (A - B) hV = restrictForm A hV - restrictForm B hV := by
  ext v φ
  rfl

private theorem restrictForm_trans {Ω V U : Opens (ComplexModel n)} {r : ℕ}
    (hVU : V ≤ U) (hUΩ : U ≤ Ω) (A : DistributionForm Ω r) :
    restrictForm (restrictForm A hUΩ) hVU = restrictForm A (hVU.trans hUΩ) := by
  ext v φ
  change restrictDistribution (restrictDistribution (A v) hUΩ) hVU φ =
    restrictDistribution (A v) (hVU.trans hUΩ) φ
  rw [restrictDistribution_trans]

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
variable (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
  (hn : 0 < n)

/-- From original compact signed closed type(1,1) T, choose ONE actual partition,
actual global K=T-ddCS, and internally smooth full density at EVERY chart point. -/
theorem exists_global_remainder_with_smooth_local_densities [CompactSpace M]
    (T : GlobalCurrent n M (degreeTwo hn)) (hclosed : T.IsClosed b)
    (h11 : T.IsTypeOneOne b hn) :
    ∃ (m : ℕ) (g : Fin m → ComplexChart n M) (P : Fin m → Opens (ComplexModel n))
      (hP : ∀ j, P j ≤ chartTarget (g j)) (R : ∀ j, 𝓓'(chartTarget (g j), ℝ))
      (χ : Fin m → M → ℝ) (hχ : ∀ j, ChartSmooth (n := n) (χ j))
      (hc : ∀ j, IsCompact (tsupport (χ j)))
      (hs : ∀ j, tsupport (χ j) ⊆ (g j).val.source)
      (K : GlobalCurrent n M (degreeTwo hn)),
      K = T - finiteGlobalDdc b hn g χ hχ hc hs R ∧
      (∀ j y, 0 ≤ χ j y) ∧
      (∀ j, tsupport (χ j) ⊆ {y | y ∈ (g j).val.source ∧ (g j).val y ∈ P j}) ∧
      (∀ y, ∑ j, χ j y = 1) ∧
      (∀ j, ddC (restrictDistribution (R j) (hP j)) =
        restrictForm (T.coefficients b (g j)) (hP j)) ∧
      K.IsClosed b ∧ K.IsTypeOneOne b hn ∧
      ∀ (e : ComplexChart n M) (x : ComplexModel n), x ∈ e.val.target →
        ∃ (V : Opens (ComplexModel n)) (hVe : V ≤ chartTarget e)
          (β : ComplexModel n → (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ),
          x ∈ V ∧ ContDiffOn ℝ ∞ β V ∧
          ∃ hβ : LocallyIntegrableOn β V b.addHaar,
            restrictForm (K.coefficients b e) hVe = regularFormDistribution b.addHaar β hβ := by
  obtain ⟨m, g, P, hP, R, χ, hχ, hnon, hsP, hc, hsum, hR⟩ :=
    exists_local_potential_partition b hn T hclosed h11
  have hs : ∀ j, tsupport (χ j) ⊆ (g j).val.source := fun j y hy => (hsP j hy).1
  let D := finiteGlobalDdc b hn g χ hχ hc hs R
  let K := T - D
  have hDclosed : D.IsClosed b := finiteGlobalDdc_isClosed b hn g χ hχ hc hs R
  have hD11 : D.IsTypeOneOne b hn := finiteGlobalDdc_isTypeOneOne b hn g χ hχ hc hs R
  have hTD : T - D = T + (-1 : ℝ) • D := by
    apply GlobalCurrent.ext
    intro e η
    change T.inChart e η - D.inChart e η = T.inChart e η + (-1 : ℝ) * D.inChart e η
    ring
  have hKclosed : K.IsClosed b := by
    change (T - D).IsClosed b
    rw [hTD]
    exact hclosed.add b (hDclosed.smul b (-1))
  have hK11 : K.IsTypeOneOne b hn := by
    change (T - D).IsTypeOneOne b hn
    rw [hTD]
    exact h11.add b (hD11.smul b (-1))
  refine ⟨m, g, P, hP, R, χ, hχ, hc, hs, K, rfl, hnon, hsP, hsum, hR,
    hKclosed, hK11, ?_⟩
  intro e x hx
  obtain ⟨Ω, hΩ, R₀, hxΩ, hR₀⟩ :=
    exists_ambient_scalar_potential (T.coefficients b e) (hclosed e) (h11 e) x hx
  obtain ⟨V, hVe, k, hxV, hVΩ, hk, hL, hreg⟩ :=
    exists_smooth_remainder b hn b.addHaar T g P hP R χ hχ hc hs hsP hsum hR
      e hΩ R₀ hR₀ x hxΩ
  have hks : ContDiffOn ℝ ∞ (smoothDDC k) V :=
    LogWeightFactorization.smoothDDC_contDiffOn V.isOpen hk
  have hβ : LocallyIntegrableOn (smoothDDC k) V b.addHaar :=
    hks.continuousOn.locallyIntegrableOn V.isOpen.measurableSet
  have hRV : ddC (restrictDistribution R₀ hVe) = restrictForm (T.coefficients b e) hVe := by
    calc
      ddC (restrictDistribution R₀ hVe) =
          ddC (restrictDistribution (restrictDistribution R₀ hΩ) hVΩ) :=
        congrArg ddC (restrictDistribution_trans R₀ hVΩ hΩ).symm
      _ = restrictForm (ddC (restrictDistribution R₀ hΩ)) hVΩ :=
        (restrictForm_ddC _ hVΩ).symm
      _ = restrictForm (restrictForm (T.coefficients b e) hΩ) hVΩ :=
        congrArg (fun A => restrictForm A hVΩ) hR₀
      _ = restrictForm (T.coefficients b e) hVe := restrictForm_trans hVΩ hΩ _
  have hcoeff : K.coefficients b e =
      T.coefficients b e - ddC (finiteScalarFamily g χ hχ hc hs R e) := by
    change (T - D).coefficients b e = _
    have hsub : (T - D).coefficients b e = T.coefficients b e - D.coefficients b e := by
      ext v φ
      rfl
    rw [hsub]
    rw [show D.coefficients b e = ddC (finiteScalarFamily g χ hχ hc hs R e) from
      finiteGlobalDdc_coefficients b hn g χ hχ hc hs R e]
  refine ⟨V, hVe, smoothDDC k, hxV, hks, hβ, ?_⟩
  calc
    restrictForm (K.coefficients b e) hVe =
        restrictForm (T.coefficients b e) hVe -
          ddC (restrictDistribution (finiteScalarFamily g χ hχ hc hs R e) hVe) := by
      rw [hcoeff, restrictForm_sub, restrictForm_ddC]
    _ = ddC (restrictDistribution R₀ hVe) -
        ddC (restrictDistribution (finiteScalarFamily g χ hχ hc hs R e) hVe) := by
      rw [hRV]
    _ = ddC (restrictDistribution (R₀ - finiteScalarFamily g χ hχ hc hs R e) hVe) := by
      rw [restrict_sub, ddC_sub]
    _ = ddC (regularDistribution b.addHaar k hL) := congrArg ddC hreg
    _ = regularFormDistribution b.addHaar (smoothDDC k) hβ :=
      ddC_regular_eq_regularForm b.addHaar hk

end SGPT.Foundations.Analysis.Pending.FiniteGlobalCurrentSmoothLocalDensity
