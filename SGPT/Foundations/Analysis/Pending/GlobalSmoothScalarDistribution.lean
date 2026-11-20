import SGPT.Foundations.Analysis.Pending.DistributionSmoothDdcRegularity
import SGPT.Foundations.Analysis.Pending.FiniteScalarDistributionGluing

set_option autoImplicit false

/-! Genuine global smooth scalar representative from its original full LF
readings and smooth native curvature. ENTIRE BP precedes the first source.
All dimensions, empty and disconnected manifolds; no input regularity/class.
-/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Distributions ContDiff Topology Manifold

namespace SGPT.Foundations.Analysis.Pending.GlobalSmoothScalarDistribution
open FirstPass FirstPass.HolomorphicMaps _root_.SGPT.Foundations.Analysis.LocalCurrents
  LelongPoincareDivisor ThetaPshChartLimitGluing FiniteScalarDistributionGluing
  DistributionSmoothDdcRegularity LocalSmoothFormDensityGluing
  FiniteGlobalCurrentSmoothLocalDensity

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

private theorem restrict_self {Ω : Opens (ComplexModel n)} (R : 𝓓'(Ω, ℝ)) :
    restrictDistribution R (le_rfl : Ω ≤ Ω) = R := by
  ext φ
  rw [restrictDistribution_apply]
  congr 1
  ext x
  rw [congrFun (testFunction_inclusion_coe (le_rfl : Ω ≤ Ω) φ) x]

private theorem restrictForm_self {Ω : Opens (ComplexModel n)} {r : ℕ}
    (A : DistributionForm Ω r) : restrictForm A (le_rfl : Ω ≤ Ω) = A := by
  ext v φ
  rw [restrictForm_apply]
  congr 1
  ext x
  rw [congrFun (testFunction_inclusion_coe (le_rfl : Ω ≤ Ω) φ) x]

private theorem scalar_eqOn_of_regular_eq
    (μ : Measure (ComplexModel n)) [μ.IsAddHaarMeasure]
    {Ω : Opens (ComplexModel n)} {a c : ComplexModel n → ℝ}
    (ha : ContinuousOn a Ω) (hc : ContinuousOn c Ω)
    (hLa : LocallyIntegrableOn a Ω μ) (hLc : LocallyIntegrableOn c Ω μ)
    (heq : regularDistribution μ a hLa = regularDistribution μ c hLc) :
    EqOn a c Ω :=
  MeasureTheory.Measure.eqOn_open_of_ae_eq
    (ae_eq_of_regularDistribution_eq μ hLa hLc heq) Ω.isOpen ha hc

private theorem regular_congr (μ : Measure (ComplexModel n))
    {Ω : Opens (ComplexModel n)} {a c : ComplexModel n → ℝ}
    (ha : LocallyIntegrableOn a Ω μ) (hc : LocallyIntegrableOn c Ω μ)
    (heq : EqOn a c Ω) : regularDistribution μ a ha = regularDistribution μ c hc := by
  apply regularDistribution_congr_ae_on ha hc
  filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with z hz
  exact heq hz

private theorem exists_smooth_scalar_density
    (μ : Measure (ComplexModel n)) [μ.IsAddHaarMeasure]
    {Ω : Opens (ComplexModel n)} (R : 𝓓'(Ω, ℝ))
    (hloc : ∀ x ∈ Ω, ∃ (V : Opens (ComplexModel n)) (hV : V ≤ Ω)
      (a : ComplexModel n → ℝ), x ∈ V ∧ ContDiffOn ℝ ∞ a V ∧
        ∃ hL : LocallyIntegrableOn a V μ,
          restrictDistribution R hV = regularDistribution μ a hL) :
    ∃ a : ComplexModel n → ℝ, ContDiffOn ℝ ∞ a Ω ∧
      ∃ hL : LocallyIntegrableOn a Ω μ, R = regularDistribution μ a hL := by
  classical
  have hp : ∀ i : Ω, ∃ (V : Opens (ComplexModel n)) (hV : V ≤ Ω)
      (a : ComplexModel n → ℝ), (i : ComplexModel n) ∈ V ∧ ContDiffOn ℝ ∞ a V ∧
        ∃ hL : LocallyIntegrableOn a V μ,
          restrictDistribution R hV = regularDistribution μ a hL := fun i => hloc i i.property
  choose V hV α hxV hα hLα hreg using hp
  let a : ComplexModel n → ℝ := fun z => if hz : z ∈ Ω then α ⟨z,hz⟩ z else 0
  have hagree (i : Ω) : EqOn a (α i) (V i) := by
    intro z hz
    have hzΩ := hV i hz
    let j : Ω := ⟨z,hzΩ⟩
    let U := V i ⊓ V j
    have hui : U ≤ V i := inf_le_left
    have huj : U ≤ V j := inf_le_right
    have heq : regularDistribution μ (α i) ((hLα i).mono_set hui) =
        regularDistribution μ (α j) ((hLα j).mono_set huj) := by
      rw [← restrictDistribution_regularDistribution μ (hLα i) hui,
        ← restrictDistribution_regularDistribution μ (hLα j) huj,
        ← hreg i, ← hreg j, restrictDistribution_trans, restrictDistribution_trans]
    have he := scalar_eqOn_of_regular_eq μ ((hα i).continuousOn.mono hui)
      ((hα j).continuousOn.mono huj) _ _ heq
    have ha : a z = α j z := by simp only [a,hzΩ,↓reduceDIte]; rfl
    exact ha.trans (he ⟨hz,hxV j⟩).symm
  have hsmooth : ContDiffOn ℝ ∞ a Ω := by
    apply contDiffOn_of_locally_contDiffOn
    intro x hx
    let i : Ω := ⟨x,hx⟩
    refine ⟨V i,(V i).isOpen,hxV i,?_⟩
    apply ((hα i).mono inter_subset_right).congr
    intro z hz
    exact hagree i hz.2
  have hLa : LocallyIntegrableOn a Ω μ :=
    hsmooth.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet
  refine ⟨a,hsmooth,hLa,?_⟩
  apply eq_of_restrict_eq_locally
  intro x hx
  let i : Ω := ⟨x,hx⟩
  refine ⟨V i,hV i,hxV i,?_⟩
  rw [hreg i,restrictDistribution_regularDistribution]
  exact regular_congr μ (hLα i) (hLa.mono_set (hV i)) (hagree i).symm

private theorem apply_pullTest
    (R : (e : ComplexChart n M) → 𝓓'(chartTarget e, ℝ))
    (hR : ScalarFamilyCompatible R) (e f : ComplexChart n M)
    (ψ : 𝓓(chartTarget f, ℝ))
    (hψ : tsupport ψ ⊆ (chartTransition e f).target) :
    R f ψ = R e (pullTest e f ψ hψ (image_tsupport_subset_chartTarget e f hψ)) := by
  let θ : 𝓓(overlapTarget e f, ℝ) := ⟨ψ,ψ.contDiff,ψ.hasCompactSupport,hψ⟩
  let η : 𝓓(overlapSource e f, ℝ) :=
    pullTest e f ψ hψ (image_tsupport_subset_source e f hψ)
  have hrel : ∀ z ∈ (chartTransition e f).source,
      η z = transitionJac e f z * θ ((chartTransition e f) z) := by
    intro z hz
    exact pullFun_of_mem e f ψ hz
  have ht : (TestFunction.monoCLM ℝ θ : 𝓓(chartTarget f, ℝ)) = ψ := by
    ext z
    rw [congrFun (testFunction_inclusion_coe (overlapTarget_le e f) θ) z]
    rfl
  have he : (TestFunction.monoCLM ℝ η : 𝓓(chartTarget e, ℝ)) =
      pullTest e f ψ hψ (image_tsupport_subset_chartTarget e f hψ) := by
    ext z
    rw [congrFun (testFunction_inclusion_coe (overlapSource_le e f) η) z]
    rfl
  have h := hR e f η θ hrel
  rw [he,ht] at h
  exact h.symm

private theorem apply_eq_integral_comp
    (μ : Measure (ComplexModel n)) [μ.IsAddHaarMeasure]
    (R : (e : ComplexChart n M) → 𝓓'(chartTarget e, ℝ))
    (hR : ScalarFamilyCompatible R) {e f : ComplexChart n M}
    {W : Opens (ComplexModel n)} (hW : W ≤ chartTarget f)
    {g : ComplexModel n → ℝ} (hg : LocallyIntegrableOn g W μ)
    (hTg : restrictDistribution (R f) hW = regularDistribution μ g hg)
    (φ : 𝓓(chartTarget e, ℝ))
    (hφ : ∀ x ∈ tsupport φ,
      x ∈ (chartTransition e f).source ∧ chartTransition e f x ∈ W) :
    R e φ = ∫ x, φ x * g (chartTransition e f x) ∂μ := by
  have hφG : tsupport φ ⊆ (chartTransition f e).target := by
    rw [chartTransition_target_eq_source]
    exact fun x hx => (hφ x hx).1
  have himW : (chartTransition f e).symm '' tsupport φ ⊆ (W : Set (ComplexModel n)) := by
    rintro _ ⟨x,hx,rfl⟩
    rw [chartTransition_symm_eq]
    exact (hφ x hx).2
  have hcompat := apply_pullTest R hR f e φ hφG
  have hmono : (pullTest f e φ hφG (image_tsupport_subset_chartTarget f e hφG) :
      𝓓(chartTarget f, ℝ)) = TestFunction.monoCLM ℝ (pullTest f e φ hφG himW) := by
    ext y
    rw [congrFun (testFunction_inclusion_coe hW (pullTest f e φ hφG himW)) y]
    simp only [pullTest_apply]
  rw [hcompat,hmono,← restrictDistribution_apply (R f) hW,hTg,regularDistribution_apply,
    integral_mul_eq_integral_pullFun μ f e hφG (fun x => g (chartTransition e f x))]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [pullTest_apply]
  by_cases hy : y ∈ (chartTransition f e).source
  · congr 2
    rw [chartTransition_apply_eq e f,symm_chartTransition_apply hy,f.val.right_inv hy.1]
  · simp [pullFun_of_notMem f e _ hy]

private theorem smooth_densities_eq_transition
    (μ : Measure (ComplexModel n)) [μ.IsAddHaarMeasure]
    (R : (e : ComplexChart n M) → 𝓓'(chartTarget e, ℝ))
    (hR : ScalarFamilyCompatible R)
    (a : ComplexChart n M → ComplexModel n → ℝ)
    (ha : ∀ e, ContDiffOn ℝ ∞ (a e) (chartTarget e))
    (hL : ∀ e, LocallyIntegrableOn (a e) (chartTarget e) μ)
    (hread : ∀ e, R e = regularDistribution μ (a e) (hL e))
    (e f : ComplexChart n M) {z : ComplexModel n}
    (hz : z ∈ (chartTransition e f).source) :
    a e z = a f ((chartTransition e f) z) := by
  let F := chartTransition e f
  let U := overlapSource e f
  have hcomp : ContDiffOn ℝ ∞ (fun y => a f (F y)) U := by
    intro y hy
    have hFy : F y ∈ chartTarget f := (F.map_source hy).1
    exact ((ha f _ hFy).contDiffAt ((chartTarget f).isOpen.mem_nhds hFy)
      |>.comp y (chartTransition_contDiffAt_real e f hy)).contDiffWithinAt
  have hLc : LocallyIntegrableOn (fun y => a f (F y)) U μ :=
    hcomp.continuousOn.locallyIntegrableOn U.isOpen.measurableSet
  have heq : regularDistribution μ (a e) ((hL e).mono_set (overlapSource_le e f)) =
      regularDistribution μ (fun y => a f (F y)) hLc := by
    rw [← restrictDistribution_regularDistribution μ (hL e) (overlapSource_le e f),
      ← hread e]
    ext φ
    rw [restrictDistribution_apply,regularDistribution_apply]
    have hrf : restrictDistribution (R f) (le_rfl : chartTarget f ≤ chartTarget f) =
        regularDistribution μ (a f) (hL f) := by
      rw [restrict_self]
      exact hread f
    have hs : ∀ x ∈ tsupport (TestFunction.monoCLM ℝ φ : 𝓓(chartTarget e, ℝ)),
        x ∈ F.source ∧ F x ∈ chartTarget f := by
      intro x hx
      have hfun := testFunction_inclusion_coe (overlapSource_le e f) φ
      have hu : x ∈ U := by
        rw [hfun] at hx
        exact φ.tsupport_subset hx
      exact ⟨hu,(F.map_source hu).1⟩
    rw [apply_eq_integral_comp μ R hR le_rfl (hL f) hrf _ hs]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [congrFun (testFunction_inclusion_coe (overlapSource_le e f) φ) x]
  exact scalar_eqOn_of_regular_eq μ ((ha e).continuousOn.mono (overlapSource_le e f))
    hcomp.continuousOn _ hLc heq hz

/-- The original compatible global scalar family with smooth native curvature
internally supplies ONE globally smooth scalar, all full tests and pointwise ddC. -/
theorem exists_global_smooth_of_smooth_ddC
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
    (σ : ClosedRealOneOneForm n M)
    (R : (e : ComplexChart n M) → 𝓓'(chartTarget e, ℝ))
    (hR : ScalarFamilyCompatible R)
    (hdd : ∀ e, ddC (R e) = smoothFormDistribution b σ.val e) :
    ∃ h : M → ℝ, ChartSmooth (n := n) h ∧
      (∀ e : ComplexChart n M,
        ∃ hL : LocallyIntegrableOn (fun z => h (e.val.symm z)) (chartTarget e) b.addHaar,
          R e = regularDistribution b.addHaar (fun z => h (e.val.symm z)) hL) ∧
      ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
        smoothDDC (fun y => h (e.val.symm y)) z = σ.val.coeff e z := by
  classical
  have hp : ∀ e : ComplexChart n M, ∃ a : ComplexModel n → ℝ,
      ContDiffOn ℝ ∞ a (chartTarget e) ∧
      ∃ hL : LocallyIntegrableOn a (chartTarget e) b.addHaar,
        R e = regularDistribution b.addHaar a hL := by
    intro e
    apply exists_smooth_scalar_density b.addHaar (R e)
    intro x hx
    have hc : ddC (R e) = restrictForm (smoothFormDistribution b σ.val e)
        (le_rfl : chartTarget e ≤ chartTarget e) := by
      rw [restrictForm_self]
      exact hdd e
    obtain ⟨V,hV,k,hxV,hsm,hL,hreg,_hcoeff⟩ :=
      exists_local_smooth_representative_of_smooth_ddC b σ e le_rfl (R e) hc x hx
    exact ⟨V,hV,k,hxV,hsm,hL,hreg⟩
  choose a ha hL hread using hp
  let h : M → ℝ := fun x => a (complexChartAt (n := n) x) ((complexChartAt x).val x)
  have hchart (e : ComplexChart n M) :
      EqOn (fun z => h (e.val.symm z)) (a e) (chartTarget e) := by
    intro z hz
    let f := complexChartAt (n := n) (e.val.symm z)
    have hzF : z ∈ (chartTransition e f).source := ⟨hz,mem_complexChartAt_source _⟩
    exact (smooth_densities_eq_transition b.addHaar R hR a ha hL hread e f hzF).symm
  have hsm : ChartSmooth (n := n) h := fun e => (ha e).congr (hchart e)
  have hHL (e : ComplexChart n M) :
      LocallyIntegrableOn (fun z => h (e.val.symm z)) (chartTarget e) b.addHaar :=
    (hsm e).continuousOn.locallyIntegrableOn (chartTarget e).isOpen.measurableSet
  have hreg (e : ComplexChart n M) :
      R e = regularDistribution b.addHaar (fun z => h (e.val.symm z)) (hHL e) :=
    (hread e).trans (regular_congr b.addHaar (hL e) (hHL e) (hchart e).symm)
  refine ⟨h,hsm,fun e => ⟨hHL e,hreg e⟩,?_⟩
  intro e z hz
  have hcurv := hdd e
  rw [hreg e,ddC_regular_eq_regularForm b.addHaar (hsm e)] at hcurv
  exact eqOn_of_regularForm_eq b.addHaar
    (LogWeightFactorization.smoothDDC_contDiffOn (chartTarget e).isOpen (hsm e)).continuousOn
    (σ.val.smooth e).continuousOn _ (smoothForm_coeff_locallyIntegrable b σ.val e) hcurv hz

end SGPT.Foundations.Analysis.Pending.GlobalSmoothScalarDistribution
