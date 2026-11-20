import SGPT.Foundations.Analysis.Pending.XiaoPoissonChartCompatibility

set_option autoImplicit false

/-! # Genuine density transport and PSH representative uniqueness from actual compatibility -/

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology ContDiff NNReal Distributions

namespace SGPT.Foundations.Analysis.Pending.XiaoCompatibleLocalRepresentatives

open FirstPass FirstPass.HolomorphicMaps FirstPass.PositiveClasses ThetaPshChartLimitGluing
  XiaoPoissonChartCompatibility

noncomputable section

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- Actual coordinate compatibility transports an actual locally integrable regular density. -/
theorem apply_eq_integral_comp (μ : Measure (ComplexModel (m + 1))) [μ.IsAddHaarMeasure]
    {U : ∀ e : ComplexChart (m + 1) M, 𝓓'(chartTarget e, ℝ)}
    (hU : IsCoordinateCompatible U) {e f : ComplexChart (m + 1) M}
    {W : Opens (ComplexModel (m + 1))} (hW : W ≤ chartTarget f)
    {g : ComplexModel (m + 1) → ℝ} (hg : LocallyIntegrableOn g W μ)
    (hTg : restrictDistribution (U f) hW = regularDistribution μ g hg)
    (φ : 𝓓(chartTarget e, ℝ))
    (hφ : ∀ x ∈ tsupport φ, x ∈ (chartTransition e f).source ∧ chartTransition e f x ∈ W) :
    U e φ = ∫ x, φ x * g (chartTransition e f x) ∂μ := by
  have hφG : tsupport φ ⊆ (chartTransition f e).target := by
    rw [chartTransition_target_eq_source]
    exact fun x hx => (hφ x hx).1
  have himW : (chartTransition f e).symm '' tsupport φ ⊆ (W : Set (ComplexModel (m + 1))) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [chartTransition_symm_eq]
    exact (hφ x hx).2
  have hcompat := hU f e φ hφG
  have hmono : (pullTest f e φ hφG (image_tsupport_subset_chartTarget f e hφG) :
      𝓓(chartTarget f, ℝ)) = TestFunction.monoCLM ℝ (pullTest f e φ hφG himW) := by
    apply TestFunction.ext
    intro y
    rw [congrFun (testFunction_inclusion_coe hW (pullTest f e φ hφG himW)) y]
    simp only [pullTest_apply]
  rw [hcompat, hmono, ← restrictDistribution_apply (U f) hW, hTg, regularDistribution_apply,
    integral_mul_eq_integral_pullFun μ f e hφG (fun x => g (chartTransition e f x))]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [pullTest_apply]
  by_cases hy : y ∈ (chartTransition f e).source
  · congr 2
    rw [chartTransition_apply_eq e f, symm_chartTransition_apply hy, f.val.right_inv hy.1]
  · simp [pullFun_of_notMem f e _ hy]


/-- Actual compatibility and actual PSH uniqueness identify local representatives across charts. -/
theorem localRep_eq_transport (μ : Measure (ComplexModel (m + 1))) [μ.IsAddHaarMeasure]
    {U : ∀ e : ComplexChart (m + 1) M, 𝓓'(chartTarget e, ℝ)}
    (hU : IsCoordinateCompatible U) {θ : SmoothRealForm (m + 1) M 2}
    {e d : ComplexChart (m + 1) M}
    (R : LocalRep μ θ e (U e)) (S : LocalRep μ θ d (U d)) {y : ComplexModel (m + 1)}
    (hyR : y ∈ R.W) (hyF : y ∈ (chartTransition e d).source)
    (hFy : chartTransition e d y ∈ S.W) :
    R.u y = S.u (chartTransition e d y) + ((-S.ρ (chartTransition e d y) : ℝ) : EReal) +
      (R.ρ y : EReal) := by
  set F := chartTransition e d with hFdef
  -- a ball around `y` where everything is defined
  have hO : IsOpen ((R.W : Set (ComplexModel (m + 1))) ∩ (F.source ∩ F ⁻¹' S.W)) :=
    R.W.isOpen.inter (F.continuousOn.isOpen_inter_preimage F.open_source S.W.isOpen)
  obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.mp hO y ⟨hyR, hyF, hFy⟩
  let B : Opens (ComplexModel (m + 1)) := ⟨ball y r, isOpen_ball⟩
  have hBR : B ≤ R.W := fun z hz => (hrO hz).1
  have hBF : ∀ z ∈ (B : Set (ComplexModel (m + 1))), z ∈ F.source ∧ F z ∈ S.W := fun z hz =>
    (hrO hz).2
  have hBe : B ≤ chartTarget e := hBR.trans R.hW
  have hBpre : IsPreconnected (B : Set (ComplexModel (m + 1))) := (convex_ball y r).isPreconnected
  have hyB : y ∈ B := mem_ball_self hr
  -- the transported function
  set g₂ : ComplexModel (m + 1) → EReal := fun z => S.u (F z) + ((-S.ρ (F z) : ℝ) : EReal) +
    (R.ρ z : EReal) with hg₂def
  have hpotB : IsSmoothLocalPotential θ e B R.ρ := R.pot.mono isOpen_ball hBR
  have hg₂ : PlurisubharmonicOn g₂ B :=
    plurisubharmonicOn_transport e d S.pot S.rep.1 isOpen_ball hBF hpotB
  have hF : DifferentiableOn ℂ F B := fun z hz =>
    ((chartTransition_contDiffAt e d (hBF z hz).1).differentiableAt
      (by simp)).differentiableWithinAt
  have hSuF : PlurisubharmonicOn (fun z => S.u (F z)) B :=
    HolomorphicPullback.plurisubharmonicOn_comp_holomorphic isOpen_ball hF
      (fun z hz => (hBF z hz).2) S.rep.1
  -- `S.u ∘ F` is not identically `-∞` on `B`
  have hne : ∃ z ∈ (B : Set (ComplexModel (m + 1))), S.u (F z) ≠ ⊥ := by
    have hsub : F '' B ⊆ S.W := by rintro _ ⟨z, hz, rfl⟩; exact (hBF z hz).2
    have hopen : IsOpen (F '' B) :=
      F.isOpen_image_of_subset_source isOpen_ball fun z hz => (hBF z hz).1
    have hpos : μ.restrict S.W (F '' B) ≠ 0 := by
      rw [Measure.restrict_apply' S.W.isOpen.measurableSet, inter_eq_left.mpr hsub]
      exact (hopen.measure_pos μ ⟨F y, y, hyB, rfl⟩).ne'
    obtain ⟨_, ⟨z, hz, rfl⟩, hfin⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos
      (ae_restrict_of_ae S.rep.2.1)
    exact ⟨z, hz, hfin.2⟩
  obtain ⟨z₀, hz₀, hz₀ne⟩ := hne
  have hSuF_fin := hSuF.ae_finite μ hBpre ⟨z₀, hz₀, hz₀ne⟩
  have hSuF_loc := hSuF.locallyIntegrableOn_toReal μ hBpre ⟨z₀, hz₀, hz₀ne⟩
  have hg₂ne : ∃ a ∈ (B : Set (ComplexModel (m + 1))), g₂ a ≠ ⊥ := by
    refine ⟨z₀, hz₀, ?_⟩
    simp only [hg₂def]
    exact EReal.add_ne_bot_iff.mpr ⟨EReal.add_ne_bot_iff.mpr ⟨hz₀ne, EReal.coe_ne_bot _⟩,
      EReal.coe_ne_bot _⟩
  have hg₂fin := hg₂.ae_finite μ hBpre hg₂ne
  have hg₂loc := hg₂.locallyIntegrableOn_toReal μ hBpre hg₂ne
  -- the density `k = (S.u - S.ρ) ∘ F` of `T_e` on `B`
  have hρScont : ContinuousOn (fun z => S.ρ (F z)) B :=
    S.pot.2.2.1.continuousOn.comp (F.continuousOn.mono fun z hz => (hBF z hz).1)
      fun z hz => (hBF z hz).2
  have hk : LocallyIntegrableOn (fun z => (S.u (F z)).toReal - S.ρ (F z)) B μ :=
    hSuF_loc.sub (hρScont.locallyIntegrableOn isOpen_ball.measurableSet)
  have hρR : LocallyIntegrableOn R.ρ B μ := R.hρi.mono_set hBR
  have hTe : restrictDistribution (U e) hBe =
      regularDistribution μ (fun z => (S.u (F z)).toReal - S.ρ (F z)) hk := by
    ext φ
    rw [restrictDistribution_apply, regularDistribution_apply]
    refine (apply_eq_integral_comp μ hU S.hW (S.rep.2.2.1.sub S.hρi)
      S.restrict_eq _ fun x hx => ?_).trans ?_
    · have hxB : x ∈ (B : Set (ComplexModel (m + 1))) := by
        have := (TestFunction.monoCLM ℝ φ : 𝓓(chartTarget e, ℝ)).tsupport_subset
        rw [show ((TestFunction.monoCLM ℝ φ : 𝓓(chartTarget e, ℝ)) : ComplexModel (m + 1) → ℝ) = φ
          from testFunction_inclusion_coe hBe φ] at hx
        exact φ.tsupport_subset hx
      exact hBF x hxB
    · refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [Pi.sub_apply]
      rw [congrFun (testFunction_inclusion_coe hBe φ) x]
  -- both `R.u` and `g₂` represent `T_e + R.ρ` on `B`
  have hRrep := R.rep.restrict μ hBR
  rw [restrictDistribution_add, restrictDistribution_trans,
    restrictDistribution_regularDistribution μ R.hρi hBR, hTe,
    ← regularDistribution_add hk hρR] at hRrep
  have hg₂rep : IsPshRepresentative μ (regularDistribution μ
      (fun z => (S.u (F z)).toReal - S.ρ (F z) + R.ρ z) (hk.add hρR)) g₂ := by
    refine ⟨hg₂, hg₂fin, hg₂loc, regularDistribution_congr_ae_on _ _ ?_⟩
    filter_upwards [hSuF_fin] with z hz
    simp only [hg₂def]
    rw [ereal_toReal_add_coe (ereal_add_coe_finite hz _), ereal_toReal_add_coe hz]
    ring
  exact hRrep.unique hg₂rep hyB


end

end SGPT.Foundations.Analysis.Pending.XiaoCompatibleLocalRepresentatives
