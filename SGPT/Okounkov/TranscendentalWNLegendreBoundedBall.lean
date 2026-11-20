import SGPT.Okounkov.TranscendentalWNLegendreBoundedTest

/-!
# The locally bounded case on a ball: identification of the measures (package WN-LEG)

Blueprint `claude-tok-wn-leg`, node `tok-wn-leg:bounded-case` (conclusion on a ball).  From the
test-function identity (`lintegral_test_eq`) and cutoffs `φ_j ↑ 1_V` (`exists_cutoff_seq`) the
identity `MA(u)(V × ℂ*) = (N + 1) ∫_a^b MA(û_λ)(V) dλ` follows for open `V ⊆ W = ball z₀ (r/8)`
by monotone convergence on both sides, together with the Borel measurability of
`λ ↦ MA(û_λ)(V)` (`open_identity`).  The measure-valued map
`λ ↦ 1_{(a,b)}(λ) MA(û_λ)|_W` is then measurable (`Measurable.measure_of_isPiSystem`), the
finite measures `E ↦ MA(u)((E ∩ W) × ℂ*)` and `E ↦ (N + 1) ∫_a^b MA(û_λ)(E ∩ W) dλ` agree on open
sets, hence on all Borel sets (`ball_identity`).  `local_identity` restates it with the measures
on the ball itself and `∫` over `[a, b]`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.FiniteGeodesicMaximality
  SGPT.Foundations.Analysis.Pending.PshRadialRegularization

variable {N : ℕ} {u : ComplexModel N → ℂ → EReal} {a b C : ℝ} {z₀ : ComplexModel N} {r : ℝ}
  {ρ : ComplexModel (N + 1) → ℝ}

/-- Monotone convergence along a cutoff sequence: `∫ φ_j dm → m(V)`. -/
theorem tendsto_lintegral_cutoff {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] {V : Set X} (hV : IsOpen V) {φ : ℕ → X → ℝ}
    (hφc : ∀ j, Continuous (φ j)) (hmono : ∀ x, Monotone fun j => φ j x)
    (hlim : ∀ x, Tendsto (fun j => φ j x) atTop (𝓝 (V.indicator (fun _ => (1 : ℝ)) x)))
    (m : Measure X) :
    Tendsto (fun j => ∫⁻ x, ENNReal.ofReal (φ j x) ∂m) atTop (𝓝 (m V)) := by
  have h := lintegral_tendsto_of_tendsto_of_monotone (μ := m)
    (f := fun j x => ENNReal.ofReal (φ j x)) (F := V.indicator 1)
    (fun j => (hφc j).measurable.ennreal_ofReal.aemeasurable)
    (Eventually.of_forall fun x j l hjl => ENNReal.ofReal_le_ofReal (hmono x hjl))
    (Eventually.of_forall fun x => by
      have := (ENNReal.continuous_ofReal.tendsto _).comp (hlim x)
      by_cases hx : x ∈ V
      · simpa [indicator_of_mem hx, Function.comp_def] using this
      · simpa [indicator_of_notMem hx, Function.comp_def] using this)
  rwa [lintegral_indicator_one hV.measurableSet] at h

namespace IsBoundedLegendreData

variable (h : IsBoundedLegendreData (ball z₀ r) u a b C) (hρ : IsRadialKernel ρ) (hr : 0 < r)
include h hρ hr

/-- **The identity on open subsets of `W`**, with the measurability and the uniform bound. -/
theorem open_identity
    (hu : PlurisubharmonicOn (productModelFunction u)
      (puncturedProductOpens (approxDomain (ball z₀ r) (localScale r))))
    (hû : ∀ lam, PlurisubharmonicOn (partialLegendre u lam)
      (approxDomain (ball z₀ r) (localScale r)))
    {M : ℝ≥0∞} (hM : ∀ k : ℕ, ∀ lam ∈ Ioo a b, ∀ hf : PlurisubharmonicOn
      (partialLegendre (logRadialFunction (approxProfile ρ u a b C (localScale r) k)) lam)
      (approxDomain (ball z₀ r) (localScale r)),
      MongeAmpere.truncationLimitMeasure (approxDomain (ball z₀ r) (localScale r))
        (partialLegendre (logRadialFunction (approxProfile ρ u a b C (localScale r) k)) lam) hf
        (ball z₀ (r / 8)) ≤ M)
    {O : Set (ComplexModel N)} (hO : IsOpen O) :
    Measurable ((Ioo a b).indicator fun lam => MongeAmpere.truncationLimitMeasure
        (approxDomain (ball z₀ r) (localScale r)) (partialLegendre u lam) (hû lam)
        (O ∩ ball z₀ (r / 8))) ∧
      (∀ lam ∈ Ioo a b, MongeAmpere.truncationLimitMeasure
        (approxDomain (ball z₀ r) (localScale r)) (partialLegendre u lam) (hû lam)
        (O ∩ ball z₀ (r / 8)) ≤ M) ∧
      MongeAmpere.truncationLimitMeasure
          (puncturedProductOpens (approxDomain (ball z₀ r) (localScale r)))
          (productModelFunction u) hu
          (stripModelEquiv N ⁻¹' ((O ∩ ball z₀ (r / 8)) ×ˢ puncturedPlane)) =
        ((N + 1 : ℕ) : ℝ≥0∞) * ∫⁻ lam in Ioo a b, MongeAmpere.truncationLimitMeasure
          (approxDomain (ball z₀ r) (localScale r)) (partialLegendre u lam) (hû lam)
          (O ∩ ball z₀ (r / 8)) := by
  set D := approxDomain (ball z₀ r) (localScale r)
  set W := ball z₀ (r / 8)
  set V := O ∩ W
  have hV : IsOpen V := hO.inter isOpen_ball
  have hVb : Bornology.IsBounded V := isBounded_ball.subset inter_subset_right
  obtain ⟨φ, hφc, hφcs, hφV, hφ01, hφmono, hφlim⟩ := exists_cutoff_seq hV hVb
  have hφW : ∀ j, tsupport (φ j) ⊆ W := fun j => (hφV j).trans inter_subset_right
  set ν := fun lam => MongeAmpere.truncationLimitMeasure D (partialLegendre u lam) (hû lam)
  set μ := MongeAmpere.truncationLimitMeasure (puncturedProductOpens D) (productModelFunction u) hu
  have hνlim : ∀ lam, Tendsto (fun j => ∫⁻ z, ENNReal.ofReal (φ j z) ∂(ν lam)) atTop
      (𝓝 (ν lam V)) := fun lam => tendsto_lintegral_cutoff hV hφc hφmono hφlim (ν lam)
  have hfl : ∀ k lam, PlurisubharmonicOn
      (partialLegendre (logRadialFunction (approxProfile ρ u a b C (localScale r) k)) lam) D :=
    fun k lam => plurisubharmonicOn_partialLegendre D.isOpen (h.localPsh hρ hr k)
      (isCircleInvariant_logRadialFunction _) lam
  -- measurability
  have hmeasj : ∀ j, Measurable ((Ioo a b).indicator fun lam =>
      ∫⁻ z, ENNReal.ofReal (φ j z) ∂(ν lam)) := fun j =>
    h.measurable_indicator_lintegral hρ hr hû (hφc j) (hφcs j) (hφW j) fun z => (hφ01 j z).1
  have hmeas : Measurable ((Ioo a b).indicator fun lam => ν lam V) := by
    refine measurable_of_tendsto_metrizable hmeasj (tendsto_pi_nhds.mpr fun lam => ?_)
    by_cases hlam : lam ∈ Ioo a b
    · simp only [indicator_of_mem hlam]
      exact hνlim lam
    · simp only [indicator_of_notMem hlam]
      exact tendsto_const_nhds
  -- the bound
  have hbound : ∀ lam ∈ Ioo a b, ν lam V ≤ M := by
    intro lam hlam
    refine le_of_tendsto' (hνlim lam) fun j => ?_
    exact le_of_tendsto' (h.tendsto_lintegral_approxTransform hρ hr hlam (hû lam)
      (fun k => hfl k lam) (hφc j) (hφcs j) ((hφW j).trans (ball_eighth_subset_approxDomain hr))
      fun z => (hφ01 j z).1) fun k =>
      (lintegral_le_measure_ball (hφW j) fun z => (hφ01 j z).2).trans (hM k lam hlam _)
  refine ⟨hmeas, hbound, ?_⟩
  -- the identity
  have hL : Tendsto (fun j => ∫⁻ q, ENNReal.ofReal (φ j (stripModelEquiv N q).1) ∂μ) atTop
      (𝓝 (μ (stripModelEquiv N ⁻¹' (V ×ˢ puncturedPlane)))) := by
    have h1 := lintegral_tendsto_of_tendsto_of_monotone (μ := μ)
      (f := fun j q => ENNReal.ofReal (φ j (stripModelEquiv N q).1))
      (F := (stripModelEquiv N ⁻¹' (V ×ˢ puncturedPlane)).indicator 1)
      (fun j => ((hφc j).measurable.comp
        (measurable_fst.comp (stripModelEquiv N).continuous.measurable)).ennreal_ofReal.aemeasurable)
      (Eventually.of_forall fun q j l hjl => ENNReal.ofReal_le_ofReal (hφmono _ hjl))
      ((ae_mem_of_truncationLimitMeasure hu).mono fun q hq => by
        have := (ENNReal.continuous_ofReal.tendsto _).comp (hφlim (stripModelEquiv N q).1)
        by_cases hx : (stripModelEquiv N q).1 ∈ V
        · have hq' : q ∈ stripModelEquiv N ⁻¹' (V ×ˢ puncturedPlane) := ⟨hx, hq.2⟩
          simpa [indicator_of_mem hx, indicator_of_mem hq', Function.comp_def] using this
        · have hq' : q ∉ stripModelEquiv N ⁻¹' (V ×ˢ puncturedPlane) := fun h' => hx h'.1
          simpa [indicator_of_notMem hx, indicator_of_notMem hq', Function.comp_def] using this)
    rwa [lintegral_indicator_one ((hV.prod isOpen_puncturedPlane).preimage
      (stripModelEquiv N).continuous).measurableSet] at h1
  have hR : Tendsto (fun j => ((N + 1 : ℕ) : ℝ≥0∞) * ∫⁻ lam in Ioo a b,
      ∫⁻ z, ENNReal.ofReal (φ j z) ∂(ν lam)) atTop
      (𝓝 (((N + 1 : ℕ) : ℝ≥0∞) * ∫⁻ lam in Ioo a b, ν lam V)) := by
    refine ENNReal.Tendsto.const_mul ?_ (Or.inr (ENNReal.natCast_ne_top _))
    refine lintegral_tendsto_of_tendsto_of_monotone (fun j => ?_)
      (Eventually.of_forall fun lam j l hjl =>
        lintegral_mono fun z => ENNReal.ofReal_le_ofReal (hφmono z hjl))
      (Eventually.of_forall fun lam => hνlim lam)
    exact (hmeasj j).aemeasurable.congr ((ae_restrict_mem measurableSet_Ioo).mono fun lam hlam =>
      indicator_of_mem hlam _)
  refine tendsto_nhds_unique hL (hR.congr fun j => ?_)
  exact (h.lintegral_test_eq hρ hr hu hû (hφc j) (hφcs j) (hφW j) (hφ01 j)).symm

/-- **The identity on Borel subsets of `W = ball z₀ (r/8)`**, measures on `D × ℂ*` and `D`. -/
theorem ball_identity
    (hu : PlurisubharmonicOn (productModelFunction u)
      (puncturedProductOpens (approxDomain (ball z₀ r) (localScale r))))
    (hû : ∀ lam, PlurisubharmonicOn (partialLegendre u lam)
      (approxDomain (ball z₀ r) (localScale r)))
    {E : Set (ComplexModel N)} (hE : MeasurableSet E) (hEW : E ⊆ ball z₀ (r / 8)) :
    Measurable ((Ioo a b).indicator fun lam => MongeAmpere.truncationLimitMeasure
        (approxDomain (ball z₀ r) (localScale r)) (partialLegendre u lam) (hû lam) E) ∧
      MongeAmpere.truncationLimitMeasure
          (puncturedProductOpens (approxDomain (ball z₀ r) (localScale r)))
          (productModelFunction u) hu (stripModelEquiv N ⁻¹' (E ×ˢ puncturedPlane)) =
        ((N + 1 : ℕ) : ℝ≥0∞) * ∫⁻ lam in Ioo a b, MongeAmpere.truncationLimitMeasure
          (approxDomain (ball z₀ r) (localScale r)) (partialLegendre u lam) (hû lam) E := by
  classical
  set D := approxDomain (ball z₀ r) (localScale r)
  set W := ball z₀ (r / 8)
  set ν := fun lam => MongeAmpere.truncationLimitMeasure D (partialLegendre u lam) (hû lam)
  set μ := MongeAmpere.truncationLimitMeasure (puncturedProductOpens D) (productModelFunction u) hu
  obtain ⟨M, hMt, hM⟩ := h.exists_cln_bound hρ hr
  have hopen := fun (O : Set (ComplexModel N)) (hO : IsOpen O) =>
    h.open_identity hρ hr hu hû hM hO
  set κ : ℝ → Measure (ComplexModel N) := fun lam =>
    if lam ∈ Ioo a b then (ν lam).restrict W else 0
  have hκapp : ∀ lam (s : Set (ComplexModel N)), MeasurableSet s →
      κ lam s = (Ioo a b).indicator (fun lam => ν lam (s ∩ W)) lam := by
    intro lam s hs
    by_cases hlam : lam ∈ Ioo a b
    · simp only [κ, if_pos hlam, indicator_of_mem hlam, Measure.restrict_apply hs]
    · simp only [κ, if_neg hlam, indicator_of_notMem hlam, Measure.coe_zero, Pi.zero_apply]
  have hfin : ∀ lam, IsFiniteMeasure (κ lam) := by
    intro lam
    refine ⟨?_⟩
    rw [hκapp lam univ MeasurableSet.univ]
    by_cases hlam : lam ∈ Ioo a b
    · rw [indicator_of_mem hlam]
      exact ((hopen univ isOpen_univ).2.1 lam hlam).trans_lt hMt
    · rw [indicator_of_notMem hlam]
      exact ENNReal.zero_lt_top
  have hκ : Measurable κ := by
    refine Measurable.measure_of_isPiSystem (S := {s | IsOpen s}) BorelSpace.measurable_eq
      isPiSystem_isOpen (fun s hs => ?_) ?_
    · have : (fun lam => κ lam s) = (Ioo a b).indicator (fun lam => ν lam (s ∩ W)) :=
        funext fun lam => hκapp lam s (IsOpen.measurableSet hs)
      rw [this]
      exact (hopen s hs).1
    · have : (fun lam => κ lam univ) = (Ioo a b).indicator (fun lam => ν lam (univ ∩ W)) :=
        funext fun lam => hκapp lam univ MeasurableSet.univ
      rw [this]
      exact (hopen univ isOpen_univ).1
  set π : ComplexModel (N + 1) → ComplexModel N := fun q => (stripModelEquiv N q).1
  have hπ : Measurable π := measurable_fst.comp (stripModelEquiv N).continuous.measurable
  set ν₀ : Measure (ComplexModel N) :=
    (μ.restrict (stripModelEquiv N ⁻¹' (W ×ˢ puncturedPlane))).map π
  set νT : Measure (ComplexModel N) :=
    ((N + 1 : ℕ) : ℝ≥0∞) • (volume.restrict (Ioo a b)).bind κ
  have hpre : ∀ s : Set (ComplexModel N), π ⁻¹' s ∩ stripModelEquiv N ⁻¹' (W ×ˢ puncturedPlane) =
      stripModelEquiv N ⁻¹' ((s ∩ W) ×ˢ puncturedPlane) := by
    intro s
    ext q
    simp only [π, mem_inter_iff, mem_preimage, mem_prod]
    tauto
  have hν₀ : ∀ s, MeasurableSet s →
      ν₀ s = μ (stripModelEquiv N ⁻¹' ((s ∩ W) ×ˢ puncturedPlane)) := by
    intro s hs
    rw [Measure.map_apply hπ hs, Measure.restrict_apply (hπ hs), hpre]
  have hνT : ∀ s, MeasurableSet s →
      νT s = ((N + 1 : ℕ) : ℝ≥0∞) * ∫⁻ lam in Ioo a b, ν lam (s ∩ W) := by
    intro s hs
    rw [Measure.smul_apply, Measure.bind_apply hs hκ.aemeasurable, smul_eq_mul]
    congr 1
    refine setLIntegral_congr_fun measurableSet_Ioo fun lam hlam => ?_
    rw [hκapp lam s hs, indicator_of_mem hlam]
  have hopen' : ∀ s ∈ {s : Set (ComplexModel N) | IsOpen s}, ν₀ s = νT s := by
    intro s hs
    rw [hν₀ s (IsOpen.measurableSet hs), hνT s (IsOpen.measurableSet hs)]
    exact (hopen s hs).2.2
  have hν₀fin : IsFiniteMeasure ν₀ := by
    refine ⟨?_⟩
    rw [hopen' univ (isOpen_univ (X := ComplexModel N)),
      hνT univ MeasurableSet.univ]
    refine ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) ?_
    calc ∫⁻ lam in Ioo a b, ν lam (univ ∩ W) ≤ ∫⁻ _ in Ioo a b, M :=
          setLIntegral_mono measurable_const fun lam hlam => (hopen univ isOpen_univ).2.1 lam hlam
      _ < ⊤ := by
          rw [setLIntegral_const, Real.volume_Ioo]
          exact ENNReal.mul_lt_top hMt ENNReal.ofReal_lt_top
  have heq : ν₀ = νT := ext_of_generate_finite {s | IsOpen s} BorelSpace.measurable_eq
    isPiSystem_isOpen hopen'
    (hopen' univ (isOpen_univ (X := ComplexModel N)))
  have hEW' : E ∩ W = E := inter_eq_left.mpr hEW
  refine ⟨?_, ?_⟩
  · have : (Ioo a b).indicator (fun lam => ν lam E) = fun lam => κ lam E := by
      funext lam
      rw [hκapp lam E hE, hEW']
    rw [this]
    exact (Measure.measurable_coe hE).comp hκ
  · have h1 := hν₀ E hE
    rw [heq, hνT E hE, hEW'] at h1
    exact h1.symm

end IsBoundedLegendreData

end SGPT.Okounkov.TranscendentalWN
