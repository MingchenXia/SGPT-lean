import SGPT.Okounkov.TranscendentalWNConvFLStatement
import SGPT.Foundations.Analysis.Pending.ActualSingularChartMassLiminf
import SGPT.Foundations.Analysis.Pending.BedfordTaylorIncreasing
import SGPT.Foundations.Analysis.Pending.BoundedGlobalTruncation
import SGPT.Foundations.Analysis.Pending.IncreasingMixedRegularizedContinuity

/-!
# Local tools for WN21 Proposition 7.4

Blueprint `claude-tok-wn-fl`, nodes `tok-wn-fl:chart-measure`, `tok-wn-fl:moving-test`,
`tok-wn-fl:subsequence`; source WN21 §7, proof of Proposition 7.4.

* `lintegral_diagonalPotentialMeasure_eq_canonical` (**the non-pluripolar measure of a locally
  bounded potential in a chart**): if on a chart domain `A` the corrected potential
  `u ∘ e⁻¹ + ρ` (`ρ` a smooth local potential of `θ`) is a real locally bounded psh function `f`,
  then `∫ G d⟨(θ + dd^c u)ⁿ⟩ = ∫ G ∘ e⁻¹ d(dd^c f)ⁿ` for every `G` vanishing off `e⁻¹(A)` (the
  global measure restricted to a potential patch is the truncation limit, which for a bounded
  tuple is the Bedford--Taylor measure: TN `MixedNonPluripolar.mixedTruncationLimitMeasure_eq_canonical_of_eqOn`);
* `tendsto_integral_canonicalBedfordTaylorMeasure_of_monotone` (**Bedford--Taylor convergence
  against moving test functions**): for an increasing sequence `h_l` of locally bounded psh
  functions converging a.e. to a locally bounded psh `H`, and test functions `χ_l → χ` uniformly,
  all vanishing off a fixed compact `K ⊆ Ω`, `∫ χ_l (dd^c h_l)ⁿ → ∫ χ (dd^c H)ⁿ` (TN
  `IncreasingTruncationLimit.boundedIncreasingConvergence` and the boundedness of the masses of `K`);
* `limsup_le_of_forall_subseq` (a `limsup` bound from further subsequences).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.MixedMongeAmpere
open SGPT.Foundations.Analysis.FirstPass.GlobalPotentialPatches
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.GlobalNonPluripolar
open SGPT.Foundations.Analysis.Pending.MixedNonPluripolar
open SGPT.Foundations.Analysis.FirstPass.LocalPotentialPullback

/-! ### The measure in a chart -/

section Chart

variable {k : ℕ} {V : Type*} [TopologicalSpace V] [ChartedSpace (ComplexModel k) V]
  [IsComplexManifold k V] [CompactSpace V] [MeasurableSpace V] [BorelSpace V]

/-- **The non-pluripolar measure of a locally bounded potential in a chart.** -/
theorem lintegral_diagonalPotentialMeasure_eq_canonical (θ : ClosedRealOneOneForm k V)
    {u : V → EReal} (hu : IsThetaPshPotential θ.val u) (e : ComplexChart k V)
    (A : Opens (ComplexModel k)) {ρ : ComplexModel k → ℝ}
    (hρ : IsSmoothLocalPotential θ.val e A ρ) {f : ComplexModel k → ℝ}
    (hf : IsLocallyBoundedPshOn A f)
    (hfeq : ∀ y ∈ A, chartFunction u e y + (ρ y : EReal) = (f y : EReal))
    (G : V → ℝ≥0∞) (hG : ∀ x, G x ≠ 0 → x ∈ e.val.source ∧ e.val x ∈ A) :
    ∫⁻ x, G x ∂(diagonalPotentialMeasure θ u hu) =
      ∫⁻ y, G (e.val.symm y) ∂(MongeAmpere.canonicalBedfordTaylorMeasure A f hf) := by
  have hpsh : PlurisubharmonicOn (fun z => chartFunction u e z + (ρ z : EReal)) A := by
    exact fun x hx => (hf.1 x hx).congr (Filter.eventuallyEq_of_mem (A.isOpen.mem_nhds hx)
      fun z hz => (hfeq z hz).symm)
  let P : Patch (fun _ : Fin k => θ) (fun _ => u) :=
    { chart := e
      domain := A
      domain_le_target := hρ.2.1
      potential := fun _ => ρ
      localPotential := fun _ => hρ
      plurisubharmonic := fun _ => hpsh }
  have hsupp : Function.support G ⊆ (P.source : Set V) := fun x hx => hG x hx
  have h1 : ∫⁻ x, G x ∂(diagonalPotentialMeasure θ u hu) =
      ∫⁻ x, G x ∂(patchMeasure P) := by
    rw [← globalMixedMeasure_restrict_patch (fun _ => hu.1) P]
    exact (setLIntegral_eq_of_support_subset hsupp).symm
  rw [h1, patchMeasure]
  refine (ActualSingularChartMassLiminf.lintegral_pushMeasure P
    (mixedTruncationLimitMeasure_compl P.plurisubharmonic) G).trans ?_
  have hv : IsLocallyBoundedMixedPshOn A (fun _ : Fin k => f) := fun _ => hf
  have heq : ∀ i, EqOn (P.corrected i) (fun z => ((fun _ : Fin k => f) i z : EReal)) A :=
    fun _ z hz => hfeq z hz
  rw [mixedTruncationLimitMeasure_eq_canonical_of_eqOn hv P.plurisubharmonic heq,
    MixedMongeAmpere.canonicalMixedBedfordTaylorMeasure_diagonal A f hf]

end Chart

/-! ### Bedford--Taylor convergence against moving test functions -/

section Moving

variable {n : ℕ}

/-- A continuous function vanishing off a compact set of finite measure is integrable. -/
theorem integrable_of_continuous_of_vanishing {μ : Measure (ComplexModel n)} {f : ComplexModel n → ℝ}
    (hf : Continuous f) {L : Set (ComplexModel n)} (hL : IsCompact L) (hμL : μ L < ⊤)
    (hfL : ∀ z, z ∉ L → f z = 0) : Integrable f μ := by
  obtain ⟨M, hM⟩ := hL.exists_bound_of_continuousOn hf.continuousOn
  refine IntegrableOn.integrable_of_forall_notMem_eq_zero (s := L) ?_ hfL
  exact Measure.integrableOn_of_bounded hμL.ne hf.aestronglyMeasurable
    ((ae_restrict_iff' hL.measurableSet).mpr (Eventually.of_forall hM))

/-- **Bedford--Taylor convergence against moving test functions.** -/
theorem tendsto_integral_canonicalBedfordTaylorMeasure_of_monotone {Ω : Opens (ComplexModel n)}
    {h : ℕ → ComplexModel n → ℝ} {H : ComplexModel n → ℝ}
    (hh : ∀ l, IsLocallyBoundedPshOn Ω (h l)) (hH : IsLocallyBoundedPshOn Ω H)
    (hmono : ∀ z ∈ Ω, Monotone fun l => h l z)
    (hae : ∀ᵐ z, z ∈ Ω → Tendsto (fun l => h l z) atTop (𝓝 (H z)))
    {χ : ℕ → ComplexModel n → ℝ} {χ₀ : ComplexModel n → ℝ}
    (hχc : ∀ l, Continuous (χ l)) (hχ₀c : Continuous χ₀)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hχK : ∀ l z, z ∉ K → χ l z = 0) (hχ₀K : ∀ z, z ∉ K → χ₀ z = 0)
    (hunif : ∀ η : ℝ, 0 < η → ∀ᶠ l in atTop, ∀ z, |χ l z - χ₀ z| ≤ η) :
    Tendsto (fun l => ∫ z, χ l z ∂(MongeAmpere.canonicalBedfordTaylorMeasure Ω (h l) (hh l)))
      atTop (𝓝 (∫ z, χ₀ z ∂(MongeAmpere.canonicalBedfordTaylorMeasure Ω H hH))) := by
  set μ : ℕ → Measure (ComplexModel n) := fun l =>
    MongeAmpere.canonicalBedfordTaylorMeasure Ω (h l) (hh l) with hμ
  set μ₀ := MongeAmpere.canonicalBedfordTaylorMeasure Ω H hH with hμ₀
  have hBT := IncreasingTruncationLimit.boundedIncreasingConvergence Ω h H hh hH hmono hae
  have htsK : ∀ g : ComplexModel n → ℝ, (∀ z, z ∉ K → g z = 0) → tsupport g ⊆ K := fun g hg =>
    closure_minimal (fun z hz => by
      by_contra h'
      exact hz (hg z h')) hK.isClosed
  -- the test function `χ₀`
  have h0 := (hBT χ₀ hχ₀c (HasCompactSupport.intro hK hχ₀K) ((htsK χ₀ hχ₀K).trans hKΩ)).1
  -- a cutoff `ψ ≥ 𝟙_K`
  obtain ⟨L, hLc, hKL, hLΩ⟩ := exists_compact_between hK Ω.isOpen hKΩ
  obtain ⟨ψ, hψ1, hψ0, hψc, hψI⟩ := exists_continuous_one_zero_of_isCompact hK
    isOpen_interior.isClosed_compl (disjoint_compl_right_iff_subset.mpr hKL)
  have hψL : ∀ z, z ∉ L → ψ z = 0 := fun z hz => hψ0 (fun h' => hz (interior_subset h'))
  have hψts : tsupport ψ ⊆ Ω := by
    refine (closure_minimal (fun z hz => ?_) hLc.isClosed).trans hLΩ
    by_contra h'
    exact hz (hψL z h')
  have hψlim := (hBT ψ ψ.continuous hψc hψts).1
  have hμL : ∀ l, μ l L < ⊤ := fun l =>
    MongeAmpere.canonicalBedfordTaylorMeasure_finiteOnCompacts (hh l) hLc hLΩ
  have hμK : ∀ l, μ l K < ⊤ := fun l =>
    MongeAmpere.canonicalBedfordTaylorMeasure_finiteOnCompacts (hh l) hK hKΩ
  have hψi : ∀ l, Integrable ψ (μ l) := fun l =>
    integrable_of_continuous_of_vanishing ψ.continuous hLc (hμL l) hψL
  have hχi : ∀ l, Integrable (χ l) (μ l) := fun l =>
    integrable_of_continuous_of_vanishing (hχc l) hK (hμK l) (hχK l)
  have hχ₀i : ∀ l, Integrable χ₀ (μ l) := fun l =>
    integrable_of_continuous_of_vanishing hχ₀c hK (hμK l) hχ₀K
  -- the difference tends to zero
  have hdiff : Tendsto (fun l => ∫ z, χ l z ∂(μ l) - ∫ z, χ₀ z ∂(μ l)) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    set B : ℝ := ∫ z, ψ z ∂μ₀ + 1 with hB
    have hB0 : 0 < B := by
      have : 0 ≤ ∫ z, ψ z ∂μ₀ := integral_nonneg fun z => (hψI z).1
      linarith
    set η : ℝ := ε / (2 * B) with hη
    have hη0 : 0 < η := by positivity
    have hev1 := hunif η hη0
    have hev2 : ∀ᶠ l in atTop, ∫ z, ψ z ∂(μ l) ≤ B :=
      hψlim.eventually (Iic_mem_nhds (by linarith))
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hev1.and hev2)
    refine ⟨N, fun l hl => ?_⟩
    obtain ⟨h1, h2⟩ := hN l hl
    rw [Real.dist_eq, sub_zero, ← integral_sub (hχi l) (hχ₀i l)]
    have hbound : ∀ z, ‖χ l z - χ₀ z‖ ≤ η * ψ z := by
      intro z
      rw [Real.norm_eq_abs]
      by_cases hz : z ∈ K
      · rw [hψ1 hz, Pi.one_apply, mul_one]
        exact h1 z
      · rw [hχK l z hz, hχ₀K z hz, sub_zero, abs_zero]
        exact mul_nonneg hη0.le (hψI z).1
    calc |∫ z, (χ l z - χ₀ z) ∂(μ l)| ≤ ∫ z, η * ψ z ∂(μ l) := by
          rw [← Real.norm_eq_abs]
          exact norm_integral_le_of_norm_le ((hψi l).const_mul η) (Eventually.of_forall hbound)
      _ = η * ∫ z, ψ z ∂(μ l) := integral_const_mul _ _
      _ ≤ η * B := mul_le_mul_of_nonneg_left h2 hη0.le
      _ < ε := by
          rw [hη, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith
  have := hdiff.add h0
  rw [zero_add] at this
  refine this.congr fun l => ?_
  show ∫ z, χ l z ∂(μ l) - ∫ z, χ₀ z ∂(μ l) + ∫ z, χ₀ z ∂(μ l) = _
  rw [sub_add_cancel]

end Moving

/-! ### Subsequences -/

/-- A `limsup` bound along `φ` follows from bounds along further subsequences of every
subsequence. -/
theorem limsup_le_of_forall_subseq {a : ℕ → ℝ≥0∞} {B : ℝ≥0∞}
    (h : ∀ ψ : ℕ → ℕ, StrictMono ψ → ∃ ξ : ℕ → ℕ, StrictMono ξ ∧
      limsup (fun l => a (ψ (ξ l))) atTop ≤ B) :
    limsup a atTop ≤ B := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨B', hB, hB'⟩ := exists_between hlt
  have hfreq : ∃ᶠ l in atTop, B' < a l := frequently_lt_of_lt_limsup (by isBoundedDefault) hB'
  obtain ⟨ψ, hψ, hψa⟩ := Filter.extraction_of_frequently_atTop hfreq
  obtain ⟨ξ, hξ, hle⟩ := h ψ hψ
  have hge : B' ≤ limsup (fun l => a (ψ (ξ l))) atTop :=
    le_limsup_of_frequently_le (Frequently.of_forall fun l => (hψa (ξ l)).le) (by isBoundedDefault)
  exact absurd (hge.trans hle) (not_le.mpr hB)

/-! ### Auxiliary topology and potentials -/

/-- A function continuous on an open set containing its topological support is continuous. -/
theorem continuous_of_continuousOn_of_tsupport_subset {X : Type*} [TopologicalSpace X]
    {f : X → ℝ} {s : Set X} (hs : IsOpen s) (hf : ContinuousOn f s) (h : tsupport f ⊆ s) :
    Continuous f := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  by_cases hx : x ∈ s
  · exact hf.continuousAt (hs.mem_nhds hx)
  · have hx' : x ∉ tsupport f := fun h' => hx (h h')
    exact continuousAt_const.congr (notMem_tsupport_iff_eventuallyEq.mp hx').symm

/-- **Uniform convergence from joint continuity on a compact product.** -/
theorem eventually_abs_sub_le_of_continuousOn {P Y : Type*} [PseudoMetricSpace P]
    [PseudoMetricSpace Y] {f : P → Y → ℝ} {S : Set P} {K : Set Y} (hS : IsCompact S)
    (hK : IsCompact K) (hf : ContinuousOn (Function.uncurry f) (S ×ˢ K)) {t₀ : P}
    (ht₀ : t₀ ∈ S) {t : ℕ → P} (ht : Tendsto t atTop (𝓝 t₀)) (htS : ∀ᶠ l in atTop, t l ∈ S)
    (η : ℝ) (hη : 0 < η) : ∀ᶠ l in atTop, ∀ y ∈ K, |f (t l) y - f t₀ y| ≤ η := by
  have hu := (hS.prod hK).uniformContinuousOn_of_continuous hf
  obtain ⟨δ, hδ, hδu⟩ := Metric.uniformContinuousOn_iff.mp hu η hη
  filter_upwards [ht.eventually (Metric.ball_mem_nhds t₀ hδ), htS] with l hl hlS y hy
  have hd : dist (t l, y) (t₀, y) < δ := by
    rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
    exact hl
  have := hδu (t l, y) ⟨hlS, hy⟩ (t₀, y) ⟨ht₀, hy⟩ hd
  rw [Real.dist_eq] at this
  exact this.le

section Potentials

variable {k : ℕ} {V : Type*} [TopologicalSpace V] [ChartedSpace (ComplexModel k) V]
  [IsComplexManifold k V]

/-- Local potentials only depend on their values on the (open) domain. -/
theorem IsSmoothLocalPotential.congr' {θ : SmoothRealForm k V 2} {e : ComplexChart k V}
    {W : Set (ComplexModel k)} {ρ ρ' : ComplexModel k → ℝ} (h : IsSmoothLocalPotential θ e W ρ)
    (heq : EqOn ρ ρ' W) : IsSmoothLocalPotential θ e W ρ' := by
  refine ⟨h.1, h.2.1, h.2.2.1.congr fun z hz => (heq hz).symm, fun z hz => ?_⟩
  rw [← h.2.2.2 hz]
  exact smoothDDC_congr (Filter.eventuallyEq_of_mem (h.1.mem_nhds hz) heq).symm

/-- A local potential plus a constant is a local potential. -/
theorem IsSmoothLocalPotential.add_const' {θ : SmoothRealForm k V 2} {e : ComplexChart k V}
    {W : Set (ComplexModel k)} {ρ : ComplexModel k → ℝ} (h : IsSmoothLocalPotential θ e W ρ)
    (c : ℝ) : IsSmoothLocalPotential θ e W (fun y => ρ y + c) := by
  refine ⟨h.1, h.2.1, h.2.2.1.add contDiffOn_const, fun z hz => ?_⟩
  rw [smoothDDC_add h.1 h.2.2.1 contDiffOn_const hz, GlobalPotentialTransforms.smoothDDC_const,
    add_zero]
  exact h.2.2.2 hz

end Potentials

/-! ### Corrected potentials and the chart-level convergence -/

section Core

variable {k N : ℕ} {V : Type*} [TopologicalSpace V] [ChartedSpace (ComplexModel k) V]
  [IsComplexManifold k V] {𝒳 : Type*} [TopologicalSpace 𝒳]
  [ChartedSpace (ComplexModel N) 𝒳] [IsComplexManifold N 𝒳]

/-- The pulled-back local potential `ρ ∘ d ∘ j ∘ e⁻¹ + c` on a chart domain `A` that `j ∘ e⁻¹` maps
into the domain of `ρ`. -/
theorem isSmoothLocalPotential_pullback_of_eqOn {j : V → 𝒳}
    (hj : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel N) ∞ j) (Θ : ClosedRealOneOneForm N 𝒳)
    {d : ComplexChart N 𝒳} {Wd : Set (ComplexModel N)} {ρ : ComplexModel N → ℝ}
    (hρ : IsSmoothLocalPotential Θ.val d Wd ρ) (e : ComplexChart k V) {A : Set (ComplexModel k)}
    (hA : IsOpen A) (hAe : A ⊆ e.val.target)
    (hAd : ∀ y ∈ A, j (e.val.symm y) ∈ d.val.source ∧ d.val (j (e.val.symm y)) ∈ Wd)
    {P : ComplexModel k → ℝ} (c : ℝ) (hP : ∀ y ∈ A, P y = ρ (d.val (j (e.val.symm y))) + c) :
    IsSmoothLocalPotential (ClosedRealOneOneForm.pullback hj Θ).val e A P := by
  have hbase := isSmoothLocalPotential_pullback hj e hρ
  have hsub : A ⊆ potentialDomain j e d Wd := fun y hy =>
    ⟨⟨hAe hy, (hAd y hy).1⟩, (hAd y hy).2⟩
  refine IsSmoothLocalPotential.congr'
    (IsSmoothLocalPotential.add_const' (hbase.mono hA hsub) c) fun y hy => ?_
  rw [hP y hy]
  rfl

/-- A corrected potential which is real and bounded on `A` is locally bounded psh there. -/
theorem isLocallyBoundedPshOn_of_corrected {θ : SmoothRealForm k V 2} {u : V → EReal}
    (hu : ThetaPlurisubharmonic θ u) (e : ComplexChart k V) (A : Opens (ComplexModel k))
    {P : ComplexModel k → ℝ} (hP : IsSmoothLocalPotential θ e A P) {f : ComplexModel k → ℝ}
    (hfeq : ∀ y ∈ A, chartFunction u e y + (P y : EReal) = (f y : EReal)) {M : ℝ}
    (hM : ∀ y ∈ A, |f y| ≤ M) : IsLocallyBoundedPshOn A f := by
  have hpsh := BoundedGlobalProduct.ThetaPlurisubharmonic.corrected_plurisubharmonicOn hu e hP
  refine ⟨fun x hx => (hpsh x hx).congr (Filter.eventuallyEq_of_mem (A.isOpen.mem_nhds hx)
    fun z hz => hfeq z hz), fun z hz => ⟨A, hz, le_rfl, M, hM⟩⟩

variable [CompactSpace V]

/-- **Convergence of the test masses in a chart** (the measure-theoretic part of WN21
Proposition 7.4): if the corrected potentials of `u_l` (for `j_l^*Θ`) and of `u₀` (for `j₀^*Θ`) in a
chart domain `A` are an increasing sequence `h_l` of locally bounded psh functions converging a.e. to
`H`, and the test functions `ρ ∘ j_l ∘ e⁻¹ = χ_l` converge uniformly to `ρ ∘ j₀ ∘ e⁻¹ = χ₀`, all
vanishing off a compact `K ⊆ A`, then `∫ ρ ∘ j_l d⟨(j_l^*Θ + dd^c u_l)ᵏ⟩ → ∫ ρ ∘ j₀ d⟨(j₀^*Θ + dd^c u₀)ᵏ⟩`. -/
theorem tendsto_restrictedTestMass_of_chart (Θ : ClosedRealOneOneForm N 𝒳)
    (e : ComplexChart k V) (A : Opens (ComplexModel k))
    {j : ℕ → V → 𝒳} (hj : ∀ l, ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel N) ∞ (j l))
    {j₀ : V → 𝒳} (hj₀ : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel N) ∞ j₀)
    {u : ℕ → V → EReal}
    (hu : ∀ l, IsThetaPshPotential (ClosedRealOneOneForm.pullback (hj l) Θ).val (u l))
    {u₀ : V → EReal} (hu₀ : IsThetaPshPotential (ClosedRealOneOneForm.pullback hj₀ Θ).val u₀)
    {P : ℕ → ComplexModel k → ℝ}
    (hP : ∀ l, IsSmoothLocalPotential (ClosedRealOneOneForm.pullback (hj l) Θ).val e A (P l))
    {P₀ : ComplexModel k → ℝ}
    (hP₀ : IsSmoothLocalPotential (ClosedRealOneOneForm.pullback hj₀ Θ).val e A P₀)
    {h : ℕ → ComplexModel k → ℝ} (hh : ∀ l, IsLocallyBoundedPshOn A (h l))
    {H : ComplexModel k → ℝ} (hH : IsLocallyBoundedPshOn A H)
    (hheq : ∀ l, ∀ y ∈ A, chartFunction (u l) e y + (P l y : EReal) = (h l y : EReal))
    (hHeq : ∀ y ∈ A, chartFunction u₀ e y + (P₀ y : EReal) = (H y : EReal))
    (hmono : ∀ y ∈ A, Monotone fun l => h l y)
    (hae : ∀ᵐ y, y ∈ A → Tendsto (fun l => h l y) atTop (𝓝 (H y)))
    (ρ : 𝒳 → ℝ) (hρ0 : ∀ z, 0 ≤ ρ z)
    (hsupp : ∀ l x, ρ (j l x) ≠ 0 → x ∈ e.val.source ∧ e.val x ∈ A)
    (hsupp₀ : ∀ x, ρ (j₀ x) ≠ 0 → x ∈ e.val.source ∧ e.val x ∈ A)
    {χ : ℕ → ComplexModel k → ℝ} {χ₀ : ComplexModel k → ℝ}
    (hχc : ∀ l, Continuous (χ l)) (hχ₀c : Continuous χ₀)
    {K : Set (ComplexModel k)} (hK : IsCompact K) (hKA : K ⊆ A)
    (hχK : ∀ l z, z ∉ K → χ l z = 0) (hχ₀K : ∀ z, z ∉ K → χ₀ z = 0)
    (hχeq : ∀ l, ∀ y ∈ A, ρ (j l (e.val.symm y)) = χ l y)
    (hχ₀eq : ∀ y ∈ A, ρ (j₀ (e.val.symm y)) = χ₀ y)
    (hunif : ∀ η : ℝ, 0 < η → ∀ᶠ l in atTop, ∀ z, |χ l z - χ₀ z| ≤ η) :
    Tendsto (fun l => restrictedTestMass (hj l) Θ (u l) (hu l) ρ) atTop
      (𝓝 (restrictedTestMass hj₀ Θ u₀ hu₀ ρ)) := by
  let : MeasurableSpace V := borel V
  have : BorelSpace V := ⟨rfl⟩
  -- the masses as Bedford--Taylor integrals
  have hnn : ∀ (g : ComplexModel k → ℝ), (∀ y ∈ A, 0 ≤ g y) → (∀ z, z ∉ K → g z = 0) →
      ∀ z, 0 ≤ g z := fun g hg hgK z => by
    by_cases hz : z ∈ K
    · exact hg z (hKA hz)
    · rw [hgK z hz]
  have hχnn : ∀ l z, 0 ≤ χ l z := fun l => hnn (χ l)
    (fun y hy => by rw [← hχeq l y hy]; exact hρ0 _) (hχK l)
  have hχ₀nn : ∀ z, 0 ≤ χ₀ z := hnn χ₀ (fun y hy => by rw [← hχ₀eq y hy]; exact hρ0 _) hχ₀K
  have hmass : ∀ (j' : V → 𝒳) (hj' : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel N) ∞ j')
      (u' : V → EReal) (hu' : IsThetaPshPotential (ClosedRealOneOneForm.pullback hj' Θ).val u')
      (P' : ComplexModel k → ℝ)
      (hP' : IsSmoothLocalPotential (ClosedRealOneOneForm.pullback hj' Θ).val e A P')
      (h' : ComplexModel k → ℝ) (hh' : IsLocallyBoundedPshOn A h')
      (hheq' : ∀ y ∈ A, chartFunction u' e y + (P' y : EReal) = (h' y : EReal))
      (hsupp' : ∀ x, ρ (j' x) ≠ 0 → x ∈ e.val.source ∧ e.val x ∈ A)
      (χ' : ComplexModel k → ℝ) (hχ'c : Continuous χ') (hχ'K : ∀ z, z ∉ K → χ' z = 0)
      (hχ'nn : ∀ z, 0 ≤ χ' z) (hχ'eq : ∀ y ∈ A, ρ (j' (e.val.symm y)) = χ' y),
      restrictedTestMass hj' Θ u' hu' ρ =
        ENNReal.ofReal (∫ y, χ' y ∂(MongeAmpere.canonicalBedfordTaylorMeasure A h' hh')) := by
    intro j' hj' u' hu' P' hP' h' hh' hheq' hsupp' χ' hχ'c hχ'K hχ'nn hχ'eq
    have hG : ∀ x, ENNReal.ofReal (ρ (j' x)) ≠ 0 → x ∈ e.val.source ∧ e.val x ∈ A :=
      fun x hx => hsupp' x fun h0 => hx (by rw [h0, ENNReal.ofReal_zero])
    unfold restrictedTestMass
    rw [lintegral_diagonalPotentialMeasure_eq_canonical _ hu' e A hP' hh' hheq' _ hG]
    have hAe : ∀ᵐ y ∂(MongeAmpere.canonicalBedfordTaylorMeasure A h' hh'), y ∈ A :=
      ae_iff.mpr (by
        have := MongeAmpere.canonicalBedfordTaylorMeasure_compl A h' hh'
        simpa [compl_def] using this)
    rw [lintegral_congr_ae (hAe.mono fun y hy => by rw [hχ'eq y hy])]
    have hμK := MongeAmpere.canonicalBedfordTaylorMeasure_finiteOnCompacts hh' hK hKA
    exact (ofReal_integral_eq_lintegral_ofReal
      (integrable_of_continuous_of_vanishing hχ'c hK hμK hχ'K)
      (Eventually.of_forall hχ'nn)).symm
  have hl : ∀ l, restrictedTestMass (hj l) Θ (u l) (hu l) ρ =
      ENNReal.ofReal (∫ y, χ l y ∂(MongeAmpere.canonicalBedfordTaylorMeasure A (h l) (hh l))) :=
    fun l => hmass (j l) (hj l) (u l) (hu l) (P l) (hP l) (h l) (hh l) (hheq l) (hsupp l) (χ l)
      (hχc l) (hχK l) (hχnn l) (hχeq l)
  have h0 : restrictedTestMass hj₀ Θ u₀ hu₀ ρ =
      ENNReal.ofReal (∫ y, χ₀ y ∂(MongeAmpere.canonicalBedfordTaylorMeasure A H hH)) :=
    hmass j₀ hj₀ u₀ hu₀ P₀ hP₀ H hH hHeq hsupp₀ χ₀ hχ₀c hχ₀K hχ₀nn hχ₀eq
  simp only [hl, h0]
  exact (ENNReal.continuous_ofReal.tendsto _).comp
    (tendsto_integral_canonicalBedfordTaylorMeasure_of_monotone hh hH hmono hae hχc hχ₀c hK hKA
      hχK hχ₀K hunif)

end Core

end SGPT.Okounkov.TranscendentalWN
