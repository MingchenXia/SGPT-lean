import SGPT.Foundations.Analysis.Pending.BergmanKernelSmooth
import SGPT.Foundations.Analysis.Pending.MultiplierIdealBergmanNadelIdeal
import SGPT.Foundations.Analysis.Pending.DemaillyApproximation
import SGPT.Foundations.Analysis.Pending.HolomorphicGermRing

set_option autoImplicit false

/-! # The full Hilbert evaluation ideal is the original multiplier ideal

Nadel's actual weighted germ identity and the genuine weighted L2 classes
identify all evaluation germs, also after every local holomorphic pullback.
No principal generator, finite section presentation or quotient is assumed.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.ActualBergmanEvaluationMultiplierPullbackIdeal

open FirstPass BergmanKernelSmooth MultiplierIdealBergmanNadelIdeal

private theorem eventually_holomorphic_comp {d n : ℕ}
    {Φ : ComplexModel d → ComplexModel n}
    (hΦ : ∀ᶠ x in 𝓝 0, DifferentiableAt ℂ Φ x)
    {f : ComplexModel n → ℂ}
    (hf : ∀ᶠ y in 𝓝 (Φ 0), DifferentiableAt ℂ f y) :
    ∀ᶠ x in 𝓝 0, DifferentiableAt ℂ (fun x => f (Φ x)) x := by
  have ht : Tendsto Φ (𝓝 0) (𝓝 (Φ 0)) := hΦ.self_of_nhds.continuousAt.tendsto
  filter_upwards [hΦ, ht.eventually hf] with x hx hfx
  exact hfx.comp x hx

private theorem multiplier_eventually_holomorphic {n : ℕ}
    {Ψ : ComplexModel n → EReal} {c : ℝ} {f : ComplexModel n → ℂ}
    {y : ComplexModel n} (hf : MultiplierIntegrableAt Ψ c f y volume) :
    ∀ᶠ t in 𝓝 y, DifferentiableAt ℂ f t := by
  obtain ⟨_, U, hU, hyU, hhol, _⟩ := hf
  exact Filter.eventually_of_mem (hU.mem_nhds hyU) fun t ht =>
    hhol.differentiableAt (hU.mem_nhds ht)

/-- The germ of the actual Hilbert evaluation along the original map. -/
def evaluationGerm {n d : ℕ} {K : Set (ComplexModel n)} {w : ComplexModel n → ℝ≥0∞}
    (hBw : BergmanWeight K w) (Φ : ComplexModel d → ComplexModel n)
    (hΦ : ∀ᶠ x in 𝓝 0, DifferentiableAt ℂ Φ x) (hyK : Φ 0 ∈ K)
    (F : bergmanSubspace K w) : HolGerm (ComplexModel d) :=
  HolGerm.mk (fun x => evalCLM hBw (Φ x) F)
    (eventually_holomorphic_comp hΦ
      (Filter.eventually_of_mem (hBw.isOpen.mem_nhds hyK) fun _ ht =>
        (differentiableOn_rep F).differentiableAt (hBw.isOpen.mem_nhds ht)))

/-- The original weighted multiplier representative, composed with the same
local holomorphic map, as a genuine holomorphic germ. -/
def weightedPullbackGerm {n d : ℕ} {Ψ : ComplexModel n → EReal} {c : ℝ}
    (Φ : ComplexModel d → ComplexModel n)
    (hΦ : ∀ᶠ x in 𝓝 0, DifferentiableAt ℂ Φ x)
    (f : {f : ComplexModel n → ℂ // MultiplierIntegrableAt Ψ c f (Φ 0) volume}) :
    HolGerm (ComplexModel d) :=
  HolGerm.mk (fun x => f.val (Φ x))
    (eventually_holomorphic_comp hΦ (multiplier_eventually_holomorphic f.property))

private theorem exists_hilbert_rep {n : ℕ} {K : Set (ComplexModel n)}
    {w : ComplexModel n → ℝ≥0∞} (hBw : BergmanWeight K w)
    {g : ComplexModel n → ℂ} (hg : g ∈ bergmanSpace K w) :
    ∃ F : bergmanSubspace K w, EqOn (rep F) g K := by
  have hmeas : AEStronglyMeasurable g (bergmanMeasure K w) :=
    (hg.1.continuousOn.aestronglyMeasurable hBw.isOpen.measurableSet).mono_ac
      (withDensity_absolutelyContinuous _ _)
  have hint := lintegral_enorm_sq_eq hBw.aemeasurable hmeas (EventuallyEq.refl _ g)
  have hmem : MemLp g 2 (bergmanMeasure K w) := by
    refine ⟨hmeas, ?_⟩
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top]
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
    rw [hint]
    exact lt_top_iff_ne_top.mpr hg.2
  let F : bergmanSubspace K w := ⟨hmem.toLp g, g, hg.1, hmem.coeFn_toLp⟩
  exact ⟨F, rep_eqOn hBw F hg.1 hmem.coeFn_toLp⟩

private theorem rep_multiplier {n : ℕ} {K : Set (ComplexModel n)}
    {Ψ : ComplexModel n → EReal} {c : ℝ} (hc : 0 < c)
    (hBw : BergmanWeight K (fun t => multiplierWeight c (Ψ t)))
    {y : ComplexModel n} (hyK : y ∈ K)
    (F : bergmanSubspace K (fun t => multiplierWeight c (Ψ t))) :
    MultiplierIntegrableAt Ψ c (rep F) y volume := by
  refine ⟨hc, K, hBw.isOpen, hyK, differentiableOn_rep F, ?_, ?_⟩
  · exact ((ENNReal.continuous_ofReal.comp_continuousOn
      ((differentiableOn_rep F).continuousOn.norm.pow 2)).aemeasurable
        hBw.isOpen.measurableSet).mul hBw.aemeasurable
  · change ∫⁻ t in K, ENNReal.ofReal (‖rep F t‖ ^ 2) * multiplierWeight c (Ψ t) < ⊤
    rw [← ofReal_norm_sq_eq hBw.aemeasurable (ae_eq_rep hBw F)]
    exact ENNReal.ofReal_lt_top

/-- The original PSH data supply the Hilbert weight; all evaluation germs
generate precisely the original multiplier ideal after every local
holomorphic pullback. -/
theorem exists_bergmanWeight_and_pullback_germ_span {m : ℕ}
    {Ω : TopologicalSpace.Opens (ComplexModel (m + 1))}
    {Ψ : ComplexModel (m + 1) → EReal} (hΨ : PlurisubharmonicOn Ψ Ω)
    {c : ℝ} (hc : 0 < c) {L : Set (ComplexModel (m + 1))}
    (hLo : IsOpen L) (hLc : Convex ℝ L) (hLb : Bornology.IsBounded L)
    (hLΩ : closure L ⊆ Ω) {K : Set (ComplexModel (m + 1))}
    (hKo : IsOpen K) (hKL : closure K ⊆ L) :
    ∃ hBw : BergmanWeight K (fun t => multiplierWeight c (Ψ t)),
      DifferentiableOn ℂ (evalCLM hBw) K ∧
      ∀ (d : ℕ) (Φ : ComplexModel d → ComplexModel (m + 1))
        (hΦ : ∀ᶠ x in 𝓝 0, DifferentiableAt ℂ Φ x) (hyK : Φ 0 ∈ K),
        Ideal.span (range (evaluationGerm hBw Φ hΦ hyK)) =
          Ideal.span (range (weightedPullbackGerm (Ψ := Ψ) (c := c) Φ hΦ)) := by
  classical
  have hKΩ : K ⊆ Ω := subset_closure.trans (hKL.trans (subset_closure.trans hLΩ))
  have hBw : BergmanWeight K (fun t => multiplierWeight c (Ψ t)) := by
    refine ⟨hKo, DemaillyApproximation.aemeasurable_multiplierWeight_restrict hKo
      (hΨ.upperSemicontinuousOn.mono hKΩ) hc.ne', fun y hy => ?_⟩
    obtain ⟨ε, hε, hεK⟩ := Metric.isOpen_iff.mp hKo y hy
    have hcb : closedBall y (ε / 2) ⊆ K :=
      (closedBall_subset_ball (by linarith)).trans hεK
    obtain ⟨C, _, hC⟩ := hΨ.exists_nonnegative_compact_upper_bound
      (isCompact_closedBall y (ε / 2)) (hcb.trans hKΩ)
    refine ⟨Real.exp (-(c * C)), Real.exp_pos _, ε / 2, by positivity, hcb, fun t ht => ?_⟩
    rw [← multiplierWeight_coe]
    exact multiplierWeight_antitone hc.le (hC t ht)
  refine ⟨hBw, differentiableOn_evalCLM hBw, ?_⟩
  intro d Φ hΦ hyK
  apply le_antisymm
  · refine Ideal.span_le.mpr ?_
    rintro _ ⟨F, rfl⟩
    let f : {f : ComplexModel (m + 1) → ℂ // MultiplierIntegrableAt Ψ c f (Φ 0) volume} :=
      ⟨rep F, rep_multiplier hc hBw hyK F⟩
    exact Ideal.subset_span ⟨f, rfl⟩
  · refine Ideal.span_le.mpr ?_
    rintro _ ⟨f, rfl⟩
    obtain ⟨_, U, hU, hyU, hfU, hfint⟩ := f.property
    obtain ⟨ρ, hρ, hρU⟩ := Metric.isOpen_iff.mp hU (Φ 0) hyU
    have hint : ∫⁻ t in ball (Φ 0) ρ, ENNReal.ofReal (‖f.val t‖ ^ 2) *
        multiplierWeight c (Ψ t) ≠ ⊤ :=
      ne_top_of_le_ne_top hfint.2.ne (lintegral_mono_set hρU)
    obtain ⟨N, s, a, hs, ha, he⟩ := inGermSpan_bergmanSpace hΨ hc hLo hLc hLb hLΩ
      hKo hKL hyK hρ (hfU.mono hρU) hint
    choose F hF using fun i => exists_hilbert_rep hBw (hs i)
    have ht : Tendsto Φ (𝓝 0) (𝓝 (Φ 0)) := hΦ.self_of_nhds.continuousAt.tendsto
    let A : Fin N → ComplexModel d → ℂ := fun i x => a i (Φ x)
    let B : Fin N → ComplexModel d → ℂ := fun i x => rep (F i) (Φ x)
    have hA : ∀ i, ∀ᶠ x in 𝓝 0, DifferentiableAt ℂ (A i) x :=
      fun i => eventually_holomorphic_comp hΦ (ha i)
    have hB : ∀ i, ∀ᶠ x in 𝓝 0, DifferentiableAt ℂ (B i) x := fun i =>
      eventually_holomorphic_comp hΦ
        (Filter.eventually_of_mem (hKo.mem_nhds hyK) fun t ht =>
          (differentiableOn_rep (F i)).differentiableAt (hKo.mem_nhds ht))
    have hprod : ∀ i, ∀ᶠ x in 𝓝 0,
        DifferentiableAt ℂ (fun x => A i x * B i x) x :=
      fun i => eventually_differentiableAt_mul (hA i) (hB i)
    have hepull : (fun x => f.val (Φ x)) =ᶠ[𝓝 0] fun x => ∑ i, A i x * B i x := by
      filter_upwards [ht.eventually he, ht.eventually (hKo.mem_nhds hyK)] with x hx hxK
      rw [hx]
      exact Finset.sum_congr rfl fun i _ => by
        dsimp only [A, B]
        rw [hF i hxK]
    have hEq : weightedPullbackGerm (Ψ := Ψ) (c := c) Φ hΦ f =
        ∑ i, HolGerm.mk (A i) (hA i) * evaluationGerm hBw Φ hΦ hyK (F i) := by
      calc
        _ = HolGerm.mk (fun x => ∑ i, A i x * B i x)
            (eventually_differentiableAt_sum Finset.univ hprod) :=
          HolGerm.mk_eq_mk_iff.mpr hepull
        _ = _ := by
          rw [HolGerm.mk_sum]
          apply Finset.sum_congr rfl
          intro i _
          exact HolGerm.mk_mul (A i) (B i) (hA i) (hB i)
    rw [hEq]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨F i, rfl⟩)

end SGPT.Foundations.Analysis.Pending.ActualBergmanEvaluationMultiplierPullbackIdeal
