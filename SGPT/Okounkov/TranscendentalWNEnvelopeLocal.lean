import SGPT.Okounkov.TranscendentalWNEnvelopeBump
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Covering.Differentiation

/-!
# Monge–Ampère measures on contact sets, in coordinates (package WN-ENV, local part)

Blueprint chapter `claude-tok-wn-env` (nodes `tok-wn-env:hessian-bump`,
`tok-wn-env:local-positivity`, `tok-wn-env:closed-ball`, `tok-wn-env:local-contact`), the local
half of `tok-wn:contact-positivity` and `tok-wn:contact-upper` of the WN chapter
(`claude-tok-wn`): the elementary inequality "`≤`" of the Di Nezza–Trapani contact formula.

Let `Ω ⊆ ℂⁿ` be open, `q` smooth and plurisubharmonic on `Ω`, and `U ≤ q` plurisubharmonic on
`Ω` (possibly unbounded).  On the contact set `C = {U = q}` the non-pluripolar Monge–Ampère
measure of `U` is bounded by the smooth measure `(ddᶜq)ⁿ`:

* `canonicalBedfordTaylorMeasure_contact_closedBall_le` — for a locally bounded `V ≤ q` and a
  closed ball `B̄(x, r)` with `B̄(x, 2r) ⊆ Ω`,
  `(ddᶜV)ⁿ(C ∩ B̄(x, r)) ≤ ∫_{C ∩ B̄(x, r)} (ddᶜq)ⁿ`.  The comparator
  `q + s(|z - x|² - (r + s)²)` is plurisubharmonic, lies below `V` on `C ∩ B̄(x, r)` and above
  `V` off the compact ball `B̄(x, r + s)`; the comparison principle on strict sets
  (`SGPT.MongeAmpere.canonicalBedfordTaylorMeasure_gt_le_smoothMeasure`) and `s → 0`
  (dominated convergence of the explicit densities `det (ddᶜq + s·1)`) give the bound.
* `canonicalBedfordTaylorMeasure_contact_le` — the same bound on every subset of `C` in a ball
  `B(x₀, R)` with `B̄(x₀, 2R) ⊆ Ω`: closed balls at every point of `C` are a fine cover, and the
  Besicovitch Vitali family (`VitaliFamily.measure_le_of_frequently_le`) turns the bound on
  small closed balls into a bound of measures.
* `truncationLimitMeasure_contact_le` — the unbounded case, by plurifine locality of the
  maximum: on `{q - 1 < U} ⊇ C` the measure of `U` is that of `max (U, q - 1)`.
* `leviForm_nonneg_of_contact` — at a contact point the Levi form of `q` is nonnegative
  (`SGPT.MongeAmpere.complexHessian_posSemidef_of_smooth_upper_test`, applied to a global
  smooth representative of the germ of `q`).

The proof uses neither the `C^{1,1}` regularity of envelopes nor the real analysis of the
book's `lma:DNTroof`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology ContDiff ComplexOrder MatrixOrder

namespace SGPT.Okounkov.TranscendentalWN.EnvelopeLocal

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.MongeAmpere

variable {n : ℕ}

/-! ### The bound on closed balls -/

/-- The strict band `{q - 4r²s < V} ∩ B̄(x, r + s)` of the closed-ball argument. -/
def strictBand (Ω : Opens (ComplexModel n)) (q V : ComplexModel n → ℝ) (x : ComplexModel n)
    (r s : ℝ) : Set (ComplexModel n) :=
  {z | z ∈ Ω ∧ q z - 4 * r ^ 2 * s < V z} ∩ closedBall x (r + s)

theorem measurableSet_strictBand {Ω : Opens (ComplexModel n)} {q V : ComplexModel n → ℝ}
    (hq : ContinuousOn q Ω) (hV : UpperSemicontinuousOn (fun z => (V z : EReal)) Ω)
    (x : ComplexModel n) (r s : ℝ) : MeasurableSet (strictBand Ω q V x r s) :=
  (measurableSet_lt_of_upperSemicontinuousOn (hq.sub continuousOn_const) hV).inter
    measurableSet_closedBall

/-- **One comparator.**  For `0 < s ≤ r`, the comparison principle applied to
`q + s(|z - x|² - (r + s)²)` bounds the Bedford–Taylor mass of `{V = q} ∩ B̄(x, r)` by the
integral of `det (ddᶜq + s·1)` over the strict band. -/
theorem canonicalBedfordTaylorMeasure_contact_closedBall_le_band (hn : 0 < n)
    {Ω : Opens (ComplexModel n)} {V q : ComplexModel n → ℝ}
    (hV : IsLocallyBoundedPshOn Ω V) (hq : IsSmoothPshOn Ω q)
    (hVq : ∀ z ∈ Ω, V z ≤ q z) {x : ComplexModel n} {r : ℝ} (hr : 0 < r)
    (hball : closedBall x (2 * r) ⊆ Ω) {s : ℝ} (hs0 : 0 < s) (hsr : s ≤ r) :
    canonicalBedfordTaylorMeasure Ω V hV ({z | z ∈ Ω ∧ V z = q z} ∩ closedBall x r) ≤
      ∫⁻ z in strictBand Ω q V x r s, ENNReal.ofReal (bumpDensity q s z) := by
  have hq2 : ∀ z ∈ Ω, ContDiffAt ℝ 2 q z := fun z hz =>
    ((hq.1 z hz).contDiffAt (Ω.isOpen.mem_nhds hz)).of_le two_le_infty
  have hTm := measurableSet_strictBand hq.1.continuousOn hV.1.upperSemicontinuousOn x r s
  have hQ : IsSmoothPshOn Ω (bump q x s ((r + s) ^ 2)) := isSmoothPshOn_bump hq x hs0.le _
  have hK : IsCompact (closedBall x (r + s)) := isCompact_closedBall x (r + s)
  have hKΩ : closedBall x (r + s) ⊆ Ω :=
    (closedBall_subset_closedBall (by linarith)).trans hball
  have hout : ∀ z ∈ Ω, z ∉ closedBall x (r + s) → V z ≤ bump q x s ((r + s) ^ 2) z := by
    intro z hz hzK
    have hd : r + s < ‖z - x‖ := by
      rw [mem_closedBall, dist_eq_norm, not_le] at hzK
      exact hzK
    have hsq : (r + s) ^ 2 < ‖z - x‖ ^ 2 := by
      have h0 : 0 ≤ r + s := by linarith
      nlinarith
    have : 0 ≤ s * (‖z - x‖ ^ 2 - (r + s) ^ 2) := mul_nonneg hs0.le (by linarith)
    simp only [bump]
    linarith [hVq z hz]
  have hcmp :=
    SGPT.MongeAmpere.canonicalBedfordTaylorMeasure_gt_le_smoothMeasure hn hV hQ hK hKΩ hout
  have hCsub : {z | z ∈ Ω ∧ V z = q z} ∩ closedBall x r ⊆
      {z | z ∈ Ω ∧ bump q x s ((r + s) ^ 2) z < V z} := by
    intro z hz
    refine ⟨hz.1.1, ?_⟩
    have hd : ‖z - x‖ ≤ r := by
      have := hz.2
      rw [mem_closedBall, dist_eq_norm] at this
      exact this
    have hsq : ‖z - x‖ ^ 2 < (r + s) ^ 2 := by nlinarith [norm_nonneg (z - x)]
    have : s * (‖z - x‖ ^ 2 - (r + s) ^ 2) < 0 := mul_neg_of_pos_of_neg hs0 (by linarith)
    simp only [bump]
    linarith [hz.1.2]
  have hsubT : {z | z ∈ Ω ∧ bump q x s ((r + s) ^ 2) z < V z} ⊆ strictBand Ω q V x r s := by
    intro z hz
    have hzK : z ∈ closedBall x (r + s) := by
      by_contra hzK
      exact absurd (hout z hz.1 hzK) (not_le.mpr hz.2)
    refine ⟨⟨hz.1, ?_⟩, hzK⟩
    have hd : ‖z - x‖ ≤ r + s := by
      rw [mem_closedBall, dist_eq_norm] at hzK
      exact hzK
    have hQge : q z - 4 * r ^ 2 * s ≤ bump q x s ((r + s) ^ 2) z := by
      simp only [bump]
      have h1 : (r + s) ^ 2 ≤ 4 * r ^ 2 := by nlinarith
      nlinarith [norm_nonneg (z - x), sq_nonneg ‖z - x‖]
    exact lt_of_le_of_lt hQge hz.2
  calc canonicalBedfordTaylorMeasure Ω V hV ({z | z ∈ Ω ∧ V z = q z} ∩ closedBall x r)
      ≤ canonicalBedfordTaylorMeasure Ω V hV
          {z | z ∈ Ω ∧ bump q x s ((r + s) ^ 2) z < V z} := measure_mono hCsub
    _ ≤ smoothMeasure Ω (bump q x s ((r + s) ^ 2)) hQ
          {z | z ∈ Ω ∧ bump q x s ((r + s) ^ 2) z < V z} := hcmp
    _ = ∫⁻ z in {z | z ∈ Ω ∧ bump q x s ((r + s) ^ 2) z < V z},
          ENNReal.ofReal (smoothDensity (bump q x s ((r + s) ^ 2)) z)
            ∂(volume.restrict (Ω : Set (ComplexModel n))) := by
        rw [smoothMeasure, withDensity_apply']
    _ ≤ ∫⁻ z in strictBand Ω q V x r s,
          ENNReal.ofReal (smoothDensity (bump q x s ((r + s) ^ 2)) z) :=
        lintegral_mono' (Measure.restrict_mono hsubT Measure.restrict_le_self) le_rfl
    _ = ∫⁻ z in strictBand Ω q V x r s, ENNReal.ofReal (bumpDensity q s z) := by
        refine setLIntegral_congr_fun hTm fun z hz => ?_
        rw [smoothDensity_bump (hq2 z hz.1.1)]

/-- **The limit of the bands.**  As `s → 0` the band integrals of `det (ddᶜq + s·1)` tend to the
integral of the smooth density of `q` over `{V = q} ∩ B̄(x, r)` (dominated convergence). -/
theorem tendsto_lintegral_strictBand {Ω : Opens (ComplexModel n)} {V q : ComplexModel n → ℝ}
    (hV : UpperSemicontinuousOn (fun z => (V z : EReal)) Ω) (hq : ContDiffOn ℝ ∞ q Ω)
    (hVq : ∀ z ∈ Ω, V z ≤ q z) {x : ComplexModel n} {r : ℝ} (hr : 0 < r)
    (hball : closedBall x (2 * r) ⊆ Ω) :
    Tendsto (fun j : ℕ => ∫⁻ z in strictBand Ω q V x r (r / ((j : ℝ) + 2)),
        ENNReal.ofReal (bumpDensity q (r / ((j : ℝ) + 2)) z)) atTop
      (𝓝 (∫⁻ z in {z | z ∈ Ω ∧ V z = q z} ∩ closedBall x r,
        ENNReal.ofReal (smoothDensity q z))) := by
  set C : Set (ComplexModel n) := {z | z ∈ Ω ∧ V z = q z} ∩ closedBall x r with hC
  have hTm := measurableSet_strictBand hq.continuousOn hV x r
  have hCm : MeasurableSet C :=
    (measurableSet_eq_of_upperSemicontinuousOn hq.continuousOn hV).inter measurableSet_closedBall
  have hdc := continuousOn_bumpDensity Ω.isOpen hq
  have hKcomp : IsCompact (Icc (0 : ℝ) r ×ˢ closedBall x (2 * r)) :=
    isCompact_Icc.prod (isCompact_closedBall x _)
  have hKsub : Icc (0 : ℝ) r ×ˢ closedBall x (2 * r) ⊆ univ ×ˢ (Ω : Set (ComplexModel n)) :=
    prod_mono (subset_univ _) hball
  obtain ⟨B, hB⟩ := hKcomp.exists_bound_of_continuousOn (hdc.mono hKsub)
  have hdz : ∀ σ : ℝ, ContinuousOn (fun z => bumpDensity q σ z) Ω :=
    continuousOn_bumpDensity_point Ω.isOpen hq
  set s : ℕ → ℝ := fun j => r / ((j : ℝ) + 2) with hsdef
  have hs0 : ∀ j, 0 < s j := fun j => div_pos hr (by positivity)
  have hsr : ∀ j, s j ≤ r := fun j =>
    div_le_self hr.le (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])
  have hslim : Tendsto s atTop (𝓝 0) := by
    have h : Tendsto (fun j : ℕ => (j : ℝ) + 2) atTop atTop :=
      tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
    exact tendsto_const_nhds.div_atTop h
  have hTL : ∀ j, strictBand Ω q V x r (s j) ⊆ closedBall x (2 * r) := fun j z hz =>
    closedBall_subset_closedBall (by linarith [hsr j]) hz.2
  have hCL : C ⊆ closedBall x (2 * r) := fun z hz =>
    closedBall_subset_closedBall (by linarith) hz.2
  have hFint : ∀ j, ∫⁻ z in strictBand Ω q V x r (s j), ENNReal.ofReal (bumpDensity q (s j) z) =
      ∫⁻ z in closedBall x (2 * r), (strictBand Ω q V x r (s j)).indicator
        (fun z => ENNReal.ofReal (bumpDensity q (s j) z)) z := by
    intro j
    rw [setLIntegral_indicator (hTm _), inter_eq_left.mpr (hTL j)]
  have hGint : ∫⁻ z in C, ENNReal.ofReal (smoothDensity q z) =
      ∫⁻ z in closedBall x (2 * r), C.indicator (fun z => ENNReal.ofReal (smoothDensity q z)) z := by
    rw [setLIntegral_indicator hCm, inter_eq_left.mpr hCL]
  rw [hGint]
  have hfun : (fun j : ℕ => ∫⁻ z in strictBand Ω q V x r (r / ((j : ℝ) + 2)),
      ENNReal.ofReal (bumpDensity q (r / ((j : ℝ) + 2)) z)) = fun j =>
      ∫⁻ z in closedBall x (2 * r), (strictBand Ω q V x r (s j)).indicator
        (fun z => ENNReal.ofReal (bumpDensity q (s j) z)) z := funext hFint
  rw [hfun]
  refine tendsto_lintegral_of_dominated_convergence' (fun _ => ENNReal.ofReal B) ?_ ?_ ?_ ?_
  · intro j
    have hg : AEMeasurable (fun z => ENNReal.ofReal (bumpDensity q (s j) z))
        (volume.restrict (closedBall x (2 * r))) :=
      (ENNReal.continuous_ofReal.comp_continuousOn ((hdz (s j)).mono hball)).aemeasurable
        measurableSet_closedBall
    exact hg.indicator (hTm _)
  · intro j
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with z hz
    have hle : ENNReal.ofReal (bumpDensity q (s j) z) ≤ ENNReal.ofReal B := by
      refine ENNReal.ofReal_le_ofReal ((le_abs_self _).trans ?_)
      have := hB ⟨s j, z⟩ ⟨⟨(hs0 j).le, hsr j⟩, hz⟩
      simpa only [Real.norm_eq_abs] using this
    by_cases hzT : z ∈ strictBand Ω q V x r (s j)
    · rw [indicator_of_mem hzT]
      exact hle
    · rw [indicator_of_notMem hzT]
      exact zero_le
  · rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_closedBall_lt_top.ne
  · filter_upwards [ae_restrict_mem measurableSet_closedBall] with z hz
    have hzΩ : z ∈ Ω := hball hz
    by_cases hzC : z ∈ C
    · have hzT : ∀ j, z ∈ strictBand Ω q V x r (s j) := by
        intro j
        refine ⟨⟨hzΩ, ?_⟩, closedBall_subset_closedBall (by linarith [hs0 j]) hzC.2⟩
        have : 0 < 4 * r ^ 2 * s j := by have := hs0 j; positivity
        linarith [hzC.1.2]
      simp only [indicator_of_mem (hzT _), indicator_of_mem hzC]
      rw [← bumpDensity_zero]
      exact (ENNReal.continuous_ofReal.tendsto _).comp (((continuous_bumpDensity_param q z).tendsto 0).comp hslim)
    · rw [indicator_of_notMem hzC]
      have hev : ∀ᶠ j in atTop, (strictBand Ω q V x r (s j)).indicator
          (fun z => ENNReal.ofReal (bumpDensity q (s j) z)) z = 0 := by
        by_cases hzr : z ∈ closedBall x r
        · have hne : V z ≠ q z := fun h => hzC ⟨⟨hzΩ, h⟩, hzr⟩
          have hlt : V z < q z := lt_of_le_of_ne (hVq z hzΩ) hne
          have h4 : 0 < 4 * r ^ 2 := by positivity
          have hd : 0 < (q z - V z) / (4 * r ^ 2) := div_pos (by linarith) h4
          filter_upwards [hslim.eventually (gt_mem_nhds hd)] with j hj
          have hnot : z ∉ strictBand Ω q V x r (s j) := by
            rintro ⟨⟨-, h⟩, -⟩
            have : 4 * r ^ 2 * s j < q z - V z := by
              have := (lt_div_iff₀ h4).mp hj
              linarith
            linarith
          rw [indicator_of_notMem hnot]
        · have hd' : r < ‖z - x‖ := by
            rw [mem_closedBall, dist_eq_norm, not_le] at hzr
            exact hzr
          have hd : 0 < ‖z - x‖ - r := by linarith
          filter_upwards [hslim.eventually (gt_mem_nhds hd)] with j hj
          have hnot : z ∉ strictBand Ω q V x r (s j) := by
            rintro ⟨-, h⟩
            rw [mem_closedBall, dist_eq_norm] at h
            linarith
          rw [indicator_of_notMem hnot]
      exact tendsto_const_nhds.congr' (hev.mono fun j hj => hj.symm)

/-- **The contact bound on closed balls.**  Let `V ≤ q` on `Ω`, with `V` locally bounded
plurisubharmonic and `q` smooth plurisubharmonic, and let `B̄(x, 2r) ⊆ Ω`.  On
`C ∩ B̄(x, r)`, `C = {V = q}`, the Bedford–Taylor measure of `V` is at most `(ddᶜq)ⁿ`. -/
theorem canonicalBedfordTaylorMeasure_contact_closedBall_le (hn : 0 < n)
    {Ω : Opens (ComplexModel n)} {V q : ComplexModel n → ℝ}
    (hV : IsLocallyBoundedPshOn Ω V) (hq : IsSmoothPshOn Ω q)
    (hVq : ∀ z ∈ Ω, V z ≤ q z) {x : ComplexModel n} {r : ℝ} (hr : 0 < r)
    (hball : closedBall x (2 * r) ⊆ Ω) :
    canonicalBedfordTaylorMeasure Ω V hV ({z | z ∈ Ω ∧ V z = q z} ∩ closedBall x r) ≤
      ∫⁻ z in {z | z ∈ Ω ∧ V z = q z} ∩ closedBall x r,
        ENNReal.ofReal (smoothDensity q z) := by
  refine ge_of_tendsto' (tendsto_lintegral_strictBand hV.1.upperSemicontinuousOn hq.1 hVq hr
    hball) fun j => ?_
  exact canonicalBedfordTaylorMeasure_contact_closedBall_le_band hn hV hq hVq hr hball
    (div_pos hr (by positivity)) (div_le_self hr.le (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]))

/-! ### Arbitrary subsets of the contact set: Besicovitch -/

/-- **The contact bound for bounded potentials.**  Under the hypotheses of the closed-ball bound,
for every subset `S` of `C ∩ B(x₀, R)` with `B̄(x₀, 2R) ⊆ Ω`,
`(ddᶜV)ⁿ(S) ≤ ∫_S (ddᶜq)ⁿ`. -/
theorem canonicalBedfordTaylorMeasure_contact_le (hn : 0 < n)
    {Ω : Opens (ComplexModel n)} {V q : ComplexModel n → ℝ}
    (hV : IsLocallyBoundedPshOn Ω V) (hq : IsSmoothPshOn Ω q)
    (hVq : ∀ z ∈ Ω, V z ≤ q z) {x₀ : ComplexModel n} {R : ℝ} (hR : 0 < R)
    (hball : closedBall x₀ (2 * R) ⊆ Ω) {S : Set (ComplexModel n)}
    (hS : S ⊆ {z | z ∈ Ω ∧ V z = q z} ∩ ball x₀ R) :
    canonicalBedfordTaylorMeasure Ω V hV S ≤ ∫⁻ z in S, ENNReal.ofReal (smoothDensity q z) := by
  set μ := canonicalBedfordTaylorMeasure Ω V hV with hμ
  set C : Set (ComplexModel n) := {z | z ∈ Ω ∧ V z = q z} with hC
  set A : Set (ComplexModel n) := C ∩ closedBall x₀ R with hA
  have hqc : ContinuousOn q Ω := hq.1.continuousOn
  have hVusc : UpperSemicontinuousOn (fun z => (V z : EReal)) Ω := hV.1.upperSemicontinuousOn
  have hAm : MeasurableSet A :=
    (measurableSet_eq_of_upperSemicontinuousOn hqc hVusc).inter measurableSet_closedBall
  have hR2 : closedBall x₀ R ⊆ Ω := (closedBall_subset_closedBall (by linarith)).trans hball
  have hμA : μ A ≠ ⊤ := ((measure_mono inter_subset_right).trans_lt
    (canonicalBedfordTaylorMeasure_finiteOnCompacts hV (isCompact_closedBall _ _) hR2)).ne
  set ρ := μ.restrict A with hρ
  have : IsFiniteMeasure ρ := isFiniteMeasure_restrict.mpr hμA
  obtain ⟨B, hB⟩ := (isCompact_closedBall x₀ R).exists_bound_of_continuousOn
    ((continuousOn_smoothDensity Ω.isOpen hq.1).mono hR2)
  set ν := (volume.restrict A).withDensity fun z => ENNReal.ofReal (smoothDensity q z) with hν
  have : IsFiniteMeasure ν := by
    refine ⟨?_⟩
    rw [hν, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    calc ∫⁻ z in A, ENNReal.ofReal (smoothDensity q z)
        ≤ ∫⁻ z in A, ENNReal.ofReal B := by
          refine setLIntegral_mono measurable_const fun z hz => ENNReal.ofReal_le_ofReal ?_
          have := hB z hz.2
          rw [Real.norm_eq_abs] at this
          exact (le_abs_self _).trans this
      _ < ⊤ := by
          rw [setLIntegral_const]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
            ((measure_mono inter_subset_right).trans_lt measure_closedBall_lt_top)
  have hSA : S ⊆ A := fun z hz => ⟨(hS hz).1, ball_subset_closedBall (hS hz).2⟩
  have key := (Besicovitch.vitaliFamily ρ).measure_le_of_frequently_le ν
    (Measure.AbsolutelyContinuous.refl ρ) S ?_
  · calc μ S = ρ S := by rw [hρ, Measure.restrict_apply' hAm, inter_eq_left.mpr hSA]
      _ ≤ ν S := key
      _ = ∫⁻ z in S, ENNReal.ofReal (smoothDensity q z) := by
          rw [hν, withDensity_apply', Measure.restrict_restrict' hAm, inter_eq_left.mpr hSA]
  · intro y hy
    rw [VitaliFamily.frequently_filterAt_iff]
    intro ε hε
    have hyR : dist y x₀ < R := (hS hy).2
    set r := min ε ((R - dist y x₀) / 2) with hr
    have hr0 : 0 < r := lt_min hε (by linarith)
    have hrε : r ≤ ε := min_le_left _ _
    have hrR : r ≤ (R - dist y x₀) / 2 := min_le_right _ _
    have hsub : closedBall y r ⊆ closedBall x₀ R :=
      closedBall_subset_closedBall' (by linarith)
    have hsub2 : closedBall y (2 * r) ⊆ Ω :=
      (closedBall_subset_closedBall' (by linarith)).trans hball
    have hset : closedBall y r ∩ A = C ∩ closedBall y r := by
      ext z
      constructor
      · rintro ⟨hz1, hz2, -⟩
        exact ⟨hz2, hz1⟩
      · rintro ⟨hz2, hz1⟩
        exact ⟨hz1, hz2, hsub hz1⟩
    refine ⟨closedBall y r, ⟨r, hr0, rfl⟩, closedBall_subset_closedBall hrε, ?_⟩
    rw [hρ, Measure.restrict_apply' hAm, hν, withDensity_apply _ measurableSet_closedBall,
      Measure.restrict_restrict measurableSet_closedBall, hset]
    exact canonicalBedfordTaylorMeasure_contact_closedBall_le hn hV hq hVq hr0 hsub2

/-! ### Unbounded potentials -/

/-- **The local contact bound.**  Let `U ≤ q` on `Ω`, with `U` plurisubharmonic (possibly with
poles) and `q` smooth plurisubharmonic, `n > 0`, and `B̄(x₀, 2R) ⊆ Ω`.  For every subset `S`
of `{U = q} ∩ B(x₀, R)`, the non-pluripolar Monge–Ampère measure of `U` satisfies
`⟨(ddᶜU)ⁿ⟩(S) ≤ ∫_S (ddᶜq)ⁿ`. -/
theorem truncationLimitMeasure_contact_le (hn : 0 < n)
    {Ω : Opens (ComplexModel n)} {U : ComplexModel n → EReal} (hU : PlurisubharmonicOn U Ω)
    {q : ComplexModel n → ℝ} (hq : IsSmoothPshOn Ω q) (hUq : ∀ z ∈ Ω, U z ≤ q z)
    {x₀ : ComplexModel n} {R : ℝ} (hR : 0 < R) (hball : closedBall x₀ (2 * R) ⊆ Ω)
    {S : Set (ComplexModel n)} (hS : S ⊆ {z | z ∈ Ω ∧ U z = q z} ∩ ball x₀ R) :
    truncationLimitMeasure Ω U hU S ≤ ∫⁻ z in S, ENNReal.ofReal (smoothDensity q z) := by
  obtain ⟨hq1, -, -⟩ := (SGPT.MongeAmpere.truncationLimitMeasure_smooth_sub_const hq).2 1
  let w : ComplexModel n → EReal := fun z => ((q z - 1 : ℝ) : EReal)
  have hw : PlurisubharmonicOn w Ω := hq1.2.1
  have hmax : PlurisubharmonicOn (fun z => max (U z) (w z)) Ω := hU.max hw
  let V : ComplexModel n → ℝ := fun z => (max (U z) (w z)).toReal
  have hVeq : EqOn (fun z => max (U z) (w z)) (fun z => (V z : EReal)) Ω := by
    intro z hz
    have hne_bot : max (U z) (w z) ≠ ⊥ :=
      ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (le_max_right _ _)
    have hne_top : max (U z) (w z) ≠ ⊤ := by
      refine ne_top_of_le_ne_top (EReal.coe_ne_top (q z)) (max_le (hUq z hz) ?_)
      exact EReal.coe_le_coe_iff.mpr (by linarith)
    exact (EReal.coe_toReal hne_top hne_bot).symm
  have hVpsh : PlurisubharmonicOn (fun z => (V z : EReal)) Ω :=
    plurisubharmonicOn_congr Ω.isOpen hmax hVeq
  have hVbounds : ∀ z ∈ Ω, q z - 1 ≤ V z ∧ V z ≤ q z := by
    intro z hz
    have h : max (U z) (w z) = (V z : EReal) := hVeq hz
    have h1 : ((q z - 1 : ℝ) : EReal) ≤ (V z : EReal) := by
      rw [← h]
      exact le_max_right _ _
    have h2 : (V z : EReal) ≤ (q z : EReal) := by
      rw [← h]
      exact max_le (hUq z hz) (EReal.coe_le_coe_iff.mpr (by linarith))
    exact ⟨EReal.coe_le_coe_iff.mp h1, EReal.coe_le_coe_iff.mp h2⟩
  have hVb : IsLocallyBoundedPshOn Ω V := by
    refine ⟨hVpsh, fun z hz => ?_⟩
    obtain ⟨O, hO, hOeq⟩ := (_root_.continuousOn_iff'.mp hq.1.continuousOn) (Metric.ball (q z) 1)
      Metric.isOpen_ball
    let W : Opens (ComplexModel n) := ⟨O ∩ Ω, hO.inter Ω.isOpen⟩
    have hzW : z ∈ W := by
      have : z ∈ q ⁻¹' Metric.ball (q z) 1 ∩ (Ω : Set (ComplexModel n)) :=
        ⟨Metric.mem_ball_self one_pos, hz⟩
      rw [hOeq] at this
      exact this
    refine ⟨W, hzW, fun y hy => hy.2, |q z| + 2, fun y hy => ?_⟩
    have hyq : y ∈ q ⁻¹' Metric.ball (q z) 1 ∩ (Ω : Set (ComplexModel n)) := by
      rw [hOeq]
      exact hy
    have hd : |q y - q z| < 1 := by
      have := hyq.1
      rwa [mem_preimage, Metric.mem_ball, Real.dist_eq] at this
    obtain ⟨hb1, hb2⟩ := hVbounds y hy.2
    have hd1 := (abs_lt.mp hd).1
    have hd2 := (abs_lt.mp hd).2
    exact abs_le.mpr ⟨by linarith [neg_abs_le (q z)], by linarith [le_abs_self (q z)]⟩
  have hVq : ∀ z ∈ Ω, V z ≤ q z := fun z hz => (hVbounds z hz).2
  have hSV : S ⊆ {z | z ∈ Ω ∧ V z = q z} ∩ ball x₀ R := by
    intro z hz
    obtain ⟨⟨hzΩ, hzU⟩, hzB⟩ := hS hz
    refine ⟨⟨hzΩ, ?_⟩, hzB⟩
    have h : max (U z) (w z) = (V z : EReal) := hVeq hzΩ
    have hmaxq : max (U z) (w z) = (q z : EReal) := by
      rw [hzU]
      exact max_eq_left (EReal.coe_le_coe_iff.mpr (by linarith))
    rw [hmaxq] at h
    exact (EReal.coe_eq_coe_iff.mp h).symm
  have hbound := canonicalBedfordTaylorMeasure_contact_le hn hVb hq hVq hR hball hSV
  -- identify the measures on the contact set
  set D : Set (ComplexModel n) := {z | z ∈ Ω ∧ ∀ _ : Fin n, w z < U z} with hD
  have hSD : S ⊆ D := by
    intro z hz
    obtain ⟨⟨hzΩ, hzU⟩, -⟩ := hS hz
    refine ⟨hzΩ, fun _ => ?_⟩
    rw [hzU]
    exact EReal.coe_lt_coe_iff.mpr (by linarith)
  have hloc := MixedNonPluripolar.mixedTruncationLimitMeasure_restrict_max_eq
    (u := fun _ : Fin n => U) (w := fun _ : Fin n => w) (fun _ => hU) (fun _ => hw)
    (fun _ => hmax)
  have hcongr := MixedNonPluripolar.mixedTruncationLimitMeasure_congr
    (u := fun _ : Fin n => fun z => max (U z) (w z)) (v := fun _ : Fin n => fun z => (V z : EReal))
    (fun _ => hmax) (fun _ => hVpsh) (fun _ => hVeq)
  calc truncationLimitMeasure Ω U hU S
      = MixedNonPluripolar.mixedTruncationLimitMeasure Ω (fun _ => U) (fun _ => hU) S := by
        rw [MixedNonPluripolar.mixedTruncationLimitMeasure_diagonal hn hU]
    _ = (MixedNonPluripolar.mixedTruncationLimitMeasure Ω (fun _ => U) (fun _ => hU)).restrict D S :=
        (Measure.restrict_eq_self _ hSD).symm
    _ = (MixedNonPluripolar.mixedTruncationLimitMeasure Ω
          (fun _ : Fin n => fun z => max (U z) (w z)) (fun _ => hmax)).restrict D S := by
        rw [← hloc]
    _ = MixedNonPluripolar.mixedTruncationLimitMeasure Ω
          (fun _ : Fin n => fun z => max (U z) (w z)) (fun _ => hmax) S :=
        Measure.restrict_eq_self _ hSD
    _ = truncationLimitMeasure Ω (fun z => (V z : EReal)) hVpsh S := by
        rw [hcongr, MixedNonPluripolar.mixedTruncationLimitMeasure_diagonal hn hVpsh]
    _ = canonicalBedfordTaylorMeasure Ω V hVb S := by
        rw [truncationLimitMeasure_eq_canonical hVb]
    _ ≤ ∫⁻ z in S, ENNReal.ofReal (smoothDensity q z) := hbound

/-! ### Positivity at contact points -/

/-- **Positivity at contact points** (local form).  If `U ≤ q` near `x`, `U` plurisubharmonic,
`q` smooth near `x` and `U x = q x`, then the Levi form of `q` at `x` is nonnegative. -/
theorem leviForm_nonneg_of_contact {W : Set (ComplexModel n)} (hW : IsOpen W)
    {U : ComplexModel n → EReal} (hU : PlurisubharmonicOn U W) {q : ComplexModel n → ℝ}
    (hq : ContDiffOn ℝ ∞ q W) {x : ComplexModel n} (hx : x ∈ W)
    (hle : ∀ᶠ z in 𝓝 x, U z ≤ q z) (heq : U x = q x) (v : ComplexModel n) :
    0 ≤ leviForm q x v := by
  obtain ⟨g, hg, hqg⟩ := exists_contDiff_eventuallyEq_of_contDiffOn hW hq hx
  have hgx : U x = g x := by rw [heq, hqg.eq_of_nhds]
  have hupper : ∀ᶠ z in 𝓝 x, U z ≤ g z := by
    filter_upwards [hle, hqg] with z hz hzg
    rwa [← hzg]
  have h := (SGPT.MongeAmpere.complexHessian_posSemidef_of_smooth_upper_test hU hx hg hgx
    hupper).2 v
  have hH : iteratedFDeriv ℝ 2 q x = iteratedFDeriv ℝ 2 g x :=
    (hqg.iteratedFDeriv ℝ 2).eq_of_nhds
  have hL : leviForm q x v = leviForm g x v := by
    simp only [leviForm, realHessian, hH]
  rw [hL]
  exact h

end SGPT.Okounkov.TranscendentalWN.EnvelopeLocal
