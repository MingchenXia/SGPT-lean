import SGPT.Envelopes.MADirichlet5Exhaustion

/-!
# Kołodziej approximants with a prescribed kernel radius, and convergence of the whole sequence

Xia, *Foundations of pluripotential theory* (FPT), `thm:bounded-multifactor-common-measure`,
Step 2 needs, for finitely many measures `α₁, …, αₙ` carried by the same compact `K`, the
approximants of all of them **on a common grid**. In the convolution variant of lanes
MA-DIR2–MA-DIR5 the grid is the kernel radius `r` of the convolutions `αᵢ ∗ ρⱼ`
(`ρⱼ = explicitRadialKernel r hr j`). MA-DIR3's `exists_convolution_approximants` chooses `r`
existentially; here it is prescribed, subject to `cthickening (4r) K ⊆ Q`:

* `exists_convolution_approximants_radius`: the approximants `Uⱼ ∈ ℰ₀(Q)` of MA-DIR3 for a given
  radius, with uniformly bounded energies;
* `exists_kolodziejApprox_radius`: they satisfy `IsKolodziejApprox` (MA-DIR4), and
  `(ddᶜUⱼ)ⁿ = (α ∗ ρⱼ + cₙ (j+1)⁻¹ χⁿ) dV` on `Q`.

FPT also uses that the **whole** sequence of approximants converges to the solution of
Kołodziej's theorem (`thm:compact-bounded-subsolution-ball-dirichlet`). MA-DIR4/MA-DIR5 obtained a
convergent subsequence; with the uniqueness of the bounded solution the whole sequence converges:

* `IsKolodziejApprox.comp`: subsequences of approximants are approximants;
* `exists_subseq_bounded_limit_of_isKolodziejApprox`: every sequence of approximants has a
  subsequence converging in `L¹_loc(Q)` to a bounded plurisubharmonic `u`, `-(M+1) ≤ u ≤ 0`, with
  boundary values `0` (the second half of MA-DIR4's `exists_approximants_bounded_limit`);
* `tendsto_localL1_of_isKolodziejApprox`: if `A ∈ ℰ₀(Q)` solves `(ddᶜA)ⁿ = α`, then `Uⱼ → A` in
  `L¹_loc(Q)` (every subsequence has a further subsequence converging to a bounded solution with
  boundary values `0`, which is `A` by `ma_eq_of_approximants` and `eq_of_ma_eq`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff

namespace SGPT.Envelopes.MADirichlet

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.MongeAmpere
open SGPT.Foundations.Analysis.Pending.BedfordTaylor SGPT.Foundations.Analysis.Pending.HolomorphicPullback
open SGPT.NPP.LogConcavityDinew

variable {n : ℕ}

/-- **Convolution approximants with a prescribed kernel radius** (MA-DIR3's
`exists_convolution_approximants` with `r` given, `cthickening (4r) K ⊆ Q`; FPT
`prop:canonical-grid-energy-control` (1), (3), (4) for `p = 1`, convolution variant). -/
theorem exists_convolution_approximants_radius (hn : 0 < n) (a : ComplexModel n) {R : ℝ}
    (hR : 0 < R) (α : Measure (ComplexModel n)) [IsFiniteMeasure α] {K : Set (ComplexModel n)}
    (hK : IsCompact K) (hαK : α Kᶜ = 0) {r : ℝ} (hr : 0 < r)
    (h4r : cthickening (4 * r) K ⊆ polydiskAt a R) {w : ComplexModel n → ℝ}
    (hw : IsLocallyBoundedPshOn (polydiskAtOpens a R) w) {b M : ℝ} (hM : 0 ≤ M)
    (hwb : ∀ z ∈ polydiskAt a R, b ≤ w z ∧ w z ≤ b + M)
    (hα : α.restrict (polydiskAt a R) ≤
      canonicalBedfordTaylorMeasure (polydiskAtOpens a R) w hw) :
    ∃ (χ : ComplexModel n → ℝ) (F U : ℕ → ComplexModel n → ℝ)
      (hU : ∀ j, IsCegrellE0 (polydiskAtOpens a R) (U j)) (C : ℝ),
      ContDiff ℝ ∞ χ ∧ (∀ z, 0 ≤ χ z ∧ χ z ≤ 1) ∧ HasCompactSupport χ ∧
      (∀ j, ContDiff ℝ ∞ (F j) ∧ (∀ z, 0 ≤ F j z) ∧ HasCompactSupport (F j) ∧
        tsupport (F j) ⊆ polydiskAt a R) ∧
      (∀ j z, mongeAmpereConst n * F j z ^ n =
        convDensity α r hr j z + mongeAmpereConst n * ((j : ℝ) + 1)⁻¹ * χ z ^ n) ∧
      (∀ j, canonicalBedfordTaylorMeasure (polydiskAtOpens a R) (U j) (hU j).psh =
        (volume.restrict (polydiskAt a R)).withDensity
          (fun z => ENNReal.ofReal (mongeAmpereConst n * F j z ^ n))) ∧
      (∀ h : ComplexModel n → ℝ, Continuous h → HasCompactSupport h →
        Tendsto (fun j => ∫ z, h z ∂canonicalBedfordTaylorMeasure (polydiskAtOpens a R) (U j)
          (hU j).psh) atTop (𝓝 (∫ z, h z ∂α))) ∧
      ∀ j, (localEnergy (polydiskAtOpens a R) 1 (U j) (hU j).psh).toReal ≤ C := by
  classical
  set Q : Opens (ComplexModel n) := polydiskAtOpens a R with hQdef
  have hQQ : (Q : Set (ComplexModel n)) = (polydiskAt a R) := rfl
  have hQm : MeasurableSet (polydiskAt a R) := (isOpen_polydiskAt a R).measurableSet
  have hQb : Bornology.IsBounded (polydiskAt a R) := isBounded_polydiskAt a hR
  have h2r : cthickening (2 * r) K ⊆ polydiskAt a R :=
    (cthickening_mono (by linarith) K).trans h4r
  obtain ⟨χ, hχs, hχ01, hχ1, hχc, hχsupp⟩ := exists_smooth_cutoff hK hr
  set c := mongeAmpereConst n with hcdef
  have hc : 0 < c := mongeAmpereConst_pos
  set g : ℕ → ComplexModel n → ℝ := fun j => convDensity α r hr j with hgdef
  set ε : ℕ → ℝ := fun j => ((j : ℝ) + 1)⁻¹ with hεdef
  have hε : ∀ j, 0 < ε j := fun j => by positivity
  have hε1 : ∀ j, ε j ≤ 1 := fun j => inv_le_one_of_one_le₀ (by linarith [j.cast_nonneg (α := ℝ)])
  set F : ℕ → ComplexModel n → ℝ := fun j => rootDensity (g j) χ c (ε j) n with hFdef
  have hnn : ∀ j x, 0 ≤ g j x / c + ε j * χ x ^ n := fun j x =>
    add_nonneg (div_nonneg (convDensity_nonneg α hr j x) hc.le)
      (mul_nonneg (hε j).le (pow_nonneg (hχ01 x).1 n))
  have hgL : ∀ j, Function.support (g j) ⊆ cthickening r K :=
    fun j => support_convDensity_subset α hαK hr j
  have hχL : EqOn χ 1 (cthickening r K) := hχ1.mono (cthickening_mono (by linarith) K)
  have hFs : ∀ j, ContDiff ℝ ∞ (F j) := fun j =>
    contDiff_rootDensity (contDiff_convDensity α hr j) hχs (convDensity_nonneg α hr j)
      (fun x => (hχ01 x).1) isClosed_cthickening (hgL j) hχL hc (hε j) hn.ne'
  have hF0 : ∀ j x, 0 ≤ F j x := fun j x => rootDensity_nonneg _ _ _ _ _ x (hnn j x)
  have hFsupp : ∀ j, Function.support (F j) ⊆ Function.support χ := by
    intro j x hx
    by_contra hχx
    rw [Function.notMem_support] at hχx
    have hxL : x ∉ cthickening r K := fun h => by
      have := hχL h
      rw [hχx] at this
      exact zero_ne_one this
    have hgx : g j x = 0 := convDensity_eq_zero_of_notMem α hαK hr j hxL
    apply hx
    simp only [hFdef, rootDensity, hgx, hχx, zero_div, zero_add, ne_eq, hn.ne', not_false_eq_true,
      zero_pow, mul_zero]
    exact Real.zero_rpow (inv_ne_zero (Nat.cast_ne_zero.mpr hn.ne'))
  have hFc : ∀ j, HasCompactSupport (F j) := fun j =>
    hχc.mono' ((hFsupp j).trans (subset_tsupport χ))
  have hFtsupp : ∀ j, tsupport (F j) ⊆ polydiskAt a R := fun j =>
    (closure_mono (hFsupp j)).trans (hχsupp.trans ((cthickening_mono (by linarith) K).trans h4r))
  have hFpow : ∀ j x, c * F j x ^ n = g j x + c * ε j * χ x ^ n := by
    intro j x
    rw [hFdef, rootDensity_pow hn.ne' (hnn j x)]
    field_simp
  -- the Dirichlet problems
  have hsol := fun j => polydiskAt_dirichlet_C2 hn a hR
    ((hFs j).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) (hF0 j) (hFc j) (hFtsupp j)
  choose U hUpsh hUma hUbd hUle _ using hsol
  have hUE0 : ∀ j, IsCegrellE0 Q (U j) := by
    intro j
    refine ⟨hUpsh j, exists_lower_bound_of_tendsto_frontier hQb (hUpsh j) (hUbd j), hUle j,
      hUbd j, ?_⟩
    obtain ⟨B, hB⟩ := (hFs j).continuous.bounded_above_of_compact_support (hFc j)
    change canonicalBedfordTaylorMeasure Q (U j) (hUpsh j) (polydiskAt a R) < ⊤
    rw [hUma j, withDensity_apply _ hQm]
    refine lt_of_le_of_lt (setLIntegral_mono (g := fun _ => ENNReal.ofReal (c * B ^ n))
      measurable_const fun z _ => ?_) ?_
    · refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hc.le)
      have := hB z
      rw [Real.norm_eq_abs, abs_of_nonneg (hF0 j z)] at this
      exact pow_le_pow_left₀ (hF0 j z) this n
    · rw [setLIntegral_const]
      refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
      rw [Measure.restrict_apply' hQm, inter_self]
      exact hQb.measure_lt_top
  -- the dominating measure and the dominating potential
  set μ : Measure (ComplexModel n) := α + ENNReal.ofReal c • volume.restrict (polydiskAt a R) with hμdef
  set W : ComplexModel n → ℝ := fun z => w z + 1 * (‖z‖ ^ 2 - 0) with hWdef
  have hW : IsLocallyBoundedPshOn Q W := by
    have := isLocallyBoundedPshOn_linComb hw hw (Ω := Q) (a := 1) (b := 0) (c := 1) zero_le_one
      le_rfl zero_le_one
    convert this using 1
    funext z
    simp [hWdef]
  set ρ := ‖a‖ + R * (n + 1) with hρdef
  have hWb : ∀ z ∈ Q, b ≤ W z ∧ W z ≤ b + (M + ρ ^ 2) := by
    intro z hz
    have h1 := hwb z hz
    have h2 : ‖z‖ ≤ ρ := norm_le_of_mem_polydiskAt hR hz
    have h3 : ‖z‖ ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ (norm_nonneg z) h2 2
    have h4 : 0 ≤ ‖z‖ ^ 2 := sq_nonneg _
    simp only [hWdef]
    constructor <;> nlinarith
  have hMW : 0 ≤ M + ρ ^ 2 := by positivity
  have hμW : μ.restrict Q ≤ canonicalBedfordTaylorMeasure Q W hW := by
    have hsum := ma_add_normSq_ge hn hw one_pos 0 hW
    rw [one_pow, mul_one] at hsum
    refine le_trans (le_of_eq ?_) (le_trans (add_le_add hα le_rfl) hsum)
    rw [hμdef, Measure.restrict_add, Measure.restrict_smul, hQQ, Measure.restrict_restrict hQm,
      inter_self]
  have hμfin : μ Q ≠ ⊤ := by
    rw [hμdef, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply' hQm]
    refine ENNReal.add_ne_top.mpr ⟨measure_ne_top α _, ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_⟩
    rw [hQQ, inter_self]
    exact hQb.measure_lt_top.ne
  -- the energy comparison
  have hctrl : ∀ j, localEnergy Q 1 (U j) (hUE0 j).psh ≤
      ENNReal.ofReal 1 * ∫⁻ z in (Q : Set (ComplexModel n)), ENNReal.ofReal ((-U j z) ^ (1 : ℝ)) ∂μ := by
    intro j
    set Ũ : ComplexModel n → ℝ := (polydiskAt a R).indicator (U j) with hŨdef
    have hŨm : Measurable Ũ := measurable_indicator_of_plurisubharmonicOn (hUpsh j).1
    have hdm : Measurable fun z => ENNReal.ofReal (c * F j z ^ n) :=
      ENNReal.measurable_ofReal.comp (measurable_const.mul ((hFs j).continuous.measurable.pow_const n))
    rw [ENNReal.ofReal_one, one_mul]
    unfold localEnergy
    rw [hUma j, hQQ, restrict_withDensity hQm, Measure.restrict_restrict hQm, inter_self,
      lintegral_withDensity_eq_lintegral_mul_non_measurable _ hdm
        (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simp only [Real.rpow_one, Pi.mul_apply]
    have e1 : ∫⁻ z in polydiskAt a R, ENNReal.ofReal (c * F j z ^ n) * ENNReal.ofReal (-U j z) =
        ∫⁻ z in polydiskAt a R, ENNReal.ofReal (g j z) * ENNReal.ofReal (-Ũ z) +
          ENNReal.ofReal (c * ε j * χ z ^ n) * ENNReal.ofReal (-Ũ z) := by
      refine setLIntegral_congr_fun hQm fun z hz => ?_
      simp only [hŨdef, indicator_of_mem hz]
      rw [hFpow, ENNReal.ofReal_add (convDensity_nonneg α hr j z)
        (by have := (hχ01 z).1; have := hε j; positivity), add_mul]
    have e2 : ∫⁻ z in polydiskAt a R, ENNReal.ofReal (-U j z) ∂μ =
        ∫⁻ z in polydiskAt a R, ENNReal.ofReal (-U j z) ∂α +
          ENNReal.ofReal c * ∫⁻ z in polydiskAt a R, ENNReal.ofReal (-Ũ z) := by
      rw [hμdef, Measure.restrict_add, lintegral_add_measure, Measure.restrict_smul,
        lintegral_smul_measure, Measure.restrict_restrict hQm, inter_self, smul_eq_mul]
      congr 2
      refine setLIntegral_congr_fun hQm fun z hz => ?_
      simp only [hŨdef, indicator_of_mem hz]
    have hm2 : Measurable fun z => ENNReal.ofReal (c * ε j * χ z ^ n) * ENNReal.ofReal (-Ũ z) :=
      (ENNReal.measurable_ofReal.comp (measurable_const.mul
        ((hχs.continuous.measurable).pow_const n))).mul (ENNReal.measurable_ofReal.comp hŨm.neg)
    rw [e1, e2, lintegral_add_right _ hm2]
    refine add_le_add ?_ ?_
    · have := lintegral_convDensity_mul_le (Ω := Q) α hαK hr h2r (hUpsh j) (hUle j) j
      refine le_trans (le_of_eq ?_) this
      refine setLIntegral_congr_fun hQm fun z hz => ?_
      simp only [hgdef, hŨdef, indicator_of_mem hz]
    · rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine setLIntegral_mono' hQm fun z hz => ?_
      gcongr
      have h1 := (hχ01 z).1
      have h2 : χ z ^ n ≤ 1 := pow_le_one₀ h1 (hχ01 z).2
      calc c * ε j * χ z ^ n ≤ c * 1 * 1 := by
            gcongr
            exact hε1 j
        _ = c := by ring
  -- weak convergence of the Monge–Ampère measures to `α`
  have hweak : ∀ h : ComplexModel n → ℝ, Continuous h → HasCompactSupport h →
      Tendsto (fun j => ∫ z, h z ∂canonicalBedfordTaylorMeasure Q (U j) (hUE0 j).psh) atTop
        (𝓝 (∫ z, h z ∂α)) := by
    intro h hhc hhs
    have hrep : ∀ j, ∫ z, h z ∂canonicalBedfordTaylorMeasure Q (U j) (hUE0 j).psh =
        (∫ z, h z * g j z) + c * ε j * ∫ z in polydiskAt a R, χ z ^ n * h z := by
      intro j
      have hdm : Measurable fun z => ENNReal.ofReal (c * F j z ^ n) :=
        ENNReal.measurable_ofReal.comp
          (measurable_const.mul ((hFs j).continuous.measurable.pow_const n))
      change ∫ z, h z ∂canonicalBedfordTaylorMeasure Q (U j) (hUpsh j) = _
      rw [hUma j, integral_withDensity_eq_integral_toReal_smul hdm
        (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
      have e : ∀ z, (ENNReal.ofReal (c * F j z ^ n)).toReal • h z =
          h z * g j z + c * ε j * (χ z ^ n * h z) := fun z => by
        rw [ENNReal.toReal_ofReal (mul_nonneg hc.le (pow_nonneg (hF0 j z) n)), smul_eq_mul,
          hFpow]
        ring
      simp_rw [e]
      have hi1 : Integrable fun z => h z * g j z :=
        (hhc.mul (contDiff_convDensity α hr j).continuous).integrable_of_hasCompactSupport
          hhs.mul_right
      have hi2 : Integrable fun z => χ z ^ n * h z :=
        ((hχs.continuous.pow n).mul hhc).integrable_of_hasCompactSupport hhs.mul_left
      rw [integral_add hi1.integrableOn (hi2.integrableOn.const_mul _), integral_const_mul]
      congr 1
      refine setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => ?_
      have hzL : z ∉ cthickening r K := fun h' =>
        hz (h2r (cthickening_mono (by linarith) K h'))
      rw [show g j z = 0 from convDensity_eq_zero_of_notMem α hαK hr j hzL, mul_zero]
    simp_rw [hrep]
    have hε0 : Tendsto ε atTop (𝓝 0) := by
      have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      simpa only [hεdef, one_div] using this
    have h2 : Tendsto (fun j => c * ε j * ∫ z in polydiskAt a R, χ z ^ n * h z) atTop (𝓝 0) := by
      have := (tendsto_const_nhds (x := c)).mul hε0 |>.mul
        (tendsto_const_nhds (x := ∫ z in polydiskAt a R, χ z ^ n * h z))
      simpa only [mul_zero, zero_mul] using this
    simpa only [add_zero] using (tendsto_integral_mul_convDensity α hr hhc hhs).add h2
  refine ⟨χ, F, U, hUE0, (1 * energyMomentConst n 1 (μ Q).toReal (M + ρ ^ 2)) ^
    (((n : ℝ) + 1) / n), hχs, hχ01, hχc, fun j => ⟨hFs j, hF0 j, hFc j, hFtsupp j⟩,
    fun j z => by rw [hFpow], fun j => hUma j, hweak, fun j => ?_⟩
  exact localEnergy_le_of_moment_control hn hQb (hUE0 j) hW hMW hWb hμW hμfin one_pos
    zero_le_one (hctrl j)

/-- **The approximants with a prescribed radius are Kołodziej approximants** (the first half of
MA-DIR4's `exists_approximants_bounded_limit`, with `r` prescribed): they satisfy
`IsKolodziejApprox` and `(ddᶜUⱼ)ⁿ = (α ∗ ρⱼ + cₙ (j+1)⁻¹ χⁿ) dV` on `Q`. -/
theorem exists_kolodziejApprox_radius (hn : 0 < n) (a : ComplexModel n) {R : ℝ} (hR : 0 < R)
    (α : Measure (ComplexModel n)) [IsFiniteMeasure α] {K : Set (ComplexModel n)}
    (hK : IsCompact K) (hαK : α Kᶜ = 0) {r : ℝ} (hr : 0 < r)
    (h4r : cthickening (4 * r) K ⊆ polydiskAt a R) {w : ComplexModel n → ℝ}
    (hw : IsLocallyBoundedPshOn (polydiskAtOpens a R) w) {b M : ℝ} (hM : 0 ≤ M)
    (hwb : ∀ z ∈ polydiskAt a R, b ≤ w z ∧ w z ≤ b + M)
    (hα : α.restrict (polydiskAt a R) ≤
      canonicalBedfordTaylorMeasure (polydiskAtOpens a R) w hw) :
    ∃ (χ : ComplexModel n → ℝ) (U : ℕ → ComplexModel n → ℝ)
      (hA : IsKolodziejApprox (polydiskAtOpens a R) α U),
      Continuous χ ∧ (∀ z, 0 ≤ χ z ∧ χ z ≤ 1) ∧
      ∀ j, canonicalBedfordTaylorMeasure (polydiskAtOpens a R) (U j) (hA.cegrell j).psh =
        (volume.restrict (polydiskAt a R)).withDensity
          (fun z => ENNReal.ofReal (convDensity α r hr j z +
            mongeAmpereConst n * ((j : ℝ) + 1)⁻¹ * χ z ^ n)) := by
  classical
  obtain ⟨χ, F, U, hU, C, hχs, hχ01, hχc, hF, hFeq, hMA, hweak, hC⟩ :=
    exists_convolution_approximants_radius hn a hR α hK hαK hr h4r hw hM hwb hα
  have h2r : cthickening (2 * r) K ⊆ polydiskAt a R :=
    (cthickening_mono (by linarith) K).trans h4r
  set Q : Opens (ComplexModel n) := polydiskAtOpens a R with hQdef
  have hQb : Bornology.IsBounded (Q : Set (ComplexModel n)) := isBounded_polydiskAt a hR
  have hQm : MeasurableSet (Q : Set (ComplexModel n)) := Q.isOpen.measurableSet
  have hcn : 0 < mongeAmpereConst n := mongeAmpereConst_pos
  have hdens : ∀ j z, mongeAmpereConst n * F j z ^ n =
      convDensity α r hr j z + mongeAmpereConst n * ((j : ℝ) + 1)⁻¹ * χ z ^ n := hFeq
  -- the measures are carried by a fixed compact set
  have hχF : tsupport χ ⊆ polydiskAt a R := by
    refine (closure_minimal (fun x hx => ?_) (isClosed_tsupport _)).trans (hF 0).2.2.2
    refine subset_tsupport _ fun h0 => hx ?_
    have h1 := hdens 0 x
    rw [h0, zero_pow hn.ne', mul_zero] at h1
    have h2 : 0 ≤ convDensity α r hr 0 x := convDensity_nonneg α hr 0 x
    have h3 : 0 ≤ mongeAmpereConst n * ((0 : ℕ) + 1 : ℝ)⁻¹ * χ x ^ n :=
      mul_nonneg (by positivity) (pow_nonneg (hχ01 x).1 n)
    have h4 : χ x ^ n = 0 := by
      have : mongeAmpereConst n * ((0 : ℕ) + 1 : ℝ)⁻¹ * χ x ^ n = 0 := by linarith
      simpa [hcn.ne'] using this
    exact pow_eq_zero_iff hn.ne' |>.mp h4
  set K₀ : Set (ComplexModel n) := tsupport χ ∪ cthickening r K with hK₀def
  have hK₀ : IsCompact K₀ := hχc.union hK.cthickening
  have hK₀Q : K₀ ⊆ Q := union_subset hχF
    ((cthickening_mono (by linarith) K).trans h2r)
  have hzero : ∀ j, ∀ x ∉ K₀,
      convDensity α r hr j x + mongeAmpereConst n * ((j : ℝ) + 1)⁻¹ * χ x ^ n = 0 := by
    intro j x hx
    rw [convDensity_eq_zero_of_notMem α hαK hr j (fun h => hx (Or.inr h)),
      image_eq_zero_of_notMem_tsupport (fun h => hx (Or.inl h)), zero_pow hn.ne']
    ring
  have hMA' : ∀ j, canonicalBedfordTaylorMeasure Q (U j) (hU j).psh =
      (volume.restrict (polydiskAt a R)).withDensity
        (fun z => ENNReal.ofReal (convDensity α r hr j z +
          mongeAmpereConst n * ((j : ℝ) + 1)⁻¹ * χ z ^ n)) := by
    intro j
    rw [hMA j]
    congr 1
    funext z
    rw [hdens j z]
  have hcarried : ∀ j, canonicalBedfordTaylorMeasure Q (U j) (hU j).psh K₀ᶜ = 0 := by
    intro j
    rw [hMA' j, withDensity_apply _ (hK₀.isClosed.isOpen_compl.measurableSet)]
    refine le_antisymm ((setLIntegral_mono' hK₀.isClosed.isOpen_compl.measurableSet
      (g := fun _ => 0) fun x hx => by rw [hzero j x hx, ENNReal.ofReal_zero]).trans ?_) bot_le
    simp
  -- the self-integral convergence
  have hself : ∀ T : ℝ, 0 < T → ∀ σ : ℕ → ℕ, StrictMono σ → ∀ b : ComplexModel n → ℝ,
      IsLocallyBoundedPshOn Q b →
      (∀ L : Set (ComplexModel n), IsCompact L → L ⊆ Q →
        Tendsto (fun k => ∫⁻ x in L, ENNReal.ofReal |max (U (σ k) x) (-T) - b x|) atTop (𝓝 0)) →
      Tendsto (fun k => ∫⁻ x, ENNReal.ofReal |max (U (σ k) x) (-T) - b x|
        ∂canonicalBedfordTaylorMeasure Q (U (σ k)) (hU (σ k)).psh) atTop (𝓝 0) := by
    intro T hT σ hσ b hb hlimb
    set f : ℕ → ComplexModel n → ℝ := fun k x => max (U (σ k) x) (-T) with hfdef
    have hconst : IsLocallyBoundedPshOn Q fun _ => (-T : ℝ) := by
      simpa using IsLocallyBoundedPshOn.add_const (isLocallyBoundedPshOn_zero Q) (-T)
    have hf : ∀ k, IsLocallyBoundedPshOn Q (f k) := fun k =>
      IsLocallyBoundedPshOn.max (hU (σ k)).psh hconst
    have hfT : ∀ k, ∀ z ∈ Q, |f k z| ≤ T := fun k z hz =>
      abs_le.mpr ⟨le_max_right _ _, max_le (((hU (σ k)).nonpos z hz).trans hT.le) (by linarith)⟩
    have hbT := abs_le_of_localL1 hf hb hfT hlimb
    have hconv := tendsto_lintegral_convDensity_abs_sub α hαK hr h2r hw hM hwb hα hf hb hfT hlimb
      hσ.tendsto_atTop
    set err : ℕ → ℝ≥0∞ := fun k => ENNReal.ofReal (mongeAmpereConst n * ((σ k : ℝ) + 1)⁻¹ * (2 * T)) *
      volume (Q : Set (ComplexModel n)) with herrdef
    have herr : Tendsto err atTop (𝓝 0) := by
      have h1 : Tendsto (fun k => mongeAmpereConst n * ((σ k : ℝ) + 1)⁻¹ * (2 * T)) atTop (𝓝 0) := by
        have h0 : Tendsto (fun k => ((σ k : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
          tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1
            (tendsto_natCast_atTop_atTop.comp hσ.tendsto_atTop))
        simpa using (h0.const_mul (mongeAmpereConst n)).mul_const (2 * T)
      have h2 := ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal h1)
        (Or.inr (hQb.measure_lt_top (μ := volume)).ne)
      simpa [ENNReal.ofReal_zero] using h2
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using hconv.add herr) (fun _ => bot_le) fun k => ?_
    have hmd : Measurable fun z => ENNReal.ofReal (convDensity α r hr (σ k) z +
        mongeAmpereConst n * ((σ k : ℝ) + 1)⁻¹ * χ z ^ n) :=
      ENNReal.measurable_ofReal.comp (((contDiff_convDensity α hr (σ k)).continuous.add
        (continuous_const.mul ((hχs.continuous).pow n))).measurable)
    rw [hMA' (σ k), lintegral_withDensity_eq_lintegral_mul_non_measurable
      (volume.restrict (polydiskAt a R)) hmd (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    have hmeas : AEMeasurable (fun x => ENNReal.ofReal (convDensity α r hr (σ k) x) *
        ENNReal.ofReal |f k x - b x|) (volume.restrict (polydiskAt a R)) :=
      (ENNReal.measurable_ofReal.comp (contDiff_convDensity α hr (σ k)).continuous.measurable
        |>.aemeasurable).mul (continuous_abs.measurable.comp_aemeasurable
          ((aemeasurable_of_isLocallyBoundedPshOn (hf k) volume).sub
            (aemeasurable_of_isLocallyBoundedPshOn hb volume))).ennreal_ofReal
    calc ∫⁻ x, ((fun z => ENNReal.ofReal (convDensity α r hr (σ k) z +
            mongeAmpereConst n * ((σ k : ℝ) + 1)⁻¹ * χ z ^ n)) *
            fun x => ENNReal.ofReal |max (U (σ k) x) (-T) - b x|) x
            ∂volume.restrict (polydiskAt a R)
        = ∫⁻ x in polydiskAt a R, (ENNReal.ofReal (convDensity α r hr (σ k) x) *
            ENNReal.ofReal |f k x - b x| + ENNReal.ofReal (mongeAmpereConst n *
              ((σ k : ℝ) + 1)⁻¹ * χ x ^ n) * ENNReal.ofReal |f k x - b x|) := by
          refine lintegral_congr fun x => ?_
          simp only [Pi.mul_apply, hfdef]
          rw [ENNReal.ofReal_add (convDensity_nonneg α hr _ x)
            (mul_nonneg (by positivity) (pow_nonneg (hχ01 x).1 n)), add_mul]
      _ = (∫⁻ x in polydiskAt a R, ENNReal.ofReal (convDensity α r hr (σ k) x) *
            ENNReal.ofReal |f k x - b x|) +
          ∫⁻ x in polydiskAt a R, ENNReal.ofReal (mongeAmpereConst n *
              ((σ k : ℝ) + 1)⁻¹ * χ x ^ n) * ENNReal.ofReal |f k x - b x| :=
          lintegral_add_left' hmeas _
      _ ≤ (∫⁻ x in (Q : Set (ComplexModel n)), ENNReal.ofReal (convDensity α r hr (σ k) x) *
            ENNReal.ofReal |f k x - b x|) + err k := by
          rw [herrdef]
          refine add_le_add le_rfl ?_
          calc ∫⁻ x in polydiskAt a R, ENNReal.ofReal (mongeAmpereConst n *
                ((σ k : ℝ) + 1)⁻¹ * χ x ^ n) * ENNReal.ofReal |f k x - b x|
              ≤ ∫⁻ x in polydiskAt a R,
                  ENNReal.ofReal (mongeAmpereConst n * ((σ k : ℝ) + 1)⁻¹ * (2 * T)) := by
                refine setLIntegral_mono' hQm fun x hx => ?_
                rw [← ENNReal.ofReal_mul (mul_nonneg (by positivity) (pow_nonneg (hχ01 x).1 n))]
                refine ENNReal.ofReal_le_ofReal ?_
                have h1 : χ x ^ n ≤ 1 := pow_le_one₀ (hχ01 x).1 (hχ01 x).2
                have h2 : |f k x - b x| ≤ 2 * T := by
                  calc |f k x - b x| ≤ |f k x| + |b x| := abs_sub _ _
                    _ ≤ T + T := add_le_add (hfT k x hx) (hbT x hx)
                    _ = 2 * T := by ring
                have h3 : 0 ≤ mongeAmpereConst n * ((σ k : ℝ) + 1)⁻¹ := by positivity
                calc mongeAmpereConst n * ((σ k : ℝ) + 1)⁻¹ * χ x ^ n * |f k x - b x|
                    ≤ mongeAmpereConst n * ((σ k : ℝ) + 1)⁻¹ * 1 * (2 * T) := by
                      gcongr
                  _ = _ := by ring
            _ = ENNReal.ofReal (mongeAmpereConst n * ((σ k : ℝ) + 1)⁻¹ * (2 * T)) *
                volume (polydiskAt a R) := setLIntegral_const _ _
  have hA : IsKolodziejApprox Q α U :=
    { bounded := hQb
      cegrell := hU
      carrier := ⟨K₀, hK₀, hK₀Q, hcarried⟩
      weak := hweak
      energy := ⟨C, hC⟩
      selfIntegral := hself }
  exact ⟨χ, U, hA, hχs.continuous, hχ01, hMA'⟩

/-- Subsequences of Kołodziej approximants are Kołodziej approximants. -/
theorem IsKolodziejApprox.comp {Q : Opens (ComplexModel n)} {α : Measure (ComplexModel n)}
    {U : ℕ → ComplexModel n → ℝ} (hA : IsKolodziejApprox Q α U) {τ : ℕ → ℕ}
    (hτ : StrictMono τ) : IsKolodziejApprox Q α fun j => U (τ j) where
  bounded := hA.bounded
  cegrell j := hA.cegrell (τ j)
  carrier := by
    obtain ⟨K₀, hK₀, hK₀Q, h⟩ := hA.carrier
    exact ⟨K₀, hK₀, hK₀Q, fun j => h (τ j)⟩
  weak h hc hcs := (hA.weak h hc hcs).comp hτ.tendsto_atTop
  energy := by
    obtain ⟨C, hC⟩ := hA.energy
    exact ⟨C, fun j => hC (τ j)⟩
  selfIntegral T hT σ hσ b hb hlim := hA.selfIntegral T hT (τ ∘ σ) (hτ.comp hσ) b hb hlim

/-- **A subsequence of Kołodziej approximants has a bounded limit with boundary values `0`** (the
second half of MA-DIR4's `exists_approximants_bounded_limit`, for an arbitrary sequence of
approximants on a polydisk): the energy bound gives `L¹(Q)` bounds, a subsequence converges in
`L¹_loc(Q)` (`exists_subseq_tendsto_localL1`), and its limit lies above the barrier
(`coe_le_of_approximants`). -/
theorem exists_subseq_bounded_limit_of_isKolodziejApprox (hn : 0 < n) (a : ComplexModel n)
    {R : ℝ} (hR : 0 < R) {α : Measure (ComplexModel n)} [IsFiniteMeasure α]
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKQ : K ⊆ polydiskAt a R) (hαK : α Kᶜ = 0)
    {w : ComplexModel n → ℝ} (hw : IsLocallyBoundedPshOn (polydiskAtOpens a R) w) {b M : ℝ}
    (hM : 0 ≤ M) (hwb : ∀ z ∈ polydiskAt a R, b ≤ w z ∧ w z ≤ b + M)
    (hα : α.restrict (polydiskAt a R) ≤
      canonicalBedfordTaylorMeasure (polydiskAtOpens a R) w hw)
    {U : ℕ → ComplexModel n → ℝ} (hA : IsKolodziejApprox (polydiskAtOpens a R) α U) :
    ∃ (σ : ℕ → ℕ) (u : ComplexModel n → ℝ), StrictMono σ ∧
      IsLocallyBoundedPshOn (polydiskAtOpens a R) u ∧
      (∀ z ∈ polydiskAt a R, -(M + 1) ≤ u z ∧ u z ≤ 0) ∧
      (∀ ζ ∈ frontier (polydiskAt a R), Tendsto u (𝓝[polydiskAt a R] ζ) (𝓝 0)) ∧
      ∀ L : Set (ComplexModel n), IsCompact L → L ⊆ polydiskAt a R →
        Tendsto (fun k => ∫⁻ x in L, ENNReal.ofReal |U (σ k) x - u x|) atTop (𝓝 0) := by
  classical
  set Q : Opens (ComplexModel n) := polydiskAtOpens a R with hQdef
  have hQb : Bornology.IsBounded (Q : Set (ComplexModel n)) := isBounded_polydiskAt a hR
  have hcn : 0 < mongeAmpereConst n := mongeAmpereConst_pos
  have hU := hA.cegrell
  obtain ⟨C, hC⟩ := hA.energy
  -- `L¹` bounds and a convergent subsequence
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ∀ z ∈ Q, ‖z‖ ≤ ρ :=
    ⟨‖a‖ + R * (n + 1), fun z hz => norm_le_of_mem_polydiskAt hR hz⟩
  set Bd : ℝ := energyMomentConst n 1
    ((ENNReal.ofReal (mongeAmpereConst n) • volume) (Q : Set (ComplexModel n))).toReal (ρ ^ 2) *
      C ^ (1 / ((n : ℝ) + 1)) / mongeAmpereConst n with hBddef
  have hL1 : ∀ j, ∫⁻ x in (Q : Set (ComplexModel n)), ENNReal.ofReal (-U j x) ≤ ENNReal.ofReal Bd :=
    fun j => lintegral_neg_le_of_localEnergy hn hQb hρ (hU j) (hC j)
  have hbound : ∀ L : Set (ComplexModel n), IsCompact L → L ⊆ Q →
      ∃ Bnd : ℝ, ∀ j, ∫ x in L, |((U j x : ℝ) : EReal).toReal| ≤ Bnd := by
    intro L hL hLQ
    refine ⟨Bd, fun j => ?_⟩
    simp only [EReal.toReal_coe]
    have hm : AEStronglyMeasurable (fun x => |U j x|) (volume.restrict L) :=
      ((continuous_abs.measurable.comp_aemeasurable
        (aemeasurable_of_isLocallyBoundedPshOn (hU j).psh volume)).mono_measure
          (Measure.restrict_mono hLQ le_rfl)).aestronglyMeasurable
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => abs_nonneg _) hm]
    have hC0 : 0 ≤ C := ENNReal.toReal_nonneg.trans (hC 0)
    refine ENNReal.toReal_le_of_le_ofReal (div_nonneg (mul_nonneg (energyMomentConst_nonneg n
      zero_le_one ENNReal.toReal_nonneg (sq_nonneg ρ)) (Real.rpow_nonneg hC0 _)) hcn.le) ?_
    calc ∫⁻ x in L, ENNReal.ofReal |U j x| ≤ ∫⁻ x in L, ENNReal.ofReal (-U j x) :=
          setLIntegral_mono' hL.measurableSet fun x hx => by
            rw [abs_of_nonpos ((hU j).nonpos x (hLQ hx))]
      _ ≤ ∫⁻ x in (Q : Set (ComplexModel n)), ENNReal.ofReal (-U j x) := lintegral_mono_set hLQ
      _ ≤ ENNReal.ofReal Bd := hL1 j
  have ha'Q : a ∈ (Q : Set (ComplexModel n)) := by
    show a ∈ polydiskAt a R
    rw [mem_polydiskAt hR]; intro j; simp [hR]
  obtain ⟨v, σ, hσ, hv, -, hvlim⟩ := exists_subseq_tendsto_localL1
    (convex_polydiskAt a hR).isPreconnected (fun j z => ((U j z : ℝ) : EReal))
    (fun j => (hU j).psh.1) (fun j => ⟨a, ha'Q, EReal.coe_ne_bot _⟩) (C := 0)
    (fun j z hz => EReal.coe_le_coe_iff.mpr ((hU j).nonpos z hz)) hbound
  -- the barrier
  obtain ⟨W, N, hW, hWb, hWfr, hN, hKN, hNQ, hWeq⟩ := exists_barrier hn a hR hK hKQ hw hM hwb
  have hWα := restrict_le_ma_barrier hN hNQ hKN hw hW hWeq hαK hα
  have hWv := coe_le_of_approximants hn hK hKQ hαK hA hW (by linarith) (fun z hz =>
    ⟨(hWb z hz).1, (hWb z hz).2⟩) hWα hv hσ hvlim
  -- the limit is bounded above by `0`
  set T₀ : ℝ := M + 1 with hT₀def
  set u : ComplexModel n → ℝ := truncReal v T₀ with hudef
  have hu : IsLocallyBoundedPshOn Q u := isLocallyBoundedPshOn_truncReal hv T₀
  have huv : ∀ z ∈ Q, (u z : EReal) = v z := fun z hz => by
    rw [hudef, coe_truncReal hv T₀ hz]
    exact max_eq_left (((EReal.coe_le_coe_iff.mpr (hWb z hz).1)).trans (hWv z hz))
  have hulim : ∀ L : Set (ComplexModel n), IsCompact L → L ⊆ Q →
      Tendsto (fun k => ∫⁻ x in L, ENNReal.ofReal |U (σ k) x - u x|) atTop (𝓝 0) := by
    intro L hL hLQ
    refine (hvlim L hL hLQ).congr fun k => setLIntegral_congr_fun hL.measurableSet fun x hx => ?_
    rw [← huv x (hLQ hx), canonicalERealAbsDiff_coe_coe]
  have hu0 : ∀ z ∈ Q, u z ≤ 0 := by
    have hae := ae_le_of_localL1 (aemeasurable_of_isLocallyBoundedPshOn hu volume) aemeasurable_const
      hulim (W := fun _ => 0) (ℓ := 0) fun j _ z hz => (hU (σ j)).nonpos z hz
    intro z hz
    have h := hu.1.le_of_ae_le Q.isOpen
      (UpperSemicontinuous.upperSemicontinuousOn
        (f := fun _ : ComplexModel n => ((0 : ℝ) : EReal)) upperSemicontinuous_const _) volume
      (hae.mono fun y hy => EReal.coe_le_coe_iff.mpr hy) z hz
    exact EReal.coe_le_coe_iff.mp h
  have huW : ∀ z ∈ Q, W z ≤ u z := fun z hz => by
    have := hWv z hz
    rw [← huv z hz] at this
    exact EReal.coe_le_coe_iff.mp this
  refine ⟨σ, u, hσ, hu, fun z hz => ⟨(hWb z hz).1.trans (huW z hz), hu0 z hz⟩, fun ζ hζ => ?_,
    hulim⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (hWfr ζ hζ) tendsto_const_nhds ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with z hz using huW z hz
  · filter_upwards [self_mem_nhdsWithin] with z hz using hu0 z hz

/-- **The whole sequence of approximants converges to the Kołodziej solution** (FPT,
`thm:compact-bounded-subsolution-ball-dirichlet`, "`A_j → A` locally in capacity", here in
`L¹_loc(Q)`, convolution variant on a polydisk): if `A ∈ ℰ₀(Q)` solves `(ddᶜA)ⁿ = α`, then every
sequence of Kołodziej approximants of `α` converges to `A` in `L¹_loc(Q)`. -/
theorem tendsto_localL1_of_isKolodziejApprox (hn : 0 < n) (a : ComplexModel n) {R : ℝ}
    (hR : 0 < R) {α : Measure (ComplexModel n)} [IsFiniteMeasure α] {K : Set (ComplexModel n)}
    (hK : IsCompact K) (hKQ : K ⊆ polydiskAt a R) (hαK : α Kᶜ = 0) {w : ComplexModel n → ℝ}
    (hw : IsLocallyBoundedPshOn (polydiskAtOpens a R) w) {b M : ℝ} (hM : 0 ≤ M)
    (hwb : ∀ z ∈ polydiskAt a R, b ≤ w z ∧ w z ≤ b + M)
    (hα : α.restrict (polydiskAt a R) ≤
      canonicalBedfordTaylorMeasure (polydiskAtOpens a R) w hw)
    {U : ℕ → ComplexModel n → ℝ} (hA : IsKolodziejApprox (polydiskAtOpens a R) α U)
    {A : ComplexModel n → ℝ} (hAE : IsCegrellE0 (polydiskAtOpens a R) A)
    (hAMA : canonicalBedfordTaylorMeasure (polydiskAtOpens a R) A hAE.psh = α)
    {L : Set (ComplexModel n)} (hL : IsCompact L) (hLQ : L ⊆ polydiskAt a R) :
    Tendsto (fun j => ∫⁻ x in L, ENNReal.ofReal |U j x - A x|) atTop (𝓝 0) := by
  classical
  set Q : Opens (ComplexModel n) := polydiskAtOpens a R with hQdef
  have hαQ : α (Q : Set (ComplexModel n))ᶜ = 0 :=
    measure_mono_null (compl_subset_compl.mpr hKQ) hαK
  by_contra hcon
  rw [ENNReal.tendsto_nhds_zero] at hcon
  push Not at hcon
  obtain ⟨ε, hε, hfreq⟩ := hcon
  obtain ⟨τ, hτ, hτε⟩ := extraction_of_frequently_atTop hfreq
  have hAτ := hA.comp hτ
  obtain ⟨σ, u, hσ, hu, hub, hbd, hulim⟩ :=
    exists_subseq_bounded_limit_of_isKolodziejApprox hn a hR hK hKQ hαK hw hM hwb hα hAτ
  have hMA : canonicalBedfordTaylorMeasure Q u hu = α :=
    ma_eq_of_approximants hn hαQ hAτ hu (B := M + 1) hub hσ hulim
  have huA : ∀ z ∈ Q, u z = A z := by
    have hfin : canonicalBedfordTaylorMeasure Q u hu (Q : Set (ComplexModel n)) < ⊤ := by
      rw [hMA]; exact measure_lt_top α _
    refine eq_of_ma_eq hn hA.bounded hu hAE.psh (fun ζ hζ δ hδ => ?_) hfin (hMA.trans hAMA.symm)
    have h := ((hbd ζ hζ).sub (hAE.tendsto_frontier ζ hζ)).eventually
      (Metric.ball_mem_nhds (0 - 0 : ℝ) hδ)
    filter_upwards [h] with z hz
    simpa [Real.dist_eq] using hz
  have hlim : Tendsto (fun k => ∫⁻ x in L, ENNReal.ofReal |U (τ (σ k)) x - A x|) atTop (𝓝 0) :=
    (hulim L hL hLQ).congr fun k => setLIntegral_congr_fun hL.measurableSet fun x hx => by
      rw [huA x (hLQ hx)]
  obtain ⟨k, hk⟩ := ((ENNReal.tendsto_nhds_zero.mp hlim) ε hε).exists
  exact absurd (hτε (σ k)) (not_lt.mpr hk)

end SGPT.Envelopes.MADirichlet
