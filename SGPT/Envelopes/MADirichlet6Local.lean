import SGPT.Envelopes.MADirichlet6Step2
import SGPT.Envelopes.DinewMeasureYau

/-!
# Dinew's inequality against a common measure, and the relative Calabi–Yau theorem

Xia, *Foundations of pluripotential theory* (FPT), `thm:bounded-multifactor-common-measure`:
for an open `Ω ⊆ ℂⁿ`, locally bounded plurisubharmonic `u₁, …, uₙ` on `Ω`, a measure `μ` and
Borel `fᵢ ≥ 0` with `(ddᶜuᵢ)ⁿ ≥ fᵢ μ`, we have `ddᶜu₁ ∧ ⋯ ∧ ddᶜuₙ ≥ (∏ᵢ fᵢ^{1/n}) μ`.

* `mixed_ge_withDensity_polydisk`: FPT Steps 1–2 on a polydisk `Q` for potentials `-B ≤ vᵢ ≤ 0`
  with boundary values `0` and finite Monge–Ampère mass: the Kołodziej solutions `A_{l,i}` of
  `𝟙_{K_l}(ddᶜvᵢ)ⁿ` (`exists_kolodziej_exhaustion_mixed`, Step 1) satisfy
  `⋀ᵢ ddᶜA_{l,i} ≥ 𝟙_{K_l} λ` (`mixed_ge_restrict_of_kolodziej`, Step 2) and their mixed products
  converge weakly to `⋀ᵢ ddᶜvᵢ`.
* `exists_nhds_restrict_le_mixed`: FPT Step 3 (localization): near a point `z₀ ∈ Ω`,
  `ũᵢ = max(uᵢ - c, C ρ_Q)` on a polydisk `Q = z₀ + R·P` (`ρ_Q = polydiskExhaustion`) is bounded,
  has boundary values `0`, finite mass (it is plurisubharmonic on the larger polydisk
  `z₀ + 2R·P ⊆ Ω`) and equals `uᵢ - c` on the open set `N = {ρ_Q < -1/4} ∋ z₀`.
* `restrict_le_of_forall_mem_nhds`: local lower bounds glue (finite subcovers of compact sets).
* `boundedMultifactorCommonMeasure`: **`BoundedMultifactorCommonMeasure n` for every `n`**.
* `source_relative_calabiYau_unconditional`: **source `thm:Yau_rel`** (existence and uniqueness)
  in every dimension, with no extra hypothesis.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ENNReal

namespace SGPT.Envelopes.MADirichlet

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.MixedMongeAmpere
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.MongeAmpere
open SGPT.Foundations.Analysis.Pending.MixedMongeAmpere SGPT.Foundations.Analysis.Pending.MixedNonPluripolar
open SGPT.Foundations.Analysis.Pending.BedfordTaylor

variable {n : ℕ}

/-! ### Polydisks -/

theorem mem_polydiskAt_of_polydiskExhaustion_neg {a z : ComplexModel n} {R : ℝ} (hn : 0 < n)
    (hz : polydiskExhaustion a R hn z < 0) : z ∈ polydiskAt a R := by
  rw [polydiskExhaustion_apply, Finset.sup'_lt_iff] at hz
  show affineFrom a R z ∈ unitPolydisk n
  intro j
  have h := hz j (Finset.mem_univ j)
  simp only [coordExhaustion] at h
  have h0 : 0 ≤ ‖affineFrom a R z j‖ := norm_nonneg _
  nlinarith

theorem polydiskExhaustion_center (a : ComplexModel n) (R : ℝ) (hn : 0 < n) :
    polydiskExhaustion a R hn a = -1 := by
  rw [polydiskExhaustion_apply]
  have h : ∀ j, coordExhaustion a R j a = -1 := fun j => by
    simp [coordExhaustion, affineFrom]
  simp only [h, Finset.sup'_const]

theorem norm_sub_le_of_mem_polydiskAt {a z : ComplexModel n} {R : ℝ} (hR : 0 < R)
    (hz : z ∈ polydiskAt a R) : ‖z - a‖ ≤ R * (n + 1) := by
  have hz' : affineFrom a R z ∈ unitPolydisk n := hz
  have h1 := norm_sq_le_of_mem_unitPolydisk hz'
  have h2 : ‖affineFrom a R z‖ ≤ n + 1 := by nlinarith [norm_nonneg (affineFrom a R z)]
  have h3 : z - a = R • affineFrom a R z := by
    simp only [affineFrom, smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
  rw [h3, norm_smul, Real.norm_eq_abs, abs_of_pos hR]
  exact mul_le_mul_of_nonneg_left h2 hR.le

/-- Compact sublevel sets of the polydisk exhaustion exhaust the polydisk; every compact subset of
the polydisk lies in one of them. -/
theorem exists_polydisk_compact_exhaustion (hn : 0 < n) (a : ComplexModel n) {R : ℝ}
    (hR : 0 < R) :
    ∃ K : ℕ → Set (ComplexModel n), (∀ l, IsCompact (K l)) ∧ (∀ l, K l ⊆ polydiskAt a R) ∧
      Monotone K ∧ ∀ S : Set (ComplexModel n), IsCompact S → S ⊆ polydiskAt a R →
        ∃ l, S ⊆ K l := by
  set ρ := polydiskExhaustion a R hn with hρdef
  have hρc : Continuous ρ := continuous_polydiskExhaustion a R hn
  set K : ℕ → Set (ComplexModel n) := fun l => {z | ρ z ≤ -1 / ((l : ℝ) + 2)} with hKdef
  have hKQ : ∀ l, K l ⊆ polydiskAt a R := fun l z hz =>
    mem_polydiskAt_of_polydiskExhaustion_neg hn (lt_of_le_of_lt hz (by
      have : (0 : ℝ) < 1 / ((l : ℝ) + 2) := by positivity
      rw [neg_div]; linarith))
  refine ⟨K, fun l => Metric.isCompact_of_isClosed_isBounded (isClosed_le hρc continuous_const)
    ((isBounded_polydiskAt a hR).subset (hKQ l)), hKQ, fun l l' hll' z hz => ?_, fun S hS hSQ => ?_⟩
  · have h1 : (1 : ℝ) / ((l' : ℝ) + 2) ≤ 1 / ((l : ℝ) + 2) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hll' 2)
    have h2 : ρ z ≤ -1 / ((l : ℝ) + 2) := hz
    show ρ z ≤ -1 / ((l' : ℝ) + 2)
    rw [neg_div] at h2 ⊢
    linarith
  · rcases S.eq_empty_or_nonempty with he | hne
    · exact ⟨0, he ▸ empty_subset _⟩
    obtain ⟨z₀, hz₀S, hmax⟩ := hS.exists_isMaxOn hne hρc.continuousOn
    have hneg : ρ z₀ < 0 := polydiskExhaustion_neg hn (hSQ hz₀S)
    obtain ⟨l, hl⟩ := exists_nat_one_div_lt (neg_pos.mpr hneg)
    refine ⟨l, fun z hz => ?_⟩
    have h1 : ρ z ≤ ρ z₀ := hmax hz
    have h2 : (1 : ℝ) / ((l : ℝ) + 2) ≤ 1 / ((l : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    show ρ z ≤ -1 / ((l : ℝ) + 2)
    rw [neg_div]
    linarith

/-! ### Steps 1 and 2 on a polydisk -/

/-- **Dinew's inequality on a polydisk for potentials with zero boundary values** (FPT
`thm:bounded-multifactor-common-measure`, Steps 1 and 2, on a polydisk instead of a ball, for
`-B ≤ vᵢ ≤ 0` with boundary values `0` and `(ddᶜvᵢ)ⁿ(Q) < ∞`, i.e. bounded potentials in
`ℰ₀(Q)`). -/
theorem mixed_ge_withDensity_polydisk (hn : 0 < n) (a : ComplexModel n) {R : ℝ} (hR : 0 < R)
    {v : Fin n → ComplexModel n → ℝ} (hv : IsLocallyBoundedMixedPshOn (polydiskAtOpens a R) v)
    {B : ℝ} (hB : 0 ≤ B) (hvb : ∀ i, ∀ z ∈ polydiskAt a R, -B ≤ v i z ∧ v i z ≤ 0)
    (hbd : ∀ i, ∀ ζ ∈ frontier (polydiskAt a R), Tendsto (v i) (𝓝[polydiskAt a R] ζ) (𝓝 0))
    (hfin : ∀ i, canonicalBedfordTaylorMeasure (polydiskAtOpens a R) (v i) (hv i)
      (polydiskAt a R) < ⊤)
    (μ : Measure (ComplexModel n)) {f : Fin n → ComplexModel n → ℝ≥0∞}
    (hf : ∀ i, Measurable (f i))
    (hfμ : ∀ i, (μ.withDensity (f i)).restrict (polydiskAt a R) ≤
      canonicalBedfordTaylorMeasure (polydiskAtOpens a R) (v i) (hv i)) :
    (μ.withDensity fun z => ∏ i, f i z ^ ((n : ℝ)⁻¹)).restrict (polydiskAt a R) ≤
      canonicalMixedBedfordTaylorMeasure (polydiskAtOpens a R) v hv := by
  classical
  set Q : Opens (ComplexModel n) := polydiskAtOpens a R with hQdef
  have hQm : MeasurableSet (polydiskAt a R) := (isOpen_polydiskAt a R).measurableSet
  obtain ⟨K, hK, hKQ, hKmono, hKcov⟩ := exists_polydisk_compact_exhaustion hn a hR
  obtain ⟨A, hA, hMA, hAb, hconv⟩ := exists_kolodziej_exhaustion_mixed hn a hR hv hB hvb hbd hfin
    hK hKQ hKmono fun z hz =>
      (hKcov {z} isCompact_singleton (singleton_subset_iff.mpr hz)).imp fun _ hl => hl rfl
  set lam : Measure (ComplexModel n) := μ.withDensity fun z => ∏ i, f i z ^ ((n : ℝ)⁻¹)
    with hlamdef
  have hAm : ∀ l, IsLocallyBoundedMixedPshOn Q (A l) := fun l i => (hA l i).psh
  have hstep : ∀ l, lam.restrict (K l) ≤ canonicalMixedBedfordTaylorMeasure Q (A l) (hAm l) :=
    fun l => mixed_ge_restrict_of_kolodziej hn a hR hv hB hvb (hK l) (hKQ l) (hA l)
      (fun i z hz => (hvb i z hz).1.trans (hAb l i z hz).1) (hMA l) μ hf fun i => by
        calc (μ.withDensity (f i)).restrict (K l)
            = ((μ.withDensity (f i)).restrict (polydiskAt a R)).restrict (K l) :=
              (Measure.restrict_restrict_of_subset (hKQ l)).symm
          _ ≤ _ := Measure.restrict_le_self.trans (hfμ i)
  have hmixfin : ∀ l, ∀ S : Set (ComplexModel n), IsCompact S → S ⊆ Q →
      canonicalMixedBedfordTaylorMeasure Q (A l) (hAm l) S < ⊤ := fun l =>
    (canonicalMixedBedfordTaylorMeasure_spec Q (A l) (hAm l)).2.2.1
  have hlamfin : ∀ S : Set (ComplexModel n), IsCompact S → S ⊆ Q →
      lam.restrict (polydiskAt a R) S < ⊤ := by
    intro S hS hSQ
    obtain ⟨l, hl⟩ := hKcov S hS hSQ
    calc lam.restrict (polydiskAt a R) S ≤ lam S := Measure.restrict_apply_le _ _
      _ = lam.restrict (K l) S := by
          rw [Measure.restrict_apply hS.measurableSet, inter_eq_left.mpr hl]
      _ ≤ canonicalMixedBedfordTaylorMeasure Q (A l) (hAm l) S := hstep l S
      _ < ⊤ := hmixfin l S hS hSQ
  have htest : ∀ h : ComplexModel n → ℝ, Continuous h → HasCompactSupport h →
      tsupport h ⊆ (Q : Set (ComplexModel n)) → (∀ z, 0 ≤ h z) →
      ∫ z, h z ∂lam.restrict (polydiskAt a R) ≤
        ∫ z, h z ∂canonicalMixedBedfordTaylorMeasure Q v hv := by
    intro h hc hcs hsupp h0
    obtain ⟨l₀, hl₀⟩ := hKcov (tsupport h) hcs.isCompact hsupp
    refine ge_of_tendsto (hconv h hc hcs hsupp) (eventually_atTop.mpr ⟨l₀, fun l hl => ?_⟩)
    have hsub : tsupport h ⊆ K l := hl₀.trans (hKmono hl)
    have e1 : ∫ z, h z ∂lam.restrict (polydiskAt a R) = ∫ z, h z ∂lam :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz =>
        image_eq_zero_of_notMem_tsupport fun h' => hz (hsupp h')
    have e2 : ∫ z, h z ∂lam.restrict (K l) = ∫ z, h z ∂lam :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz =>
        image_eq_zero_of_notMem_tsupport fun h' => hz (hsub h')
    rw [e1, ← e2]
    exact integral_le_integral_of_le (hstep l) (hmixfin l) hc hcs hsupp h0
  have hcmp : ∀ S : Set (ComplexModel n), IsCompact S → S ⊆ Q →
      lam.restrict (polydiskAt a R) S ≤ canonicalMixedBedfordTaylorMeasure Q v hv S :=
    fun S hS hSQ => measure_le_of_testFunction_integral_le (U := Q) hlamfin
      (canonicalMixedBedfordTaylorMeasure_spec Q v hv).2.2.1 htest hS hSQ
  have hres := restrict_le_of_isCompact_le hlamfin hcmp
  refine le_trans (le_of_eq ?_) hres
  exact (Measure.restrict_eq_self_of_ae_mem (ae_restrict_mem hQm)).symm

/-! ### Step 3: localization -/

/-- **Localization** (FPT `thm:bounded-multifactor-common-measure`, Step 3): every point of `Ω`
has an open neighbourhood `N ⊆ Ω` on which `ddᶜu₁ ∧ ⋯ ∧ ddᶜuₙ ≥ (∏ᵢ fᵢ^{1/n}) μ`. -/
theorem exists_nhds_restrict_le_mixed (hn : 0 < n) {Ω : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → ℝ} (hu : IsLocallyBoundedMixedPshOn Ω u)
    (μ : Measure (ComplexModel n)) {f : Fin n → ComplexModel n → ℝ≥0∞}
    (hf : ∀ i, Measurable (f i))
    (hfμ : ∀ i, (μ.withDensity (f i)).restrict Ω ≤ canonicalBedfordTaylorMeasure Ω (u i) (hu i))
    {z₀ : ComplexModel n} (hz₀ : z₀ ∈ Ω) :
    ∃ N : Set (ComplexModel n), IsOpen N ∧ z₀ ∈ N ∧ N ⊆ Ω ∧
      (μ.withDensity fun z => ∏ i, f i z ^ ((n : ℝ)⁻¹)).restrict N ≤
        canonicalMixedBedfordTaylorMeasure Ω u hu := by
  classical
  obtain ⟨ε, hε, hεΩ⟩ := Metric.isOpen_iff.mp Ω.isOpen z₀ hz₀
  set R : ℝ := ε / (4 * ((n : ℝ) + 1)) with hRdef
  have hR : 0 < R := by positivity
  have h2R : 0 < 2 * R := by positivity
  have hRε : 2 * R * ((n : ℝ) + 1) = ε / 2 := by rw [hRdef]; field_simp; ring
  -- the polydisks `Q = z₀ + R·P ⊆ Q₂ = z₀ + 2R·P ⊆ B̄(z₀, ε/2) ⊆ Ω`
  set Q : Opens (ComplexModel n) := polydiskAtOpens z₀ R with hQdef
  set Q₂ : Opens (ComplexModel n) := polydiskAtOpens z₀ (2 * R) with hQ₂def
  have hQm : MeasurableSet (polydiskAt z₀ R) := (isOpen_polydiskAt z₀ R).measurableSet
  set Kb : Set (ComplexModel n) := closedBall z₀ (ε / 2) with hKbdef
  have hKbΩ : Kb ⊆ Ω := (closedBall_subset_ball (by linarith)).trans hεΩ
  have hQ₂Kb : polydiskAt z₀ (2 * R) ⊆ Kb := fun w hw => by
    rw [hKbdef, mem_closedBall, dist_eq_norm, ← hRε]
    exact norm_sub_le_of_mem_polydiskAt h2R hw
  have hQ₂Ω : Q₂ ≤ Ω := hQ₂Kb.trans hKbΩ
  set Kc : Set (ComplexModel n) := {w | ∀ j, ‖w j - z₀ j‖ ≤ R} with hKcdef
  have hQKc : polydiskAt z₀ R ⊆ Kc := fun w hw j => ((mem_polydiskAt hR).mp hw j).le
  have hKcQ₂ : Kc ⊆ polydiskAt z₀ (2 * R) := fun w hw =>
    (mem_polydiskAt h2R).mpr fun j => lt_of_le_of_lt (hw j) (by linarith)
  have hKcc : IsCompact Kc := by
    refine Metric.isCompact_of_isClosed_isBounded ?_
      ((isBounded_polydiskAt z₀ h2R).subset hKcQ₂)
    rw [hKcdef, ofPred_forall]
    exact isClosed_iInter fun j => isClosed_le
      (((EuclideanSpace.proj (𝕜 := ℂ) j).continuous.sub continuous_const).norm) continuous_const
  have hQQ₂ : Q ≤ Q₂ := hQKc.trans hKcQ₂
  have hQΩ : Q ≤ Ω := hQQ₂.trans hQ₂Ω
  -- a bound for the potentials on `B̄(z₀, ε/2)`
  choose m hm using fun i => IsLocallyBoundedPshOn.exists_abs_le (hu i)
    (isCompact_closedBall z₀ (ε / 2)) hKbΩ
  set M : ℝ := ∑ i, |m i| with hMdef
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hMb : ∀ i, ∀ w ∈ Kb, |u i w| ≤ M := fun i w hw =>
    (hm i w hw).trans ((le_abs_self _).trans
      (Finset.single_le_sum (fun k _ => abs_nonneg (m k)) (Finset.mem_univ i)))
  have huQ : ∀ i, ∀ w ∈ polydiskAt z₀ R, -M ≤ u i w ∧ u i w ≤ M := fun i w hw =>
    abs_le.mp (hMb i w (hQ₂Kb (hQQ₂ hw)))
  -- the modified potentials `ũᵢ = max(uᵢ - c, C ρ_Q)`
  set ρ := polydiskExhaustion z₀ R hn with hρdef
  have hρc : Continuous ρ := continuous_polydiskExhaustion z₀ R hn
  set Cc : ℝ := 4 * (2 * M + 2) with hCcdef
  have hCc : 0 < Cc := by positivity
  set c : ℝ := M + 1 with hcdef
  set ũ : Fin n → ComplexModel n → ℝ := fun i w => max (u i w + -c) (Cc * ρ w) with hũdef
  have hu₂ : ∀ i, IsLocallyBoundedPshOn Q₂ fun w => u i w + -c := fun i =>
    IsLocallyBoundedPshOn.add_const (IsLocallyBoundedPshOn.mono_opens (hu i) hQ₂Ω) (-c)
  have hũ₂ : ∀ i, IsLocallyBoundedPshOn Q₂ (ũ i) := fun i =>
    IsLocallyBoundedPshOn.max (hu₂ i)
      (isLocallyBoundedPshOn_const_mul (isLocallyBoundedPshOn_polydiskExhaustion z₀ R hn Q₂)
        hCc.le)
  have hũ : IsLocallyBoundedMixedPshOn Q ũ := fun i =>
    IsLocallyBoundedPshOn.mono_opens (hũ₂ i) hQQ₂
  have hρQ : ∀ w ∈ polydiskAt z₀ R, -1 ≤ ρ w ∧ ρ w < 0 := fun w hw =>
    ⟨neg_one_le_polydiskExhaustion z₀ R hn w, polydiskExhaustion_neg hn hw⟩
  have hub : ∀ i, ∀ w ∈ polydiskAt z₀ R, -Cc ≤ ũ i w ∧ ũ i w ≤ 0 := by
    intro i w hw
    refine ⟨le_trans (by nlinarith [(hρQ w hw).1]) (le_max_right _ _), max_le ?_ ?_⟩
    · linarith [(huQ i w hw).2]
    · exact mul_nonpos_of_nonneg_of_nonpos hCc.le (hρQ w hw).2.le
  have hbdũ : ∀ i, ∀ ζ ∈ frontier (polydiskAt z₀ R),
      Tendsto (ũ i) (𝓝[polydiskAt z₀ R] ζ) (𝓝 0) := by
    intro i ζ hζ
    have hρζ : ρ ζ = 0 := polydiskExhaustion_eq_zero_of_mem_frontier hR hn hζ
    have hlim : Tendsto (fun w => Cc * ρ w) (𝓝 ζ) (𝓝 0) := by
      have := (hρc.tendsto ζ).const_mul Cc
      rwa [hρζ, mul_zero] at this
    have hev : ∀ᶠ w in 𝓝[polydiskAt z₀ R] ζ, Cc * ρ w = ũ i w := by
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (hlim.eventually (Ioi_mem_nhds (by norm_num : (-1 : ℝ) < 0)))]
        with w hw hw'
      have h1 : u i w + -c ≤ -1 := by linarith [(huQ i w hw).2]
      have h2 : -1 < Cc * ρ w := hw'
      exact (max_eq_right (by linarith)).symm
    exact (hlim.mono_left nhdsWithin_le_nhds).congr' hev
  have hfinũ : ∀ i, canonicalBedfordTaylorMeasure Q (ũ i) (hũ i) (polydiskAt z₀ R) < ⊤ := by
    intro i
    rw [← canonicalBedfordTaylorMeasure_restrict_eq hQQ₂ (hũ₂ i) (hũ i),
      Measure.restrict_apply hQm]
    exact lt_of_le_of_lt (measure_mono (inter_subset_left.trans hQKc))
      ((isBTLimit_canonicalBedfordTaylorMeasure (hũ₂ i)).2.1 Kc hKcc hKcQ₂)
  -- the open set `N = {ρ_Q < -1/4}`, where `ũᵢ = uᵢ - c`
  set N : Set (ComplexModel n) := {w | ρ w < -1 / 4} with hNdef
  have hNo : IsOpen N := isOpen_lt hρc continuous_const
  have hNm : MeasurableSet N := hNo.measurableSet
  have hNQ : N ⊆ polydiskAt z₀ R := fun w hw =>
    mem_polydiskAt_of_polydiskExhaustion_neg hn (lt_trans hw (by norm_num))
  have hNΩ : N ⊆ Ω := hNQ.trans hQΩ
  have hz₀N : z₀ ∈ N := by
    show ρ z₀ < -1 / 4
    rw [hρdef, polydiskExhaustion_center]
    norm_num
  have hũN : ∀ i, ∀ w ∈ N, ũ i w = u i w + -c := by
    intro i w hw
    have h1 : ρ w < -1 / 4 := hw
    have h2 := (huQ i w (hNQ hw)).1
    refine max_eq_left ?_
    have h3 : Cc * ρ w ≤ Cc * (-1 / 4) := mul_le_mul_of_nonneg_left h1.le hCc.le
    have h4 : Cc * (-1 / 4) = -(2 * M + 2) := by rw [hCcdef]; ring
    linarith
  -- the hypothesis on `Q` for the measure `𝟙_N μ`
  have huQ' : ∀ i, IsLocallyBoundedPshOn Q (u i) := fun i =>
    IsLocallyBoundedPshOn.mono_opens (hu i) hQΩ
  have hfμN : ∀ i, ((μ.restrict N).withDensity (f i)).restrict (polydiskAt z₀ R) ≤
      canonicalBedfordTaylorMeasure Q (ũ i) (hũ i) := by
    intro i
    set α : Measure (ComplexModel n) := (μ.withDensity (f i)).restrict N with hαdef
    have hαQ : α.restrict (polydiskAt z₀ R) = α :=
      Measure.restrict_eq_self_of_ae_mem ((ae_restrict_mem hNm).mono fun x hx => hNQ hx)
    have hαN : α Nᶜ = 0 := by
      rw [hαdef, Measure.restrict_apply hNm.compl, compl_inter_self, measure_empty]
    have hα : α.restrict Q ≤ canonicalBedfordTaylorMeasure Q (u i) (huQ' i) := by
      change α.restrict (polydiskAt z₀ R) ≤ _
      rw [hαQ, ← canonicalBedfordTaylorMeasure_restrict_eq hQΩ (hu i) (huQ' i)]
      calc α = ((μ.withDensity (f i)).restrict Ω).restrict N :=
            (Measure.restrict_restrict_of_subset hNΩ).symm
        _ ≤ (canonicalBedfordTaylorMeasure Ω (u i) (hu i)).restrict N :=
            Measure.restrict_mono le_rfl (hfμ i)
        _ ≤ (canonicalBedfordTaylorMeasure Ω (u i) (hu i)).restrict (polydiskAt z₀ R) :=
            Measure.restrict_mono hNQ le_rfl
    have h := restrict_le_ma_of_eqOn hNo hNQ (huQ' i) (hũ i) (hũN i) hαN hα
    rw [← restrict_withDensity hNm]
    change α.restrict (polydiskAt z₀ R) ≤ _
    exact h
  -- Steps 1–2 on `Q`
  have hB := mixed_ge_withDensity_polydisk hn z₀ hR hũ hCc.le hub hbdũ hfinũ (μ.restrict N) hf
    hfμN
  -- identification on `N`
  set N' : Opens (ComplexModel n) := ⟨N, hNo⟩ with hN'def
  have hN'Q : N' ≤ Q := hNQ
  have hN'Ω : N' ≤ Ω := hNΩ
  have huN' : IsLocallyBoundedMixedPshOn N' u := fun i =>
    IsLocallyBoundedPshOn.mono_opens (hu i) hN'Ω
  have hucN' : IsLocallyBoundedMixedPshOn N' fun i w => u i w + -c := fun i =>
    IsLocallyBoundedPshOn.add_const (huN' i) (-c)
  have e1 : (canonicalMixedBedfordTaylorMeasure Q ũ hũ).restrict N =
      canonicalMixedBedfordTaylorMeasure N' (fun i w => u i w + -c) hucN' :=
    canonicalMixedBedfordTaylorMeasure_open_locality hN'Q hũ hucN' fun i w hw => hũN i w hw
  have e2 : canonicalMixedBedfordTaylorMeasure N' (fun i w => u i w + -c) hucN' =
      canonicalMixedBedfordTaylorMeasure N' u huN' :=
    canonicalMixedBedfordTaylorMeasure_add_const huN' (fun _ => -c) hucN'
  have e3 : (canonicalMixedBedfordTaylorMeasure Ω u hu).restrict N =
      canonicalMixedBedfordTaylorMeasure N' u huN' :=
    canonicalMixedBedfordTaylorMeasure_restrict hN'Ω hu huN'
  refine ⟨N, hNo, hz₀N, hNΩ, ?_⟩
  have hL : (μ.withDensity fun z => ∏ i, f i z ^ ((n : ℝ)⁻¹)).restrict N =
      (((μ.restrict N).withDensity fun z => ∏ i, f i z ^ ((n : ℝ)⁻¹)).restrict
        (polydiskAt z₀ R)).restrict N := by
    rw [Measure.restrict_restrict_of_subset hNQ, ← restrict_withDensity hNm,
      Measure.restrict_restrict_of_subset (subset_refl N)]
  calc (μ.withDensity fun z => ∏ i, f i z ^ ((n : ℝ)⁻¹)).restrict N
      = (((μ.restrict N).withDensity fun z => ∏ i, f i z ^ ((n : ℝ)⁻¹)).restrict
          (polydiskAt z₀ R)).restrict N := hL
    _ ≤ (canonicalMixedBedfordTaylorMeasure Q ũ hũ).restrict N := Measure.restrict_mono le_rfl hB
    _ = (canonicalMixedBedfordTaylorMeasure Ω u hu).restrict N := by rw [e1, e2, e3]
    _ ≤ canonicalMixedBedfordTaylorMeasure Ω u hu := Measure.restrict_le_self

/-! ### Gluing -/

/-- Lower bounds on two measurable sets give a lower bound on their union. -/
theorem restrict_union_le_of_restrict_le {X : Type*} [MeasurableSpace X] {α ν : Measure X}
    {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B) (hAν : α.restrict A ≤ ν)
    (hBν : α.restrict B ≤ ν) : α.restrict (A ∪ B) ≤ ν := by
  rw [← union_sdiff_self, Measure.restrict_union disjoint_sdiff_right (hB.diff hA)]
  have h1 : α.restrict A ≤ ν.restrict A := by
    have h := Measure.restrict_mono (subset_refl A) hAν
    rwa [Measure.restrict_restrict_of_subset (subset_refl A)] at h
  have h2 : α.restrict (B \ A) ≤ ν.restrict (B \ A) := by
    have h := Measure.restrict_mono (subset_refl (B \ A)) hBν
    rwa [Measure.restrict_restrict_of_subset sdiff_subset] at h
  calc α.restrict A + α.restrict (B \ A) ≤ ν.restrict A + ν.restrict (B \ A) := add_le_add h1 h2
    _ = ν.restrict (A ∪ (B \ A)) :=
        (Measure.restrict_union disjoint_sdiff_right (hB.diff hA)).symm
    _ ≤ ν := Measure.restrict_le_self

/-- **Local lower bounds glue** (the countable cover at the end of FPT's Step 3, here through
finite subcovers of compact sets): if every point of `Ω` has an open neighbourhood `N ⊆ Ω` with
`α|_N ≤ ν`, and `ν` is finite on compact subsets of `Ω`, then `α|_Ω ≤ ν`. -/
theorem restrict_le_of_forall_mem_nhds {Ω : Opens (ComplexModel n)}
    {α ν : Measure (ComplexModel n)} (hν : ∀ K, IsCompact K → K ⊆ Ω → ν K < ⊤)
    (h : ∀ z ∈ Ω, ∃ N : Set (ComplexModel n), IsOpen N ∧ z ∈ N ∧ N ⊆ Ω ∧ α.restrict N ≤ ν) :
    α.restrict (Ω : Set (ComplexModel n)) ≤ ν := by
  classical
  choose! N hNo hzN hNΩ hNle using h
  have hfin : ∀ t : Finset (ComplexModel n), (∀ z ∈ t, z ∈ Ω) →
      α.restrict (⋃ z ∈ t, N z) ≤ ν := by
    intro t
    induction t using Finset.induction_on with
    | empty => intro _; simpa using Measure.zero_le ν
    | insert a t ha ih =>
        intro ht
        rw [Finset.set_biUnion_insert]
        exact restrict_union_le_of_restrict_le (hNo a (ht a (Finset.mem_insert_self a t))).measurableSet
          (isOpen_biUnion fun z hz => hNo z (ht z (Finset.mem_insert_of_mem hz))).measurableSet
          (hNle a (ht a (Finset.mem_insert_self a t)))
          (ih fun z hz => ht z (Finset.mem_insert_of_mem hz))
  have hKle : ∀ K : Set (ComplexModel n), IsCompact K → K ⊆ Ω → α K ≤ ν K := by
    intro K hK hKΩ
    obtain ⟨t, htK, hKt⟩ := hK.elim_nhds_subcover N fun z hz =>
      (hNo z (hKΩ hz)).mem_nhds (hzN z (hKΩ hz))
    have h := hfin t fun z hz => hKΩ (htK z hz)
    calc α K = α.restrict (⋃ z ∈ t, N z) K := by
          rw [Measure.restrict_apply hK.measurableSet, inter_eq_left.mpr hKt]
      _ ≤ ν K := h K
  exact restrict_le_of_isCompact_le (fun K hK hKΩ => (hKle K hK hKΩ).trans_lt (hν K hK hKΩ))
    hKle

/-! ### The theorem -/

/-- **Dinew's inequality for bounded plurisubharmonic functions against a common measure** (Xia,
*Foundations of pluripotential theory*, `thm:bounded-multifactor-common-measure`), in every
dimension: the statement `SGPT.Envelopes.DinewMeasure.BoundedMultifactorCommonMeasure n` holds for
all `n`. -/
theorem boundedMultifactorCommonMeasure (n : ℕ) :
    SGPT.Envelopes.DinewMeasure.BoundedMultifactorCommonMeasure n := by
  intro hn Ω u hu μ _ f hf hfμ
  have hfμ' : ∀ i, (μ.withDensity (f i)).restrict Ω ≤
      canonicalBedfordTaylorMeasure Ω (u i) (hu i) := fun i => by
    have h := hfμ i
    rwa [canonicalMixedBedfordTaylorMeasure_diagonal] at h
  exact restrict_le_of_forall_mem_nhds (canonicalMixedBedfordTaylorMeasure_spec Ω u hu).2.2.1
    fun z hz => exists_nhds_restrict_le_mixed hn hu μ hf hfμ' hz

end SGPT.Envelopes.MADirichlet

namespace SGPT.Envelopes.MADirichlet

open Set MeasureTheory
open scoped ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open SGPT.Envelopes.RelativeMA SGPT.Envelopes.RelativeCY SGPT.PSH.VariableComplexAtlas

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]
  [BorelSpace M]

/-- S61's global form of Dinew's inequality (`CommonMeasureConvexLowerBound`, FPT
`cor:nonpluripolar-common-measure-convex`) holds in every dimension. -/
theorem commonMeasureConvexLowerBound_all : CommonMeasureConvexLowerBound n M :=
  SGPT.Envelopes.DinewMeasure.commonMeasureConvexLowerBound_of_boundedMultifactor M
    (boundedMultifactorCommonMeasure n)

/-- **Source `thm:Yau_rel`** (relative Calabi–Yau theorem), unconditionally in every dimension.
Let `X` be a connected compact Kähler manifold, `θ` represent a big class and `φ` be a model
potential with positive mass. For every non-pluripolar measure `μ` with `μ(X) = ∫_X θ_φⁿ` there is
a unique `u ∈ ℰ(X, θ; φ)` with `θ_uⁿ = μ` and `sup_X u = 0`. -/
theorem source_relative_calabiYau_unconditional [ConnectedSpace M]
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (ω : KahlerBackground n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (hφ : SourceModelPotential θ φ) {μ : Measure M} (hμ : SourceNonPluripolarMeasure (n := n) μ)
    (hmass : μ univ = sourcePotentialNonPluripolarMeasure θ φ hφ.thetaPSH univ) :
    ∃! u : M → EReal, SourceRelativeFullMass θ φ u hφ ∧ SourceSolvesMeasureEquation θ μ u ∧
      (⨆ x, u x) = 0 :=
  source_relative_calabiYau_of_boundedMultifactor (boundedMultifactorCommonMeasure n) ω hbig hφ
    hμ hmass

end SGPT.Envelopes.MADirichlet
