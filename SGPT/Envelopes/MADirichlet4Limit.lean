import SGPT.Envelopes.MADirichlet4Kolodziej

/-!
# The convolution approximants converge to a bounded limit with zero boundary values

Xia, *Foundations of pluripotential theory* (FPT), `thm:compact-bounded-subsolution-ball-dirichlet`,
Steps 1–3 up to the identification of the equation, in the convolution variant on a polydisk
`Q = a + R·P`:

Let `α` be a finite measure carried by a compact `K ⊆ Q` with `α ≤ (ddᶜw)ⁿ` on `Q`,
`b ≤ w ≤ b + M`. The convolution approximants `U_j` of MA-DIR3 (`exists_convolution_approximants`,
`(ddᶜU_j)ⁿ = (α ∗ ρ_j + cₙ (j+1)⁻¹ χⁿ) dV`, `U_j ∈ ℰ₀(Q)`) satisfy the hypotheses
`IsKolodziejApprox` (`isKolodziejApprox_of_convolution` inside the proof: carried by a fixed
compact set, weak convergence, bounded `e₁`, and the self-integral convergence of
`tendsto_lintegral_convDensity_abs_sub` plus the `O(1/j)` error term), are bounded in `L¹(Q)`
(Cegrell–Persson for `cₙ dV = (ddᶜ|z|²)ⁿ`), so a subsequence converges in `L¹_loc(Q)`
(`exists_subseq_tendsto_localL1`), and by `coe_le_of_approximants` its limit `u` satisfies
`W ≤ u ≤ 0` for the barrier `W` of `exists_barrier`. Hence (`exists_approximants_bounded_limit`):
`u` is a bounded plurisubharmonic function on `Q`, `-(M+1) ≤ u ≤ 0`, with boundary values `0`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ENNReal

namespace SGPT.Envelopes.MADirichlet

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.MongeAmpere
open SGPT.Foundations.Analysis.Pending.BedfordTaylor
open SGPT.NPP.LogConcavityDinew

variable {n : ℕ}

/-- Polydisks are convex. -/
theorem convex_polydiskAt (a : ComplexModel n) {R : ℝ} (hR : 0 < R) : Convex ℝ (polydiskAt a R) := by
  intro z hz w hw s t hs ht hst
  rw [mem_polydiskAt hR] at hz hw ⊢
  intro j
  have h : (s • z + t • w) j - a j = s • (z j - a j) + t • (w j - a j) := by
    simp only [PiLp.add_apply, PiLp.smul_apply]
    rw [smul_sub, smul_sub, ← add_sub_add_comm, ← add_smul, hst, one_smul]
  rw [h]
  calc ‖s • (z j - a j) + t • (w j - a j)‖ ≤ ‖s • (z j - a j)‖ + ‖t • (w j - a j)‖ :=
        norm_add_le _ _
    _ = s * ‖z j - a j‖ + t * ‖w j - a j‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg hs, Real.norm_of_nonneg ht]
    _ < s * R + t * R := by
        rcases eq_or_lt_of_le hs with h0 | h0
        · subst h0
          have ht1 : t = 1 := by linarith
          subst ht1; simp only [zero_mul, one_mul, zero_add]; exact hw j
        · exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left (hz j) h0)
            (mul_le_mul_of_nonneg_left (hw j).le ht)
    _ = R := by rw [← add_mul, hst, one_mul]

/-- **`L¹` bound from the energy** (FPT `prop:canonical-grid-energy-control` (2), via the
Cegrell–Persson estimate for `cₙ dV = (ddᶜ|z|²)ⁿ`). -/
theorem lintegral_neg_le_of_localEnergy (hn : 0 < n) {Q : Opens (ComplexModel n)}
    (hQb : Bornology.IsBounded (Q : Set (ComplexModel n))) {ρ : ℝ} (hρ : ∀ z ∈ Q, ‖z‖ ≤ ρ)
    {U : ComplexModel n → ℝ} (hU : IsCegrellE0 Q U) {C : ℝ}
    (hC : (localEnergy Q 1 U hU.psh).toReal ≤ C) :
    ∫⁻ x in (Q : Set (ComplexModel n)), ENNReal.ofReal (-U x) ≤
      ENNReal.ofReal (energyMomentConst n 1
        ((ENNReal.ofReal (mongeAmpereConst n) • volume) (Q : Set (ComplexModel n))).toReal (ρ ^ 2) *
          C ^ (1 / ((n : ℝ) + 1)) / mongeAmpereConst n) := by
  have hcn : 0 < mongeAmpereConst n := mongeAmpereConst_pos
  set μ : Measure (ComplexModel n) := ENNReal.ofReal (mongeAmpereConst n) • volume with hμdef
  have hw : IsLocallyBoundedPshOn Q fun z => (fun _ => (0 : ℝ)) z + 1 * (‖z‖ ^ 2 - ρ ^ 2) := by
    have h := IsLocallyBoundedPshOn.add_const (isLocallyBoundedPshOn_normSq Q) (-(ρ ^ 2))
    convert h using 1
    funext z; ring
  have hwb : ∀ z ∈ Q, -(ρ ^ 2) ≤ (fun _ => (0 : ℝ)) z + 1 * (‖z‖ ^ 2 - ρ ^ 2) ∧
      (fun _ => (0 : ℝ)) z + 1 * (‖z‖ ^ 2 - ρ ^ 2) ≤ -(ρ ^ 2) + ρ ^ 2 := fun z hz => by
    have h1 : ‖z‖ ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ (norm_nonneg z) (hρ z hz) 2
    constructor <;> nlinarith [sq_nonneg ‖z‖]
  have hμ : μ.restrict Q ≤ canonicalBedfordTaylorMeasure Q _ hw := by
    have h := ma_add_normSq_ge hn (isLocallyBoundedPshOn_zero Q) one_pos (ρ ^ 2) hw
    rw [one_pow, mul_one] at h
    rw [hμdef, Measure.restrict_smul]
    exact (Measure.le_add_left le_rfl).trans h
  have hμD : μ (Q : Set (ComplexModel n)) ≠ ⊤ := by
    rw [hμdef, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hQb.measure_lt_top.ne
  have he := hU.localEnergy_ne_top (p := 1) zero_le_one
  have hmom := lintegral_neg_rpow_le hn hQb hU.psh hU.nonpos hU.tendsto_frontier hw (sq_nonneg ρ)
    hwb hμ hμD one_pos he
  have hlhs : ∫⁻ z in (Q : Set (ComplexModel n)), ENNReal.ofReal ((-U z) ^ (1 : ℝ)) ∂μ =
      ENNReal.ofReal (mongeAmpereConst n) *
        ∫⁻ x in (Q : Set (ComplexModel n)), ENNReal.ofReal (-U x) := by
    simp only [Real.rpow_one]
    rw [hμdef, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]
  rw [hlhs] at hmom
  set E : ℝ := energyMomentConst n 1 (μ (Q : Set (ComplexModel n))).toReal (ρ ^ 2) with hEdef
  have hE0 : 0 ≤ E := energyMomentConst_nonneg n zero_le_one ENNReal.toReal_nonneg (sq_nonneg ρ)
  have hpow : (localEnergy Q 1 U hU.psh).toReal ^ ((1 : ℝ) / ((n : ℝ) + 1)) ≤
      C ^ (1 / ((n : ℝ) + 1)) :=
    Real.rpow_le_rpow ENNReal.toReal_nonneg hC (by positivity)
  have h2 : ENNReal.ofReal (mongeAmpereConst n) *
      ∫⁻ x in (Q : Set (ComplexModel n)), ENNReal.ofReal (-U x) ≤
      ENNReal.ofReal (mongeAmpereConst n) *
        ENNReal.ofReal (E * C ^ (1 / ((n : ℝ) + 1)) / mongeAmpereConst n) := by
    rw [← ENNReal.ofReal_mul hcn.le, mul_div_cancel₀ _ hcn.ne']
    exact hmom.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hpow hE0))
  exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr hcn).ne' ENNReal.ofReal_ne_top).mp h2

/-- **The convolution approximants have a bounded limit with zero boundary values** (FPT,
Steps 1–3 of the proof of `thm:compact-bounded-subsolution-ball-dirichlet`, convolution variant on
a polydisk, up to the identification of the equation). -/
theorem exists_approximants_bounded_limit (hn : 0 < n) (a : ComplexModel n) {R : ℝ} (hR : 0 < R)
    (α : Measure (ComplexModel n)) [IsFiniteMeasure α] {K : Set (ComplexModel n)}
    (hK : IsCompact K) (hKQ : K ⊆ polydiskAt a R) (hαK : α Kᶜ = 0) {w : ComplexModel n → ℝ}
    (hw : IsLocallyBoundedPshOn (polydiskAtOpens a R) w) {b M : ℝ} (hM : 0 ≤ M)
    (hwb : ∀ z ∈ polydiskAt a R, b ≤ w z ∧ w z ≤ b + M)
    (hα : α.restrict (polydiskAt a R) ≤
      canonicalBedfordTaylorMeasure (polydiskAtOpens a R) w hw) :
    ∃ (r : ℝ) (hr : 0 < r) (χ : ComplexModel n → ℝ) (U : ℕ → ComplexModel n → ℝ)
      (hA : IsKolodziejApprox (polydiskAtOpens a R) α U) (σ : ℕ → ℕ) (u : ComplexModel n → ℝ),
      Continuous χ ∧ (∀ z, 0 ≤ χ z ∧ χ z ≤ 1) ∧
      (∀ j, canonicalBedfordTaylorMeasure (polydiskAtOpens a R) (U j) (hA.cegrell j).psh =
        (volume.restrict (polydiskAt a R)).withDensity
          (fun z => ENNReal.ofReal (convDensity α r hr j z +
            mongeAmpereConst n * ((j : ℝ) + 1)⁻¹ * χ z ^ n))) ∧
      StrictMono σ ∧ IsLocallyBoundedPshOn (polydiskAtOpens a R) u ∧
      (∀ z ∈ polydiskAt a R, -(M + 1) ≤ u z ∧ u z ≤ 0) ∧
      (∀ ζ ∈ frontier (polydiskAt a R), Tendsto u (𝓝[polydiskAt a R] ζ) (𝓝 0)) ∧
      ∀ L : Set (ComplexModel n), IsCompact L → L ⊆ polydiskAt a R →
        Tendsto (fun k => ∫⁻ x in L, ENNReal.ofReal |U (σ k) x - u x|) atTop (𝓝 0) := by
  classical
  obtain ⟨r, hr, χ, F, U, hU, C, h2r, hχs, hχ01, hχc, hF, hFeq, hMA, hweak, hC⟩ :=
    exists_convolution_approximants hn a hR α hK hKQ hαK hw hM hwb hα
  set Q : Opens (ComplexModel n) := polydiskAtOpens a R with hQdef
  have hQQ : (Q : Set (ComplexModel n)) = polydiskAt a R := rfl
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
    -- the error term
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
  have hconst : IsLocallyBoundedPshOn Q fun _ => (-T₀ : ℝ) := by
    simpa using IsLocallyBoundedPshOn.add_const (isLocallyBoundedPshOn_zero Q) (-T₀)
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
  refine ⟨r, hr, χ, U, hA, σ, u, hχs.continuous, hχ01, hMA', hσ, hu,
    fun z hz => ⟨(hWb z hz).1.trans (huW z hz), hu0 z hz⟩, fun ζ hζ => ?_, hulim⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (hWfr ζ hζ) tendsto_const_nhds ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with z hz using huW z hz
  · filter_upwards [self_mem_nhdsWithin] with z hz using hu0 z hz

end SGPT.Envelopes.MADirichlet
