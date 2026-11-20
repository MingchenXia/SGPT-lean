import SGPT.Envelopes.MADirichlet6Holder
import SGPT.Envelopes.MADirichletMixed

/-!
# Dinew's inequality for Kołodziej solutions on a polydisk (FPT Step 2)

Xia, *Foundations of pluripotential theory* (FPT), `thm:bounded-multifactor-common-measure`,
Step 2, on a polydisk `Q = a + R·P` and in the convolution variant of lanes MA-DIR2–MA-DIR5:

Let `v₁, …, vₙ` be plurisubharmonic on `Q` with `-B ≤ vᵢ ≤ 0`, `K ⊆ Q` compact,
`αᵢ = 𝟙_K (ddᶜvᵢ)ⁿ`, and `Aᵢ ∈ ℰ₀(Q)` the Kołodziej solutions of `(ddᶜAᵢ)ⁿ = αᵢ`. If
`(ddᶜvᵢ)ⁿ ≥ fᵢ μ` on `K`, then `ddᶜA₁ ∧ ⋯ ∧ ddᶜAₙ ≥ 𝟙_K (∏ᵢ fᵢ^{1/n}) μ`
(`mixed_ge_restrict_of_kolodziej`).

*Proof.* Put `λ = 𝟙_K (∏ᵢ fᵢ^{1/n}) μ`; by Hölder, `∫ g dλ ≤ ∏ᵢ (∫ g dαᵢ)^{1/n}` (so `λ` is finite).
Fix one kernel radius `r` with `cthickening (4r) K ⊆ Q` and let `U_{i,j}` be the convolution
approximants of `αᵢ` with this radius (`exists_kolodziejApprox_radius`), so
`(ddᶜU_{i,j})ⁿ ≥ (αᵢ ∗ ρⱼ) dV`. Then:

* `U_{i,j} → Aᵢ` in `L¹_loc` (whole sequence, `tendsto_localL1_of_isKolodziejApprox`) and in
  capacity (`tendsto_relCapacity_abs_sub_of_approximants`), so for every level `T ≥ B` the mixed
  products of the truncations `max(U_{i,j}, -T)` converge weakly to `⋀ᵢ ddᶜAᵢ`
  (`tendsto_integral_mixed_of_relCapacity`);
* `⋀ᵢ ddᶜU_{i,j} ≥ ∏ᵢ (αᵢ ∗ ρⱼ)^{1/n} dV ≥ (λ ∗ ρⱼ) dV` (`mixed_ge_withDensity` and
  `ofReal_convDensity_le_prod`; `withDensity_le_mixed_of_convDensity`);
* on `G = ⋂ᵢ {U_{i,j} > -T}` the truncated and untruncated mixed products agree (TN's plurifine
  locality `localMixedBedfordTaylorMeasure_max_const_locality`), and
  `(λ ∗ ρⱼ) dV (Gᶜ) ≤ ∑ᵢ ∑ₖ (ddᶜU_{k,j})ⁿ{U_{i,j} ≤ -T}`, which is small uniformly in `j` for large
  `T` (capacity of sublevel sets of functions of bounded energy and the capacity modulus
  `ma_le_relCapacity_add_of_localEnergy_le`; FPT controls this by the energy bound of the
  approximants as well);
* `(λ ∗ ρⱼ) dV → λ` weakly (`tendsto_integral_mul_convDensity`).
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
open SGPT.NPP.LogConcavityDinew

variable {n : ℕ}

/-- **Lower bound for the mixed product of the approximants** (FPT, Step 2: "on `Int Q`,
`⋀ᵢ ddᶜA_{i,l,j} ≥ ∏ᵢ (αᵢ(Q)/|Q|)^{1/n} dV ≥ λ_{l,j}`", convolution variant): if
`(ddᶜUᵢ)ⁿ ≥ (αᵢ ∗ ρⱼ) dV` on `Q` for all `i` and `∫ g dν ≤ ∏ᵢ (∫ g dαᵢ)^{1/n}` for all
measurable `g ≥ 0`, then `ddᶜU₁ ∧ ⋯ ∧ ddᶜUₙ ≥ (ν ∗ ρⱼ) dV` on `Q`. -/
theorem withDensity_le_mixed_of_convDensity (hn : 0 < n) {Q : Opens (ComplexModel n)}
    {U : Fin n → ComplexModel n → ℝ} (hU : IsLocallyBoundedMixedPshOn Q U)
    {α : Fin n → Measure (ComplexModel n)} [∀ i, IsFiniteMeasure (α i)]
    {ν : Measure (ComplexModel n)} [IsFiniteMeasure ν]
    (hνα : ∀ g : ComplexModel n → ℝ≥0∞, Measurable g →
      ∫⁻ x, g x ∂ν ≤ ∏ i, (∫⁻ x, g x ∂α i) ^ ((n : ℝ)⁻¹))
    {r : ℝ} (hr : 0 < r) (j : ℕ)
    (hMA : ∀ i, (volume.restrict (Q : Set (ComplexModel n))).withDensity
        (fun z => ENNReal.ofReal (convDensity (α i) r hr j z)) ≤
      canonicalBedfordTaylorMeasure Q (U i) (hU i)) :
    (volume.restrict (Q : Set (ComplexModel n))).withDensity
        (fun z => ENNReal.ofReal (convDensity ν r hr j z)) ≤
      canonicalMixedBedfordTaylorMeasure Q U hU := by
  set c := mongeAmpereConst n with hcdef
  have hc : 0 < c := mongeAmpereConst_pos
  have hninv : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
  set g : Fin n → ComplexModel n → ℝ := fun i z => convDensity (α i) r hr j z with hgdef
  have hg0 : ∀ i z, 0 ≤ g i z := fun i z => convDensity_nonneg (α i) hr j z
  have hmix := mixed_ge_withDensity hn hU (f := fun i z => g i z / c)
    (fun i => ((contDiff_convDensity (α i) hr j).continuous.div_const c).continuousOn)
    (fun i z _ => div_nonneg (hg0 i z) hc.le) (fun i => by
      have e : (fun z => ENNReal.ofReal (c * (g i z / c))) =
          fun z => ENNReal.ofReal (convDensity (α i) r hr j z) := by
        funext z
        rw [mul_div_cancel₀ _ hc.ne']
      rw [e]
      exact hMA i)
  refine le_trans (withDensity_mono (Eventually.of_forall fun z => ?_)) hmix
  rw [mul_prod_div_rpow_inv hn hc fun i => hg0 i z,
    ENNReal.ofReal_prod_of_nonneg fun i _ => Real.rpow_nonneg (hg0 i z) _]
  simp_rw [← ENNReal.ofReal_rpow_of_nonneg (hg0 _ z) hninv]
  exact ofReal_convDensity_le_prod hνα hr j z

/-- **Dinew's inequality for the Kołodziej solutions of `𝟙_K (ddᶜvᵢ)ⁿ`** (FPT
`thm:bounded-multifactor-common-measure`, Step 2 for a fixed compact set, on a polydisk). -/
theorem mixed_ge_restrict_of_kolodziej (hn : 0 < n) (a : ComplexModel n) {R : ℝ} (hR : 0 < R)
    {v : Fin n → ComplexModel n → ℝ} (hv : IsLocallyBoundedMixedPshOn (polydiskAtOpens a R) v)
    {B : ℝ} (hB : 0 ≤ B) (hvb : ∀ i, ∀ z ∈ polydiskAt a R, -B ≤ v i z ∧ v i z ≤ 0)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKQ : K ⊆ polydiskAt a R)
    {A : Fin n → ComplexModel n → ℝ} (hA : ∀ i, IsCegrellE0 (polydiskAtOpens a R) (A i))
    (hAb : ∀ i, ∀ z ∈ polydiskAt a R, -B ≤ A i z)
    (hAMA : ∀ i, canonicalBedfordTaylorMeasure (polydiskAtOpens a R) (A i) (hA i).psh =
      (canonicalBedfordTaylorMeasure (polydiskAtOpens a R) (v i) (hv i)).restrict K)
    (μ : Measure (ComplexModel n)) {f : Fin n → ComplexModel n → ℝ≥0∞}
    (hf : ∀ i, Measurable (f i))
    (hfμ : ∀ i, (μ.withDensity (f i)).restrict K ≤
      canonicalBedfordTaylorMeasure (polydiskAtOpens a R) (v i) (hv i)) :
    (μ.withDensity fun z => ∏ i, f i z ^ ((n : ℝ)⁻¹)).restrict K ≤
      canonicalMixedBedfordTaylorMeasure (polydiskAtOpens a R) A (fun i => (hA i).psh) := by
  classical
  set Q : Opens (ComplexModel n) := polydiskAtOpens a R with hQdef
  have hQb : Bornology.IsBounded (Q : Set (ComplexModel n)) := isBounded_polydiskAt a hR
  have hQm : MeasurableSet (Q : Set (ComplexModel n)) := Q.isOpen.measurableSet
  set c := mongeAmpereConst n with hcdef
  have hc : 0 < c := mongeAmpereConst_pos
  have hninv : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
  -- the measures `αᵢ = 𝟙_K (ddᶜvᵢ)ⁿ`
  set α : Fin n → Measure (ComplexModel n) :=
    fun i => (canonicalBedfordTaylorMeasure Q (v i) (hv i)).restrict K with hαdef
  have hαfin : ∀ i, IsFiniteMeasure (α i) := fun i =>
    ⟨by rw [Measure.restrict_apply_univ]
        exact (isBTLimit_canonicalBedfordTaylorMeasure (hv i)).2.1 K hK hKQ⟩
  have := hαfin
  have hαK : ∀ i, α i Kᶜ = 0 := fun i => by
    rw [Measure.restrict_apply hK.isClosed.measurableSet.compl, compl_inter_self, measure_empty]
  have hαle : ∀ i, (α i).restrict (polydiskAt a R) ≤ canonicalBedfordTaylorMeasure Q (v i) (hv i) :=
    fun i => Measure.restrict_le_self.trans Measure.restrict_le_self
  have hvb' : ∀ i, ∀ z ∈ polydiskAt a R, -B ≤ v i z ∧ v i z ≤ -B + B := fun i z hz =>
    ⟨(hvb i z hz).1, by linarith [(hvb i z hz).2]⟩
  -- the measure `λ = 𝟙_K (∏ᵢ fᵢ^{1/n}) μ`
  set lam : Measure (ComplexModel n) :=
    (μ.withDensity fun z => ∏ i, f i z ^ ((n : ℝ)⁻¹)).restrict K with hlamdef
  have hfα : ∀ i, (μ.withDensity (f i)).restrict K ≤ α i := fun i => by
    have h := Measure.restrict_mono (le_refl K) (hfμ i)
    rwa [Measure.restrict_restrict hK.measurableSet, inter_self] at h
  have hHolder : ∀ g : ComplexModel n → ℝ≥0∞, Measurable g →
      ∫⁻ x, g x ∂lam ≤ ∏ i, (∫⁻ x, g x ∂α i) ^ ((n : ℝ)⁻¹) := fun g hg =>
    lintegral_withDensity_prod_rpow_le hn μ hK.measurableSet hf hfα hg
  have hlamfin : IsFiniteMeasure lam := by
    refine ⟨?_⟩
    have h := hHolder (fun _ => 1) measurable_const
    simp only [lintegral_one] at h
    exact h.trans_lt (ENNReal.prod_lt_top fun i _ =>
      ENNReal.rpow_lt_top_of_nonneg hninv (measure_ne_top _ _))
  have hlamK : lam Kᶜ = 0 := by
    rw [hlamdef, Measure.restrict_apply hK.isClosed.measurableSet.compl, compl_inter_self,
      measure_empty]
  -- a common kernel radius
  obtain ⟨δ, hδ, hδQ⟩ := hK.exists_cthickening_subset_open (isOpen_polydiskAt a R) hKQ
  set r : ℝ := δ / 4 with hrdef
  have hr : 0 < r := by positivity
  have h4r : cthickening (4 * r) K ⊆ polydiskAt a R := by
    have e : 4 * r = δ := by rw [hrdef]; ring
    rw [e]; exact hδQ
  -- the approximants
  choose χ U hAU hχc hχ01 hUMA using fun i => exists_kolodziejApprox_radius hn a hR (α i) hK
    (hαK i) hr h4r (hv i) hB (hvb' i) (hαle i)
  have hUc : ∀ i j, IsCegrellE0 Q (U i j) := fun i j => (hAU i).cegrell j
  have hUfin : ∀ i j, IsFiniteMeasure (canonicalBedfordTaylorMeasure Q (U i j) (hUc i j).psh) :=
    fun i j => (hUc i j).isFiniteMeasure
  -- convergence of the whole sequence to `Aᵢ`, in `L¹_loc` and in capacity
  have hlim : ∀ i, ∀ L : Set (ComplexModel n), IsCompact L → L ⊆ Q →
      Tendsto (fun j => ∫⁻ x in L, ENNReal.ofReal |U i j x - A i x|) atTop (𝓝 0) :=
    fun i L hL hLQ => tendsto_localL1_of_isKolodziejApprox hn a hR hK hKQ (hαK i) (hv i) hB
      (hvb' i) (hαle i) (hAU i) (hA i) (hAMA i) hL hLQ
  have hAbd : ∀ i, ∀ z ∈ Q, -B ≤ A i z ∧ A i z ≤ 0 := fun i z hz =>
    ⟨hAb i z hz, (hA i).nonpos z hz⟩
  have hcapA : ∀ i, ∀ L : Set (ComplexModel n), IsCompact L → L ⊆ Q → ∀ b : ℝ, 0 < b →
      Tendsto (fun j => relCapacity Q (L ∩ {z | b < |U i j z - A i z|})) atTop (𝓝 0) :=
    fun i L hL hLQ b hb => tendsto_relCapacity_abs_sub_of_approximants hn (hAU i) (hA i).psh
      (hAbd i) strictMono_id (fun L' hL' hL'Q => hlim i L' hL' hL'Q) hL hLQ hb
  -- the truncated mixed products converge
  have hconstT : ∀ T : ℝ, IsLocallyBoundedPshOn Q fun _ => (-T : ℝ) := fun T => by
    simpa using IsLocallyBoundedPshOn.add_const (isLocallyBoundedPshOn_zero Q) (-T)
  set W : ℝ → ℕ → Fin n → ComplexModel n → ℝ := fun T j i z => max (U i j z) (-T) with hWdef
  have hW : ∀ T j, IsLocallyBoundedMixedPshOn Q (W T j) := fun T j i =>
    IsLocallyBoundedPshOn.max (hUc i j).psh (hconstT T)
  have hAm : IsLocallyBoundedMixedPshOn Q A := fun i => (hA i).psh
  have hmixedT : ∀ T : ℝ, B ≤ T → 0 < T → ∀ h : ComplexModel n → ℝ, Continuous h →
      HasCompactSupport h → tsupport h ⊆ Q →
      Tendsto (fun j => ∫ z, h z ∂canonicalMixedBedfordTaylorMeasure Q (W T j) (hW T j)) atTop
        (𝓝 (∫ z, h z ∂canonicalMixedBedfordTaylorMeasure Q A hAm)) := by
    intro T hBT hT h hc hcs hsupp
    refine tendsto_integral_mixed_of_relCapacity hcs.isCompact hsupp (hW T) hAm hT.le
      (fun j i z hz => ⟨le_max_right _ _, max_le (((hUc i j).nonpos z hz).trans hT.le)
        (by linarith)⟩)
      (fun i z hz => ⟨by linarith [hAb i z hz], ((hA i).nonpos z hz).trans hT.le⟩) ?_ hc hcs
      subset_rfl
    intro i V hVQ T' hT' hT'V b hb
    have h := tendsto_relCapacity_of_le_opens hVQ hQb hT' hT'V
      (hcapA i T' hT' (hT'V.trans hVQ) b hb)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => zero_le)
      fun j => relCapacity_mono ?_
    rintro z ⟨hzT, hz⟩
    exact ⟨hzT, lt_of_lt_of_le hz
      (abs_max_neg_sub_le (by linarith [hAb i z (hVQ (hT'V hzT))]))⟩
  -- the measures `(λ ∗ ρⱼ) dV`
  have := hlamfin
  set D : ℕ → Measure (ComplexModel n) := fun j =>
    (volume.restrict (polydiskAt a R)).withDensity
      (fun z => ENNReal.ofReal (convDensity lam r hr j z)) with hDdef
  have hUm : ∀ j, IsLocallyBoundedMixedPshOn Q fun i => U i j := fun j i => (hUc i j).psh
  have hDle : ∀ j, D j ≤ canonicalMixedBedfordTaylorMeasure Q (fun i => U i j) (hUm j) := by
    intro j
    refine withDensity_le_mixed_of_convDensity hn (hUm j) hHolder hr j fun i => ?_
    change _ ≤ canonicalBedfordTaylorMeasure Q (U i j) ((hAU i).cegrell j).psh
    rw [hUMA i j]
    exact withDensity_mono (Eventually.of_forall fun z => ENNReal.ofReal_le_ofReal
      (le_add_of_nonneg_right (mul_nonneg (by positivity) (pow_nonneg (hχ01 i z).1 n))))
  have hpt : ∀ j z, ENNReal.ofReal (convDensity lam r hr j z) ≤
      ∑ k, ENNReal.ofReal (convDensity (α k) r hr j z +
        mongeAmpereConst n * ((j : ℝ) + 1)⁻¹ * χ k z ^ n) := by
    intro j z
    calc ENNReal.ofReal (convDensity lam r hr j z)
        ≤ ∏ k, ENNReal.ofReal (convDensity (α k) r hr j z) ^ ((n : ℝ)⁻¹) :=
          ofReal_convDensity_le_prod hHolder hr j z
      _ ≤ ∑ k, ENNReal.ofReal (convDensity (α k) r hr j z) := prod_rpow_inv_le_sum hn _
      _ ≤ _ := Finset.sum_le_sum fun k _ => ENNReal.ofReal_le_ofReal
          (le_add_of_nonneg_right (mul_nonneg (by positivity) (pow_nonneg (hχ01 k z).1 n)))
  have hDsum : ∀ j E, MeasurableSet E →
      D j E ≤ ∑ k, canonicalBedfordTaylorMeasure Q (U k j) (hUc k j).psh E := by
    intro j E hE
    have hmk : ∀ k, Measurable fun z => ENNReal.ofReal (convDensity (α k) r hr j z +
        mongeAmpereConst n * ((j : ℝ) + 1)⁻¹ * χ k z ^ n) := fun k =>
      ENNReal.measurable_ofReal.comp (((contDiff_convDensity (α k) hr j).continuous.add
        (continuous_const.mul ((hχc k).pow n))).measurable)
    calc D j E = ∫⁻ z in E, ENNReal.ofReal (convDensity lam r hr j z)
          ∂volume.restrict (polydiskAt a R) := withDensity_apply _ hE
      _ ≤ ∫⁻ z in E, ∑ k, ENNReal.ofReal (convDensity (α k) r hr j z +
            mongeAmpereConst n * ((j : ℝ) + 1)⁻¹ * χ k z ^ n) ∂volume.restrict (polydiskAt a R) :=
          lintegral_mono fun z => hpt j z
      _ = ∑ k, ∫⁻ z in E, ENNReal.ofReal (convDensity (α k) r hr j z +
            mongeAmpereConst n * ((j : ℝ) + 1)⁻¹ * χ k z ^ n) ∂volume.restrict (polydiskAt a R) :=
          lintegral_finsetSum _ fun k _ => hmk k
      _ = ∑ k, canonicalBedfordTaylorMeasure Q (U k j) (hUc k j).psh E :=
          Finset.sum_congr rfl fun k _ => by rw [hUMA k j, withDensity_apply _ hE]
  have hDfin : ∀ j, IsFiniteMeasure (D j) := fun j => ⟨by
    refine (hDsum j univ MeasurableSet.univ).trans_lt (ENNReal.sum_lt_top.mpr fun k _ => ?_)
    exact measure_lt_top _ _⟩
  -- `∫ h d(λ ∗ ρⱼ) dV = ∫ h (λ ∗ ρⱼ)`
  have hDint : ∀ j, ∀ h : ComplexModel n → ℝ,
      ∫ z, h z ∂D j = ∫ z, h z * convDensity lam r hr j z := by
    intro j h
    have hdm : Measurable fun z => ENNReal.ofReal (convDensity lam r hr j z) :=
      ENNReal.measurable_ofReal.comp (contDiff_convDensity lam hr j).continuous.measurable
    rw [hDdef, integral_withDensity_eq_integral_toReal_smul hdm
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    have e : ∀ z, (ENNReal.ofReal (convDensity lam r hr j z)).toReal • h z =
        h z * convDensity lam r hr j z := fun z => by
      rw [ENNReal.toReal_ofReal (convDensity_nonneg lam hr j z), smul_eq_mul, mul_comm]
    simp_rw [e]
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => ?_
    have hzL : z ∉ cthickening r K := fun h' =>
      hz (h4r (cthickening_mono (by linarith) K h'))
    rw [convDensity_eq_zero_of_notMem lam hlamK hr j hzL, mul_zero]
  -- the bad sets `{U_{i,j} ≤ -T}` have small mass, uniformly in `j`
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ k j, (localEnergy Q 1 (U k j) (hUc k j).psh).toReal ≤ C := by
    choose C hC using fun k => (hAU k).energy
    exact ⟨∑ k, |C k|, fun k j => (hC k j).trans ((le_abs_self _).trans
      (Finset.single_le_sum (fun i _ => abs_nonneg (C i)) (Finset.mem_univ k)))⟩
  have hC0 : 0 ≤ C := ENNReal.toReal_nonneg.trans (hC ⟨0, hn⟩ 0)
  have hbad : ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, B ≤ T ∧ 0 < T ∧ ∀ i k j,
      canonicalBedfordTaylorMeasure Q (U k j) (hUc k j).psh {z | z ∈ Q ∧ U i j z ≤ -T} ≤
        ENNReal.ofReal ε := by
    intro ε hε
    set s : ℝ := 2 * C / ε + 1 with hsdef
    have hs : 0 < s := by positivity
    have hCs : C / s ≤ ε / 2 := by
      rw [div_le_iff₀ hs, hsdef]
      have : ε / 2 * (2 * C / ε + 1) = C + ε / 2 := by field_simp
      rw [this]; linarith
    have hlimT : Tendsto (fun T : ℝ => s ^ n * (2 ^ ((n : ℝ) + 1) * (T / 2) ^ (-((n : ℝ) + 1))) * C)
        atTop (𝓝 0) := by
      have h1 : Tendsto (fun T : ℝ => (T / 2) ^ (-((n : ℝ) + 1))) atTop (𝓝 0) :=
        (tendsto_rpow_neg_atTop (by positivity)).comp (tendsto_id.atTop_div_const (by norm_num))
      simpa using ((h1.const_mul (2 ^ ((n : ℝ) + 1))).const_mul (s ^ n)).mul_const C
    obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp
      (hlimT.eventually (Iic_mem_nhds (by positivity : (0 : ℝ) < ε / 2)))
    set T : ℝ := max T₀ (max B 1) with hTdef
    have hT1 : 1 ≤ T := (le_max_right B 1).trans (le_max_right _ _)
    have hT : 0 < T := by linarith
    refine ⟨T, (le_max_left B 1).trans (le_max_right _ _), hT, fun i k j => ?_⟩
    set E : Set (ComplexModel n) := {z | z ∈ Q ∧ U i j z ≤ -T} with hEdef
    have hEQ : E ⊆ Q := fun z hz => hz.1
    have hcap : relCapacity Q E ≤ ENNReal.ofReal (2 ^ ((n : ℝ) + 1) * (T / 2) ^ (-((n : ℝ) + 1))) *
        ENNReal.ofReal C := by
      refine (relCapacity_mono ?_).trans ((relCapacity_sublevel_le_localEnergy hn hQb (hUc i j).psh
        (hUc i j).tendsto_frontier one_pos (by positivity : (0 : ℝ) < T / 2)).trans ?_)
      · rintro z ⟨hzQ, hz⟩
        exact ⟨hzQ, by linarith⟩
      · refine mul_le_mul' le_rfl ?_
        rw [← ENNReal.ofReal_toReal ((hUc i j).localEnergy_ne_top zero_le_one)]
        exact ENNReal.ofReal_le_ofReal (hC i j)
    have hma := ma_le_relCapacity_add_of_localEnergy_le hn hQb
      (φ := fun p : Fin n × ℕ => U p.1 p.2) (fun p => hUc p.1 p.2) (fun p => hC p.1 p.2) (k, j)
      hs hEQ
    have hval := hT₀ T (le_max_left _ _)
    calc canonicalBedfordTaylorMeasure Q (U k j) (hUc k j).psh E
        ≤ ENNReal.ofReal (s ^ n) * relCapacity Q E + ENNReal.ofReal (C / s) := hma
      _ ≤ ENNReal.ofReal (s ^ n) * (ENNReal.ofReal (2 ^ ((n : ℝ) + 1) *
            (T / 2) ^ (-((n : ℝ) + 1))) * ENNReal.ofReal C) + ENNReal.ofReal (ε / 2) :=
          add_le_add (mul_le_mul' le_rfl hcap) (ENNReal.ofReal_le_ofReal hCs)
      _ = ENNReal.ofReal (s ^ n * (2 ^ ((n : ℝ) + 1) * (T / 2) ^ (-((n : ℝ) + 1))) * C) +
            ENNReal.ofReal (ε / 2) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
            ← mul_assoc]
      _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
          add_le_add (ENNReal.ofReal_le_ofReal hval) le_rfl
      _ = ENNReal.ofReal ε := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf
  -- the estimate at level `T` and index `j`
  have hstep : ∀ T : ℝ, 0 < T → ∀ j, ∀ h : ComplexModel n → ℝ, Continuous h →
      HasCompactSupport h → tsupport h ⊆ Q → (∀ z, 0 ≤ h z) → ∀ Ch : ℝ, (∀ z, |h z| ≤ Ch) →
      ∫ z, h z ∂D j ≤ ∫ z, h z ∂canonicalMixedBedfordTaylorMeasure Q (W T j) (hW T j) +
        Ch * ∑ i, ∑ k, (canonicalBedfordTaylorMeasure Q (U k j) (hUc k j).psh
          {z | z ∈ Q ∧ U i j z ≤ -T}).toReal := by
    intro T hT j h hc hcs hsupp h0 Ch hCh
    have := hDfin j
    set G : Set (ComplexModel n) := {z | z ∈ Q ∧ ∀ i, -T < U i j z} with hGdef
    have hGm : MeasurableSet G := by
      have e : G = (Q : Set (ComplexModel n)) ∩ ⋂ i, {z | z ∈ Q ∧ -T < U i j z} := by
        ext z
        simp only [hGdef, mem_ofPred_eq, mem_inter_iff, mem_iInter]
        constructor
        · rintro ⟨hz, hzi⟩; exact ⟨hz, fun i => ⟨hz, hzi i⟩⟩
        · rintro ⟨hz, hzi⟩; exact ⟨hz, fun i => (hzi i).2⟩
      rw [e]
      exact hQm.inter (MeasurableSet.iInter fun i => measurableSet_superlevel (hUc i j).psh (-T))
    -- plurifine locality on `G`
    have hloc := localMixedBedfordTaylorMeasure_max_const_locality
      (canonicalMixedBedfordTaylorMeasure_spec Q (fun i => U i j) (hUm j))
      (canonicalMixedBedfordTaylorMeasure_spec Q (W T j) (hW T j)) (-T)
      (fun i => fun z _ => rfl)
    have hGle : (D j).restrict G ≤ canonicalMixedBedfordTaylorMeasure Q (W T j) (hW T j) := by
      calc (D j).restrict G ≤ (canonicalMixedBedfordTaylorMeasure Q (fun i => U i j)
            (hUm j)).restrict G := Measure.restrict_mono le_rfl (hDle j)
        _ = (canonicalMixedBedfordTaylorMeasure Q (W T j) (hW T j)).restrict G := hloc.symm
        _ ≤ _ := Measure.restrict_le_self
    have hint : Integrable h (D j) := (integrable_const Ch).mono' hc.aestronglyMeasurable
      (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hCh z)
    have hsplit : ∫ z, h z ∂D j = ∫ z, h z ∂(D j).restrict G + ∫ z, h z ∂(D j).restrict Gᶜ := by
      rw [← integral_add_measure hint.restrict hint.restrict, Measure.restrict_add_restrict_compl hGm]
    have h1 : ∫ z, h z ∂(D j).restrict G ≤
        ∫ z, h z ∂canonicalMixedBedfordTaylorMeasure Q (W T j) (hW T j) :=
      integral_le_integral_of_le hGle
        (canonicalMixedBedfordTaylorMeasure_spec Q (W T j) (hW T j)).2.2.1 hc hcs hsupp h0
    have h2 : ∫ z, h z ∂(D j).restrict Gᶜ ≤ Ch * ((D j) Gᶜ).toReal := by
      have hnb := norm_integral_le_of_norm_le_const (μ := (D j).restrict Gᶜ) (f := h) (C := Ch)
        (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hCh x)
      rw [Real.norm_eq_abs] at hnb
      have h' : |∫ z, h z ∂(D j).restrict Gᶜ| ≤ Ch * ((D j) Gᶜ).toReal := by
        simpa [Measure.real, Measure.restrict_apply_univ] using hnb
      exact (le_abs_self _).trans h'
    -- the mass of `Gᶜ`
    have hDQ : D j (Q : Set (ComplexModel n))ᶜ = 0 := by
      rw [hDdef, withDensity_apply _ hQm.compl]
      refine setLIntegral_measure_zero _ _ ?_
      rw [Measure.restrict_apply hQm.compl]
      exact (congrArg volume (compl_inter_self (Q : Set (ComplexModel n)))).trans measure_empty
    have hEm : ∀ i, MeasurableSet {z | z ∈ Q ∧ U i j z ≤ -T} := fun i => by
      have e : {z | z ∈ Q ∧ U i j z ≤ -T} =
          (Q : Set (ComplexModel n)) \ {z | z ∈ Q ∧ -T < U i j z} := by
        ext z
        simp only [mem_ofPred_eq, Set.mem_sdiff, not_and, not_lt]
        constructor
        · rintro ⟨hz, h⟩; exact ⟨hz, fun _ => h⟩
        · rintro ⟨hz, h⟩; exact ⟨hz, h hz⟩
      rw [e]
      exact hQm.diff (measurableSet_superlevel (hUc i j).psh (-T))
    have hGc : Gᶜ ⊆ (Q : Set (ComplexModel n))ᶜ ∪ ⋃ i, {z | z ∈ Q ∧ U i j z ≤ -T} := by
      intro z hz
      by_cases hzQ : z ∈ Q
      · right
        by_contra hcon
        simp only [mem_iUnion, mem_ofPred_eq, not_exists, not_and, not_le] at hcon
        exact hz ⟨hzQ, fun i => hcon i hzQ⟩
      · exact Or.inl hzQ
    have hDGc : (D j) Gᶜ ≤ ∑ i, ∑ k,
        canonicalBedfordTaylorMeasure Q (U k j) (hUc k j).psh {z | z ∈ Q ∧ U i j z ≤ -T} := by
      calc (D j) Gᶜ ≤ D j ((Q : Set (ComplexModel n))ᶜ ∪ ⋃ i, {z | z ∈ Q ∧ U i j z ≤ -T}) :=
            measure_mono hGc
        _ ≤ D j (Q : Set (ComplexModel n))ᶜ + D j (⋃ i, {z | z ∈ Q ∧ U i j z ≤ -T}) :=
            measure_union_le _ _
        _ ≤ 0 + ∑ i, D j {z | z ∈ Q ∧ U i j z ≤ -T} :=
            add_le_add hDQ.le (measure_iUnion_fintype_le _ _)
        _ ≤ ∑ i, ∑ k, canonicalBedfordTaylorMeasure Q (U k j) (hUc k j).psh
              {z | z ∈ Q ∧ U i j z ≤ -T} := by
            rw [zero_add]
            exact Finset.sum_le_sum fun i _ => hDsum j _ (hEm i)
    have hfinsum : ∀ i k, canonicalBedfordTaylorMeasure Q (U k j) (hUc k j).psh
        {z | z ∈ Q ∧ U i j z ≤ -T} ≠ ⊤ := fun i k => measure_ne_top _ _
    have hDGc' : ((D j) Gᶜ).toReal ≤ ∑ i, ∑ k, (canonicalBedfordTaylorMeasure Q (U k j)
        (hUc k j).psh {z | z ∈ Q ∧ U i j z ≤ -T}).toReal := by
      refine (ENNReal.toReal_mono ?_ hDGc).trans (le_of_eq ?_)
      · exact ENNReal.sum_ne_top.mpr fun i _ => ENNReal.sum_ne_top.mpr fun k _ => hfinsum i k
      · rw [ENNReal.toReal_sum fun i _ => ENNReal.sum_ne_top.mpr fun k _ => hfinsum i k]
        exact Finset.sum_congr rfl fun i _ => ENNReal.toReal_sum fun k _ => hfinsum i k
    have hCh0 : 0 ≤ Ch := (abs_nonneg _).trans (hCh 0)
    calc ∫ z, h z ∂D j = ∫ z, h z ∂(D j).restrict G + ∫ z, h z ∂(D j).restrict Gᶜ := hsplit
      _ ≤ ∫ z, h z ∂canonicalMixedBedfordTaylorMeasure Q (W T j) (hW T j) +
          Ch * ((D j) Gᶜ).toReal := add_le_add h1 h2
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hDGc' hCh0)
  -- the integral inequality for nonnegative test functions
  have htest : ∀ h : ComplexModel n → ℝ, Continuous h → HasCompactSupport h →
      tsupport h ⊆ (Q : Set (ComplexModel n)) → (∀ z, 0 ≤ h z) →
      ∫ z, h z ∂lam ≤ ∫ z, h z ∂canonicalMixedBedfordTaylorMeasure Q A hAm := by
    intro h hc hcs hsupp h0
    obtain ⟨Ch, hCh⟩ := hc.bounded_above_of_compact_support hcs
    have hCh' : ∀ z, |h z| ≤ Ch := fun z => by rw [← Real.norm_eq_abs]; exact hCh z
    have hCh0 : 0 ≤ Ch := (abs_nonneg _).trans (hCh' 0)
    have hDlim : Tendsto (fun j => ∫ z, h z ∂D j) atTop (𝓝 (∫ z, h z ∂lam)) :=
      (tendsto_integral_mul_convDensity lam hr hc hcs).congr fun j => (hDint j h).symm
    refine le_of_forall_pos_le_add fun η hη => ?_
    set N : ℝ := (n : ℝ) * n with hNdef
    have hN : 0 ≤ N := by positivity
    set ε : ℝ := η / ((Ch + 1) * (N + 1)) with hεdef
    have hε : 0 < ε := by positivity
    obtain ⟨T, hBT, hT, hTbad⟩ := hbad ε hε
    have hj : ∀ j, ∫ z, h z ∂D j ≤
        ∫ z, h z ∂canonicalMixedBedfordTaylorMeasure Q (W T j) (hW T j) + Ch * (N * ε) := by
      intro j
      refine (hstep T hT j h hc hcs hsupp h0 Ch hCh').trans (add_le_add le_rfl
        (mul_le_mul_of_nonneg_left ?_ hCh0))
      calc ∑ i, ∑ k, (canonicalBedfordTaylorMeasure Q (U k j) (hUc k j).psh
            {z | z ∈ Q ∧ U i j z ≤ -T}).toReal ≤ ∑ _i : Fin n, ∑ _k : Fin n, ε :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ =>
              ENNReal.toReal_le_of_le_ofReal hε.le (hTbad i k j)
        _ = N * ε := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hNdef]
            ring
    have hle := le_of_tendsto_of_tendsto' hDlim
      ((hmixedT T hBT hT h hc hcs hsupp).add_const (Ch * (N * ε))) hj
    refine hle.trans (add_le_add le_rfl ?_)
    have e : Ch * (N * ε) = η * (Ch / (Ch + 1)) * (N / (N + 1)) := by
      rw [hεdef]; field_simp
    rw [e]
    have h1 : Ch / (Ch + 1) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
    have h2 : N / (N + 1) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
    calc η * (Ch / (Ch + 1)) * (N / (N + 1)) ≤ η * 1 * 1 := by
          gcongr
      _ = η := by ring
  -- from integrals to measures
  have hmixfin : ∀ K' : Set (ComplexModel n), IsCompact K' → K' ⊆ Q →
      canonicalMixedBedfordTaylorMeasure Q A hAm K' < ⊤ :=
    (canonicalMixedBedfordTaylorMeasure_spec Q A hAm).2.2.1
  have hlamfin' : ∀ K' : Set (ComplexModel n), IsCompact K' → K' ⊆ Q → lam K' < ⊤ :=
    fun _ _ _ => measure_lt_top lam _
  have hcmp : ∀ K' : Set (ComplexModel n), IsCompact K' → K' ⊆ Q →
      lam K' ≤ canonicalMixedBedfordTaylorMeasure Q A hAm K' := fun K' hK' hK'Q =>
    measure_le_of_testFunction_integral_le (U := Q) hlamfin' hmixfin htest hK' hK'Q
  have hres := restrict_le_of_isCompact_le hlamfin' hcmp
  have hlamQ : lam.restrict (Q : Set (ComplexModel n)) = lam := by
    exact Measure.restrict_eq_self_of_ae_mem
      ((ae_restrict_mem hK.measurableSet).mono fun x hx => hKQ hx)
  rw [hlamQ] at hres
  exact hres

end SGPT.Envelopes.MADirichlet
