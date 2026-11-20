import SGPT.TestCurve.SkodaIncComparison
import SGPT.Foundations.Analysis.Pending.StrongOpennessRegularRoute
import SGPT.Foundations.Analysis.Pending.StrongOpennessEnvelope

/-!
# The multiplier ideals of the obstacle of a filtration

Input of `SkodaInclusionIdeal` (the Skoda-division part of [RWN14, Theorem 7.10], used for
`rmk:PhongSturm`, chapter *Test curves*). For a filtration `𝓕` and `τ < τ(𝓕)`, the obstacle
`ψ_τ = usc sup_K K⁻¹ Γ^{𝓕,K}_τ` of `ex:RWN` is the regularized limit of the increasing sequence
`u_j = K_j⁻¹ Γ^{𝓕,K_j}_τ`, `K_j = (j+1)! m`, of `θ`-psh functions. If every member satisfies
`u_j ≤ φ + C_j` for a continuous `φ` (constants depending on `j`), then by the strong openness
theorem for increasing sequences (Guan–Zhou; Xia, *SGPT*, Theorem 1.4.4,
`SGPT.Foundations.Analysis.Pending.increasingStrongOpenness_ofRegularRoute`) the multiplier ideals
of `ψ_τ` are contained in those of `φ`: `𝓘(cψ_τ) ⊆ 𝓘(cφ)` for all `c > 0`
(`iOrderOnManifold_obstacle`).

Applied with `φ = d⁻¹ log |w|²` (`SkodaIncComparison`) this gives
`H⁰(X, L^k ⊗ 𝓘(kψ_τ)) ⊆ H⁰(X, L^k ⊗ 𝓘(M log |w|²))` for `M d ≤ k`
(`isIdealSection_familyLog_of_isMultiplierSection`).

## Main results

* `multiplierIntegrableAt_of_weight_le`: comparison of local weighted `L²` conditions.
* `iOrderOnManifold_of_le_add_of_continuous`: `u ≤ φ + C` with `φ` continuous gives
  `𝓘(cu) ⊆ 𝓘(cφ)`.
* `multiplierIdeal_scale_le`: `𝓘(k d⁻¹ φ) ⊆ 𝓘(M φ)` for `M d ≤ k`, `φ` bounded above.
* **`iOrderOnManifold_obstacle`**.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.TestCurve.SkodaInc

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Filter Set SGPT.Okounkov SGPT.LineBundle
open SGPT.TestCurve.TestConfig MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open scoped Topology ENNReal

/-! ### Comparison of weighted `L²` conditions -/

/-- If `e^{-c'ψ} ≤ A e^{-cφ}` near `z` and `ψ` is continuous there, a germ in `𝓘(cφ)_z` lies in
`𝓘(c'ψ)_z`. -/
theorem multiplierIntegrableAt_of_weight_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} {φ ψ : E → EReal} {c c' : ℝ}
    (hc' : 0 < c') {f : E → ℂ} {z : E} {U : Set E} (hU : IsOpen U) (hz : z ∈ U)
    (hψ : ContinuousOn ψ U) {A : ℝ≥0∞} (hA : A ≠ ⊤)
    (hw : ∀ y ∈ U, multiplierWeight c' (ψ y) ≤ A * multiplierWeight c (φ y))
    (hf : MultiplierIntegrableAt φ c f z μ) : MultiplierIntegrableAt ψ c' f z μ := by
  obtain ⟨-, V, hV, hzV, hfV, -, hint⟩ := hf
  have hVU : IsOpen (V ∩ U) := hV.inter hU
  refine ⟨hc', V ∩ U, hVU, ⟨hzV, hz⟩, hfV.mono inter_subset_left, ?_, ?_⟩
  · have h1 : AEMeasurable (fun y => ENNReal.ofReal (‖f y‖ ^ 2)) (μ.restrict (V ∩ U)) :=
      ENNReal.measurable_ofReal.comp_aemeasurable
        (((continuous_pow 2).comp_continuousOn
          (continuous_norm.comp_continuousOn (hfV.continuousOn.mono inter_subset_left))).aemeasurable
          hVU.measurableSet)
    have h2 : AEMeasurable (fun y => multiplierWeight c' (ψ y)) (μ.restrict (V ∩ U)) :=
      (multiplierWeight_antitone hc'.le).measurable.comp_aemeasurable
        ((hψ.mono inter_subset_right).aemeasurable hVU.measurableSet)
    exact h1.mul h2
  · calc ∫⁻ y in V ∩ U, multiplierDensity ψ c' f y ∂μ
        ≤ ∫⁻ y in V ∩ U, A * multiplierDensity φ c f y ∂μ := by
          refine setLIntegral_mono' hVU.measurableSet fun y hy => ?_
          unfold multiplierDensity
          calc ENNReal.ofReal (‖f y‖ ^ 2) * multiplierWeight c' (ψ y)
              ≤ ENNReal.ofReal (‖f y‖ ^ 2) * (A * multiplierWeight c (φ y)) :=
                mul_le_mul' le_rfl (hw y hy.2)
            _ = A * (ENNReal.ofReal (‖f y‖ ^ 2) * multiplierWeight c (φ y)) := by ring
      _ = A * ∫⁻ y in V ∩ U, multiplierDensity φ c f y ∂μ := lintegral_const_mul' _ _ hA
      _ ≤ A * ∫⁻ y in V, multiplierDensity φ c f y ∂μ :=
          mul_le_mul' le_rfl (lintegral_mono_set inter_subset_left)
      _ < ⊤ := ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hA) hint

section Generic

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

omit [IsComplexManifold n M] in
/-- A global comparison `u ≤ φ + C` with a *continuous* (extended-valued) `φ` gives the
multiplier-ideal order `𝓘(cu) ⊆ 𝓘(cφ)`, `c > 0`. -/
theorem iOrderOnManifold_of_le_add_of_continuous {u φ : M → EReal} (hφ : Continuous φ) {C : ℝ}
    (h : ∀ x, u x ≤ φ x + (C : EReal)) : IOrderOnManifold (n := n) u φ := by
  intro c hc e z hz g _ hmem
  let _ : MeasurableSpace (ComplexModel n) := borel _
  have _ : BorelSpace (ComplexModel n) := ⟨rfl⟩
  exact multiplierIntegrableAt_of_weight_le hc e.val.open_target hz
    (hφ.comp_continuousOn e.val.continuousOn_symm) ENNReal.ofReal_ne_top
    (fun y _ => SGPT.TestCurve.SkodaRWN.multiplierWeight_le_of_le_add_coe hc (h _)) hmem

omit [IsComplexManifold n M] in
/-- **Change of exponent**: for `φ ≤ B` continuous and integers `M d ≤ k`, `M > 0`,
`𝓘(k · d⁻¹ φ) ⊆ 𝓘(M φ)`. -/
theorem multiplierIdeal_scale_le {φ : M → EReal} (hφ : Continuous φ) {B : ℝ}
    (hB : ∀ x, φ x ≤ (B : EReal)) {d k m : ℕ} (hd : 0 < d) (hm : 0 < m) (hmk : m * d ≤ k) :
    (multiplierIdeal (n := n) (k : ℝ) fun x => (((d : ℝ)⁻¹ : ℝ) : EReal) * φ x).Le
      (multiplierIdeal (n := n) (m : ℝ) φ) := by
  rintro x g ⟨hg, hint⟩
  refine ⟨hg, ?_⟩
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hkd : (m : ℝ) ≤ (k : ℝ) / d := by
    rw [le_div_iff₀ hdR]; exact_mod_cast hmk
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr (lt_of_lt_of_le (Nat.mul_pos hm hd) hmk)
  set e := complexChartAt (n := n) x
  refine multiplierIntegrableAt_of_weight_le hmR e.val.open_target (e.val.map_source
    (mem_complexChartAt_source x)) (hφ.comp_continuousOn e.val.continuousOn_symm)
    (A := ENNReal.ofReal (Real.exp (((k : ℝ) / d - m) * B))) ENNReal.ofReal_ne_top
    (fun y _ => ?_) hint
  change multiplierWeight (m : ℝ) (φ (e.val.symm y)) ≤ _ *
    multiplierWeight (k : ℝ) ((((d : ℝ)⁻¹ : ℝ) : EReal) * φ (e.val.symm y))
  have htB := hB (e.val.symm y)
  generalize φ (e.val.symm y) = t at *
  induction t with
  | bot =>
    rw [EReal.coe_mul_bot_of_pos (inv_pos.mpr hdR), multiplierWeight_bot hkR,
      multiplierWeight_bot hmR, ENNReal.mul_top (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne']
  | top => exact absurd htB (by simp)
  | coe l =>
    have hlB : l ≤ B := EReal.coe_le_coe_iff.mp htB
    rw [← EReal.coe_mul, multiplierWeight_coe, multiplierWeight_coe,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
    have h1 : ((k : ℝ) / d - m) * l ≤ ((k : ℝ) / d - m) * B :=
      mul_le_mul_of_nonneg_left hlB (by linarith)
    have h2 : (k : ℝ) * ((d : ℝ)⁻¹ * l) = (k : ℝ) / d * l := by ring
    rw [h2]
    linarith

end Generic

/-! ### The obstacle -/

variable {X : Scheme} {f : X ⟶ Spec (.of ℂ)} {n : ℕ} [SmoothOfRelativeDimension n f]
  {E : ClosedProjectiveEmbedding f}

local instance skodaIncOpTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance skodaIncOpCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance skodaIncOpManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

variable {L : X.Modules} {a : LineBundleAtlas L} [IsIntegral X]

/-- For `τ < τ(𝓕)`, the normalized potentials along the degrees `K_j = (j+1)! m` form an
increasing sequence of normalized `θ`-psh functions whose supremum is
`sup_{K>0} K⁻¹Γ^{𝓕,K}_τ` (the sequence of `SectionFiltration.exists_increasing_sequence`, with
its degrees made explicit). -/
theorem exists_increasing_degrees (F : SectionFiltration f a)
    (H : SchemeLineBundleMetric f n E L) {τ : ℝ} (hτ : (τ : EReal) < F.slope) :
    ∃ kseq : ℕ → ℕ, (∀ j, 0 < kseq j) ∧
      (letI := E.isSeparated; letI := E.quasiCompact;
        ∀ j, IsThetaPshPotential (H.curvature a).val (F.normalizedPotential H (kseq j) τ)) ∧
      Monotone (fun j => F.normalizedPotential H (kseq j) τ) ∧
      (⨆ j, F.normalizedPotential H (kseq j) τ) = F.rawObstacle H τ := by
  let := E.isSeparated
  let := E.quasiCompact
  obtain ⟨m, hm0, hjump⟩ := F.exists_degree_jump_of_lt_slope hτ
  let kseq : ℕ → ℕ := fun j => (j + 1).factorial * m
  have hkpos : ∀ j, 0 < kseq j := fun j => Nat.mul_pos (Nat.factorial_pos _) hm0
  refine ⟨kseq, hkpos, fun j => ?_, ?_, ?_⟩
  · have hkR : (0 : ℝ) < kseq j := by exact_mod_cast hkpos j
    have hpsh := F.isThetaPshPotential_sectionPotential H (k := kseq j) (τ := τ)
      (hjump _ (Nat.factorial_pos _))
    have h := RestrictedApproximantComparison.isThetaPshPotential_smul hpsh (inv_pos.mpr hkR)
    simp only [smul_smul, inv_mul_cancel₀ hkR.ne', one_smul] at h
    convert h using 1
    funext x
    change F.sectionPotential H (kseq j) τ x / (((kseq j : ℕ) : ℝ) : EReal) = _
    rw [div_eq_mul_inv, mul_comm, ← EReal.coe_inv]
  · refine monotone_nat_of_le_succ fun j x => ?_
    have hidx : kseq (j + 1) = (j + 2) * kseq j := by
      simp only [kseq, Nat.factorial_succ (j + 1)]
      ring
    change F.normalizedPotential H (kseq j) τ x ≤ F.normalizedPotential H (kseq (j + 1)) τ x
    rw [hidx]
    exact F.normalizedPotential_le_mul H _ _ (hkpos j) (by omega) τ x
  · funext x
    rw [iSup_apply]
    apply le_antisymm
    · exact iSup_le fun j => le_iSup₂ (f := fun k (_ : 0 < k) => F.normalizedPotential H k τ x)
        (kseq j) (hkpos j)
    · refine iSup₂_le fun k hk => ?_
      obtain ⟨c, hc⟩ := Nat.dvd_factorial hk (Nat.le_succ k)
      have hc0 : 0 < c := by
        rcases Nat.eq_zero_or_pos c with h | h
        · rw [h, mul_zero] at hc
          exact absurd hc (Nat.factorial_pos _).ne'
        · exact h
      have hidx : kseq k = (c * m) * k := by
        simp only [kseq, hc]
        ring
      refine le_trans ?_ (le_iSup (fun j => F.normalizedPotential H (kseq j) τ x) k)
      rw [hidx]
      exact F.normalizedPotential_le_mul H k (c * m) hk (Nat.mul_pos hc0 hm0) τ x

/-- **The multiplier ideals of the obstacle are controlled by one level.** Let `τ < τ(𝓕)` and
`φ` be continuous with `K⁻¹ Γ^{𝓕,K}_τ ≤ φ + C_K` on `X` for every `K > 0` (the constants may
depend on `K`). Then `𝓘(cψ_τ) ⊆ 𝓘(cφ)` for all `c > 0`, `ψ_τ = usc sup_K K⁻¹Γ^{𝓕,K}_τ` the
obstacle of `ex:RWN`. The proof is the strong openness theorem for the increasing sequence of
`exists_increasing_degrees`. -/
theorem iOrderOnManifold_obstacle (F : SectionFiltration f a) (H : SchemeLineBundleMetric f n E L)
    {τ : ℝ} (hτ : (τ : EReal) < F.slope) {φ : SchemeComplexPoint f → EReal} (hφ : Continuous φ)
    (hcmp : ∀ K : ℕ, 0 < K → ∃ C : ℝ, ∀ x, F.normalizedPotential H K τ x ≤ φ x + (C : EReal)) :
    letI := E.isSeparated
    letI := E.quasiCompact
    IOrderOnManifold (n := n) (F.obstacle H τ) φ := by
  let := E.isSeparated
  let := E.quasiCompact
  obtain ⟨kseq, hkpos, hpsh, hmono, hsup⟩ := exists_increasing_degrees F H hτ
  have h := iOrderOnManifold_uscRegularization_iSup_of_strongOpenness
    (increasingStrongOpenness_ofRegularRoute n)
    (LocalPotentials.closedRealOneOne_hasLocalPotentials (H.curvature a)) hpsh
    (fun j x => F.normalizedPotential_le_zero H _ τ x) hmono
    (fun j => by
      obtain ⟨C, hC⟩ := hcmp (kseq j) (hkpos j)
      exact iOrderOnManifold_of_le_add_of_continuous hφ hC)
  rw [hsup] at h
  exact h

omit [IsIntegral X] in
/-- **Sections in the multiplier ideal of the obstacle.** If `𝓘(cψ) ⊆ 𝓘(c d⁻¹ log |w|²)` for all
`c > 0`, then for `M d ≤ k`, `M > 0`, every section of `L^k ⊗ 𝓘(kψ)` is a section of
`L^k ⊗ 𝓘(M log |w|²)`. -/
theorem isIdealSection_familyLog_of_isMultiplierSection (H : SchemeLineBundleMetric f n E L)
    {ψ : SchemeComplexPoint f → EReal} {d r : ℕ} (hd : 0 < d) (w : Fin r → SectionSpace f L d)
    (hIO : letI := E.isSeparated; letI := E.quasiCompact;
      IOrderOnManifold (n := n) ψ fun x => (((d : ℝ)⁻¹ : ℝ) : EReal) * familyLog H a d w x)
    {k m : ℕ} (hm : 0 < m) (hmk : m * d ≤ k) (σ : SectionSpace f L k)
    (hσ : IsMultiplierSection f n E ψ k σ) :
    IsIdealSection f n E (multiplierIdeal (n := n) (m : ℝ) (familyLog H a d w)) k σ := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have hk : 0 < k := lt_of_lt_of_le (Nat.mul_pos hm hd) hmk
  rcases hσ with h0 | hσ
  · exact absurd h0 hk.ne'
  -- an upper bound of `log |w|²`
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ x, familyLog H a d w x ≤ (B : EReal) := by
    have hbd : ∀ j, ∃ C : ℝ, 0 < C ∧ ∀ p, H.sectionNormSq a d (w j) p ≤ C :=
      fun j => H.exists_sectionNormSq_le a d (w j)
    choose C hC0 hC using hbd
    refine ⟨Real.log (∑ j, C j + 1), fun x => ?_⟩
    have hpos : (0 : ℝ) < ∑ j, C j + 1 := by
      have := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => (hC0 j).le
      linarith
    rw [familyLog, ← ENNReal.log_ofReal_of_pos hpos]
    refine ENNReal.log_le_log (ENNReal.ofReal_le_ofReal ?_)
    have : familyNormSq H a d w x ≤ ∑ j, C j := Finset.sum_le_sum fun j _ => hC j x
    linarith
  have hle1 := SGPT.Okounkov.multiplierIdeal_le_of_iOrderOnManifold hIO
    (c := (k : ℝ)) (Nat.cast_pos.mpr hk)
  have hle2 := multiplierIdeal_scale_le (n := n) (continuous_familyLog H a d w) hB hd hm hmk
  exact fun U α p hp => hle2 _ _ (hle1 _ _ (hσ U α p hp))

end SGPT.TestCurve.SkodaInc
