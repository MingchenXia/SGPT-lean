import SGPT.Foundations.Analysis.Pending.RawPshConvexCutoff
import SGPT.Foundations.Analysis.Pending.ExplicitRadialScalarDdcCalibration
import SGPT.Foundations.Analysis.Pending.LocalPositiveCurrentGluing

set_option autoImplicit false

/-! One literal original raw PSH radial sequence has all original pointwise
pole limits, decreasing smooth approximations of ALL convex cutoffs, and
simultaneous recovery of the SAME current's full AC form. Natural local
reader AE-finite/L1 fields are the only extra raw-data inputs. Full math
and ENTIRE proof precede Lean. No comparison/limit/finite/class cert input. -/

noncomputable section
open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ContDiff Distributions BigOperators

namespace SGPT.Foundations.Analysis.Pending.RawPshRadialConvexACApproximation
open FirstPass FirstPass.MongeAmpere StronglyPositiveForms LocalProductCurrents
  LocalCurrentDensityMatrix LocalCurrentDeterminant LocalBedfordTaylorProducts
  ScalarLeviPositiveCurrent LocalPositiveCurrentGluing HolomorphicPullback
  ExplicitRadialCurrentACApproximation ExplicitRadialScalarDdcCalibration
  TopDegreeDensity

private theorem raw_antitone {n : ℕ} {U : Opens (ComplexModel n)}
    {u : ComplexModel n → EReal} (hu : PlurisubharmonicOn u U)
    (hfin : ∀ᵐ z ∂volume.restrict U, u z ≠ ⊤ ∧ u z ≠ ⊥)
    {R : ℝ} (hR : 0 < R) {N K : Set (ComplexModel n)}
    (hKU : K ⊆ U) (hball : ∀ z ∈ N, closedBall z (2 * R) ⊆ K) :
    ∀ z ∈ N, Antitone (fun j => translationPairing volume
      (K.indicator (fun y => (u y).toReal)) (explicitRadialKernel R hR j) z) := by
  intro z hz a d had
  let r : ℝ := ((a : ℝ) + 1) / ((d : ℝ) + 1)
  have hr : 0 < r := by dsimp [r]; positivity
  have hr1 : r ≤ 1 := by
    dsimp [r]
    apply (div_le_one (by positivity : (0 : ℝ) < (d : ℝ) + 1)).2
    exact_mod_cast Nat.add_le_add_right had 1
  have hBU : ball z (2 * R) ⊆ U := ball_subset_closedBall.trans ((hball z hz).trans hKU)
  have hfB : ∀ᵐ y ∂volume.restrict (ball z (2 * R)), u y ≠ ⊤ ∧ u y ≠ ⊥ :=
    ae_mono (Measure.restrict_mono hBU le_rfl) hfin
  obtain ⟨y, hy, hyfin⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (measure_ball_pos volume z (by positivity : (0 : ℝ) < 2 * R)).ne' hfB
  have hne : ∃ y ∈ ball z (2 * R), u y ≠ ⊥ := ⟨y, hy, hyfin.2⟩
  have hκR : tsupport (explicitRadialKernel (n := n) R hR a) ⊆ closedBall 0 R := by
    rw [explicitRadialKernel_tsupport]
    apply closedBall_subset_closedBall
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (a : ℝ) + 1)).2
    have hapos : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
    nlinarith
  have hcut (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
      (∫ y : ComplexModel n, K.indicator (fun w => (u w).toReal) (z + t • y) *
        explicitRadialKernel R hR a y ∂volume) =
      ∫ y : ComplexModel n, (u (z + t • y)).toReal * explicitRadialKernel R hR a y ∂volume := by
    apply integral_congr_ae
    filter_upwards with w
    by_cases hw : w ∈ tsupport (explicitRadialKernel (n := n) R hR a)
    · have hnorm := mem_closedBall_zero_iff.mp (hκR hw)
      have hmem : z + t • w ∈ K := hball z hz
        ((closedBall_subset_closedBall (by linarith : R ≤ 2 * R))
          (PshRadialRegularization.add_smul_mem_closedBall hnorm
            (by rw [abs_of_pos ht]; exact ht1) hR.le))
      rw [indicator_of_mem hmem]
    · simp only [image_eq_zero_of_notMem_tsupport hw, mul_zero]
  have hmono := PshRadialRegularization.integral_mono_of_psh
    isOpen_ball (convex_ball z (2 * R)).isPreconnected (hu.mono hBU) hne
    (explicitRadialKernel_contDiff R hR a).continuous
    (explicitRadialKernel_nonneg R hR a) (explicitRadialKernel_unitary R hR a)
    hκR (by linarith : R < 2 * R) (Subset.rfl : ball z (2 * R) ⊆ ball z (2 * R))
    hr hr1 (le_rfl : (1 : ℝ) ≤ 1)
  calc
    _ = ∫ y : ComplexModel n,
        K.indicator (fun w => (u w).toReal) (z + r • y) * explicitRadialKernel R hR a y ∂volume := by
      simpa only [inv_div, r] using translationPairing_explicitRadialKernel_scale
        (K.indicator (fun w => (u w).toReal)) R hR a d z
    _ = ∫ y : ComplexModel n, (u (z + r • y)).toReal * explicitRadialKernel R hR a y ∂volume :=
      hcut r hr hr1
    _ ≤ ∫ y : ComplexModel n, (u (z + (1 : ℝ) • y)).toReal * explicitRadialKernel R hR a y ∂volume :=
      hmono
    _ = ∫ y : ComplexModel n,
        K.indicator (fun w => (u w).toReal) (z + (1 : ℝ) • y) * explicitRadialKernel R hR a y ∂volume :=
      (hcut 1 one_pos le_rfl).symm
    _ = _ := by
      symm
      simpa only [div_self (by positivity : (a : ℝ) + 1 ≠ 0), inv_one, one_smul] using
        translationPairing_explicitRadialKernel_scale
          (K.indicator (fun w => (u w).toReal)) R hR a a z

private theorem finite_cutoff (s b : ℝ) :
    b + SmoothMax.posPart (max s (b - 2) - b) = b + SmoothMax.posPart (s - b) := by
  by_cases h : b - 2 ≤ s
  · rw [max_eq_left h]
  · have hl : s ≤ b - 2 := (lt_of_not_ge h).le
    rw [max_eq_right hl, SmoothMax.posPart_eq_zero (by linarith),
      SmoothMax.posPart_eq_zero (by linarith)]

variable {m : ℕ} {U A : Opens (ComplexModel (m+1))}

/-- Original raw local PSH reader fields internally produce positivity, one
literal radial sequence for ALL cutoff levels, ALLpoint pole limits, and
simultaneous AC recovery of the SAME original complementary current. -/
theorem exists_raw_radial_convex_ac_approximation
    {u : ComplexModel (m+1) → EReal} (hu : PlurisubharmonicOn u U)
    (hfin : ∀ᵐ z ∂volume.restrict U, u z ≠ ⊤ ∧ u z ≠ ⊥)
    (hL : LocallyIntegrableOn (fun z => (u z).toReal) U volume)
    (hA : RelativelyCompactIn A U) :
    let D := regularDistribution volume (fun z => (u z).toReal) hL
    let T := ddc (scalarTopCurrent D)
    ∃ (hT : IsPositive T) (R : ℝ) (hR : 0 < R) (K : Set (ComplexModel (m+1))),
      IsCompact K ∧ K ⊆ U ∧
      let f : ℕ → ComplexModel (m+1) → ℝ := fun j =>
        translationPairing volume (K.indicator (fun y => (u y).toReal)) (explicitRadialKernel R hR j)
      (∀ j, IsSmoothPshOn A (f j)) ∧
      (∀ z ∈ A, Antitone (fun j => f j z)) ∧
      (∀ z ∈ A, Tendsto (fun j => (f j z : EReal)) atTop (𝓝 (u z))) ∧
      (∀ b : ℝ, IsDecreasingApproximation A
        (fun z => b + SmoothMax.posPart ((max (u z) ((b-2 : ℝ) : EReal)).toReal - b))
        (fun j z => b + SmoothMax.posPart (f j z - b))) ∧
      ∀ᵐ z ∂volume, z ∈ A →
        Tendsto (fun j => f j z) atTop (𝓝 (u z).toReal) ∧
        Tendsto (fun j => smoothDDC (f j) z) atTop (𝓝 (acForm hT z)) ∧
        Tendsto (fun j => normalizedHermitianMatrix (smoothDDC (f j) z)) atTop
          (𝓝 (acMatrix hT z)) ∧
        Tendsto (fun j => actualTopPowerDensity (smoothDDC (f j) z)) atTop
          (𝓝 (actualTopPowerDensity (acForm hT z))) := by
  classical
  let p : ComplexModel (m+1) → ℝ := fun z => (u z).toReal
  let D := regularDistribution volume p hL
  let T := ddc (scalarTopCurrent D)
  have hLevi : HasNonnegativeDistributionalLevi D :=
    hu.hasNonnegativeDistributionalLevi_of_locallyIntegrable hL hfin
  have hT : IsPositive T := isPositive_ddc_scalarTopCurrent hLevi
  obtain ⟨R₀,hR₀,N,K,hN,hclAN,hNK,hK,hKU,hball₀⟩ :=
    exists_open_compact_closedBall_neighborhood hA.1 U.isOpen hA.2
  let R := R₀/2
  have hR : 0 < R := by dsimp [R]; positivity
  have hball : ∀ z ∈ N, closedBall z R ⊆ K := fun z hz =>
    (closedBall_subset_closedBall (by dsimp [R]; linarith)).trans (hball₀ z hz)
  have hball2 : ∀ z ∈ N, closedBall z (2 * R) ⊆ K := by
    simpa only [R, mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using hball₀
  have hAN : (A : Set (ComplexModel (m+1))) ⊆ N := subset_closure.trans hclAN
  have hAU : (A : Set (ComplexModel (m+1))) ⊆ U := hAN.trans (hNK.trans hKU)
  have hg : LocallyIntegrable (K.indicator p) volume :=
    (integrable_indicator_of_locallyIntegrableOn_isCompact hL hK hKU).locallyIntegrable
  have hae : ∀ᵐ z ∂volume.restrict N, Tendsto (fun j =>
      translationPairing volume (K.indicator p) (explicitRadialKernel R hR j) z)
      atTop (𝓝 (p z)) := by
    filter_upwards [ae_restrict_of_ae (ae_tendsto_translationPairing_explicitRadialKernel hg R hR),
      ae_restrict_mem hN.measurableSet] with z hz hzN
    simpa only [indicator_of_mem (hNK hzN)] using hz
  let S : RadialConvolutionSystem ⟨N,hN⟩ K p R :=
    { kernel := fun j => explicitRadialKernel R hR j
      kernel_contDiff := fun j => explicitRadialKernel_contDiff R hR j
      kernel_hasCompactSupport := fun j => explicitRadialKernel_hasCompactSupport R hR j
      kernel_nonneg := fun j => explicitRadialKernel_nonneg R hR j
      kernel_integral_one := fun j => explicitRadialKernel_integral_one R hR j
      kernel_radial := fun j => explicitRadialKernel_unitary R hR j
      kernel_tsupport := fun j => by rw [explicitRadialKernel_tsupport]
      translated_tsupport := fun j z hz =>
        (tsupport_explicitRadialKernel_translate_subset R hR j z).trans
          ((closedBall_subset_closedBall (shrinkingBump_rOut_le R hR j)).trans (hball z hz))
      antitone_pairing := raw_antitone hu hfin hR hKU hball2
      ae_tendsto_pairing := hae }
  let f : ℕ → ComplexModel (m+1) → ℝ := fun j =>
    translationPairing volume (K.indicator p) (explicitRadialKernel R hR j)
  have hfSmooth (j : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (f j) :=
    contDiff_translationPairing hg (explicitRadialKernel_hasCompactSupport R hR j)
      (explicitRadialKernel_contDiff R hR j)
  have hfPsh (j : ℕ) : PlurisubharmonicOn (fun z => (f j z : EReal)) A :=
    ((discPshOn_translationPairing_indicator hL hLevi
      (S.kernel_hasCompactSupport j) (S.kernel_contDiff j) (S.kernel_nonneg j)
      hK hKU (S.translated_tsupport j)).plurisubharmonicOn hN).mono hAN
  have hf (j : ℕ) : IsSmoothPshOn A (f j) :=
    isSmoothPshOn_of_psh (hfSmooth j).contDiffOn (hfPsh j)
  have hanti : ∀ z ∈ A, Antitone (fun j => f j z) := fun z hz => S.antitone_pairing z (hAN hz)
  have haeA : ∀ᵐ z ∂volume.restrict A, Tendsto (fun j => f j z) atTop (𝓝 (p z)) :=
    ae_mono (Measure.restrict_mono hAN le_rfl) hae
  have hfinA : ∀ᵐ z ∂volume.restrict A, u z ≠ ⊤ ∧ u z ≠ ⊥ :=
    ae_mono (Measure.restrict_mono hAU le_rfl) hfin
  have haeE : ∀ᵐ z ∂volume.restrict A,
      Tendsto (fun j => (f j z : EReal)) atTop (𝓝 (u z)) := by
    filter_upwards [haeA,hfinA] with z hz hzfin
    have he := EReal.tendsto_coe.mpr hz
    simpa only [p, EReal.coe_toReal hzfin.1 hzfin.2] using he
  have hpoint := tendsto_everywhere_ereal_of_ae_of_antitone_psh (hu.mono hAU) hfPsh hanti haeE
  have hcutoff : ∀ b : ℝ, IsDecreasingApproximation A
      (fun z => b + SmoothMax.posPart ((max (u z) ((b-2 : ℝ) : EReal)).toReal - b))
      (fun j z => b + SmoothMax.posPart (f j z - b)) := by
    intro b
    let q : ComplexModel (m+1) → ℝ := fun z =>
      b + SmoothMax.posPart ((max (u z) ((b-2 : ℝ) : EReal)).toReal - b)
    let g : ℕ → ComplexModel (m+1) → ℝ := fun j z => b + SmoothMax.posPart (f j z - b)
    have hgSmooth (j : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (g j) :=
      contDiff_const.add (SmoothMax.contDiff_posPart.comp ((hfSmooth j).sub contDiff_const))
    have hgPsh (j : ℕ) : PlurisubharmonicOn (fun z => (g j z : EReal)) A := by
      have hh := RegularizedMaxPsh.plurisubharmonicOn_eregularizedMax
        (δ := 1) (by norm_num) (hfPsh j)
        ((RegularizedMaxPsh.discPshOn_const b (A : Set (ComplexModel (m+1)))).plurisubharmonicOn A.isOpen)
      intro z hz
      refine (hh z hz).congr (Eventually.of_forall fun y => ?_)
      change RegularizedMaxEReal.eregularizedMax 1 (f j y : EReal) (b : EReal) =
        ((b + SmoothMax.posPart (f j y - b) : ℝ) : EReal)
      rw [RegularizedMaxEReal.eregularizedMax_eq_coe_formula (EReal.coe_ne_top _) (EReal.coe_ne_bot _)
        (EReal.coe_ne_top _) (EReal.coe_ne_bot _)]
      simp only [EReal.toReal_coe, div_one, one_mul]
    have hgAnti : ∀ z ∈ A, Antitone (fun j => g j z) := by
      intro z hz a d had
      exact add_le_add le_rfl (SmoothMax.posPart_monotone (sub_le_sub_right (hanti z hz had) b))
    have hgAE : ∀ᵐ z ∂volume.restrict A, Tendsto (fun j => g j z) atTop (𝓝 (q z)) := by
      filter_upwards [haeA,hfinA] with z hz hzfin
      have he : q z = b + SmoothMax.posPart (p z - b) := by
        dsimp only [q,p]
        rw [PshRadialRegularization.toReal_max_coe hzfin.1 hzfin.2]
        exact finite_cutoff _ b
      rw [he]
      have hc : Continuous (fun s : ℝ => b + SmoothMax.posPart (s-b)) :=
        continuous_const.add (SmoothMax.contDiff_posPart.continuous.comp (continuous_id.sub continuous_const))
      exact (hc.tendsto _).comp hz
    have hq := RawPshConvexCutoff.isLocallyBoundedPshOn_convexCutoff U hu b
    exact ⟨fun j => isSmoothPshOn_of_psh (hgSmooth j).contDiffOn (hgPsh j),hgAnti,
      tendsto_everywhere_of_ae_of_antitone_psh (hq.1.mono hAU) hgPsh hgAnti hgAE⟩
  have hclosed (j : ℕ) (z : ComplexModel (m+1)) (hz : z ∈ A) :
      closedBall z (shrinkingBump (E := ComplexModel (m+1)) R hR j).rOut ⊆ U :=
    ((closedBall_subset_closedBall (shrinkingBump_rOut_le R hR j)).trans (hball z (hAN hz))).trans hKU
  have heq (j : ℕ) : Set.EqOn (radialMollifiedScalar D R hR j) (f j) A := by
    intro z hz
    unfold radialMollifiedScalar
    rw [dif_pos (hclosed j z hz),regularDistribution_apply]
    change (∫ y, explicitRadialKernel R hR j (z-y)*p y ∂volume) =
      ∫ y, K.indicator p y * explicitRadialKernel R hR j (y-z) ∂volume
    apply integral_congr_ae
    filter_upwards with y
    have heven : explicitRadialKernel R hR j (z-y) = explicitRadialKernel R hR j (y-z) := by
      rw [← neg_sub y z,explicitRadialKernel_neg]
    rw [heven]
    by_cases hy : y ∈ K
    · rw [indicator_of_mem hy]
      exact mul_comm _ _
    · have hzero : explicitRadialKernel R hR j (y-z) = 0 := by
        by_contra hne
        have hsup : y ∈ tsupport (fun q => explicitRadialKernel R hR j (q-z)) := subset_tsupport _ hne
        exact hy ((hball z (hAN hz)) ((closedBall_subset_closedBall (shrinkingBump_rOut_le R hR j))
          (tsupport_explicitRadialKernel_translate_subset R hR j z hsup)))
      rw [hzero,zero_mul,mul_zero]
  have heventual (z : ComplexModel (m+1)) (hz : z ∈ A) :
      (fun j => smoothDDC (f j) z) =ᶠ[atTop] (fun j => radialMollifiedForm T R hR j z) := by
    obtain ⟨V,hVU,hzV,Nz,hNz⟩ := exists_buffered_radial_scalar_ddc_calibration (hAU hz) R hR
    filter_upwards [eventually_ge_atTop Nz] with j hj
    have hc := (hNz D j hj).2 z hzV
    rw [hc]
    exact (FirstPass.smoothDDC_congr ((heq j).eventuallyEq_of_mem (A.isOpen.mem_nhds hz))).symm
  refine ⟨hT,R,hR,K,hK,hKU,hf,hanti,hpoint,hcutoff,?_⟩
  have hfull := (positive_and_ae_tendsto_radial_form_matrix_density hT R hR).2
  have hscalar := (ae_restrict_iff' hN.measurableSet).mp hae
  filter_upwards [hfull,hscalar] with z hz hzs hzA
  have h := hz (hAU hzA)
  have he := heventual z hzA
  exact ⟨hzs (hAN hzA),h.1.congr' he.symm,
    h.2.1.congr' (he.mono fun j hj => congrArg normalizedHermitianMatrix hj.symm),
    h.2.2.congr' (he.mono fun j hj => congrArg actualTopPowerDensity hj.symm)⟩

end SGPT.Foundations.Analysis.Pending.RawPshRadialConvexACApproximation
