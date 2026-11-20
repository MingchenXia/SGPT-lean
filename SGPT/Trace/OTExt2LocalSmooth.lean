import SGPT.Trace.OTExt2LocalStep
import SGPT.Trace.TwistedL2SingularMeanValue
import SGPT.Foundations.Analysis.Pending.HolomorphicNormalFamilies

/-!
# The local critical-gain extension for smooth weights

Blueprint `claude-ot-ext2.tex`, node `claude-ot-ext2:local-smooth`.  Xia, *Foundations of
pluripotential theory*, proof of `lem:local-critical-gain-extension`, paragraph *The limit
`ε → 0`* (smooth weights).

For `P` smooth near `D̄` with `Levi(P) ≥ π|v|²` and `f` holomorphic near `B̄(0, r')` with
`∫_{B'} |f|² e^{-P(z', 0)} < ∞`, there is `F` holomorphic on `D` with `F(z', 0) = f(z')` and

`∫_D |F|² e^{-P} |w|^{-2d} (log |w|²)^{-2} ≤ C_d ∫_{B'} |f|² e^{-P(z', 0)}`,

`C_d = 40 M² 2^d vol(B_{ℂ^d}(0, 1))` (`localGainConst`, `M` a bound of `|χ'|`).

Proof: the steps `exists_local_step` for `ε_k = ε₀/(k + 2)`, the shell bound
`∫_{ε/2 ≤ |w|² ≤ ε} |f|² e^{-P} |w|^{-2d} ≤ 2 · 2^d vol(B(0,1)) ∫_{B'} |f|² e^{-P(z',0)}` for
`ε ≤ ε₀` (uniform continuity of `P` and Fubini, `lintegral_image_prod`), a uniform `L²` bound
(the weight `e^{-P}(ε + R)^{-d} log(ε + R)^{-2}` is `≥ e^{-max P}/2`), Montel's theorem
(`exists_subseq_of_l2_bounded`) and Fatou's lemma; the cut-off parts `f χ(R/ε_k)` vanish
pointwise off `{w = 0}`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Trace.OTExt2

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.RegularLocusDense
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.OTChen
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open SGPT.Trace.TwistedL2
open SGPT.Trace.OTMargin (normalWeight normalWeight_nonneg normalWeight_eq_zero_iff
  fst_prodModelEquiv_symm normalWeight_eq_norm_snd)

/-! ### The critical kernel and the constant -/

/-- The critical kernel `|w|^{-2(n-m)} (log |w|²)^{-2}` on `ℂⁿ = ℂ^m × ℂ^{n-m}`
(`|w|² = normalWeight n m z`), with the value `∞` on `{w = 0}`. -/
def criticalKernel (n m : ℕ) (z : ComplexModel n) : ℝ≥0∞ :=
  (ENNReal.ofReal (normalWeight n m z ^ (n - m) * Real.log (normalWeight n m z) ^ 2))⁻¹

/-- A bound `M` of `|χ'|` for the cut-off `χ = chenCutoff`. -/
def chenM : ℝ := (exists_abs_deriv_chenCutoff_le).choose

theorem chenM_nonneg : 0 ≤ chenM := (exists_abs_deriv_chenCutoff_le).choose_spec.1

theorem abs_deriv_chenCutoff_le_chenM (x : ℝ) : |deriv chenCutoff x| ≤ chenM :=
  (exists_abs_deriv_chenCutoff_le).choose_spec.2 x

/-- The constant `C_d = 40 M² 2^d vol(B_{ℂ^d}(0, 1))` of the local critical-gain extension. -/
def localGainConst (d : ℕ) : ℝ≥0∞ :=
  40 * ENNReal.ofReal (chenM ^ 2) * 2 ^ d * volume (ball (0 : ComplexModel d) 1)

theorem localGainConst_lt_top (d : ℕ) : localGainConst d < ⊤ := by
  unfold localGainConst
  refine ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num)
    ENNReal.ofReal_lt_top) (ENNReal.pow_lt_top (by norm_num))) measure_ball_lt_top

/-! ### Normal families -/

variable {n : ℕ}

/-- **Montel's theorem for `L²`-bounded holomorphic functions** on an open set of `ℂⁿ`. -/
theorem exists_subseq_of_l2_bounded {D : Set (ComplexModel n)} (hD : IsOpen D)
    (F : ℕ → ComplexModel n → ℂ) (hF : ∀ k, DifferentiableOn ℂ (F k) D) {B : ℝ≥0∞}
    (hB : B < ⊤) (hbd : ∀ k, ∫⁻ z in D, ENNReal.ofReal (‖F k z‖ ^ 2) ≤ B) :
    ∃ (ψ : ℕ → ℕ) (G : ComplexModel n → ℂ), StrictMono ψ ∧ DifferentiableOn ℂ G D ∧
      TendstoLocallyUniformlyOn (fun k => F (ψ k)) G atTop D := by
  refine exists_subseq_tendstoLocallyUniformlyOn_of_eventually_bounded hD F fun x hx => ?_
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hD x hx
  obtain ⟨A, hA⟩ := exists_eventually_uniform_norm_bound_of_ball_l2 hρ F hB
    (Eventually.of_forall fun k => ⟨(hF k).mono hball,
      (lintegral_mono_set hball).trans (hbd k)⟩)
  refine ⟨ρ / 2, by positivity, A, hA.mono fun k hk => ⟨(hF k).mono
    ((ball_subset_ball (by linarith)).trans hball), hk⟩⟩

/-! ### Scalar bounds -/

theorem pow_mul_log_sq_le_two {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) {d : ℕ} (hd : 1 ≤ d) :
    t ^ d * Real.log t ^ 2 ≤ 2 := by
  have h1 : t ^ d ≤ t := by
    calc t ^ d ≤ t ^ 1 := pow_le_pow_of_le_one ht.le ht1 hd
      _ = t := pow_one t
  have h2 := log_sq_le_two_inv ht ht1
  have h3 : t * Real.log t ^ 2 ≤ 2 := by
    calc t * Real.log t ^ 2 ≤ t * (2 * t⁻¹) := mul_le_mul_of_nonneg_left h2 ht.le
      _ = 2 := by field_simp
  calc t ^ d * Real.log t ^ 2 ≤ t * Real.log t ^ 2 :=
        mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
    _ ≤ 2 := h3

/-- `stepWeight ≥ e^{-P}/2` for `0 < ε + R ≤ 1`. -/
theorem half_exp_le_stepWeight {d : ℕ} (hd : 1 ≤ d) {P R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε)
    (h1 : ε + R < 1) : Real.exp (-P) / 2 ≤ stepWeight d P R ε := by
  have ht : 0 < ε + R := by linarith
  have hl : Real.log (ε + R) < 0 := Real.log_neg ht h1
  have hl2 : 0 < Real.log (ε + R) ^ 2 := by nlinarith
  have hb := pow_mul_log_sq_le_two ht h1.le hd
  have hpos : 0 < (ε + R) ^ d * Real.log (ε + R) ^ 2 := mul_pos (pow_pos ht d) hl2
  unfold stepWeight
  rw [mul_assoc, ← mul_inv, div_eq_mul_inv]
  gcongr

/-! ### The smooth case -/

variable {m d : ℕ}

theorem tanWeight_inclusion_proj (hmn : m ≤ n) (z : ComplexModel n) :
    tanWeight n m (coordinateInclusion n m (coordinateProjection n m z)) = tanWeight n m z := by
  rw [tanWeight_eq_norm_proj hmn, tanWeight_eq_norm_proj hmn,
    coordinateProjection_coordinateInclusion hmn]

theorem normalWeight_inclusion (w : ComplexModel m) :
    normalWeight n m (coordinateInclusion n m w) = 0 :=
  (normalWeight_eq_zero_iff _).mpr (coordinateInclusion_mem_complexCoordinatePlane w)

theorem norm_sub_inclusion_proj_sq (z : ComplexModel n) :
    ‖z - coordinateInclusion n m (coordinateProjection n m z)‖ ^ 2 = normalWeight n m z := by
  rw [normalWeight_eq_norm_sq]
  rfl

theorem inclusion_mem_localDom {r' r'' : ℝ} (hr'' : 0 < r'') {w : ComplexModel m}
    (hw : w ∈ ball (0 : ComplexModel m) r') (hmn : m ≤ n) :
    coordinateInclusion n m w ∈ localDom n m r' r'' := by
  refine ⟨?_, ?_⟩
  · rw [tanWeight_eq_norm_proj hmn, coordinateProjection_coordinateInclusion hmn]
    exact pow_lt_pow_left₀ (mem_ball_zero_iff.mp hw) (norm_nonneg _) two_ne_zero
  · rw [normalWeight_inclusion]; positivity

/-- **FPT `lem:local-critical-gain-extension` for smooth weights** with `Levi(P) ≥ π|v|²`. -/
theorem localCriticalGain_smooth (hd : 1 ≤ d) {r' r'' : ℝ} (hr' : 0 < r') (hr'' : 0 < r'')
    (hr''e : r'' ^ 2 < Real.exp (-4))
    {O : Set (ComplexModel (m + d))} (hO : IsOpen O)
    (hDO : closure (localDom (m + d) m r' r'') ⊆ O)
    {P : ComplexModel (m + d) → ℝ} (hP : ContDiffOn ℝ ∞ P O)
    (hPL : ∀ z ∈ O, ∀ v : ComplexModel (m + d), Real.pi * ‖v‖ ^ 2 ≤ leviForm P z v)
    {O' : Set (ComplexModel m)} (hO' : IsOpen O') (hBO' : closedBall 0 r' ⊆ O')
    {f : ComplexModel m → ℂ} (hf : DifferentiableOn ℂ f O')
    (hI : ∫⁻ z' in ball (0 : ComplexModel m) r', ENNReal.ofReal (‖f z'‖ ^ 2) *
      ENNReal.ofReal (Real.exp (-P (coordinateInclusion (m + d) m z'))) ≠ ⊤) :
    ∃ F : ComplexModel (m + d) → ℂ, DifferentiableOn ℂ F (localDom (m + d) m r' r'') ∧
      (∀ z' ∈ ball (0 : ComplexModel m) r', F (coordinateInclusion (m + d) m z') = f z') ∧
      ∫⁻ z in localDom (m + d) m r' r'', ENNReal.ofReal (‖F z‖ ^ 2) *
          ENNReal.ofReal (Real.exp (-P z)) * criticalKernel (m + d) m z ≤
        localGainConst d * ∫⁻ z' in ball (0 : ComplexModel m) r', ENNReal.ofReal (‖f z'‖ ^ 2) *
          ENNReal.ofReal (Real.exp (-P (coordinateInclusion (m + d) m z'))) := by
  classical
  set M := chenM
  have hM := abs_deriv_chenCutoff_le_chenM
  have hM0 := chenM_nonneg
  set D := localDom (m + d) m r' r'' with hDdef
  set U := localPunct (m + d) m r' r'' with hUdef
  set R := normalWeight (m + d) m with hRdef
  set proj := coordinateProjection (m + d) m with hproj
  set ι := coordinateInclusion (m + d) m with hι
  set I := ∫⁻ z' in ball (0 : ComplexModel m) r', ENNReal.ofReal (‖f z'‖ ^ 2) *
      ENNReal.ofReal (Real.exp (-P (ι z'))) with hIdef
  have hmn : m ≤ m + d := by omega
  have hDo : IsOpen D := isOpen_localDom m r' r''
  have hUD : U ⊆ D := localPunct_subset m r' r''
  have hDO' : D ⊆ O := subset_closure.trans hDO
  have hRc : Continuous R := continuous_normalWeight m
  have hR4 : ∀ z ∈ D, R z < Real.exp (-4) := fun z hz => lt_trans hz.2 hr''e
  have hprojD : ∀ z ∈ D, proj z ∈ ball 0 r' := fun z hz =>
    coordinateProjection_mem_ball hmn hz.1 hr'
  have hιD : ∀ w ∈ ball (0 : ComplexModel m) r', ι w ∈ D := fun w hw =>
    inclusion_mem_localDom hr'' hw hmn
  have hfPc : ContinuousOn (fun z => f (proj z)) D := fun z hz =>
    ((hf.continuousOn.continuousAt (hO'.mem_nhds (hBO' (ball_subset_closedBall (hprojD z hz))))).comp
      (coordinateProjection (m + d) m).continuous.continuousAt).continuousWithinAt
  have hPc : ContinuousOn P D := hP.continuousOn.mono hDO'
  -- bounds
  obtain ⟨Cf, hCf⟩ := (isCompact_closedBall (0 : ComplexModel m) r').exists_bound_of_continuousOn
    (hf.continuousOn.mono hBO')
  have hBf : ∀ z ∈ D, ‖f (proj z)‖ ^ 2 ≤ Cf ^ 2 := fun z hz =>
    pow_le_pow_left₀ (norm_nonneg _) (hCf _ (ball_subset_closedBall (hprojD z hz))) 2
  obtain ⟨BP, hBP'⟩ := (isCompact_closure_localDom (n := m + d) (m := m) hr' hr'').exists_bound_of_continuousOn
    (hP.continuousOn.mono hDO)
  have hBP : ∀ z ∈ D, |P z| ≤ BP := fun z hz => by
    have := hBP' z (subset_closure hz); rwa [Real.norm_eq_abs] at this
  have hvolD : volume D < ⊤ := volume_localDom_lt_top hr' hr''
  -- uniform continuity of `P`
  obtain ⟨δ, hδ, hδP⟩ : ∃ δ > 0, ∀ x ∈ closure D, ∀ y ∈ closure D, dist x y < δ →
      dist (P x) (P y) < Real.log 2 :=
    Metric.uniformContinuousOn_iff.mp
      ((isCompact_closure_localDom hr' hr'').uniformContinuousOn_of_continuous
        (hP.continuousOn.mono hDO)) _ (Real.log_pos (by norm_num))
  set ε₀ : ℝ := min (Real.exp (-4) / 2) (δ ^ 2 / 2) with hε₀
  have hε₀pos : 0 < ε₀ := lt_min (by positivity) (by positivity)
  have hε₀e : ε₀ < Real.exp (-4) := lt_of_le_of_lt (min_le_left _ _) (by
    have := Real.exp_pos (-4); linarith)
  have hcmp : ∀ z ∈ D, R z ≤ ε₀ → Real.exp (-P z) ≤ 2 * Real.exp (-P (ι (proj z))) := by
    intro z hz hRz
    have hιz : ι (proj z) ∈ D := by
      refine ⟨?_, ?_⟩
      · rw [hι, hproj, tanWeight_inclusion_proj hmn]; exact hz.1
      · show R (ι (proj z)) < r'' ^ 2
        rw [hRdef, hι, normalWeight_inclusion]; positivity
    have hdist : dist z (ι (proj z)) < δ := by
      rw [dist_eq_norm]
      have h1 : ‖z - ι (proj z)‖ ^ 2 = R z := norm_sub_inclusion_proj_sq z
      have h2 : R z < δ ^ 2 := lt_of_le_of_lt hRz (lt_of_le_of_lt (min_le_right _ _) (by
        have := sq_pos_of_pos hδ; linarith))
      exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hδ.le two_ne_zero).mp (h1 ▸ h2)
    have h := hδP z (subset_closure hz) _ (subset_closure hιz) hdist
    rw [Real.dist_eq, abs_lt] at h
    calc Real.exp (-P z) ≤ Real.exp (Real.log 2 + -P (ι (proj z))) :=
          Real.exp_le_exp.mpr (by linarith)
      _ = 2 * Real.exp (-P (ι (proj z))) := by
          rw [Real.exp_add, Real.exp_log (by norm_num)]
  -- the shell bound
  have hshell : ∀ ε, 0 < ε → ε ≤ ε₀ →
      ∫⁻ z in D, ENNReal.ofReal (4 * M ^ 2 * ‖f (proj z)‖ ^ 2 * shellInd ε (R z) *
          (Real.exp (-P z) * (R z ^ d)⁻¹)) ≤
        ENNReal.ofReal (8 * M ^ 2) * (I * (2 ^ d * volume (ball (0 : ComplexModel d) 1))) := by
    intro ε hε hεε₀
    set e := prodModelEquiv m d with he
    set g : ComplexModel m → ℝ≥0∞ := (ball (0 : ComplexModel m) r').indicator
      fun w => ENNReal.ofReal (‖f w‖ ^ 2) * ENNReal.ofReal (Real.exp (-P (ι w))) with hgdef
    set h : ComplexModel d → ℝ≥0∞ :=
      {w : ComplexModel d | ε / 2 ≤ ‖w‖ ^ 2 ∧ ‖w‖ ^ 2 ≤ ε}.indicator
        fun w => ENNReal.ofReal ((‖w‖ ^ 2)⁻¹ ^ d) with hhdef
    have hgm : AEMeasurable g := by
      refine (aemeasurable_indicator_iff measurableSet_ball).mpr ?_
      have heq : (fun w => ENNReal.ofReal (‖f w‖ ^ 2) * ENNReal.ofReal (Real.exp (-P (ι w)))) =
          fun w => ENNReal.ofReal (‖f w‖ ^ 2 * Real.exp (-P (ι w))) :=
        funext fun w => (ENNReal.ofReal_mul (sq_nonneg _)).symm
      rw [heq]
      refine ContinuousOn.aemeasurable ?_ measurableSet_ball
      refine ENNReal.continuous_ofReal.comp_continuousOn
        (((hf.continuousOn.mono (ball_subset_closedBall.trans hBO')).norm.pow 2).mul ?_)
      refine Real.continuous_exp.comp_continuousOn (ContinuousOn.neg ?_)
      exact hPc.comp (coordinateInclusion (m + d) m).continuous.continuousOn hιD
    have hhm : AEMeasurable h :=
      ((ENNReal.measurable_ofReal.comp ((measurable_norm.pow_const 2).inv.pow_const d)).indicator
        (measurableSet_shell d ε)).aemeasurable
    have hpt : ∀ z ∈ D, ENNReal.ofReal (4 * M ^ 2 * ‖f (proj z)‖ ^ 2 * shellInd ε (R z) *
        (Real.exp (-P z) * (R z ^ d)⁻¹)) ≤
          ENNReal.ofReal (8 * M ^ 2) * (g (e.symm z).1 * h (e.symm z).2) := by
      intro z hz
      have h1 : (e.symm z).1 = proj z := fst_prodModelEquiv_symm m d z
      have h2 : R z = ‖(e.symm z).2‖ ^ 2 := normalWeight_eq_norm_snd m d z
      by_cases hs : shellInd ε (R z) = 0
      · rw [hs]; simp
      · have hs1 : ε / 2 ≤ R z ∧ R z ≤ ε := by
          unfold shellInd at hs; split_ifs at hs with h'; exact h'; exact absurd rfl hs
        have hsv : shellInd ε (R z) = 1 := by unfold shellInd; rw [if_pos hs1]
        have hRpos : 0 < R z := lt_of_lt_of_le (by positivity) hs1.1
        rw [hsv, mul_one, hgdef, hhdef, h1, indicator_of_mem (hprojD z hz),
          indicator_of_mem (show (e.symm z).2 ∈ {w : ComplexModel d | ε / 2 ≤ ‖w‖ ^ 2 ∧
            ‖w‖ ^ 2 ≤ ε} by show ε / 2 ≤ ‖(e.symm z).2‖ ^ 2 ∧ ‖(e.symm z).2‖ ^ 2 ≤ ε
                            rw [← h2]; exact hs1)]
        rw [← h2, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have hc := hcmp z hz (hs1.2.trans hεε₀)
        rw [inv_pow]
        have hi : 0 ≤ (R z ^ d)⁻¹ := by positivity
        have hfn : 0 ≤ ‖f (proj z)‖ ^ 2 := sq_nonneg _
        calc 4 * M ^ 2 * ‖f (proj z)‖ ^ 2 * (Real.exp (-P z) * (R z ^ d)⁻¹)
            ≤ 4 * M ^ 2 * ‖f (proj z)‖ ^ 2 * (2 * Real.exp (-P (ι (proj z))) * (R z ^ d)⁻¹) := by
              gcongr
          _ = 8 * M ^ 2 * (‖f (proj z)‖ ^ 2 * Real.exp (-P (ι (proj z))) * (R z ^ d)⁻¹) := by
              ring
    calc ∫⁻ z in D, ENNReal.ofReal (4 * M ^ 2 * ‖f (proj z)‖ ^ 2 * shellInd ε (R z) *
          (Real.exp (-P z) * (R z ^ d)⁻¹))
        ≤ ∫⁻ z in D, ENNReal.ofReal (8 * M ^ 2) * (g (e.symm z).1 * h (e.symm z).2) :=
          setLIntegral_mono' hDo.measurableSet hpt
      _ ≤ ∫⁻ z, ENNReal.ofReal (8 * M ^ 2) * (g (e.symm z).1 * h (e.symm z).2) :=
          setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal (8 * M ^ 2) * ∫⁻ z, g (e.symm z).1 * h (e.symm z).2 :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (8 * M ^ 2) * ((∫⁻ x, g x) * ∫⁻ w, h w) := by
          congr 1
          have := lintegral_image_prod m d (A := univ) (B := univ) g h hgm hhm
          rw [univ_prod_univ, image_univ_of_surjective e.surjective, Measure.restrict_univ,
            Measure.restrict_univ, Measure.restrict_univ] at this
          exact this
      _ ≤ ENNReal.ofReal (8 * M ^ 2) * (I * (2 ^ d * volume (ball (0 : ComplexModel d) 1))) := by
          gcongr
          · rw [hgdef, lintegral_indicator measurableSet_ball]
          · rw [hhdef, lintegral_indicator (measurableSet_shell d ε)]
            exact lintegral_shell_le d hε
  -- the steps
  set εs : ℕ → ℝ := fun k => ε₀ / ((k : ℝ) + 2) with hεsdef
  have hεs0 : ∀ k, 0 < εs k := fun k => div_pos hε₀pos (by positivity)
  have hεsle : ∀ k, εs k ≤ ε₀ := fun k =>
    div_le_self hε₀pos.le (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)
  have hεse : ∀ k, εs k < Real.exp (-4) := fun k => (hεsle k).trans_lt hε₀e
  have hεslim : Tendsto εs atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  choose F hF hFext hFest using fun k => exists_local_step hd hr' hr'' hr''e hO hDO hP hPL hO'
    hBO' hf hM (hεs0 k) (hεse k)
  set G : ℕ → ComplexModel (m + d) → ℂ := fun k z => f (proj z) * (chenCutoff (R z / εs k) : ℂ)
    with hGdef
  set B₁ : ℝ≥0∞ := 5 * (ENNReal.ofReal (8 * M ^ 2) *
    (I * (2 ^ d * volume (ball (0 : ComplexModel d) 1)))) with hB₁def
  have hB₁ : B₁ < ⊤ := by
    refine ENNReal.mul_lt_top (by norm_num) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hI) (ENNReal.mul_lt_top
        (ENNReal.pow_lt_top (by norm_num)) measure_ball_lt_top)))
  have hcorr : ∀ k, ∫⁻ z in D, ENNReal.ofReal (‖F k z - G k z‖ ^ 2 *
      stepWeight d (P z) (R z) (εs k)) ≤ B₁ := by
    intro k
    refine (hFest k).trans ?_
    rw [hB₁def]
    gcongr
    exact hshell _ (hεs0 k) (hεsle k)
  -- the uniform `L²` bound
  set B₂ : ℝ≥0∞ := ENNReal.ofReal (2 * Cf ^ 2) * volume D +
    ENNReal.ofReal (4 * Real.exp BP) * B₁ with hB₂def
  have hB₂ : B₂ < ⊤ := ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hvolD,
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hB₁⟩
  have hL2 : ∀ k, ∫⁻ z in D, ENNReal.ofReal (‖F k z‖ ^ 2) ≤ B₂ := by
    intro k
    have hpt : ∀ z ∈ D, ENNReal.ofReal (‖F k z‖ ^ 2) ≤ ENNReal.ofReal (2 * Cf ^ 2) +
        ENNReal.ofReal (4 * Real.exp BP) *
          ENNReal.ofReal (‖F k z - G k z‖ ^ 2 * stepWeight d (P z) (R z) (εs k)) := by
      intro z hz
      have hR0 := normalWeight_nonneg (m + d) m z
      have h1e : εs k + R z < 1 := by
        have := hR4 z hz; have := hεse k
        have : Real.exp (-4) < 1 / 2 := by
          have h := Real.exp_lt_one_iff.mpr (show (-4 : ℝ) < 0 by norm_num)
          have h2 : Real.exp (-4) * Real.exp 4 = 1 := by rw [← Real.exp_add]; simp
          have h3 : (2 : ℝ) < Real.exp 4 := by
            have := Real.add_one_lt_exp (show (4 : ℝ) ≠ 0 by norm_num); linarith
          nlinarith [Real.exp_pos (-4)]
        linarith
      have hw := half_exp_le_stepWeight (P := P z) hd hR0 (hεs0 k) h1e
      have hGz : ‖G k z‖ ^ 2 ≤ Cf ^ 2 := by
        have hc : ‖(chenCutoff (R z / εs k) : ℂ)‖ ≤ 1 := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (chenCutoff_nonneg _)]
          exact chenCutoff_le_one _
        have : ‖G k z‖ ≤ ‖f (proj z)‖ := by
          simp only [hGdef, norm_mul]
          exact mul_le_of_le_one_right (norm_nonneg _) hc
        exact (pow_le_pow_left₀ (norm_nonneg _) this 2).trans (hBf z hz)
      have h1 : ‖F k z‖ ≤ ‖G k z‖ + ‖F k z - G k z‖ := by
        have := norm_add_le (G k z) (F k z - G k z)
        rwa [add_sub_cancel] at this
      have h2 : ‖F k z‖ ^ 2 ≤ 2 * ‖G k z‖ ^ 2 + 2 * ‖F k z - G k z‖ ^ 2 := by
        nlinarith [norm_nonneg (F k z), norm_nonneg (G k z), norm_nonneg (F k z - G k z),
          sq_nonneg (‖G k z‖ - ‖F k z - G k z‖)]
      have h3 : 2 * ‖F k z - G k z‖ ^ 2 ≤
          4 * Real.exp BP * (‖F k z - G k z‖ ^ 2 * stepWeight d (P z) (R z) (εs k)) := by
        have he : 1 ≤ Real.exp BP * Real.exp (-P z) := by
          rw [← Real.exp_add]; apply Real.one_le_exp
          have := hBP z hz; rw [abs_le] at this; linarith
        have hn := sq_nonneg ‖F k z - G k z‖
        nlinarith [mul_le_mul_of_nonneg_left hw (by positivity : (0 : ℝ) ≤ 4 * Real.exp BP),
          Real.exp_pos BP]
      calc ENNReal.ofReal (‖F k z‖ ^ 2)
          ≤ ENNReal.ofReal (2 * Cf ^ 2 + 4 * Real.exp BP *
              (‖F k z - G k z‖ ^ 2 * stepWeight d (P z) (R z) (εs k))) :=
            ENNReal.ofReal_le_ofReal (by linarith)
        _ ≤ ENNReal.ofReal (2 * Cf ^ 2) + ENNReal.ofReal (4 * Real.exp BP *
              (‖F k z - G k z‖ ^ 2 * stepWeight d (P z) (R z) (εs k))) := ENNReal.ofReal_add_le
        _ = _ := by
          congr 1
          exact ENNReal.ofReal_mul (by positivity)
    calc ∫⁻ z in D, ENNReal.ofReal (‖F k z‖ ^ 2)
        ≤ ∫⁻ z in D, (ENNReal.ofReal (2 * Cf ^ 2) + ENNReal.ofReal (4 * Real.exp BP) *
            ENNReal.ofReal (‖F k z - G k z‖ ^ 2 * stepWeight d (P z) (R z) (εs k))) :=
          setLIntegral_mono' hDo.measurableSet hpt
      _ = ENNReal.ofReal (2 * Cf ^ 2) * volume D + ENNReal.ofReal (4 * Real.exp BP) *
            ∫⁻ z in D, ENNReal.ofReal (‖F k z - G k z‖ ^ 2 *
              stepWeight d (P z) (R z) (εs k)) := by
          rw [lintegral_add_left measurable_const, setLIntegral_const,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ B₂ := by rw [hB₂def]; gcongr; exact hcorr k
  -- Montel
  obtain ⟨ψ, Flim, hψ, hFlim, hconv⟩ := exists_subseq_of_l2_bounded hDo F hF hB₂ hL2
  refine ⟨Flim, hFlim, fun z' hz' => ?_, ?_⟩
  · have h1 : Tendsto (fun k => F (ψ k) (ι z')) atTop (𝓝 (Flim (ι z'))) :=
      hconv.tendsto_at (hιD z' hz')
    have h2 : (fun k => F (ψ k) (ι z')) = fun _ => f z' := funext fun k => hFext (ψ k) z' hz'
    rw [h2] at h1
    exact tendsto_nhds_unique h1 tendsto_const_nhds
  · -- Fatou
    set gk : ℕ → ComplexModel (m + d) → ℝ≥0∞ := fun k z =>
      ENNReal.ofReal (‖F (ψ k) z - G (ψ k) z‖ ^ 2 * stepWeight d (P z) (R z) (εs (ψ k)))
      with hgkdef
    set glim : ComplexModel (m + d) → ℝ≥0∞ := fun z =>
      ENNReal.ofReal (‖Flim z‖ ^ 2 * (Real.exp (-P z) * (R z ^ d)⁻¹ * (Real.log (R z) ^ 2)⁻¹))
      with hglimdef
    have hRs : ContDiff ℝ ∞ R := contDiff_normalWeight m
    have hmeas : ∀ k, AEMeasurable (gk k) (volume.restrict D) := by
      intro k
      refine ENNReal.measurable_ofReal.comp_aemeasurable (ContinuousOn.aemeasurable ?_
        hDo.measurableSet)
      have hFc : ContinuousOn (F (ψ k)) D := (hF (ψ k)).continuousOn
      have hGc : ContinuousOn (G (ψ k)) D := hfPc.mul (Complex.continuous_ofReal.comp
        ((contDiff_chenCutoff (k := ⊤)).continuous.comp (hRc.div_const _))).continuousOn
      have hpos : ∀ z ∈ D, 0 < εs (ψ k) + R z := fun z _ =>
        by linarith [hεs0 (ψ k), normalWeight_nonneg (m + d) m z]
      have hlt : ∀ z ∈ D, εs (ψ k) + R z < 1 := by
        intro z hz
        have h1 := hR4 z hz; have h2 := hεse (ψ k)
        have h3 : Real.exp (-4) < 1 / 2 := by
          have h2' : (2 : ℝ) < Real.exp 4 := by
            have := Real.add_one_lt_exp (show (4 : ℝ) ≠ 0 by norm_num); linarith
          have h4 : Real.exp (-4) * Real.exp 4 = 1 := by rw [← Real.exp_add]; simp
          nlinarith [Real.exp_pos (-4)]
        linarith
      have hwc : ContinuousOn (fun z => stepWeight d (P z) (R z) (εs (ψ k))) D := by
        unfold stepWeight
        refine ((Real.continuous_exp.comp_continuousOn hPc.neg).mul ?_).mul ?_
        · refine ContinuousOn.inv₀ ((continuous_const.add hRc).pow d).continuousOn fun z hz => ?_
          exact (pow_pos (hpos z hz) d).ne'
        · refine ContinuousOn.inv₀ ((Real.continuousOn_log.comp (continuous_const.add hRc).continuousOn
            fun z hz => (hpos z hz).ne').pow 2) fun z hz => ?_
          have := Real.log_neg (hpos z hz) (hlt z hz)
          exact pow_ne_zero 2 this.ne
      exact ((hFc.sub hGc).norm.pow 2).mul hwc
    have hlim : ∀ z ∈ U, Tendsto (fun k => gk k z) atTop (𝓝 (glim z)) := by
      intro z hz
      have hRz : 0 < R z := hz.2.2
      have hR1 : R z < 1 := (hR4 z (hUD hz)).trans (Real.exp_lt_one_iff.mpr (by norm_num))
      have hεψ : Tendsto (fun k => εs (ψ k)) atTop (𝓝 0) := hεslim.comp hψ.tendsto_atTop
      have hF1 : Tendsto (fun k => F (ψ k) z) atTop (𝓝 (Flim z)) := hconv.tendsto_at (hUD hz)
      have hG1 : Tendsto (fun k => G (ψ k) z) atTop (𝓝 0) := by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hεψ.eventually (gt_mem_nhds hRz),
          (hεslim.comp hψ.tendsto_atTop).eventually (lt_mem_nhds (show (-1 : ℝ) < 0 by norm_num))]
          with k hk _
        have hk0 := hεs0 (ψ k)
        simp only [hGdef]
        rw [chenCutoff_of_ge (by rw [le_div_iff₀ hk0]; linarith), Complex.ofReal_zero, mul_zero]
      have hlog0 : Real.log (R z) ≠ 0 := (Real.log_neg hRz hR1).ne
      have hwc : ContinuousAt (fun ε => stepWeight d (P z) (R z) ε) 0 := by
        unfold stepWeight
        refine (continuousAt_const.mul ((continuousAt_id.add continuousAt_const).pow d |>.inv₀ ?_)).mul
          ((((continuousAt_id.add continuousAt_const).log ?_).pow 2).inv₀ ?_)
        · simpa using (pow_pos hRz d).ne'
        · simpa using hRz.ne'
        · simpa using pow_ne_zero 2 hlog0
      have hw1 : Tendsto (fun k => stepWeight d (P z) (R z) (εs (ψ k))) atTop
          (𝓝 (Real.exp (-P z) * (R z ^ d)⁻¹ * (Real.log (R z) ^ 2)⁻¹)) := by
        have := hwc.tendsto.comp hεψ
        simp only [stepWeight, zero_add] at this
        exact this
      have h := ((hF1.sub hG1).norm.pow 2).mul hw1
      rw [sub_zero] at h
      exact (ENNReal.continuous_ofReal.tendsto _).comp h
    have hU_ae := ae_restrict_localPunct (m := m) (d := d) (r' := r') (r'' := r'') hd
    have hle1 : ∫⁻ z in D, ENNReal.ofReal (‖Flim z‖ ^ 2) * ENNReal.ofReal (Real.exp (-P z)) *
        criticalKernel (m + d) m z ≤ ∫⁻ z in D, glim z := by
      refine lintegral_mono_ae (hU_ae.mono fun z hz => le_of_eq ?_)
      have hRz : 0 < R z := hz.2.2
      have hR1 : R z < 1 := (hR4 z (hUD hz)).trans (Real.exp_lt_one_iff.mpr (by norm_num))
      have hlog0 : Real.log (R z) ≠ 0 := (Real.log_neg hRz hR1).ne
      have hx : 0 < R z ^ d * Real.log (R z) ^ 2 := mul_pos (pow_pos hRz d) (by positivity)
      unfold criticalKernel
      rw [show m + d - m = d by omega, ← ENNReal.ofReal_inv_of_pos hx, mul_inv,
        ← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
      simp only [hglimdef]
      congr 1
      ring
    have hle2 : ∫⁻ z in D, glim z ≤ ∫⁻ z in D, liminf (fun k => gk k z) atTop :=
      lintegral_mono_ae (hU_ae.mono fun z hz => le_of_eq ((hlim z hz).liminf_eq).symm)
    have hle3 := lintegral_liminf_le' (μ := volume.restrict D) (u := atTop) hmeas
    have hle4 : liminf (fun k => ∫⁻ z in D, gk k z) atTop ≤ B₁ :=
      liminf_le_of_frequently_le' (Frequently.of_forall fun k => hcorr (ψ k))
    have hB₁eq : B₁ = localGainConst d * I := by
      rw [hB₁def, localGainConst, show (8 : ℝ) * M ^ 2 = 8 * M ^ 2 from rfl,
        ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
      ring
    calc ∫⁻ z in D, ENNReal.ofReal (‖Flim z‖ ^ 2) * ENNReal.ofReal (Real.exp (-P z)) *
          criticalKernel (m + d) m z
        ≤ ∫⁻ z in D, glim z := hle1
      _ ≤ ∫⁻ z in D, liminf (fun k => gk k z) atTop := hle2
      _ ≤ liminf (fun k => ∫⁻ z in D, gk k z) atTop := hle3
      _ ≤ B₁ := hle4
      _ = localGainConst d * I := hB₁eq

end SGPT.Trace.OTExt2
