import SGPT.Trace.OTExt4Lip

/-!
# FPT `lem:critical-gain-initial-gluing`

Blueprint `claude-ot-ext4.tex`, node `claude-ot-ext4:gluing`.  Xia, *Foundations of
pluripotential theory*, q07, `lem:critical-gain-initial-gluing`.

`criticalGainInitialGluingAlong`: for a closed connected submanifold `W` of dimension `m < n` of a
compact Kähler manifold and a normal pole `R` of `W` (`IsGlobalNormalPole`, FPT
`lem:global-normal-pole`), `CriticalGainInitialGluingAlong ω W R` holds: for every line bundle `V`
with a smooth metric, every `Φ ∈ PSH(X, c₁(V, h₀))` and every holomorphic section `f` of `V|_W` in
`𝓘(Φ|_W)` there are `κ > 0` and a glued `G = ∑ η_i F_i` with `G|_W = f`, a pointwise bound `D_G` of
`|∂̄G|²_{ω,h₀}` in every chart and frame vanishing on `W`,
`∫_X (|G|² + D_G) e^{-(1+κ)Φ} R^{-q} (log R)^{-2} < ∞` and
`∫_{R < ε} D_G e^{-Φ} R^{-q} → 0`.

Proof (FPT): local extensions with the critical gain at the points of `W`
(`exists_criticalPatch`; the uniform `κ` is the minimum over a finite subcover), a chart-smooth
partition of unity subordinate to these neighbourhoods and to `X \ W`
(`exists_chartSmooth_partition`), the glued section and its `∂̄`-density (`dbar_glued_le`),
`D_G ≤ C R` (`exists_gluedDensity_le`), and for the decay the splitting
`e^{-Φ} ≤ e^{-(1+κ)Φ} (log R)^{-2} + (log R)^{2/κ}` (`multiplierWeight_one_le_split`, FPT's Hölder
inequality) with `D_G R^{-q} (log R)^{2/κ} ≤ C R^{-(q - 1/2)}`, integrable by
`lintegral_multiplierWeight_logPole_lt_top`, and dominated convergence.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Trace.OTExt4

open Set Filter Metric MeasureTheory Bundle
open scoped Topology ENNReal NNReal Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace
  SGPT.Foundations.Analysis.FirstPass.RegularLocusDense SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
  SGPT.Bergman.QuantizationDraft SGPT.Bergman.PolynomialH0Growth
open HermitianHolomorphicLineBundle
open SGPT.PSH.GlobalL2 (IsOwnFirstChernForm)
open SGPT.Trace.TwistedL2 SGPT.Trace.OTMargin SGPT.Trace.OTExt2

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

/-- `D R^{-q} (log R)^{2/κ} ≤ C R^{-(q - 1/2)}` for `D ≤ C₀ R`, `0 < R < 1`. -/
theorem density_rpow_le {R D C₀ Cκ κ : ℝ} {q : ℕ} (hR : 0 < R) (hR1 : R < 1) (hD : D ≤ C₀ * R)
    (hC₀ : 0 ≤ C₀) (hCκ : ∀ t : ℝ, 0 < t → t < 1 → (Real.log t ^ 2) ^ (1 / κ) ≤ Cκ * t ^ (-(1 / 2 : ℝ))) :
    D * (R ^ q)⁻¹ * (Real.log R ^ 2) ^ (1 / κ) ≤ C₀ * Cκ * R ^ (-((q : ℝ) - 1 / 2)) := by
  have hRq : 0 < R ^ q := pow_pos hR q
  have hL := hCκ R hR hR1
  have hL0 : 0 ≤ (Real.log R ^ 2) ^ (1 / κ) := Real.rpow_nonneg (sq_nonneg _) _
  have hCκ0 : 0 ≤ Cκ * R ^ (-(1 / 2 : ℝ)) := hL0.trans hL
  have hpow : R ^ (-((q : ℝ) - 1 / 2)) = R * (R ^ q)⁻¹ * R ^ (-(1 / 2 : ℝ)) := by
    rw [show -((q : ℝ) - 1 / 2) = (1 + -(q : ℝ)) + -(1 / 2) by ring, Real.rpow_add hR,
      Real.rpow_add hR, Real.rpow_one, Real.rpow_neg hR.le, Real.rpow_natCast]
  rw [hpow]
  calc D * (R ^ q)⁻¹ * (Real.log R ^ 2) ^ (1 / κ)
      ≤ (C₀ * R) * (R ^ q)⁻¹ * (Cκ * R ^ (-(1 / 2 : ℝ))) := by
        gcongr
    _ = C₀ * Cκ * (R * (R ^ q)⁻¹ * R ^ (-(1 / 2 : ℝ))) := by ring

/-- **FPT `lem:critical-gain-initial-gluing`** for a normal pole `R` of a closed connected
submanifold `W` of positive codimension. -/
theorem criticalGainInitialGluingAlong (ωb : KahlerBackground n X) {W : Set X} {m : ℕ}
    (hW : IsClosedConnectedSubmanifold n W m) (hmn : m < n) {R : X → ℝ}
    (hR : IsGlobalNormalPole ωb W R) : CriticalGainInitialGluingAlong ωb hW R := by
  unfold CriticalGainInitialGluingAlong
  intro hk
  let : ChartedSpace (ComplexModel m) W := chartedSpace hk hW.2.2
  have : IsComplexManifold m W := isComplexManifold_chartedSpace hk hW.2.2
  intro V _hV θV _hθV Φ hΦ _hΦW f hf
  set μ := IntegrationCurrent.kahlerVolume ωb with hμdef
  have hμ := KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume ωb
  have hWc : IsCompact W := hW.1.isCompact
  have hΦq : ManifoldQuasiPlurisubharmonic (n := n) Φ := hΦ.1.quasiPlurisubharmonic
  have hΦm : Measurable Φ := hΦq.upperSemicontinuous.measurable
  obtain ⟨x₀, hx₀⟩ := hW.2.1.nonempty
  have : Nonempty X := ⟨x₀⟩
  obtain ⟨MΦ, hMΦ⟩ := exists_real_upper_bound_of_upperSemicontinuous hΦq.upperSemicontinuous
    hΦq.ne_top
  -- the local extensions
  choose κp hκp B' K B Fp hB'o hBo hKc hmem hB'K hKB hhol hagree hgain using
    fun p : W => exists_criticalPatch V.Fiber hμ hk hmn hW.2.2 hR hΦq hf p
  obtain ⟨t, ht⟩ := hWc.elim_finite_subcover (fun p : W => B' p) hB'o
    (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hmem ⟨x, hx⟩⟩)
  have htne : t.Nonempty := by
    obtain ⟨p, hp, -⟩ := mem_iUnion₂.mp (ht hx₀); exact ⟨p, hp⟩
  set κ : ℝ := t.inf' htne κp with hκdef
  have hκ0 : 0 < κ := (Finset.lt_inf'_iff htne).mpr fun p _ => hκp p
  have hκle : ∀ p ∈ t, κ ≤ κp p := fun p hp => Finset.inf'_le _ hp
  -- the cover of `X`
  let U : Option t → Set X := fun i => match i with
    | none => Wᶜ
    | some p => B' p.1
  let F : Option t → (x : X) → V.Fiber x := fun i => match i with
    | none => fun _ => 0
    | some p => Fp p.1
  have hUo : ∀ i, IsOpen (U i) := by
    rintro (_ | p)
    · exact hW.1.isOpen_compl
    · exact hB'o p.1
  have hcov : ∀ x, ∃ i, x ∈ U i := by
    intro x
    by_cases hx : x ∈ W
    · obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp (ht hx)
      exact ⟨some ⟨p, hp⟩, hxp⟩
    · exact ⟨none, hx⟩
  have hFhol : ∀ i, SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) V.Fiber (F i) (U i) := by
    rintro (_ | p)
    · exact isHolomorphicSectionOn_zero V.Fiber _
    · exact (hhol p.1).mono ((hB'K p.1).trans (hKB p.1))
  have hFW : ∀ i, ∀ y : W, y.1 ∈ U i → F i y = f y := by
    rintro (_ | p) y hy
    · exact absurd y.2 hy
    · exact hagree p.1 y ((hKB p.1) ((hB'K p.1) hy))
  have hagr : ∀ a b, ∀ x ∈ W, x ∈ U a → x ∈ U b → F a x = F b x := fun a b x hx ha hb => by
    rw [hFW a ⟨x, hx⟩ ha, hFW b ⟨x, hx⟩ hb]
  obtain ⟨η, hηs, hη0, hη1, hηU⟩ := exists_chartSmooth_partition (n := n) U hUo hcov
  choose Mi hMi0 hMi using fun i => exists_holDerivSq_le_kahlerQuad ωb (hηs i)
  set M : ℝ := ∑ i, Mi i with hMdef
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun i _ => hMi0 i
  have hM : ∀ i, ∀ (c : ComplexChart n X), ∀ z ∈ c.val.target, ∀ v : ComplexModel n,
      holDerivSq (fun y => η i (c.val.symm y)) z v ≤ M * kahlerQuad ωb c z v := fun i c z hz v =>
    (hMi i c z hz v).trans (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun j _ => hMi0 j) (Finset.mem_univ i)) (kahlerQuad_nonneg ωb c hz v))
  set G := glued V η U F with hG
  set Dg := gluedDensity V M η U F with hDg
  -- `G = f` on `W`
  have hGW : ∀ y : W, G y = f y := by
    intro y
    rw [hG, glued_apply]
    have h : ∀ i, ((η i y : ℝ) : ℂ) • extSec V (U i) (F i) y = ((η i y : ℝ) : ℂ) • f y := by
      intro i
      by_cases hyi : y.1 ∈ tsupport (η i)
      · rw [extSec_of_mem V (hηU i hyi), hFW i y (hηU i hyi)]
      · rw [image_eq_zero_of_notMem_tsupport hyi, Complex.ofReal_zero, zero_smul, zero_smul]
    rw [Finset.sum_congr rfl fun i _ => h i, ← Finset.sum_smul, ← Complex.ofReal_sum, hη1,
      Complex.ofReal_one, one_smul]
  -- `D_G = 0` on `W`
  have hDgW : ∀ x ∈ W, Dg x = 0 := by
    intro x hx
    have h0 : ∀ a b, (tsupport (η a) ∩ tsupport (η b)).indicator
        (fun x => ‖extSec V (U a) (F a) x - extSec V (U b) (F b) x‖ ^ 2) x = 0 := by
      intro a b
      by_cases hab : x ∈ tsupport (η a) ∩ tsupport (η b)
      · rw [indicator_of_mem hab, extSec_of_mem V (hηU a hab.1), extSec_of_mem V (hηU b hab.2),
          hagr a b x hx (hηU a hab.1) (hηU b hab.2), sub_self, norm_zero]
        norm_num
      · rw [indicator_of_notMem hab]
    rw [hDg, gluedDensity]
    simp only [h0, Finset.sum_const_zero, mul_zero]
  -- the critical weight
  set k : X → ℝ := fun x => (R x ^ (n - m) * Real.log (R x) ^ 2)⁻¹ with hkdef
  have hk0 : ∀ x, 0 ≤ k x := fun x => inv_nonneg.mpr (mul_nonneg (pow_nonneg (hR.nonneg x) _)
    (sq_nonneg _))
  have hkm : Measurable k := by
    have hRc := hR.continuous
    exact (((hRc.pow _).measurable).mul ((Real.measurable_log.comp hRc.measurable).pow_const 2)).inv
  -- the exponent `1 + κ` from the exponents `1 + κ_p`
  have hmono : ∀ p ∈ t, ∀ x, multiplierWeight (1 + κ) (Φ x) ≤
      ENNReal.ofReal (Real.exp ((1 + κ) * ((1 + κp p) / (1 + κ) - 1) * MΦ)) *
        multiplierWeight (1 + κp p) (Φ x) := by
    intro p hp x
    have h1 : (1 : ℝ) ≤ (1 + κp p) / (1 + κ) := by
      rw [le_div_iff₀ (by linarith)]; linarith [hκle p hp]
    have h := multiplierWeight_le_mul_of_le (by linarith : (0 : ℝ) ≤ 1 + κ) h1 (hMΦ x)
    rwa [mul_div_cancel₀ _ (by linarith : (1 : ℝ) + κ ≠ 0)] at h
  have hgainκ : ∀ p ∈ t, ∫⁻ x in K p, ENNReal.ofReal (‖Fp p x‖ ^ 2) *
      multiplierWeight (1 + κ) (Φ x) * ENNReal.ofReal (k x) ∂μ ≠ ⊤ := by
    intro p hp
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top
      (r := Real.exp ((1 + κ) * ((1 + κp p) / (1 + κ) - 1) * MΦ))) (hgain p)) ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun x => ?_
    calc ENNReal.ofReal (‖Fp p x‖ ^ 2) * multiplierWeight (1 + κ) (Φ x) * ENNReal.ofReal (k x)
        ≤ ENNReal.ofReal (‖Fp p x‖ ^ 2) * (ENNReal.ofReal (Real.exp ((1 + κ) *
            ((1 + κp p) / (1 + κ) - 1) * MΦ)) * multiplierWeight (1 + κp p) (Φ x)) *
            ENNReal.ofReal (k x) := by gcongr; exact hmono p hp x
      _ = _ := by ring
  -- finiteness on the supports of the cut-offs
  have hfin : ∀ i, ∫⁻ x in tsupport (η i), ENNReal.ofReal (‖extSec V (U i) (F i) x‖ ^ 2) *
      multiplierWeight (1 + κ) (Φ x) * ENNReal.ofReal (k x) ∂μ ≠ ⊤ := by
    rintro (_ | p)
    · have h0 : ∀ x, extSec V (U none) (F none) x = 0 := fun x => by
        classical
        simp only [extSec]; split_ifs <;> rfl
      simp [h0]
    · refine ne_top_of_le_ne_top (hgainκ p.1 p.2) ?_
      refine (setLIntegral_congr_fun (isClosed_tsupport _).measurableSet fun x hx => ?_).trans_le
        (lintegral_mono_set ((hηU (some p)).trans ((hB'K p.1))))
      rw [extSec_of_mem V (hηU (some p) hx)]
  -- the strengthened initial norm
  set S : X → ℝ := fun x => ∑ i, (tsupport (η i)).indicator
    (fun x => ‖extSec V (U i) (F i) x‖ ^ 2) x with hS
  obtain ⟨Cg, hCgdef⟩ : ∃ Cg : ℝ,
      Cg = (Fintype.card (Option t) : ℝ) + 4 * (Fintype.card (Option t) : ℝ) ^ 3 * M := ⟨_, rfl⟩
  have hCg0 : 0 ≤ Cg := by rw [hCgdef]; positivity
  have hGD : ∀ x, ‖G x‖ ^ 2 + Dg x ≤ Cg * S x := fun x => by
    have h1 := norm_glued_sq_le V (U := U) (F := F) hη0 hη1 x
    have h2 := gluedDensity_le V (η := η) (U := U) (F := F) hM0 x
    have hSx : S x = ∑ i, (tsupport (η i)).indicator
        (fun x => ‖extSec V (U i) (F i) x‖ ^ 2) x := rfl
    calc ‖G x‖ ^ 2 + Dg x ≤ _ := add_le_add h1 h2
      _ = Cg * S x := by rw [hSx, hCgdef]; ring
  have hsum_m : ∀ i, Measurable fun x => (tsupport (η i)).indicator
      (fun x => ENNReal.ofReal (‖extSec V (U i) (F i) x‖ ^ 2)) x *
        multiplierWeight (1 + κ) (Φ x) * ENNReal.ofReal (k x) := fun i =>
    ((measurable_indicator_closed_of_continuousOn (hUo i) (isClosed_tsupport _) (hηU i)
      (ENNReal.continuous_ofReal.comp_continuousOn
        ((continuousOn_norm_extSec V (hFhol i)).pow 2))).mul
      ((multiplierWeight_antitone (by linarith)).measurable.comp hΦm)).mul
      (ENNReal.measurable_ofReal.comp hkm)
  have hstrong : ∫⁻ x, ENNReal.ofReal ((‖G x‖ ^ 2 + Dg x) * k x) *
      multiplierWeight (1 + κ) (Φ x) ∂μ ≠ ⊤ := by
    have hpt : ∀ x, ENNReal.ofReal ((‖G x‖ ^ 2 + Dg x) * k x) * multiplierWeight (1 + κ) (Φ x) ≤
        ENNReal.ofReal Cg * ∑ i, (tsupport (η i)).indicator
          (fun x => ENNReal.ofReal (‖extSec V (U i) (F i) x‖ ^ 2)) x *
            multiplierWeight (1 + κ) (Φ x) * ENNReal.ofReal (k x) := by
      intro x
      have hSk : ENNReal.ofReal (S x * k x) = ∑ i, (tsupport (η i)).indicator
          (fun x => ENNReal.ofReal (‖extSec V (U i) (F i) x‖ ^ 2)) x * ENNReal.ofReal (k x) := by
        rw [hS, Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg fun i _ => mul_nonneg
          (indicator_nonneg (fun _ _ => by positivity) _) (hk0 x)]
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases hx : x ∈ tsupport (η i)
        · rw [indicator_of_mem hx, indicator_of_mem hx, ENNReal.ofReal_mul (sq_nonneg _)]
        · rw [indicator_of_notMem hx, indicator_of_notMem hx, zero_mul, zero_mul,
            ENNReal.ofReal_zero]
      calc ENNReal.ofReal ((‖G x‖ ^ 2 + Dg x) * k x) * multiplierWeight (1 + κ) (Φ x)
          ≤ ENNReal.ofReal (Cg * (S x * k x)) * multiplierWeight (1 + κ) (Φ x) := by
            refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
            calc (‖G x‖ ^ 2 + Dg x) * k x ≤ Cg * S x * k x :=
                  mul_le_mul_of_nonneg_right (hGD x) (hk0 x)
              _ = Cg * (S x * k x) := by ring
        _ = ENNReal.ofReal Cg * ∑ i, (tsupport (η i)).indicator
            (fun x => ENNReal.ofReal (‖extSec V (U i) (F i) x‖ ^ 2)) x *
              multiplierWeight (1 + κ) (Φ x) * ENNReal.ofReal (k x) := by
            rw [ENNReal.ofReal_mul hCg0, hSk, mul_assoc, Finset.sum_mul]
            congr 1
            refine Finset.sum_congr rfl fun i _ => ?_
            ring
    refine ne_top_of_le_ne_top ?_ (lintegral_mono hpt)
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_finsetSum' _ fun i _ => (hsum_m i).aemeasurable]
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.sum_ne_top.mpr fun i _ => ?_)
    have hind : (fun x => (tsupport (η i)).indicator
        (fun x => ENNReal.ofReal (‖extSec V (U i) (F i) x‖ ^ 2)) x *
          multiplierWeight (1 + κ) (Φ x) * ENNReal.ofReal (k x)) =
        (tsupport (η i)).indicator (fun x => ENNReal.ofReal (‖extSec V (U i) (F i) x‖ ^ 2) *
          multiplierWeight (1 + κ) (Φ x) * ENNReal.ofReal (k x)) := by
      funext x
      by_cases hx : x ∈ tsupport (η i)
      · rw [indicator_of_mem hx, indicator_of_mem hx]
      · rw [indicator_of_notMem hx, indicator_of_notMem hx, zero_mul, zero_mul]
    rw [hind, lintegral_indicator (isClosed_tsupport _).measurableSet]
    exact hfin i
  -- the decay of the gluing error
  obtain ⟨CD, hCD0, hCD⟩ := exists_gluedDensity_le V hμ hW.2.2 hWc hmn hR hUo hηU hFhol hagr hM0
  obtain ⟨Cκ, hCκ0, hCκ⟩ := rpow_log_sq_le (s := 1 / κ) (by positivity)
  have hDgm : Measurable Dg := measurable_gluedDensity V hUo hηU hFhol M
  have hRc := hR.continuous
  have hR1 : ∀ x, R x < 1 := fun x => (hR.lt_exp x).trans
    ((Real.exp_lt_exp.mpr (show (-4 : ℝ) < 0 by norm_num)).trans_eq Real.exp_zero)
  set q : ℕ := n - m with hq
  have hq1 : 1 ≤ q := by omega
  set hfun : X → ℝ≥0∞ := fun x => ENNReal.ofReal (Dg x * (R x ^ q)⁻¹) *
    multiplierWeight 1 (Φ x) with hhfun
  set Bfun : X → ℝ≥0∞ := fun x => ENNReal.ofReal (Dg x * (R x ^ q)⁻¹ *
    (Real.log (R x) ^ 2) ^ (1 / κ)) with hBfun
  have hBm : Measurable Bfun := by
    refine ENNReal.measurable_ofReal.comp ((hDgm.mul ((hRc.pow _).measurable.inv)).mul ?_)
    exact ((Real.measurable_log.comp hRc.measurable).pow_const 2).pow_const _
  have hBfin : ∫⁻ x, Bfun x ∂μ < ⊤ := by
    have hc0 : (0 : ℝ) ≤ (q : ℝ) - 1 / 2 := by
      have : (1 : ℝ) ≤ q := by exact_mod_cast hq1
      linarith
    have hcq : (q : ℝ) - 1 / 2 < ((n - m : ℕ) : ℝ) := by rw [← hq]; linarith
    have hpt : ∀ x, Bfun x ≤ ENNReal.ofReal (CD * Cκ) *
        multiplierWeight ((q : ℝ) - 1 / 2) (logPole R x) := by
      intro x
      by_cases hx : x ∈ W
      · have : R x = 0 := (hR.eq_zero_iff x).mpr hx
        simp only [hBfun, this, zero_pow (by omega : q ≠ 0), inv_zero, mul_zero, zero_mul,
          ENNReal.ofReal_zero]
        exact zero_le
      · have hRx := hR.pos_of_notMem hx
        rw [multiplierWeight_logPole hRx, ← ENNReal.ofReal_mul (by positivity)]
        exact ENNReal.ofReal_le_ofReal
          (density_rpow_le hRx (hR1 x) (hCD x) hCD0 hCκ)
    refine (lintegral_mono hpt).trans_lt ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (lintegral_multiplierWeight_logPole_lt_top hμ hW.2.2 hWc hmn hR hc0 hcq)
  have hsplit : ∀ x, hfun x ≤ ENNReal.ofReal ((‖G x‖ ^ 2 + Dg x) * k x) *
      multiplierWeight (1 + κ) (Φ x) + Bfun x := by
    intro x
    by_cases hx : x ∈ W
    · simp only [hhfun, hDgW x hx, zero_mul, ENNReal.ofReal_zero]
      exact zero_le
    · have hRx := hR.pos_of_notMem hx
      have hL : 0 < Real.log (R x) ^ 2 := by
        have : Real.log (R x) < 0 := Real.log_neg hRx (hR1 x)
        nlinarith
      have hD0 : 0 ≤ Dg x * (R x ^ q)⁻¹ :=
        mul_nonneg (gluedDensity_nonneg V hM0 x) (inv_nonneg.mpr (pow_nonneg hRx.le _))
      have h1 := multiplierWeight_one_le_split hκ0 hL (Φ x)
      calc hfun x ≤ ENNReal.ofReal (Dg x * (R x ^ q)⁻¹) *
            (multiplierWeight (1 + κ) (Φ x) * ENNReal.ofReal (Real.log (R x) ^ 2)⁻¹ +
              ENNReal.ofReal ((Real.log (R x) ^ 2) ^ (1 / κ))) := by
            simp only [hhfun]; gcongr
        _ = ENNReal.ofReal (Dg x * (R x ^ q)⁻¹ * (Real.log (R x) ^ 2)⁻¹) *
              multiplierWeight (1 + κ) (Φ x) + Bfun x := by
            show _ = _ + ENNReal.ofReal (Dg x * (R x ^ q)⁻¹ * (Real.log (R x) ^ 2) ^ (1 / κ))
            rw [mul_add, ENNReal.ofReal_mul hD0, ENNReal.ofReal_mul hD0]
            ring
        _ ≤ _ := by
            refine add_le_add_left (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _) _
            have hkx : k x = (R x ^ q * Real.log (R x) ^ 2)⁻¹ := rfl
            have : Dg x * (R x ^ q)⁻¹ * (Real.log (R x) ^ 2)⁻¹ = Dg x * k x := by
              rw [hkx, mul_inv]; ring
            rw [this]
            exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (sq_nonneg _)) (hk0 x)
  have hhfin : ∫⁻ x, hfun x ∂μ ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (lintegral_mono hsplit)
    rw [lintegral_add_right _ hBm]
    exact ENNReal.add_ne_top.mpr ⟨hstrong, hBfin.ne⟩
  have hhm : Measurable hfun :=
    (ENNReal.measurable_ofReal.comp (hDgm.mul ((hRc.pow _).measurable.inv))).mul
      ((multiplierWeight_antitone zero_le_one).measurable.comp hΦm)
  have hdecay : Tendsto (fun ε : ℝ => ∫⁻ x in {x | R x < ε}, hfun x ∂μ) (𝓝[>] 0) (𝓝 0) := by
    have hmeas : ∀ ε : ℝ, MeasurableSet {x | R x < ε} := fun ε =>
      measurableSet_lt hRc.measurable measurable_const
    have hlim := tendsto_lintegral_filter_of_dominated_convergence (μ := μ) (l := 𝓝[>] (0 : ℝ))
      (F := fun ε => {x | R x < ε}.indicator hfun) (f := fun _ => 0) hfun
      (Eventually.of_forall fun ε => hhm.indicator (hmeas ε))
      (Eventually.of_forall fun ε => Eventually.of_forall fun x => indicator_le_self _ _ x)
      hhfin (Eventually.of_forall fun x => ?_)
    · rw [lintegral_zero] at hlim
      refine hlim.congr fun ε => ?_
      rw [lintegral_indicator (hmeas ε)]
    · by_cases hx : x ∈ W
      · have : hfun x = 0 := by simp only [hhfun, hDgW x hx, zero_mul, ENNReal.ofReal_zero]
        refine tendsto_const_nhds.congr fun ε => ?_
        by_cases hε : x ∈ {x | R x < ε}
        · rw [indicator_of_mem hε, this]
        · rw [indicator_of_notMem hε]
      · have hRx := hR.pos_of_notMem hx
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [Ioo_mem_nhdsGT hRx] with ε hε
        rw [indicator_of_notMem (show x ∉ {x | R x < ε} from fun h => by
          simp only [mem_ofPred_eq] at h; linarith [hε.2])]
  refine ⟨κ, hκ0, G, Dg, ⟨Option t, inferInstance, U, F, η, hUo, hFhol, fun i y hy => hFW i y hy,
    ?_, hηs, fun i => (isClosed_tsupport _).isCompact, hηU,
    ⟨univ, isOpen_univ, subset_univ _, fun x _ => hη1 x⟩, fun x => rfl⟩,
    isSmoothSectionOn_glued V hηs hUo hηU hFhol, hGW, gluedDensity_nonneg V hM0, hDgW,
    fun c e z hz v => dbar_glued_le V ωb hηs hη0 hη1 hUo hηU hFhol hM c e hz v, hstrong, hdecay⟩
  · rintro (_ | p)
    · simp [F]
    · refine ne_top_of_le_ne_top (hgainκ p.1 p.2) ?_
      exact lintegral_mono_set (hB'K p.1)

end SGPT.Trace.OTExt4
