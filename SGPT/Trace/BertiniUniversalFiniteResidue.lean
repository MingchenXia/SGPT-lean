import SGPT.Trace.OTResMain

/-! Actual prescribed-normal-pole residue estimate for arbitrary CLOSED
REGULAR W, possibly disconnected/empty/dimension0, for weights finite on W. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniUniversal
open Set Filter Metric MeasureTheory Bundle
open scoped Topology ENNReal NNReal Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.RegularLocusDense SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Foundations.Analysis.Pending.ActualOriginalSquaredDensityGentle
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.PolynomialH0Growth
open SGPT.Trace.TwistedL2 HermitianHolomorphicLineBundle
open SGPT.PSH.GlobalL2 (IsOwnFirstChernForm)
open SGPT.Trace.OTMargin (fcoord finv finv_mem continuousOn_finv fcoord_finv finv_fcoord
  normalWeight lintegral_finv_image_le lintegral_le_finv_image)
open SGPT.Trace.OTExt2 (IsGlobalNormalPole IsCriticalGainGluing)
open SGPT.Trace.OTRes SGPT.Trace.OTExt4
section Definition
variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
def regularFiniteWeightResidueEstimate (ωb : KahlerBackground n X) {W : Set X} {m : ℕ}
    (_hclosed : IsClosed W) (hkn : m ≤ n)
    (hreg : ∀ x ∈ W, RegularAtDim (n := n) W x m) (R : X → ℝ) : Prop :=
  let hk : m ≤ n := hkn
  letI : ChartedSpace (ComplexModel m) W := chartedSpace hk hreg
  haveI : IsComplexManifold m W := isComplexManifold_chartedSpace hk hreg
  haveI : CompactSpace W := isCompact_iff_compactSpace.mp _hclosed.isCompact
  letI : MeasurableSpace W := borel W
  haveI : BorelSpace W := ⟨rfl⟩
  ∃ CY : ℝ, 0 < CY ∧
  ∀ (V : HermitianHolomorphicLineBundle.{0, 0} n X), IsSourceSmoothHermitianMetric V →
  ∀ θV : ClosedRealOneOneForm n X, IsOwnFirstChernForm V θV →
  ∀ Φ : X → EReal, IsThetaPshPotential θV.val Φ →
    (∃ (c : ℚ) (𝔞 : GermIdeal n X), HasGentleAnalyticSingularitiesOfType (n := n) Φ c 𝔞) →
    (∀ y : W, Φ y ≠ ⊥) →
  ∀ f : (y : W) → V.Fiber y,
    IsAlongMultiplierSection V.Fiber (m := m) 1 (fun y : W => Φ y) f →
  ∀ κ : ℝ, 0 < κ → ∀ G : (x : X) → V.Fiber x,
    IsCriticalGainGluing (n := n) V.Fiber (IntegrationCurrent.kahlerVolume ωb) W (n - m) R Φ κ f G →
    limsup (fun ε : ℝ => ∫⁻ x in {x | ε / 2 ≤ R x ∧ R x ≤ ε},
        ENNReal.ofReal (‖G x‖ ^ 2 * (R x ^ (n - m))⁻¹) * multiplierWeight 1 (Φ x)
          ∂(IntegrationCurrent.kahlerVolume ωb)) (𝓝[>] 0) ≤
      ENNReal.ofReal CY * ∫⁻ y : W, ENNReal.ofReal (‖f y‖ ^ 2) * multiplierWeight 1 (Φ y)
        ∂(IntegrationCurrent.kahlerVolume (SubmanifoldKahlerRestriction.kahlerBackground hk hreg ωb))

end Definition
section Residue
variable {m d : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + d)) X]
  [IsComplexManifold (m + d) X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
theorem regularFiniteWeight_normalResidue_aux (ωb : KahlerBackground (m + d) X) {W : Set X}
    (hclosed : IsClosed W) (hreg : ∀ x ∈ W, RegularAtDim (n := m + d) W x m)
    (R : X → ℝ) (hR : IsGlobalNormalPole ωb W R) :
    regularFiniteWeightResidueEstimate ωb hclosed (Nat.le_add_right m d) hreg R := by
  unfold regularFiniteWeightResidueEstimate
  intro hk
  let _ : ChartedSpace (ComplexModel m) W := chartedSpace hk hreg
  have _ : IsComplexManifold m W := isComplexManifold_chartedSpace hk hreg
  have _ : CompactSpace W := isCompact_iff_compactSpace.mp hclosed.isCompact
  let _ : MeasurableSpace W := borel W
  have _ : BorelSpace W := ⟨rfl⟩
  have hq : m + d - m = d := Nat.add_sub_cancel_left m d
  rw [hq]
  set μ := IntegrationCurrent.kahlerVolume ωb with hμdef
  have hμ : IsSmoothPositiveVolume (n := m + d) μ :=
    KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume ωb
  set μW := IntegrationCurrent.kahlerVolume
    (SubmanifoldKahlerRestriction.kahlerBackground hk hreg ωb) with hμWdef
  have hμW : IsSmoothPositiveVolume (n := m) μW :=
    KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume _
  -- the pieces
  choose r cR hr0 hcR0 hKt hcomp using fun p : W => exists_piece hreg hR p
  set Fd : W → FlatData (m + d) m X W := fun p => FlatData.ofRegularAtDim (hreg p.1 p.2)
    with hFddef
  set K : W → Set (ComplexModel (m + d)) := fun p => closedLocalDom (m + d) m (r p) (r p)
    with hKdef
  have hKc : ∀ p, IsCompact (K p) := fun p => SGPT.Trace.OTExt4.isCompact_closedLocalDom _ _ _ _
  have hKt' : ∀ p, K p ⊆ (Fd p).flat.target := hKt
  set O : W → Set X := fun p => finv (Fd p) '' SGPT.Trace.OTExt2.localDom (m + d) m (r p) (r p)
    with hOdef
  have hDK : ∀ p, SGPT.Trace.OTExt2.localDom (m + d) m (r p) (r p) ⊆ K p := fun p =>
    SGPT.Trace.OTExt4.localDom_subset_closedLocalDom _ _ _ _
  have hOo : ∀ p, IsOpen (O p) := fun p =>
    SGPT.Trace.OTExt4.isOpen_finv_image' (Fd p) (SGPT.Trace.OTExt2.isOpen_localDom m _ _)
      ((hDK p).trans (hKt' p))
  have hpO : ∀ p : W, p.1 ∈ O p := by
    intro p
    have hreg := hreg p.1 p.2
    have hz0 : (Fd p).flat ((Fd p).amb.val p.1) = 0 := hreg.2.2.choose_spec.2.1
    have hxsrc : p.1 ∈ (Fd p).ambSource := FlatData.mem_ambSource_ofRegularAtDim hreg
    refine ⟨0, ⟨?_, ?_⟩, ?_⟩
    · have : SGPT.Trace.OTExt2.tanWeight (m + d) m 0 = 0 := by simp [SGPT.Trace.OTExt2.tanWeight]
      rw [this]; have := hr0 p; positivity
    · have : normalWeight (m + d) m (0 : ComplexModel (m + d)) = 0 :=
        (SGPT.Trace.OTMargin.normalWeight_eq_zero_iff _).mpr fun i _ => rfl
      rw [this]; have := hr0 p; positivity
    · have := finv_fcoord (Fd p) hxsrc
      rwa [show fcoord (Fd p) p.1 = 0 from hz0] at this
  obtain ⟨t, ht⟩ := hclosed.isCompact.elim_finite_subcover O hOo
    (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hpO ⟨x, hx⟩⟩)
  obtain ⟨ε₀, hε₀, hε₀O⟩ := exists_pos_imp_mem hR.continuous
    (isOpen_biUnion fun p _ => hOo p) (fun x hx => ht ((hR.eq_zero_iff x).mp
      (le_antisymm hx (hR.nonneg x))))
  -- the constants
  choose Cμ hCμ0 hCμ using fun p : W => lintegral_finv_image_le (Fd p) hμ (hKc p) (hKt' p)
  have hballt : ∀ p : W, closedBall (0 : ComplexModel m) (r p) ⊆
      (complexChartAt (n := m) p).val.target := fun p ζ hζ =>
    hKt' p (coordinateInclusion_mem_closedLocalDom (d := d) hζ)
  choose CW hCW0 hCW using fun p : W =>
    exists_lintegral_chart_le hμW (complexChartAt (n := m) p) (isCompact_closedBall _ _) (hballt p)
  have hsymm : ∀ p : W, ∀ ζ ∈ closedBall (0 : ComplexModel m) (r p),
      (((complexChartAt (n := m) p).val.symm ζ : W) : X) =
        finv (Fd p) (coordinateInclusion (m + d) m ζ) := fun p ζ hζ =>
    FlatData.invPoint_val (Fd p) (hballt p hζ)
  set vD : ℝ≥0∞ := volume (ball (0 : ComplexModel d) 1) with hvDdef
  have hvD : vD ≠ ⊤ := measure_ball_lt_top.ne
  set CY : ℝ := 1 + ∑ p ∈ t, Cμ p * (2 / cR p) ^ d * vD.toReal * CW p with hCYdef
  have hCY0 : 0 < CY := by
    have : 0 ≤ ∑ p ∈ t, Cμ p * (2 / cR p) ^ d * vD.toReal * CW p :=
      Finset.sum_nonneg fun p _ => by
        have := hCμ0 p; have := hCW0 p; have := hcR0 p; positivity
    linarith
  refine ⟨CY, hCY0, ?_⟩
  intro V hV θV _ Φ hΦ hgent hFinite f _ κ hκ G hG
  classical
  obtain ⟨c, 𝔞, hga⟩ := hgent
  set cr : ℝ := (c : ℝ) with hcrdef
  have hcg : (0 : ℝ) < cr := by rw [hcrdef]; exact_mod_cast hga.2.1.1
  set ψ : X → ℝ := gentlePsi c Φ with hψdef
  have hψs : ChartSmooth (n := m + d) ψ := chartSmooth_gentlePsi hga
  have hψc : Continuous ψ := continuous_gentlePsi hga
  have hw : ∀ (α : ℝ) (x : X), multiplierWeight α (Φ x) = ENNReal.ofReal (ψ x) ^ (-(α * cr)) :=
    multiplierWeight_eq_gentlePsi_rpow hga
  have hwm : ∀ α : ℝ, Measurable fun x => multiplierWeight α (Φ x) := fun α => by
    simp_rw [hw]
    exact (ENNReal.continuous_rpow_const.comp (ENNReal.continuous_ofReal.comp hψc)).measurable
  -- the glued section
  obtain ⟨ι, _, U, F, η, hUo, hFhol, hFf, -, hηs, -, hηU, ⟨N, -, hWN, hsum⟩, hGeq⟩ := id hG
  have hGs : IsSmoothSectionOn V G univ := by
    have h := isSmoothSectionOn_glued V hηs hUo hηU hFhol
    have : G = glued V η U F := funext hGeq
    rwa [this]
  set g : X → ℝ := fun x => ‖G x‖ ^ 2 with hgdef
  have hgs : ChartSmooth (n := m + d) g := chartSmooth_normSq V hV hGs
  have hgc : Continuous g := SGPT.Trace.OTRes.continuous_of_chartSmooth hgs
  have hGf : ∀ y : W, G y = f y := by
    intro y
    rw [hGeq y]
    have h1 : ∀ i, ((η i y : ℝ) : ℂ) • (if (y : X) ∈ U i then F i y else 0) =
        ((η i y : ℝ) : ℂ) • f y := by
      intro i
      by_cases hη : η i y = 0
      · simp [hη]
      · have hyU : (y : X) ∈ U i := hηU i (subset_tsupport _ hη)
        rw [if_pos hyU, hFf i y hyU]
    simp_rw [h1]
    rw [← Finset.sum_smul, ← Complex.ofReal_sum, hsum y (hWN y.2), Complex.ofReal_one, one_smul]
  -- the critical integral of `G` and Skoda on `W`
  have hIG := lintegral_glued_crit_ne_top V hG (hwm (1 + κ)) hR.continuous hR.nonneg
  have hψpos (y : W) : 0 < ψ y :=
    (SGPT.Trace.OTExt5.gentleExp_pos_iff hga.2.1.1 (fun x => hΦ.1.quasiPlurisubharmonic.ne_top x) y.val).mpr (hFinite y)
  let β : ℝ := 1
  have hβ0 : 0 < β := by norm_num [β]
  have hβW : (∫⁻ y : W, ENNReal.ofReal (ψ y) ^ (-β) ∂μW) ≠ ⊤ := by
    have hInv : Continuous (fun y : W => (ψ y)⁻¹) :=
      (hψc.comp continuous_subtype_val).inv₀ (fun y => (hψpos y).ne')
    obtain ⟨M,hM⟩ := isCompact_univ.exists_bound_of_continuousOn hInv.continuousOn
    have hb (y : W) : ENNReal.ofReal (ψ y) ^ (-β) ≤ ENNReal.ofReal M := by
      change ENNReal.ofReal (ψ y) ^ (-1 : ℝ) ≤ _
      rw [ENNReal.rpow_neg_one,← ENNReal.ofReal_inv_of_pos (hψpos y)]
      exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans
        ((Real.norm_eq_abs _).symm.le.trans (hM y (mem_univ y))))
    have hconst : (∫⁻ _y : W, ENNReal.ofReal M ∂μW) < ⊤ := by
      rw [lintegral_const]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top μW univ)
    exact ne_top_of_lt ((lintegral_mono hb).trans_lt hconst)
  set IW : ℝ≥0∞ := ∫⁻ y : W, ENNReal.ofReal (‖f y‖ ^ 2) * multiplierWeight 1 (Φ y) ∂μW
    with hIWdef
  set A : W → ℝ → ℝ≥0∞ := fun p ε =>
    ∫⁻ z in K p ∩ {z | ε / 2 ≤ R (finv (Fd p) z) ∧ R (finv (Fd p) z) ≤ ε},
      ENNReal.ofReal (g (finv (Fd p) z) * (R (finv (Fd p) z) ^ d)⁻¹) *
        ENNReal.ofReal (ψ (finv (Fd p) z)) ^ (-cr) with hAdef
  -- the estimate on one piece
  have hpiece : ∀ p : W, limsup (A p) (𝓝[>] 0) ≤
      ENNReal.ofReal ((2 / cR p) ^ d) * vD * (ENNReal.ofReal (CW p) * IW) := by
    intro p
    have hKcv : Convex ℝ (K p) := convex_closedLocalDom _ _ (hr0 p).le (hr0 p).le
    obtain ⟨Lg, hLg0, hLg⟩ := exists_lipschitz_flat (Fd p) hgs (hKc p) (hKt' p) hKcv
    obtain ⟨Lψ, hLψ0, hLψ⟩ := exists_lipschitz_flat (Fd p) hψs (hKc p) (hKt' p) hKcv
    have hfinvc : ContinuousOn (finv (Fd p)) (K p) := (continuousOn_finv (Fd p)).mono (hKt' p)
    obtain ⟨Mg, hMg⟩ := (hKc p).exists_bound_of_continuousOn (hgc.comp_continuousOn hfinvc)
    -- the critical gain in the coordinates
    obtain ⟨C', -, hC'⟩ := lintegral_le_finv_image (Fd p) hμ (hKc p) (hKt' p)
    have hcritm : Measurable fun x => ENNReal.ofReal (g x * (R x ^ d * Real.log (R x) ^ 2)⁻¹) *
        multiplierWeight (1 + κ) (Φ x) :=
      (ENNReal.measurable_ofReal.comp (hgc.measurable.mul ((hR.continuous.pow d).measurable.mul
        ((Real.measurable_log.comp hR.continuous.measurable).pow_const 2)).inv)).mul (hwm _)
    have hcrit : ∫⁻ z in K p, ENNReal.ofReal (g (finv (Fd p) z) *
        (R (finv (Fd p) z) ^ d * Real.log (R (finv (Fd p) z)) ^ 2)⁻¹) *
          ENNReal.ofReal (ψ (finv (Fd p) z)) ^ (-(cr * (1 + κ))) ≠ ⊤ := by
      have h1 := hC' _ hcritm
      refine ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ne_top_of_le_ne_top hIG (setLIntegral_le_lintegral _ _))) (le_trans (le_of_eq ?_) h1)
      refine lintegral_congr fun z => ?_
      rw [hw, mul_comm (1 + κ) cr]
    -- Skoda in the coordinates
    have hsk : ∫⁻ ζ in closedBall (0 : ComplexModel m) (r p),
        ENNReal.ofReal (ψ (finv (Fd p) (coordinateInclusion (m + d) m ζ))) ^ (-β) ≠ ⊤ := by
      have hfm : Measurable fun y : W => ENNReal.ofReal (ψ y) ^ (-β) :=
        (ENNReal.continuous_rpow_const.comp (ENNReal.continuous_ofReal.comp
          (hψc.comp continuous_subtype_val))).measurable
      have h1 := hCW p _ hfm
      refine ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hβW)
        (le_trans (le_of_eq ?_) h1)
      refine setLIntegral_congr_fun measurableSet_closedBall fun ζ hζ => ?_
      rw [hsymm p ζ hζ]
    have hshell := limsup_shell_le (m := m) (d := d) (a := r p) (b := r p) (hr0 p).le
      (r := fun z => R (finv (Fd p) z)) (g := fun z => g (finv (Fd p) z))
      (ψ := fun z => ψ (finv (Fd p) z)) (Mg := Mg) hcg hκ (hcR0 p) hβ0 hLg0 hLψ0
      (hR.continuous.comp_continuousOn hfinvc) (hgc.comp_continuousOn hfinvc)
      (hψc.comp_continuousOn hfinvc) (hcomp p) (fun z _ => sq_nonneg _)
      (fun z hz => (le_abs_self _).trans (by
        have h := hMg z hz
        rw [Real.norm_eq_abs] at h
        exact h))
      (fun z hz => by
        have h := hLg z hz _ (tangProj_mem_closedLocalDom hz)
        rw [norm_sub_tangProj] at h
        linarith [(abs_le.mp h).2])
      (fun z _ => gentlePsi_nonneg _ _ _)
      (fun z hz => by
        have h := hLψ z hz _ (tangProj_mem_closedLocalDom hz)
        rw [norm_sub_tangProj] at h
        linarith [(abs_le.mp h).1])
      hcrit hsk
    refine hshell.trans ?_
    gcongr
    have hFm : Measurable fun y : W => ENNReal.ofReal (g y) * ENNReal.ofReal (ψ y) ^ (-cr) :=
      (ENNReal.measurable_ofReal.comp (hgc.comp continuous_subtype_val).measurable).mul
        (ENNReal.continuous_rpow_const.comp (ENNReal.continuous_ofReal.comp
          (hψc.comp continuous_subtype_val))).measurable
    calc ∫⁻ ζ in closedBall (0 : ComplexModel m) (r p),
          ENNReal.ofReal (g (finv (Fd p) (coordinateInclusion (m + d) m ζ))) *
            ENNReal.ofReal (ψ (finv (Fd p) (coordinateInclusion (m + d) m ζ))) ^ (-cr)
        = ∫⁻ ζ in closedBall (0 : ComplexModel m) (r p),
            (fun y : W => ENNReal.ofReal (g y) * ENNReal.ofReal (ψ y) ^ (-cr))
              ((complexChartAt (n := m) p).val.symm ζ) := by
          refine setLIntegral_congr_fun measurableSet_closedBall fun ζ hζ => ?_
          beta_reduce
          rw [hsymm p ζ hζ]
      _ ≤ ENNReal.ofReal (CW p) * ∫⁻ y, ENNReal.ofReal (g y) * ENNReal.ofReal (ψ y) ^ (-cr) ∂μW :=
          hCW p _ hFm
      _ = ENNReal.ofReal (CW p) * IW := by
          congr 1
          refine lintegral_congr fun y => ?_
          simp only [hgdef]
          rw [hGf y, hw 1, one_mul]
  -- the shell is covered by the pieces
  have hbound : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∫⁻ x in {x | ε / 2 ≤ R x ∧ R x ≤ ε}, ENNReal.ofReal (‖G x‖ ^ 2 * (R x ^ d)⁻¹) *
        multiplierWeight 1 (Φ x) ∂μ ≤ ∑ p ∈ t, ENNReal.ofReal (Cμ p) * A p ε := by
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hε₀)] with ε hεlt
    set S : Set X := {x | ε / 2 ≤ R x ∧ R x ≤ ε} with hSdef
    have hSm : MeasurableSet S :=
      ((isClosed_le continuous_const hR.continuous).inter
        (isClosed_le hR.continuous continuous_const)).measurableSet
    set h : X → ℝ≥0∞ := fun x => ENNReal.ofReal (‖G x‖ ^ 2 * (R x ^ d)⁻¹) *
      multiplierWeight 1 (Φ x) with hhdef
    have hhm : Measurable h :=
      (ENNReal.measurable_ofReal.comp (hgc.measurable.mul
        (hR.continuous.pow d).measurable.inv)).mul (hwm 1)
    have hSsub : S ⊆ ⋃ p ∈ t, finv (Fd p) '' K p := fun x hx => by
      obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp (hε₀O x (lt_of_le_of_lt hx.2 hεlt))
      exact mem_iUnion₂.mpr ⟨p, hp, image_mono (hDK p) hxp⟩
    calc ∫⁻ x in S, h x ∂μ = ∫⁻ x in ⋃ p ∈ t, finv (Fd p) '' K p, S.indicator h x ∂μ := by
          rw [setLIntegral_indicator hSm, inter_eq_left.mpr hSsub]
      _ ≤ ∑ p ∈ t, ∫⁻ x in finv (Fd p) '' K p, S.indicator h x ∂μ :=
          setLIntegral_biUnion_finset_le t _ _
      _ ≤ ∑ p ∈ t, ENNReal.ofReal (Cμ p) * ∫⁻ z in K p, S.indicator h (finv (Fd p) z) :=
          Finset.sum_le_sum fun p _ => hCμ p _ (hhm.indicator hSm)
      _ = ∑ p ∈ t, ENNReal.ofReal (Cμ p) * A p ε := by
          refine Finset.sum_congr rfl fun p _ => ?_
          congr 1
          set T : Set (ComplexModel (m + d)) :=
            {z | ε / 2 ≤ R (finv (Fd p) z) ∧ R (finv (Fd p) z) ≤ ε} with hTdef
          have hKTm : MeasurableSet (K p ∩ T) :=
            ((hR.continuous.comp_continuousOn ((continuousOn_finv (Fd p)).mono
              (hKt' p))).preimage_isClosed_of_isClosed (hKc p).isClosed
                isClosed_Icc).measurableSet
          calc ∫⁻ z in K p, S.indicator h (finv (Fd p) z)
              = ∫⁻ z in K p, (K p ∩ T).indicator (fun z => h (finv (Fd p) z)) z :=
                setLIntegral_congr_fun (hKc p).isClosed.measurableSet fun z hz => by
                  by_cases hzT : z ∈ T
                  · rw [indicator_of_mem (show finv (Fd p) z ∈ S from hzT),
                      indicator_of_mem (show z ∈ K p ∩ T from ⟨hz, hzT⟩)]
                  · rw [indicator_of_notMem (show finv (Fd p) z ∉ S from hzT),
                      indicator_of_notMem (fun h' => hzT h'.2)]
            _ = ∫⁻ z in K p ∩ T, h (finv (Fd p) z) := by
                rw [setLIntegral_indicator hKTm, inter_eq_left.mpr inter_subset_left]
            _ = A p ε := by
                refine lintegral_congr fun z => ?_
                simp only [hhdef]
                rw [hw 1, one_mul]
  -- summing over the pieces
  calc limsup (fun ε : ℝ => ∫⁻ x in {x | ε / 2 ≤ R x ∧ R x ≤ ε},
        ENNReal.ofReal (‖G x‖ ^ 2 * (R x ^ d)⁻¹) * multiplierWeight 1 (Φ x) ∂μ) (𝓝[>] 0)
      ≤ limsup (fun ε => ∑ p ∈ t, ENNReal.ofReal (Cμ p) * A p ε) (𝓝[>] 0) :=
        limsup_le_limsup hbound
    _ ≤ ∑ p ∈ t, limsup (fun ε => ENNReal.ofReal (Cμ p) * A p ε) (𝓝[>] 0) :=
        limsup_finset_sum_le t (fun p ε => ENNReal.ofReal (Cμ p) * A p ε)
    _ = ∑ p ∈ t, ENNReal.ofReal (Cμ p) * limsup (A p) (𝓝[>] 0) :=
        Finset.sum_congr rfl fun p _ => ENNReal.limsup_const_mul_of_ne_top ENNReal.ofReal_ne_top
    _ ≤ ∑ p ∈ t, ENNReal.ofReal (Cμ p) *
          (ENNReal.ofReal ((2 / cR p) ^ d) * vD * (ENNReal.ofReal (CW p) * IW)) :=
        Finset.sum_le_sum fun p _ => mul_le_mul' le_rfl (hpiece p)
    _ = ∑ p ∈ t, ENNReal.ofReal (Cμ p * (2 / cR p) ^ d * vD.toReal * CW p) * IW := by
        refine Finset.sum_congr rfl fun p _ => ?_
        have h := ofReal_mul_four_eq (hCμ0 p)
          (show (0 : ℝ) ≤ (2 / cR p) ^ d by have := hcR0 p; positivity)
          (ENNReal.toReal_nonneg (a := vD)) (hCW0 p) IW
        rwa [ENNReal.ofReal_toReal hvD] at h
    _ = ENNReal.ofReal (∑ p ∈ t, Cμ p * (2 / cR p) ^ d * vD.toReal * CW p) * IW := by
        rw [← Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg fun p _ => by
          have := hCμ0 p; have := hCW0 p; have := hcR0 p; positivity]
    _ ≤ ENNReal.ofReal CY * IW := by
        gcongr
        rw [hCYdef]
        linarith

end Residue
end SGPT.Trace.BertiniUniversal
