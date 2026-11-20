import SGPT.Trace.OTResPiece
import SGPT.Trace.OTExt5Main

/-!
# FPT `lem:gentle-weighted-normal-residue`, and `thm:OT_ext` in every dimension

Blueprint `claude-ot-residue.tex`, nodes `claude-ot-residue:residue`, `claude-ot-residue:main`.

`gentleWeightedNormalResidueHypothesis` proves the named hypothesis
`SGPT.Trace.OTExt2.GentleWeightedNormalResidueHypothesis ω W` (exact statement) for every closed
connected submanifold `W` with `0 < dim W` (the hypothesis is vacuous unless `dim W < dim X`).
Consequently (`otExtStatement`) the book's `thm:OT_ext` holds unconditionally, in every
dimension, through the `otExtStatement_of_residue`.

## Proof of the residue estimate

Fix a normal pole `R` of `W` (`exists_isGlobalNormalPole_of_lt`).  Around every `p ∈ W` take the
flattening coordinates `(z', w)` of `p` and a closed product `K_p = {|z'| ≤ r_p, |w| ≤ r_p}` with
`R ≥ c_p |w|²` on it (`exists_piece`); finitely many `p ∈ t` cover `W`, and for `ε < ε₀` the shell
`{ε/2 ≤ R ≤ ε}` lies in their union.  The constants `C_μ(p)` (comparison of `ω^n` with Lebesgue
measure on `K_p`), `C_W(p)` (comparison of Lebesgue measure on `{|z'| ≤ r_p}` with `dV_W`) and
`c_p` depend only on `X, ω, W, R`, and `C_Y = 1 + ∑_{p ∈ t} C_μ(p) (2/c_p)^q vol(B^q) C_W(p)`.

Given a gentle `Φ`, `f` and a glued `G`: `|G|²` and `ψ = e^{Φ/c}` are smooth in every chart, hence
Lipschitz on each `K_p`; the critical gain of `G` (`lintegral_glued_crit_ne_top`) and Skoda's
theorem on `W` (`exists_lintegral_gentlePsi_rpow_neg_ne_top`) give the remaining hypotheses of the
Euclidean shell estimate `limsup_shell_le` on each `K_p`; its right side is
`(2/c_p)^q vol(B^q) ∫_{|z'| ≤ r_p} |f|² e^{-Φ} dz' ≤ (2/c_p)^q vol(B^q) C_W(p) ∫_W |f|² e^{-Φ} dV_W`.
Summing over `p ∈ t` (`limsup_finset_sum_le`) gives the claim.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Trace.OTRes

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
open SGPT.Trace.OTExt2 (IsGlobalNormalPole GentleWeightedNormalResidueHypothesis
  IsCriticalGainGluing exists_isGlobalNormalPole_of_lt)
open SGPT.Trace.OTExt4 (closedLocalDom glued isSmoothSectionOn_glued)

/-- `ι(B̄(0, r)) ⊆ {|z'| ≤ r, |w| ≤ r}`. -/
theorem coordinateInclusion_mem_closedLocalDom {m d : ℕ} {r : ℝ} {ζ : ComplexModel m}
    (hζ : ζ ∈ closedBall (0 : ComplexModel m) r) :
    coordinateInclusion (m + d) m ζ ∈ closedLocalDom (m + d) m r r := by
  have hr : 0 ≤ r := (norm_nonneg ζ).trans (mem_closedBall_zero_iff.mp hζ)
  refine ⟨?_, ?_⟩
  · rw [SGPT.Trace.OTExt2.tanWeight_eq_norm_proj (by omega),
      coordinateProjection_coordinateInclusion (by omega)]
    exact pow_le_pow_left₀ (norm_nonneg _) (mem_closedBall_zero_iff.mp hζ) 2
  · have h0 := normalWeight_tangProj m d (coordinateInclusion (m + d) m ζ)
    rw [tangProj, coordinateProjection_coordinateInclusion (by omega)] at h0
    rw [h0]; positivity

theorem ofReal_mul_four_eq {a b w e : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hw : 0 ≤ w) (_he : 0 ≤ e)
    (I : ℝ≥0∞) :
    ENNReal.ofReal a * (ENNReal.ofReal b * ENNReal.ofReal w * (ENNReal.ofReal e * I)) =
      ENNReal.ofReal (a * b * w * e) * I := by
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul ha]
  ring

variable {m d : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + d)) X]
  [IsComplexManifold (m + d) X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

/-- **FPT `lem:gentle-weighted-normal-residue`** (the named hypothesis of lanes OT-EXT2–5, exact
statement), for `X` of dimension `m + d` and `W` of dimension `m > 0`. -/
theorem gentleWeightedNormalResidueHypothesis_aux (ωb : KahlerBackground (m + d) X) {W : Set X}
    (hW : IsClosedConnectedSubmanifold (m + d) W m) (hm : 0 < m) :
    GentleWeightedNormalResidueHypothesis ωb hW := by
  unfold GentleWeightedNormalResidueHypothesis
  intro hk hmn
  let _ : ChartedSpace (ComplexModel m) W := chartedSpace hk hW.2.2
  have _ : IsComplexManifold m W := isComplexManifold_chartedSpace hk hW.2.2
  have _ : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
  let _ : MeasurableSpace W := borel W
  have _ : BorelSpace W := ⟨rfl⟩
  have hq : m + d - m = d := Nat.add_sub_cancel_left m d
  rw [hq]
  set μ := IntegrationCurrent.kahlerVolume ωb with hμdef
  have hμ : IsSmoothPositiveVolume (n := m + d) μ :=
    KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume ωb
  set μW := IntegrationCurrent.kahlerVolume
    (SubmanifoldKahlerRestriction.kahlerBackground hk hW.2.2 ωb) with hμWdef
  have hμW : IsSmoothPositiveVolume (n := m) μW :=
    KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume _
  obtain ⟨R, hR⟩ := exists_isGlobalNormalPole_of_lt ωb hW hmn
  -- the pieces
  choose r cR hr0 hcR0 hKt hcomp using fun p : W => exists_piece hW.2.2 hR p
  set Fd : W → FlatData (m + d) m X W := fun p => FlatData.ofRegularAtDim (hW.2.2 p.1 p.2)
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
    have hreg := hW.2.2 p.1 p.2
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
  obtain ⟨t, ht⟩ := hW.1.isCompact.elim_finite_subcover O hOo
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
  refine ⟨R, hR, CY, hCY0, ?_⟩
  intro V hV θV _ Φ hΦ hgent hne f _ κ hκ G hG
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
  have hgc : Continuous g := continuous_of_chartSmooth hgs
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
  obtain ⟨β, hβ0, hβW⟩ := exists_lintegral_gentlePsi_rpow_neg_ne_top ωb hW hm hΦ.1 hne hga
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

section General

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

/-- **FPT `lem:gentle-weighted-normal-residue`**: the named hypothesis
`GentleWeightedNormalResidueHypothesis ω W` (lanes OT-EXT2–OT-EXT5) holds, with its exact
statement, for every closed connected submanifold `W` of positive dimension of a compact Kähler
manifold `(X, ω)`. -/
theorem gentleWeightedNormalResidueHypothesis (ωb : KahlerBackground n X) {W : Set X} {m : ℕ}
    (hW : IsClosedConnectedSubmanifold n W m) (hm : 0 < m) :
    GentleWeightedNormalResidueHypothesis ωb hW := by
  obtain ⟨d, rfl⟩ : ∃ d, n = m + d :=
    ⟨n - m, (Nat.add_sub_of_le (le_of_isClosedConnectedSubmanifold hW)).symm⟩
  exact gentleWeightedNormalResidueHypothesis_aux ωb hW hm

variable (n X) in
/-- **`thm:OT_ext`** (Hisamoto, Theorem 1.4; Xia, *Foundations of pluripotential theory*,
`thm:compact-submanifold-extension`, `cor:compact-positive-metric-extension`), unconditionally and
in every dimension: OT-EXT5's `otExtStatement_of_residue` applied to
`gentleWeightedNormalResidueHypothesis`. -/
theorem otExtStatement : SGPT.Trace.TwistedL2.OTExtStatement n X :=
  SGPT.Trace.OTExt5.otExtStatement_of_residue n X
    fun ωb _ _ hW hm _ => gentleWeightedNormalResidueHypothesis ωb hW hm

/-- `thm:OT_ext` for one closed connected submanifold `W` and one `δ > 0` (the book's conclusion
`OTExtAlong`), unconditionally. -/
theorem otExtAlong (ωb : KahlerBackground n X)
    (L T : HermitianHolomorphicLineBundle.{0, 0} n X) (hL : IsSourceSmoothHermitianMetric L)
    (hT : IsSourceSmoothHermitianMetric T) (θ : ClosedRealOneOneForm n X)
    (hθ : IsOwnFirstChernForm L θ) {W : Set X} {m : ℕ} (hW : IsClosedConnectedSubmanifold n W m)
    {δ : ℝ} (hδ : 0 < δ) : SGPT.Trace.TwistedL2.OTExtAlong ωb L T θ hW δ :=
  otExtStatement n X ωb L T hL hT θ hθ W m hW δ hδ

end General

end SGPT.Trace.OTRes
