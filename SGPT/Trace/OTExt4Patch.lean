import SGPT.Trace.OTExt4Grad
import SGPT.Trace.OTExt2Statement
import SGPT.Trace.OTMarginExistence
import SGPT.Foundations.Analysis.Pending.RawQuasiPshUniformStrictGenericNecessity

/-!
# Local extensions with the critical gain near a point of the submanifold

Blueprint `claude-ot-ext4.tex`, node `claude-ot-ext4:patch`.  Xia, *Foundations of
pluripotential theory*, q07, proof of `lem:critical-gain-initial-gluing`, first two paragraphs.

`exists_criticalPatch`: let `W ⊆ X` be a closed submanifold of dimension `m < n`, `R` a normal
pole of `W` (`IsGlobalNormalPole`), `Φ` quasi-psh on `X` and `f` a section of `V|_W` with
coefficients in `𝓘(Φ|_W)`.  Near every `p ∈ W` there are `κ > 0` and a local holomorphic section
`F` of `V` with `F = f` on `W` and

  `∫_K |F|² e^{-(1+κ)Φ} R^{-q} (log R)^{-2} dμ < ∞`

on a compact neighbourhood `K` of `p` (`q = n - m`).  Proof: in the flattening coordinates
`(z', w)` at `p` and the preferred frame at `p`, `Φ = P + O(1)` with `P` psh; strong openness at
`0` for the weight of `f` on `W` (`exists_gt_multiplierIntegrableAt`) gives `c' = 1 + κ > 1` with
`∫ |f|² e^{-c' P(z', 0)} < ∞` near `0`; the local critical gain extension
(`localCriticalGainExtension`, FPT `lem:local-critical-gain-extension`) applied to `c' P` on a
product `D = B' × B''` gives `F₀` with `∫_D |F₀|² e^{-c'P} |w|^{-2q} (log |w|²)^{-2} < ∞`; and
`|log R - log |w|²| ≤ C` (the local form of the normal pole) gives
`(R^q (log R)²)⁻¹ ≤ C' (|w|^{2q} (log |w|²)²)⁻¹` (`inv_pow_mul_log_sq_le`), since `R` and `|w|²`
are `< e^{-4}`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Trace.OTExt4

open Set Filter Metric MeasureTheory Bundle
open scoped Topology ENNReal NNReal Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace
  SGPT.Foundations.Analysis.FirstPass.RegularLocusDense SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
  SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Trace.TwistedL2 SGPT.Trace.OTMargin SGPT.Bergman.CompactHolomorphicSectionsDraft
open SGPT.Trace.OTExt2 (localDom criticalKernel tanWeight localCriticalGainExtension
  IsGlobalNormalPole logPole)

/-- **Comparison of critical weights.**  For `0 < R < e^{-4}`, `0 < w < 1` and
`|log R - log w| ≤ C`: `(R^q (log R)²)⁻¹ ≤ e^{qC} (1 + C/4)² (w^q (log w)²)⁻¹`. -/
theorem inv_pow_mul_log_sq_le {R w C : ℝ} (q : ℕ) (hR : 0 < R) (hw : 0 < w)
    (hRe : R < Real.exp (-4)) (hw1 : w < 1) (hC : 0 ≤ C) (hRw : |Real.log R - Real.log w| ≤ C) :
    (R ^ q * Real.log R ^ 2)⁻¹ ≤
      Real.exp (q * C) * (1 + C / 4) ^ 2 * (w ^ q * Real.log w ^ 2)⁻¹ := by
  have hs : 4 < -Real.log R := by
    have := Real.log_lt_log hR hRe
    rw [Real.log_exp] at this; linarith
  have ht : 0 < -Real.log w := neg_pos.mpr (Real.log_neg hw hw1)
  have h1 := (abs_le.mp hRw).2
  have hts : -Real.log w ≤ (-Real.log R) * (1 + C / 4) := by
    nlinarith [mul_le_mul_of_nonneg_right hs.le hC]
  have hsq : Real.log w ^ 2 ≤ Real.log R ^ 2 * (1 + C / 4) ^ 2 := by
    have : (-Real.log w) ^ 2 ≤ ((-Real.log R) * (1 + C / 4)) ^ 2 :=
      pow_le_pow_left₀ ht.le hts 2
    nlinarith
  have hwR : w ≤ R * Real.exp C := by
    have h2 := (abs_le.mp hRw).1
    calc w = Real.exp (Real.log w) := (Real.exp_log hw).symm
      _ ≤ Real.exp (Real.log R + C) := Real.exp_le_exp.mpr (by linarith)
      _ = R * Real.exp C := by rw [Real.exp_add, Real.exp_log hR]
  have hpow : w ^ q ≤ R ^ q * Real.exp (q * C) := by
    calc w ^ q ≤ (R * Real.exp C) ^ q := pow_le_pow_left₀ hw.le hwR q
      _ = R ^ q * Real.exp (q * C) := by rw [mul_pow, ← Real.exp_nat_mul]
  have hb : 0 < w ^ q * Real.log w ^ 2 := by
    have : 0 < Real.log w ^ 2 := by nlinarith
    positivity
  have ha : 0 < R ^ q * Real.log R ^ 2 := by
    have : 0 < Real.log R ^ 2 := by nlinarith
    positivity
  set K := Real.exp (q * C) * (1 + C / 4) ^ 2 with hK
  have hK0 : 0 < K := by positivity
  have hba : w ^ q * Real.log w ^ 2 ≤ K * (R ^ q * Real.log R ^ 2) := by
    calc w ^ q * Real.log w ^ 2 ≤ (R ^ q * Real.exp (q * C)) * (Real.log R ^ 2 * (1 + C / 4) ^ 2) :=
          mul_le_mul hpow hsq (sq_nonneg _) (by positivity)
      _ = K * (R ^ q * Real.log R ^ 2) := by rw [hK]; ring
  calc (R ^ q * Real.log R ^ 2)⁻¹ = K * (K * (R ^ q * Real.log R ^ 2))⁻¹ := by
        field_simp
    _ ≤ K * (w ^ q * Real.log w ^ 2)⁻¹ := by
        gcongr

/-- The image of an open subset of the flat target under `ζ⁻¹` is open. -/
theorem isOpen_finv_image' {n m : ℕ} {X : Type} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] {W : Set X} (F : FlatData n m X W)
    {A : Set (ComplexModel n)} (hA : IsOpen A) (hAt : A ⊆ F.flat.target) :
    IsOpen (finv F '' A) := by
  rw [finv_image F hAt]
  exact (continuousOn_fcoord F).isOpen_inter_preimage F.isOpen_ambSource hA

/-- The closed product `{|z'| ≤ a, |w| ≤ b}`. -/
def closedLocalDom (n m : ℕ) (a b : ℝ) : Set (ComplexModel n) :=
  {z | tanWeight n m z ≤ a ^ 2 ∧ normalWeight n m z ≤ b ^ 2}

theorem isCompact_closedLocalDom (n m : ℕ) (a b : ℝ) : IsCompact (closedLocalDom n m a b) := by
  have hcl : IsClosed (closedLocalDom n m a b) :=
    (isClosed_le (SGPT.Trace.OTExt2.continuous_tanWeight m) continuous_const).inter
      (isClosed_le (SGPT.Trace.OTExt2.continuous_normalWeight m) continuous_const)
  refine (isCompact_closedBall (0 : ComplexModel n) (Real.sqrt (a ^ 2 + b ^ 2))).of_isClosed_subset
    hcl fun z hz => ?_
  rw [mem_closedBall_zero_iff, ← Real.sqrt_sq (norm_nonneg z)]
  refine Real.sqrt_le_sqrt ?_
  rw [← SGPT.Trace.OTExt2.tanWeight_add_normalWeight m z]
  exact add_le_add hz.1 hz.2

theorem localDom_subset_closedLocalDom (n m : ℕ) (a b : ℝ) :
    localDom n m a b ⊆ closedLocalDom n m a b := fun _ hz => ⟨hz.1.le, hz.2.le⟩

theorem closedLocalDom_subset_localDom {n m : ℕ} {a b a' b' : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (haa : a < a') (hbb : b < b') : closedLocalDom n m a b ⊆ localDom n m a' b' :=
  fun _ hz => ⟨hz.1.trans_lt (pow_lt_pow_left₀ haa ha two_ne_zero),
    hz.2.trans_lt (pow_lt_pow_left₀ hbb hb two_ne_zero)⟩

theorem norm_le_of_mem_closedLocalDom {n m : ℕ} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    {z : ComplexModel n} (hz : z ∈ closedLocalDom n m a b) : ‖z‖ ≤ a + b := by
  have h : ‖z‖ ^ 2 ≤ (a + b) ^ 2 := by
    rw [← SGPT.Trace.OTExt2.tanWeight_add_normalWeight m z]
    nlinarith [hz.1, hz.2]
  exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) h

variable {n m : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {W : Set X}
  (V : X → Type) [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℂ (V x)]
  [TopologicalSpace (TotalSpace ℂ V)] [FiberBundle ℂ V] [VectorBundle ℂ ℂ V]
  [ContMDiffVectorBundle ∞ ℂ V 𝓘(ℂ, ComplexModel n)] [ContinuousFiberNorm V]
  [MeasurableSpace X] [BorelSpace X]

/-- **A local extension with the critical gain** near `p ∈ W` (FPT, proof of
`lem:critical-gain-initial-gluing`). -/
theorem exists_criticalPatch {μ : Measure X} (hμ : IsSmoothPositiveVolume (n := n) μ)
    (hk : m ≤ n) (hmn : m < n) (hW : ∀ x ∈ W, RegularAtDim (n := n) W x m)
    {ωb : KahlerBackground n X} {R : X → ℝ} (hR : IsGlobalNormalPole ωb W R)
    {Φ : X → EReal} (hΦ : ManifoldQuasiPlurisubharmonic (n := n) Φ) {f : (y : W) → V y}
    (hf : letI := chartedSpace hk hW
      haveI := isComplexManifold_chartedSpace hk hW
      IsAlongMultiplierSection V (m := m) 1 (fun y : W => Φ y) f) (p : W) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ (B' K B : Set X) (F : (x : X) → V x), IsOpen B' ∧ IsOpen B ∧
      IsCompact K ∧ p.1 ∈ B' ∧ B' ⊆ K ∧ K ⊆ B ∧
      SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) V F B ∧
      (∀ y : W, y.1 ∈ B → F y = f y) ∧
      ∫⁻ x in K, ENNReal.ofReal (‖F x‖ ^ 2) * multiplierWeight (1 + κ) (Φ x) *
        ENNReal.ofReal ((R x ^ (n - m) * Real.log (R x) ^ 2)⁻¹) ∂μ ≠ ⊤ := by
  let := chartedSpace hk hW
  set Fd : FlatData n m X W := FlatData.ofRegularAtDim (hW p.1 p.2) with hFd
  set e := trivializationAt ℂ V p.1 with he
  set x : X := p.1 with hxdef
  have hreg := hW p.1 p.2
  set amb : ComplexChart n X := Fd.amb with hamb
  set flat := Fd.flat with hflat
  set ι : ComplexModel m →L[ℂ] ComplexModel n := coordinateInclusion n m with hι
  have hpsrc : p ∈ (Fd.chart hk).source := FlatData.mem_ambSource_ofRegularAtDim hreg
  have hxsrc : x ∈ Fd.ambSource := hpsrc
  have hz0 : flat (amb.val x) = 0 := hreg.2.2.choose_spec.2.1
  have hζ0 : (Fd.chart hk) p = 0 := by
    rw [FlatData.chart_apply, FlatData.toCoord]
    rw [show Fd.flat (Fd.amb.val p.1) = 0 from hz0, map_zero]
  -- the coefficient of `f` in the frame `e`, in the chart of `W` at `p`
  set coef : W → ℂ := alongCoefficient V e f with hcoef
  have hmem := hf p
  obtain ⟨-, hint1⟩ := hmem
  have hint : MultiplierIntegrableAt (chartFunction (fun q : W => Φ q.1) (complexChartAt (n := m) p)) 1
      (fun z => coef ((complexChartAt (n := m) p).val.symm z)) ((complexChartAt (n := m) p).val p)
      volume := (SGPT.Bergman.MultiplierSectionsDraft.multiplierIntegrableAt_scaled_one_iff _
        one_pos _ _ _).mp hint1
  set ψt : ComplexModel n → EReal := fun z => chartFunction Φ amb (flat.symm z) with hψtdef
  set f₀ : ComplexModel m → ℂ := fun ζ => coef ((complexChartAt (n := m) p).val.symm ζ) with hf₀def
  -- Step 1: the weight of `Φ|_W` in the chart of `W` at `p` is `ψt ∘ ι`
  have h0T : (0 : ComplexModel m) ∈ Fd.coordTarget := by
    rw [← hζ0]; exact Fd.toCoord_mem_coordTarget p hxsrc
  have hweightW : chartFunction (fun q : W => Φ q.1) (complexChartAt (n := m) p) =ᶠ[𝓝 0]
      fun ζ => ψt (ι ζ) := by
    filter_upwards [Fd.isOpen_coordTarget.mem_nhds h0T] with ζ hζ
    show Φ (((Fd.chart hk).symm ζ : W) : X) = Φ (amb.val.symm (flat.symm (ι ζ)))
    rw [show (((Fd.chart hk).symm ζ : W) : X) = Fd.ofCoord ζ from Fd.invPoint_val hζ]
    rfl
  have hintW : MultiplierIntegrableAt (fun ζ => ψt (ι ζ)) 1 f₀ 0 volume := by
    have h1 := hint
    rw [show (complexChartAt (n := m) p).val p = 0 from hζ0] at h1
    exact h1.congr hweightW (EventuallyEq.refl _ _)
  -- Step 2: `ψt` is quasi-psh at the origin
  have hflat_symm_cd : ContDiffOn ℂ ∞ flat.symm flat.target :=
    contDiffOn_of_differentiableOn_complex Fd.differentiableOn_flat_symm flat.open_target
  have hxflat : amb.val x ∈ flat.source := hxsrc.2
  have h0flat : (0 : ComplexModel n) ∈ flat.target := by
    rw [← hz0]; exact flat.map_source hxflat
  have hsymm0 : flat.symm 0 = amb.val x := by rw [← hz0]; exact flat.left_inv hxflat
  have hψamb : QuasiPlurisubharmonicOn (chartFunction Φ amb) amb.val.target := hΦ amb
  have hψ0 : QuasiPlurisubharmonicAt ψt 0 := by
    have hq : QuasiPlurisubharmonicAt (chartFunction Φ amb) (flat.symm 0) := by
      rw [hsymm0]; exact hψamb _ (amb.val.map_source hxsrc.1)
    exact HolomorphicPullback.quasiPlurisubharmonicAt_comp_holomorphic flat.open_target
      hflat_symm_cd h0flat hq
  -- Step 3: strong openness for the weight on `W`
  have hψι : QuasiPlurisubharmonicAt (fun ζ => ψt (ι ζ)) 0 := by
    have h := HolomorphicPullback.quasiPlurisubharmonicAt_comp_holomorphic (F := ι) isOpen_univ
      ι.contDiff.contDiffOn (mem_univ 0) (by simpa using hψ0)
    simpa using h
  obtain ⟨c', hc'1, hintc'⟩ :=
    RawQuasiPshUniformStrictGenericNecessity.exists_gt_multiplierIntegrableAt hψι hintW
  have hc'0 : 0 < c' := one_pos.trans hc'1
  -- Step 4: `ψt = P + h` near the origin, `P` psh, `h` smooth and bounded
  obtain ⟨P, hs', hP, hhs, heq⟩ := id hψ0
  obtain ⟨UP, hUP, h0UP, hPdisc⟩ := id hP
  have hscont : ContinuousAt hs' 0 := hhs.self_of_nhds.continuousAt
  set M : ℝ := |hs' 0| + 1 with hM
  have hsbd : ∀ᶠ y in 𝓝 (0 : ComplexModel n), |hs' y| ≤ M := by
    filter_upwards [hscont.eventually (Metric.ball_mem_nhds (hs' 0) one_pos)] with y hy
    rw [Real.dist_eq] at hy
    have := abs_sub_abs_le_abs_sub (hs' y) (hs' 0)
    linarith
  -- the slice integral with the exponent `c'`
  have hιcont : Tendsto ι (𝓝 0) (𝓝 0) := by simpa using ι.continuous.tendsto 0
  have hmoreW : MoreSingularAt (fun w => ψt (ι w)) (fun w => P (ι w)) 0 := by
    refine ⟨M, ?_⟩
    filter_upwards [hιcont.eventually heq, hιcont.eventually hsbd] with w hw hwb
    rw [hw]
    exact add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (le_of_abs_le hwb))
  have hPι : QuasiPlurisubharmonicAt (fun w => P (ι w)) 0 := by
    refine (HolomorphicPullback.plurisubharmonicAt_comp_holomorphic isOpen_univ
      ι.differentiable.differentiableOn (mem_univ 0) ?_).quasiPlurisubharmonicAt
    simpa using hP
  obtain ⟨-, U', hU', h0U', hfU', hfint⟩ :=
    multiplierIntegrableAt_of_moreSingularAt hPι hmoreW hintc'
  -- Step 5: the local form of the normal pole in the flattening coordinates
  obtain ⟨UR, hUR, CR, hCR⟩ := localForm_normalized hW hR.pole 0 p
  -- Step 6: a radius on which everything holds
  have hfc : ContinuousAt (finv Fd) 0 :=
    (continuousOn_finv Fd).continuousAt (flat.open_target.mem_nhds h0flat)
  have hfx : finv Fd 0 = x := by
    show amb.val.symm (flat.symm 0) = x
    rw [hsymm0, amb.val.left_inv hxsrc.1]
  have hxe : x ∈ e.baseSet := mem_baseSet_trivializationAt ℂ V x
  have hev : ∀ᶠ z in 𝓝 (0 : ComplexModel n), z ∈ UP ∧ z ∈ flat.target ∧
      finv Fd z ∈ e.baseSet ∧ ψt z = P z + (hs' z : EReal) ∧ |hs' z| ≤ M ∧ finv Fd z ∈ UR := by
    filter_upwards [hUP.mem_nhds h0UP, flat.open_target.mem_nhds h0flat,
      hfc.eventually (by rw [hfx]; exact e.open_baseSet.mem_nhds hxe), heq, hsbd,
      hfc.eventually (by rw [hfx]; exact hUR)]
      with z h1 h2 h3 h4 h5 h6
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  obtain ⟨r₁, hr₁, hr₁s⟩ := Metric.eventually_nhds_iff_ball.mp hev
  obtain ⟨r₂, hr₂, hr₂U'⟩ := Metric.isOpen_iff.mp hU' 0 h0U'
  set r : ℝ := min (min (r₁ / 3) (r₂ / 2)) (Real.exp (-2) / 2) with hr
  have hr0 : 0 < r := lt_min (lt_min (by positivity) (by positivity)) (by positivity)
  have hrr₁ : 2 * r < r₁ := by
    have : r ≤ r₁ / 3 := (min_le_left _ _).trans (min_le_left _ _)
    linarith
  have hrr₂ : r < r₂ := by
    have : r ≤ r₂ / 2 := (min_le_left _ _).trans (min_le_right _ _)
    linarith
  have hre : r < Real.exp (-2) := by
    have : r ≤ Real.exp (-2) / 2 := min_le_right _ _
    linarith [Real.exp_pos (-2)]
  -- the domains
  set D : Set (ComplexModel n) := localDom n m r r with hD
  set Kc : Set (ComplexModel n) := closedLocalDom n m (r / 2) (r / 2) with hKc
  set D' : Set (ComplexModel n) := localDom n m (r / 2) (r / 2) with hD'
  have hclD : closure D ⊆ ball 0 r₁ := by
    refine (closure_minimal (localDom_subset_closedLocalDom n m r r)
      (isCompact_closedLocalDom n m r r).isClosed).trans fun z hz => ?_
    rw [mem_ball_zero_iff]
    exact (norm_le_of_mem_closedLocalDom hr0.le hr0.le hz).trans_lt (by linarith)
  have hDball : D ⊆ ball 0 r₁ := subset_closure.trans hclD
  have hKcD : Kc ⊆ D := closedLocalDom_subset_localDom (by positivity) (by positivity)
    (by linarith) (by linarith)
  have hD'Kc : D' ⊆ Kc := localDom_subset_closedLocalDom n m _ _
  have hDt : D ⊆ flat.target := fun z hz => (hr₁s z (hDball hz)).2.1
  -- Step 7: the local critical gain extension of `f₀` for the weight `c' P`
  obtain ⟨C₀, hC₀, hgain⟩ := localCriticalGainExtension n m hmn r r hr0 hr0 hre
  have hPpsh : PlurisubharmonicOn (fun z => (c' : EReal) * P z) (ball (0 : ComplexModel n) r₁) := by
    refine PlurisubharmonicOn.const_mul (fun y hy => ⟨UP, hUP, (hr₁s y hy).1, hPdisc⟩) hc'0
  have hsliceU' : closedBall (0 : ComplexModel m) r ⊆ U' := fun w hw =>
    hr₂U' (closedBall_subset_ball hrr₂ hw)
  have hfi : ∫⁻ z' in ball (0 : ComplexModel m) r, ENNReal.ofReal (‖f₀ z'‖ ^ 2) *
      multiplierWeight 1 ((c' : EReal) * P (coordinateInclusion n m z')) ≠ ⊤ := by
    have h := hfint.2.ne
    refine ne_top_of_le_ne_top h ((lintegral_mono fun z' => le_of_eq ?_).trans
      (lintegral_mono_set (ball_subset_closedBall.trans hsliceU')))
    simp only [multiplierDensity, multiplierWeight_one_coe_mul]
    rfl
  obtain ⟨F₀, hF₀d, hF₀ext, hF₀int⟩ := hgain (ball 0 r₁) isOpen_ball hclD
    (fun z => (c' : EReal) * P z) hPpsh U' hU' hsliceU' f₀ hfU' hfi
  have hF₀fin : ∫⁻ z in D, ENNReal.ofReal (‖F₀ z‖ ^ 2) *
      multiplierWeight 1 ((c' : EReal) * P z) * criticalKernel n m z ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfi) hF₀int
  -- Step 8: the section
  set S : (x : X) → V x := fun y => e.symm y (F₀ (fcoord Fd y)) with hS
  set B : Set X := finv Fd '' D with hB
  set K : Set X := finv Fd '' Kc with hK
  set B' : Set X := finv Fd '' D' with hB'
  have hBo : IsOpen B := isOpen_finv_image' Fd (SGPT.Trace.OTExt2.isOpen_localDom m r r) hDt
  have hB'o : IsOpen B' := isOpen_finv_image' Fd (SGPT.Trace.OTExt2.isOpen_localDom m _ _)
    ((hD'Kc.trans hKcD).trans hDt)
  have hKcpt : IsCompact K := (isCompact_closedLocalDom n m _ _).image_of_continuousOn
    ((continuousOn_finv Fd).mono (hKcD.trans hDt))
  have h0D' : (0 : ComplexModel n) ∈ D' := by
    have ht0 : tanWeight n m 0 = 0 := by simp [tanWeight]
    have hn0 : normalWeight n m (0 : ComplexModel n) = 0 :=
      (normalWeight_eq_zero_iff _).mpr fun i _ => rfl
    refine ⟨?_, ?_⟩
    · rw [ht0]; positivity
    · rw [hn0]; positivity
  refine ⟨c' - 1, by linarith, B', K, B, S, hB'o, hBo, hKcpt, ⟨0, h0D', hfx⟩,
    image_mono hD'Kc, image_mono hKcD, ?_, ?_, ?_⟩
  · -- holomorphy of `S`
    rintro _ ⟨z, hz, rfl⟩
    have hzt := hDt hz
    have hxe' := (hr₁s z (hDball hz)).2.2.1
    have hxa := finv_mem Fd hzt
    refine MDifferentiableAt.mdifferentiableWithinAt ?_
    rw [Trivialization.mdifferentiableAt_section_iff (IB := 𝓘(ℂ, ComplexModel n)) e S hxe']
    have hG' : DifferentiableAt ℂ F₀ (fcoord Fd (finv Fd z)) := by
      rw [fcoord_finv Fd hzt]
      exact hF₀d.differentiableAt ((SGPT.Trace.OTExt2.isOpen_localDom m r r).mem_nhds hz)
    have hcomp := hG'.mdifferentiableAt.comp (finv Fd z) (mdifferentiableAt_fcoord Fd hxa)
    refine hcomp.congr_of_eventuallyEq ?_
    filter_upwards [e.open_baseSet.mem_nhds hxe'] with y hy
    show (e ⟨y, e.symm y (F₀ (fcoord Fd y))⟩).2 = F₀ (fcoord Fd y)
    rw [e.apply_mk_symm hy]
  · -- agreement with `f` on `W`
    rintro y ⟨z, hz, hzy⟩
    have hzt := hDt hz
    have hye : y.1 ∈ e.baseSet := hzy ▸ (hr₁s z (hDball hz)).2.2.1
    have hya : y.1 ∈ Fd.ambSource := hzy ▸ finv_mem Fd hzt
    have hyz : fcoord Fd y.1 = z := by rw [← hzy, fcoord_finv Fd hzt]
    have hιy : ι (Fd.toCoord y) = fcoord Fd y.1 := Fd.coordinateInclusion_toCoord y hya
    have hty : Fd.toCoord y ∈ ball (0 : ComplexModel m) r := by
      have h1 : tanWeight n m (ι (Fd.toCoord y)) < r ^ 2 := by rw [hιy, hyz]; exact hz.1
      rw [SGPT.Trace.OTExt2.tanWeight_eq_norm_proj hk, coordinateProjection_coordinateInclusion hk]
        at h1
      rw [mem_ball_zero_iff]
      exact lt_of_pow_lt_pow_left₀ 2 hr0.le h1
    show e.symm y.1 (F₀ (fcoord Fd y.1)) = f y
    rw [← hιy, hF₀ext _ hty]
    have hfy : f₀ (Fd.toCoord y) = coef y := by
      show coef ((Fd.chart hk).symm ((Fd.chart hk) y)) = coef y
      rw [(Fd.chart hk).left_inv hya]
    rw [hfy]
    exact e.symm_apply_apply_mk hye (f y)
  · -- the critical gain
    have hKe : K ⊆ e.baseSet := by
      rintro _ ⟨z, hz, rfl⟩; exact (hr₁s z (hDball (hKcD hz))).2.2.1
    have hfrc : ContinuousOn (frameNorm V e) K := (frameNorm_continuousOn V e).mono hKe
    obtain ⟨Fp, hFp⟩ := hKcpt.exists_bound_of_continuousOn hfrc
    have hΦm : Measurable Φ := hΦ.upperSemicontinuous.measurable
    have hc1 : (1 : ℝ) + (c' - 1) = c' := by ring
    rw [hc1]
    set g : X → ℝ≥0∞ := fun x => B.indicator (fun x => ENNReal.ofReal (‖S x‖ ^ 2)) x *
      multiplierWeight c' (Φ x) * ENNReal.ofReal ((R x ^ (n - m) * Real.log (R x) ^ 2)⁻¹)
      with hg
    have hSc : ContinuousOn (fun x => ‖S x‖) B := by
      intro y hy
      obtain ⟨z, hz, rfl⟩ := hy
      have hhol : SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) V S B := by
        rintro _ ⟨z, hz, rfl⟩
        have hzt := hDt hz
        have hxe' := (hr₁s z (hDball hz)).2.2.1
        have hxa := finv_mem Fd hzt
        refine MDifferentiableAt.mdifferentiableWithinAt ?_
        rw [Trivialization.mdifferentiableAt_section_iff (IB := 𝓘(ℂ, ComplexModel n)) e S hxe']
        have hG' : DifferentiableAt ℂ F₀ (fcoord Fd (finv Fd z)) := by
          rw [fcoord_finv Fd hzt]
          exact hF₀d.differentiableAt ((SGPT.Trace.OTExt2.isOpen_localDom m r r).mem_nhds hz)
        have hcomp := hG'.mdifferentiableAt.comp (finv Fd z) (mdifferentiableAt_fcoord Fd hxa)
        refine hcomp.congr_of_eventuallyEq ?_
        filter_upwards [e.open_baseSet.mem_nhds hxe'] with y hy
        show (e ⟨y, e.symm y (F₀ (fcoord Fd y))⟩).2 = F₀ (fcoord Fd y)
        rw [e.apply_mk_symm hy]
      exact (ContinuousFiberNorm.continuous.comp_continuousOn hhol.continuousOn) _ ⟨z, hz, rfl⟩
    have hgm : Measurable g := by
      refine ((measurable_indicator_of_continuousOn' hBo (ENNReal.continuous_ofReal.comp_continuousOn
        (hSc.pow 2))).mul ((multiplierWeight_antitone hc'0.le).measurable.comp hΦm)).mul ?_
      refine ENNReal.measurable_ofReal.comp (Measurable.inv ?_)
      have hRc := hR.continuous
      exact ((hRc.pow _).measurable).mul ((Real.measurable_log.comp hRc.measurable).pow_const 2)
    obtain ⟨C₁, -, hC₁⟩ := lintegral_finv_image_le Fd hμ (isCompact_closedLocalDom n m _ _)
      (hKcD.trans hDt)
    have heqK : ∫⁻ x in K, ENNReal.ofReal (‖S x‖ ^ 2) * multiplierWeight c' (Φ x) *
        ENNReal.ofReal ((R x ^ (n - m) * Real.log (R x) ^ 2)⁻¹) ∂μ = ∫⁻ x in K, g x ∂μ := by
      refine setLIntegral_congr_fun hKcpt.isClosed.measurableSet fun y hy => ?_
      rw [hg]; simp only; rw [indicator_of_mem (image_mono hKcD hy)]
    rw [heqK]
    set CR' : ℝ := max CR 0 with hCR'
    set Kq : ℝ := Real.exp ((n - m : ℕ) * CR') * (1 + CR' / 4) ^ 2 with hKq
    have hr1 : r / 2 < 1 := by
      have : Real.exp (-2) < 1 := (Real.exp_lt_exp.mpr (show (-2 : ℝ) < 0 by norm_num)).trans_eq Real.exp_zero
      linarith
    -- the pointwise kernel comparison on `Kc`
    have hkern : ∀ z ∈ Kc, ENNReal.ofReal ((R (finv Fd z) ^ (n - m) *
        Real.log (R (finv Fd z)) ^ 2)⁻¹) ≤ ENNReal.ofReal Kq * criticalKernel n m z := by
      intro z hz
      have hzt := hDt (hKcD hz)
      by_cases hpl : z ∈ complexCoordinatePlane n m
      · have hW' : finv Fd z ∈ W := (mem_iff_fcoord Fd (finv_mem Fd hzt)).mpr
          (by rw [fcoord_finv Fd hzt]; exact hpl)
        have hR0 : R (finv Fd z) = 0 := (hR.eq_zero_iff _).mpr hW'
        have hq : n - m ≠ 0 := by omega
        rw [hR0, zero_pow hq, zero_mul, inv_zero, ENNReal.ofReal_zero]
        exact zero_le
      · have hnw := normalWeight_pos_of_notMem hpl
        have hW' : finv Fd z ∉ W := fun h => hpl (by
          have := (mem_iff_fcoord Fd (finv_mem Fd hzt)).mp h
          rwa [fcoord_finv Fd hzt] at this)
        have hRp := hR.pos_of_notMem hW'
        have hloc := hCR (finv Fd z) (hr₁s z (hDball (hKcD hz))).2.2.2.2.2 hW'
        rw [fcoord_finv Fd hzt, neg_zero, EReal.coe_zero, add_zero, logPole,
          ENNReal.log_pos_real' (by rw [ENNReal.toReal_ofReal (hR.nonneg _)]; exact hRp),
          EReal.toReal_coe, ENNReal.toReal_ofReal (hR.nonneg _)] at hloc
        have hnw1 : normalWeight n m z < 1 := by
          have h2 := hz.2
          have : (r / 2) ^ 2 < 1 := by nlinarith
          linarith
        have hle := inv_pow_mul_log_sq_le (n - m) hRp hnw (hR.lt_exp _) hnw1 (le_max_right _ _)
          (hloc.trans (le_max_left _ _))
        have hpos : 0 < normalWeight n m z ^ (n - m) * Real.log (normalWeight n m z) ^ 2 := by
          have : Real.log (normalWeight n m z) ≠ 0 := (Real.log_neg hnw hnw1).ne
          positivity
        rw [criticalKernel, ← ENNReal.ofReal_inv_of_pos hpos, ← ENNReal.ofReal_mul (by positivity)]
        exact ENNReal.ofReal_le_ofReal hle
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := C₁))
      (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := |Fp| ^ 2 * Real.exp (c' * M) * Kq))
        hF₀fin)) ?_
    refine (hC₁ g hgm).trans (mul_le_mul' le_rfl ?_)
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine (setLIntegral_mono' (isCompact_closedLocalDom n m _ _).isClosed.measurableSet
      fun z hz => ?_).trans (lintegral_mono_set hKcD)
    have hzD := hKcD hz
    have hxK : finv Fd z ∈ K := ⟨z, hz, rfl⟩
    rw [hg]; simp only
    rw [indicator_of_mem (show finv Fd z ∈ B from ⟨z, hzD, rfl⟩)]
    have hSz : ‖S (finv Fd z)‖ ≤ ‖F₀ z‖ * |Fp| := by
      rw [show S (finv Fd z) = e.symm (finv Fd z) (F₀ (fcoord Fd (finv Fd z))) from rfl,
        fcoord_finv Fd (hDt hzD),
        SGPT.PSH.GlobalL2.norm_eq_coef_mul_norm_frame e (hKe hxK),
        Trivialization.continuousLinearMapAt_apply_of_mem (R := ℂ) e (hKe hxK)]
      refine mul_le_mul (le_of_eq ?_) ?_ (norm_nonneg _) (norm_nonneg _)
      · show ‖(e ⟨_, e.symm _ (F₀ z)⟩).2‖ = ‖F₀ z‖
        rw [e.apply_mk_symm (hKe hxK)]
      · have := hFp _ hxK
        rw [Real.norm_eq_abs, abs_of_nonneg (frameNorm_pos V e (hKe hxK)).le] at this
        exact this.trans (le_abs_self _)
    have hz1 := hr₁s z (hDball hzD)
    have hΦz : Φ (finv Fd z) = P z + (hs' z : EReal) := hz1.2.2.2.1
    have hw := multiplierWeight_add_coe_le hc'0.le (x := P z) (neg_le_of_abs_le hz1.2.2.2.2.1)
    rw [hΦz]
    calc ENNReal.ofReal (‖S (finv Fd z)‖ ^ 2) * multiplierWeight c' (P z + (hs' z : EReal)) *
          ENNReal.ofReal ((R (finv Fd z) ^ (n - m) * Real.log (R (finv Fd z)) ^ 2)⁻¹)
        ≤ ENNReal.ofReal ((‖F₀ z‖ * |Fp|) ^ 2) *
          (ENNReal.ofReal (Real.exp (c' * M)) * multiplierWeight c' (P z)) *
          (ENNReal.ofReal Kq * criticalKernel n m z) := by
          gcongr
          exact hkern z hz
      _ = ENNReal.ofReal (|Fp| ^ 2 * Real.exp (c' * M) * Kq) *
          (ENNReal.ofReal (‖F₀ z‖ ^ 2) * multiplierWeight 1 ((c' : EReal) * P z) *
            criticalKernel n m z) := by
          rw [multiplierWeight_one_coe_mul, mul_pow, ENNReal.ofReal_mul (sq_nonneg ‖F₀ z‖),
            ENNReal.ofReal_mul (show 0 ≤ |Fp| ^ 2 * Real.exp (c' * M) by positivity),
            ENNReal.ofReal_mul (show 0 ≤ |Fp| ^ 2 by positivity)]
          ring
