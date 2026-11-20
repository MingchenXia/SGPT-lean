import SGPT.Trace.OTMarginPole
import SGPT.Trace.TwistedL2OTExtStatement

/-!
# Local extensions with a subcritical gain near a point of the submanifold

Blueprint `claude-ot3.tex`, node `claude-ot3:gain-patch`.

`exists_gainPatch`: let `W ⊆ X` be a closed submanifold of dimension `m`, `ψ` quasi-psh on `X`,
`c > 0` and `s` a section of `V|_W` whose coefficients lie in `𝓘(c ψ|_W)`
(`IsAlongMultiplierSection`).  Near every `p ∈ W`, in the flattening coordinates `ζ` of `p` and
the preferred frame `e` of `V` at `p`, there is a local holomorphic section `S = G(ζ) e` with
`S = s` on `W` and the subcritical gain

  `∫ |G|² e^{-c ψ} |w|^{-2(n-m)(1-1/N)} < ∞`

near `0`.  This is TN's restriction argument (`RestrictionOhsawaTakegoshi`) with the
Ohsawa--Takegoshi extension replaced by the ramified extension with gain
(`exists_extension_flat`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Trace.OTMargin

open Set Filter Metric MeasureTheory Bundle
open scoped Topology ENNReal NNReal Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace
  SGPT.Foundations.Analysis.FirstPass.RegularLocusDense SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Trace.TwistedL2

/-- `e^{-c(x + h)} ≤ e^{cM} e^{-cx}` for `h ≥ -M`. -/
theorem multiplierWeight_add_coe_le {c : ℝ} (hc : 0 ≤ c) {x : EReal} {h M : ℝ} (hhM : -M ≤ h) :
    multiplierWeight c (x + (h : EReal)) ≤ ENNReal.ofReal (Real.exp (c * M)) * multiplierWeight c x := by
  induction x using EReal.rec with
  | bot =>
      rw [EReal.bot_add]
      rcases hc.lt_or_eq with h | h
      · rw [multiplierWeight_bot h, ENNReal.mul_top (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne']
      · subst h; simp [multiplierWeight]
  | coe s =>
      rw [← EReal.coe_add, multiplierWeight_coe, multiplierWeight_coe,
        ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by nlinarith))
  | top =>
      rw [EReal.top_add_coe]; exact le_of_eq (by
        rcases hc.lt_or_eq with h | h
        · rw [multiplierWeight_top h, mul_zero]
        · subst h; simp [multiplierWeight])

theorem ball_subset_flatDom {n m : ℕ} (hmn : m ≤ n) {r : ℝ} :
    ball (0 : ComplexModel n) r ⊆ flatDom n m (ball 0 r) r := by
  intro z hz
  rw [mem_ball_zero_iff] at hz
  refine ⟨?_, fun i _ => (PiLp.norm_apply_le z i).trans_lt hz⟩
  rw [mem_ball_zero_iff]
  refine lt_of_le_of_lt ?_ hz
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), EuclideanSpace.norm_sq_eq,
    EuclideanSpace.norm_sq_eq]
  have : ∑ a : Fin m, ‖coordinateProjection n m z a‖ ^ 2 =
      ∑ a : Fin m, ‖z ⟨a.1, lt_of_lt_of_le a.2 hmn⟩‖ ^ 2 := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [coordinateProjection_apply, dif_pos (lt_of_lt_of_le a.2 hmn)]
  rw [this]
  have hinj : Function.Injective (fun a : Fin m => (⟨a.1, lt_of_lt_of_le a.2 hmn⟩ : Fin n)) :=
    fun a b h => Fin.ext (by simpa using congrArg Fin.val h)
  calc ∑ a : Fin m, ‖z ⟨a.1, lt_of_lt_of_le a.2 hmn⟩‖ ^ 2
      = ∑ i ∈ Finset.univ.map ⟨_, hinj⟩, ‖z i‖ ^ 2 := by rw [Finset.sum_map]; rfl
    _ ≤ ∑ i, ‖z i‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => by positivity

theorem norm_lt_of_mem_flatDom {n m : ℕ} (_hmn : m ≤ n) {r : ℝ} (hr : 0 < r) {z : ComplexModel n}
    (hz : z ∈ flatDom n m (ball 0 r) r) : ‖z‖ < (n + 1) * r := by
  have hcoord : ∀ i : Fin n, ‖z i‖ ≤ r := by
    intro i
    by_cases hi : m ≤ i.1
    · exact (hz.2 i hi).le
    · have h1 : z i = coordinateProjection n m z ⟨i.1, by omega⟩ := by
        rw [coordinateProjection_apply, dif_pos i.2]
      rw [h1]
      exact (PiLp.norm_apply_le _ _).trans (mem_ball_zero_iff.mp hz.1).le
  have hsq : ‖z‖ ^ 2 ≤ n * r ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc ∑ i, ‖z i‖ ^ 2 ≤ ∑ _i : Fin n, r ^ 2 :=
          Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hcoord i) 2
      _ = n * r ^ 2 := by simp
  have hlt : (n : ℝ) * r ^ 2 < ((n + 1) * r) ^ 2 := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith [sq_nonneg r, mul_pos hr hr]
  exact lt_of_pow_lt_pow_left₀ 2 (by positivity) (hsq.trans_lt hlt)

theorem multiplierWeight_one_coe_mul (c : ℝ) (x : EReal) :
    multiplierWeight 1 ((c : EReal) * x) = multiplierWeight c x := by
  simp [multiplierWeight]

variable {n m : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {W : Set X}
  (V : X → Type) [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℂ (V x)]
  [TopologicalSpace (TotalSpace ℂ V)] [FiberBundle ℂ V] [VectorBundle ℂ ℂ V]
  [ContMDiffVectorBundle ∞ ℂ V 𝓘(ℂ, ComplexModel n)]

/-- **A local extension with subcritical gain** near `p ∈ W`. -/
theorem exists_gainPatch (hk : m ≤ n) (hW : ∀ x ∈ W, RegularAtDim (n := n) W x m)
    {ψ : X → EReal} (hψ : ManifoldQuasiPlurisubharmonic (n := n) ψ) {c : ℝ} (hc : 0 < c)
    {N : ℕ} (hN : N ≠ 0) {s : (y : W) → V y}
    (hs : letI := chartedSpace hk hW
      haveI := isComplexManifold_chartedSpace hk hW
      IsAlongMultiplierSection V (m := m) c (fun y : W => ψ y) s) (p : W) :
    ∃ r > 0, ∃ G : ComplexModel n → ℂ, ∃ S : (x : X) → V x,
      ball (0 : ComplexModel n) r ⊆ (FlatData.ofRegularAtDim (hW p.1 p.2)).flat.target ∧
      (∀ z ∈ ball (0 : ComplexModel n) r,
        finv (FlatData.ofRegularAtDim (hW p.1 p.2)) z ∈ (trivializationAt ℂ V p.1).baseSet) ∧
      DifferentiableOn ℂ G (ball 0 r) ∧
      (∀ x ∈ finv (FlatData.ofRegularAtDim (hW p.1 p.2)) '' ball 0 r,
        S x = (trivializationAt ℂ V p.1).symm x (G (fcoord (FlatData.ofRegularAtDim (hW p.1 p.2)) x))) ∧
      SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) V S
        (finv (FlatData.ofRegularAtDim (hW p.1 p.2)) '' ball 0 r) ∧
      (∀ y : W, y.1 ∈ finv (FlatData.ofRegularAtDim (hW p.1 p.2)) '' ball 0 r → S y = s y) ∧
      ∀ ε, 0 < ε → ε < r →
        ∫⁻ z in closedBall 0 ε, ENNReal.ofReal (‖G z‖ ^ 2) *
          multiplierWeight c (ψ (finv (FlatData.ofRegularAtDim (hW p.1 p.2)) z)) *
          ENNReal.ofReal (normalWeight n m z ^ (-(((n - m : ℕ) : ℝ) * (1 - 1 / (N : ℝ))))) ≠ ⊤ := by
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
  -- the coefficient of `s` in the frame `e`, in the chart of `W` at `p`
  set coef : W → ℂ := alongCoefficient V e s with hcoef
  have hmem := hs p
  obtain ⟨-, hint1⟩ := hmem
  have hint : MultiplierIntegrableAt (chartFunction (fun q : W => ψ q.1) (complexChartAt (n := m) p)) c
      (fun z => coef ((complexChartAt (n := m) p).val.symm z)) ((complexChartAt (n := m) p).val p)
      volume := (SGPT.Bergman.MultiplierSectionsDraft.multiplierIntegrableAt_scaled_one_iff _ hc _ _ _).mp
        hint1
  set ψt : ComplexModel n → EReal := fun z => chartFunction ψ amb (flat.symm z) with hψtdef
  set f : ComplexModel m → ℂ := fun ζ => coef ((complexChartAt (n := m) p).val.symm ζ) with hfdef
  -- Step 1: the weight of `ψ|_W` in the chart of `W` at `p` is `ψt ∘ ι`
  have h0T : (0 : ComplexModel m) ∈ Fd.coordTarget := by
    rw [← hζ0]; exact Fd.toCoord_mem_coordTarget p hxsrc
  have hweightW : chartFunction (fun q : W => ψ q.1) (complexChartAt (n := m) p) =ᶠ[𝓝 0]
      fun ζ => ψt (ι ζ) := by
    filter_upwards [Fd.isOpen_coordTarget.mem_nhds h0T] with ζ hζ
    show ψ (((Fd.chart hk).symm ζ : W) : X) = ψ (amb.val.symm (flat.symm (ι ζ)))
    rw [show (((Fd.chart hk).symm ζ : W) : X) = Fd.ofCoord ζ from Fd.invPoint_val hζ]
    rfl
  have hintW : MultiplierIntegrableAt (fun ζ => ψt (ι ζ)) c f 0 volume := by
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
  have hψamb : QuasiPlurisubharmonicOn (chartFunction ψ amb) amb.val.target := hψ amb
  have hψ0 : QuasiPlurisubharmonicAt ψt 0 := by
    have hq : QuasiPlurisubharmonicAt (chartFunction ψ amb) (flat.symm 0) := by
      rw [hsymm0]; exact hψamb _ (amb.val.map_source hxsrc.1)
    exact HolomorphicPullback.quasiPlurisubharmonicAt_comp_holomorphic flat.open_target
      hflat_symm_cd h0flat hq
  -- Step 3: `ψt = P + h` near the origin, `P` psh, `h` smooth and bounded
  obtain ⟨P, hs', hP, hhs, heq⟩ := id hψ0
  obtain ⟨UP, hUP, h0UP, hPdisc⟩ := id hP
  have hscont : ContinuousAt hs' 0 := hhs.self_of_nhds.continuousAt
  set M : ℝ := |hs' 0| + 1 with hM
  have hsbd : ∀ᶠ y in 𝓝 (0 : ComplexModel n), |hs' y| ≤ M := by
    filter_upwards [hscont.eventually_mem (Metric.ball_mem_nhds (hs' 0) one_pos)] with y hy
    rw [mem_ball, Real.dist_eq] at hy
    have := abs_sub_abs_le_abs_sub (hs' y) (hs' 0)
    linarith
  -- Step 4: the slice integral of `|f|² e^{-c P(·, 0)}` is finite near the origin
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
    multiplierIntegrableAt_of_moreSingularAt hPι hmoreW hintW
  -- Step 5: a radius on which everything holds
  have hev : ∀ᶠ z in 𝓝 (0 : ComplexModel n), z ∈ UP ∧ z ∈ flat.target ∧
      finv Fd z ∈ e.baseSet ∧ ψt z = P z + (hs' z : EReal) ∧ |hs' z| ≤ M := by
    have hfc : ContinuousAt (finv Fd) 0 :=
      (continuousOn_finv Fd).continuousAt (flat.open_target.mem_nhds h0flat)
    have hfx : finv Fd 0 = x := by
      show amb.val.symm (flat.symm 0) = x
      rw [hsymm0, amb.val.left_inv hxsrc.1]
    have hxe : x ∈ e.baseSet := mem_baseSet_trivializationAt ℂ V x
    filter_upwards [hUP.mem_nhds h0UP, flat.open_target.mem_nhds h0flat,
      hfc.eventually (by rw [hfx]; exact e.open_baseSet.mem_nhds hxe), heq, hsbd]
      with z h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨r₁, hr₁, hr₁s⟩ := Metric.eventually_nhds_iff_ball.mp hev
  obtain ⟨r₂, hr₂, hr₂U'⟩ := Metric.isOpen_iff.mp hU' 0 h0U'
  set r : ℝ := min (r₁ / (n + 1)) r₂ with hr
  have hr0 : 0 < r := lt_min (by positivity) hr₂
  have hrr₁ : (n + 1) * r ≤ r₁ := by
    have : r ≤ r₁ / (n + 1) := min_le_left _ _
    rw [le_div_iff₀ (by positivity)] at this; linarith
  have hdom : flatDom n m (ball (0 : ComplexModel m) r) r ⊆ ball 0 r₁ := fun z hz =>
    mem_ball_zero_iff.mpr ((norm_lt_of_mem_flatDom hk hr0 hz).trans_le hrr₁)
  have hball_r : ball (0 : ComplexModel n) r ⊆ ball 0 r₁ := fun z hz =>
    hdom (ball_subset_flatDom hk hz)
  -- Step 6: the ramified Ohsawa--Takegoshi extension with gain
  have hPpsh : PlurisubharmonicOn (fun z => (c : EReal) * P z) (flatDom n m (ball 0 r) r) := by
    refine PlurisubharmonicOn.const_mul (fun y hy => ⟨UP, hUP, (hr₁s y (hdom hy)).1, hPdisc⟩) hc
  have hsliceU' : ball (0 : ComplexModel m) r ⊆ U' := fun w hw =>
    hr₂U' (ball_subset_ball (min_le_right _ _) hw)
  have hfi : ∫⁻ w in ball (0 : ComplexModel m) r,
      multiplierDensity (fun w => (c : EReal) * P (coordinateInclusion n m w)) 1 f w ≠ ⊤ := by
    rw [SGPT.Bergman.MultiplierSectionsDraft.multiplierDensity_scaled_one
      (fun w => P (coordinateInclusion n m w)) c f]
    exact ne_top_of_le_ne_top hfint.2.ne (lintegral_mono_set hsliceU')
  obtain ⟨G, hGd, hGext, hGint⟩ := exists_extension_flat hk isOpen_ball (convex_ball 0 r) hr0 hN
    hPpsh (hfU'.mono hsliceU') hfi
  have hGball : DifferentiableOn ℂ G (ball 0 r) := hGd.mono (ball_subset_flatDom hk)
  set S : (x : X) → V x := fun y => e.symm y (G (fcoord Fd y)) with hS
  refine ⟨r, hr0, G, S, fun z hz => (hr₁s z (hball_r hz)).2.1,
    fun z hz => (hr₁s z (hball_r hz)).2.2.1, hGball, fun _ _ => rfl, ?_, ?_, ?_⟩
  · -- holomorphy of `S`
    rintro _ ⟨z, hz, rfl⟩
    have hzt := (hr₁s z (hball_r hz)).2.1
    have hxe := (hr₁s z (hball_r hz)).2.2.1
    have hxa := finv_mem Fd hzt
    refine MDifferentiableAt.mdifferentiableWithinAt ?_
    rw [Trivialization.mdifferentiableAt_section_iff (IB := 𝓘(ℂ, ComplexModel n)) e S hxe]
    have hG' : DifferentiableAt ℂ G (fcoord Fd (finv Fd z)) := by
      rw [fcoord_finv Fd hzt]; exact hGball.differentiableAt (isOpen_ball.mem_nhds hz)
    have hcomp := hG'.mdifferentiableAt.comp (finv Fd z) (mdifferentiableAt_fcoord Fd hxa)
    refine hcomp.congr_of_eventuallyEq ?_
    filter_upwards [e.open_baseSet.mem_nhds hxe] with y hy
    show (e ⟨y, e.symm y (G (fcoord Fd y))⟩).2 = G (fcoord Fd y)
    rw [e.apply_mk_symm hy]
  · -- agreement with `s` on `W`
    rintro y ⟨z, hz, hzy⟩
    have hzt := (hr₁s z (hball_r hz)).2.1
    have hye : y.1 ∈ e.baseSet := hzy ▸ (hr₁s z (hball_r hz)).2.2.1
    have hya : y.1 ∈ Fd.ambSource := hzy ▸ finv_mem Fd hzt
    have hyz : fcoord Fd y.1 = z := by rw [← hzy, fcoord_finv Fd hzt]
    have hιy : ι (Fd.toCoord y) = fcoord Fd y.1 := Fd.coordinateInclusion_toCoord y hya
    have hty : Fd.toCoord y ∈ ball (0 : ComplexModel m) r := by
      rw [mem_ball_zero_iff, ← RestrictionOhsawaTakegoshi.norm_coordinateInclusion_of_le hk, hιy, hyz]
      exact mem_ball_zero_iff.mp hz
    show e.symm y.1 (G (fcoord Fd y.1)) = s y
    rw [← hιy, hGext _ hty]
    have hfy : f (Fd.toCoord y) = coef y := by
      show coef ((Fd.chart hk).symm ((Fd.chart hk) y)) = coef y
      rw [(Fd.chart hk).left_inv hya]
    rw [hfy]
    exact e.symm_apply_apply_mk hye (s y)
  · -- the gain
    intro ε hε0 hεr
    set a : ℝ := ((n - m : ℕ) : ℝ) * (1 - 1 / (N : ℝ))
    have hcb : closedBall (0 : ComplexModel n) ε ⊆ flatDom n m (ball 0 r) r :=
      (closedBall_subset_ball hεr).trans (ball_subset_flatDom hk)
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := Real.exp (c * M)))
      hGint) ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine (setLIntegral_mono' measurableSet_closedBall fun z hz => ?_).trans
      (lintegral_mono_set hcb)
    have hz1 := hr₁s z (hball_r (closedBall_subset_ball hεr hz))
    have hψz : ψ (finv Fd z) = P z + (hs' z : EReal) := hz1.2.2.2.1
    rw [hψz]
    have hw := multiplierWeight_add_coe_le hc.le (x := P z) (neg_le_of_abs_le hz1.2.2.2.2)
    simp only [multiplierDensity, multiplierWeight_one_coe_mul]
    calc ENNReal.ofReal (‖G z‖ ^ 2) * multiplierWeight c (P z + (hs' z : EReal)) *
          ENNReal.ofReal (normalWeight n m z ^ (-a))
        ≤ ENNReal.ofReal (‖G z‖ ^ 2) * (ENNReal.ofReal (Real.exp (c * M)) * multiplierWeight c (P z)) *
          ENNReal.ofReal (normalWeight n m z ^ (-a)) := by gcongr
      _ = _ := by ring

end SGPT.Trace.OTMargin
