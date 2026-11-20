import SGPT.Trace.TwistedL2YLimit

/-!
# The density lemma and the twisted `L²` estimate on a complex manifold

Blueprint `claude-tl2-man2.tex` (lane TL2-MAN2, `claude-tl2-man2:main`).  Every twisted datum on a
complex manifold `X` satisfies `SigmaGraphDensityX` (`claude-tl2-man:sigma-density`): the
`ℂⁿ`-argument of `claude-tl2-dens:main` on `X`, with the projected field `exists_vX`, the
localization `exists_localizationX` into chart-frame domains, Friedrichs' lemma in each chart-frame
(`exists_approxG`) and the diagonal argument over the complete cut-offs.  Consequently
`TwistedL2CorrectionStatement n X` and `CompactTwistedL2CorrectionStatement n X` hold for every
complex manifold `X` (`twistedL2CorrectionStatement_manifold`,
`compactTwistedL2CorrectionStatement_manifold`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter MeasureTheory Matrix Metric
open scoped Topology ContDiff ComplexConjugate Manifold ComplexOrder InnerProductSpace ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.Pending.CauchyGreen SGPT.Foundations.Analysis.Pending.Hormander
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
open HermitianHolomorphicLineBundle SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Foundations.Analysis.Pending.OTChen

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

theorem continuous_of_chartSmooth {χ : X → ℝ} (hχ : ChartSmooth (n := n) χ) : Continuous χ := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  set c := complexChartAt (n := n) x
  have hxs : x ∈ c.val.source := mem_complexChartAt_source x
  have h1 : ContinuousAt (fun z => χ (c.val.symm z)) (c.val x) :=
    (hχ c).continuousOn.continuousAt (c.val.open_target.mem_nhds (c.val.map_source hxs))
  have h2 : ContinuousAt (fun y => χ (c.val.symm (c.val y))) x :=
    h1.comp (c.val.continuousOn.continuousAt (c.val.open_source.mem_nhds hxs))
  refine h2.congr ?_
  filter_upwards [c.val.open_source.mem_nhds hxs] with y hy
  rw [c.val.left_inv hy]

variable [MeasurableSpace X] [BorelSpace X]

namespace TwistedDatum

variable {T : TwistedDatum n X}

/-! ### Bookkeeping -/

theorem ArX_sub (c : ComplexChart n X) (e : AtlasFrame T.L) (g g' : ComplexModel n → ℂ) (x : X) :
    T.ArX c e (fun z => g z - g' z) x = T.ArX c e g x - T.ArX c e g' x := by
  by_cases hx : x ∈ T.cfd c e
  · simp only [ArX, indicator_of_mem hx]; ring
  · simp [ArX, indicator_of_notMem hx]

theorem SrX_sub (c : ComplexChart n X) (e : AtlasFrame T.L)
    (β β' : ComplexModel n → Matrix (Fin n) (Fin n) ℂ) (x : X) :
    T.SrX c e (fun z => β z - β' z) x = T.SrX c e β x - T.SrX c e β' x := by
  by_cases hx : x ∈ T.cfd c e
  · simp only [SrX, indicator_of_mem hx, Matrix.mul_sub, Matrix.sub_mul]
    rw [← smul_sub]
    congr 1
  · simp [SrX, indicator_of_notMem hx]

theorem SrX_congr {c : ComplexChart n X} {e : AtlasFrame T.L}
    {β β' : ComplexModel n → Matrix (Fin n) (Fin n) ℂ}
    (h : ∀ z ∈ T.pieceDomain c e, β z = β' z) (x : X) : T.SrX c e β x = T.SrX c e β' x := by
  by_cases hx : x ∈ T.cfd c e
  · simp only [SrX, indicator_of_mem hx, h _ (chart_mem_pieceDomain hx)]
  · simp [SrX, indicator_of_notMem hx]

theorem memLp_of_chart_ArX {c : ComplexChart n X} {e : AtlasFrame T.L} {K : Set (ComplexModel n)}
    (hK : IsCompact K) (hKd : K ⊆ T.pieceDomain c e) {g : ComplexModel n → ℂ}
    (hg : MemLp g 2 volume) (hgm : Measurable g) (h0 : ∀ z ∉ K, g z = 0) :
    MemLp (T.ArX c e g) 2 T.μ := by
  obtain ⟨C, hC⟩ := exists_eLpNorm_ArX_le (T := T) c e hK hKd
  exact ⟨(measurable_ArX c e hgm).aestronglyMeasurable,
    (hC g hgm h0).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hg.2)⟩

theorem memLp_of_chart_SrX {c : ComplexChart n X} {e : AtlasFrame T.L} {K : Set (ComplexModel n)}
    (hK : IsCompact K) (hKd : K ⊆ T.pieceDomain c e)
    {β : ComplexModel n → Matrix (Fin n) (Fin n) ℂ} (hβ : MemLp (fun z => flat2 (β z)) 2 volume)
    (hβm : ∀ a b, Measurable fun z => β z a b) (h0 : ∀ z ∉ K, β z = 0) :
    MemLp (T.SrX c e β) 2 T.μ := by
  obtain ⟨C, hC⟩ := exists_eLpNorm_SrX_le (T := T) c e hK hKd
  exact ⟨(measurable_SrX c e hβm).aestronglyMeasurable,
    (hC β hβm h0).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hβ.2)⟩

theorem memLp_flat2_of_entries {β : ComplexModel n → Matrix (Fin n) (Fin n) ℂ}
    (hβ : ∀ j k, MemLp (fun z => β z j k) 2 volume) :
    MemLp (fun z => flat2 (β z)) 2 volume := by
  have hg : MemLp (fun z => ∑ p : Fin n × Fin n, ‖β z p.1 p.2‖) 2 volume :=
    memLp_finsetSum _ fun (p : Fin n × Fin n) _ => (hβ p.1 p.2).norm
  refine hg.of_le (aestronglyMeasurable_flat2 fun j k => (hβ j k).1)
    (Eventually.of_forall fun z => ?_)
  rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)]
  exact (norm_euclid_le_sum _).trans (le_of_eq rfl)

theorem norm_flat2_le_sum (M : Matrix (Fin n) (Fin n) ℂ) :
    ‖flat2 M‖ ≤ ∑ p : Fin n × Fin n, ‖M p.1 p.2‖ :=
  norm_euclid_le_sum _

theorem contDiffOn_sigmaMatX' (c : ComplexChart n X) (e : AtlasFrame T.L) (l k : Fin n) :
    ContDiffOn ℝ ∞ (fun z => sigmaMatX T.omega T.r c z l k) (T.pieceDomain c e) :=
  (contDiffOn_sigmaMatX T.isOpen_U T.kahler c l k).mono (T.pieceDomain_subset_chartSmooth c e)

theorem measurable_f0G {c : ComplexChart n X} {e : AtlasFrame T.L} {ζ : ComplexModel n → ℝ}
    (hζ : ContDiff ℝ ∞ ζ) (hζd : tsupport ζ ⊆ T.pieceDomain c e) {W : ComplexModel n → ComplexModel n}
    (hW : Measurable W) {Θ : ComplexModel n → ℂ} (hΘ : ContinuousOn Θ (T.pieceDomain c e)) :
    Measurable (f0G ζ W Θ) := by
  have hζc : Continuous fun z => (ζ z : ℂ) := Complex.continuous_ofReal.comp hζ.continuous
  have h1 : Measurable fun z => (ζ z : ℂ) * Θ z :=
    measurable_of_continuousOn_of_eq_zero (T.isOpen_pieceDomain c e)
      (hζc.continuousOn.mul hΘ) fun z hz => by
        simp [image_eq_zero_of_notMem_tsupport fun h => hz (hζd h)]
  have h2 : ∀ l, Measurable fun z => dDir (coordVec l) (fun y => (ζ y : ℂ)) z * W z l := fun l =>
    (contDiff_dDir (k := 0) ((Complex.ofRealCLM.contDiff.comp hζ).of_le (by norm_num))).continuous.measurable.mul
      (((EuclideanSpace.proj l : ComplexModel n →L[ℂ] ℂ).continuous.measurable).comp hW)
  exact h1.sub (Finset.measurable_sum _ fun l _ => h2 l)

theorem measurable_fSG {c : ComplexChart n X} {e : AtlasFrame T.L} {ζ : ComplexModel n → ℝ}
    (hζ : ContDiff ℝ ∞ ζ) (hζd : tsupport ζ ⊆ T.pieceDomain c e) {W : ComplexModel n → ComplexModel n}
    (hW : Measurable W) (j k : Fin n) :
    Measurable (fSG (sigmaMatX T.omega T.r c) ζ W j k) := by
  have hζc : ContDiff ℝ ∞ fun z => (ζ z : ℂ) := Complex.ofRealCLM.contDiff.comp hζ
  have hd : ∀ a, Continuous (dbarDir (coordVec a) fun y => (ζ y : ℂ)) := fun a =>
    continuous_dbarDir' (hζc.of_le (by simp))
  have hm : ∀ a b l, Measurable fun z => dbarDir (coordVec a) (fun y => (ζ y : ℂ)) z *
      sigmaMatX T.omega T.r c z l b := fun a b l =>
    measurable_of_continuousOn_of_eq_zero (T.isOpen_pieceDomain c e)
      ((hd a).continuousOn.mul (contDiffOn_sigmaMatX' (T := T) c e l b).continuousOn) fun z hz => by
        have hz' : z ∉ tsupport fun y => (ζ y : ℂ) := fun h =>
          hz (hζd ((tsupport_comp_subset Complex.ofReal_zero ζ) h))
        simp [dbarDir_eq_zero_of_notMem hz']
  have hWl : ∀ l, Measurable fun z => W z l := fun l =>
    ((EuclideanSpace.proj l : ComplexModel n →L[ℂ] ℂ).continuous.measurable).comp hW
  have hfun : fSG (sigmaMatX T.omega T.r c) ζ W j k = fun z => ∑ l,
      ((dbarDir (coordVec j) (fun y => (ζ y : ℂ)) z * sigmaMatX T.omega T.r c z l k) * W z l -
        (dbarDir (coordVec k) (fun y => (ζ y : ℂ)) z * sigmaMatX T.omega T.r c z l j) * W z l) := by
    funext z
    simp only [fSG, lowS, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [hfun]
  exact Finset.measurable_sum _ fun l _ => ((hm j k l).mul (hWl l)).sub ((hm k j l).mul (hWl l))

theorem continuousOn_sigmaDbarG {c : ComplexChart n X} {e : AtlasFrame T.L}
    {h : ComplexModel n → ComplexModel n} (hh : ContDiff ℝ ∞ h) (j k : Fin n) :
    ContinuousOn (fun z => sigmaDbarG (sigmaMatX T.omega T.r c) h z j k) (T.pieceDomain c e) := by
  have hO := T.isOpen_pieceDomain c e
  have hl : ∀ a, ContDiffOn ℝ ∞ (fun y => lowS (sigmaMatX T.omega T.r c) h y a)
      (T.pieceDomain c e) := fun a =>
    ContDiffOn.sum fun l _ => (contDiffOn_sigmaMatX' (T := T) c e l a).mul
      (contDiffOn_coord hh.contDiffOn l)
  simp only [sigmaDbarG, of_apply]
  exact (contDiffOn_dbarDir hO (hl k) _).continuousOn.sub (contDiffOn_dbarDir hO (hl j) _).continuousOn

theorem sigmaDbarG_eq_zero {c : ComplexChart n X} {h : ComplexModel n → ComplexModel n}
    {z : ComplexModel n} (hz : z ∉ tsupport h) : sigmaDbarG (sigmaMatX T.omega T.r c) h z = 0 := by
  have hev : ∀ a, (fun y => lowS (sigmaMatX T.omega T.r c) h y a) =ᶠ[𝓝 z] fun _ => 0 := by
    intro a
    filter_upwards [(isClosed_tsupport h).isOpen_compl.mem_nhds hz] with y hy
    simp [lowS, image_eq_zero_of_notMem_tsupport hy]
  ext j k
  simp [sigmaDbarG, dbarDir_eq_zero_of_eventuallyEq_zero (hev _)]

/-! ### One cut-off level -/

/-- **One cut-off level on a manifold** (`claude-tl2-man2:level`). -/
theorem exists_levelX (F : T.XFam) (v : H2X T)
    (hW1 : ∀ (c : ComplexChart n X) (e : AtlasFrame T.L) (ψ : ComplexModel n → ℂ),
      IsTestFunctionOn (T.pieceDomain c e) ψ → ∀ j k : Fin n,
      ∫ z, (T.pieceDomain c e).indicator (fun z =>
        conj (dDir (coordVec k) ψ z) * lowS (sigmaMatX T.omega T.r c) (T.WeX c e v) z j -
        conj (dDir (coordVec j) ψ z) * lowS (sigmaMatX T.omega T.r c) (T.WeX c e v) z k) z = 0)
    (hW2 : ∀ (c : ComplexChart n X) (e : AtlasFrame T.L) (u : ComplexModel n → ℂ),
      IsTestFunctionOn (T.pieceDomain c e) u →
      ∫ z, (T.pieceDomain c e).indicator (fun z => cweight (T.pX c e) z *
        ∑ l, dbarDir (coordVec l) u z * conj (T.WeX c e v z l)) z =
      ∫ z, u z * conj (chartTheta (T.pX c e) (F.tot c e) z) * cweight (T.pX c e) z)
    {χ : X → ℝ} (hχ : ChartSmooth (n := n) χ) (hχc : HasCompactSupport χ)
    (hχU : tsupport χ ⊆ T.U) :
    ∃ Fs : ℕ → T.XFam,
      Tendsto (fun m => (Fs m).data) atTop (𝓝 (∫ x, (χ x : ℂ) * ⟪v x, T.yG x⟫_ℂ ∂T.μ)) ∧
      Tendsto (fun m => (Fs m).energy) atTop (𝓝 (∫ x, ‖T.AlimX F χ v x‖ ^ 2 ∂T.μ)) ∧
      Tendsto (fun m => (Fs m).senergy) atTop
        (𝓝 ((1 / 2 : ℝ) * ∫ x, ‖T.SlimX χ v x‖ ^ 2 ∂T.μ)) ∧
      MemLp (T.AlimX F χ v) 2 T.μ ∧ MemLp (T.SlimX χ v) 2 T.μ := by
  obtain ⟨N, c, e, ζ, D, K, hζs, hζd, hDo, hKc, hDK, hKd, hζC, hζcs, hζD, hsum⟩ :=
    T.exists_localizationX hχ hχc hχU
  have hDd : ∀ i, D i ⊆ T.pieceDomain (c i) (e i) := fun i => (hDK i).trans (hKd i)
  have hζK : ∀ i, tsupport (chartFn (c i) (ζ i)) ⊆ K i := fun i => (hζD i).trans (hDK i)
  have hζpd : ∀ i, tsupport (chartFn (c i) (ζ i)) ⊆ T.pieceDomain (c i) (e i) := fun i =>
    (hζK i).trans (hKd i)
  have hΘ : ∀ i, ContinuousOn (chartTheta (T.pX (c i) (e i)) (F.tot (c i) (e i)))
      (T.pieceDomain (c i) (e i)) := fun i =>
    continuousOn_chartTheta' (T.isOpen_pieceDomain _ _) (contDiffOn_pX _ _) (F.contDiffOn_tot _ _)
  have happ := fun i => exists_approxG (T.isOpen_pieceDomain (c i) (e i))
    (contDiffOn_pX (c i) (e i)) (contDiffOn_sigmaMatX' (T := T) (c i) (e i))
    (isLocL2_WeX (c i) (e i) v) (hΘ i) (hW1 (c i) (e i)) (hW2 (c i) (e i)) (hζC i) (hζcs i)
    (hDo i) (hζD i) (hDd i)
  choose hs hspec using happ
  have hsT := fun i m => (hspec i).1 m
  have hsD := fun i m => (hspec i).2.1 m
  have hc1 := fun i => (hspec i).2.2.1
  have hc2 := fun i => (hspec i).2.2.2.1
  have hc3 := fun i => (hspec i).2.2.2.2.1
  have hf0 := fun i => (hspec i).2.2.2.2.2.1
  have hfS := fun i => (hspec i).2.2.2.2.2.2
  let Fs : ℕ → T.XFam := fun m =>
    { ι := Fin N, s := Finset.univ, c := c, e := e, h := fun i => hs i m,
      spec := fun i => ⟨(hsT i m).1, (hsT i m).2, (hsD i m).trans (hDd i)⟩ }
  have hWm : ∀ i, Measurable (T.WeX (c i) (e i) v) := fun i =>
    measurable_WeX (c i) (e i) (measurable_coe v)
  -- the localizing functions on `X`
  have hζX : ∀ i x, ζ i x = (c i).val.source.indicator
      (fun x => chartFn (c i) (ζ i) ((c i).val x)) x := by
    intro i x
    by_cases hx : x ∈ (c i).val.source
    · rw [indicator_of_mem hx, chartFn_chart _ hx]
    · rw [indicator_of_notMem hx]
      exact image_eq_zero_of_notMem_tsupport fun h => hx ((hζd i h).1.1)
  have hζm : ∀ i, Measurable fun x => ((ζ i x : ℝ) : ℂ) := fun i => by
    have := Complex.measurable_ofReal.comp
      (measurable_indicator_comp_chart (c i) (hζC i).continuous.measurable)
    convert this using 1
    funext x
    simp only [Function.comp, hζX i x]
  have hζb : ∀ i, ∃ M, 0 ≤ M ∧ ∀ x, ‖((ζ i x : ℝ) : ℂ)‖ ≤ M := by
    intro i
    obtain ⟨M, hM⟩ := (hζC i).continuous.bounded_above_of_compact_support (hζcs i)
    refine ⟨max M 0, le_max_right _ _, fun x => ?_⟩
    rw [Complex.norm_real, hζX i x]
    by_cases hx : x ∈ (c i).val.source
    · rw [indicator_of_mem hx]; exact (hM _).trans (le_max_left _ _)
    · rw [indicator_of_notMem hx, norm_zero]; exact le_max_right _ _
  -- the limit identities
  have hsumC : ∀ x, ((χ x : ℝ) : ℂ) = ∑ i, ((ζ i x : ℝ) : ℂ) := fun x => by
    rw [← hsum x]; push_cast; rfl
  have hdR : ∀ x, T.dRX χ x = ∑ i, T.dRX (ζ i) x := fun x => by
    rw [← dRX_sum hζs x]
    congr 1
    funext y
    exact (hsum y).symm
  have hAeq : ∀ x, T.AlimX F χ v x = ∑ i, T.ArX (c i) (e i)
      (f0G (chartFn (c i) (ζ i)) (T.WeX (c i) (e i) v)
        (chartTheta (T.pX (c i) (e i)) (F.tot (c i) (e i)))) x := by
    intro x
    simp only [ArX_f0 F (hζs _) (hζd _) (v : X → ComplexModel n) x]
    by_cases hx : x ∈ T.U
    · simp only [AlimX, indicator_of_mem hx]
      rw [hsumC x, hdR x, sum_inner, Finset.mul_sum, Finset.mul_sum,
        Finset.sum_mul, ← Finset.sum_sub_distrib]
    · simp [AlimX, indicator_of_notMem hx]
  have hSeq : ∀ x, T.SlimX χ v x = ∑ i, T.SrX (c i) (e i) (fun z => Matrix.of fun j k =>
      fSG (sigmaMatX T.omega T.r (c i)) (chartFn (c i) (ζ i)) (T.WeX (c i) (e i) v) j k z) x := by
    intro x
    simp only [SrX_fS (hζs _) (hζd _) (v : X → ComplexModel n) x, SlimX]
    rw [hdR x, wedgeM_sum_left, flat2_sum]
  -- measurability and `L²`-membership of the pieces
  have hf0m : ∀ i, Measurable (f0G (chartFn (c i) (ζ i)) (T.WeX (c i) (e i) v)
      (chartTheta (T.pX (c i) (e i)) (F.tot (c i) (e i)))) := fun i =>
    measurable_f0G (hζC i) (hζpd i) (hWm i) (hΘ i)
  have hf00 : ∀ i, ∀ z ∉ K i, f0G (chartFn (c i) (ζ i)) (T.WeX (c i) (e i) v)
      (chartTheta (T.pX (c i) (e i)) (F.tot (c i) (e i))) z = 0 := by
    intro i z hz
    have hz' : z ∉ tsupport (chartFn (c i) (ζ i)) := fun h => hz (hζK i h)
    have hz'' : z ∉ tsupport fun y => ((chartFn (c i) (ζ i) y : ℝ) : ℂ) := fun h =>
      hz' ((tsupport_comp_subset Complex.ofReal_zero _) h)
    simp [f0G, image_eq_zero_of_notMem_tsupport hz', dDir_eq_zero_of_notMem hz'']
  have hθm : ∀ i m, Continuous (chartTheta (T.pX (c i) (e i)) (hs i m)) := fun i m =>
    continuous_of_continuousOn_of_eq_zero' (T.isOpen_pieceDomain _ _)
      (continuousOn_chartTheta' (T.isOpen_pieceDomain _ _) (contDiffOn_pX _ _)
        (hsT i m).1.contDiffOn) (isClosed_tsupport _) ((hsD i m).trans (hDd i)) fun z hz =>
        chartTheta_eq_zero_of_eventuallyEq (eventuallyEq_zero_of_notMem_tsupport hz)
  have hθ0 : ∀ i m, ∀ z ∉ K i, chartTheta (T.pX (c i) (e i)) (hs i m) z = 0 := fun i m z hz =>
    chartTheta_eq_zero_of_eventuallyEq (eventuallyEq_zero_of_notMem_tsupport fun h =>
      hz ((hDK i) (hsD i m h)))
  have hθ0D : ∀ i m, ∀ z ∉ D i, chartTheta (T.pX (c i) (e i)) (hs i m) z = 0 := fun i m z hz =>
    chartTheta_eq_zero_of_eventuallyEq (eventuallyEq_zero_of_notMem_tsupport fun h =>
      hz (hsD i m h))
  have hf00D : ∀ i, ∀ z ∉ D i, f0G (chartFn (c i) (ζ i)) (T.WeX (c i) (e i) v)
      (chartTheta (T.pX (c i) (e i)) (F.tot (c i) (e i))) z = 0 := by
    intro i z hz
    have hz' : z ∉ tsupport (chartFn (c i) (ζ i)) := fun h => hz (hζD i h)
    have hz'' : z ∉ tsupport fun y => ((chartFn (c i) (ζ i) y : ℝ) : ℂ) := fun h =>
      hz' ((tsupport_comp_subset Complex.ofReal_zero _) h)
    simp [f0G, image_eq_zero_of_notMem_tsupport hz', dDir_eq_zero_of_notMem hz'']
  have hAp : ∀ i m, MemLp (T.ArX (c i) (e i) (chartTheta (T.pX (c i) (e i)) (hs i m))) 2 T.μ :=
    fun i m => memLp_of_chart_ArX (hKc i) (hKd i) ((hθm i m).memLp_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact (hKc i) fun z hz => by
        by_contra h; exact hz (hθ0 i m z h))) (hθm i m).measurable (hθ0 i m)
  have hAl : ∀ i, MemLp (T.ArX (c i) (e i) (f0G (chartFn (c i) (ζ i)) (T.WeX (c i) (e i) v)
      (chartTheta (T.pX (c i) (e i)) (F.tot (c i) (e i))))) 2 T.μ := fun i =>
    memLp_of_chart_ArX (hKc i) (hKd i) (hf0 i) (hf0m i) (hf00 i)
  have hAlim : MemLp (T.AlimX F χ v) 2 T.μ := by
    rw [show T.AlimX F χ v = fun x => ∑ i, T.ArX (c i) (e i)
      (f0G (chartFn (c i) (ζ i)) (T.WeX (c i) (e i) v)
        (chartTheta (T.pX (c i) (e i)) (F.tot (c i) (e i)))) x from funext hAeq]
    exact memLp_finsetSum _ fun i _ => hAl i
  -- the `S`-pieces
  have hσ : ∀ i m, ∀ z ∈ T.pieceDomain (c i) (e i),
      kahlerAntisym (gX T.omega T.r (c i) z) (Amat (hs i m) z) =
        sigmaDbarG (sigmaMatX T.omega T.r (c i)) (hs i m) z := fun i m z hz =>
    (sigmaDbarG_eq_kahlerAntisym T.isOpen_U T.kahler (T.isOpen_pieceDomain _ _)
      (T.pieceDomain_subset_chartSmooth _ _) (hsT i m).1.contDiffOn hz).symm
  have hβm : ∀ i m j k, Measurable fun z => sigmaDbarG (sigmaMatX T.omega T.r (c i)) (hs i m) z j k :=
    fun i m j k => measurable_of_continuousOn_of_eq_zero (T.isOpen_pieceDomain (c i) (e i))
      (continuousOn_sigmaDbarG (hsT i m).1 j k) fun z hz => by
        rw [sigmaDbarG_eq_zero fun h => hz ((hsD i m).trans (hDd i) h)]; rfl
  have hβ0 : ∀ i m, ∀ z ∉ K i, sigmaDbarG (sigmaMatX T.omega T.r (c i)) (hs i m) z = 0 :=
    fun i m z hz => sigmaDbarG_eq_zero fun h => hz ((hDK i) (hsD i m h))
  have hSp : ∀ i m, MemLp (T.SrX (c i) (e i)
      (sigmaDbarG (sigmaMatX T.omega T.r (c i)) (hs i m))) 2 T.μ := by
    intro i m
    refine memLp_of_chart_SrX (hKc i) (hKd i) ?_ (hβm i m) (hβ0 i m)
    have hcont : Continuous fun z => flat2 (sigmaDbarG (sigmaMatX T.omega T.r (c i)) (hs i m) z) :=
      continuous_flat2.comp (continuous_pi fun j => continuous_pi fun k =>
        continuous_of_continuousOn_of_eq_zero' (T.isOpen_pieceDomain (c i) (e i))
          (continuousOn_sigmaDbarG (hsT i m).1 j k) (isClosed_tsupport (hs i m))
          ((hsD i m).trans (hDd i)) fun z hz => by rw [sigmaDbarG_eq_zero hz]; rfl)
    exact hcont.memLp_of_hasCompactSupport (HasCompactSupport.of_support_subset_isCompact (hKc i)
      fun z hz => by by_contra h; exact hz (by show flat2 _ = 0; rw [hβ0 i m z h, flat2_zero]))
  have hfSm : ∀ i j k, Measurable fun z => (Matrix.of fun j k =>
      fSG (sigmaMatX T.omega T.r (c i)) (chartFn (c i) (ζ i)) (T.WeX (c i) (e i) v) j k z) j k :=
    fun i j k => by simpa using measurable_fSG (hζC i) (hζpd i) (hWm i) j k
  have hfS0 : ∀ i, ∀ z ∉ K i, (Matrix.of fun j k =>
      fSG (sigmaMatX T.omega T.r (c i)) (chartFn (c i) (ζ i)) (T.WeX (c i) (e i) v) j k z) = 0 := by
    intro i z hz
    have hz' : z ∉ tsupport fun y => ((chartFn (c i) (ζ i) y : ℝ) : ℂ) := fun h =>
      hz (hζK i ((tsupport_comp_subset Complex.ofReal_zero _) h))
    ext j k
    simp [fSG, dbarDir_eq_zero_of_notMem hz']
  have hβ0D : ∀ i m, ∀ z ∉ D i, sigmaDbarG (sigmaMatX T.omega T.r (c i)) (hs i m) z = 0 :=
    fun i m z hz => sigmaDbarG_eq_zero fun h => hz (hsD i m h)
  have hfS0D : ∀ i, ∀ z ∉ D i, (Matrix.of fun j k =>
      fSG (sigmaMatX T.omega T.r (c i)) (chartFn (c i) (ζ i)) (T.WeX (c i) (e i) v) j k z) = 0 := by
    intro i z hz
    have hz' : z ∉ tsupport fun y => ((chartFn (c i) (ζ i) y : ℝ) : ℂ) := fun h =>
      hz (hζD i ((tsupport_comp_subset Complex.ofReal_zero _) h))
    ext j k
    simp [fSG, dbarDir_eq_zero_of_notMem hz']
  have hSl : ∀ i, MemLp (T.SrX (c i) (e i) (fun z => Matrix.of fun j k =>
      fSG (sigmaMatX T.omega T.r (c i)) (chartFn (c i) (ζ i)) (T.WeX (c i) (e i) v) j k z)) 2 T.μ :=
    fun i => memLp_of_chart_SrX (hKc i) (hKd i) (memLp_flat2_of_entries fun j k => by
      simpa using hfS i j k) (hfSm i) (hfS0 i)
  have hSlim : MemLp (T.SlimX χ v) 2 T.μ := by
    rw [show T.SlimX χ v = fun x => ∑ i, T.SrX (c i) (e i) (fun z => Matrix.of fun j k =>
      fSG (sigmaMatX T.omega T.r (c i)) (chartFn (c i) (ζ i)) (T.WeX (c i) (e i) v) j k z) x from
        funext hSeq]
    exact memLp_finsetSum _ fun i _ => hSl i
  refine ⟨Fs, ?_, ?_, ?_, hAlim, hSlim⟩
  · -- the data pairing
    have hwm : ∀ i, Measurable (ofComps (wsysG (chartFn (c i) (ζ i)) (T.WeX (c i) (e i) v))) := by
      intro i
      have h1 : Measurable fun z => fun l => wsysG (chartFn (c i) (ζ i)) (T.WeX (c i) (e i) v) l z :=
        measurable_pi_lambda _ fun l => (Complex.measurable_ofReal.comp
          (hζC i).continuous.measurable).mul
          (((EuclideanSpace.proj l : ComplexModel n →L[ℂ] ℂ).continuous.measurable).comp (hWm i))
      exact (PiLp.continuous_toLp 2 _).measurable.comp h1
    have hwL : ∀ i, MemLp (T.repX (c i) (e i)
        (ofComps (wsysG (chartFn (c i) (ζ i)) (T.WeX (c i) (e i) v)))) 2 T.μ := by
      intro i
      rw [show T.repX (c i) (e i) (ofComps (wsysG (chartFn (c i) (ζ i)) (T.WeX (c i) (e i) v))) =
        fun x => ((ζ i x : ℝ) : ℂ) • v x from funext (repX_wsys (hζd i) v)]
      obtain ⟨M, -, hM⟩ := hζb i
      exact (Lp.memLp v).of_le_mul (c := M) ((hζm i).aestronglyMeasurable.smul
        (Lp.aestronglyMeasurable v)) (Eventually.of_forall fun x => by
          rw [norm_smul]; exact mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _))
    have hpiece : ∀ i m, IsLocalTestField T.L T.U (c i) (e i) (hs i m) := fun i m =>
      ⟨(hsT i m).1, (hsT i m).2, (hsD i m).trans (hDd i)⟩
    have hCrep : ∀ i, ∃ C : ℝ, ∀ h : ComplexModel n → ComplexModel n, Measurable h →
        (∀ z ∉ K i, h z = 0) →
        eLpNorm (T.repX (c i) (e i) h) 2 T.μ ≤ ENNReal.ofReal C * eLpNorm h 2 volume := fun i =>
      exists_eLpNorm_repX_le (T := T) (c i) (e i) (hKc i) (hKd i)
    choose Crep hCrep using hCrep
    have hR' : Tendsto (fun m => ∑ i, (memLp_pieceX (hpiece i m)).toLp
        (T.repX (c i) (e i) (hs i m))) atTop (𝓝 (∑ i, (hwL i).toLp _)) := by
      refine tendsto_finsetSum _ fun i _ => ?_
      refine tendsto_toLp_of_eLpNorm' (fun m => memLp_pieceX (hpiece i m)) (hwL i)
        (tendsto_zero_of_le_const_mul (C := Crep i) (hc1 i) fun m => ?_)
      have h1 : (fun x => T.repX (c i) (e i) (hs i m) x - T.repX (c i) (e i)
          (ofComps (wsysG (chartFn (c i) (ζ i)) (T.WeX (c i) (e i) v))) x) =
          T.repX (c i) (e i) (fun z => hs i m z -
            ofComps (wsysG (chartFn (c i) (ζ i)) (T.WeX (c i) (e i) v)) z) := by
        funext x; rw [repX_sub]
      rw [h1]
      refine hCrep i _ ((hsT i m).1.continuous.measurable.sub (hwm i)) fun z hz => ?_
      have h2 : hs i m z = 0 := image_eq_zero_of_notMem_tsupport fun h => hz ((hDK i) (hsD i m h))
      have h3 : ofComps (wsysG (chartFn (c i) (ζ i)) (T.WeX (c i) (e i) v)) z = 0 := by
        ext l
        simp [ofComps, wsysG, image_eq_zero_of_notMem_tsupport fun h => hz (hζK i h)]
      rw [h2, h3, sub_zero]
    have hR : Tendsto (fun m => repFamX (Fs m)) atTop (𝓝 (∑ i, (hwL i).toLp _)) := hR'
    have hl := (hR.inner (tendsto_const_nhds (x := memLp_yG.toLp T.yG))).congr
      fun m => inner_repFamX_yG (Fs m)
    convert hl using 2
    have hI : Integrable (fun x => ⟪v x, T.yG x⟫_ℂ) T.μ := by
      refine (L2.integrable_inner (𝕜 := ℂ) v (memLp_yG.toLp T.yG)).congr ?_
      filter_upwards [memLp_yG.coeFn_toLp] with x hx
      rw [hx]
    have hIi : ∀ i, Integrable (fun x => ((ζ i x : ℝ) : ℂ) * ⟪v x, T.yG x⟫_ℂ) T.μ := by
      intro i
      obtain ⟨M, -, hM⟩ := hζb i
      exact hI.bdd_mul (c := M) (hζm i).aestronglyMeasurable (Eventually.of_forall hM)
    have hterm : ∀ i, ⟪(hwL i).toLp _, memLp_yG.toLp T.yG⟫_ℂ =
        ∫ x, ((ζ i x : ℝ) : ℂ) * ⟪v x, T.yG x⟫_ℂ ∂T.μ := by
      intro i
      rw [inner_toLp_toLp']
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only
      rw [repX_wsys (hζd i), inner_smul_left, Complex.conj_ofReal]
    rw [sum_inner, Finset.sum_congr rfl fun i _ => hterm i,
      ← integral_finsetSum _ fun i _ => hIi i]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [← Finset.sum_mul, ← hsumC x]
  · -- the `T*`-energy
    have hAF : ∀ m, MemLp (T.AFX (Fs m)) 2 T.μ := fun m =>
      memLp_finsetSum _ fun i _ => hAp i m
    simp only [energy_eqX]
    refine tendsto_integral_norm_sq' hAF hAlim ?_
    refine tendsto_eLpNorm_sum'' Finset.univ (G := fun i m x =>
      T.ArX (c i) (e i) (chartTheta (T.pX (c i) (e i)) (hs i m)) x -
        T.ArX (c i) (e i) (f0G (chartFn (c i) (ζ i)) (T.WeX (c i) (e i) v)
          (chartTheta (T.pX (c i) (e i)) (F.tot (c i) (e i)))) x)
      (fun i m => (hAp i m).1.sub (hAl i).1) (fun m x => ?_) fun i _ => ?_
    · rw [hAeq]
      have hA : T.AFX (Fs m) x = ∑ i, T.ArX (c i) (e i)
          (chartTheta (T.pX (c i) (e i)) (hs i m)) x := rfl
      rw [hA, ← Finset.sum_sub_distrib]
      exact norm_sum_le _ _
    · obtain ⟨C, hC⟩ := exists_eLpNorm_ArX_le (T := T) (c i) (e i) (hKc i) (hKd i)
      refine tendsto_zero_of_le_const_mul (C := C) (hc2 i) fun m => ?_
      have h1 : (fun x => T.ArX (c i) (e i) (chartTheta (T.pX (c i) (e i)) (hs i m)) x -
          T.ArX (c i) (e i) (f0G (chartFn (c i) (ζ i)) (T.WeX (c i) (e i) v)
            (chartTheta (T.pX (c i) (e i)) (F.tot (c i) (e i)))) x) =
          T.ArX (c i) (e i) (fun z => chartTheta (T.pX (c i) (e i)) (hs i m) z -
            f0G (chartFn (c i) (ζ i)) (T.WeX (c i) (e i) v)
              (chartTheta (T.pX (c i) (e i)) (F.tot (c i) (e i))) z) := by
        funext x; rw [ArX_sub]
      rw [h1]
      refine (hC _ ((hθm i m).measurable.sub (hf0m i)) fun z hz => by
        have h1 := hθ0 i m z hz
        have h2 := hf00 i z hz
        simp [h1, h2]).trans (le_of_eq ?_)
      congr 1
      refine (eLpNorm_restrict_eq_of_support_subset fun z hz => ?_).symm
      by_contra h
      exact hz (by
        have h1 := hθ0D i m z h
        have h2 := hf00D i z h
        simp [h1, h2])
  · -- the `S`-energy
    have hSF : ∀ m, MemLp (T.SFX (Fs m)) 2 T.μ := by
      intro m
      have heq : T.SFX (Fs m) = fun x => ∑ i, T.SrX (c i) (e i)
          (sigmaDbarG (sigmaMatX T.omega T.r (c i)) (hs i m)) x := by
        funext x
        exact Finset.sum_congr rfl fun i _ => SrX_congr (hσ i m) x
      rw [heq]
      exact memLp_finsetSum _ fun i _ => hSp i m
    simp only [senergy_eqX, integral_const_mul]
    refine Tendsto.const_mul _ (tendsto_integral_norm_sq' hSF hSlim ?_)
    refine tendsto_eLpNorm_sum'' Finset.univ (G := fun i m x =>
      T.SrX (c i) (e i) (sigmaDbarG (sigmaMatX T.omega T.r (c i)) (hs i m)) x -
        T.SrX (c i) (e i) (fun z => Matrix.of fun j k => fSG (sigmaMatX T.omega T.r (c i))
          (chartFn (c i) (ζ i)) (T.WeX (c i) (e i) v) j k z) x)
      (fun i m => (hSp i m).1.sub (hSl i).1) (fun m x => ?_) fun i _ => ?_
    · rw [hSeq]
      have hS : T.SFX (Fs m) x = ∑ i, T.SrX (c i) (e i)
          (sigmaDbarG (sigmaMatX T.omega T.r (c i)) (hs i m)) x :=
        Finset.sum_congr rfl fun i _ => SrX_congr (hσ i m) x
      rw [hS, ← Finset.sum_sub_distrib]
      exact norm_sum_le _ _
    · obtain ⟨C, hC⟩ := exists_eLpNorm_SrX_le (T := T) (c i) (e i) (hKc i) (hKd i)
      have hG : Tendsto (fun m => eLpNorm (fun z => flat2
          (sigmaDbarG (sigmaMatX T.omega T.r (c i)) (hs i m) z - Matrix.of fun j k =>
            fSG (sigmaMatX T.omega T.r (c i)) (chartFn (c i) (ζ i)) (T.WeX (c i) (e i) v) j k z))
          2 volume) atTop (𝓝 0) := by
        refine tendsto_eLpNorm_sum'' (μ := volume) Finset.univ (G := fun (p : Fin n × Fin n) m z =>
          sigmaDbarG (sigmaMatX T.omega T.r (c i)) (hs i m) z p.1 p.2 -
            fSG (sigmaMatX T.omega T.r (c i)) (chartFn (c i) (ζ i)) (T.WeX (c i) (e i) v) p.1 p.2 z)
          (fun p m => ((hβm i m p.1 p.2).sub
            (measurable_fSG (hζC i) (hζpd i) (hWm i) p.1 p.2)).aestronglyMeasurable)
          (fun m z => ?_) fun p _ => ?_
        · refine (norm_flat2_le_sum _).trans (le_of_eq ?_)
          simp [Matrix.sub_apply]
        · refine (hc3 i p.1 p.2).congr fun m => ?_
          refine eLpNorm_restrict_eq_of_support_subset fun z hz => ?_
          by_contra h'
          exact hz (by
            have h1 := hβ0D i m z h'
            have h2 := congrFun (congrFun (hfS0D i z h') p.1) p.2
            simp only [of_apply, Matrix.zero_apply] at h2
            simp [h1, h2])
      refine tendsto_zero_of_le_const_mul (C := C) hG fun m => ?_
      have h1 : (fun x => T.SrX (c i) (e i) (sigmaDbarG (sigmaMatX T.omega T.r (c i)) (hs i m)) x -
          T.SrX (c i) (e i) (fun z => Matrix.of fun j k => fSG (sigmaMatX T.omega T.r (c i))
            (chartFn (c i) (ζ i)) (T.WeX (c i) (e i) v) j k z) x) =
          T.SrX (c i) (e i) (fun z => sigmaDbarG (sigmaMatX T.omega T.r (c i)) (hs i m) z -
            Matrix.of fun j k => fSG (sigmaMatX T.omega T.r (c i)) (chartFn (c i) (ζ i))
              (T.WeX (c i) (e i) v) j k z) := by
        funext x; rw [SrX_sub]
      rw [h1]
      refine hC _ (fun a b => by
          have h := (hβm i m a b).sub (hfSm i a b)
          simp only [of_apply] at h
          exact h)
        fun z hz => by rw [hβ0 i m z hz, hfS0 i z hz, sub_zero]

/-! ### Letting the cut-off tend to `1` -/

theorem AlimX_sub_AFX (F : T.XFam) (χ : X → ℝ) (v : X → ComplexModel n) (x : X) :
    T.AlimX F χ v x - T.AFX F x = ((χ x : ℂ) - 1) * T.AFX F x -
      T.U.indicator (fun x => ((Real.sqrt (T.a x + T.b x) : ℝ) : ℂ) * ⟪T.dRX χ x, v x⟫_ℂ) x := by
  by_cases hx : x ∈ T.U
  · rw [AlimX, AFX_eq, indicator_of_mem hx, indicator_of_mem hx, indicator_of_mem hx]; ring
  · simp [AlimX, AFX_eq, indicator_of_notMem hx]

theorem norm_dRX_le {χ : X → ℝ} (hχ : ChartSmooth (n := n) χ) {C : ℝ}
    (hC : ∀ (c : ComplexChart n X), ∀ z ∈ c.val.target, c.val.symm z ∈ T.U →
      ∀ v : ComplexModel n, fderiv ℝ (fun y => χ (c.val.symm y)) z v ^ 2 ≤
        C ^ 2 * modifiedKahlerQuad T.omega T.r c z v) (x : X) :
    ‖T.dRX χ x‖ ≤ |C| := by
  have h1 := norm_dRX_sq_le hχ hC x
  have : ‖T.dRX χ x‖ ^ 2 ≤ |C| ^ 2 := by rw [sq_abs]; nlinarith [sq_nonneg C]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (abs_nonneg C) two_ne_zero).mp this

theorem norm_cut_tstar_leX {χ : X → ℝ} (hχ : ChartSmooth (n := n) χ) {C : ℝ}
    (hC : ∀ (c : ComplexChart n X), ∀ z ∈ c.val.target, c.val.symm z ∈ T.U →
      ∀ v : ComplexModel n, fderiv ℝ (fun y => χ (c.val.symm y)) z v ^ 2 ≤
        C ^ 2 * modifiedKahlerQuad T.omega T.r c z v) {M : ℝ}
    (hM : ∀ x ∈ T.U, T.a x + T.b x ≤ 2 * M) (v : X → ComplexModel n) (x : X) :
    ‖T.U.indicator (fun x => ((Real.sqrt (T.a x + T.b x) : ℝ) : ℂ) * ⟪T.dRX χ x, v x⟫_ℂ) x‖ ≤
      Real.sqrt (2 * M) * |C| * ‖v x‖ := by
  by_cases hx : x ∈ T.U
  · rw [indicator_of_mem hx, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    have h2 := norm_dRX_le hχ hC x
    have h3 := norm_inner_le_norm (𝕜 := ℂ) (T.dRX χ x) (v x)
    have h4 : Real.sqrt (T.a x + T.b x) ≤ Real.sqrt (2 * M) := Real.sqrt_le_sqrt (hM x hx)
    calc Real.sqrt (T.a x + T.b x) * ‖⟪T.dRX χ x, v x⟫_ℂ‖
        ≤ Real.sqrt (2 * M) * (|C| * ‖v x‖) :=
          mul_le_mul h4 (h3.trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))) (norm_nonneg _)
            (Real.sqrt_nonneg _)
      _ = _ := by ring
  · rw [indicator_of_notMem hx, norm_zero]; positivity

theorem norm_SlimX_le {χ : X → ℝ} (hχ : ChartSmooth (n := n) χ) {C : ℝ}
    (hC : ∀ (c : ComplexChart n X), ∀ z ∈ c.val.target, c.val.symm z ∈ T.U →
      ∀ v : ComplexModel n, fderiv ℝ (fun y => χ (c.val.symm y)) z v ^ 2 ≤
        C ^ 2 * modifiedKahlerQuad T.omega T.r c z v) (v : X → ComplexModel n) (x : X) :
    ‖T.SlimX χ v x‖ ≤ 2 * |C| * ‖v x‖ := by
  rw [SlimX]
  refine (norm_flat2_wedge_le _ _).trans ?_
  have h2 := norm_dRX_le hχ hC x
  nlinarith [norm_nonneg (v x), norm_nonneg (T.dRX χ x)]

theorem memLp_AFX (F : T.XFam) : MemLp (T.AFX F) 2 T.μ := by
  refine memLp_finsetSum _ fun i _ => ?_
  have hθ0 : ∀ z ∉ tsupport (F.h i), chartTheta (T.pX (F.c i) (F.e i)) (F.h i) z = 0 :=
    fun z hz => chartTheta_eq_zero_of_eventuallyEq (eventuallyEq_zero_of_notMem_tsupport hz)
  have hθc : Continuous (chartTheta (T.pX (F.c i) (F.e i)) (F.h i)) :=
    continuous_of_continuousOn_of_eq_zero' (T.isOpen_pieceDomain _ _)
      (continuousOn_chartTheta' (T.isOpen_pieceDomain _ _) (contDiffOn_pX _ _)
        (F.spec i).1.contDiffOn) (isClosed_tsupport _) (F.spec i).2.2 hθ0
  exact memLp_of_chart_ArX (F.spec i).2.1 (F.spec i).2.2 (hθc.memLp_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact (F.spec i).2.1 fun z hz => by
      by_contra h; exact hz (hθ0 z h))) hθc.measurable hθ0

/-- **The density lemma on a complex manifold** (`claude-tl2-man2:main`,
`claude-tl2-man:sigma-density`): every twisted datum on `X` satisfies `SigmaGraphDensityX`. -/
theorem sigmaGraphDensityX (T : TwistedDatum n X) : T.SigmaGraphDensityX := by
  intro F ε hε
  obtain ⟨v, hW1, hW2, hW3⟩ := exists_vX F
  obtain ⟨χ, C, hχ, hχc, hχU, hχ01, hχlim, hχd⟩ := T.complete
  obtain ⟨mm, M, -, hb⟩ := T.bounds
  have hM : ∀ x ∈ T.U, T.a x + T.b x ≤ 2 * M := fun x hx => by
    linarith [(hb x hx).2.1, (hb x hx).2.2.2]
  set c : ℕ → ℝ := fun k => C / ((k : ℝ) + 1) with hc_def
  have hc0 : Tendsto c atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul C
    simpa [hc_def, div_eq_mul_inv] using this
  have hca : Tendsto (fun k => |c k|) atTop (𝓝 0) := by simpa using hc0.abs
  have hlev := fun k => exists_levelX F v hW1 hW2 (hχ k) (hχc k) (hχU k)
  have hAl : ∀ k, MemLp (T.AlimX F (χ k) v) 2 T.μ := fun k => (hlev k).choose_spec.2.2.2.1
  have hSl : ∀ k, MemLp (T.SlimX (χ k) v) 2 T.μ := fun k => (hlev k).choose_spec.2.2.2.2
  have hχb : ∀ k x, ‖((χ k x : ℝ) : ℂ)‖ ≤ 1 := fun k x => by
    rw [Complex.norm_real, Real.norm_of_nonneg (hχ01 k x).1]; exact (hχ01 k x).2
  have hχm : ∀ k, Continuous fun x => ((χ k x : ℝ) : ℂ) := fun k =>
    Complex.continuous_ofReal.comp (continuous_of_chartSmooth (hχ k))
  -- the data pairings
  have hI : Integrable (fun x => ⟪v x, T.yG x⟫_ℂ) T.μ := by
    refine (L2.integrable_inner (𝕜 := ℂ) v (memLp_yG.toLp T.yG)).congr ?_
    filter_upwards [memLp_yG.coeFn_toLp] with x hx
    rw [hx]
  have hdk : Tendsto (fun k => ∫ x, (χ k x : ℂ) * ⟪v x, T.yG x⟫_ℂ ∂T.μ) atTop (𝓝 F.data) := by
    rw [← hW3, inner_toLp_right']
    refine tendsto_integral_of_dominated_convergence (fun x => ‖⟪v x, T.yG x⟫_ℂ‖)
      (fun k => (hχm k).aestronglyMeasurable.mul hI.1) hI.norm
      (fun k => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hχb k x)
    · by_cases hx : x ∈ T.U
      · have := ((Complex.continuous_ofReal.tendsto _).comp (hχlim x hx)).mul_const
          (⟪v x, T.yG x⟫_ℂ)
        simpa using this
      · have h0 : T.yG x = 0 := by simp [yG, indicator_of_notMem hx]
        simp [h0]
  -- the `T*`-energies
  have hek : Tendsto (fun k => ∫ x, ‖T.AlimX F (χ k) v x‖ ^ 2 ∂T.μ) atTop (𝓝 F.energy) := by
    rw [energy_eqX F]
    refine tendsto_integral_norm_sq' hAl (memLp_AFX F) ?_
    have hAFm := memLp_AFX F
    have hm : ∀ k, MemLp (fun x => ((χ k x : ℂ) - 1) * T.AFX F x) 2 T.μ := fun k =>
      hAFm.of_le_mul (c := 2) ((((hχm k).sub continuous_const).aestronglyMeasurable).mul hAFm.1)
        (Eventually.of_forall fun x => by
          rw [norm_mul]
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          exact (norm_sub_le _ _).trans (by linarith [hχb k x, norm_one (α := ℂ)]))
    have h1 : Tendsto (fun k => eLpNorm (fun x => ((χ k x : ℂ) - 1) * T.AFX F x) 2 T.μ)
        atTop (𝓝 0) := by
      refine tendsto_eLpNorm_of_integral' hm ?_
      have hInt : Integrable (fun x => 4 * ‖T.AFX F x‖ ^ 2) T.μ :=
        (hAFm.integrable_norm_rpow two_ne_zero ENNReal.ofNat_ne_top |>.congr
          (Eventually.of_forall fun x => by simp)).const_mul 4
      have := tendsto_integral_of_dominated_convergence (fun x => 4 * ‖T.AFX F x‖ ^ 2)
        (F := fun k x => ‖((χ k x : ℂ) - 1) * T.AFX F x‖ ^ 2) (f := fun _ => (0 : ℝ))
        (fun k => ((hm k).1.norm).pow 2) hInt (fun k => Eventually.of_forall fun x => ?_)
        (Eventually.of_forall fun x => ?_)
      · simpa using this
      · rw [Real.norm_of_nonneg (sq_nonneg _), norm_mul, mul_pow]
        have : ‖((χ k x : ℂ) - 1)‖ ^ 2 ≤ 4 := by
          have h := (norm_sub_le ((χ k x : ℂ)) 1).trans
            (by linarith [hχb k x, norm_one (α := ℂ)] : ‖((χ k x : ℂ))‖ + ‖(1 : ℂ)‖ ≤ 2)
          nlinarith [norm_nonneg ((χ k x : ℂ) - 1)]
        exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
      · by_cases hx : x ∈ T.U
        · have h2 : Tendsto (fun k => ((χ k x : ℂ) - 1)) atTop (𝓝 0) := by
            have := ((Complex.continuous_ofReal.tendsto _).comp (hχlim x hx)).sub_const 1
            simpa using this
          have := ((h2.mul_const (T.AFX F x)).norm).pow 2
          simpa using this
        · have h0 : T.AFX F x = 0 := by
            rw [AFX_eq]; simp [indicator_of_notMem hx]
          simp [h0]
    have h2 : Tendsto (fun k => ENNReal.ofReal (Real.sqrt (2 * M) * |c k|) * eLpNorm v 2 T.μ)
        atTop (𝓝 0) := by
      have h3 : Tendsto (fun k => ENNReal.ofReal (Real.sqrt (2 * M) * |c k|)) atTop (𝓝 0) := by
        have := ENNReal.tendsto_ofReal (hca.const_mul (Real.sqrt (2 * M)))
        simpa using this
      have := ENNReal.Tendsto.mul_const h3 (Or.inr (Lp.eLpNorm_ne_top v))
      simpa using this
    have h12 := h1.add h2
    rw [add_zero] at h12
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h12
      (fun _ => by positivity) fun k => ?_
    have hpt : ∀ x, ‖T.AlimX F (χ k) v x - T.AFX F x‖ ≤
        ‖((χ k x : ℂ) - 1) * T.AFX F x‖ + Real.sqrt (2 * M) * |c k| * ‖v x‖ := by
      intro x
      rw [AlimX_sub_AFX]
      exact (norm_sub_le _ _).trans (add_le_add le_rfl
        (norm_cut_tstar_leX (hχ k) (hχd k) hM v x))
    refine (eLpNorm_mono_real hpt).trans ?_
    refine (eLpNorm_add_le (hm k).1.norm
      ((Lp.aestronglyMeasurable v).norm.const_mul _) (by norm_num)).trans (add_le_add ?_ ?_)
    · exact le_of_eq (eLpNorm_norm _)
    · refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Eventually.of_forall fun x => ?_) 2
      rw [Real.norm_of_nonneg (by positivity)]
  -- the `S`-energies
  have hsk : Tendsto (fun k => (1 / 2 : ℝ) * ∫ x, ‖T.SlimX (χ k) v x‖ ^ 2 ∂T.μ) atTop (𝓝 0) := by
    have hle : ∀ k, (1 / 2 : ℝ) * ∫ x, ‖T.SlimX (χ k) v x‖ ^ 2 ∂T.μ ≤
        (1 / 2 : ℝ) * (2 * |c k| * ‖v‖) ^ 2 := by
      intro k
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      rw [integral_norm_sq_eq' (hSl k), Lp.norm_toLp]
      have hb : eLpNorm (T.SlimX (χ k) v) 2 T.μ ≤
          ENNReal.ofReal (2 * |c k|) * eLpNorm v 2 T.μ :=
        eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Eventually.of_forall fun x =>
          norm_SlimX_le (hχ k) (hχd k) v x) 2
      have hb' : (eLpNorm (T.SlimX (χ k) v) 2 T.μ).toReal ≤ 2 * |c k| * ‖v‖ := by
        rw [Lp.norm_def, ← ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 * |c k|),
          ← ENNReal.toReal_mul]
        exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (Lp.eLpNorm_ne_top v)) hb
      exact pow_le_pow_left₀ ENNReal.toReal_nonneg hb' 2
    have hlim : Tendsto (fun k => (1 / 2 : ℝ) * (2 * |c k| * ‖v‖) ^ 2) atTop (𝓝 0) := by
      have := ((hca.const_mul 2).mul_const ‖v‖).pow 2 |>.const_mul (1 / 2 : ℝ)
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun k => ?_) hle
    exact mul_nonneg (by norm_num) (integral_nonneg fun x => sq_nonneg _)
  -- the diagonal choice
  have hε2 : 0 < ε / 2 := half_pos hε
  obtain ⟨k, hk1, hk2, hk3⟩ := ((hdk.eventually (Metric.ball_mem_nhds _ hε2)).and
    ((hek.eventually (Iio_mem_nhds (by linarith : F.energy < F.energy + ε / 2))).and
      (hsk.eventually (Iio_mem_nhds hε2)))).exists
  obtain ⟨Fs, h1, h2, h3, -, -⟩ := hlev k
  obtain ⟨m, hm1, hm2, hm3⟩ := ((h1.eventually (Metric.ball_mem_nhds _ hε2)).and
    ((h2.eventually (Iio_mem_nhds (lt_add_of_pos_right _ hε2))).and
      (h3.eventually (Iio_mem_nhds (lt_add_of_pos_right _ hε2))))).exists
  replace hk1 := Metric.mem_ball.mp hk1
  replace hm1 := Metric.mem_ball.mp hm1
  refine ⟨Fs m, ?_, by linarith, by linarith⟩
  have := dist_triangle ((Fs m).data) (∫ x, (χ k x : ℂ) * ⟪v x, T.yG x⟫_ℂ ∂T.μ) F.data
  rw [← dist_eq_norm]
  linarith

end TwistedDatum

variable (n X)

/-- **The functional bound of the twisted `L²` estimate on a complex manifold**
(`claude-tl2-man2:main`). -/
theorem twistedFunctionalBoundStatement_manifold : TwistedFunctionalBoundStatement n X :=
  twistedFunctionalBoundStatement_of_graphDensityX n X fun T =>
    TwistedDatum.graphDensityX_of_sigmaGraphDensityX (TwistedDatum.sigmaGraphDensityX T)

/-- **The main twisted `L²` estimate on a complex manifold** (`claude-twisted-l2:main`;
FPT `lem:twisted-kahler-line-estimate`): `TwistedL2CorrectionStatement n X` for every complex
manifold `X`. -/
theorem twistedL2CorrectionStatement_manifold : TwistedL2CorrectionStatement n X :=
  twistedL2CorrectionStatement_of_sigmaGraphDensityX n X TwistedDatum.sigmaGraphDensityX

/-- **The compact singular twisted `L²` estimate on a complex manifold**
(`claude-twisted-l2:compact`). -/
theorem compactTwistedL2CorrectionStatement_manifold : CompactTwistedL2CorrectionStatement n X :=
  compactTwistedL2CorrectionStatement_of_sigmaGraphDensityX n X TwistedDatum.sigmaGraphDensityX

end SGPT.Trace.TwistedL2
