import SGPT.Currents.AnalyticSupportGraph
import SGPT.Siu.LocalDivisorBound
import SGPT.Foundations.Analysis.Pending.DivisorSingularProjection

/-!
# The local support theorem: comparison of two potentials across a hypersurface

Let `u₁, u₂` be plurisubharmonic on an open set `Ω ⊆ ℂⁿ` and let `A ⊆ Ω` be contained in the
zero set of a holomorphic function `g` vanishing identically near no point.  Suppose that
`u₁ = u₂ + h` off `A`, with `h` pluriharmonic (continuous, `h` and `-h` plurisubharmonic) on
`Ω \ A`.  This is the local form of two closed positive `(1,1)`-currents `ddᶜu₁`, `ddᶜu₂` that
agree off `A`.

The analytic content of the support theorem (Xia, *Foundations of pluripotential theory*,
`thm:analytic-order-zero-support`) is that `h` is locally bounded above near `A` as soon as
`u₂` has no logarithmic pole along any hypersurface piece of `A`
(`SparseLogPoles`): then `h` extends plurisubharmonically across `A`, i.e. `ddᶜu₁ ≥ ddᶜu₂`.

* `exists_nhds_le_of_regularPresentation` (**regular points**): near a regular point `y` of
  the divisor of `g` (transverse to a direction `u₀`), the zero set is a holomorphic graph and
  the transverse decomposition `h = c(w) log |t| + O(1)` holds
  (`exists_log_bound_on_graph`).  If `c(w₁) < 0`, then `h → +∞` at the graph points over a
  neighbourhood of `w₁`, so these lie in `A`, and `u₂ = u₁ - h ≤ a log |t| + C` there: `u₂`
  has a logarithmic pole of order `a = -c(w₁)/2` at every point of an open piece of the
  hypersurface `A`, which `SparseLogPoles` excludes.  Hence `c ≥ 0` and `h ≤ C`.
* `exists_nhds_le_of_eq_add` (**all points**): slicing by the complex lines parallel to `u₀`;
  almost every line meets the zero set of `g` only at transverse regular points
  (`DivisorSingularProjection.measure_image_bad_eq_zero`), where the first step bounds `h`;
  the maximum principle with removable zeros on each line (`le_on_closedBall_of_removable`)
  bounds `h` on the line by its values on a circle off the zero set.  This is the argument of
  `SGPT.Siu.LocalDivisorBound`, with `u - c log |g|²` replaced by `h`.  No information on the
  singular points of `A` is needed.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ENNReal InnerProductSpace

namespace SGPT.Currents.AnalyticSupport

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DivisorRegularLocus

/-- **No logarithmic poles along hypersurface pieces.**  At every point `z ∈ A` which is a
regular point of the divisor of `g` and near which `A` contains the zero set of `g`, and for
every order `a > 0`, points of `A` at which `u` has no logarithmic pole of order `a` accumulate
at `z`.  (For a local potential `u` of a closed positive current with vanishing generic Lelong
numbers along the prime divisors contained in `A`, this holds by Siu's semicontinuity theorem.) -/
def SparseLogPoles {n : ℕ} (u : EuclideanSpace ℂ (Fin n) → EReal)
    (g : EuclideanSpace ℂ (Fin n) → ℂ) (A : Set (EuclideanSpace ℂ (Fin n))) : Prop :=
  ∀ z ∈ A, Nonempty (RegularPresentation g z) → (∀ᶠ z' in 𝓝 z, g z' = 0 → z' ∈ A) →
    ∀ a : ℝ, 0 < a → ∀ O ∈ 𝓝 z, ∃ z' ∈ O ∩ A, ∀ C : ℝ,
      ¬ ∀ᶠ ζ in 𝓝[≠] z', u ζ ≤ ((a * Real.log ‖ζ - z'‖ + C : ℝ) : EReal)

section Transverse

variable {n k : ℕ} {u0 : EuclideanSpace ℂ (Fin n)} (S : Splitting u0 (EuclideanSpace ℂ (Fin k)))

local notation "V" => EuclideanSpace ℂ (Fin n)
local notation "W" => EuclideanSpace ℂ (Fin k)

/-- The transverse coordinate of `ζ` with respect to the graph of `kf`. -/
def transCoord (kf : W → ℂ) (ζ : V) : ℂ := ⟪u0, ζ⟫_ℂ - kf (S.π ζ)

theorem graphBase_add_transCoord (kf : W → ℂ) (ζ : V) :
    graphBase S kf (S.π ζ) + transCoord S kf ζ • u0 = ζ := by
  unfold graphBase transCoord
  conv_rhs => rw [S.decomp ζ]
  rw [sub_smul]
  abel

theorem graphBase_add_eq (kf : W → ℂ) (w : W) (t : ℂ) :
    graphBase S kf w + t • u0 = (kf w + t) • u0 + S.ι w := by
  unfold graphBase; rw [add_smul]; abel

theorem π_graphBase_add (kf : W → ℂ) (w : W) (t : ℂ) :
    S.π (graphBase S kf w + t • u0) = w := by
  rw [graphBase_add_eq, S.π_smul_add]

theorem transCoord_graphBase_add (hu0 : ‖u0‖ = 1) (kf : W → ℂ) (w : W) (t : ℂ) :
    transCoord S kf (graphBase S kf w + t • u0) = t := by
  unfold transCoord
  rw [π_graphBase_add, graphBase_add_eq, S.inner_smul_add hu0]
  ring

theorem continuousOn_transCoord {kf : W → ℂ} {s : Set W} (hkf : ContinuousOn kf s) :
    ContinuousOn (transCoord S kf) (S.π ⁻¹' s) :=
  ((innerSL ℂ u0).continuous.continuousOn).sub
    (hkf.comp S.π.continuous.continuousOn (fun _ h => h))

include S in
/-- **The regular-point step.** -/
theorem exists_nhds_le_of_regularPresentation (hu0 : ‖u0‖ = 1) {Ω : Set V} (hΩ : IsOpen Ω)
    {u₁ u₂ : V → EReal} (hu₁ : PlurisubharmonicOn u₁ Ω) (hu₂ : PlurisubharmonicOn u₂ Ω)
    (hi₁ : LocallyIntegrableOn (fun z => (u₁ z).toReal) Ω volume)
    (hi₂ : LocallyIntegrableOn (fun z => (u₂ z).toReal) Ω volume)
    (hf₁ : ∀ᵐ z ∂volume.restrict Ω, u₁ z ≠ ⊥) (hf₂ : ∀ᵐ z ∂volume.restrict Ω, u₂ z ≠ ⊥)
    {g : V → ℂ} (hg : DifferentiableOn ℂ g Ω) (hg0 : ∀ y ∈ Ω, ∃ᶠ z in 𝓝 y, g z ≠ 0)
    {A : Set V} (hAg : ∀ z ∈ A, g z = 0) (hAo : IsOpen (Ω \ A))
    {h : V → ℝ} (hhc : ContinuousOn h (Ω \ A))
    (hhp : PlurisubharmonicOn (fun z => (h z : EReal)) (Ω \ A))
    (hhn : PlurisubharmonicOn (fun z => ((-h z : ℝ) : EReal)) (Ω \ A))
    (heq : ∀ z ∈ Ω \ A, u₁ z = u₂ z + (h z : EReal))
    (hsp : SparseLogPoles u₂ g A)
    {y : V} (hy : y ∈ Ω) (P : RegularPresentation g y) (hyu : fderiv ℂ P.h y u0 ≠ 0) :
    ∃ U ∈ 𝓝 y, ∃ C : ℝ, ∀ z ∈ U, z ∈ Ω \ A → h z ≤ C := by
  classical
  obtain ⟨N, Wd, kf, hNo, hyN, hNU, -, hWo, hyW, hkf, hgraph, hzero, -⟩ :=
    P.exists_graph_slices hu0 S hyu
  obtain ⟨wy, hwydef⟩ : ∃ wy : W, wy = S.π y := ⟨_, rfl⟩
  have hzero' : ∀ (w : W) (t : ℂ), graphBase S kf w + t • u0 ∈ N →
      (g (graphBase S kf w + t • u0) = 0 ↔ w ∈ Wd ∧ t = 0) := by
    intro w t hm
    rw [graphBase_add_eq] at hm ⊢
    rw [hzero w (kf w + t) hm]
    constructor
    · rintro ⟨hw, h⟩; exact ⟨hw, by linear_combination h⟩
    · rintro ⟨hw, rfl⟩; exact ⟨hw, by simp⟩
  have hgraph0 : ∀ w ∈ Wd, g (graphBase S kf w) = 0 := by
    intro w hw
    obtain ⟨hm, hP⟩ := hgraph w hw
    exact (P.g_eq_zero_iff (hNU hm)).mpr hP
  have hgb : graphBase S kf wy = y := by
    rw [hwydef]
    have hdec := graphBase_add_transCoord S kf y
    have hm : graphBase S kf (S.π y) + transCoord S kf y • u0 ∈ N := by rw [hdec]; exact hyN
    have h0 := ((hzero' _ _ hm).mp (by rw [hdec]; exact P.g_x)).2
    rw [h0, zero_smul, add_zero] at hdec
    exact hdec
  -- the tube
  have hyW' : wy ∈ Wd := by rw [hwydef]; exact hyW
  have hkfc : ContinuousAt kf wy := (hkf.differentiableAt (hWo.mem_nhds hyW')).continuousAt
  have hcont : ContinuousAt (fun p : W × ℂ => graphBase S kf p.1 + p.2 • u0) (wy, 0) := by
    have h1 : ContinuousAt (fun p : W × ℂ => kf p.1) (wy, 0) :=
      hkfc.comp continuous_fst.continuousAt
    exact ((h1.smul continuousAt_const).add (S.ι.continuous.comp continuous_fst).continuousAt).add
      (continuous_snd.smul continuous_const).continuousAt
  have hNΩ : N ∩ Ω ∈ 𝓝 (graphBase S kf (wy, (0 : ℂ)).1 + (wy, (0 : ℂ)).2 • u0) := by
    simp only [zero_smul, add_zero, hgb]
    exact inter_mem (hNo.mem_nhds hyN) (hΩ.mem_nhds hy)
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (hcont.preimage_mem_nhds hNΩ)
  obtain ⟨ε', hε', hε'sub⟩ := Metric.isOpen_iff.mp hWo wy hyW'
  set δ : ℝ := min (ε / 2) (ε' / 2) with hδdef
  set R : ℝ := min (ε / 2) (1 / 2) with hRdef
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hR : 0 < R := lt_min (by positivity) (by norm_num)
  have hR1 : R ≤ 1 / 2 := min_le_right _ _
  have htube : ∀ w ∈ closedBall wy δ, ∀ t ∈ closedBall (0 : ℂ) R,
      graphBase S kf w + t • u0 ∈ N ∩ Ω := by
    intro w hw t ht
    have hmem : (w, t) ∈ ball (wy, (0 : ℂ)) ε := by
      rw [mem_ball, Prod.dist_eq, max_lt_iff]
      constructor
      · exact (mem_closedBall.mp hw).trans_lt ((min_le_left _ _).trans_lt (by linarith))
      · exact (mem_closedBall.mp ht).trans_lt ((min_le_left _ _).trans_lt (by linarith))
    have h := hεsub hmem
    rw [mem_preimage] at h
    exact h
  have hδW : closedBall wy δ ⊆ Wd :=
    (closedBall_subset_ball ((min_le_right _ _).trans_lt (by linarith))).trans hε'sub
  have hkfB : ContinuousOn kf (closedBall wy δ) := hkf.continuousOn.mono hδW
  have hoff : ∀ w ∈ closedBall wy δ, ∀ t ∈ closedBall (0 : ℂ) R, t ≠ 0 →
      graphBase S kf w + t • u0 ∉ A := by
    intro w hw t ht ht0 hA
    exact ht0 ((hzero' w t (htube w hw t ht).1).mp (hAg _ hA)).2
  obtain ⟨c, hcc, C₀, hbd⟩ := exists_log_bound_on_graph S hu0 hΩ hu₁ hu₂ hi₁ hi₂ hf₁ hf₂ hAo
    hhc hhp hhn heq hR hkfB (fun w hw t ht => (htube w hw t ht).2) hoff
  have hlog0 : ∀ t : ℂ, ‖t‖ ≤ R / 2 → Real.log ‖t‖ ≤ 0 := fun t htR =>
    Real.log_nonpos (norm_nonneg _) (by linarith)
  -- a bound for `u₁` on the tube
  have hKc : IsCompact ((fun p : W × ℂ => graphBase S kf p.1 + p.2 • u0) ''
      (closedBall wy δ ×ˢ closedBall 0 R)) :=
    ((isCompact_closedBall wy δ).prod (isCompact_closedBall 0 R)).image_of_continuousOn
      ((continuousOn_graphLine S hkfB).mono (prod_mono subset_rfl (subset_univ _)))
  obtain ⟨B₁, hB₁⟩ := SGPT.Siu.PlurisubharmonicOn.exists_real_bound_of_isCompact hu₁ hKc
    (by rintro _ ⟨p, hp, rfl⟩; exact (htube p.1 hp.1 p.2 hp.2).2)
  have hcontTC : ContinuousOn (transCoord S kf) (S.π ⁻¹' ball wy δ) :=
    continuousOn_transCoord S (hkfB.mono ball_subset_closedBall)
  -- the transverse coordinate is small near graph points
  have htc_ev : ∀ w ∈ ball wy δ, ∀ r > 0,
      ∀ᶠ ζ in 𝓝 (graphBase S kf w), S.π ζ ∈ ball wy δ ∧ ‖transCoord S kf ζ‖ < r := by
    intro w hw r hr
    have hπ : S.π (graphBase S kf w) = w := by simpa using π_graphBase_add S kf w 0
    have hmem : graphBase S kf w ∈ S.π ⁻¹' ball wy δ := by rw [mem_preimage, hπ]; exact hw
    have hopen : IsOpen (S.π ⁻¹' ball wy δ) := isOpen_ball.preimage S.π.continuous
    have htc : transCoord S kf (graphBase S kf w) = 0 := by
      simpa using transCoord_graphBase_add S hu0 kf w 0
    have h1 := (hcontTC.continuousAt (hopen.mem_nhds hmem)).eventually
      (ball_mem_nhds (transCoord S kf (graphBase S kf w)) hr)
    filter_upwards [h1, hopen.mem_nhds hmem] with ζ hζ hζ'
    refine ⟨hζ', ?_⟩
    rw [htc] at hζ
    rwa [dist_zero_right] at hζ
  -- **the coefficient is nonnegative**
  have hcpos : ∀ w ∈ ball wy δ, 0 ≤ c w := by
    intro w₁ hw₁
    by_contra hneg
    push Not at hneg
    set a : ℝ := -c w₁ / 2 with hadef
    have ha : 0 < a := by linarith
    have hcev : ∀ᶠ w in 𝓝 w₁, w ∈ ball wy δ ∧ c w < -a := by
      have hcat : ContinuousAt c w₁ :=
        hcc.continuousAt (mem_of_superset (isOpen_ball.mem_nhds hw₁) ball_subset_closedBall)
      filter_upwards [isOpen_ball.mem_nhds hw₁,
        hcat.eventually (gt_mem_nhds (show c w₁ < -a by linarith))] with w h1 h2
      exact ⟨h1, h2⟩
    obtain ⟨η, hη, hηsub⟩ := Metric.eventually_nhds_iff_ball.mp hcev
    -- graph points over `ball w₁ η` lie in `A`
    have hgA : ∀ w ∈ ball w₁ η, graphBase S kf w ∈ A := by
      intro w hw
      obtain ⟨hwB, hcw⟩ := hηsub w hw
      by_contra hwA
      set z₀ := graphBase S kf w with hz₀def
      have hz₀Ω : z₀ ∈ Ω := by
        simpa using (htube w (ball_subset_closedBall hwB) 0
          (mem_closedBall_self hR.le)).2
      have hhz₀ : ContinuousAt h z₀ := hhc.continuousAt (hAo.mem_nhds ⟨hz₀Ω, hwA⟩)
      have hline : Tendsto (fun t : ℂ => z₀ + t • u0) (𝓝[≠] 0) (𝓝 z₀) := by
        have : Tendsto (fun t : ℂ => z₀ + t • u0) (𝓝 0) (𝓝 (z₀ + (0 : ℂ) • u0)) :=
          ((continuous_const.add (continuous_id.smul continuous_const)).tendsto 0)
        simp only [zero_smul, add_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      set ε₀ : ℝ := Real.exp (-(h z₀ + 1 + C₀) / a) with hε₀def
      have hε₀ : 0 < ε₀ := Real.exp_pos _
      have h1 : ∀ᶠ t in 𝓝[≠] (0 : ℂ), h (z₀ + t • u0) < h z₀ + 1 :=
        (hhz₀.tendsto.comp hline).eventually (gt_mem_nhds (by linarith))
      have h2 : ∀ᶠ t in 𝓝[≠] (0 : ℂ), ‖t‖ < min (R / 2) ε₀ :=
        nhdsWithin_le_nhds (by
          have : Tendsto (fun t : ℂ => ‖t‖) (𝓝 0) (𝓝 0) := by
            simpa using (continuous_norm.tendsto (0 : ℂ))
          exact this.eventually (gt_mem_nhds (lt_min (by positivity) hε₀)))
      obtain ⟨t, ht1, ht2, ht0⟩ := (h1.and (h2.and self_mem_nhdsWithin)).exists
      have ht0' : t ≠ 0 := ht0
      have htR : ‖t‖ ≤ R / 2 := (lt_of_lt_of_le ht2 (min_le_left _ _)).le
      have hb := hbd w hwB t ht0' htR
      have hlt : Real.log ‖t‖ < -(h z₀ + 1 + C₀) / a := by
        rw [← Real.log_exp (-(h z₀ + 1 + C₀) / a)]
        exact Real.log_lt_log (norm_pos_iff.mpr ht0') (ht2.trans_le (min_le_right _ _))
      have hl0 := hlog0 t htR
      rw [abs_le] at hb
      have key : -a * Real.log ‖t‖ > h z₀ + 1 + C₀ := by
        rw [lt_div_iff₀ ha] at hlt
        nlinarith
      nlinarith
    -- logarithmic poles of `u₂` at the graph points over `ball w₁ η`
    have hpole : ∀ w ∈ ball w₁ η, ∃ C' : ℝ, ∀ᶠ ζ in 𝓝[≠] graphBase S kf w,
        u₂ ζ ≤ ((a * Real.log ‖ζ - graphBase S kf w‖ + C' : ℝ) : EReal) := by
      intro w hw
      obtain ⟨hwB, -⟩ := hηsub w hw
      set z' := graphBase S kf w with hz'def
      have hwW : w ∈ Wd := hδW (ball_subset_closedBall hwB)
      have hfd : HasFDerivAt kf (fderiv ℂ kf w) w :=
        (hkf.differentiableAt (hWo.mem_nhds hwW)).hasFDerivAt
      obtain ⟨L, hL0, hLw⟩ := hfd.isBigO_sub.exists_pos
      have hLev : ∀ᶠ x in 𝓝 w, ‖kf x - kf w‖ ≤ L * ‖x - w‖ := hLw.bound
      have hπz' : S.π z' = w := by simpa using π_graphBase_add S kf w 0
      have htcz' : transCoord S kf z' = 0 := by simpa using transCoord_graphBase_add S hu0 kf w 0
      set K : ℝ := 1 + L * ‖S.π‖ with hKdef
      have hK : 0 < K := by positivity
      set C' : ℝ := B₁ + C₀ + a * Real.log K with hC'def
      have hev : ∀ᶠ ζ in 𝓝 z', (S.π ζ ∈ ball w₁ η ∧ ‖transCoord S kf ζ‖ < R / 2) ∧
          ‖kf (S.π ζ) - kf w‖ ≤ L * ‖S.π ζ - w‖ ∧ ζ ∈ Ω := by
        have hπt : Tendsto S.π (𝓝 z') (𝓝 w) := by
          rw [← hπz']; exact S.π.continuous.tendsto z'
        refine ((htc_ev w hwB (R / 2) (by positivity)).and
          (hπt.eventually (isOpen_ball.mem_nhds hw))).mono ?_ |>.and ((hπt.eventually hLev).and
          (hΩ.mem_nhds (by simpa using (htube w (ball_subset_closedBall hwB) 0
            (mem_closedBall_self hR.le)).2)))
        intro ζ hζ
        exact ⟨hζ.2, hζ.1.2⟩
      obtain ⟨ρ', hρ', hρ'sub⟩ := Metric.eventually_nhds_iff_ball.mp hev
      set B' : Set V := ball z' ρ' \ {z'} with hB'def
      have hB'o : IsOpen B' := isOpen_ball.sdiff isClosed_singleton
      have hB'Ω : B' ⊆ Ω := fun ζ hζ => (hρ'sub ζ hζ.1).2.2
      set v : V → EReal := fun ζ => ((a * Real.log ‖ζ - z'‖ + C' : ℝ) : EReal) with hvdef
      have hvusc : UpperSemicontinuousOn v B' := by
        apply ContinuousOn.upperSemicontinuousOn
        apply continuous_coe_real_ereal.comp_continuousOn
        refine ContinuousOn.add (continuousOn_const.mul ?_) continuousOn_const
        refine ContinuousOn.log ((continuous_id.sub continuous_const).norm.continuousOn) ?_
        intro ζ hζ
        exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr hζ.2)
      have hae : ∀ᵐ ζ ∂(volume.restrict B'), u₂ ζ ≤ v ζ := by
        filter_upwards [LelongPoincareDivisor.ae_ne_zero hB'o (hg.mono hB'Ω)
          (fun y hy => hg0 y (hB'Ω hy)), ae_restrict_mem hB'o.measurableSet] with ζ hgζ hζB
        obtain ⟨⟨hπζ, htζ⟩, hLζ, hζΩ⟩ := hρ'sub ζ hζB.1
        set t := transCoord S kf ζ with htdef
        set w' := S.π ζ with hw'def
        have hdec : graphBase S kf w' + t • u0 = ζ := graphBase_add_transCoord S kf ζ
        have hw'B : w' ∈ ball wy δ := (hηsub w' hπζ).1
        have ht0 : t ≠ 0 := by
          intro ht0
          rw [ht0, zero_smul, add_zero] at hdec
          exact hgζ (hdec ▸ hgraph0 w' (hδW (ball_subset_closedBall hw'B)))
        have hζA : ζ ∉ A := fun hA => hgζ (hAg ζ hA)
        have hb := hbd w' hw'B t ht0 htζ.le
        rw [hdec, abs_le] at hb
        have hcw' := (hηsub w' hπζ).2
        have hl0 := hlog0 t htζ.le
        have hhζ : -a * Real.log ‖t‖ - C₀ ≤ h ζ := by nlinarith
        have hu₁ζ : u₁ ζ ≤ (B₁ : EReal) := by
          apply hB₁
          refine ⟨(w', t), ⟨ball_subset_closedBall hw'B, ?_⟩, hdec⟩
          exact mem_closedBall_zero_iff.mpr (by linarith)
        have hsum : u₂ ζ + ((-(-h ζ) : ℝ) : EReal) ≤ (B₁ : EReal) := by
          rw [neg_neg, ← heq ζ ⟨hζΩ, hζA⟩]; exact hu₁ζ
        have hu₂ζ := SGPT.Siu.EReal.le_add_of_add_neg_le hsum
        refine hu₂ζ.trans (EReal.coe_le_coe_iff.mpr ?_)
        -- `‖t‖ ≤ K ‖ζ - z'‖`
        have htK : ‖t‖ ≤ K * ‖ζ - z'‖ := by
          have h1 : t = ⟪u0, ζ - z'⟫_ℂ - (kf (S.π ζ) - kf w) := by
            have h2 : transCoord S kf z' = 0 := htcz'
            simp only [htdef, transCoord, inner_sub_right] at h2 ⊢
            rw [hπz'] at h2
            linear_combination h2
          rw [h1]
          calc ‖⟪u0, ζ - z'⟫_ℂ - (kf (S.π ζ) - kf w)‖
              ≤ ‖⟪u0, ζ - z'⟫_ℂ‖ + ‖kf (S.π ζ) - kf w‖ := norm_sub_le _ _
            _ ≤ ‖ζ - z'‖ + L * ‖S.π ζ - w‖ := by
                gcongr
                · calc ‖⟪u0, ζ - z'⟫_ℂ‖ ≤ ‖u0‖ * ‖ζ - z'‖ := norm_inner_le_norm _ _
                    _ = ‖ζ - z'‖ := by rw [hu0, one_mul]
            _ = ‖ζ - z'‖ + L * ‖S.π (ζ - z')‖ := by rw [map_sub, hπz']
            _ ≤ ‖ζ - z'‖ + L * (‖S.π‖ * ‖ζ - z'‖) := by
                gcongr; exact S.π.le_opNorm _
            _ = K * ‖ζ - z'‖ := by rw [hKdef]; ring
        have htpos : 0 < ‖t‖ := norm_pos_iff.mpr ht0
        have hdpos : 0 < ‖ζ - z'‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hζB.2)
        have hlogt : Real.log ‖t‖ ≤ Real.log K + Real.log ‖ζ - z'‖ := by
          rw [← Real.log_mul hK.ne' hdpos.ne']
          exact Real.log_le_log htpos htK
        rw [hC'def]
        nlinarith
      have hle := SGPT.Foundations.Analysis.PlurisubharmonicOn.le_of_ae_le (hu₂.mono hB'Ω) hB'o
        hvusc volume hae
      refine ⟨C', ?_⟩
      have hmem : B' ∈ 𝓝[≠] z' := sdiff_mem_nhdsWithin_compl (ball_mem_nhds z' hρ') _
      filter_upwards [hmem] with ζ hζ
      exact hle ζ hζ
    -- the contradiction with `SparseLogPoles`
    set z₁ := graphBase S kf w₁ with hz₁def
    have hz₁A := hgA w₁ (mem_ball_self hη)
    have hz₁N : z₁ ∈ N := by
      simpa using (htube w₁ (ball_subset_closedBall hw₁) 0 (mem_closedBall_self hR.le)).1
    have hP₁ : Nonempty (RegularPresentation g z₁) := ⟨P.restrict (hNU hz₁N) (hAg z₁ hz₁A)⟩
    have hgraphpt : ∀ z', S.π z' ∈ ball w₁ η → z' ∈ N → g z' = 0 →
        z' = graphBase S kf (S.π z') := by
      intro z' hπ hN hg'
      have hdec := graphBase_add_transCoord S kf z'
      have hmem : graphBase S kf (S.π z') + transCoord S kf z' • u0 ∈ N := by rw [hdec]; exact hN
      have h0 := ((hzero' _ _ hmem).mp (by rw [hdec]; exact hg')).2
      rw [h0, zero_smul, add_zero] at hdec
      exact hdec.symm
    have hπz₁ : S.π z₁ = w₁ := by simpa using π_graphBase_add S kf w₁ 0
    set O : Set V := S.π ⁻¹' ball w₁ η ∩ N with hOdef
    have hO : O ∈ 𝓝 z₁ := by
      refine inter_mem ?_ (hNo.mem_nhds hz₁N)
      apply (isOpen_ball.preimage S.π.continuous).mem_nhds
      rw [mem_preimage, hπz₁]; exact mem_ball_self hη
    have hloc : ∀ᶠ z' in 𝓝 z₁, g z' = 0 → z' ∈ A := by
      filter_upwards [hO] with z' hz' hg'
      rw [hgraphpt z' hz'.1 hz'.2 hg']
      exact hgA _ hz'.1
    obtain ⟨z', ⟨hz'O, hz'A⟩, hnot⟩ := hsp z₁ hz₁A hP₁ hloc a ha O hO
    have hz'g := hgraphpt z' hz'O.1 hz'O.2 (hAg z' hz'A)
    obtain ⟨C', hC'⟩ := hpole (S.π z') hz'O.1
    apply hnot C'
    rw [hz'g]
    exact hC'
  -- **the bound**
  set O' : Set V := S.π ⁻¹' ball wy δ ∩ transCoord S kf ⁻¹' ball 0 (R / 2) with hO'def
  have hO'o : IsOpen O' :=
    hcontTC.isOpen_inter_preimage (isOpen_ball.preimage S.π.continuous) isOpen_ball
  have hyO' : y ∈ O' := by
    have := htc_ev wy (mem_ball_self hδ) (R / 2) (by positivity)
    rw [hgb] at this
    obtain ⟨h1, h2⟩ := this.self_of_nhds
    exact ⟨h1, mem_ball_zero_iff.mpr h2⟩
  have hfirst : ∀ ζ ∈ O', ζ ∈ Ω \ A → g ζ ≠ 0 → h ζ ≤ C₀ := by
    intro ζ hζ hζΩ hgζ
    set t := transCoord S kf ζ with htdef
    have hdec : graphBase S kf (S.π ζ) + t • u0 = ζ := graphBase_add_transCoord S kf ζ
    have ht0 : t ≠ 0 := by
      intro ht0
      rw [ht0, zero_smul, add_zero] at hdec
      exact hgζ (hdec ▸ hgraph0 _ (hδW (ball_subset_closedBall hζ.1)))
    have htR : ‖t‖ ≤ R / 2 := (mem_ball_zero_iff.mp hζ.2).le
    have hb := hbd (S.π ζ) hζ.1 t ht0 htR
    rw [hdec, abs_le] at hb
    have := hcpos (S.π ζ) hζ.1
    have := hlog0 t htR
    nlinarith
  refine ⟨O', hO'o.mem_nhds hyO', C₀, fun ζ hζ hζΩ => ?_⟩
  by_cases hgζ : g ζ = 0
  · by_contra hlt
    push Not at hlt
    have hcz : ContinuousAt h ζ := hhc.continuousAt (hAo.mem_nhds hζΩ)
    have hev : ∀ᶠ ζ' in 𝓝 ζ, C₀ < h ζ' ∧ ζ' ∈ O' ∧ ζ' ∈ Ω \ A :=
      (hcz.eventually (lt_mem_nhds hlt)).and
        ((show ∀ᶠ ζ' in 𝓝 ζ, ζ' ∈ O' from hO'o.mem_nhds hζ).and
          (show ∀ᶠ ζ' in 𝓝 ζ, ζ' ∈ Ω \ A from hAo.mem_nhds hζΩ))
    obtain ⟨ζ', ⟨h1, h2, h3⟩, h4⟩ := (hev.and_frequently (hg0 ζ hζΩ.1)).exists
    linarith [hfirst ζ' h2 h3 h4]
  · exact hfirst ζ hζ hζΩ hgζ

end Transverse

section Slicing

variable {n : ℕ}

local notation "V" => EuclideanSpace ℂ (Fin n)

/-- **The local bound.**  If `u₁ = u₂ + h` off `A ⊆ {g = 0}`, with `u₁, u₂` plurisubharmonic
and locally integrable, `h` pluriharmonic on `Ω \ A`, and `u₂` without logarithmic poles along
the hypersurface pieces of `A` (`SparseLogPoles`), then `h` is bounded above near every point of
`Ω`, off `A`. -/
theorem exists_nhds_le_of_eq_add {Ω : Set V} (hΩ : IsOpen Ω)
    {u₁ u₂ : V → EReal} (hu₁ : PlurisubharmonicOn u₁ Ω) (hu₂ : PlurisubharmonicOn u₂ Ω)
    (hi₁ : LocallyIntegrableOn (fun z => (u₁ z).toReal) Ω volume)
    (hi₂ : LocallyIntegrableOn (fun z => (u₂ z).toReal) Ω volume)
    (hf₁ : ∀ᵐ z ∂volume.restrict Ω, u₁ z ≠ ⊥) (hf₂ : ∀ᵐ z ∂volume.restrict Ω, u₂ z ≠ ⊥)
    {g : V → ℂ} (hg : DifferentiableOn ℂ g Ω) (hg0 : ∀ y ∈ Ω, ∃ᶠ z in 𝓝 y, g z ≠ 0)
    {A : Set V} (hAg : ∀ z ∈ A, g z = 0) (hAo : IsOpen (Ω \ A))
    {h : V → ℝ} (hhc : ContinuousOn h (Ω \ A))
    (hhp : PlurisubharmonicOn (fun z => (h z : EReal)) (Ω \ A))
    (hhn : PlurisubharmonicOn (fun z => ((-h z : ℝ) : EReal)) (Ω \ A))
    (heq : ∀ z ∈ Ω \ A, u₁ z = u₂ z + (h z : EReal))
    (hsp : SparseLogPoles u₂ g A) {p : V} (hp : p ∈ Ω) :
    ∃ U ∈ 𝓝 p, ∃ C : ℝ, ∀ z ∈ U, z ∈ Ω \ A → h z ≤ C := by
  classical
  -- off the zero set of `g`: continuity
  by_cases hgp : g p ≠ 0
  · have hpA : p ∈ Ω \ A := ⟨hp, fun hA => hgp (hAg p hA)⟩
    have hc : ContinuousAt h p := hhc.continuousAt (hAo.mem_nhds hpA)
    exact ⟨_, hc.eventually (gt_mem_nhds (lt_add_one (h p))), h p + 1,
      fun z hz _ => le_of_lt hz⟩
  push Not at hgp
  -- a ball, and a direction along which `g` does not vanish identically
  obtain ⟨r0, hr0, hball⟩ := Metric.isOpen_iff.mp hΩ p hp
  obtain ⟨z1, hz1g, hz1b⟩ := ((hg0 p hp).and_eventually (ball_mem_nhds p (half_pos hr0))).exists
  have hz1p : z1 ≠ p := fun h => hz1g (h ▸ hgp)
  set ρ1 : ℝ := ‖z1 - p‖ with hρ1def
  have hρ1 : 0 < ρ1 := norm_pos_iff.mpr (sub_ne_zero.mpr hz1p)
  have hρ1r : ρ1 < r0 / 2 := by
    rw [dist_eq_norm] at hz1b; exact hz1b
  set u0 : V := ((ρ1 : ℂ)⁻¹) • (z1 - p) with hu0def
  have hu0 : ‖u0‖ = 1 := by
    rw [hu0def, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ1,
      ← hρ1def, inv_mul_cancel₀ hρ1.ne']
  have hz1eq : p + (ρ1 : ℂ) • u0 = z1 := by
    rw [hu0def, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hρ1.ne'), one_smul]; abel
  -- the line through `p`
  set G0 : ℂ → ℂ := fun s => g (p + s • u0) with hG0def
  have hnormline : ∀ (b : V) (s : ℂ), ‖(b + s • u0) - b‖ = ‖s‖ := by
    intro b s; rw [add_sub_cancel_left, norm_smul, hu0, mul_one]
  have hG0d : DifferentiableOn ℂ G0 (ball (0 : ℂ) r0) := by
    refine hg.comp ((differentiable_const _).add
      (differentiable_id.smul_const u0)).differentiableOn ?_
    intro s hs
    apply hball
    rw [mem_ball, dist_eq_norm, hnormline]
    simpa using hs
  have hiso : ∀ᶠ s in 𝓝[≠] (0 : ℂ), G0 s ≠ 0 := by
    by_contra hcon
    rw [Filter.not_eventually] at hcon
    have hfreq : ∃ᶠ s in 𝓝[≠] (0 : ℂ), G0 s = 0 := hcon.mono fun s hs => not_not.mp hs
    have hzero := (hG0d.analyticOnNhd isOpen_ball).eqOn_zero_of_preconnected_of_frequently_eq_zero
      (convex_ball (0 : ℂ) r0).isPreconnected (mem_ball_self hr0) hfreq
    have hmem : (ρ1 : ℂ) ∈ ball (0 : ℂ) r0 := by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ1]; linarith
    have := hzero hmem
    simp only [hG0def, Pi.zero_apply, hz1eq] at this
    exact hz1g this
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hiso
  obtain ⟨ε, hε, hεG⟩ := hiso
  set R : ℝ := min (ε / 2) (r0 / 4) with hRdef
  have hR : 0 < R := lt_min (half_pos hε) (by positivity)
  have hRε : R < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  have hRr : R ≤ r0 / 4 := min_le_right _ _
  have hGR : ∀ s ∈ sphere (0 : ℂ) R, G0 s ≠ 0 := by
    intro s hs
    have hsR : ‖s‖ = R := by simpa using hs
    refine hεG (by rw [dist_zero_right, hsR]; exact hRε) ?_
    intro h0; rw [mem_singleton_iff] at h0; rw [h0, norm_zero] at hsR; exact hR.ne hsR
  have hsphball : sphere (0 : ℂ) R ⊆ ball (0 : ℂ) r0 := by
    intro s hs; rw [mem_ball_zero_iff]; rw [mem_sphere_zero_iff_norm] at hs; linarith
  -- an orthogonal splitting along `u₀`
  obtain ⟨k, -, ⟨S⟩⟩ := DivisorRegularLocus.exists_splitting hu0
  set E := EuclideanSpace ℂ (Fin k)
  have hLcont : Continuous (fun q : E × ℂ => (p + S.ι q.1) + q.2 • u0) :=
    (continuous_const.add (S.ι.continuous.comp continuous_fst)).add
      (continuous_snd.smul continuous_const)
  have hnormw : ∀ (w : E) (s : ℂ), ‖((p + S.ι w) + s • u0) - p‖ ≤ ‖w‖ + ‖s‖ := by
    intro w s
    have : ((p + S.ι w) + s • u0) - p = S.ι w + s • u0 := by abel
    rw [this]
    refine (norm_add_le _ _).trans ?_
    rw [S.ι.norm_map, norm_smul, hu0, mul_one]
  -- `g` has no zeros on the circles of the nearby lines
  have htube : ∀ᶠ w in 𝓝 (0 : E), ∀ s ∈ sphere (0 : ℂ) R,
      g ((p + S.ι w) + s • u0) ≠ 0 := by
    apply (isCompact_sphere (0 : ℂ) R).eventually_forall_of_forall_eventually
    intro s hs
    have hpt : (p + S.ι (0 : E)) + s • u0 ∈ Ω := by
      apply hball
      rw [mem_ball, dist_eq_norm]
      refine (hnormw 0 s).trans_lt ?_
      rw [norm_zero, zero_add]
      have := hsphball hs; rw [mem_ball_zero_iff] at this; exact this
    have hcont : ContinuousAt (fun q : E × ℂ => g ((p + S.ι q.1) + q.2 • u0)) (0, s) := by
      have h1 : ContinuousAt g ((fun q : E × ℂ => (p + S.ι q.1) + q.2 • u0) (0, s)) :=
        (hg.differentiableAt (hΩ.mem_nhds hpt)).continuousAt
      exact ContinuousAt.comp (f := fun q : E × ℂ => (p + S.ι q.1) + q.2 • u0) h1
        hLcont.continuousAt
    have hval : g ((p + S.ι (0 : E)) + s • u0) ≠ 0 := by
      simpa [hG0def] using hGR s hs
    have := hcont.eventually (isOpen_ne.mem_nhds hval)
    exact this
  rw [Metric.eventually_nhds_iff] at htube
  obtain ⟨δ1, hδ1, hδ1G⟩ := htube
  set δ : ℝ := min (δ1 / 2) (r0 / 4) with hδdef
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδr : δ ≤ r0 / 4 := min_le_right _ _
  have hδδ1 : δ < δ1 := (min_le_left _ _).trans_lt (by linarith)
  -- a bound for `h` on the circles
  set Ks : Set V := (fun q : E × ℂ => (p + S.ι q.1) + q.2 • u0) ''
    (closedBall (0 : E) δ ×ˢ sphere (0 : ℂ) R) with hKsdef
  have hKsc : IsCompact Ks :=
    ((isCompact_closedBall _ _).prod (isCompact_sphere _ _)).image hLcont
  have hKsA : Ks ⊆ Ω \ A := by
    rintro _ ⟨q, hq, rfl⟩
    have hw : dist q.1 0 < δ1 := (mem_closedBall.mp hq.1).trans_lt hδδ1
    have hg' := hδ1G hw q.2 hq.2
    refine ⟨?_, fun hA => hg' (hAg _ hA)⟩
    apply hball
    rw [mem_ball, dist_eq_norm]
    refine (hnormw q.1 q.2).trans_lt ?_
    have h1 : ‖q.1‖ ≤ δ := by simpa using hq.1
    have h2 : ‖q.2‖ = R := by simpa using hq.2
    linarith
  obtain ⟨B, hB⟩ := hKsc.exists_bound_of_continuousOn (hhc.mono hKsA)
  -- the null set of bad lines
  set Bad : Set V := {y | y ∈ ball p r0 ∧ g y = 0 ∧ y ∉ transverseLocus g u0} with hBaddef
  set Ynull : Set E := S.π '' Bad with hYdef
  have hnull : volume Ynull = 0 :=
    DivisorSingularProjection.measure_image_bad_eq_zero (volume : Measure E) isOpen_ball
      (hg.mono hball) (fun y hy => hg0 y (hball hy)) hu0 S
  -- the bound on a good line
  have hslice : ∀ w : E, ‖w‖ < δ → S.π p + w ∉ Ynull → ∀ s : ℂ, ‖s‖ < R →
      g ((p + S.ι w) + s • u0) ≠ 0 → h ((p + S.ι w) + s • u0) ≤ B := by
    intro w hw hgood s hs hgs
    set a : V := p + S.ι w with hadef
    set Lw : ℂ → V := fun s => a + s • u0 with hLwdef
    have hLwc : Continuous Lw := continuous_const.add (continuous_id.smul continuous_const)
    set O : Set ℂ := Lw ⁻¹' ball p r0 with hOdef
    have hOopen : IsOpen O := isOpen_ball.preimage hLwc
    set G : ℂ → ℂ := fun s => g (Lw s) with hGdef
    have hGd : DifferentiableOn ℂ G O :=
      hg.comp ((differentiable_const _).add (differentiable_id.smul_const u0)).differentiableOn
        (fun s hs => hball hs)
    set F : ℂ → EReal := fun s => (h (Lw s) : EReal) with hFdef
    have hnormLw : ∀ s : ℂ, ‖Lw s - p‖ ≤ ‖w‖ + ‖s‖ := fun s => hnormw w s
    have hD : closedBall (0 : ℂ) R ⊆ O := by
      intro s hs
      rw [mem_closedBall_zero_iff] at hs
      show Lw s ∈ ball p r0
      rw [mem_ball, dist_eq_norm]
      refine (hnormLw s).trans_lt ?_
      linarith
    have hoffA : ∀ s ∈ O, G s ≠ 0 → Lw s ∈ Ω \ A := fun s hs hGs =>
      ⟨hball hs, fun hA => hGs (hAg _ hA)⟩
    have hFpsh : PlurisubharmonicOn F (O \ {s | G s = 0}) := by
      have := hhp.comp_affine (ContinuousLinearMap.toSpanSingleton ℂ u0) a
      simp only [ContinuousLinearMap.toSpanSingleton_apply] at this
      exact this.mono (fun s hs => hoffA s hs.1 hs.2)
    have hFbound : ∀ x ∈ O, ∃ U ∈ 𝓝 x, ∃ C : ℝ, ∀ y ∈ U, G y ≠ 0 → F y ≤ (C : EReal) := by
      intro x hx
      by_cases hGx : G x = 0
      · set y : V := Lw x with hydef
        have hyb : y ∈ ball p r0 := hx
        have hπy : S.π y = S.π p + w := by
          simp only [hydef, hLwdef, hadef, map_add, map_smul, S.π_ι, S.π_u, smul_zero, add_zero]
        have htr : y ∈ transverseLocus g u0 := by
          by_contra hbad
          exact hgood (hπy ▸ ⟨y, ⟨hyb, hGx, hbad⟩, rfl⟩)
        obtain ⟨P⟩ := htr.1
        have hdh : fderiv ℂ P.h y u0 ≠ 0 :=
          (P.mem_transverseLocus_iff P.mem P.g_x u0).mp htr
        obtain ⟨U', hU', C, hC⟩ := exists_nhds_le_of_regularPresentation S hu0 hΩ hu₁ hu₂ hi₁ hi₂
          hf₁ hf₂ hg hg0 hAg hAo hhc hhp hhn heq hsp (hball hyb) P hdh
        refine ⟨Lw ⁻¹' U' ∩ O, inter_mem (hLwc.continuousAt.preimage_mem_nhds hU')
          (hOopen.mem_nhds hx), C, fun y' hy' hGy' => ?_⟩
        exact EReal.coe_le_coe_iff.mpr (hC _ hy'.1 (hoffA y' hy'.2 hGy'))
      · obtain ⟨C, hC⟩ := SGPT.Siu.PlurisubharmonicOn.exists_real_bound_nhds hFpsh ⟨hx, hGx⟩
        exact ⟨_, hC, C, fun y hy _ => hy⟩
    have hsph : ∀ s ∈ sphere (0 : ℂ) R, G s ≠ 0 ∧ F s ≤ (B : EReal) := by
      intro s hs
      have hwδ1 : dist w 0 < δ1 := by
        rw [dist_zero_right]; exact hw.trans_le (min_le_left _ _ |>.trans (by linarith))
      have hGs : G s ≠ 0 := hδ1G hwδ1 s hs
      refine ⟨hGs, EReal.coe_le_coe_iff.mpr ?_⟩
      have hmem : Lw s ∈ Ks := ⟨(w, s), ⟨by simpa using hw.le, hs⟩, rfl⟩
      exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hB _ hmem)
    have hmain := SGPT.Siu.le_on_closedBall_of_removable hOopen hGd hFpsh hFbound hR hD hsph s
      (mem_closedBall_zero_iff.mpr hs.le) hgs
    exact EReal.coe_le_coe_iff.mp hmain
  -- the bound almost everywhere, hence everywhere off `A`
  set N : Set V :=
    {z | ‖⟪u0, z - p⟫_ℂ‖ < R ∧ ‖S.π (z - p)‖ < δ} with hNdef
  have hNopen : IsOpen N := by
    apply IsOpen.inter
    · exact isOpen_lt ((continuous_const.inner (continuous_id.sub continuous_const)).norm)
        continuous_const
    · exact isOpen_lt ((S.π.continuous.comp (continuous_id.sub continuous_const)).norm)
        continuous_const
  have hpN : p ∈ N := by
    simp only [hNdef, mem_ofPred_eq, sub_self, inner_zero_right, norm_zero, map_zero]
    exact ⟨hR, hδ⟩
  have hdecomp : ∀ z : V, z = (p + S.ι (S.π (z - p))) + ⟪u0, z - p⟫_ℂ • u0 := by
    intro z
    have h := S.decomp (z - p)
    calc z = p + (z - p) := by abel
      _ = p + (⟪u0, z - p⟫_ℂ • u0 + S.ι (S.π (z - p))) := by rw [← h]
      _ = _ := by abel
  have hNball : N ⊆ ball p r0 := by
    intro z hz
    rw [mem_ball, dist_eq_norm]
    have h := hnormw (S.π (z - p)) (⟪u0, z - p⟫_ℂ)
    rw [← hdecomp z] at h
    have := hz.1; have := hz.2
    linarith
  set Ω' : Set V := N ∩ (Ω \ A) with hΩ'def
  have hΩ'open : IsOpen Ω' := hNopen.inter hAo
  have hpre : volume (S.π ⁻¹' Ynull) = 0 := by
    have hmp := DivisorIntegrationCurrent.measurePreserving_splitMap hu0 S
    have hemb := DivisorIntegrationCurrent.measurableEmbedding_splitMap hu0 S
    rw [← hmp.map_eq, hemb.map_apply]
    have : DivisorIntegrationCurrent.splitMap S ⁻¹' (S.π ⁻¹' Ynull) = univ ×ˢ Ynull := by
      ext q
      simp [DivisorIntegrationCurrent.splitMap_apply, S.π_smul_add]
    rw [this, Measure.prod_prod, hnull, mul_zero]
  have hgae : ∀ᵐ z ∂(volume.restrict Ω'), g z ≠ 0 :=
    ae_restrict_of_ae_restrict_of_subset (fun z hz => hz.2.1)
      (LelongPoincareDivisor.ae_ne_zero hΩ hg hg0)
  have hae : ∀ᵐ z ∂(volume.restrict Ω'), (h z : EReal) ≤ ((B : ℝ) : EReal) := by
    have hYc : ∀ᵐ z ∂(volume.restrict Ω'), z ∉ S.π ⁻¹' Ynull :=
      ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.mp hpre)
    filter_upwards [hgae, hYc, ae_restrict_mem hΩ'open.measurableSet] with z hgz hzY hzΩ'
    have hw : S.π p + S.π (z - p) = S.π z := by rw [map_sub]; abel
    have hgood : S.π p + S.π (z - p) ∉ Ynull := by rw [hw]; exact hzY
    have hz' := hdecomp z
    have hgz' : g ((p + S.ι (S.π (z - p))) + ⟪u0, z - p⟫_ℂ • u0) ≠ 0 := by
      rw [← hz']; exact hgz
    have := hslice (S.π (z - p)) hzΩ'.1.2 hgood (⟪u0, z - p⟫_ℂ) hzΩ'.1.1 hgz'
    rw [← hz'] at this
    exact EReal.coe_le_coe_iff.mpr this
  have hle := SGPT.Foundations.Analysis.PlurisubharmonicOn.le_of_ae_le
    (hhp.mono (fun z hz => hz.2)) hΩ'open
    (continuousOn_const.upperSemicontinuousOn) volume hae
  refine ⟨N, hNopen.mem_nhds hpN, B, fun z hz hzA => EReal.coe_le_coe_iff.mp (hle z ⟨hz, hzA⟩)⟩

end Slicing

end SGPT.Currents.AnalyticSupport
