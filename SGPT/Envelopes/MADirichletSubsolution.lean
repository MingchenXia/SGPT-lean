import SGPT.Envelopes.MADirichletFrame
import SGPT.Foundations.Analysis.Pending.BedfordTaylorDecreasingLimit
import SGPT.Foundations.Analysis.Pending.BoundedPairMaxLocality
import SGPT.Foundations.Analysis.Pending.BedfordTaylorFixedWeight

/-!
# The algebra of Monge–Ampère subsolutions

Xia, *Foundations of pluripotential theory* (FPT), `lem:continuous-density-subsolution-algebra`:
let `u, v` be locally bounded plurisubharmonic on an open set `Ω ⊆ ℂⁿ` and `F, G ≥ 0` continuous
on `Ω` with `(ddᶜu)ⁿ ≥ Fⁿ ηⁿ` and `(ddᶜv)ⁿ ≥ Gⁿ ηⁿ` (`η = ddᶜ|z|²`, `ηⁿ = n!/πⁿ dV`). Then

* `ma_ge_linComb`: for `a, b, c ≥ 0`,
  `(ddᶜ(a u + b v + c|z|²))ⁿ ≥ (a F + b G + c)ⁿ ηⁿ`
  (FPT states it for `a = 1 - t`, `b = t`; the case of arbitrary `a, b ≥ 0` is the same proof);
* `ma_ge_max`: `(ddᶜ max(u, v))ⁿ ≥ α` whenever `(ddᶜu)ⁿ ≥ α` and `(ddᶜv)ⁿ ≥ α` for a measure `α`
  finite on the compact subsets of `Ω`; in particular (`ma_ge_max_withDensity`)
  `(ddᶜ max(u, v))ⁿ ≥ min(F, G)ⁿ ηⁿ`.

The first assertion follows FPT: the lower bound is equivalent to the linear inequalities
`L_Y u ≥ n F` (`MADirichletFrame`), which add up; locally the densities are replaced by constants
and the local bounds are glued (`withDensity_le_of_forall_lt`).

For the maximum we use the plurifine locality of Bedford–Taylor measures instead of upper test
functions, which gives the statement for an arbitrary measure `α` (it is needed in that
generality for envelopes of subsolutions with measure data): on `{v + t < u}` and `{u < v + t}`
the measure of `max(u, v + t)` is that of `u`, resp. `v` (TN
`restrict_eq_of_bounded_pair_max`), for all but countably many levels `t` the set `{u = v + t}`
is `α`-null, and `max(u, v + tₖ) ↓ max(u, v)` along such levels `tₖ ↓ 0`, so the lower bound
passes to the limit (decreasing continuity, TN `tendsto_integral_of_antitone_isBTLimit`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Matrix TopologicalSpace
open scoped Topology ENNReal ComplexOrder ContDiff

namespace SGPT.Envelopes.MADirichlet

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.MongeAmpere
open SGPT.Foundations.Analysis.Pending.BedfordTaylor
open SGPT.NPP.LogConcavityDinew

variable {n : ℕ}

/-- Nonnegative multiples of locally bounded psh functions are locally bounded psh. -/
theorem isLocallyBoundedPshOn_const_mul {Ω : Opens (ComplexModel n)} {u : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u) {a : ℝ} (ha : 0 ≤ a) :
    IsLocallyBoundedPshOn Ω fun z => a * u z := by
  rcases ha.eq_or_lt with h0 | hpos
  · subst h0
    simp only [zero_mul]
    exact isLocallyBoundedPshOn_of_abs_le
      (fun x _ => plurisubharmonicAt_const _ (EReal.coe_ne_top _) x) (C := 0) fun _ _ => by simp
  · refine ⟨?_, fun z hz => ?_⟩
    · simpa only [EReal.coe_mul] using hu.1.const_mul hpos
    · obtain ⟨V, hzV, hVU, C, hC⟩ := hu.2 z hz
      exact ⟨V, hzV, hVU, a * C, fun y hy => by
        rw [abs_mul, abs_of_pos hpos]
        exact mul_le_mul_of_nonneg_left (hC y hy) hpos.le⟩

/-- `|z|²` is locally bounded psh on every open set. -/
theorem isLocallyBoundedPshOn_normSq (Ω : Opens (ComplexModel n)) :
    IsLocallyBoundedPshOn Ω fun z : ComplexModel n => ‖z‖ ^ 2 := by
  simpa only [one_mul] using SGPT.PSH.BookDeepDomination.isLocallyBoundedPshOn_mul_normSq Ω one_pos

/-- `a u + b v + c|z|²` is locally bounded psh for `a, b, c ≥ 0`. -/
theorem isLocallyBoundedPshOn_linComb {Ω : Opens (ComplexModel n)} {u v : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u) (hv : IsLocallyBoundedPshOn Ω v) {a b c : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hc : 0 ≤ c) :
    IsLocallyBoundedPshOn Ω fun z => a * u z + b * v z + c * ‖z‖ ^ 2 :=
  SGPT.PSH.BookDeepDomination.isLocallyBoundedPshOn_add
    (SGPT.PSH.BookDeepDomination.isLocallyBoundedPshOn_add (isLocallyBoundedPshOn_const_mul hu ha)
      (isLocallyBoundedPshOn_const_mul hv hb))
    (isLocallyBoundedPshOn_const_mul (isLocallyBoundedPshOn_normSq Ω) hc)

/-! ### Local constants from a continuous density -/

/-- **A constant lower bound on a small ball.** If `(ddᶜu)ⁿ ≥ Fⁿ ηⁿ` on `Ω` with `F ≥ 0`
continuous, then near `x` the frame inequalities hold with the constant `max (F x - δ) 0`. -/
theorem exists_frameIneqOnBall (hn : 0 < n) {Ω : Opens (ComplexModel n)} {u : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u) {F : ComplexModel n → ℝ} (hF : ContinuousOn F Ω)
    (hF0 : ∀ z ∈ Ω, 0 ≤ F z)
    (hμ : (volume.restrict (Ω : Set (ComplexModel n))).withDensity
        (fun z => ENNReal.ofReal (mongeAmpereConst n * F z ^ n)) ≤
      canonicalBedfordTaylorMeasure Ω u hu)
    {x : ComplexModel n} (hx : x ∈ Ω) {δ : ℝ} (hδ : 0 < δ) :
    ∃ r > 0, Metric.closedBall x (2 * r) ⊆ Ω ∧ FrameIneqOnBall u (max (F x - δ) 0) x r := by
  have hFc : ContinuousAt F x := hF.continuousAt (Ω.isOpen.mem_nhds hx)
  obtain ⟨ρ, hρ, hFρ⟩ := Metric.continuousAt_iff.mp hFc δ hδ
  obtain ⟨ε, hε, hεΩ⟩ := Metric.isOpen_iff.mp Ω.isOpen x hx
  set R : ℝ := min ρ ε / 2 with hRdef
  have hR : 0 < R := by positivity
  set Ω' : Opens (ComplexModel n) := ⟨Metric.ball x (min ρ ε), Metric.isOpen_ball⟩ with hΩ'
  have hΩ'Ω : Ω' ≤ Ω := fun z hz => hεΩ (Metric.ball_subset_ball (min_le_right _ _) hz)
  have hcl : Metric.closedBall x R ⊆ Ω' := Metric.closedBall_subset_ball (by linarith)
  have hclΩ : Metric.closedBall x R ⊆ Ω := hcl.trans hΩ'Ω
  set m : ℝ := max (F x - δ) 0 with hm
  refine ⟨R / 2, by positivity, by rwa [show 2 * (R / 2) = R by ring], ?_⟩
  rcases (le_max_right (F x - δ) 0).eq_or_lt with h0 | hpos
  · rw [show m = 0 by rw [hm]; exact h0.symm]
    exact frameIneqOnBall_zero hn hu hR hclΩ
  · have hu' : IsLocallyBoundedPshOn Ω' u := ⟨hu.1.mono hΩ'Ω, fun z hz => by
      obtain ⟨V, hzV, hVΩ, C, hC⟩ := hu.2 z (hΩ'Ω hz)
      exact ⟨V ⊓ Ω', ⟨hzV, hz⟩, inf_le_right, C, fun y hy => hC y hy.1⟩⟩
    have hmF : ∀ z ∈ (Ω' : Set (ComplexModel n)), m ≤ F z := by
      intro z hz
      have hz' : dist z x < ρ := lt_of_lt_of_le (Metric.mem_ball.mp hz) (min_le_left _ _)
      have := hFρ hz'
      rw [Real.dist_eq] at this
      exact max_le (by linarith [(abs_lt.mp this).1]) (hF0 z (hΩ'Ω hz))
    have hμ' : ENNReal.ofReal (mongeAmpereConst n * m ^ n) •
        volume.restrict (Ω' : Set (ComplexModel n)) ≤ canonicalBedfordTaylorMeasure Ω' u hu' := by
      rw [← canonicalBedfordTaylorMeasure_restrict hΩ'Ω hu hu']
      calc ENNReal.ofReal (mongeAmpereConst n * m ^ n) • volume.restrict (Ω' : Set (ComplexModel n))
          = (volume.restrict (Ω' : Set (ComplexModel n))).withDensity
              (fun _ => ENNReal.ofReal (mongeAmpereConst n * m ^ n)) := by rw [withDensity_const]
        _ ≤ (volume.restrict (Ω' : Set (ComplexModel n))).withDensity
              (fun z => ENNReal.ofReal (mongeAmpereConst n * F z ^ n)) := by
            refine withDensity_mono ?_
            filter_upwards [ae_restrict_mem Ω'.isOpen.measurableSet] with z hz
            refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ mongeAmpereConst_pos.le)
            exact pow_le_pow_left₀ (le_max_right _ _) (hmF z hz) n
        _ = ((volume.restrict (Ω : Set (ComplexModel n))).withDensity
              (fun z => ENNReal.ofReal (mongeAmpereConst n * F z ^ n))).restrict Ω' := by
            rw [restrict_withDensity Ω'.isOpen.measurableSet,
              Measure.restrict_restrict_of_subset hΩ'Ω]
        _ ≤ (canonicalBedfordTaylorMeasure Ω u hu).restrict Ω' :=
            Measure.restrict_mono subset_rfl hμ
    exact frameIneqOnBall_of_ma_ge hn hu' hpos hμ' hR hcl

/-! ### Convex combinations (FPT `lem:continuous-density-subsolution-algebra`, first part) -/

/-- **Monge–Ampère subsolutions are stable under nonnegative combinations and the addition of
`c|z|²`** (FPT `lem:continuous-density-subsolution-algebra`, first assertion, with `a = 1 - t`,
`b = t`): `(ddᶜ(a u + b v + c|z|²))ⁿ ≥ (aF + bG + c)ⁿ ηⁿ`. -/
theorem ma_ge_linComb (hn : 0 < n) {Ω : Opens (ComplexModel n)} {u v : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u) (hv : IsLocallyBoundedPshOn Ω v)
    {F G : ComplexModel n → ℝ} (hF : ContinuousOn F Ω) (hG : ContinuousOn G Ω)
    (hF0 : ∀ z ∈ Ω, 0 ≤ F z) (hG0 : ∀ z ∈ Ω, 0 ≤ G z)
    (hμu : (volume.restrict (Ω : Set (ComplexModel n))).withDensity
        (fun z => ENNReal.ofReal (mongeAmpereConst n * F z ^ n)) ≤
      canonicalBedfordTaylorMeasure Ω u hu)
    (hμv : (volume.restrict (Ω : Set (ComplexModel n))).withDensity
        (fun z => ENNReal.ofReal (mongeAmpereConst n * G z ^ n)) ≤
      canonicalBedfordTaylorMeasure Ω v hv)
    {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hw : IsLocallyBoundedPshOn Ω fun z => a * u z + b * v z + c * ‖z‖ ^ 2) :
    (volume.restrict (Ω : Set (ComplexModel n))).withDensity
        (fun z => ENNReal.ofReal (mongeAmpereConst n * (a * F z + b * G z + c) ^ n)) ≤
      canonicalBedfordTaylorMeasure Ω _ hw := by
  set w : ComplexModel n → ℝ := fun z => a * u z + b * v z + c * ‖z‖ ^ 2 with hwdef
  set g : ComplexModel n → ℝ := fun z => mongeAmpereConst n * (a * F z + b * G z + c) ^ n
    with hgdef
  have hg : ContinuousOn g Ω :=
    continuousOn_const.mul ((((continuousOn_const.mul hF).add (continuousOn_const.mul hG)).add
      continuousOn_const).pow n)
  refine withDensity_le_of_forall_lt hg fun x hx t ht => ?_
  -- a good error `δ` for the constants
  set φ : ℝ → ℝ := fun δ =>
    mongeAmpereConst n * (a * max (F x - δ) 0 + b * max (G x - δ) 0 + c) ^ n with hφ
  have hφc : Continuous φ := by
    simp only [hφ]
    fun_prop
  have hφ0 : φ 0 = g x := by
    simp only [hφ, hgdef, sub_zero, max_eq_left (hF0 x hx), max_eq_left (hG0 x hx)]
  have hev : ∀ᶠ δ in 𝓝 (0 : ℝ), t < φ δ :=
    hφc.continuousAt.eventually (lt_mem_nhds (by rw [hφ0]; exact ht))
  have hev' : ∀ᶠ δ in 𝓝[Ioi (0 : ℝ)] 0, t < φ δ ∧ δ ∈ Ioi (0 : ℝ) :=
    (hev.filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
  obtain ⟨δ, hδt, hδ⟩ := hev'.exists
  have hδ0 : (0 : ℝ) < δ := hδ
  obtain ⟨r₁, hr₁, hb₁, hf₁⟩ := exists_frameIneqOnBall hn hu hF hF0 hμu hx hδ0
  obtain ⟨r₂, hr₂, -, hf₂⟩ := exists_frameIneqOnBall hn hv hG hG0 hμv hx hδ0
  set r : ℝ := min r₁ r₂ with hrdef
  have hr : 0 < r := lt_min hr₁ hr₂
  have hbr : Metric.closedBall x (2 * r) ⊆ Ω :=
    (Metric.closedBall_subset_closedBall (by linarith [min_le_left r₁ r₂])).trans hb₁
  have hballr : Metric.ball x r ⊆ Ω := Metric.ball_subset_closedBall.trans
    ((Metric.closedBall_subset_closedBall (by linarith)).trans hbr)
  set m₁ : ℝ := max (F x - δ) 0 with hm₁
  set m₂ : ℝ := max (G x - δ) 0 with hm₂
  have h1 : FrameIneqOnBall (fun z => a * u z) (a * m₁) x r :=
    (hf₁.mono le_rfl (min_le_left _ _)).smul ha
  have h2 : FrameIneqOnBall (fun z => b * v z) (b * m₂) x r :=
    (hf₂.mono le_rfl (min_le_right _ _)).smul hb
  have h3 : FrameIneqOnBall (fun z : ComplexModel n => c * ‖z‖ ^ 2) (c * 1) x r :=
    (frameIneqOnBall_normSq hn x hr).smul hc
  have h12 := FrameIneqOnBall.add (isLocallyBoundedPshOn_const_mul hu ha)
    (isLocallyBoundedPshOn_const_mul hv hb) hballr h1 h2
  have h123 := FrameIneqOnBall.add (SGPT.PSH.BookDeepDomination.isLocallyBoundedPshOn_add
    (isLocallyBoundedPshOn_const_mul hu ha) (isLocallyBoundedPshOn_const_mul hv hb))
    (isLocallyBoundedPshOn_const_mul (isLocallyBoundedPshOn_normSq Ω) hc) hballr h12 h3
  have hM0 : 0 ≤ a * m₁ + b * m₂ + c * 1 := by positivity
  have hfw : FrameIneqOnBall w (a * m₁ + b * m₂ + c * 1) x (2 * r / 2) := by
    rw [show 2 * r / 2 = r by ring]
    exact h123
  have hloc := ma_ge_on_ball_of_frameIneq hn hw hM0 (by positivity : (0 : ℝ) < 2 * r) hbr hfw
  refine ⟨2 * r / 4, by positivity, ?_, le_trans ?_ hloc⟩
  · exact Metric.ball_subset_closedBall.trans
      ((Metric.closedBall_subset_closedBall (by linarith)).trans hbr)
  · have hle : ENNReal.ofReal t ≤ ENNReal.ofReal (mongeAmpereConst n * (a * m₁ + b * m₂ + c * 1) ^ n) := by
      refine ENNReal.ofReal_le_ofReal (le_of_lt ?_)
      simpa [hφ, mul_one] using hδt
    refine Measure.le_iff.mpr fun s hs => ?_
    rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
    exact mul_le_mul_of_nonneg_right hle zero_le

/-! ### Maxima (FPT `lem:continuous-density-subsolution-algebra`, second part) -/

/-- On the strict superlevel set `{v + t < u}` the Monge–Ampère measure of `max(u, v + t)` is that
of `u`, and on `{u < v + t}` that of `v`. Hence a common lower bound `α` of the two measures is a
lower bound for the measure of `max(u, v + t)` as soon as `{u = v + t}` is `α`-null. -/
theorem restrict_le_max_add_const (hn : 0 < n) {Ω : Opens (ComplexModel n)}
    {u v : ComplexModel n → ℝ} (hu : IsLocallyBoundedPshOn Ω u) (hv : IsLocallyBoundedPshOn Ω v)
    {α : Measure (ComplexModel n)}
    (hαu : α.restrict (Ω : Set (ComplexModel n)) ≤ canonicalBedfordTaylorMeasure Ω u hu)
    (hαv : α.restrict (Ω : Set (ComplexModel n)) ≤ canonicalBedfordTaylorMeasure Ω v hv)
    (t : ℝ) (hnull : α ((Ω : Set (ComplexModel n)) ∩ {z | u z = v z + t}) = 0)
    (hw : IsLocallyBoundedPshOn Ω fun z => max (u z) (v z + t)) :
    α.restrict (Ω : Set (ComplexModel n)) ≤ canonicalBedfordTaylorMeasure Ω _ hw := by
  classical
  have hall : ∀ P : Prop, (∀ _ : Fin n, P) ↔ P := fun P => ⟨fun h => h ⟨0, hn⟩, fun h _ => h⟩
  have hvt : IsLocallyBoundedPshOn Ω fun z => v z + t := IsLocallyBoundedPshOn.add_const hv t
  set μw := canonicalBedfordTaylorMeasure Ω _ hw with hμw
  have hlimw := isBTLimit_canonicalBedfordTaylorMeasure hw
  have hlimu := isBTLimit_canonicalBedfordTaylorMeasure hu
  have hlimv := (isBTLimit_canonicalBedfordTaylorMeasure hv).add_const_diag t
  set A : Set (ComplexModel n) := {z | z ∈ Ω ∧ v z + t < u z} with hA
  set B : Set (ComplexModel n) := {z | z ∈ Ω ∧ u z < v z + t} with hB
  have hloc1 := BoundedPairMaxLocality.restrict_eq_of_bounded_pair_max
    (u := fun _ => u) (w := fun _ => fun z => max (u z) (v z + t)) (g := fun _ => fun z => v z + t)
    hlimu hlimw (fun _ => hvt) (fun _ z _ => rfl)
  have hloc2 := BoundedPairMaxLocality.restrict_eq_of_bounded_pair_max
    (u := fun _ => fun z => v z + t) (w := fun _ => fun z => max (u z) (v z + t))
    (g := fun _ => u) hlimv hlimw (fun _ => hu) (fun _ z _ => max_comm _ _)
  simp only [hall] at hloc1 hloc2
  have hAm : MeasurableSet A := by
    have h := SGPT.PSH.BookDeepDomination.measurableSet_add_lt_add hv hu t 0
    simpa only [add_zero] using h
  have hBm : MeasurableSet B := by
    have h := SGPT.PSH.BookDeepDomination.measurableSet_add_lt_add hu hv 0 t
    simpa only [add_zero] using h
  have hAB : Disjoint A B := by
    rw [Set.disjoint_left]
    rintro z ⟨-, h1⟩ ⟨-, h2⟩
    linarith
  refine Measure.le_iff.mpr fun s hs => ?_
  rw [Measure.restrict_apply hs]
  have hsplit : s ∩ (Ω : Set (ComplexModel n)) ⊆
      (s ∩ A) ∪ (s ∩ B) ∪ ((Ω : Set (ComplexModel n)) ∩ {z | u z = v z + t}) := by
    rintro z ⟨hzs, hzΩ⟩
    rcases lt_trichotomy (u z) (v z + t) with h | h | h
    · exact mem_union_left _ (mem_union_right _ ⟨hzs, hzΩ, h⟩)
    · exact mem_union_right _ ⟨hzΩ, h⟩
    · exact mem_union_left _ (mem_union_left _ ⟨hzs, hzΩ, h⟩)
  have hαA : α (s ∩ A) ≤ μw (s ∩ A) := by
    have h1 := hαu (s ∩ A)
    rw [Measure.restrict_apply (hs.inter hAm),
      inter_eq_left.mpr (inter_subset_right.trans fun z hz => hz.1)] at h1
    have h2 := congrArg (fun μ : Measure (ComplexModel n) => μ s) hloc1
    simp only [Measure.restrict_apply hs] at h2
    rw [← hA] at h2
    calc α (s ∩ A) ≤ canonicalBedfordTaylorMeasure Ω u hu (s ∩ A) := h1
      _ = μw (s ∩ A) := h2.symm
  have hαB : α (s ∩ B) ≤ μw (s ∩ B) := by
    have h1 := hαv (s ∩ B)
    rw [Measure.restrict_apply (hs.inter hBm),
      inter_eq_left.mpr (inter_subset_right.trans fun z hz => hz.1)] at h1
    have h2 := congrArg (fun μ : Measure (ComplexModel n) => μ s) hloc2
    simp only [Measure.restrict_apply hs] at h2
    rw [← hB] at h2
    have hcan : canonicalBedfordTaylorMeasure Ω v hv =
        canonicalBedfordTaylorMeasure Ω (fun z => v z + t) hvt :=
      hlimv.unique (isBTLimit_canonicalBedfordTaylorMeasure hvt)
    calc α (s ∩ B) ≤ canonicalBedfordTaylorMeasure Ω v hv (s ∩ B) := h1
      _ = μw (s ∩ B) := h2.symm
  calc α (s ∩ (Ω : Set (ComplexModel n)))
      ≤ α ((s ∩ A) ∪ (s ∩ B) ∪ ((Ω : Set (ComplexModel n)) ∩ {z | u z = v z + t})) :=
        measure_mono hsplit
    _ ≤ α ((s ∩ A) ∪ (s ∩ B)) + α ((Ω : Set (ComplexModel n)) ∩ {z | u z = v z + t}) :=
        measure_union_le _ _
    _ = α (s ∩ A) + α (s ∩ B) := by
        rw [hnull, add_zero, measure_union
          (hAB.mono inter_subset_right inter_subset_right) (hs.inter hBm)]
    _ ≤ μw (s ∩ A) + μw (s ∩ B) := add_le_add hαA hαB
    _ = μw ((s ∩ A) ∪ (s ∩ B)) :=
        (measure_union (hAB.mono inter_subset_right inter_subset_right) (hs.inter hBm)).symm
    _ ≤ μw s := measure_mono (union_subset inter_subset_left inter_subset_left)

/-- **The maximum of two subsolutions is a subsolution**, for an arbitrary measure `α` finite on
the compact subsets of `Ω` (FPT `lem:continuous-density-subsolution-algebra`, second assertion,
in the generality of a measure). -/
theorem ma_ge_max (hn : 0 < n) {Ω : Opens (ComplexModel n)} {u v : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u) (hv : IsLocallyBoundedPshOn Ω v)
    {α : Measure (ComplexModel n)} (hα : ∀ K, IsCompact K → K ⊆ Ω → α K < ⊤)
    (hαu : α.restrict (Ω : Set (ComplexModel n)) ≤ canonicalBedfordTaylorMeasure Ω u hu)
    (hαv : α.restrict (Ω : Set (ComplexModel n)) ≤ canonicalBedfordTaylorMeasure Ω v hv)
    (hw : IsLocallyBoundedPshOn Ω fun z => max (u z) (v z)) :
    α.restrict (Ω : Set (ComplexModel n)) ≤ canonicalBedfordTaylorMeasure Ω _ hw := by
  -- generic levels
  have hgm : Measurable fun z => (Ω : Set (ComplexModel n)).indicator u z -
      (Ω : Set (ComplexModel n)).indicator v z :=
    (measurable_indicator_of_plurisubharmonicOn hu.1).sub
      (measurable_indicator_of_plurisubharmonicOn hv.1)
  obtain ⟨t, htanti, htpos, htlim, htnull⟩ := exists_antitone_level_null hα hgm
  have hnull : ∀ k, α ((Ω : Set (ComplexModel n)) ∩ {z | u z = v z + t k}) = 0 := by
    intro k
    refine measure_mono_null ?_ (htnull k)
    rintro z ⟨hzΩ, hz⟩
    refine ⟨hzΩ, ?_⟩
    have hz' : u z = v z + t k := hz
    show (Ω : Set (ComplexModel n)).indicator u z - (Ω : Set (ComplexModel n)).indicator v z = t k
    rw [indicator_of_mem hzΩ, indicator_of_mem hzΩ]
    linarith
  have hwk : ∀ k, IsLocallyBoundedPshOn Ω fun z => max (u z) (v z + t k) := fun k =>
    IsLocallyBoundedPshOn.max hu (IsLocallyBoundedPshOn.add_const hv (t k))
  have hstage : ∀ k, α.restrict (Ω : Set (ComplexModel n)) ≤
      canonicalBedfordTaylorMeasure Ω _ (hwk k) := fun k =>
    restrict_le_max_add_const hn hu hv hαu hαv (t k) (hnull k) (hwk k)
  refine restrict_le_of_tendsto_integral hα (fun k K hK hKΩ =>
    canonicalBedfordTaylorMeasure_finiteOnCompacts (hwk k) hK hKΩ)
    (fun K hK hKΩ => canonicalBedfordTaylorMeasure_finiteOnCompacts hw hK hKΩ) hstage ?_
  intro φ hφ hφc hφΩ
  refine tendsto_integral_of_antitone_isBTLimit hwk hw (fun z _ k l hkl => ?_) (fun z _ => ?_)
    (fun k => isBTLimit_canonicalBedfordTaylorMeasure (hwk k))
    (isBTLimit_canonicalBedfordTaylorMeasure hw) hφ hφc hφΩ
  · exact max_le_max le_rfl (by linarith [htanti hkl])
  · have h := ((tendsto_const_nhds (x := v z)).add htlim)
    simp only [add_zero] at h
    exact (tendsto_const_nhds (x := u z)).max h

/-- **The maximum of two subsolutions with continuous densities** (FPT
`lem:continuous-density-subsolution-algebra`, second assertion):
`(ddᶜ max(u, v))ⁿ ≥ min(F, G)ⁿ ηⁿ`. -/
theorem ma_ge_max_withDensity (hn : 0 < n) {Ω : Opens (ComplexModel n)}
    {u v : ComplexModel n → ℝ} (hu : IsLocallyBoundedPshOn Ω u) (hv : IsLocallyBoundedPshOn Ω v)
    {F G : ComplexModel n → ℝ} (hF : ContinuousOn F Ω) (hG : ContinuousOn G Ω)
    (hF0 : ∀ z ∈ Ω, 0 ≤ F z) (hG0 : ∀ z ∈ Ω, 0 ≤ G z)
    (hμu : (volume.restrict (Ω : Set (ComplexModel n))).withDensity
        (fun z => ENNReal.ofReal (mongeAmpereConst n * F z ^ n)) ≤
      canonicalBedfordTaylorMeasure Ω u hu)
    (hμv : (volume.restrict (Ω : Set (ComplexModel n))).withDensity
        (fun z => ENNReal.ofReal (mongeAmpereConst n * G z ^ n)) ≤
      canonicalBedfordTaylorMeasure Ω v hv)
    (hw : IsLocallyBoundedPshOn Ω fun z => max (u z) (v z)) :
    (volume.restrict (Ω : Set (ComplexModel n))).withDensity
        (fun z => ENNReal.ofReal (mongeAmpereConst n * min (F z) (G z) ^ n)) ≤
      canonicalBedfordTaylorMeasure Ω _ hw := by
  set α := volume.withDensity
    (fun z => ENNReal.ofReal (mongeAmpereConst n * min (F z) (G z) ^ n)) with hαdef
  have hαΩ : α.restrict (Ω : Set (ComplexModel n)) = (volume.restrict (Ω : Set (ComplexModel n))).withDensity
      (fun z => ENNReal.ofReal (mongeAmpereConst n * min (F z) (G z) ^ n)) := by
    rw [hαdef, restrict_withDensity Ω.isOpen.measurableSet]
  have hmono : ∀ {H : ComplexModel n → ℝ}, (∀ z ∈ Ω, min (F z) (G z) ≤ H z) →
      (volume.restrict (Ω : Set (ComplexModel n))).withDensity
        (fun z => ENNReal.ofReal (mongeAmpereConst n * min (F z) (G z) ^ n)) ≤
      (volume.restrict (Ω : Set (ComplexModel n))).withDensity
        (fun z => ENNReal.ofReal (mongeAmpereConst n * H z ^ n)) := by
    intro H hH
    refine withDensity_mono ?_
    filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with z hz
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ mongeAmpereConst_pos.le)
    exact pow_le_pow_left₀ (le_min (hF0 z hz) (hG0 z hz)) (hH z hz) n
  have hα : ∀ K, IsCompact K → K ⊆ Ω → α K < ⊤ := by
    intro K hK hKΩ
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
      (((continuousOn_const.mul ((continuous_min.comp_continuousOn (hF.prodMk hG)).pow n))).mono
        hKΩ)
    rw [hαdef, withDensity_apply _ hK.measurableSet]
    refine lt_of_le_of_lt (setLIntegral_mono (g := fun _ => ENNReal.ofReal C) measurable_const
      fun z hz => ENNReal.ofReal_le_ofReal ((le_abs_self _).trans
        (by rw [← Real.norm_eq_abs]; exact hC z hz))) ?_
    rw [setLIntegral_const]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top
  rw [← hαΩ]
  refine ma_ge_max hn hu hv hα ?_ ?_ hw
  · rw [hαΩ]; exact (hmono fun z _ => min_le_left _ _).trans hμu
  · rw [hαΩ]; exact (hmono fun z _ => min_le_right _ _).trans hμv

end SGPT.Envelopes.MADirichlet
