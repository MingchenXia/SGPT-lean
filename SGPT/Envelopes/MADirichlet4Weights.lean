import SGPT.Envelopes.MADirichlet4SelfIntegral
import SGPT.Foundations.Analysis.Pending.CapacityWeightedConvergence
import SGPT.Foundations.Analysis.Pending.VaguePortmanteau

/-!
# Weights controlled by capacity

Xia, *Foundations of pluripotential theory* (FPT), `lem:capacity-controlled-measure-weights`,
for a fixed weight: let `K₀ ⊆ D` be compact and `μ_j, ν` finite measures carried by `K₀` with
`μ_j → ν` weakly (against continuous compactly supported functions) and uniformly small on sets
of small capacity: for every `r > 0` there is `η > 0` with `μ_j(E) ≤ r` whenever
`Cap_D(E) < η` (FPT's modulus `ω`). Let `f` be bounded, measurable and quasi-continuous on `D`
(for every compact `L ⊆ D` and `ε > 0` there is an open `G` with `Cap_D(G) < ε` such that `f`
is continuous on `L \ G`; e.g. a difference of bounded plurisubharmonic functions, TN
`exists_isOpen_relCapacity_lt_continuousOn`). Then

* `∫ f dμ_j → ∫ f dν` (`tendsto_integral_of_quasiContinuousOn`);
* for every level `c` and `s > 0`, eventually `μ_j({f < c}) ≤ ν({f ≤ c + s}) + ε`
  (`eventually_measure_lt_le`), the upper half of FPT's moving-level-set convergence
  `eq:capacity-controlled-moving-level-sets` for a fixed weight.

*Proof.* The bound passes to `ν` on open sets by the open-set portmanteau inequality (TN
`measure_le_liminf_of_tendsto_integral`, FPT `prop:vague-set-inequalities`). Multiplying `f` by a
continuous cut-off equal to one on `K₀` makes it continuous off an open set of small capacity in
all of `ℂⁿ`, and TN's capacity-weighted convergence theorem (`tendsto_integral_of_quasiContinuousFor`,
the Tietze-extension argument of FPT) applies to the set function equal to `Cap_D` on open subsets
of `D` and to `∞` elsewhere. For the level sets, `𝟙_{(-∞,c)} ≤ σ ≤ 𝟙_{(-∞,c+s]}` for the
continuous piecewise linear `σ`, and `σ ∘ f` is again a bounded quasi-continuous weight.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ENNReal

namespace SGPT.Envelopes.MADirichlet

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.MongeAmpere
open SGPT.Foundations.Analysis.Pending.BedfordTaylor

variable {n : ℕ}

/-- Quasi-continuity on `D` with respect to `Cap_D`. -/
def IsQuasiContinuousOn (D : Opens (ComplexModel n)) (f : ComplexModel n → ℝ) : Prop :=
  ∀ L : Set (ComplexModel n), IsCompact L → L ⊆ D → ∀ ε : ℝ, 0 < ε →
    ∃ G : Set (ComplexModel n), IsOpen G ∧ relCapacity D G < ENNReal.ofReal ε ∧
      ContinuousOn f (L \ G)

/-- Bounded plurisubharmonic functions are quasi-continuous (TN). -/
theorem isQuasiContinuousOn_of_isLocallyBoundedPshOn {D : Opens (ComplexModel n)}
    {u : ComplexModel n → ℝ} (hu : IsLocallyBoundedPshOn D u) : IsQuasiContinuousOn D u :=
  fun _ hL hLD _ hε => IsLocallyBoundedPshOn.exists_isOpen_relCapacity_lt_continuousOn hu hL hLD hε

/-- Differences of quasi-continuous functions are quasi-continuous. -/
theorem IsQuasiContinuousOn.sub {D : Opens (ComplexModel n)} {f g : ComplexModel n → ℝ}
    (hf : IsQuasiContinuousOn D f) (hg : IsQuasiContinuousOn D g) :
    IsQuasiContinuousOn D fun x => f x - g x := by
  intro L hL hLD ε hε
  obtain ⟨G₁, hG₁, hc₁, hf₁⟩ := hf L hL hLD (ε / 2) (by positivity)
  obtain ⟨G₂, hG₂, hc₂, hg₂⟩ := hg L hL hLD (ε / 2) (by positivity)
  refine ⟨G₁ ∪ G₂, hG₁.union hG₂, ?_, ?_⟩
  · calc relCapacity D (G₁ ∪ G₂) ≤ relCapacity D G₁ + relCapacity D G₂ := relCapacity_union_le _ _ _
      _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := ENNReal.add_lt_add hc₁ hc₂
      _ = ENNReal.ofReal ε := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf
  · exact (hf₁.mono fun x hx => ⟨hx.1, fun h => hx.2 (Or.inl h)⟩).sub
      (hg₂.mono fun x hx => ⟨hx.1, fun h => hx.2 (Or.inr h)⟩)

/-- Composition with a continuous function preserves quasi-continuity. -/
theorem IsQuasiContinuousOn.comp {D : Opens (ComplexModel n)} {f : ComplexModel n → ℝ}
    (hf : IsQuasiContinuousOn D f) {σ : ℝ → ℝ} (hσ : Continuous σ) :
    IsQuasiContinuousOn D fun x => σ (f x) := by
  intro L hL hLD ε hε
  obtain ⟨G, hG, hc, hfc⟩ := hf L hL hLD ε hε
  exact ⟨G, hG, hc, hσ.comp_continuousOn hfc⟩

/-- **Fixed weights controlled by capacity** (FPT `lem:capacity-controlled-measure-weights`, first
assertion, for a fixed weight). -/
theorem tendsto_integral_of_quasiContinuousOn {D : Opens (ComplexModel n)}
    {K₀ : Set (ComplexModel n)} (hK₀ : IsCompact K₀) (hK₀D : K₀ ⊆ D)
    {μ : ℕ → Measure (ComplexModel n)} {ν : Measure (ComplexModel n)}
    [∀ j, IsFiniteMeasure (μ j)] [IsFiniteMeasure ν]
    (hμK : ∀ j, μ j K₀ᶜ = 0) (hνK : ν K₀ᶜ = 0)
    (hweak : ∀ h : ComplexModel n → ℝ, Continuous h → HasCompactSupport h →
      Tendsto (fun j => ∫ x, h x ∂μ j) atTop (𝓝 (∫ x, h x ∂ν)))
    (hmod : ∀ r : ℝ, 0 < r → ∃ η : ℝ≥0∞, 0 < η ∧ ∀ j, ∀ E : Set (ComplexModel n), E ⊆ D →
      relCapacity D E < η → μ j E ≤ ENNReal.ofReal r)
    {f : ComplexModel n → ℝ} (hfm : Measurable f) {B : ℝ} (hB : 0 ≤ B) (hfB : ∀ x, |f x| ≤ B)
    (hquasi : IsQuasiContinuousOn D f) :
    Tendsto (fun j => ∫ x, f x ∂μ j) atTop (𝓝 (∫ x, f x ∂ν)) := by
  classical
  -- a cut-off equal to one on `K₀`
  obtain ⟨δ, hδ, hδD⟩ := hK₀.exists_cthickening_subset_open D.isOpen hK₀D
  obtain ⟨χ, hχs, hχ01, hχ1, hχc, hχsupp⟩ := exists_smooth_cutoff hK₀ (r := δ / 4) (by positivity)
  have hχcont : Continuous χ := hχs.continuous
  have hχK : ∀ x ∈ K₀, χ x = 1 := fun x hx =>
    hχ1 (self_subset_cthickening K₀ hx)
  set O : Set (ComplexModel n) := thickening δ K₀ with hOdef
  have hOo : IsOpen O := isOpen_thickening
  set L : Set (ComplexModel n) := cthickening δ K₀ with hLdef
  have hLc : IsCompact L := hK₀.cthickening
  have hOL : O ⊆ L := thickening_subset_cthickening δ K₀
  have hLD : L ⊆ D := hδD
  have hsuppO : tsupport χ ⊆ O := hχsupp.trans
    (cthickening_subset_thickening' hδ (by linarith) K₀)
  -- measures carried by `K₀` do not see the cut-off
  have hae : ∀ m : Measure (ComplexModel n), m K₀ᶜ = 0 → ∀ᵐ x ∂m, x ∈ K₀ := fun m hm =>
    (measure_eq_zero_iff_ae_notMem.mp hm).mono fun x hx => by simpa using hx
  have hcut : ∀ m : Measure (ComplexModel n), m K₀ᶜ = 0 → ∀ g : ComplexModel n → ℝ,
      ∫ x, χ x * g x ∂m = ∫ x, g x ∂m := fun m hm g =>
    integral_congr_ae ((hae m hm).mono fun x hx => by simp [hχK x hx])
  -- the set function
  set cap : Set (ComplexModel n) → ℝ≥0∞ := fun A =>
    if IsOpen A ∧ A ⊆ D then relCapacity D A else ⊤ with hcapdef
  have hcontrol : CapacityWeightedConvergence.UniformCapacityControl cap μ ν := by
    intro r hr
    obtain ⟨η, hη, hsmall⟩ := hmod r hr
    refine ⟨η, hη, fun A _ hA => ?_⟩
    by_cases hAo : IsOpen A ∧ A ⊆ D
    · have hcapA : relCapacity D A < η := by simpa only [hcapdef, if_pos hAo] using hA
      refine ⟨fun j => hsmall j A hAo.2 hcapA, ?_⟩
      have hport := VaguePortmanteau.measure_le_liminf_of_tendsto_integral (Ω := D) hAo.1 hAo.2
        (fun j K _ _ => measure_lt_top (μ j) K) (fun K _ _ => measure_lt_top ν K)
        (fun φ hφ hφc _ => hweak φ hφ hφc)
      exact hport.trans (liminf_le_of_frequently_le' (Frequently.of_forall fun j =>
        hsmall j A hAo.2 hcapA))
    · simp only [hcapdef, if_neg hAo] at hA
      exact absurd hA (not_lt.mpr le_top)
  -- the cut weight
  set f' : ComplexModel n → ℝ := fun x => χ x * f x with hf'def
  have hf'm : Measurable f' := hχcont.measurable.mul hfm
  have hf'B : ∀ x, |f' x| ≤ B := fun x => by
    rw [hf'def, abs_mul, abs_of_nonneg (hχ01 x).1]
    exact (mul_le_of_le_one_left (abs_nonneg _) (hχ01 x).2).trans (hfB x)
  have hquasi' : CapacityWeightedConvergence.QuasiContinuousFor cap f' := by
    intro η hη
    obtain ⟨ε, hε, hεη⟩ : ∃ ε : ℝ, 0 < ε ∧ ENNReal.ofReal ε < η := by
      rcases eq_or_ne η ⊤ with h | h
      · exact ⟨1, one_pos, h ▸ ENNReal.ofReal_lt_top⟩
      · refine ⟨η.toReal / 2, by have := ENNReal.toReal_pos hη.ne' h; positivity, ?_⟩
        rw [ENNReal.ofReal_lt_iff_lt_toReal (by positivity) h]
        have := ENNReal.toReal_pos hη.ne' h
        linarith
    obtain ⟨G₀, hG₀, hcap₀, hfc⟩ := hquasi L hLc hLD ε hε
    refine ⟨G₀ ∩ O, hG₀.inter hOo, ?_, ?_⟩
    · have hsub : G₀ ∩ O ⊆ D := fun x hx => hLD (hOL hx.2)
      simp only [hcapdef, if_pos (And.intro (hG₀.inter hOo) hsub)]
      exact ((relCapacity_mono inter_subset_left).trans_lt hcap₀).trans hεη
    · intro x hx
      by_cases hxs : x ∈ tsupport χ
      · have hxO : x ∈ O := hsuppO hxs
        have hxG : x ∉ G₀ := fun h => hx ⟨h, hxO⟩
        have hwithin : ContinuousWithinAt f (G₀ ∩ O)ᶜ x := by
          have h1 : ContinuousWithinAt f (L \ G₀) x := hfc x ⟨hOL hxO, hxG⟩
          have h2 : (G₀ ∩ O)ᶜ ∩ O ⊆ L \ G₀ := fun y hy =>
            ⟨hOL hy.2, fun h => hy.1 ⟨h, hy.2⟩⟩
          exact (h1.mono h2).mono_of_mem_nhdsWithin
            (inter_mem_nhdsWithin _ (hOo.mem_nhds hxO))
        exact hχcont.continuousWithinAt.mul hwithin
      · have hzero : f' =ᶠ[𝓝 x] fun _ => 0 := by
          filter_upwards [(notMem_tsupport_iff_eventuallyEq.mp hxs)] with y hy
          simp [hf'def, hy]
        exact (continuousAt_const.congr hzero.symm).continuousWithinAt
  have hweak' : ∀ v : C(ComplexModel n, ℝ), Tendsto (fun j => ∫ x, v x ∂μ j) atTop
      (𝓝 (∫ x, v x ∂ν)) := by
    intro v
    have h := hweak (fun x => χ x * v x) (hχcont.mul v.continuous) (hχc.mul_right)
    rwa [hcut ν hνK v, funext fun j => hcut (μ j) (hμK j) v] at h
  have h := CapacityWeightedConvergence.tendsto_integral_of_quasiContinuousFor hcontrol hweak'
    hf'm hquasi' hB hf'B
  rwa [hcut ν hνK f, funext fun j => hcut (μ j) (hμK j) f] at h

/-- **Level sets** (FPT `eq:capacity-controlled-moving-level-sets`, upper half, fixed weight):
under the hypotheses of `tendsto_integral_of_quasiContinuousOn`, for every `c`, `s > 0` and
`ε > 0`, eventually `μ_j({f < c}) ≤ ν({f ≤ c + s}) + ε`. -/
theorem eventually_measure_lt_le {D : Opens (ComplexModel n)}
    {K₀ : Set (ComplexModel n)} (hK₀ : IsCompact K₀) (hK₀D : K₀ ⊆ D)
    {μ : ℕ → Measure (ComplexModel n)} {ν : Measure (ComplexModel n)}
    [∀ j, IsFiniteMeasure (μ j)] [IsFiniteMeasure ν]
    (hμK : ∀ j, μ j K₀ᶜ = 0) (hνK : ν K₀ᶜ = 0)
    (hweak : ∀ h : ComplexModel n → ℝ, Continuous h → HasCompactSupport h →
      Tendsto (fun j => ∫ x, h x ∂μ j) atTop (𝓝 (∫ x, h x ∂ν)))
    (hmod : ∀ r : ℝ, 0 < r → ∃ η : ℝ≥0∞, 0 < η ∧ ∀ j, ∀ E : Set (ComplexModel n), E ⊆ D →
      relCapacity D E < η → μ j E ≤ ENNReal.ofReal r)
    {f : ComplexModel n → ℝ} (hfm : Measurable f) (hquasi : IsQuasiContinuousOn D f)
    (c : ℝ) {s : ℝ} (hs : 0 < s) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j in atTop, μ j {x | f x < c} ≤ ν {x | f x ≤ c + s} + ENNReal.ofReal ε := by
  set σ : ℝ → ℝ := fun t => min 1 (max 0 ((c + s - t) / s)) with hσdef
  have hσc : Continuous σ := continuous_const.min (continuous_const.max
    ((continuous_const.sub continuous_id).div_const s))
  have hσ01 : ∀ t, 0 ≤ σ t ∧ σ t ≤ 1 := fun t => ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩
  have hσlow : ∀ t, t < c → σ t = 1 := fun t ht => by
    simp only [hσdef]
    refine min_eq_left ?_
    refine le_max_of_le_right ?_
    rw [le_div_iff₀ hs]; linarith
  have hσhigh : ∀ t, c + s < t → σ t = 0 := fun t ht => by
    simp only [hσdef]
    have : (c + s - t) / s ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hs.le
    rw [max_eq_left this, min_eq_right zero_le_one]
  have hlim := tendsto_integral_of_quasiContinuousOn hK₀ hK₀D hμK hνK hweak hmod
    (hσc.measurable.comp hfm) zero_le_one (fun x => by
      show |σ (f x)| ≤ 1
      rw [abs_of_nonneg (hσ01 _).1]; exact (hσ01 _).2) (hquasi.comp hσc)
  have hmeas_lt : MeasurableSet {x | f x < c} := measurableSet_lt hfm measurable_const
  have hmeas_le : MeasurableSet {x | f x ≤ c + s} := measurableSet_le hfm measurable_const
  have hint : ∀ m : Measure (ComplexModel n), IsFiniteMeasure m →
      Integrable (fun x => σ (f x)) m := fun m _ =>
    (integrable_const (1 : ℝ)).mono' (hσc.measurable.comp hfm).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hσ01 _).1]; exact (hσ01 _).2)
  have hup : ∫ x, σ (f x) ∂ν ≤ ν.real {x | f x ≤ c + s} := by
    rw [← integral_indicator_one hmeas_le]
    refine integral_mono (hint ν inferInstance) ((integrable_const (1 : ℝ)).indicator hmeas_le)
      fun x => ?_
    by_cases hx : f x ≤ c + s
    · rw [indicator_of_mem (show x ∈ {x | f x ≤ c + s} from hx)]; exact (hσ01 _).2
    · rw [indicator_of_notMem (show x ∉ {x | f x ≤ c + s} from hx), hσhigh _ (not_le.mp hx)]
  filter_upwards [(tendsto_order.1 hlim).2 _ (lt_add_of_pos_right (∫ x, σ (f x) ∂ν) hε)]
    with j hj
  have hlow : (μ j).real {x | f x < c} ≤ ∫ x, σ (f x) ∂μ j := by
    rw [← integral_indicator_one hmeas_lt]
    refine integral_mono ((integrable_const (1 : ℝ)).indicator hmeas_lt) (hint (μ j) inferInstance)
      fun x => ?_
    by_cases hx : f x < c
    · rw [indicator_of_mem (show x ∈ {x | f x < c} from hx)]; exact (hσlow _ hx).ge
    · rw [indicator_of_notMem (show x ∉ {x | f x < c} from hx)]; exact (hσ01 _).1
  calc μ j {x | f x < c} = ENNReal.ofReal ((μ j).real {x | f x < c}) :=
        (ofReal_measureReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal (ν.real {x | f x ≤ c + s} + ε) := by
        have hj' : ∫ x, σ (f x) ∂μ j < ∫ x, σ (f x) ∂ν + ε := hj
        exact ENNReal.ofReal_le_ofReal (by linarith)
    _ ≤ ENNReal.ofReal (ν.real {x | f x ≤ c + s}) + ENNReal.ofReal ε := ENNReal.ofReal_add_le
    _ = ν {x | f x ≤ c + s} + ENNReal.ofReal ε := by
        rw [ofReal_measureReal (measure_ne_top _ _)]

end SGPT.Envelopes.MADirichlet
