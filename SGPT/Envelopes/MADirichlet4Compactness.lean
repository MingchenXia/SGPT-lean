import SGPT.Envelopes.MADirichlet3Truncation
import SGPT.Foundations.Analysis.Pending.PshUltrafilterLimit
import SGPT.Foundations.Analysis.Pending.NaturalWeakPotentialHartogs
import SGPT.Foundations.Analysis.Pending.NaturalPshHartogsBallEstimate

/-!
# `L¹_loc` compactness of plurisubharmonic functions and Hartogs' lemma

Xia, *Foundations of pluripotential theory* (FPT), `thm:psh-compactness-hartogs`, in the form
needed for the convolution approximants of lane MA-DIR3.

* `exists_subseq_tendsto_localL1`: **compactness**. A sequence of plurisubharmonic functions on a
  connected open `Ω ⊆ ℂⁿ`, none identically `-∞`, bounded above by a common constant and with
  uniformly bounded `L¹` norms on every compact subset, has a subsequence converging in
  `L¹_loc(Ω)` to a plurisubharmonic function `v ≢ -∞`. (FPT states the dichotomy "locally
  uniformly to `-∞` or convergent in `L¹_loc`" for sequences locally uniformly bounded above; the
  `L¹` bound excludes the first alternative.) `L¹_loc` convergence is expressed as in TN and
  `SGPT.PSH.LocalL1Recovery`: `∫⁻_K d(u_j, v) → 0` for every compact `K ⊆ Ω`, where `d` is TN's
  canonical extended distance (`|a - b|` at finite values).

  *Proof.* TN's ultrafilter weak limit (`exists_isPshRepresentative_of_tendsto`) gives a
  plurisubharmonic `v` with `∫ φ u_j → ∫ φ v` along an ultrafilter `𝒰 ≤ atTop`, for every test
  function `φ`. TN's weak Hartogs lemma (`eventually_locally_le_of_weak_tests`) gives, for `x ∈ Ω`
  and `a > v(x)`, a ball around `x` and an event of `𝒰` on which `u_j ≤ a` on that ball. By
  Lindelöf's theorem countably many of these balls (for rational `a`) suffice, and countably many
  events of `𝒰`, together with the convergence events of countably many cut-offs, are
  eventually satisfied along a subsequence (`exists_strictMono_eventually_mem`). Along it
  `limsup u_{j_k} ≤ v` almost everywhere, so `∫ φ (u_{j_k} - v)₊ → 0` by dominated convergence,
  and `|t| = 2 t₊ - t`.
* `eventually_lt_of_tendsto_localL1`: **Hartogs' lemma** on compact sets for a constant majorant
  (FPT `thm:psh-compactness-hartogs`, second part, for constant `f`), from TN's ball version.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ENNReal Distributions

namespace SGPT.Envelopes.MADirichlet

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.MongeAmpere
open SGPT.Foundations.Analysis.Pending.BedfordTaylor

variable {n : ℕ}

/-- Countably many events of an ultrafilter on `ℕ` finer than `atTop` are eventually satisfied
along one subsequence. -/
theorem exists_strictMono_eventually_mem {U : Ultrafilter ℕ} (hU : (U : Filter ℕ) ≤ atTop)
    {𝓔 : Set (Set ℕ)} (h𝓔 : 𝓔.Countable) (hE : ∀ E ∈ 𝓔, E ∈ (U : Filter ℕ)) :
    ∃ s : ℕ → ℕ, StrictMono s ∧ ∀ E ∈ 𝓔, ∀ᶠ k in atTop, s k ∈ E := by
  rcases 𝓔.eq_empty_or_nonempty with rfl | hne
  · exact ⟨id, strictMono_id, fun E hE => absurd hE (notMem_empty E)⟩
  obtain ⟨e, he⟩ := h𝓔.exists_eq_range hne
  have hfreq : ∀ k : ℕ, ∃ᶠ i in atTop, i ∈ ⋂ c ∈ Finset.range (k + 1), e c := by
    intro k
    have hmem : (⋂ c ∈ Finset.range (k + 1), e c) ∈ (U : Filter ℕ) :=
      (Filter.biInter_finset_mem _).mpr fun c _ => hE _ (he ▸ mem_range_self c)
    exact (Filter.Eventually.frequently hmem).filter_mono hU
  obtain ⟨s, hs, hP⟩ := Filter.extraction_forall_of_frequently hfreq
  refine ⟨s, hs, fun E hEmem => ?_⟩
  rw [he] at hEmem
  obtain ⟨c, rfl⟩ := hEmem
  filter_upwards [eventually_ge_atTop c] with k hk
  exact (mem_iInter₂.mp (hP k)) c (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))

/-- **`L¹_loc` compactness of plurisubharmonic functions** (FPT `thm:psh-compactness-hartogs`,
first part, under an `L¹` bound). -/
theorem exists_subseq_tendsto_localL1 {Ω : Opens (ComplexModel n)}
    (hΩ : IsPreconnected (Ω : Set (ComplexModel n))) (u : ℕ → ComplexModel n → EReal)
    (hu : ∀ j, PlurisubharmonicOn (u j) Ω) (hne : ∀ j, ∃ a ∈ Ω, u j a ≠ ⊥) {C : ℝ}
    (hC : ∀ j, ∀ z ∈ Ω, u j z ≤ (C : EReal))
    (hbound : ∀ K : Set (ComplexModel n), IsCompact K → K ⊆ Ω →
      ∃ B : ℝ, ∀ j, ∫ x in K, |(u j x).toReal| ≤ B) :
    ∃ (v : ComplexModel n → EReal) (s : ℕ → ℕ), StrictMono s ∧ PlurisubharmonicOn v Ω ∧
      (∃ a ∈ Ω, v a ≠ ⊥) ∧
      ∀ K : Set (ComplexModel n), IsCompact K → K ⊆ Ω →
        Tendsto (fun k => ∫⁻ x in K, canonicalERealAbsDiff (u (s k) x) (v x)) atTop (𝓝 0) := by
  classical
  set 𝒰 : Ultrafilter ℕ := Ultrafilter.of atTop with h𝒰def
  have h𝒰 : (𝒰 : Filter ℕ) ≤ atTop := Ultrafilter.of_le atTop
  obtain ⟨T, v, hrep, hT⟩ :=
    PshUltrafilterLimit.exists_isPshRepresentative_of_tendsto volume hΩ 𝒰 u hu hne hbound
  obtain ⟨hv, hvfin, hvint, hTeq⟩ := hrep
  have hΩne : (Ω : Set (ComplexModel n)).Nonempty := (hne 0).imp fun a ha => ha.1
  have hΩm : MeasurableSet (Ω : Set (ComplexModel n)) := Ω.isOpen.measurableSet
  have hnv : ∃ a ∈ Ω, v a ≠ ⊥ := by
    have hpos : 0 < volume (Ω : Set (ComplexModel n)) := Ω.isOpen.measure_pos volume hΩne
    have hfin' : ∀ᵐ x ∂volume, x ∈ (Ω : Set (ComplexModel n)) → (v x ≠ ⊤ ∧ v x ≠ ⊥) :=
      (ae_restrict_iff' hΩm).mp hvfin
    by_contra hcon
    have hcon' : ∀ x ∈ Ω, v x = ⊥ := fun x hx => by_contra fun h => hcon ⟨x, hx, h⟩
    have : (Ω : Set (ComplexModel n)) ⊆ {x | ¬(x ∈ (Ω : Set (ComplexModel n)) →
        (v x ≠ ⊤ ∧ v x ≠ ⊥))} := fun x hx h => (h hx).2 (hcon' x hx)
    exact (hpos.trans_le (measure_mono this)).ne' (ae_iff.mp hfin')
  have hlim : ∀ φ : 𝓓(Ω, ℝ), Tendsto (fun i => ∫ z, φ z * (u i z).toReal) (𝒰 : Filter ℕ)
      (𝓝 (∫ z, φ z * (v z).toReal)) := by
    intro φ
    have h := hT φ
    simp only [pshRegularDistribution_apply] at h
    rwa [hTeq, regularDistribution_apply] at h
  -- Hartogs events
  have hH : ∀ (q : ℚ) (x : {x : ComplexModel n // x ∈ Ω ∧ v x < ((q : ℝ) : EReal)}),
      ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ i in (𝒰 : Filter ℕ), ∀ y ∈ ball (x : ComplexModel n) ε,
        u i y ≤ ((q : ℝ) : EReal) := by
    intro q x
    obtain ⟨ε, hε, -, hev⟩ := NaturalWeakPotentialHartogs.eventually_locally_le_of_weak_tests
      hu hv volume hΩ hne hnv hlim hC x.1 x.2.1 x.2.2
    exact ⟨ε, hε, hev⟩
  choose ε hε hev using hH
  have hcount : ∀ q : ℚ, ∃ S : Set {x : ComplexModel n // x ∈ Ω ∧ v x < ((q : ℝ) : EReal)},
      S.Countable ∧ ⋃ x ∈ S, ball (x : ComplexModel n) (ε q x) =
        ⋃ x : {x : ComplexModel n // x ∈ Ω ∧ v x < ((q : ℝ) : EReal)}, ball x.1 (ε q x) :=
    fun q => TopologicalSpace.isOpen_iUnion_countable _ fun _ => isOpen_ball
  choose S hSc hSU using hcount
  -- cut-offs along an exhaustion
  obtain ⟨W, -, hWrc, hWabs⟩ := exists_exhaustion Ω
  have hφex : ∀ m, ∃ φ : 𝓓(Ω, ℝ), (∀ x, 0 ≤ φ x) ∧
      ∀ x ∈ closure (W m : Set (ComplexModel n)), 1 ≤ φ x :=
    fun m => exists_nonneg_testFunction_one_le_on_compact (hWrc m).1 (hWrc m).2
  choose φ hφ0 hφ1 using hφex
  -- the countable family of events
  set Ev : ∀ q : ℚ, {x : ComplexModel n // x ∈ Ω ∧ v x < ((q : ℝ) : EReal)} → Set ℕ :=
    fun q x => {i | ∀ y ∈ ball (x : ComplexModel n) (ε q x), u i y ≤ ((q : ℝ) : EReal)} with hEvdef
  set Wk : ℕ × ℕ → Set ℕ := fun p =>
    {i | dist (∫ z, φ p.1 z * (u i z).toReal) (∫ z, φ p.1 z * (v z).toReal) <
      1 / ((p.2 : ℝ) + 1)} with hWkdef
  set 𝓔 : Set (Set ℕ) := (⋃ q : ℚ, Ev q '' S q) ∪ range Wk with h𝓔def
  have h𝓔c : 𝓔.Countable :=
    (countable_iUnion fun q => (hSc q).image _).union (countable_range _)
  have h𝓔U : ∀ E ∈ 𝓔, E ∈ (𝒰 : Filter ℕ) := by
    rintro E (hE | hE)
    · obtain ⟨q, hq⟩ := mem_iUnion.mp hE
      obtain ⟨x, -, rfl⟩ := hq
      exact hev q x
    · obtain ⟨p, rfl⟩ := hE
      exact (hlim (φ p.1)).eventually (ball_mem_nhds _ (by positivity))
  obtain ⟨s, hs, hsE⟩ := exists_strictMono_eventually_mem h𝒰 h𝓔c h𝓔U
  refine ⟨v, s, hs, hv, hnv, fun K hK hKΩ => ?_⟩
  obtain ⟨m, hKm⟩ := hWabs K hK hKΩ
  set ψ : 𝓓(Ω, ℝ) := φ m with hψdef
  have hψ0 : ∀ x, 0 ≤ ψ x := hφ0 m
  have hψK : ∀ x ∈ K, 1 ≤ ψ x := fun x hx => hφ1 m x (subset_closure (hKm hx))
  have hψΩ : ∀ x, x ∉ (Ω : Set (ComplexModel n)) → ψ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (ψ.tsupport_subset h)
  -- real representatives
  set f : ℕ → ComplexModel n → ℝ := fun k x => (u (s k) x).toReal with hfdef
  set g : ComplexModel n → ℝ := fun x => (v x).toReal with hgdef
  have hfloc : ∀ k, LocallyIntegrableOn (f k) (Ω : Set (ComplexModel n)) volume := fun k =>
    (hu (s k)).locallyIntegrableOn_toReal volume hΩ (hne (s k))
  have hgloc : LocallyIntegrableOn g (Ω : Set (ComplexModel n)) volume := hvint
  have hfi : ∀ k, Integrable (fun z => ψ z * f k z) := fun k => by
    simpa only [ContinuousLinearMap.mul_apply'] using
      ψ.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ) (hfloc k)
  have hgi : Integrable (fun z => ψ z * g z) := by
    simpa only [ContinuousLinearMap.mul_apply'] using
      ψ.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ) hgloc
  set h : ℕ → ComplexModel n → ℝ := fun k z => ψ z * f k z - ψ z * g z with hhdef
  have hhi : ∀ k, Integrable (h k) := fun k => (hfi k).sub hgi
  -- almost everywhere finiteness
  have hfinu : ∀ᵐ x ∂volume, x ∈ (Ω : Set (ComplexModel n)) →
      ∀ j, u j x ≠ ⊤ ∧ u j x ≠ ⊥ := by
    have : ∀ j, ∀ᵐ x ∂volume, x ∈ (Ω : Set (ComplexModel n)) → (u j x ≠ ⊤ ∧ u j x ≠ ⊥) :=
      fun j => (ae_restrict_iff' hΩm).mp ((hu j).ae_finite volume hΩ (hne j))
    filter_upwards [ae_all_iff.mpr this] with x hx hxΩ j using hx j hxΩ
  have hfinv : ∀ᵐ x ∂volume, x ∈ (Ω : Set (ComplexModel n)) → (v x ≠ ⊤ ∧ v x ≠ ⊥) :=
    (ae_restrict_iff' hΩm).mp hvfin
  -- the signed integrals tend to zero
  have hsigned : Tendsto (fun k => ∫ z, h k z) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => ∫ z, ψ z * f k z) atTop (𝓝 (∫ z, ψ z * g z)) := by
      rw [Metric.tendsto_atTop]
      intro δ hδ
      obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
      have hmem : Wk (m, N) ∈ 𝓔 := Or.inr (mem_range_self _)
      obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp (hsE _ hmem)
      exact ⟨k₀, fun k hk => (hk₀ k hk).trans hN⟩
    have h2 : (fun k => ∫ z, h k z) = fun k => (∫ z, ψ z * f k z) - ∫ z, ψ z * g z :=
      funext fun k => integral_sub (hfi k) hgi
    rw [h2]
    simpa using h1.sub_const (∫ z, ψ z * g z)
  -- the positive parts tend to zero
  have hpos : Tendsto (fun k => ∫ z, max (h k z) 0) atTop (𝓝 0) := by
    have hdom : Integrable (fun z => |C| * ψ z + |ψ z * g z|) :=
      ((ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport).const_mul |C|).add
        hgi.abs
    have := tendsto_integral_of_dominated_convergence (μ := volume)
      (F := fun k z => max (h k z) 0) (f := fun _ => (0 : ℝ))
      (fun z => |C| * ψ z + |ψ z * g z|)
      (fun k => ((hhi k).pos_part).aestronglyMeasurable) hdom ?_ ?_
    · simpa using this
    · intro k
      filter_upwards [hfinu] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      refine max_le ?_ (add_nonneg (mul_nonneg (abs_nonneg C) (hψ0 x)) (abs_nonneg _))
      by_cases hxΩ : x ∈ (Ω : Set (ComplexModel n))
      · have hfC : f k x ≤ C := by
          have h1 := hC (s k) x hxΩ
          rw [← EReal.coe_toReal (hx hxΩ (s k)).1 (hx hxΩ (s k)).2] at h1
          exact EReal.coe_le_coe_iff.mp h1
        have h2 : h k x = ψ x * (f k x - g x) := by simp only [hhdef]; ring
        rw [h2]
        calc ψ x * (f k x - g x) ≤ ψ x * (|C| + |g x|) :=
              mul_le_mul_of_nonneg_left (by linarith [le_abs_self C, neg_abs_le (g x)]) (hψ0 x)
          _ = |C| * ψ x + |ψ x * g x| := by rw [abs_mul, abs_of_nonneg (hψ0 x)]; ring
      · simp only [hhdef, hψΩ x hxΩ, zero_mul, sub_zero]
        exact add_nonneg (mul_nonneg (abs_nonneg C) le_rfl) (abs_nonneg _)
    · filter_upwards [hfinu, hfinv] with x hxu hxv
      by_cases hxΩ : x ∈ (Ω : Set (ComplexModel n))
      · have hgx : (g x : EReal) = v x := EReal.coe_toReal (hxv hxΩ).1 (hxv hxΩ).2
        have hkey : ∀ δ : ℝ, 0 < δ → ∀ᶠ k in atTop, f k x < g x + δ := by
          intro δ hδ
          obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show g x < g x + δ by linarith)
          have hxq : x ∈ Ω ∧ v x < ((q : ℝ) : EReal) :=
            ⟨hxΩ, by rw [← hgx]; exact EReal.coe_lt_coe_iff.mpr hq1⟩
          have hxU : x ∈ ⋃ x' ∈ S q, ball (x' : ComplexModel n) (ε q x') := by
            rw [hSU q]
            exact mem_iUnion.mpr ⟨⟨x, hxq⟩, mem_ball_self (hε q _)⟩
          obtain ⟨x', hx'S, hxx'⟩ := mem_iUnion₂.mp hxU
          have hmem : Ev q x' ∈ 𝓔 := Or.inl (mem_iUnion.mpr ⟨q, mem_image_of_mem _ hx'S⟩)
          filter_upwards [hsE _ hmem] with k hk
          have h1 : u (s k) x ≤ ((q : ℝ) : EReal) := hk x hxx'
          rw [← EReal.coe_toReal (hxu hxΩ (s k)).1 (hxu hxΩ (s k)).2] at h1
          exact (EReal.coe_le_coe_iff.mp h1).trans_lt hq2
        have hmax : Tendsto (fun k => max (f k x - g x) 0) atTop (𝓝 0) := by
          refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun k =>
            ha.trans_le (le_max_right _ _), fun a ha => ?_⟩
          filter_upwards [hkey a ha] with k hk
          exact max_lt (by linarith) ha
        have heq : (fun k => max (h k x) 0) = fun k => ψ x * max (f k x - g x) 0 := by
          funext k
          rw [mul_max_of_nonneg _ _ (hψ0 x), mul_zero]
          congr 1
          simp only [hhdef]; ring
        rw [heq]
        simpa using hmax.const_mul (ψ x)
      · have : (fun k => max (h k x) 0) = fun _ => (0 : ℝ) := by
          funext k
          simp [hhdef, hψΩ x hxΩ]
        rw [this]
        exact tendsto_const_nhds
  -- conclusion
  have habs : Tendsto (fun k => ∫ z, |h k z|) atTop (𝓝 0) := by
    have heq : (fun k => ∫ z, |h k z|) = fun k => 2 * (∫ z, max (h k z) 0) - ∫ z, h k z := by
      funext k
      rw [← integral_const_mul, ← integral_sub ((hhi k).pos_part.const_mul 2) (hhi k)]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      show |h k z| = 2 * max (h k z) 0 - h k z
      rcases le_total 0 (h k z) with h0 | h0
      · rw [abs_of_nonneg h0, max_eq_left h0]; ring
      · rw [abs_of_nonpos h0, max_eq_right h0]; ring
    rw [heq]
    simpa using (hpos.const_mul 2).sub hsigned
  have hbd : ∀ k, ∫⁻ x in K, canonicalERealAbsDiff (u (s k) x) (v x) ≤
      ENNReal.ofReal (∫ z, |h k z|) := by
    intro k
    calc ∫⁻ x in K, canonicalERealAbsDiff (u (s k) x) (v x)
        = ∫⁻ x in K, ENNReal.ofReal |f k x - g x| := by
          refine lintegral_congr_ae ?_
          have h1 : ∀ᵐ x ∂volume.restrict K, ∀ j, u j x ≠ ⊤ ∧ u j x ≠ ⊥ :=
            (ae_restrict_iff' hK.measurableSet).mpr
              (hfinu.mono fun x hx hxK => hx (hKΩ hxK))
          have h2 : ∀ᵐ x ∂volume.restrict K, v x ≠ ⊤ ∧ v x ≠ ⊥ :=
            (ae_restrict_iff' hK.measurableSet).mpr
              (hfinv.mono fun x hx hxK => hx (hKΩ hxK))
          filter_upwards [h1, h2] with x hxu hxv
          simpa only [EReal.coe_toReal (hxu (s k)).1 (hxu (s k)).2,
            EReal.coe_toReal hxv.1 hxv.2] using
            canonicalERealAbsDiff_coe_coe (u (s k) x).toReal (v x).toReal
      _ ≤ ∫⁻ x in K, ENNReal.ofReal |h k x| := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
          refine ENNReal.ofReal_le_ofReal ?_
          have h2 : h k x = ψ x * (f k x - g x) := by simp only [hhdef]; ring
          rw [h2, abs_mul, abs_of_nonneg (hψ0 x)]
          exact le_mul_of_one_le_left (abs_nonneg _) (hψK x hx)
      _ ≤ ∫⁻ x, ENNReal.ofReal |h k x| := setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal (∫ z, |h k z|) :=
          (ofReal_integral_eq_lintegral_ofReal (hhi k).abs
            (Eventually.of_forall fun z => abs_nonneg _)).symm
  have hupper : Tendsto (fun k => ENNReal.ofReal (∫ z, |h k z|)) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal habs
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun _ => zero_le) hbd

/-- **Hartogs' lemma** (FPT `thm:psh-compactness-hartogs`, second part, for a constant majorant):
if plurisubharmonic `u_j → v` in `L¹_loc(Ω)` and `v < A` on a compact `K ⊆ Ω`, then `u_j < A` on
`K` for all large `j`. -/
theorem eventually_lt_of_tendsto_localL1 {Ω : Opens (ComplexModel n)}
    (hΩ : IsPreconnected (Ω : Set (ComplexModel n))) {u : ℕ → ComplexModel n → EReal}
    {v : ComplexModel n → EReal} (hu : ∀ j, PlurisubharmonicOn (u j) Ω)
    (hv : PlurisubharmonicOn v Ω) (hne : ∀ j, ∃ a ∈ Ω, u j a ≠ ⊥) (hnv : ∃ a ∈ Ω, v a ≠ ⊥)
    (hlim : ∀ K : Set (ComplexModel n), IsCompact K → K ⊆ Ω →
      Tendsto (fun k => ∫⁻ x in K, canonicalERealAbsDiff (u k x) (v x)) atTop (𝓝 0))
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKΩ : K ⊆ Ω) {A : ℝ}
    (hA : ∀ x ∈ K, v x < (A : EReal)) :
    ∀ᶠ j in atTop, ∀ x ∈ K, u j x < (A : EReal) := by
  have hloc : ∀ x ∈ K, ∃ r : ℝ, 0 < r ∧ ∀ᶠ j in atTop, ∀ y ∈ ball x r, u j y < (A : EReal) := by
    intro x hx
    obtain ⟨b, hvb, hbA⟩ := EReal.exists_rat_btwn_of_lt (hA x hx)
    have husc : ∀ᶠ y in 𝓝 x, v y < ((b : ℝ) : EReal) :=
      (hv x (hKΩ hx)).upperSemicontinuousAt _ hvb
    obtain ⟨ρ, hρ, hρb⟩ := Metric.eventually_nhds_iff.mp
      (husc.and (Ω.isOpen.mem_nhds (hKΩ hx)))
    set r := ρ / 4 with hrdef
    have hr : 0 < r := by positivity
    have hsub : closedBall x (3 * r) ⊆ ball x ρ :=
      closedBall_subset_ball (by rw [hrdef]; linarith)
    have hbA' : (b : ℝ) < A := EReal.coe_lt_coe_iff.mp hbA
    have hev := NaturalPshHartogsBallEstimate.eventually_le_on_ball_of_lintegral_canonical_tendsto
      hu hv hΩ hne hnv volume x (r := r) (A := (b : ℝ)) (δ := (A - b) / 2) hr
      (fun y hy => (hρb (hsub hy)).2) (fun y hy => (hρb (hsub hy)).1.le)
      (hlim _ (isCompact_closedBall x _) fun y hy => (hρb (hsub hy)).2) (by linarith)
    refine ⟨r, hr, hev.mono fun j hj y hy => (hj y hy).trans_lt ?_⟩
    exact EReal.coe_lt_coe_iff.mpr (by linarith)
  choose! r hr hev using hloc
  obtain ⟨t, htK, hcover⟩ := hK.elim_nhds_subcover (fun x => ball x (r x))
    fun x hx => ball_mem_nhds x (hr x hx)
  have hall : ∀ᶠ j in atTop, ∀ x ∈ t, ∀ y ∈ ball x (r x), u j y < (A : EReal) :=
    (eventually_all_finset t).mpr fun x hx => hev x (htK x hx)
  filter_upwards [hall] with j hj y hy
  obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.mp (hcover hy)
  exact hj x hxt y hyx

end SGPT.Envelopes.MADirichlet
