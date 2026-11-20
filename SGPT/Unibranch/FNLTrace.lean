import SGPT.Unibranch.FNLPuiseux
import SGPT.Foundations.Analysis.Pending.PshAnalyticRemovable

/-!
# FN80 Lemma 5.1: the trace of a weakly plurisubharmonic function is plurisubharmonic

Source: `[FN80]` (Fornæss–Narasimhan, Math. Ann. 248 (1980)), Lemma 5.1, used for SGPT
`thm:FN` (`appendix_unibranch.tex`), implication (2) ⇒ (1) on singular spaces.

**Lemma 5.1.** Let `X` be a pure `k`-dimensional closed subvariety of `Δⁿ` such that the
projection `π : X → Δᵏ` is a finite `λ`-sheeted branched covering, and let `φ ∈ WP(X)`.
Then `tr φ(z) = ∑_{p ∈ π⁻¹(z)} φ(p)` (points counted with multiplicity) is plurisubharmonic.

We prove this for every finite branched covering `π : X → D` of an open set `D ⊆ ℂᵏ`
(`IsBranchedCovering`), with the multiplicity of a point given by its sheet number
(`sheetNumber`): `IsBranchedCovering.discPshOn_trace`.

Proof (as in `[FN80]`): off the branch hypersurface `{δ = 0}` the trace is a finite sum of
pull-backs of `φ` by holomorphic sections, hence plurisubharmonic; it is locally bounded above,
so (Demailly, CADG I.5.24, `PshAnalyticRemovable.plurisubharmonicOn_extension_of_zeroLocus`)
its upper regularized extension across `{δ = 0}` is plurisubharmonic, and it remains to see
that this extension is the trace:

* `≥`: the trace is bounded by the nearby generic traces through the Puiseux discs of a complex
  line meeting `{δ = 0}` only at the point (`trace_le_of_eventually_le`, the sub-mean value
  inequality for the subharmonic function `s ↦ ∑ φ(G_x(s))`);
* `≤`: upper semicontinuity of `φ` and the definition of sheet numbers
  (`eventually_trace_lt`).
-/

set_option autoImplicit false

open Set Filter Metric TopologicalSpace
open scoped Topology

noncomputable section

namespace SGPT.Unibranch.FNL

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending

/-- Finite sums of disc-subharmonic functions are disc-subharmonic. -/
theorem discPshOn_finset_sum {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {U : Set E}
    (s : Finset ι) (u : ι → E → EReal) (hu : ∀ i ∈ s, DiscPshOn (u i) U) :
    DiscPshOn (fun y => ∑ i ∈ s, u i y) U := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using discPshOn_const (0 : EReal) (by simp) U
  | insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    exact (hu j (Finset.mem_insert_self j s)).add
      (ih fun i hi => hu i (Finset.mem_insert_of_mem hi))

/-- A sum of two terms `< ⊤` below `c` splits into two real bounds. -/
theorem EReal.exists_real_add_lt {x y c : EReal} (hx : x ≠ ⊤) (hy : y ≠ ⊤) (h : x + y < c) :
    ∃ u v : ℝ, x < u ∧ y < v ∧ ((u + v : ℝ) : EReal) < c := by
  obtain ⟨c', hc', hc'c⟩ := EReal.exists_between_coe_real h
  by_cases hxb : x = ⊥
  · obtain ⟨v, hyv, -⟩ := EReal.exists_between_coe_real (lt_top_iff_ne_top.mpr hy)
    refine ⟨c' - v - 1, v, by rw [hxb]; exact EReal.bot_lt_coe _, hyv, ?_⟩
    refine lt_trans ?_ hc'c
    exact EReal.coe_lt_coe_iff.mpr (by linarith)
  by_cases hyb : y = ⊥
  · obtain ⟨u, hxu, -⟩ := EReal.exists_between_coe_real (lt_top_iff_ne_top.mpr hx)
    refine ⟨u, c' - u - 1, hxu, by rw [hyb]; exact EReal.bot_lt_coe _, ?_⟩
    refine lt_trans ?_ hc'c
    exact EReal.coe_lt_coe_iff.mpr (by linarith)
  have hx' : x = (x.toReal : EReal) := (EReal.coe_toReal hx hxb).symm
  have hy' : y = (y.toReal : EReal) := (EReal.coe_toReal hy hyb).symm
  rw [hx', hy', ← EReal.coe_add, EReal.coe_lt_coe_iff] at hc'
  set d := (c' - x.toReal - y.toReal) / 3 with hd
  have hdpos : 0 < d := by rw [hd]; linarith
  refine ⟨x.toReal + d, y.toReal + d, ?_, ?_, ?_⟩
  · have h1 := EReal.coe_lt_coe_iff.mpr (show x.toReal < x.toReal + d by linarith)
    rwa [← hx'] at h1
  · have h1 := EReal.coe_lt_coe_iff.mpr (show y.toReal < y.toReal + d by linarith)
    rwa [← hy'] at h1
  · refine lt_trans ?_ hc'c
    exact EReal.coe_lt_coe_iff.mpr (by linarith)

theorem EReal.nsmul_ne_top {a : EReal} (ha : a ≠ ⊤) (m : ℕ) : m • a ≠ ⊤ := by
  induction m with
  | zero => simp
  | succ m ih => rw [succ_nsmul]; exact EReal.add_ne_top ih ha

theorem EReal.sum_ne_top {ι : Type*} (T : Finset ι) (f : ι → EReal) (hf : ∀ i ∈ T, f i ≠ ⊤) :
    ∑ i ∈ T, f i ≠ ⊤ := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert j T hj ih =>
    rw [Finset.sum_insert hj]
    exact EReal.add_ne_top (hf j (Finset.mem_insert_self j T))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- Real upper bounds for a weighted finite sum of terms `< ⊤` below `c`. -/
theorem EReal.exists_real_gt_sum_lt {ι : Type*} (T : Finset ι) (a : ι → EReal)
    (ha : ∀ i ∈ T, a i ≠ ⊤) (m : ι → ℕ) {c : EReal} (h : ∑ i ∈ T, m i • a i < c) :
    ∃ b : ι → ℝ, (∀ i ∈ T, a i < b i) ∧ ∑ i ∈ T, m i • ((b i : ℝ) : EReal) < c := by
  classical
  induction T using Finset.induction_on generalizing c with
  | empty => exact ⟨0, by simp, by simpa using h⟩
  | insert j T hj ih =>
    rw [Finset.sum_insert hj] at h
    have hT : ∀ i ∈ T, a i ≠ ⊤ := fun i hi => ha i (Finset.mem_insert_of_mem hi)
    have haj : a j ≠ ⊤ := ha j (Finset.mem_insert_self j T)
    obtain ⟨u, v, hu, hv, huv⟩ := EReal.exists_real_add_lt (EReal.nsmul_ne_top haj (m j))
      (EReal.sum_ne_top T _ fun i hi => EReal.nsmul_ne_top (hT i hi) (m i)) h
    obtain ⟨b, hb, hbv⟩ := ih hT hv
    -- the value at `j`
    obtain ⟨bj, hbj, hbjm⟩ : ∃ bj : ℝ, a j < bj ∧ m j • ((bj : ℝ) : EReal) + ((v : ℝ) : EReal) ≤
        ((u + v : ℝ) : EReal) := by
      rcases Nat.eq_zero_or_pos (m j) with hm | hm
      · obtain ⟨bj, hbj, -⟩ := EReal.exists_between_coe_real (lt_top_iff_ne_top.mpr haj)
        refine ⟨bj, hbj, ?_⟩
        rw [hm, zero_nsmul, zero_add]
        rw [hm, zero_nsmul] at hu
        exact EReal.coe_le_coe_iff.mpr (by linarith [EReal.coe_pos.mp hu])
      · refine ⟨u / m j, ?_, ?_⟩
        · by_cases hab : a j = ⊥
          · rw [hab]; exact EReal.bot_lt_coe _
          · have hae : a j = ((a j).toReal : EReal) := (EReal.coe_toReal haj hab).symm
            rw [hae, ← EReal.coe_nsmul, EReal.coe_lt_coe_iff, nsmul_eq_mul] at hu
            rw [hae, EReal.coe_lt_coe_iff, lt_div_iff₀ (by exact_mod_cast hm)]
            linarith
        · rw [← EReal.coe_nsmul, nsmul_eq_mul, ← EReal.coe_add, EReal.coe_le_coe_iff]
          rw [mul_div_cancel₀ _ (by exact_mod_cast hm.ne')]
    refine ⟨Function.update b j bj, ?_, ?_⟩
    · intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · simpa using hbj
      · have hij : i ≠ j := fun h => hj (h ▸ hi)
        rw [Function.update_of_ne hij]
        exact hb i hi
    · rw [Finset.sum_insert hj, Function.update_self]
      have hrest : ∑ i ∈ T, m i • ((Function.update b j bj i : ℝ) : EReal) =
          ∑ i ∈ T, m i • ((b i : ℝ) : EReal) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        have hij : i ≠ j := fun h => hj (h ▸ hi)
        rw [Function.update_of_ne hij]
      rw [hrest]
      calc m j • ((bj : ℝ) : EReal) + ∑ i ∈ T, m i • ((b i : ℝ) : EReal)
          < m j • ((bj : ℝ) : EReal) + ((v : ℝ) : EReal) := by
            have hne : m j • ((bj : ℝ) : EReal) = ((m j • bj : ℝ) : EReal) :=
              (EReal.coe_nsmul _ _).symm
            rw [hne]
            exact EReal.add_lt_add_left_coe hbv _
        _ ≤ ((u + v : ℝ) : EReal) := hbjm
        _ < c := huv

variable {n k : ℕ}
variable {X : Set (ComplexModel n)} {π : ComplexModel n →L[ℂ] ComplexModel k}
  {D : Set (ComplexModel k)} {deg : ℕ} {δ : ComplexModel k → ℂ}

namespace IsBranchedCovering

variable (hX : IsBranchedCovering X π D deg δ)
include hX

/-- Over a generic point the trace is the plain fibre sum, read through any enumeration of
the fibre. -/
theorem trace_eq_sum_of_bijOn {z : ComplexModel k} (hδ : δ z ≠ 0)
    (φ : ComplexModel n → EReal) {ι : Type*} (S : Finset ι) (f : ι → ComplexModel n)
    (hf : BijOn f (S : Set ι) (fibre X π z)) : trace X π δ φ z = ∑ i ∈ S, φ (f i) := by
  rw [trace, ← finsum_mem_coe_finset]
  symm
  apply finsum_mem_eq_of_bijOn f hf
  intro i hi
  have hπ : π (f i) = z := (hf.1 hi).2
  rw [hX.sheetNumber_eq_one (hf.1 hi).1 (by rw [hπ]; exact hδ), one_nsmul]

/-- A separation radius for the points of a finite fibre. -/
theorem eventually_separated {z₀ : ComplexModel k} (hz₀ : z₀ ∈ D) (p : ComplexModel n) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ p' ∈ fibre X π z₀, p' ≠ p → 2 * ε < dist p p' := by
  refine ((hX.finite_fibre z₀ hz₀).eventually_all).mpr fun p' _ => ?_
  by_cases hpp : p' = p
  · exact Eventually.of_forall fun _ h => absurd hpp h
  · have hd : 0 < dist p p' := dist_pos.mpr (Ne.symm hpp)
    filter_upwards [Ioo_mem_nhdsGT (half_pos hd)] with ε hε _
    linarith [hε.2]

/-- **The line argument of `[FN80]` Lemma 5.1**: the trace at `z₀` is bounded by every real
bound of the nearby generic traces. -/
theorem trace_le_of_eventually_le {z₀ : ComplexModel k} (hz₀ : z₀ ∈ D)
    {φ : ComplexModel n → EReal} (hφ : IsWeaklyPSHOn X φ) {C : ℝ}
    (h : ∀ᶠ z in 𝓝[{w | δ w ≠ 0}] z₀, trace X π δ φ z ≤ C) : trace X π δ φ z₀ ≤ C := by
  classical
  obtain ⟨e, ρ, hρ, hline, hgen⟩ := hX.exists_line hz₀
  obtain ⟨M, r, F₀, G, hM, hr, hGd, hGX, hG0, hgen', hbij⟩ :=
    hX.exists_puiseux_discs hline hgen hρ
  set U : ℂ → EReal := fun s => ∑ x ∈ F₀, φ (G x s) with hUdef
  have hU : DiscPshOn U (ball 0 r) := discPshOn_finset_sum F₀ _ fun x hx =>
    hφ.discPshOn_comp isOpen_ball (hGd x hx) (fun s hs => hGX x hx s hs)
  have hUs : ∀ s ∈ ball (0 : ℂ) r, s ≠ 0 → U s = trace X π δ φ (z₀ + s ^ M • e) :=
    fun s hs hs0 => (hX.trace_eq_sum_of_bijOn (hgen' s hs hs0).2 φ F₀ (fun x => G x s)
      (hbij s hs hs0)).symm
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h
  obtain ⟨η, hη, hηh⟩ := h
  have hcont : Continuous (fun s : ℂ => z₀ + s ^ M • e) := by fun_prop
  obtain ⟨r', hr', hr'h⟩ := Metric.continuous_iff.mp hcont 0 η hη
  have hr'' : 0 < min r r' := lt_min hr hr'
  have hU' : DiscPshOn U (ball 0 (min r r')) := hU.mono (ball_subset_ball (min_le_left _ _))
  have hbound : ∀ s ∈ ball (0 : ℂ) (min r r'), s ≠ 0 → U s ≤ C := by
    intro s hs hs0
    have hsr : s ∈ ball (0 : ℂ) r := ball_subset_ball (min_le_left _ _) hs
    rw [hUs s hsr hs0]
    apply hηh
    · have := hr'h s (lt_of_lt_of_le (mem_ball.mp hs) (min_le_right _ _))
      simpa [zero_pow hM.ne'] using this
    · exact (hgen' s hsr hs0).2
  have hU0 := le_of_forall_punctured_le hr'' hU' hbound
  suffices hcenter : U 0 = trace X π δ φ z₀ by rw [← hcenter]; exact hU0
  -- the central value: sheet numbers are the numbers of Puiseux discs through a point
  have hsheet : ∀ p ∈ fibre X π z₀, sheetNumber X π δ p = (F₀.filter (fun x => G x 0 = p)).card := by
    intro p hp
    have hpz : π p = z₀ := hp.2
    obtain ⟨m, hm⟩ := hX.exists_isSheetNumber hp.1
    rw [sheetNumber_eq (hX.neBot_generic (hX.mem_base hp.1)) hm]
    obtain ⟨ε, ⟨hεm, hεsep⟩, hεpos⟩ :=
      ((hm.and (hX.eventually_separated hz₀ p)).and self_mem_nhdsWithin).exists
    have hε : (0 : ℝ) < ε := hεpos
    rw [hpz, eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hεm
    obtain ⟨η', hη', hη'h⟩ := hεm
    have hGc : ∀ x ∈ F₀, ContinuousAt (G x) 0 := fun x hx =>
      ((hGd x hx).differentiableAt (ball_mem_nhds 0 hr)).continuousAt
    have hev : ∀ᶠ s in 𝓝[≠] (0 : ℂ), s ≠ 0 ∧ s ∈ ball (0 : ℂ) r ∧
        dist (z₀ + s ^ M • e) z₀ < η' ∧ ∀ x ∈ F₀, G x s ∈ ball (G x 0) ε := by
      refine Filter.Eventually.and self_mem_nhdsWithin (nhdsWithin_le_nhds ?_)
      refine Filter.Eventually.and (ball_mem_nhds (0 : ℂ) hr) (Filter.Eventually.and ?_ ?_)
      · have := (hcont.tendsto 0).eventually (ball_mem_nhds _ hη')
        simpa [zero_pow hM.ne'] using this
      · exact (Filter.eventually_all_finset F₀).mpr fun x hx =>
          (hGc x hx).preimage_mem_nhds (ball_mem_nhds _ hε)
    obtain ⟨s, hs0, hsr, hsη, hsG⟩ := hev.exists
    set z := z₀ + s ^ M • e with hzdef
    have hcount := hη'h hsη (hgen' s hsr hs0).2
    have hset : fibre X π z ∩ ball p ε =
        (fun x => G x s) '' ((F₀.filter (fun x => G x 0 = p) : Finset _) : Set (ComplexModel n)) := by
      ext y
      constructor
      · rintro ⟨hy, hyp⟩
        obtain ⟨x, hx, rfl⟩ := (hbij s hsr hs0).2.2 hy
        refine ⟨x, ?_, rfl⟩
        rw [Finset.coe_filter]
        refine ⟨hx, ?_⟩
        by_contra hne
        have hsep := hεsep (G x 0) (hG0 x hx) hne
        have h1 : dist (G x s) p < ε := hyp
        have h2 : dist (G x s) (G x 0) < ε := hsG x hx
        linarith [dist_triangle p (G x s) (G x 0), dist_comm p (G x s)]
      · rintro ⟨x, hx, rfl⟩
        rw [Finset.coe_filter] at hx
        refine ⟨(hbij s hsr hs0).1 hx.1, ?_⟩
        have := hsG x hx.1
        rwa [hx.2] at this
    rw [← hcount, hset, ((hbij s hsr hs0).2.1.mono (by
      intro x hx
      rw [Finset.coe_filter] at hx
      exact hx.1)).ncard_image, Set.ncard_coe_finset]
  have hfin := hX.finite_fibre z₀ hz₀
  rw [trace, finsum_mem_eq_finite_toFinset_sum _ hfin]
  simp only [hUdef]
  rw [Finset.sum_comp (fun p => φ p) (fun x => G x 0)]
  symm
  have himg : F₀.image (fun x => G x 0) ⊆ hfin.toFinset := by
    intro p hp
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
    exact (hfin.mem_toFinset).mpr (hG0 x hx)
  rw [← Finset.sum_subset himg]
  · refine Finset.sum_congr rfl fun p hp => ?_
    rw [hsheet p ((hfin.mem_toFinset).mp (himg hp))]
  · intro p hp hpi
    rw [hsheet p ((hfin.mem_toFinset).mp hp)]
    have : F₀.filter (fun x => G x 0 = p) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro x hx hxp
      exact hpi (Finset.mem_image.mpr ⟨x, hx, hxp⟩)
    rw [this, Finset.card_empty, zero_nsmul]

/-- **Upper semicontinuity of the trace**, along generic points: the nearby generic fibres
have exactly `sheetNumber p` points near each point `p` of the fibre over `z₀`. -/
theorem eventually_trace_lt {z₀ : ComplexModel k} (hz₀ : z₀ ∈ D)
    {φ : ComplexModel n → EReal} (hφ : IsWeaklyPSHOn X φ) {c : EReal}
    (hc : trace X π δ φ z₀ < c) : ∀ᶠ z in 𝓝[{w | δ w ≠ 0}] z₀, trace X π δ φ z < c := by
  classical
  have hfin := hX.finite_fibre z₀ hz₀
  set T := hfin.toFinset with hTdef
  have hmemT : ∀ p, p ∈ T ↔ p ∈ fibre X π z₀ := fun p => hfin.mem_toFinset
  rw [trace, finsum_mem_eq_finite_toFinset_sum _ hfin] at hc
  obtain ⟨b, hb, hbc⟩ := EReal.exists_real_gt_sum_lt T φ
    (fun p hp => hφ.ne_top p ((hmemT p).mp hp).1) (fun p => sheetNumber X π δ p) hc
  have hε_usc : ∀ p ∈ T, ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y ∈ X, dist y p < ε → φ y < b p := by
    intro p hp
    have h := hφ.upperSemicontinuousOn p ((hmemT p).mp hp).1 (b p) (hb p hp)
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h
    obtain ⟨ε₀, hε₀, hε₀h⟩ := h
    filter_upwards [Ioo_mem_nhdsGT hε₀] with ε hε y hy hyp
    exact hε₀h (lt_trans hyp hε.2) hy
  have hε_sheet : ∀ p ∈ T, ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᶠ z in 𝓝[{w | δ w ≠ 0}] z₀,
      (fibre X π z ∩ ball p ε).ncard = sheetNumber X π δ p := by
    intro p hp
    obtain ⟨m, hm⟩ := hX.exists_isSheetNumber ((hmemT p).mp hp).1
    rw [sheetNumber_eq (hX.neBot_generic (hX.mem_base ((hmemT p).mp hp).1)) hm]
    have hπp : π p = z₀ := ((hmemT p).mp hp).2
    have h : IsSheetNumber X π δ p m := hm
    rw [IsSheetNumber, hπp] at h
    exact h
  have hall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (∀ p ∈ T, ∀ y ∈ X, dist y p < ε → φ y < b p) ∧
      (∀ p ∈ T, ∀ p' ∈ fibre X π z₀, p' ≠ p → 2 * ε < dist p p') ∧
      (∀ p ∈ T, ∀ᶠ z in 𝓝[{w | δ w ≠ 0}] z₀,
        (fibre X π z ∩ ball p ε).ncard = sheetNumber X π δ p) ∧ ε ∈ Ioi 0 :=
    ((Filter.eventually_all_finset T).mpr hε_usc).and
      (((Filter.eventually_all_finset T).mpr fun p _ => hX.eventually_separated hz₀ p).and
        (((Filter.eventually_all_finset T).mpr hε_sheet).and self_mem_nhdsWithin))
  obtain ⟨ε, hεusc, hεsep, hεsheet, hεpos⟩ := hall.exists
  have hε : (0 : ℝ) < ε := hεpos
  have hgen : ∀ᶠ z in 𝓝[{w | δ w ≠ 0}] z₀, z ∈ D ∧ z ∈ {w | δ w ≠ 0} ∧
      fibre X π z ⊆ (⋃ p ∈ fibre X π z₀, ball p ε) ∧
      ∀ p ∈ T, (fibre X π z ∩ ball p ε).ncard = sheetNumber X π δ p :=
    Filter.Eventually.and (nhdsWithin_le_nhds (hX.isOpen_base.mem_nhds hz₀))
      (Filter.Eventually.and self_mem_nhdsWithin
        (Filter.Eventually.and (nhdsWithin_le_nhds (hX.eventually_fibre_subset hz₀ hε))
          ((Filter.eventually_all_finset T).mpr hεsheet)))
  filter_upwards [hgen] with z hz
  obtain ⟨hzD, hzδ, hzsub, hzcount⟩ := hz
  have hfz := hX.finite_fibre z hzD
  rw [hX.trace_eq_sum_of_bijOn hzδ φ hfz.toFinset id (by rw [hfz.coe_toFinset]; exact bijOn_id _)]
  have hex : ∀ y ∈ fibre X π z, ∃ p ∈ T, y ∈ ball p ε := by
    intro y hy
    obtain ⟨p, hp, hyp⟩ := mem_iUnion₂.mp (hzsub hy)
    exact ⟨p, (hmemT p).mpr hp, hyp⟩
  let g : ComplexModel n → ComplexModel n := fun y =>
    if h : ∃ p ∈ T, y ∈ ball p ε then h.choose else y
  have hg : ∀ y ∈ fibre X π z, g y ∈ T ∧ y ∈ ball (g y) ε := by
    intro y hy
    have h := hex y hy
    simp only [g, dif_pos h]
    exact h.choose_spec
  have hguniq : ∀ y ∈ fibre X π z, ∀ p ∈ T, y ∈ ball p ε → g y = p := by
    intro y hy p hp hyp
    by_contra hne
    have hsep := hεsep p hp (g y) ((hmemT _).mp (hg y hy).1) hne
    have h1 : dist y p < ε := hyp
    have h2 : dist y (g y) < ε := (hg y hy).2
    linarith [dist_triangle p y (g y), dist_comm p y]
  have himg : hfz.toFinset.image g ⊆ T := by
    intro p hp
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hp
    exact (hg y ((hfz.mem_toFinset).mp hy)).1
  have hcard : ∀ p ∈ T,
      (hfz.toFinset.filter (fun y => g y = p)).card = sheetNumber X π δ p := by
    intro p hp
    rw [← hzcount p hp, ← Set.ncard_coe_finset]
    congr 1
    ext y
    simp only [Finset.coe_filter, Set.Finite.mem_toFinset, mem_ofPred_eq, mem_inter_iff]
    constructor
    · rintro ⟨hy, hgy⟩
      exact ⟨hy, hgy ▸ (hg y hy).2⟩
    · rintro ⟨hy, hyp⟩
      exact ⟨hy, hguniq y hy p hp hyp⟩
  calc ∑ y ∈ hfz.toFinset, φ (id y) ≤ ∑ y ∈ hfz.toFinset, ((b (g y) : ℝ) : EReal) := by
        refine Finset.sum_le_sum fun y hy => ?_
        have hy' := (hfz.mem_toFinset).mp hy
        exact (hεusc (g y) (hg y hy').1 y hy'.1 (hg y hy').2).le
    _ = ∑ p ∈ hfz.toFinset.image g,
          (hfz.toFinset.filter (fun y => g y = p)).card • ((b p : ℝ) : EReal) :=
        Finset.sum_comp (fun p => ((b p : ℝ) : EReal)) g
    _ = ∑ p ∈ T, sheetNumber X π δ p • ((b p : ℝ) : EReal) := by
        rw [← Finset.sum_subset himg]
        · exact Finset.sum_congr rfl fun p hp => by rw [hcard p (himg hp)]
        · intro p hp hpi
          rw [← hcard p hp]
          have : hfz.toFinset.filter (fun y => g y = p) = ∅ := by
            rw [Finset.filter_eq_empty_iff]
            intro y hy hgy
            exact hpi (Finset.mem_image.mpr ⟨y, hy, hgy⟩)
          rw [this, Finset.card_empty, zero_nsmul]
    _ < c := hbc

/-- **`[FN80]` Lemma 5.1.** For a finite branched covering `π : X → D` and `φ ∈ WP(X)`, the
trace `tr φ(z) = ∑_{p ∈ π⁻¹(z)} φ(p)` (points counted with their sheet numbers) is
plurisubharmonic on `D` (in the disc sense: psh or locally `≡ -∞`). -/
theorem discPshOn_trace {φ : ComplexModel n → EReal} (hφ : IsWeaklyPSHOn X φ) :
    DiscPshOn (trace X π δ φ) D := by
  classical
  set A : Set (ComplexModel k) := {w | δ w = 0} with hAdef
  set T := trace X π δ φ with hTdef
  have hDA : IsOpen (D \ A) := by
    have h := hX.differentiableOn_disc.continuousOn.isOpen_inter_preimage hX.isOpen_base
      (isOpen_ne : IsOpen {w : ℂ | w ≠ 0})
    have hset : D \ A = D ∩ δ ⁻¹' {w : ℂ | w ≠ 0} := by
      ext z
      simp [hAdef]
    rw [hset]
    exact h
  have hTpsh : PlurisubharmonicOn T (D \ A) := by
    intro z hz
    have hδz : δ z ≠ 0 := hz.2
    obtain ⟨W, hWo, hzW, -, hWδ, g, -, hgd, hbij⟩ := hX.exists_local_sections hz.1 hδz
    have hF := hX.finite_fibre z hz.1
    refine ⟨W, hWo, hzW, ?_⟩
    have hsum : DiscPshOn (fun w => ∑ x ∈ hF.toFinset, φ (g x w)) W :=
      discPshOn_finset_sum _ _ fun x hx => hφ.discPshOn_comp hWo
        (hgd x ((hF.mem_toFinset).mp hx))
        (fun w hw => ((hbij w hw).1 ((hF.mem_toFinset).mp hx)).1)
    refine hsum.congr fun w hw => ?_
    exact (hX.trace_eq_sum_of_bijOn (hWδ w hw) φ hF.toFinset (fun x => g x w)
      (by rw [hF.coe_toFinset]; exact hbij w hw)).symm
  have hbound : PshHypersurfaceRemovable.LocallyBoundedAboveOff A D T := by
    intro z hz
    obtain ⟨r, hr, hrD⟩ := hX.exists_closedBall_subset hz
    set K := X ∩ π ⁻¹' closedBall z r with hKdef
    have hK : IsCompact K := hX.isCompact_inter_preimage _ hrD (isCompact_closedBall z r)
    obtain ⟨C₀, hC₀⟩ : ∃ C₀ : ℝ, ∀ y ∈ K, φ y ≤ C₀ := by
      rcases K.eq_empty_or_nonempty with hKe | hKne
      · exact ⟨0, fun y hy => by simp [hKe] at hy⟩
      · obtain ⟨a, haK, hamax⟩ :=
          (hφ.upperSemicontinuousOn.mono inter_subset_left).exists_isMaxOn hKne hK
        obtain ⟨C₀, hC₀, -⟩ :=
          EReal.exists_between_coe_real (lt_top_iff_ne_top.mpr (hφ.ne_top a haK.1))
        exact ⟨C₀, fun y hy => (hamax hy).trans hC₀.le⟩
    refine ⟨closedBall z r, closedBall_mem_nhds z hr, deg * C₀, ?_⟩
    intro y hy hyA
    have hδy : δ y ≠ 0 := hyA
    have hyD := hrD hy
    have hfy := hX.finite_fibre y hyD
    rw [hTdef, hX.trace_eq_sum_of_bijOn hδy φ hfy.toFinset id
      (by rw [hfy.coe_toFinset]; exact bijOn_id _)]
    calc ∑ p ∈ hfy.toFinset, φ (id p) ≤ hfy.toFinset.card • ((C₀ : ℝ) : EReal) := by
          apply Finset.sum_le_card_nsmul
          intro p hp
          have hp' := (hfy.mem_toFinset).mp hp
          have hπp : π p = y := hp'.2
          refine hC₀ p ⟨hp'.1, ?_⟩
          show π p ∈ closedBall z r
          rw [hπp]
          exact hy
      _ = ((deg * C₀ : ℝ) : EReal) := by
          rw [← Set.ncard_eq_toFinset_card _ hfy, hX.ncard_fibre y hyD hδy, ← EReal.coe_nsmul,
            nsmul_eq_mul]
  have hext := PshAnalyticRemovable.plurisubharmonicOn_extension_of_zeroLocus hX.isOpen_base
    hTpsh hbound (g := fun _ : Fin 1 => δ) (fun _ => hX.differentiableOn_disc)
    (fun y _ => by simp [hAdef])
  have heq : EqOn (PshCodimTwoExtension.extension A T) T D := by
    intro z hz
    rw [PshCodimTwoExtension.extension_eq_uscRegularization]
    by_cases hzA : z ∈ A
    · apply le_antisymm
      · apply le_of_forall_gt_imp_ge_of_dense
        intro c hc
        have hev := hX.eventually_trace_lt hz hφ hc
        rw [eventually_nhdsWithin_iff] at hev
        refine (uscRegularization_le_localSup _ hev).trans (iSup₂_le fun y hy => ?_)
        by_cases hyA : y ∈ A
        · simp [hyA]
        · simp only [if_neg hyA]
          exact (hy hyA).le
      · apply le_of_forall_gt_imp_ge_of_dense
        intro c hc
        rcases eq_or_ne c ⊤ with rfl | hct
        · exact le_top
        obtain ⟨C, hC, hCc⟩ := EReal.exists_between_coe_real hc
        refine le_trans ?_ hCc.le
        apply hX.trace_le_of_eventually_le hz hφ
        have husc := upperSemicontinuous_uscRegularization
          (fun y => if y ∈ A then (⊥ : EReal) else T y) z C hC
        filter_upwards [nhdsWithin_le_nhds husc, self_mem_nhdsWithin] with y hy hyδ
        have hyA : y ∉ A := hyδ
        have h := le_uscRegularization (fun y => if y ∈ A then (⊥ : EReal) else T y) y
        simp only [if_neg hyA] at h
        exact h.trans hy.le
    · have h := PshCodimTwoExtension.extension_eq hTpsh hDA ⟨hz, hzA⟩
      rwa [PshCodimTwoExtension.extension_eq_uscRegularization] at h
  exact hext.discPshOn.congr heq

end IsBranchedCovering

end SGPT.Unibranch.FNL
