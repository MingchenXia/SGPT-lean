import SGPT.Okounkov.TranscendentalWNConvFLChart
import SGPT.Okounkov.TranscendentalWNKeyLSCStrict
import SGPT.Okounkov.TranscendentalWNConvFLReduction

/-!
# WN21 Proposition 7.4 near `X' \ ℰ`

Blueprint `claude-tok-wn-fl`, node `tok-wn-fl:strict-convergence`; source WN21 §7,
Proposition 7.4 (with the adaptation that `Σ_l e^{k_l/2}|τ_{k_l}| < ∞` suffices).

`strictFibreConvergence_of_strictLipschitz :
  StrictLipschitzStatement F → StrictFibreConvergenceStatement F`.

## Proof

Let `p = ι(x₀) ∈ X' \ ℰ` with `Ψ(p) ≠ -∞` (so `x₀ ∉ Z`), and `U₀ ∋ x₀`, `C` the data of the
Lipschitz bound (WN21 Corollary 7.6).  In a chart `e` of `X` at `x₀` and the affine chart `c₀` of
`ℙ¹` at `0`, the coordinates `(y, t) ↦ (e⁻¹ y, c₀⁻¹ t)` of `X × ℙ¹` avoid the centre `Z × {0}`, so
they lift through `μ` to a holomorphic `Γ` (WN-LSC `exists_strictLift`), with
`s_τ(e⁻¹ y) = Γ(y, c₀ τ)` and `ι(e⁻¹ y) = Γ(y, c₀ 0)`.  Let `ρ` be a local potential of `Θ` in a
chart `d` of `𝒳` at `p`, and `ρ_t(y) = ρ(d(Γ(y, t)))`.  The neighbourhood is
`W = μ⁻¹(e⁻¹(B(y₀, R/2)) × c₀⁻¹(B(t₀, R/2)))`.

By `limsup_le_of_forall_subseq` it suffices to bound the `limsup` along a further subsequence of
any subsequence; choose it (`k_l`) with `e_{k_l} ≤ 1/2`, `t_l = c₀(τ_{k_l})` close to `t₀` and
`sup |ρ_{t_l} - ρ_{t₀}| ≤ 2^{-l}` on a ball.  With `a_l = C e_{k_l} + 2^{-l}` (summable) and
`b_l = a_l + 2 Σ_{m<l} a_m`, the functions
`h_l(y) = v_{k_l}(s_{k_l}(e⁻¹ y)) + ρ_{t_l}(y) + k_l + b_l`
are psh, uniformly bounded (Lemma 7.5) and increasing in `l` (Corollary 7.6 and the monotonicity
of `v_k + k` on `X'`, WN21 Proposition 7.2); they converge pointwise to
`sup_k (v_k ∘ ι ∘ e⁻¹ + k) + ρ_{t₀} + b_∞`, which is a.e. the regularized limit
`v_{X'} ∘ e⁻¹ + ρ_{t₀} + b_∞` (TN `ae_chartFunction_iSup_eq_of_genuine`).  The fibre measures are the
Bedford--Taylor measures `(dd^c h_l)ⁿ` in the chart (`lintegral_diagonalPotentialMeasure_eq_canonical`),
and the test functions `ρ_test ∘ Γ(·, t_l)` converge uniformly; Bedford--Taylor convergence
(`tendsto_integral_canonicalBedfordTaylorMeasure_of_monotone`) gives
`∫ ρ_test ∘ s_{k_l} dν_{k_l} → ∫ ρ_test ∘ ι dλ'`.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open scoped SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity
open SGPT.Okounkov.TranscendentalMain
open SGPT.Okounkov.TranscendentalWN.LSC

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))

/-- **`tok-wn-fl:strict-convergence`** (WN21 Proposition 7.4 near `X' \ ℰ`) from the Lipschitz
bound (WN21 Corollary 7.6). -/
theorem strictFibreConvergence_of_strictLipschitz (hL : StrictLipschitzStatement F) :
    StrictFibreConvergenceStatement F := by
  classical
  intro E hE hE0 𝒳 _ _ _ μ hμ Eℰ hEℰ θ b c hc hcb hξ hξc ι hι hμι η' ε hε Ψ hΨ hVΨ 𝒵 _ _ _ π hπ
    D' h hh h𝒵c h𝒵conn hExc hΨπ hK χ hχ τ hτ0 hτlim s hs hμs hw hX' hℰ p hpX hpE hΨp
  set Θ := deformationForm F hμ.contMDiff θ b c Eℰ + ε • η'.form with hΘ
  have := compactSpace_normalCone F hμ
  -- `p = ι x₀` with `x₀ ∉ Z`
  obtain ⟨x₀, rfl⟩ : p ∈ range ι := by rw [(range_centralLift F hμ hι hμι).1]; exact hpX
  have hx₀ : x₀ ∉ F.flag (1 : Fin (m + 2)) := by
    rw [← (range_centralLift F hμ hι hμι).2]
    exact hpE
  -- the Lipschitz data
  obtain ⟨U₀, hU₀o, hx₀U₀, C, k₀, hC⟩ := hL E hE hE0 𝒳 μ hμ Eℰ hEℰ θ b c hc hcb hξ hξc ι hι hμι η'
    ε hε Ψ hΨ hVΨ 𝒵 π hπ D' h hh h𝒵c h𝒵conn hExc hΨπ hK χ hχ x₀ hx₀ hΨp
  -- the charts and the lift `Γ`
  set e : ComplexChart (m + 1) F.carrier := complexChartAt x₀ with he
  set c₀ := chartAt (ComplexModel 1) projectiveZero with hc₀
  set L := splitEquiv m with hLdef
  set SD := strictDomain F x₀ with hSD
  obtain ⟨ℓ, hℓ, hμℓ⟩ := exists_strictLift F hμ x₀
  have hx₀e : x₀ ∈ e.val.source := mem_complexChartAt_source x₀
  have h0c : projectiveZero ∈ c₀.source := mem_chart_source _ _
  set y₀ : ComplexModel (m + 1) := e.val x₀ with hy₀
  set t₀ : ComplexModel 1 := c₀ projectiveZero with ht₀
  set w₀ : ComplexModel (m + 1 + 1) := L (y₀, t₀) with hw₀def
  have hLL : ∀ y t, L.symm (L (y, t)) = (y, t) := fun y t => L.symm_apply_apply _
  have hw₀ : w₀ ∈ SD := by
    rw [mem_strictDomain, hw₀def, hLL]
    refine ⟨e.val.map_source hx₀e, ?_, c₀.map_source h0c⟩
    show e.val.symm (e.val x₀) ∉ _
    rw [e.val.left_inv hx₀e]
    exact hx₀
  set p₀ : LiftedOpen.{u} SD := LiftedOpen.mk SD w₀ hw₀
  set Γ : ComplexModel (m + 1 + 1) → 𝒳 := fun w => ℓ (liftMk SD p₀ w) with hΓ
  have hΓμ : ∀ w ∈ SD, μ (Γ w) = (e.val.symm (L.symm w).1, c₀.symm (L.symm w).2) := by
    intro w hw
    have h := congrFun hμℓ (liftMk SD p₀ w)
    simp only [Function.comp] at h
    rw [hΓ, h, strictInclusion, toModel_liftMk p₀ hw, chartAt_prod, prodChart_symm_apply]
    rfl
  have hΓsm : ∀ w ∈ SD,
      ContMDiffAt 𝓘(ℂ, ComplexModel (m + 1 + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ Γ w :=
    fun w hw => (hℓ _).comp w (contMDiffAt_liftMk p₀ hw)
  have hΓc : ContinuousOn Γ SD := fun w hw => (hΓsm w hw).continuousAt.continuousWithinAt
  have hΓsec : ∀ w ∈ SD, ∀ j : F.carrier → 𝒳,
      μ (j (e.val.symm (L.symm w).1)) = (e.val.symm (L.symm w).1, c₀.symm (L.symm w).2) →
        j (e.val.symm (L.symm w).1) = Γ w := by
    intro w hw j hj
    have hnot : μ (Γ w) ∉ deformationCentre F := by
      rw [hΓμ w hw]
      intro h
      exact ((mem_strictDomain F).mp hw).2.1 ((mem_deformationCentre_iff F).mp h).1
    exact (eq_of_map_eq_of_notMem F hμ hnot (by rw [hΓμ w hw, hj])).symm
  have hΓw₀ : Γ w₀ = ι x₀ := by
    have h := hΓsec w₀ hw₀ ι (by
      rw [hw₀def, hLL]
      simp only [hy₀, ht₀, e.val.left_inv hx₀e, c₀.left_inv h0c, hμι])
    rw [hw₀def, hLL] at h
    simp only [hy₀, e.val.left_inv hx₀e] at h
    exact h.symm
  clear_value Γ
  -- the chart of `𝒳` and the local potential of `Θ`
  set d : ComplexChart (m + 1 + 1) 𝒳 := complexChartAt (ι x₀) with hd
  have hιd : ι x₀ ∈ d.val.source := mem_complexChartAt_source _
  obtain ⟨Wd, ρ, hρ0, hρ⟩ := LocalPotentials.closedRealOneOne_hasLocalPotentials Θ d
    (d.val (ι x₀)) (d.val.map_source hιd)
  -- the good set of coordinates
  set O : Set 𝒳 := (d.val.source ∩ d.val ⁻¹' Wd) ∩ μ ⁻¹' (U₀ ×ˢ univ) with hO
  have hOo : IsOpen O := (d.val.isOpen_inter_preimage hρ.1).inter
    ((hU₀o.prod isOpen_univ).preimage hμ.continuous)
  set G : Set (ComplexModel (m + 1 + 1)) := SD ∩ Γ ⁻¹' O with hG
  have hGo : IsOpen G := hΓc.isOpen_inter_preimage SD.isOpen hOo
  have hw₀G : w₀ ∈ G := by
    refine ⟨hw₀, ?_⟩
    simp only [mem_preimage, hΓw₀, hO, mem_inter_iff, mem_prod, hμι]
    exact ⟨⟨hιd, hρ0⟩, hx₀U₀, mem_univ _⟩
  have hLsw : Continuous (fun q : ComplexModel 1 × ComplexModel (m + 1) => L (q.2, q.1)) :=
    L.continuous.comp (continuous_snd.prodMk continuous_fst)
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.isOpen_iff.mp (hGo.preimage hLsw) (t₀, y₀) (by
    show L (y₀, t₀) ∈ G
    exact hw₀G)
  set R : ℝ := ε₀ / 3 with hR
  have hR0 : 0 < R := by positivity
  have hbox : ∀ t, dist t t₀ < R → ∀ y, dist y y₀ < 2 * R →
      (t, y) ∈ (fun q : ComplexModel 1 × ComplexModel (m + 1) => L (q.2, q.1)) ⁻¹' G := by
    intro t ht y hy
    apply hball
    rw [← ball_prod_same]
    exact ⟨mem_ball.mpr (by linarith), mem_ball.mpr (by linarith)⟩
  -- the fibres in the coordinates
  have hsec : ∀ t, dist t t₀ < R → ∀ j : F.carrier → 𝒳, (∀ x, μ (j x) = (x, c₀.symm t)) →
      ∀ y, dist y y₀ < 2 * R → j (e.val.symm y) = Γ (L (y, t)) := by
    intro t ht j hj y hy
    have h := hΓsec _ (hbox t ht y hy).1 j (by rw [hLL]; exact hj _)
    rwa [hLL] at h
  have hGO : ∀ t, dist t t₀ < R → ∀ y, dist y y₀ < 2 * R →
      y ∈ e.val.target ∧ Γ (L (y, t)) ∈ d.val.source ∧ d.val (Γ (L (y, t))) ∈ Wd ∧
        e.val.symm y ∈ U₀ := by
    intro t ht y hy
    have hG' := hbox t ht y hy
    have h1 := (mem_strictDomain F).mp hG'.1
    rw [hLL] at h1
    have h2 := hG'.2
    simp only [mem_preimage, hO, mem_inter_iff, mem_prod] at h2
    rw [hΓμ _ hG'.1, hLL] at h2
    exact ⟨h1.1, h2.1.1, h2.1.2, h2.2.1⟩
  -- the neighbourhood `W`
  set W : Set 𝒳 := μ ⁻¹' ((e.val.source ∩ e.val ⁻¹' ball y₀ (R / 2)) ×ˢ
    (c₀.source ∩ c₀ ⁻¹' ball t₀ (R / 2))) with hWdef
  have hWo : IsOpen W := ((e.val.isOpen_inter_preimage isOpen_ball).prod
    (c₀.isOpen_inter_preimage isOpen_ball)).preimage hμ.continuous
  have hpW : ι x₀ ∈ W := by
    simp only [hWdef, mem_preimage, hμι, mem_prod, mem_inter_iff]
    exact ⟨⟨hx₀e, mem_ball_self (by positivity)⟩, h0c, mem_ball_self (by positivity)⟩
  refine ⟨W, hWo, hpW, fun ρt hρtc hρt0 hρtW φ hφ hφsum => ?_⟩
  -- basic facts on the sequence
  have hg : ∀ j, Continuous (cutoffObstacle μ χ j) := fun j =>
    (continuous_cutoffObstacleLine hχ j).comp (continuous_snd.comp hμ.continuous)
  have hι0 : ∀ y, (μ (ι y)).2 = projectiveZero := fun y => by rw [hμι]
  set v : ℕ → 𝒳 → EReal := fun j => prescribedEnvelope Θ (cutoffObstacle μ χ j) Ψ with hv
  have hvtop : ∀ j z, v j z ≠ ⊤ := fun j z =>
    ne_top_of_le_ne_top (EReal.coe_ne_top _) (prescribedEnvelope_le (hg j) z)
  set eK : ℕ → ℝ := fun j => Real.exp ((j : ℝ) / 2) * ‖τ j‖ with heK
  have heK0 : ∀ j, 0 ≤ eK j := fun j => mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
  have hτ : Tendsto τ atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) hτlim
    have h1 : (1 : ℝ) ≤ Real.exp ((k : ℝ) / 2) := Real.one_le_exp (by positivity)
    nlinarith [norm_nonneg (τ k)]
  have hpt : Tendsto (fun j => affineLinePoint (τ j)) atTop (𝓝 projectiveZero) := by
    have := (continuous_affineLinePoint'.tendsto 0).comp hτ
    rwa [affineLinePoint_zero] at this
  set tK : ℕ → ComplexModel 1 := fun j => c₀ (affineLinePoint (τ j)) with htKdef
  have htK : Tendsto tK atTop (𝓝 t₀) := ((c₀.continuousAt h0c).tendsto).comp hpt
  -- joint continuity in the coordinates
  set S : Set (ComplexModel 1) := closedBall t₀ (R / 2) with hS
  set K' : Set (ComplexModel (m + 1)) := closedBall y₀ R with hK'
  have hSK : ∀ q ∈ S ×ˢ K', L (q.2, q.1) ∈ G := fun q hq =>
    hbox q.1 (lt_of_le_of_lt (mem_closedBall.mp hq.1) (by linarith)) q.2
      (lt_of_le_of_lt (mem_closedBall.mp hq.2) (by linarith))
  have hcontΓ : ContinuousOn (fun q : ComplexModel 1 × ComplexModel (m + 1) => Γ (L (q.2, q.1)))
      (S ×ˢ K') := hΓc.comp hLsw.continuousOn fun q hq => (hSK q hq).1
  set Fρ : ComplexModel 1 → ComplexModel (m + 1) → ℝ := fun t y => ρ (d.val (Γ (L (y, t))))
    with hFρ
  have hFρc : ContinuousOn (Function.uncurry Fρ) (S ×ˢ K') := by
    have h1 : ContinuousOn (fun q : ComplexModel 1 × ComplexModel (m + 1) => d.val (Γ (L (q.2, q.1))))
        (S ×ˢ K') := d.val.continuousOn.comp hcontΓ fun q hq => by
      have := (hSK q hq).2
      simp only [mem_preimage, hO, mem_inter_iff] at this
      exact this.1.1
    exact hρ.2.2.1.continuousOn.comp h1 fun q hq => by
      have := (hSK q hq).2
      simp only [mem_preimage, hO, mem_inter_iff] at this
      exact this.1.2
  set Ft : ComplexModel 1 → ComplexModel (m + 1) → ℝ := fun t y => ρt (Γ (L (y, t))) with hFt
  have hFtc : ContinuousOn (Function.uncurry Ft) (S ×ˢ K') := hρtc.comp_continuousOn hcontΓ
  clear_value Fρ Ft
  have ht₀S : t₀ ∈ S := mem_closedBall_self (by positivity)
  -- reduction to further subsequences
  refine limsup_le_of_forall_subseq fun ψ hψ => ?_
  have hφψ : StrictMono (φ ∘ ψ) := hφ.comp hψ
  have hev : ∀ n : ℕ, ∀ᶠ j in atTop, k₀ ≤ φ (ψ j) ∧ eK (φ (ψ j)) ≤ 1 / 2 ∧
      affineLinePoint (τ (φ (ψ j))) ∈ c₀.source ∧ dist (tK (φ (ψ j))) t₀ < R / 2 ∧
      ∀ y ∈ K', |Fρ (tK (φ (ψ j))) y - Fρ t₀ y| ≤ (1 / 2 : ℝ) ^ n := by
    intro n
    have hk : ∀ᶠ k in atTop, k₀ ≤ k ∧ eK k ≤ 1 / 2 ∧ affineLinePoint (τ k) ∈ c₀.source ∧
        dist (tK k) t₀ < R / 2 ∧ ∀ y ∈ K', |Fρ (tK k) y - Fρ t₀ y| ≤ (1 / 2 : ℝ) ^ n := by
      have h1 : ∀ᶠ k in atTop, eK k ≤ 1 / 2 := hτlim.eventually (Iic_mem_nhds (by norm_num))
      have h2 : ∀ᶠ k in atTop, affineLinePoint (τ k) ∈ c₀.source :=
        hpt.eventually (c₀.open_source.mem_nhds h0c)
      have h3 : ∀ᶠ k in atTop, dist (tK k) t₀ < R / 2 :=
        htK.eventually (Metric.ball_mem_nhds t₀ (by positivity))
      have h4 := eventually_abs_sub_le_of_continuousOn (isCompact_closedBall t₀ (R / 2))
        (isCompact_closedBall y₀ R) hFρc ht₀S htK
        (h3.mono fun k hk => mem_closedBall.mpr hk.le) ((1 / 2 : ℝ) ^ n) (pow_pos (by norm_num) n)
      exact (eventually_ge_atTop k₀).and (h1.and (h2.and (h3.and h4)))
    exact hφψ.tendsto_atTop.eventually hk
  obtain ⟨ξ, hξ, hξP⟩ := Filter.extraction_forall_of_eventually hev
  refine ⟨ξ, hξ, ?_⟩
  set kl : ℕ → ℕ := fun l => φ (ψ (ξ l)) with hkl
  have hklm : StrictMono kl := hφψ.comp hξ
  have hkl0 : ∀ l, k₀ ≤ kl l := fun l => (hξP l).1
  have hkl1 : ∀ l, eK (kl l) ≤ 1 / 2 := fun l => (hξP l).2.1
  have hkl2 : ∀ l, affineLinePoint (τ (kl l)) ∈ c₀.source := fun l => (hξP l).2.2.1
  have hkl3 : ∀ l, dist (tK (kl l)) t₀ < R / 2 := fun l => (hξP l).2.2.2.1
  have hkl4 : ∀ l, ∀ y ∈ K', |Fρ (tK (kl l)) y - Fρ t₀ y| ≤ (1 / 2 : ℝ) ^ l :=
    fun l => (hξP l).2.2.2.2
  -- the sections in the coordinates
  have hsk : ∀ l, ∀ y, dist y y₀ < 2 * R → s (kl l) (e.val.symm y) = Γ (L (y, tK (kl l))) := by
    intro l y hy
    refine hsec (tK (kl l)) (by linarith [hkl3 l]) (s (kl l)) (fun x => ?_) y hy
    rw [hμs, htKdef, c₀.left_inv (hkl2 l)]
  have hιk : ∀ y, dist y y₀ < 2 * R → ι (e.val.symm y) = Γ (L (y, t₀)) := by
    intro y hy
    refine hsec t₀ (by simpa using hR0) ι (fun x => ?_) y hy
    rw [hμι, ht₀, c₀.left_inv h0c]
  -- the Lipschitz bounds in the coordinates
  have hyU : ∀ y, dist y y₀ < 2 * R → e.val.symm y ∈ U₀ := fun y hy =>
    (hGO t₀ (by simpa using hR0) y hy).2.2.2
  have hlow : ∀ j : ℕ, k₀ ≤ j → ∀ y, dist y y₀ < 2 * R →
      ((-(j : ℝ) - C : ℝ) : EReal) ≤ v j (ι (e.val.symm y)) := fun j hj y hy =>
    (hC j hj _ (hyU y hy)).1
  have hlip : ∀ l, ∀ y, dist y y₀ < 2 * R →
      v (kl l) (s (kl l) (e.val.symm y)) ≠ ⊥ ∧
      |(v (kl l) (s (kl l) (e.val.symm y))).toReal - (v (kl l) (ι (e.val.symm y))).toReal| ≤
        C * eK (kl l) := by
    intro l y hy
    have hτs : ‖τ (kl l)‖ ≤ Real.exp (-((kl l : ℕ) : ℝ) / 2) / 2 := by
      have h1 := hkl1 l
      simp only [heK] at h1
      have h2 : Real.exp (-((kl l : ℕ) : ℝ) / 2) * Real.exp (((kl l : ℕ) : ℝ) / 2) = 1 := by
        rw [← Real.exp_add, show -((kl l : ℕ) : ℝ) / 2 + ((kl l : ℕ) : ℝ) / 2 = 0 by ring,
          Real.exp_zero]
      have h3 : ‖τ (kl l)‖ = Real.exp (-((kl l : ℕ) : ℝ) / 2) *
          (Real.exp (((kl l : ℕ) : ℝ) / 2) * ‖τ (kl l)‖) := by
        rw [← mul_assoc, h2, one_mul]
      rw [h3]
      have h4 : 0 < Real.exp (-((kl l : ℕ) : ℝ) / 2) := Real.exp_pos _
      nlinarith
    have h := (hC (kl l) (hkl0 l) _ (hyU y hy)).2 (τ (kl l)) (hτ0 _) hτs (s (kl l) (e.val.symm y))
      (hμs _ _)
    refine ⟨h.1, h.2.trans_eq ?_⟩
    simp only [heK]
    ring
  have hC0 : 0 ≤ C := by
    have h := (hlip 0 y₀ (by simpa using hR0)).2
    have hpos : 0 < eK (kl 0) := mul_pos (Real.exp_pos _) (norm_pos_iff.mpr (hτ0 _))
    by_contra hneg
    rw [not_le] at hneg
    have : C * eK (kl 0) < 0 := mul_neg_of_neg_of_pos hneg hpos
    linarith [abs_nonneg ((v (kl 0) (s (kl 0) (e.val.symm y₀))).toReal -
      (v (kl 0) (ι (e.val.symm y₀))).toReal)]
  -- real values on the central fibre
  set vR : ℕ → F.carrier → ℝ := fun j x => (v j (ι x)).toReal with hvR
  have hvfin : ∀ j : ℕ, k₀ ≤ j → ∀ y, dist y y₀ < 2 * R →
      v j (ι (e.val.symm y)) = ((vR j (e.val.symm y) : ℝ) : EReal) := by
    intro j hj y hy
    refine (EReal.coe_toReal (hvtop _ _) fun hb => ?_).symm
    have := hlow j hj y hy
    rw [hb] at this
    exact EReal.coe_ne_bot _ (le_bot_iff.mp this)
  have hvR_low : ∀ j : ℕ, k₀ ≤ j → ∀ y, dist y y₀ < 2 * R →
      -(j : ℝ) - C ≤ vR j (e.val.symm y) := by
    intro j hj y hy
    have := hlow j hj y hy
    rwa [hvfin j hj y hy, EReal.coe_le_coe_iff] at this
  have hvR_up : ∀ j : ℕ, k₀ ≤ j → ∀ y, dist y y₀ < 2 * R → vR j (e.val.symm y) + j ≤ -1 := by
    intro j hj y hy
    have h : v j (ι (e.val.symm y)) + ((j : ℝ) : EReal) ≤ ((-1 : ℝ) : EReal) :=
      centralSequence_le (Θ := Θ) (ψ := Ψ) (ι := ι) hg hι0 j (e.val.symm y)
    rw [hvfin j hj y hy, ← EReal.coe_add, EReal.coe_le_coe_iff] at h
    exact h
  have hvR_mono : ∀ y, dist y y₀ < 2 * R → ∀ j j' : ℕ, k₀ ≤ j → j ≤ j' →
      vR j (e.val.symm y) + j ≤ vR j' (e.val.symm y) + j' := by
    intro y hy j j' hj hjj'
    have h : v j (ι (e.val.symm y)) + ((j : ℝ) : EReal) ≤
        v j' (ι (e.val.symm y)) + ((j' : ℝ) : EReal) :=
      monotone_centralSequence (Θ := Θ) (μ := μ) (ψ := Ψ) (ι := ι) hχ hjj' (e.val.symm y)
    rw [hvfin j hj y hy, hvfin j' (hj.trans hjj') y hy, ← EReal.coe_add, ← EReal.coe_add,
      EReal.coe_le_coe_iff] at h
    exact h
  -- the corrections `a_l`, `b_l`
  set a : ℕ → ℝ := fun l => C * eK (kl l) + (1 / 2 : ℝ) ^ l with ha
  have ha0 : ∀ l, 0 ≤ a l := fun l =>
    add_nonneg (mul_nonneg hC0 (heK0 _)) (pow_nonneg (by norm_num) l)
  have hasum : Summable a := by
    have h1 : Summable fun l => eK (kl l) :=
      hφsum.comp_injective (hψ.comp hξ).injective
    exact (h1.mul_left C).add (summable_geometric_of_lt_one (by norm_num) (by norm_num))
  set Ssum : ℝ := ∑' l, a l with hSsum
  set bb : ℕ → ℝ := fun l => a l + 2 * ∑ i ∈ Finset.range l, a i with hbb
  have hbb_succ : ∀ l, bb (l + 1) = bb l + a l + a (l + 1) := by
    intro l
    simp only [hbb, Finset.sum_range_succ]
    ring
  have hsum_le : ∀ l, ∑ i ∈ Finset.range l, a i ≤ Ssum := fun l =>
    hasum.sum_le_tsum _ (fun i _ => ha0 i)
  have hbb0 : ∀ l, 0 ≤ bb l := fun l =>
    add_nonneg (ha0 l) (mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => ha0 i))
  have hbb_le : ∀ l, bb l ≤ 3 * Ssum := fun l => by
    have h1 : a l ≤ Ssum := hasum.le_tsum l (fun i _ => ha0 i)
    have h2 := hsum_le l
    simp only [hbb]
    linarith
  have hbb_lim : Tendsto bb atTop (𝓝 (2 * Ssum)) := by
    have h1 : Tendsto a atTop (𝓝 0) := hasum.tendsto_atTop_zero
    have h2 : Tendsto (fun l => ∑ i ∈ Finset.range l, a i) atTop (𝓝 Ssum) :=
      hasum.hasSum.tendsto_sum_nat
    have := h1.add (h2.const_mul 2)
    rwa [zero_add] at this
  -- the bound of `ρ_{t₀}` on the ball
  have hFρ0c : ContinuousOn (fun y => Fρ t₀ y) K' :=
    hFρc.comp (continuous_const.prodMk continuous_id).continuousOn (fun y hy => ⟨ht₀S, hy⟩)
  obtain ⟨Mρ, hMρ⟩ := (isCompact_closedBall y₀ R).exists_bound_of_continuousOn hFρ0c
  -- the potentials `h_l`
  obtain ⟨hfun, hhfun⟩ : ∃ f : ℕ → ComplexModel (m + 1) → ℝ, f = fun l y =>
      (v (kl l) (s (kl l) (e.val.symm y))).toReal + Fρ (tK (kl l)) y + (kl l : ℝ) + bb l :=
    ⟨_, rfl⟩
  have hK'2 : ∀ y ∈ K', dist y y₀ < 2 * R := fun y hy =>
    lt_of_le_of_lt (mem_closedBall.mp hy) (by linarith)
  have hmono : ∀ y ∈ K', Monotone fun l => hfun l y := by
    intro y hy
    refine monotone_nat_of_le_succ fun l => ?_
    have hy2 := hK'2 y hy
    have h1 := (hlip l y hy2).2
    have h2 := (hlip (l + 1) y hy2).2
    have h3 := hvR_mono y hy2 _ _ (hkl0 l) (hklm.monotone (Nat.le_succ l))
    have h4 := hkl4 l y hy
    have h5 := hkl4 (l + 1) y hy
    rw [abs_le] at h1 h2 h4 h5
    show hfun l y ≤ hfun (l + 1) y
    rw [hhfun]
    simp only
    rw [hbb_succ]
    have ha1 : a (l + 1) = C * eK (kl (l + 1)) + (1 / 2 : ℝ) ^ l * (1 / 2) := by
      simp only [ha, pow_succ]
    have ha2 : a l = C * eK (kl l) + (1 / 2 : ℝ) ^ l := rfl
    rw [pow_succ] at h5
    have h3' : (v (kl l) (ι (e.val.symm y))).toReal + (kl l : ℝ) ≤
        (v (kl (l + 1)) (ι (e.val.symm y))).toReal + (kl (l + 1) : ℝ) := h3
    have hp := pow_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num) l
    linarith [h1.1, h1.2, h2.1, h2.2, h4.1, h4.2, h5.1, h5.2, h3']
  set Mh : ℝ := (2 * C + 1) + (Mρ + 1) + 3 * Ssum with hMh
  have hbound : ∀ l, ∀ y ∈ K', |hfun l y| ≤ Mh := by
    intro l y hy
    have hy2 := hK'2 y hy
    have h1 := (hlip l y hy2).2
    have h2 := hvR_low (kl l) (hkl0 l) y hy2
    have h3 := hvR_up (kl l) (hkl0 l) y hy2
    have h4 := hkl4 l y hy
    have h5 := hMρ y hy
    have h6 := hkl1 l
    have h7 := hbb0 l
    have h8 := hbb_le l
    have hpow : (1 / 2 : ℝ) ^ l ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hCe : C * eK (kl l) ≤ C * (1 / 2) := mul_le_mul_of_nonneg_left h6 hC0
    have hCe0 : 0 ≤ C * eK (kl l) := mul_nonneg hC0 (heK0 _)
    rw [abs_le] at h1 h4 ⊢
    rw [Real.norm_eq_abs, abs_le] at h5
    rw [hhfun]
    have h2' : -((kl l : ℕ) : ℝ) - C ≤ (v (kl l) (ι (e.val.symm y))).toReal := h2
    have h3' : (v (kl l) (ι (e.val.symm y))).toReal + (kl l : ℝ) ≤ -1 := h3
    constructor <;> linarith
  -- the limit potential
  set vX : F.carrier → EReal := centralLimitPotential Θ μ χ Ψ ι with hvX
  have hvX_low : ∀ y, dist y y₀ < 2 * R → ((-C : ℝ) : EReal) ≤ vX (e.val.symm y) := by
    intro y hy
    have h1 := hlow k₀ le_rfl y hy
    have h2 : v k₀ (ι (e.val.symm y)) + ((k₀ : ℝ) : EReal) ≤ vX (e.val.symm y) := by
      refine le_trans ?_ (le_uscRegularization _ _)
      exact le_iSup (fun j : ℕ => fun x => v j (ι x) + ((j : ℝ) : EReal)) k₀ |> fun h => h _
    have h3 := add_le_add h1 (le_refl ((k₀ : ℝ) : EReal))
    rw [← EReal.coe_add, show -(k₀ : ℝ) - C + k₀ = -C by ring] at h3
    exact h3.trans h2
  have hvX_up : ∀ x, vX x ≤ ((-1 : ℝ) : EReal) := fun x => by
    rw [hvX, centralLimitPotential]
    exact uscRegularization_le upperSemicontinuous_const
      (iSup_le fun j y => centralSequence_le (Θ := Θ) (ψ := Ψ) (ι := ι) hg hι0 j y) x
  have hvXfin : ∀ y, dist y y₀ < 2 * R →
      vX (e.val.symm y) = (((vX (e.val.symm y)).toReal : ℝ) : EReal) := by
    intro y hy
    refine (EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top _) (hvX_up _)) ?_).symm
    exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (hvX_low y hy)
  obtain ⟨Hfun, hHfun⟩ : ∃ f : ComplexModel (m + 1) → ℝ, f = fun y =>
      (vX (e.val.symm y)).toReal + Fρ t₀ y + 2 * Ssum := ⟨_, rfl⟩
  set Aop : Opens (ComplexModel (m + 1)) := ⟨ball y₀ R, isOpen_ball⟩ with hAop
  have hA2 : ∀ y ∈ Aop, dist y y₀ < 2 * R := fun y hy => by
    have : dist y y₀ < R := hy
    linarith
  have hAK' : ∀ y ∈ Aop, y ∈ K' := fun y hy => ball_subset_closedBall hy
  have hAe : (Aop : Set (ComplexModel (m + 1))) ⊆ e.val.target := fun y hy =>
    (hGO t₀ (by simpa using hR0) y (hA2 y hy)).1
  -- the local potentials
  have hFρ_eq : ∀ t, dist t t₀ < R → ∀ (j' : F.carrier → 𝒳), (∀ y, dist y y₀ < 2 * R →
      j' (e.val.symm y) = Γ (L (y, t))) → ∀ y ∈ Aop, Fρ t y = ρ (d.val (j' (e.val.symm y))) := by
    intro t ht j' hj' y hy
    rw [hj' y (hA2 y hy), hFρ]
  have hPl : ∀ l, IsSmoothLocalPotential (ClosedRealOneOneForm.pullback (hs (kl l)) Θ).val e Aop
      (fun y => Fρ (tK (kl l)) y + ((kl l : ℝ) + bb l)) := by
    intro l
    have ht : dist (tK (kl l)) t₀ < R := by linarith [hkl3 l]
    refine isSmoothLocalPotential_pullback_of_eqOn (hs (kl l)) Θ hρ e Aop.isOpen hAe
      (fun y hy => ?_) ((kl l : ℝ) + bb l) (fun y hy => ?_)
    · rw [hsk l y (hA2 y hy)]
      exact ⟨(hGO _ ht y (hA2 y hy)).2.1, (hGO _ ht y (hA2 y hy)).2.2.1⟩
    · rw [hFρ_eq _ ht _ (hsk l) y hy]
  have hP₀ : IsSmoothLocalPotential (ClosedRealOneOneForm.pullback hι Θ).val e Aop
      (fun y => Fρ t₀ y + 2 * Ssum) := by
    have ht : dist t₀ t₀ < R := by simpa using hR0
    refine isSmoothLocalPotential_pullback_of_eqOn hι Θ hρ e Aop.isOpen hAe
      (fun y hy => ?_) (2 * Ssum) (fun y hy => ?_)
    · rw [hιk y (hA2 y hy)]
      exact ⟨(hGO _ ht y (hA2 y hy)).2.1, (hGO _ ht y (hA2 y hy)).2.2.1⟩
    · rw [hFρ_eq _ ht _ hιk y hy]
  -- the corrected potentials
  have hheq : ∀ l, ∀ y ∈ Aop, chartFunction (fun x => v (kl l) (s (kl l) x)) e y +
      ((Fρ (tK (kl l)) y + ((kl l : ℝ) + bb l) : ℝ) : EReal) = (hfun l y : EReal) := by
    intro l y hy
    have hfin : v (kl l) (s (kl l) (e.val.symm y)) =
        (((v (kl l) (s (kl l) (e.val.symm y))).toReal : ℝ) : EReal) :=
      (EReal.coe_toReal (hvtop _ _) (hlip l y (hA2 y hy)).1).symm
    show v (kl l) (s (kl l) (e.val.symm y)) + _ = _
    rw [hfin, ← EReal.coe_add, hhfun]
    congr 1
    ring
  have hHeq : ∀ y ∈ Aop, chartFunction vX e y + ((Fρ t₀ y + 2 * Ssum : ℝ) : EReal) =
      (Hfun y : EReal) := by
    intro y hy
    show vX (e.val.symm y) + _ = _
    rw [hvXfin y (hA2 y hy), ← EReal.coe_add, hHfun]
    congr 1
    ring
  have hh : ∀ l, IsLocallyBoundedPshOn Aop (hfun l) := fun l =>
    isLocallyBoundedPshOn_of_corrected (hw (kl l)).1 e Aop (hPl l) (hheq l)
      (fun y hy => hbound l y (hAK' y hy))
  have hH : IsLocallyBoundedPshOn Aop Hfun := by
    refine isLocallyBoundedPshOn_of_corrected hX'.1 e Aop hP₀ hHeq
      (M := (C + 1) + Mρ + 2 * Ssum) fun y hy => ?_
    have h1 := hvX_low y (hA2 y hy)
    have h2 := hvX_up (e.val.symm y)
    rw [hvXfin y (hA2 y hy), EReal.coe_le_coe_iff] at h1 h2
    have h3 := hMρ y (hAK' y hy)
    rw [Real.norm_eq_abs, abs_le] at h3
    have h4 : 0 ≤ Ssum := tsum_nonneg ha0
    rw [hHfun, abs_le]
    constructor <;> linarith
  -- the potentials on `X'` are genuine
  have : Nonempty 𝒳 := ⟨ι x₀⟩
  have hvpsh : ∀ j : ℕ, ThetaPlurisubharmonic Θ.val (v j) := by
    intro j
    obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ z, cutoffObstacle μ χ j z ≤ B := by
      obtain ⟨z₀, -, hz₀⟩ := isCompact_univ.exists_isMaxOn univ_nonempty (hg j).continuousOn
      exact ⟨_, fun z => hz₀ (mem_univ z)⟩
    have hne : (prescribedCompetitors Θ (cutoffObstacle μ χ j) Ψ).Nonempty := by
      obtain ⟨Mψ, hMψ⟩ := hΨ.exists_global_upper_bound
      obtain ⟨z₁, -, hz₁⟩ := isCompact_univ.exists_isMinOn univ_nonempty (hg j).continuousOn
      refine ⟨fun x => Ψ x + ((cutoffObstacle μ χ j z₁ - Mψ : ℝ) : EReal),
        hΨ.add_const _, fun z => ?_,
        (SGPT.PSH.singularityLE_iff_exists_real _ _).mpr ⟨_, fun z => le_rfl⟩⟩
      calc Ψ z + ((cutoffObstacle μ χ j z₁ - Mψ : ℝ) : EReal)
          ≤ (Mψ : EReal) + ((cutoffObstacle μ χ j z₁ - Mψ : ℝ) : EReal) :=
            add_le_add (hMψ z) le_rfl
        _ = (cutoffObstacle μ χ j z₁ : EReal) := by rw [← EReal.coe_add]; ring_nf
        _ ≤ (cutoffObstacle μ χ j z : EReal) := EReal.coe_le_coe_iff.mpr (hz₁ (mem_univ z))
    exact (isThetaPshPotential_prescribedEnvelope hne hB).1
  have hey₀ : e.val.symm y₀ = x₀ := e.val.left_inv hx₀e
  have hgen : ∀ j : ℕ, IsThetaPshPotential (ClosedRealOneOneForm.pullback hι Θ).val
      (fun x => v j (ι x) + ((j : ℝ) : EReal)) := by
    intro j
    have hpsh := GlobalPotentialPullback.thetaPlurisubharmonic_comp hι (hvpsh j)
    have hne : ∃ x, v j (ι x) ≠ ⊥ := ⟨x₀, by
      obtain ⟨Cj, hCj⟩ := le_prescribedEnvelope_add (Θ := Θ) (hg j) hΨ
      intro hb
      have h := hCj (ι x₀)
      have hb' : prescribedEnvelope Θ (cutoffObstacle μ χ j) Ψ (ι x₀) = ⊥ := hb
      rw [hb', EReal.bot_add] at h
      exact hΨp (le_bot_iff.mp h)⟩
    exact IsThetaPshPotential.add_const
      ⟨hpsh, ThetaPshIdentityPrinciple.locallyNondegenerate_of_exists_ne_bot hpsh hne⟩ _
  have hmonoG : Monotone (fun j : ℕ => fun x => v j (ι x) + ((j : ℝ) : EReal)) :=
    monotone_centralSequence (Θ := Θ) (μ := μ) (ψ := Ψ) (ι := ι) hχ
  have hae0 := IncreasingMixedRegularizedContinuity.ae_chartFunction_iSup_eq_of_genuine hgen
    hmonoG hX' e
  -- a.e. convergence of `h_l` to `H`
  have hae : ∀ᵐ y, y ∈ Aop → Tendsto (fun l => hfun l y) atTop (𝓝 (Hfun y)) := by
    have h1 := (ae_restrict_iff' e.val.open_target.measurableSet).mp hae0
    filter_upwards [h1] with y hy hyA
    have heq := hy (hAe hyA)
    have hy2 := hA2 y hyA
    set x := e.val.symm y with hx
    have hlimE : Tendsto (fun j : ℕ => v j (ι x) + ((j : ℝ) : EReal)) atTop (𝓝 (vX x)) := by
      have h := tendsto_atTop_iSup (fun j j' (hjj' : j ≤ j') => hmonoG hjj' x)
      have h' : (⨆ j : ℕ, v j (ι x) + ((j : ℝ) : EReal)) = vX x := heq
      rwa [h'] at h
    have hvXne : vX x ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) (hvX_up _)
    have hvXnb : vX x ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (hvX_low y hy2)
    have hlimR : Tendsto (fun j : ℕ => vR j x + j) atTop (𝓝 (vX x).toReal) := by
      refine ((EReal.tendsto_toReal hvXne hvXnb).comp hlimE).congr'
        ((eventually_ge_atTop k₀).mono fun j hj => ?_)
      simp only [Function.comp]
      rw [hvfin j hj y hy2, ← EReal.coe_add, EReal.toReal_coe]
    have hkt := hklm.tendsto_atTop
    have T1 : Tendsto (fun l => (v (kl l) (s (kl l) x)).toReal - vR (kl l) x) atTop (𝓝 0) := by
      have he : Tendsto (fun l => C * eK (kl l)) atTop (𝓝 0) := by
        have := (hτlim.comp hkt).const_mul C
        rwa [mul_zero] at this
      refine squeeze_zero_norm (fun l => ?_) he
      rw [Real.norm_eq_abs]
      exact (hlip l y hy2).2
    have T2 : Tendsto (fun l => Fρ (tK (kl l)) y - Fρ t₀ y) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun l => ?_)
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num : (1 / 2 : ℝ) < 1))
      rw [Real.norm_eq_abs]
      exact hkl4 l y (hAK' y hyA)
    have T3 := hlimR.comp hkt
    have hsum := (((T1.add T2).add T3).add_const (Fρ t₀ y)).add hbb_lim
    refine hsum.congr' (Eventually.of_forall fun l => ?_) |>.trans (le_of_eq ?_)
    · simp only [Function.comp, hhfun, hvR]
      ring
    · rw [hHfun]
      simp only [zero_add]
      rfl
  -- the test functions
  have hR34 : R / 2 < 3 * R / 4 := by linarith
  set κ : ContDiffBump y₀ := ⟨R / 2, 3 * R / 4, by positivity, hR34⟩ with hκ
  set Kc : Set (ComplexModel (m + 1)) := closedBall y₀ (3 * R / 4) with hKc
  have hKcA : Kc ⊆ Aop := closedBall_subset_ball (by linarith)
  have hκK : ∀ z, z ∉ Kc → κ z = 0 := fun z hz => by
    by_contra h
    have hz' : z ∈ Function.support κ := h
    rw [κ.support_eq] at hz'
    exact hz (ball_subset_closedBall hz')
  have hκ01 : ∀ z, 0 ≤ κ z ∧ κ z ≤ 1 := fun z => ⟨κ.nonneg, κ.le_one⟩
  have hκts : tsupport κ ⊆ ball y₀ R := by
    rw [κ.tsupport_eq]
    exact closedBall_subset_ball (by show 3 * R / 4 < R; linarith)
  have hFtS : ∀ t ∈ S, ContinuousOn (fun y => Ft t y) (ball y₀ R) := fun t ht =>
    hFtc.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun y hy => ⟨ht, ball_subset_closedBall hy⟩)
  have hχc' : ∀ t ∈ S, Continuous fun y => κ y * Ft t y := fun t ht =>
    continuous_of_continuousOn_of_tsupport_subset isOpen_ball
      (κ.continuous.continuousOn.mul (hFtS t ht)) (tsupport_mul_subset_left.trans hκts)
  have htS : ∀ l, tK (kl l) ∈ S := fun l => mem_closedBall.mpr (hkl3 l).le
  -- off `e⁻¹(B(y₀, R/2))`, the test function vanishes on the fibres
  have hzero : ∀ (j' : F.carrier → 𝒳) (pt : ProjectiveLine), (∀ x, μ (j' x) = (x, pt)) →
      ∀ x, ρt (j' x) ≠ 0 → x ∈ e.val.source ∧ e.val x ∈ ball y₀ (R / 2) := by
    intro j' pt hj' x hx
    have hW := hρtW (subset_tsupport _ hx)
    simp only [hWdef, mem_preimage, hj', mem_prod, mem_inter_iff] at hW
    exact hW.1
  have hχeq' : ∀ (j' : F.carrier → 𝒳) (pt : ProjectiveLine), (∀ x, μ (j' x) = (x, pt)) →
      ∀ t, (∀ y, dist y y₀ < 2 * R → j' (e.val.symm y) = Γ (L (y, t))) →
      ∀ y ∈ Aop, ρt (j' (e.val.symm y)) = κ y * Ft t y := by
    intro j' pt hj' t hjt y hy
    have hFt_eq : Ft t y = ρt (j' (e.val.symm y)) := by rw [hFt, hjt y (hA2 y hy)]
    rw [hFt_eq]
    by_cases hy' : y ∈ closedBall y₀ (R / 2)
    · rw [κ.one_of_mem_closedBall hy', one_mul]
    · have h0 : ρt (j' (e.val.symm y)) = 0 := by
        by_contra hne
        have := (hzero j' pt hj' _ hne).2
        rw [e.val.right_inv (hAe hy)] at this
        exact hy' (ball_subset_closedBall this)
      rw [h0, mul_zero]
  have hsupp : ∀ l x, ρt (s (kl l) x) ≠ 0 → x ∈ e.val.source ∧ e.val x ∈ Aop := fun l x hx => by
    have h := hzero (s (kl l)) _ (hμs (kl l)) x hx
    exact ⟨h.1, ball_subset_ball (by linarith) h.2⟩
  have hsupp₀ : ∀ x, ρt (ι x) ≠ 0 → x ∈ e.val.source ∧ e.val x ∈ Aop := fun x hx => by
    have h := hzero ι _ hμι x hx
    exact ⟨h.1, ball_subset_ball (by linarith) h.2⟩
  have hunif : ∀ η : ℝ, 0 < η → ∀ᶠ l in atTop,
      ∀ z, |κ z * Ft (tK (kl l)) z - κ z * Ft t₀ z| ≤ η := by
    intro η hη
    have h := eventually_abs_sub_le_of_continuousOn (isCompact_closedBall t₀ (R / 2))
      (isCompact_closedBall y₀ R) hFtc ht₀S (htK.comp hklm.tendsto_atTop)
      (Eventually.of_forall htS) η hη
    filter_upwards [h] with l hl z
    by_cases hz : z ∈ K'
    · rw [← mul_sub, abs_mul, abs_of_nonneg (hκ01 z).1]
      calc κ z * |Ft (tK (kl l)) z - Ft t₀ z| ≤ 1 * η :=
            mul_le_mul (hκ01 z).2 (hl z hz) (abs_nonneg _) zero_le_one
        _ = η := one_mul η
    · have hzK : z ∉ Kc := fun h' => hz (closedBall_subset_closedBall (by linarith) h')
      rw [hκK z hzK, zero_mul, zero_mul, sub_zero, abs_zero]
      exact hη.le
  -- the chart-level convergence
  have htend := tendsto_restrictedTestMass_of_chart Θ e Aop (j := fun l => s (kl l))
    (fun l => hs (kl l)) hι (u := fun l x => v (kl l) (s (kl l) x)) (fun l => hw (kl l)) hX'
    hPl hP₀ hh hH hheq hHeq (fun y hy => hmono y (hAK' y hy)) hae ρt hρt0 hsupp hsupp₀
    (fun l => hχc' _ (htS l)) (hχc' t₀ ht₀S) (isCompact_closedBall y₀ (3 * R / 4)) hKcA
    (fun l z hz => by rw [hκK z hz, zero_mul]) (fun z hz => by rw [hκK z hz, zero_mul])
    (fun l => hχeq' (s (kl l)) _ (hμs (kl l)) _ (hsk l))
    (hχeq' ι _ hμι t₀ hιk) hunif
  refine (htend.limsup_eq).le.trans ?_
  unfold centralLimitTestMass
  exact le_self_add

end SGPT.Okounkov.TranscendentalWN
