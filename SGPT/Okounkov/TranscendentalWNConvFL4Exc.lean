import SGPT.Okounkov.TranscendentalWNConvFL4Measure
import SGPT.Okounkov.TranscendentalWNConvFL2Small
import SGPT.Okounkov.TranscendentalWNKeyLSCStrict
import SGPT.Okounkov.TranscendentalWNConvFLReduction

/-!
# WN21 Proposition 7.4 near `ℰ \ X'`

Blueprint `claude-tok-wn-fl4`, node `tok-wn-fl4:exceptional-convergence`
(= `tok-wn-fl:exceptional-convergence`); source WN21 §7, Proposition 7.4 and the paragraph before
its proof ("Let now `z̃₁, z₂, …, z_n, τ` be local coordinates centered at a point `z ∈ ℰ` …"),
with the adaptation that `Σ_l e^{k_l/2}|τ_{k_l}| < ∞` suffices.

`exceptionalFibreConvergence_of_excLipschitz :
  ExcLipschitzStatement F → ExceptionalFibreConvergenceStatement F`.

## Proof

Let `p ∈ ℰ \ X'` with `Ψ(p) ≠ -∞`, and `Γ(τ, y)` the fibre-disc coordinates at `p`
(`exists_excCoords`; `Γ(0, ·)` parametrizes `ℰ`, `Γ(τ, ·)` the fibre `X_τ`, `ν` the inverse of `y`).
WN21 Corollary 7.6 along these discs (`ExcLipschitzStatement`) gives `R₀`, `C`, `k₀`.  Let `ρ` be a
local potential of `Θ` in a chart `d` of `𝒳` at `p` and `F_ρ(τ, y) = ρ(d(Γ(τ, y)))`.  The neighbourhood
is `W = {z ∈ O ∩ d⁻¹(W_d) ∩ U_ℰ : |ν z - y₀| < R/2}`.

By `limsup_le_of_forall_subseq` it suffices to bound the `limsup` along a further subsequence of any
subsequence; choose it (`k_l`) with `e_{k_l} ≤ 1/2`, `k_l ≥ k₀`, `|τ_{k_l}| ≤ r/2` and
`sup |F_ρ(τ_{k_l}, ·) - F_ρ(0, ·)| ≤ 2^{-l}` on the ball.  With `a_l = C e_{k_l} + 2^{-l}`,
`b_l = a_l + 2 Σ_{i<l} a_i`, the functions
`h_l(y) = v_{k_l}(Γ(τ_{k_l}, y)) + F_ρ(τ_{k_l}, y) + k_l + b_l`
are bounded and increasing in `l` (Corollary 7.6 and the monotonicity of `v_k + k`, WN21
Proposition 7.2); they converge a.e. to `H(y) = v_ℰ(Γ(0, y)) + F_ρ(0, y) + 2 Σ a` (TN
`ae_chartFunction_iSup_eq_of_genuine` in a chart of `ℰ`, transported to the coordinates `y` by the
smooth map `ζ ↦ ν(e_ℰ⁻¹ ζ)`, which maps null sets to null sets).  The fibre measures and the measure
on `ℰ` are the Bedford--Taylor measures of `h_l` and `H` in the coordinates `y`
(`fibre_testMass_eq`, `exc_testMass_eq`), and Bedford--Taylor convergence against the uniformly
converging test functions (`tendsto_integral_canonicalBedfordTaylorMeasure_of_monotone`) gives
`∫ ρ_t ∘ s_{k_l} dν_{k_l} → ∫_ℰ ρ_t dλ_ℰ ≤ ∫ ρ_t ∘ ι dλ' + ∫_ℰ ρ_t dλ_ℰ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

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
open SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity
open SGPT.Okounkov.TranscendentalMain
open SGPT.Okounkov.TranscendentalWN.LSC

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))

/-- **`tok-wn-fl4:exceptional-convergence`** (WN21 Proposition 7.4 near `ℰ \ X'`) from the
Lipschitz bound along fibre discs (WN21 Corollary 7.6, `ExcLipschitzStatement`). -/
theorem exceptionalFibreConvergence_of_excLipschitz (hL : ExcLipschitzStatement F) :
    ExceptionalFibreConvergenceStatement F := by
  classical
  intro E hE hE0 𝒳 _ _ _ μ hμ Eℰ hEℰ θ b c hc hcb hξ hξc ι hι hμι η' ε hε Ψ hΨ hVΨ 𝒵 _ _ _ π hπ
    D' h hh h𝒵c h𝒵conn hExc hΨπ hK χ hχ τ hτ0 hτlim s hs hμs hw hX' hℰ p hpE hpX hΨp
  set Θ := deformationForm F hμ.contMDiff θ b c Eℰ + ε • η'.form with hΘ
  have := compactSpace_normalCone F hμ
  have : Nonempty 𝒳 := ⟨p⟩
  let _ := exceptionalChartedSpace F hμ
  have _ := isComplexManifold_exceptional F hμ
  have _ := compactSpace_exceptional F hμ
  have _ := connectedSpace_exceptional F hμ
  obtain ⟨K⟩ := exists_excCoords F hμ hpE hpX
  -- the Lipschitz data
  obtain ⟨R₀, hR₀, C, k₀, hC⟩ := hL 𝒳 μ hμ Θ Ψ hΨ 𝒵 π hπ D' h hh h𝒵c h𝒵conn hExc hΨπ hK χ hχ
    K.G K.Γ K.isOpen_G (fun q hq => (K.smooth q hq).contMDiffWithinAt) K.fibre K.y₀ K.mem_G
    (by rw [K.Γ_y₀]; exact hΨp)
  -- the chart of `𝒳` and the local potential of `Θ`
  set d : ComplexChart (m + 1 + 1) 𝒳 := complexChartAt p with hd
  have hpd : p ∈ d.val.source := mem_complexChartAt_source _
  obtain ⟨Wd, ρ, hρ0, hρ⟩ := LocalPotentials.closedRealOneOne_hasLocalPotentials Θ d
    (d.val p) (d.val.map_source hpd)
  -- the chart of `ℰ`
  set pE : exceptionalSet F μ := ⟨p, hpE⟩ with hpEdef
  set eE : ComplexChart (m + 1) (exceptionalSet F μ) := complexChartAt pE with heE
  obtain ⟨UE, hUEo, hUE⟩ := isOpen_induced_iff.mp eE.val.open_source
  have hpUE : p ∈ UE := by
    have : pE ∈ Subtype.val ⁻¹' UE := by rw [hUE]; exact mem_complexChartAt_source pE
    exact this
  -- the good set and the box
  set Og : Set 𝒳 := (K.O ∩ (d.val.source ∩ d.val ⁻¹' Wd)) ∩ UE with hOg
  have hOgo : IsOpen Og := (K.isOpen_O.inter (d.val.isOpen_inter_preimage hρ.1)).inter hUEo
  have hpOg : p ∈ Og := ⟨⟨K.mem_O, hpd, hρ0⟩, hpUE⟩
  have hOgO : Og ⊆ K.O := fun z hz => hz.1.1
  set G₁ : Set (ℂ × ComplexModel (m + 1)) := K.G ∩ K.Γ ⁻¹' Og with hG₁
  have hG₁o : IsOpen G₁ := K.continuousOn_Γ.isOpen_inter_preimage K.isOpen_G hOgo
  have h0G₁ : ((0 : ℂ), K.y₀) ∈ G₁ :=
    ⟨K.mem_G, by show K.Γ (0, K.y₀) ∈ Og; rw [K.Γ_y₀]; exact hpOg⟩
  obtain ⟨r, hr, hbox⟩ := FL2.exists_closedBall_prod_subset hG₁o h0G₁
  set R : ℝ := min r R₀ / 2 with hRdef
  have hR : 0 < R := by positivity
  have hRr : R < r := by
    have := min_le_left r R₀
    rw [hRdef]; linarith
  have hRR₀ : R < R₀ := by
    have := min_le_right r R₀
    rw [hRdef]; linarith
  have hboxR : ∀ t : ℂ, ‖t‖ ≤ r → ∀ y, dist y K.y₀ ≤ R → (t, y) ∈ G₁ := fun t ht y hy =>
    hbox ⟨mem_closedBall.mpr (by rwa [dist_zero_right]),
      mem_closedBall.mpr (hy.trans hRr.le)⟩
  have hG₁V : ∀ q ∈ G₁, q ∈ K.G ∧ K.Γ q ∈ K.O ∧ K.Γ q ∈ d.val.source ∧
      d.val (K.Γ q) ∈ Wd ∧ K.Γ q ∈ UE := fun q hq =>
    ⟨hq.1, hq.2.1.1, hq.2.1.2.1, hq.2.1.2.2, hq.2.2⟩
  -- the neighbourhood `W`
  set W : Set 𝒳 := Og ∩ K.ν ⁻¹' ball K.y₀ (R / 2) with hWdef
  have hWo : IsOpen W := (K.continuousOn_ν.mono hOgO).isOpen_inter_preimage hOgo isOpen_ball
  have hpW : p ∈ W := by
    refine ⟨hpOg, ?_⟩
    have h1 : K.ν (K.Γ (0, K.y₀)) = K.y₀ := K.ν_Γ _ K.mem_G (by rw [K.Γ_y₀]; exact K.mem_O)
    rw [K.Γ_y₀] at h1
    show K.ν p ∈ ball K.y₀ (R / 2)
    rw [h1]
    exact mem_ball_self (by positivity)
  refine ⟨W, hWo, hpW, fun ρt hρtc hρt0 hρtW φ hφ hφsum => ?_⟩
  /- ### Basic facts on the sequence -/
  have hg : ∀ j, Continuous (cutoffObstacle μ χ j) := fun j =>
    (continuous_cutoffObstacleLine hχ j).comp (continuous_snd.comp hμ.continuous)
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
  -- joint continuity in the coordinates
  set S : Set ℂ := closedBall 0 (r / 2) with hS
  set K' : Set (ComplexModel (m + 1)) := closedBall K.y₀ R with hK'
  have hSK : ∀ q ∈ S ×ˢ K', q ∈ G₁ := fun q hq =>
    hboxR q.1 (by
      have := mem_closedBall.mp hq.1
      rw [dist_zero_right] at this
      linarith) q.2 (mem_closedBall.mp hq.2)
  have hcontΓ : ContinuousOn K.Γ (S ×ˢ K') :=
    K.continuousOn_Γ.mono fun q hq => (hSK q hq).1
  set Fρ : ℂ → ComplexModel (m + 1) → ℝ := fun t y => ρ (d.val (K.Γ (t, y))) with hFρ
  have hFρc : ContinuousOn (Function.uncurry Fρ) (S ×ˢ K') := by
    have h1 : ContinuousOn (fun q => d.val (K.Γ q)) (S ×ˢ K') :=
      d.val.continuousOn.comp hcontΓ fun q hq => (hG₁V _ (hSK q hq)).2.2.1
    exact hρ.2.2.1.continuousOn.comp h1 fun q hq => (hG₁V _ (hSK q hq)).2.2.2.1
  set Ft : ℂ → ComplexModel (m + 1) → ℝ := fun t y => ρt (K.Γ (t, y)) with hFt
  have hFtc : ContinuousOn (Function.uncurry Ft) (S ×ˢ K') := hρtc.comp_continuousOn hcontΓ
  have h0S : (0 : ℂ) ∈ S := mem_closedBall_self (by positivity)
  /- ### Reduction to further subsequences -/
  refine limsup_le_of_forall_subseq fun ψ hψ => ?_
  have hφψ : StrictMono (φ ∘ ψ) := hφ.comp hψ
  have hev : ∀ n : ℕ, ∀ᶠ j in atTop, eK (φ (ψ j)) ≤ 1 / 2 ∧ k₀ ≤ φ (ψ j) ∧
      τ (φ (ψ j)) ∈ S ∧ ∀ y ∈ K', |Fρ (τ (φ (ψ j))) y - Fρ 0 y| ≤ (1 / 2 : ℝ) ^ n := by
    intro n
    have hk : ∀ᶠ k in atTop, eK k ≤ 1 / 2 ∧ k₀ ≤ k ∧ τ k ∈ S ∧
        ∀ y ∈ K', |Fρ (τ k) y - Fρ 0 y| ≤ (1 / 2 : ℝ) ^ n := by
      have h1 : ∀ᶠ k in atTop, eK k ≤ 1 / 2 := hτlim.eventually (Iic_mem_nhds (by norm_num))
      have h2 : ∀ᶠ k in atTop, k₀ ≤ k := eventually_ge_atTop k₀
      have h3 : ∀ᶠ k in atTop, τ k ∈ S := hτ.eventually (closedBall_mem_nhds 0 (by positivity))
      have h4 := eventually_abs_sub_le_of_continuousOn (isCompact_closedBall (0 : ℂ) (r / 2))
        (isCompact_closedBall K.y₀ R) hFρc h0S hτ h3 ((1 / 2 : ℝ) ^ n) (pow_pos (by norm_num) n)
      exact h1.and (h2.and (h3.and h4))
    exact hφψ.tendsto_atTop.eventually hk
  obtain ⟨ξ, hξ, hξP⟩ := Filter.extraction_forall_of_eventually hev
  refine ⟨ξ, hξ, ?_⟩
  set kl : ℕ → ℕ := fun l => φ (ψ (ξ l)) with hkl
  have hklm : StrictMono kl := hφψ.comp hξ
  have hkl1 : ∀ l, eK (kl l) ≤ 1 / 2 := fun l => (hξP l).1
  have hkl0 : ∀ l, k₀ ≤ kl l := fun l => (hξP l).2.1
  have htS : ∀ l, τ (kl l) ∈ S := fun l => (hξP l).2.2.1
  have hkl4 : ∀ l, ∀ y ∈ K', |Fρ (τ (kl l)) y - Fρ 0 y| ≤ (1 / 2 : ℝ) ^ l :=
    fun l => (hξP l).2.2.2
  have hτr : ∀ l, ‖τ (kl l)‖ ≤ r := fun l => by
    have := mem_closedBall.mp (htS l)
    rw [dist_zero_right] at this
    linarith
  /- ### The Lipschitz bounds in the coordinates -/
  have hτs : ∀ l, ‖τ (kl l)‖ ≤ Real.exp (-((kl l : ℕ) : ℝ) / 2) / 2 := by
    intro l
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
  have hK'R₀ : ∀ y ∈ K', y ∈ ball K.y₀ R₀ := fun y hy =>
    mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hy) hRR₀)
  have hlow : ∀ j : ℕ, k₀ ≤ j → ∀ y ∈ K',
      ((-(j : ℝ) - C : ℝ) : EReal) ≤ v j (K.Γ (0, y)) := fun j hj y hy =>
    (hC j hj y (hK'R₀ y hy)).2.1
  have hlip : ∀ l, ∀ y ∈ K', v (kl l) (K.Γ (τ (kl l), y)) ≠ ⊥ ∧
      |(v (kl l) (K.Γ (τ (kl l), y))).toReal - (v (kl l) (K.Γ (0, y))).toReal| ≤
        C * eK (kl l) := by
    intro l y hy
    obtain ⟨-, h2, h3⟩ := (hC (kl l) (hkl0 l) y (hK'R₀ y hy)).2.2 (τ (kl l)) (hτs l)
    refine ⟨h2, h3.trans_eq ?_⟩
    simp only [heK]
    ring
  have hy₀K' : K.y₀ ∈ K' := mem_closedBall_self hR.le
  have hC0 : 0 ≤ C := by
    have h := (hlip 0 K.y₀ hy₀K').2
    have hpos : 0 < eK (kl 0) := mul_pos (Real.exp_pos _) (norm_pos_iff.mpr (hτ0 _))
    by_contra hneg
    rw [not_le] at hneg
    have : C * eK (kl 0) < 0 := mul_neg_of_neg_of_pos hneg hpos
    linarith [abs_nonneg ((v (kl 0) (K.Γ (τ (kl 0), K.y₀))).toReal -
      (v (kl 0) (K.Γ (0, K.y₀))).toReal)]
  /- ### Values on `ℰ` -/
  have hι0 : ∀ z : exceptionalSet F μ, (μ z.1).2 = projectiveZero := fun z =>
    ((mem_deformationCentre_iff F).mp z.2).2
  have hB0 : ∀ y ∈ K', ((0 : ℂ), y) ∈ G₁ := fun y hy =>
    hboxR 0 (by simp [hr.le]) y (mem_closedBall.mp hy)
  have hE0y : ∀ y ∈ K', K.Γ (0, y) ∈ exceptionalSet F μ := fun y hy =>
    K.exceptional y (hG₁V _ (hB0 y hy)).1 (hG₁V _ (hB0 y hy)).2.1
  set zE : ComplexModel (m + 1) → exceptionalSet F μ := fun y =>
    if hy : K.Γ (0, y) ∈ exceptionalSet F μ then ⟨_, hy⟩ else pE with hzEdef
  have hzE : ∀ y ∈ K', (zE y).1 = K.Γ (0, y) := by
    intro y hy
    simp only [hzEdef, dif_pos (hE0y y hy)]
  set vR : ℕ → ComplexModel (m + 1) → ℝ := fun j y => (v j (K.Γ (0, y))).toReal with hvR
  have hvfin : ∀ j : ℕ, k₀ ≤ j → ∀ y ∈ K', v j (K.Γ (0, y)) = ((vR j y : ℝ) : EReal) := by
    intro j hj y hy
    refine (EReal.coe_toReal (hvtop _ _) fun hb => ?_).symm
    have := hlow j hj y hy
    rw [hb] at this
    exact EReal.coe_ne_bot _ (le_bot_iff.mp this)
  have hvR_low : ∀ j : ℕ, k₀ ≤ j → ∀ y ∈ K', -(j : ℝ) - C ≤ vR j y := by
    intro j hj y hy
    have := hlow j hj y hy
    rwa [hvfin j hj y hy, EReal.coe_le_coe_iff] at this
  have hvR_up : ∀ j : ℕ, k₀ ≤ j → ∀ y ∈ K', vR j y + j ≤ -1 := by
    intro j hj y hy
    have h := centralSequence_le (Θ := Θ) (ψ := Ψ) (ι := (Subtype.val : exceptionalSet F μ → 𝒳))
      hg hι0 j (zE y)
    rw [hzE y hy] at h
    change v j (K.Γ (0, y)) + ((j : ℝ) : EReal) ≤ ((-1 : ℝ) : EReal) at h
    rw [hvfin j hj y hy, ← EReal.coe_add, EReal.coe_le_coe_iff] at h
    exact h
  set gq : ℕ → exceptionalSet F μ → EReal := fun j z => v j z.1 + ((j : ℝ) : EReal) with hgq
  have hmonoG : Monotone gq :=
    monotone_centralSequence (Θ := Θ) (μ := μ) (ψ := Ψ)
      (ι := (Subtype.val : exceptionalSet F μ → 𝒳)) hχ
  have hvR_mono : ∀ y ∈ K', ∀ j j' : ℕ, k₀ ≤ j → j ≤ j' → vR j y + j ≤ vR j' y + j' := by
    intro y hy j j' hj hjj'
    have h := hmonoG hjj' (zE y)
    simp only [hgq, hzE y hy] at h
    rw [hvfin j hj y hy, hvfin j' (hj.trans hjj') y hy, ← EReal.coe_add, ← EReal.coe_add,
      EReal.coe_le_coe_iff] at h
    exact h
  /- ### The corrections `a_l`, `b_l` -/
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
  have hFρ0c : ContinuousOn (fun y => Fρ 0 y) K' :=
    hFρc.comp (continuous_const.prodMk continuous_id).continuousOn (fun y hy => ⟨h0S, hy⟩)
  obtain ⟨Mρ, hMρ⟩ := (isCompact_closedBall K.y₀ R).exists_bound_of_continuousOn hFρ0c
  /- ### The potentials `h_l` and `H` -/
  obtain ⟨hfun, hhfun⟩ : ∃ f : ℕ → ComplexModel (m + 1) → ℝ, f = fun l y =>
      (v (kl l) (K.Γ (τ (kl l), y))).toReal + Fρ (τ (kl l)) y + (kl l : ℝ) + bb l :=
    ⟨_, rfl⟩
  have hmono : ∀ y ∈ K', Monotone fun l => hfun l y := by
    intro y hy
    refine monotone_nat_of_le_succ fun l => ?_
    have h1 := (hlip l y hy).2
    have h2 := (hlip (l + 1) y hy).2
    have h3 := hvR_mono y hy (kl l) (kl (l + 1)) (hkl0 l) (hklm.monotone (Nat.le_succ l))
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
    have h3' : (v (kl l) (K.Γ (0, y))).toReal + (kl l : ℝ) ≤
        (v (kl (l + 1)) (K.Γ (0, y))).toReal + (kl (l + 1) : ℝ) := h3
    have hp := pow_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num) l
    linarith [h1.1, h1.2, h2.1, h2.2, h4.1, h4.2, h5.1, h5.2, h3']
  set Mh : ℝ := (2 * C + 1) + (Mρ + 1) + 3 * Ssum with hMh
  have hbound : ∀ l, ∀ y ∈ K', |hfun l y| ≤ Mh := by
    intro l y hy
    have h1 := (hlip l y hy).2
    have h2 := hvR_low (kl l) (hkl0 l) y hy
    have h3 := hvR_up (kl l) (hkl0 l) y hy
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
    have h2' : -((kl l : ℕ) : ℝ) - C ≤ (v (kl l) (K.Γ (0, y))).toReal := h2
    have h3' : (v (kl l) (K.Γ (0, y))).toReal + (kl l : ℝ) ≤ -1 := h3
    constructor <;> linarith
  -- the limit potential on `ℰ`
  set vE : exceptionalSet F μ → EReal :=
    centralLimitPotential Θ μ χ Ψ (Subtype.val : exceptionalSet F μ → 𝒳) with hvE
  have hvE_low : ∀ y ∈ K', ((-C : ℝ) : EReal) ≤ vE (zE y) := by
    intro y hy
    have h1 := hlow k₀ le_rfl y hy
    have h2 : gq k₀ (zE y) ≤ vE (zE y) := by
      refine le_trans ?_ (le_uscRegularization _ _)
      exact le_iSup (fun j : ℕ => gq j) k₀ |> fun h => h _
    simp only [hgq, hzE y hy] at h2
    have h3 : ((-C : ℝ) : EReal) = ((-(k₀ : ℝ) - C : ℝ) : EReal) + ((k₀ : ℝ) : EReal) := by
      rw [← EReal.coe_add]; congr 1; ring
    rw [h3]
    exact (add_le_add h1 le_rfl).trans h2
  have hvE_up : ∀ z, vE z ≤ ((-1 : ℝ) : EReal) := fun z => by
    rw [hvE, centralLimitPotential]
    exact uscRegularization_le upperSemicontinuous_const
      (iSup_le fun j y => centralSequence_le (Θ := Θ) (ψ := Ψ)
        (ι := (Subtype.val : exceptionalSet F μ → 𝒳)) hg hι0 j y) z
  have hvEfin : ∀ y ∈ K', vE (zE y) = (((vE (zE y)).toReal : ℝ) : EReal) := by
    intro y hy
    refine (EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top _) (hvE_up _)) ?_).symm
    exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (hvE_low y hy)
  obtain ⟨Hfun, hHfun⟩ : ∃ f : ComplexModel (m + 1) → ℝ, f = fun y =>
      (vE (zE y)).toReal + Fρ 0 y + 2 * Ssum := ⟨_, rfl⟩
  have hHbound : ∀ y ∈ K', |Hfun y| ≤ (C + 1) + (Mρ + 1) + 2 * Ssum := by
    intro y hy
    have h1 := hvE_low y hy
    have h2 := hvE_up (zE y)
    rw [hvEfin y hy, EReal.coe_le_coe_iff] at h1 h2
    have h3 := hMρ y hy
    rw [Real.norm_eq_abs, abs_le] at h3
    have h4 : 0 ≤ Ssum := tsum_nonneg ha0
    rw [hHfun, abs_le]
    constructor <;> linarith
  /- ### The coordinate ball -/
  set B : Opens (ComplexModel (m + 1)) := ⟨ball K.y₀ R, isOpen_ball⟩ with hBdef
  have hBK' : ∀ y ∈ B, y ∈ K' := fun y hy => ball_subset_closedBall hy
  have hy₀B : K.y₀ ∈ B := mem_ball_self hR
  have hBl : ∀ l, ∀ y ∈ B, (τ (kl l), y) ∈ K.G ∧ K.Γ (τ (kl l), y) ∈ K.O ∧
      K.Γ (τ (kl l), y) ∈ d.val.source ∧ d.val (K.Γ (τ (kl l), y)) ∈ Wd := by
    intro l y hy
    have h := hG₁V _ (hboxR _ (hτr l) y (mem_closedBall.mp (hBK' y hy)))
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  have hB0' : ∀ y ∈ B, ((0 : ℂ), y) ∈ K.G ∧ K.Γ (0, y) ∈ K.O ∧
      K.Γ (0, y) ∈ d.val.source ∧ d.val (K.Γ (0, y)) ∈ Wd := by
    intro y hy
    have h := hG₁V _ (hB0 y (hBK' y hy))
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  have hBE : ∀ y ∈ B, ∀ z : exceptionalSet F μ, z.1 = K.Γ (0, y) → z ∈ eE.val.source := by
    intro y hy z hz
    rw [← hUE]
    show z.1 ∈ UE
    rw [hz]
    exact (hG₁V _ (hB0 y (hBK' y hy))).2.2.2.2
  have hsuppW : ∀ z, ρt z ≠ 0 → z ∈ K.O ∧ z ∈ d.val.source ∧ d.val z ∈ Wd ∧ K.ν z ∈ B := by
    intro z hz
    have hzW := hρtW (subset_tsupport _ hz)
    exact ⟨hzW.1.1.1, hzW.1.1.2.1, hzW.1.1.2.2,
      ball_subset_ball (by linarith) hzW.2⟩
  /- ### The test functions -/
  have hR34 : R / 2 < 3 * R / 4 := by linarith
  set κ : ContDiffBump K.y₀ := ⟨R / 2, 3 * R / 4, by positivity, hR34⟩ with hκ
  set Lc : Set (ComplexModel (m + 1)) := closedBall K.y₀ (3 * R / 4) with hLc
  have hLcB : Lc ⊆ B := closedBall_subset_ball (by linarith)
  have hκK : ∀ z, z ∉ Lc → κ z = 0 := fun z hz => by
    by_contra h'
    have hz' : z ∈ Function.support κ := h'
    rw [κ.support_eq] at hz'
    exact hz (ball_subset_closedBall hz')
  have hκ01 : ∀ z, 0 ≤ κ z ∧ κ z ≤ 1 := fun z => ⟨κ.nonneg, κ.le_one⟩
  have hκts : tsupport κ ⊆ ball K.y₀ R := by
    rw [κ.tsupport_eq]
    exact closedBall_subset_ball (by show 3 * R / 4 < R; linarith)
  have hFtS : ∀ t ∈ S, ContinuousOn (fun y => Ft t y) (ball K.y₀ R) := fun t ht =>
    hFtc.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun y hy => ⟨ht, ball_subset_closedBall hy⟩)
  have hχc' : ∀ t ∈ S, Continuous fun y => κ y * Ft t y := fun t ht =>
    continuous_of_continuousOn_of_tsupport_subset isOpen_ball
      (κ.continuous.continuousOn.mul (hFtS t ht)) (tsupport_mul_subset_left.trans hκts)
  have hχeq : ∀ t ∈ S, ∀ y ∈ B, ρt (K.Γ (t, y)) = κ y * Ft t y := by
    intro t ht y hy
    show ρt (K.Γ (t, y)) = κ y * ρt (K.Γ (t, y))
    by_cases hy' : y ∈ closedBall K.y₀ (R / 2)
    · rw [κ.one_of_mem_closedBall hy', one_mul]
    · have h0 : ρt (K.Γ (t, y)) = 0 := by
        by_contra hne
        have hW := hρtW (subset_tsupport _ hne)
        have hq := hSK (t, y) ⟨ht, hBK' y hy⟩
        have hν := K.ν_Γ _ (hG₁V _ hq).1 (hG₁V _ hq).2.1
        have := hW.2
        rw [mem_preimage, hν] at this
        exact hy' (ball_subset_closedBall this)
      rw [h0, mul_zero]
  have hunif : ∀ η : ℝ, 0 < η → ∀ᶠ l in atTop,
      ∀ z, |κ z * Ft (τ (kl l)) z - κ z * Ft 0 z| ≤ η := by
    intro η hη
    have h := eventually_abs_sub_le_of_continuousOn (isCompact_closedBall (0 : ℂ) (r / 2))
      (isCompact_closedBall K.y₀ R) hFtc h0S (hτ.comp hklm.tendsto_atTop)
      (Eventually.of_forall htS) η hη
    filter_upwards [h] with l hl z
    by_cases hz : z ∈ K'
    · rw [← mul_sub, abs_mul, abs_of_nonneg (hκ01 z).1]
      calc κ z * |Ft (τ (kl l)) z - Ft 0 z| ≤ 1 * η :=
            mul_le_mul (hκ01 z).2 (hl z hz) (abs_nonneg _) zero_le_one
        _ = η := one_mul η
    · have hzK : z ∉ Lc := fun h' => hz (closedBall_subset_closedBall (by linarith) h')
      rw [hκK z hzK, zero_mul, zero_mul, sub_zero, abs_zero]
      exact hη.le
  /- ### The measures in the coordinates -/
  have hml : ∀ l, ∃ hf : IsLocallyBoundedPshOn B (hfun l),
      restrictedTestMass (hs (kl l)) Θ (fun x => v (kl l) (s (kl l) x)) (hw (kl l)) ρt =
        ENNReal.ofReal (∫ y, κ y * Ft (τ (kl l)) y ∂(MongeAmpere.canonicalBedfordTaylorMeasure
          B (hfun l) hf)) := by
    intro l
    refine fibre_testMass_eq hμ K Θ d hρ (hτ0 _) (hs _) (hμs _) (u := v (kl l)) (hw (kl l)) B
      (hBl l) ((kl l : ℝ) + bb l) (fun y hy => ?_) (fun y hy => hbound l y (hBK' y hy)) ρt hρt0
      hsuppW (hχc' _ (htS l)) (isCompact_closedBall _ _) hLcB
      (fun y hy => by rw [hκK y hy, zero_mul]) (fun y hy => hχeq _ (htS l) y hy)
    have hfin : v (kl l) (K.Γ (τ (kl l), y)) =
        (((v (kl l) (K.Γ (τ (kl l), y))).toReal : ℝ) : EReal) :=
      (EReal.coe_toReal (hvtop _ _) (hlip l y (hBK' y hy)).1).symm
    rw [hfin, ← EReal.coe_add, hhfun]
    congr 1
    simp only [hFρ]
    ring
  have hm0 := exc_testMass_eq hμ K hpE Θ d hρ hℰ B hy₀B hB0' hBE (2 * Ssum) (f := Hfun)
    (fun y hy z hz => by
      have hz' : z = zE y := Subtype.ext (hz.trans (hzE y (hBK' y hy)).symm)
      rw [hz', hvEfin y (hBK' y hy), ← EReal.coe_add, hHfun]
      congr 1
      simp only [hFρ, hzE y (hBK' y hy)]
      ring)
    (fun y hy => hHbound y (hBK' y hy)) ρt hρt0 hsuppW (hχc' 0 h0S) (isCompact_closedBall _ _)
    hLcB (fun y hy => by rw [hκK y hy, zero_mul]) (fun y hy => hχeq 0 h0S y hy)
  choose hhl hml' using hml
  obtain ⟨hH, hm0'⟩ := hm0
  /- ### a.e. convergence of `h_l` to `H` -/
  have hvpsh : ∀ j : ℕ, ThetaPlurisubharmonic Θ.val (v j) := by
    intro j
    obtain ⟨Bj, hBj⟩ : ∃ B : ℝ, ∀ z, cutoffObstacle μ χ j z ≤ B := by
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
    exact (isThetaPshPotential_prescribedEnvelope hne hBj).1
  have hgen : ∀ j : ℕ, IsThetaPshPotential
      (ClosedRealOneOneForm.pullback (contMDiff_exceptionalInclusion F hμ) Θ).val
      (gq (j + k₀)) := by
    intro j
    have hpsh := GlobalPotentialPullback.thetaPlurisubharmonic_comp
      (contMDiff_exceptionalInclusion F hμ) (hvpsh (j + k₀))
    have hne : ∃ z : exceptionalSet F μ, v (j + k₀) z.1 ≠ ⊥ := ⟨pE, by
      have := hlow (j + k₀) (Nat.le_add_left _ _) K.y₀ hy₀K'
      rw [K.Γ_y₀] at this
      exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) this⟩
    exact IsThetaPshPotential.add_const
      ⟨hpsh, ThetaPshIdentityPrinciple.locallyNondegenerate_of_exists_ne_bot hpsh hne⟩ _
  have hsup : (⨆ j, gq (j + k₀)) = ⨆ j, gq j := hmonoG.iSup_nat_add k₀
  have hU : IsThetaPshPotential
      (ClosedRealOneOneForm.pullback (contMDiff_exceptionalInclusion F hμ) Θ).val
      (uscRegularization (⨆ j, gq (j + k₀))) := by
    rw [hsup]
    exact hℰ
  have hae0 := IncreasingMixedRegularizedContinuity.ae_chartFunction_iSup_eq_of_genuine hgen
    (hmonoG.comp fun a b hab => Nat.add_le_add_right hab k₀) hU eE
  have h1 := (ae_restrict_iff' eE.val.open_target.measurableSet).mp hae0
  have hgoodζ : ∀ᵐ ζ, ζ ∈ eE.val.target →
      (⨆ j, gq (j + k₀) (eE.val.symm ζ)) = vE (eE.val.symm ζ) := by
    filter_upwards [h1] with ζ hζ hζt
    have h2 := hζ hζt
    have h3 : (⨆ j, gq (j + k₀) (eE.val.symm ζ)) =
        ⨆ j, chartFunction (gq (j + k₀)) eE ζ := rfl
    rw [h3, h2]
    show uscRegularization (⨆ j, gq (j + k₀)) (eE.val.symm ζ) = vE (eE.val.symm ζ)
    rw [hsup]
    rfl
  -- transport of the null set to the coordinates `y`
  set τE : ComplexModel (m + 1) → ComplexModel (m + 1) := fun ζ => K.ν (eE.val.symm ζ).1
    with hτE
  set DE : Set (ComplexModel (m + 1)) :=
    eE.val.target ∩ (fun ζ => (eE.val.symm ζ).1) ⁻¹' K.O with hDE
  have hτEd : DifferentiableOn ℝ τE DE := by
    intro ζ hζ
    have h1 : ContMDiffAt 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞
        eE.val.symm ζ :=
      contMDiffOn_chart_symm.contMDiffAt (eE.val.open_target.mem_nhds hζ.1)
    have h2 := (contMDiff_exceptionalInclusion F hμ _).comp ζ h1
    have h3 := (K.smooth_ν _ hζ.2).comp ζ h2
    exact ((contMDiffAt_iff_contDiffAt.mp h3).differentiableAt (by simp)).restrictScalars ℝ
      |>.differentiableWithinAt
  set Nζ : Set (ComplexModel (m + 1)) :=
    {ζ | ζ ∈ eE.val.target ∧ ¬ (⨆ j, gq (j + k₀) (eE.val.symm ζ)) = vE (eE.val.symm ζ)} ∩ DE
    with hNζ
  have hNζ0 : volume Nζ = 0 := by
    refine measure_mono_null (fun ζ hζ => ?_) (ae_iff.mp hgoodζ)
    show ¬ (ζ ∈ eE.val.target → _)
    exact fun h' => hζ.1.2 (h' hζ.1.1)
  have hNy0 : volume (τE '' Nζ) = 0 :=
    MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      (hτEd.mono inter_subset_right) hNζ0
  have hgoody : ∀ᵐ y, y ∈ B → (⨆ j, gq (j + k₀) (zE y)) = vE (zE y) := by
    rw [ae_iff]
    refine measure_mono_null (fun y hy => ?_) hNy0
    have hy' : ¬ (y ∈ B → (⨆ j, gq (j + k₀) (zE y)) = vE (zE y)) := hy
    rw [Classical.not_imp] at hy'
    obtain ⟨hyB, hbad⟩ := hy'
    have hyK := hBK' y hyB
    have hzsrc : zE y ∈ eE.val.source := hBE y hyB _ (hzE y hyK)
    refine ⟨eE.val (zE y), ⟨⟨eE.val.map_source hzsrc, ?_⟩, eE.val.map_source hzsrc, ?_⟩, ?_⟩
    · rw [eE.val.left_inv hzsrc]
      exact hbad
    · show (eE.val.symm (eE.val (zE y))).1 ∈ K.O
      rw [eE.val.left_inv hzsrc, hzE y hyK]
      exact (hB0' y hyB).2.1
    · show K.ν (eE.val.symm (eE.val (zE y))).1 = y
      rw [eE.val.left_inv hzsrc, hzE y hyK, K.ν_Γ _ (hB0' y hyB).1 (hB0' y hyB).2.1]
  have hae : ∀ᵐ y, y ∈ B → Tendsto (fun l => hfun l y) atTop (𝓝 (Hfun y)) := by
    filter_upwards [hgoody] with y hy hyB
    have hgood := hy hyB
    have hyK := hBK' y hyB
    have hlimE : Tendsto (fun j => gq j (zE y)) atTop (𝓝 (vE (zE y))) := by
      have h := tendsto_atTop_iSup (fun j j' (hjj' : j ≤ j') => hmonoG hjj' (zE y))
      have h' : (⨆ j, gq j (zE y)) = vE (zE y) := by
        rw [← hgood]
        have := congrFun hsup (zE y)
        simp only [iSup_apply] at this
        exact this.symm
      rwa [h'] at h
    have hvEne : vE (zE y) ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) (hvE_up _)
    have hvEnb : vE (zE y) ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (hvE_low y hyK)
    have hlimR : Tendsto (fun j => (gq j (zE y)).toReal) atTop (𝓝 (vE (zE y)).toReal) :=
      (EReal.tendsto_toReal hvEne hvEnb).comp hlimE
    have hkt := hklm.tendsto_atTop
    have T3 : Tendsto (fun l => vR (kl l) y + kl l) atTop (𝓝 (vE (zE y)).toReal) := by
      refine (hlimR.comp hkt).congr fun l => ?_
      simp only [Function.comp, hgq, hzE y hyK]
      rw [hvfin (kl l) (hkl0 l) y hyK, ← EReal.coe_add, EReal.toReal_coe]
    have T1 : Tendsto (fun l => (v (kl l) (K.Γ (τ (kl l), y))).toReal - vR (kl l) y) atTop
        (𝓝 0) := by
      have he : Tendsto (fun l => C * eK (kl l)) atTop (𝓝 0) := by
        have := (hτlim.comp hkt).const_mul C
        rwa [mul_zero] at this
      refine squeeze_zero_norm (fun l => ?_) he
      rw [Real.norm_eq_abs]
      exact (hlip l y hyK).2
    have T2 : Tendsto (fun l => Fρ (τ (kl l)) y - Fρ 0 y) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun l => ?_)
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num : (1 / 2 : ℝ) < 1))
      rw [Real.norm_eq_abs]
      exact hkl4 l y hyK
    have hsum := (((T1.add T2).add T3).add_const (Fρ 0 y)).add hbb_lim
    refine hsum.congr' (Eventually.of_forall fun l => ?_) |>.trans (le_of_eq ?_)
    · simp only [hhfun, hvR]
      ring
    · rw [hHfun]
      simp only [zero_add]
  /- ### The chart-level convergence -/
  have htend := tendsto_integral_canonicalBedfordTaylorMeasure_of_monotone hhl hH
    (fun y hy => hmono y (hBK' y hy)) hae (fun l => hχc' _ (htS l)) (hχc' 0 h0S)
    (isCompact_closedBall K.y₀ (3 * R / 4)) hLcB (fun l z hz => by rw [hκK z hz, zero_mul])
    (fun z hz => by rw [hκK z hz, zero_mul]) hunif
  have hT : Tendsto (fun l => restrictedTestMass (hs (kl l)) Θ
      (fun x => v (kl l) (s (kl l) x)) (hw (kl l)) ρt) atTop
      (𝓝 (restrictedTestMass (contMDiff_exceptionalInclusion F hμ) Θ vE hℰ ρt)) := by
    simp only [hml', hm0']
    exact (ENNReal.continuous_ofReal.tendsto _).comp htend
  refine (hT.limsup_eq).le.trans ?_
  unfold centralLimitTestMass
  exact le_add_self

end SGPT.Okounkov.TranscendentalWN
