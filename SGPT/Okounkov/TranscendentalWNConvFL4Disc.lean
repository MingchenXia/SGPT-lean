import SGPT.Okounkov.TranscendentalWNConvFL4Statement
import SGPT.Okounkov.TranscendentalWNConvFL5Disc

/-!
# WN21 Lemma 7.5 along holomorphic families of fibre discs

Blueprint `claude-tok-wn-fl4`, node `tok-wn-fl4:disc-laplacian`; source WN21 §7, Lemma 7.5 and
the paragraph after Corollary 7.6 (the same estimate near `ℰ`, in the coordinates `(z̃₁, z', τ)`),
`references/wn21-restricted-volume`, with the threshold `k₀` of `tok-wn-fl3:disc-statement-k0`.

`excDiscLaplacian : ExcDiscLaplacianStatement F`: for a holomorphic family of fibre discs
`Γ : G → 𝒳` (`π_{ℙ¹}(μ(Γ(t, y))) = [t : 1]`) through `p = Γ(0, y₀)` with `Ψ(p) ≠ -∞`, there are
`R > 0`, `C`, `k₀` such that for `k ≥ k₀`, `|y - y₀| < R`: `|v_k(Γ(t, y)) + k| ≤ C` on
`|t| ≤ e^{-k/2}`, and `t ↦ v_k(Γ(t, y))` is there the uniform limit of `C²` functions `U_j` on `ℂ`
with `-C ≤ Δ U_j ≤ C e^k` on the open disc.

## Proof (the route of lane WN-FL5 near `X' \ ℰ`, with `π` in place of `μ ∘ π`)

* **Discs in the resolution.**  A point `z₀ ∈ π⁻¹(p)` lies off `Supp D' ⊇ Exc(π)` (as
  `Ψ(p) ≠ -∞`), so `π` has a holomorphic local inverse `S` at `p` (TN
  `HolomorphicLocalInverse.exists_localInverse`).  In the chart `e` of `𝒵` at `z₀` the discs
  `γ_y(t) = e(S(Γ(t, y)))` are holomorphic and stay in a closed ball `B̄(e z₀, ρ)` inside the chart
  and off `Supp D'` for `|y - y₀| < ε₀`, `|t| < 2R`; there `Γ(t, y) = π(S(Γ(t, y)))`.  Cauchy's
  estimate bounds `|γ_y'|` on `|t| ≤ R` (`norm_deriv_le_of_mapsTo_ball`).
* **The bound**: `Ψ ∘ π = ψ_{D'} + h ≥ -C₁` on the compact `K = e⁻¹(B̄(e z₀, ρ))`, so
  `v_k ≥ v_0 - k ≥ Ψ + c₀ - k ≥ -C₁ + c₀ - k` (`le_prescribedEnvelope`,
  `prescribedEnvelope_cutoffObstacle_zero_le`), and `v_k ≤ g_k ≤ -k` on `|t| ≤ e^{-k/2}`.
* **The Laplacian** (as `exists_strictDisc_laplacian`, lane WN-FL5): WN-FL3's
  `exists_lineBound_cutoffEnvelope` (Proposition 7.1 + Berman's estimate) gives `v_k ∘ π = ṽ_k + Ψ ∘ π`
  with `ṽ_k` the uniform limit of smooth `u_j`, `0 ≤ ω̃ + dd^c u_j ≤ (C₀ e^k e^{a(g_k∘π - Ψ∘π + k)} + 1) ω̃`
  on lines over `K`; `Δ_t (F_j ∘ γ_y) = 4π [(ω̃ + dd^c u_j) - π^*Θ](γ_y', iγ_y')` for
  `F_j = u_j + ψ_{D'} + h` (`laplacian_comp_holomorphic_eq_smoothDDC`, `smoothDDC_chart_resolved`), whence
  `-C ≤ Δ ≤ C e^k`; the cutoff `exists_contDiff_two_eqOn_closedBall` globalizes the `C²` functions.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter Metric
open scoped Topology Manifold ContDiff Laplacian
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity
open SGPT.Okounkov.TranscendentalMain
open SGPT.Okounkov.TranscendentalCore

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))
variable {𝒳 : Type u} [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
  [IsComplexManifold (m + 1 + 1) 𝒳] {μ : 𝒳 → F.carrier × ProjectiveLine}

/-- **WN21 Lemma 7.5 along a holomorphic family of fibre discs, with a threshold `k₀`** (general
form of `ExcDiscLaplacianStatement`). -/
theorem exists_excDisc_laplacian (hμ : IsNormalConeDeformation F μ)
    {Θ : ClosedRealOneOneForm (m + 1 + 1) 𝒳} {Ψ : 𝒳 → EReal} (hΨ : IsThetaPshPotential Θ.val Ψ)
    {𝒵 : Type u} [TopologicalSpace 𝒵] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒵]
    [IsComplexManifold (m + 1 + 1) 𝒵] [CompactSpace 𝒵] [ConnectedSpace 𝒵] {π : 𝒵 → 𝒳}
    (hπ : IsAnalyticModification (n := m + 1 + 1) π) (D' : MeteredEffectiveQDivisor (m + 1 + 1) 𝒵)
    (hexc : exceptionalLocus (m + 1 + 1) π ⊆ D'.support)
    {h : 𝒵 → ℝ} (hh : ChartSmooth (n := m + 1 + 1) h)
    (hΨπ : ∀ z, Ψ (π z) = D'.weight z + (h z : EReal))
    (hKah : ((ClosedRealOneOneForm.pullback hπ.1 Θ - D'.curvature) +
      ddcClosedForm h hh).val.IsKahler)
    {χ : ℝ → ℝ} (hχ : IsWNCutoff χ)
    {G : Set (ℂ × ComplexModel (m + 1))} {Γ : ℂ × ComplexModel (m + 1) → 𝒳} (hG : IsOpen G)
    (hΓ : ContMDiffOn 𝓘(ℂ, ℂ × ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ Γ G)
    (hΓμ : ∀ q ∈ G, (μ (Γ q)).2 = affineLinePoint q.1)
    {y₀ : ComplexModel (m + 1)} (hy₀ : ((0 : ℂ), y₀) ∈ G) (hΨy₀ : Ψ (Γ (0, y₀)) ≠ ⊥) :
    ∃ R : ℝ, 0 < R ∧ ∃ C : ℝ, ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ y ∈ Metric.ball y₀ R,
      (∀ t : ℂ, ‖t‖ ≤ Real.exp (-(k : ℝ) / 2) → (t, y) ∈ G ∧
        prescribedEnvelope Θ (cutoffObstacle μ χ k) Ψ (Γ (t, y)) ≠ ⊥ ∧
        |(prescribedEnvelope Θ (cutoffObstacle μ χ k) Ψ (Γ (t, y))).toReal + k| ≤ C) ∧
      ∃ u : ℕ → ℂ → ℝ, (∀ j, ContDiff ℝ 2 (u j)) ∧
        TendstoUniformlyOn u
          (fun t => (prescribedEnvelope Θ (cutoffObstacle μ χ k) Ψ (Γ (t, y))).toReal) atTop
          (Metric.closedBall 0 (Real.exp (-(k : ℝ) / 2))) ∧
        ∀ j, ∀ t ∈ Metric.ball (0 : ℂ) (Real.exp (-(k : ℝ) / 2)),
          -C ≤ Δ (u j) t ∧ Δ (u j) t ≤ C * Real.exp k := by
  classical
  have : CompactSpace 𝒳 := compactSpace_normalCone F hμ
  have : Nonempty 𝒳 := ⟨Γ (0, y₀)⟩
  have hμc : Continuous μ := hμ.continuous
  have hgc : ∀ k, Continuous (cutoffObstacle μ χ k) := fun k =>
    (continuous_cutoffObstacleLine hχ k).comp (continuous_snd.comp hμc)
  set ωt := (ClosedRealOneOneForm.pullback hπ.1 Θ - D'.curvature) + ddcClosedForm h hh with hωt
  set P := ClosedRealOneOneForm.pullback hπ.1 Θ with hP
  -- the point `z₀` over `p = Γ(0, y₀)`, off `Supp D'`
  have hSc : IsClosed D'.support := (ResidualNef.isComplexAnalyticSubset_support D').isClosed
  obtain ⟨z₀, hz₀⟩ :=
    AnalyticModificationStrongPullback.surjective_of_isAnalyticModification hπ (Γ (0, y₀))
  have hz₀S : z₀ ∉ D'.support := by
    intro hz
    apply hΨy₀
    have hbot : D'.weight z₀ = ⊥ := hz
    rw [← hz₀, hΨπ z₀, hbot, EReal.bot_add]
  -- a holomorphic local inverse `S` of `π` at `p`
  obtain ⟨V, S, hVo, hgV, hSg, hgS, hSs, -⟩ :=
    HolomorphicLocalInverse.exists_localInverse hπ.1 (fun h => hz₀S (hexc h))
  rw [hz₀] at hgV hSg
  -- the chart at `z₀` and a closed ball in it, off `Supp D'`
  set e := complexChartAt (n := m + 1 + 1) z₀ with he
  have hz₀e : z₀ ∈ e.val.source := mem_complexChartAt_source z₀
  have hO : IsOpen (e.val.target ∩ e.val.symm ⁻¹' D'.supportᶜ) :=
    e.val.isOpen_inter_preimage_symm hSc.isOpen_compl
  have hz₀O : e.val z₀ ∈ e.val.target ∩ e.val.symm ⁻¹' D'.supportᶜ :=
    ⟨e.val.map_source hz₀e, by rw [mem_preimage, e.val.left_inv hz₀e]; exact hz₀S⟩
  obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.mp hO _ hz₀O
  set ρ : ℝ := r / 2 with hρ
  have hρpos : 0 < ρ := by positivity
  have hcb : closedBall (e.val z₀) ρ ⊆ e.val.target ∩ e.val.symm ⁻¹' D'.supportᶜ :=
    (closedBall_subset_ball (by linarith)).trans hrO
  set K : Set 𝒵 := e.val.symm '' closedBall (e.val z₀) ρ with hKdef
  have hKc : IsCompact K := (isCompact_closedBall _ _).image_of_continuousOn
    (e.val.continuousOn_symm.mono fun y hy => (hcb hy).1)
  have hKd : Disjoint K D'.support := by
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨y, hy, rfl⟩
    exact (hcb hy).2
  -- the discs stay in the chart: a box around `(0, y₀)`
  have hScont : ContinuousOn S V := fun q hq => (hSs q hq).continuousAt.continuousWithinAt
  set O' : Set 𝒵 := e.val.source ∩ e.val ⁻¹' ball (e.val z₀) ρ with hO'def
  have hO' : IsOpen O' := e.val.isOpen_inter_preimage isOpen_ball
  have hV' : IsOpen (V ∩ S ⁻¹' O') := hScont.isOpen_inter_preimage hVo hO'
  have hpV' : Γ (0, y₀) ∈ V ∩ S ⁻¹' O' :=
    ⟨hgV, by rw [mem_preimage, hSg]; exact ⟨hz₀e, mem_ball_self hρpos⟩⟩
  have hΓc : ContinuousOn Γ G := hΓ.continuousOn
  set G' : Set (ℂ × ComplexModel (m + 1)) := G ∩ Γ ⁻¹' (V ∩ S ⁻¹' O') with hG'
  have hG'o : IsOpen G' := hΓc.isOpen_inter_preimage hG hV'
  have hy₀G' : ((0 : ℂ), y₀) ∈ G' := ⟨hy₀, hpV'⟩
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.isOpen_iff.mp hG'o _ hy₀G'
  set R : ℝ := ε₀ / 2 with hR
  have hRpos : 0 < R := by positivity
  have hmem : ∀ y ∈ ball y₀ ε₀, ∀ s ∈ ball (0 : ℂ) (2 * R),
      (s, y) ∈ G ∧ Γ (s, y) ∈ V ∧ S (Γ (s, y)) ∈ O' := by
    intro y hy s hs
    have hs' : s ∈ ball (0 : ℂ) ε₀ := by
      rw [mem_ball] at hs ⊢; linarith
    have : (s, y) ∈ ball ((0 : ℂ), y₀) ε₀ := by
      rw [← ball_prod_same]; exact ⟨hs', hy⟩
    obtain ⟨h1, h2, h3⟩ := hball this
    exact ⟨h1, h2, h3⟩
  -- WN-FL3: Lemma 7.5 on the resolution
  obtain ⟨a, C₀, ha, hC₀, hline⟩ :=
    exists_lineBound_cutoffEnvelope (contMDiff_deformationProjP1 F hμ.contMDiff) hΨ hπ D' hh hΨπ
      hKah hχ
  -- `Ψ ∘ π` on `K`
  obtain ⟨Cw, hCw⟩ :=
    MeteredDivisorWeightBounds.exists_bound_of_isCompact_disjoint_support D' hKc hKd
  obtain ⟨Bh, hBh⟩ := isCompact_univ.exists_bound_of_continuousOn
    (ProductTestForms.ChartSmooth.continuous hh).continuousOn
  set C₁ : ℝ := Cw + Bh with hC₁
  have hΨK : ∀ z ∈ K, Ψ (π z) = (((D'.weight z).toReal + h z : ℝ) : EReal) ∧
      -C₁ ≤ (D'.weight z).toReal + h z := by
    intro z hz
    obtain ⟨h1, h2⟩ := hCw z hz
    have hne_bot : D'.weight z ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) h1
    have hne_top : D'.weight z ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) h2
    have hreal := (EReal.coe_toReal hne_top hne_bot).symm
    refine ⟨by rw [hΨπ z, hreal, EReal.toReal_coe, ← EReal.coe_add], ?_⟩
    rw [hreal] at h1
    have h1' := EReal.coe_le_coe_iff.mp h1
    have hhz := hBh z (mem_univ z)
    rw [Real.norm_eq_abs] at hhz
    linarith [neg_abs_le (h z)]
  -- the competitor `Ψ + c₀` of `v_0`
  obtain ⟨MΨ, hMΨ⟩ := hΨ.exists_global_upper_bound
  obtain ⟨w₀, -, hw₀⟩ := isCompact_univ.exists_isMinOn univ_nonempty (hgc 0).continuousOn
  set c₀ : ℝ := cutoffObstacle μ χ 0 w₀ - MΨ with hc₀
  have hcomp : (fun x => Ψ x + (c₀ : EReal)) ∈
      prescribedCompetitors Θ (cutoffObstacle μ χ 0) Ψ := by
    refine ⟨hΨ.add_const c₀, fun x => ?_,
      (SGPT.PSH.singularityLE_iff_exists_real _ _).mpr ⟨c₀, fun x => le_rfl⟩⟩
    calc Ψ x + (c₀ : EReal) ≤ (MΨ : EReal) + (c₀ : EReal) := add_le_add (hMΨ x) le_rfl
      _ = (cutoffObstacle μ χ 0 w₀ : EReal) := by rw [← EReal.coe_add, hc₀]; ring_nf
      _ ≤ (cutoffObstacle μ χ 0 x : EReal) := EReal.coe_le_coe_iff.mpr (hw₀ (mem_univ x))
  -- the coefficients of `ω̃` and `P` on the closed ball
  obtain ⟨Mω, hMω⟩ := (isCompact_closedBall (e.val z₀) ρ).exists_bound_of_continuousOn
    ((ωt.val.smooth e).continuousOn.mono fun y hy => (hcb hy).1)
  obtain ⟨MP, hMP⟩ := (isCompact_closedBall (e.val z₀) ρ).exists_bound_of_continuousOn
    ((P.val.smooth e).continuousOn.mono fun y hy => (hcb hy).1)
  have hMω0 : 0 ≤ Mω := (norm_nonneg _).trans (hMω _ (mem_closedBall_self hρpos.le))
  have hMP0 : 0 ≤ MP := (norm_nonneg _).trans (hMP _ (mem_closedBall_self hρpos.le))
  -- the discs and the Cauchy bound
  have hγ : ∀ y ∈ ball y₀ ε₀, ∀ s ∈ ball (0 : ℂ) (2 * R),
      ContDiffAt ℂ ∞ (fun s => e.val (S (Γ (s, y)))) s := by
    intro y hy s hs
    obtain ⟨h1, h2, h3⟩ := hmem y hy s hs
    have hin : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ × ComplexModel (m + 1)) ∞ (fun s : ℂ => (s, y)) s :=
      (contDiff_id.prodMk contDiff_const).contMDiff.contMDiffAt
    have hΓs : ContMDiffAt 𝓘(ℂ, ℂ × ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ Γ
        (s, y) := (hΓ _ h1).contMDiffAt (hG.mem_nhds h1)
    have h4 := (hSs _ h2).comp s (ContMDiffAt.comp (g := Γ) s hΓs hin)
    have hch : ContMDiffAt 𝓘(ℂ, ComplexModel (m + 1 + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞
        (chartAt (ComplexModel (m + 1 + 1)) z₀) (S (Γ (s, y))) :=
      (contMDiffOn_chart (n := ∞)).contMDiffAt
        ((chartAt (ComplexModel (m + 1 + 1)) z₀).open_source.mem_nhds h3.1)
    exact contMDiffAt_iff_contDiffAt.mp (hch.comp s h4)
  set Mv : ℝ := 2 * ρ / R with hMv
  have hMv0 : 0 ≤ Mv := by positivity
  have hγbd : ∀ y ∈ ball y₀ ε₀, ∀ t : ℂ, ‖t‖ ≤ R →
      ‖deriv (fun s => e.val (S (Γ (s, y)))) t‖ ≤ Mv := by
    intro y hy t ht
    refine norm_deriv_le_of_mapsTo_ball hRpos (p := e.val z₀)
      (fun s hs => ((hγ y hy s hs).differentiableAt (by simp)).differentiableWithinAt)
      (fun s hs => ?_) ht
    have h2 := (hmem y hy s hs).2.2.2
    rw [mem_preimage, mem_ball, dist_eq_norm] at h2
    exact h2.le
  -- the threshold
  obtain ⟨k₁, hk₁⟩ : ∃ k₁ : ℕ, ∀ k : ℕ, k₁ ≤ k → Real.exp (-(k : ℝ) / 2) < R := by
    have ht : Tendsto (fun k : ℕ => Real.exp (-(k : ℝ) / 2)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun k : ℕ => -(k : ℝ) / 2) atTop atBot :=
        (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop).atBot_div_const
          (by norm_num)
      exact Real.tendsto_exp_atBot.comp h1
    exact eventually_atTop.mp ((tendsto_order.mp ht).2 R hRpos)
  -- the constants
  set Cb : ℝ := |C₁| + |c₀| with hCb
  set C₂ : ℝ := 4 * Real.pi * MP * Mv ^ 2 with hC₂
  set C₃ : ℝ := 4 * Real.pi * ((C₀ * Real.exp (a * C₁) + 1) * Mω + MP) * Mv ^ 2 with hC₃
  refine ⟨ε₀, hε₀, max Cb (max C₂ C₃), k₁, fun k hk y hy => ?_⟩
  have hrk : Real.exp (-(k : ℝ) / 2) < R := hk₁ k hk
  -- the disc `γ = e ∘ S ∘ Γ(·, y)` and the identification `Γ(·, y) = π ∘ S ∘ Γ(·, y)`
  set γ : ℂ → ComplexModel (m + 1 + 1) := fun s => e.val (S (Γ (s, y))) with hγdef
  have hσS : ∀ t ∈ ball (0 : ℂ) (2 * R), π (S (Γ (t, y))) = Γ (t, y) := fun t ht =>
    hgS _ (hmem y hy t ht).2.1
  have hSe : ∀ t ∈ ball (0 : ℂ) (2 * R), e.val.symm (γ t) = S (Γ (t, y)) :=
    fun t ht => e.val.left_inv (hmem y hy t ht).2.2.1
  have hγball : ∀ t ∈ ball (0 : ℂ) (2 * R), γ t ∈ closedBall (e.val z₀) ρ :=
    fun t ht => ball_subset_closedBall (hmem y hy t ht).2.2.2
  have hγK : ∀ t ∈ ball (0 : ℂ) (2 * R), S (Γ (t, y)) ∈ K :=
    fun t ht => ⟨γ t, hγball t ht, hSe t ht⟩
  have hdisc : ∀ t ∈ closedBall (0 : ℂ) (Real.exp (-(k : ℝ) / 2)), t ∈ ball (0 : ℂ) R := by
    intro t ht
    rw [mem_closedBall] at ht
    rw [mem_ball]
    linarith
  have hRR : ball (0 : ℂ) R ⊆ ball (0 : ℂ) (2 * R) := ball_subset_ball (by linarith)
  -- `g_k ≤ -k` on the disc
  have hgk : ∀ t : ℂ, ‖t‖ ≤ Real.exp (-(k : ℝ) / 2) → t ∈ ball (0 : ℂ) (2 * R) →
      cutoffObstacle μ χ k (Γ (t, y)) ≤ -k := by
    intro t ht ht2
    show cutoffObstacleLine χ k (μ (Γ (t, y))).2 ≤ -k
    rw [hΓμ _ (hmem y hy t ht2).1]
    exact cutoffObstacleLine_affineLinePoint_le hχ k (exp_mul_norm_sq_le_one ht)
  refine ⟨fun t ht => ?_, ?_⟩
  · -- the bound
    have ht2 : t ∈ ball (0 : ℂ) (2 * R) := hRR (hdisc t (mem_closedBall.mpr (by simpa using ht)))
    refine ⟨(hmem y hy t ht2).1, ?_⟩
    have hzK := hγK t ht2
    have hΨz : ((-C₁ : ℝ) : EReal) ≤ Ψ (Γ (t, y)) := by
      rw [← hσS t ht2, (hΨK _ hzK).1]
      exact EReal.coe_le_coe_iff.mpr (hΨK _ hzK).2
    have hlo : (((-C₁ + c₀ - k : ℝ)) : EReal) ≤
        prescribedEnvelope Θ (cutoffObstacle μ χ k) Ψ (Γ (t, y)) := by
      calc (((-C₁ + c₀ - k : ℝ)) : EReal) = (((-C₁ : ℝ) : EReal) + (c₀ : EReal)) +
            ((-(k : ℝ) : ℝ) : EReal) := by rw [← EReal.coe_add, ← EReal.coe_add]; ring_nf
        _ ≤ (Ψ (Γ (t, y)) + (c₀ : EReal)) + ((-(k : ℝ) : ℝ) : EReal) :=
            add_le_add (add_le_add hΨz le_rfl) le_rfl
        _ ≤ prescribedEnvelope Θ (cutoffObstacle μ χ 0) Ψ (Γ (t, y)) +
              ((-(k : ℝ) : ℝ) : EReal) :=
            add_le_add (le_prescribedEnvelope hcomp _) le_rfl
        _ ≤ _ := prescribedEnvelope_cutoffObstacle_zero_le hχ Θ Ψ k _
    have hhi : prescribedEnvelope Θ (cutoffObstacle μ χ k) Ψ (Γ (t, y)) ≤ (((-k : ℝ)) : EReal) :=
      (prescribedEnvelope_le (hgc k) _).trans (EReal.coe_le_coe_iff.mpr (hgk t ht ht2))
    have hne_bot : prescribedEnvelope Θ (cutoffObstacle μ χ k) Ψ (Γ (t, y)) ≠ ⊥ :=
      ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hlo
    have hne_top : prescribedEnvelope Θ (cutoffObstacle μ χ k) Ψ (Γ (t, y)) ≠ ⊤ :=
      ne_top_of_le_ne_top (EReal.coe_ne_top _) hhi
    have hreal := (EReal.coe_toReal hne_top hne_bot).symm
    rw [hreal] at hlo hhi
    have h1 := EReal.coe_le_coe_iff.mp hlo
    have h2 := EReal.coe_le_coe_iff.mp hhi
    refine ⟨hne_bot, (abs_le.mpr ⟨by linarith [neg_abs_le c₀, le_abs_self C₁, neg_abs_le C₁], by
      linarith [abs_nonneg c₀, abs_nonneg C₁]⟩).trans (le_max_left _ _)⟩
  -- WN-FL3's approximants for this `k`
  obtain ⟨hreal, heq, happrox⟩ := hline k
  obtain ⟨uj, huj, hconv, hKj, hbdj⟩ := happrox K hKc hKd
  obtain ⟨J, hJ⟩ := eventually_atTop.mp (hbdj 1 one_pos)
  -- the `C²` functions on the disc of radius `2R`
  set f : ℕ → ComplexModel (m + 1 + 1) → ℝ := fun i ζ =>
    uj i (e.val.symm ζ) + (D'.weight (e.val.symm ζ)).toReal + h (e.val.symm ζ) with hfdef
  have hfC : ∀ i, ∀ ζ ∈ closedBall (e.val z₀) ρ, ContDiffAt ℝ 2 (f i) ζ := by
    intro i ζ hζ
    have hζO := hcb hζ
    have hnhds : e.val.target ∩ e.val.symm ⁻¹' D'.supportᶜ ∈ 𝓝 ζ := hO.mem_nhds hζO
    have h1 : ContDiffAt ℝ ∞ (fun ζ => uj i (e.val.symm ζ)) ζ :=
      (huj i e).contDiffAt (e.val.open_target.mem_nhds hζO.1)
    have h2 : ContDiffAt ℝ ∞ (fun ζ => (D'.weight (e.val.symm ζ)).toReal) ζ :=
      (chartSmoothOn_meteredWeight_toReal D' e).contDiffAt hnhds
    have h3 : ContDiffAt ℝ ∞ (fun ζ => h (e.val.symm ζ)) ζ :=
      (hh e).contDiffAt (e.val.open_target.mem_nhds hζO.1)
    exact ((h1.add h2).add h3).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hγ2 : ∀ s ∈ ball (0 : ℂ) (2 * R), ContDiffAt ℂ 2 γ s := fun s hs =>
    (hγ y hy s hs).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hUC : ∀ i, ContDiffOn ℝ 2 (fun s => f i (γ s)) (ball (0 : ℂ) (2 * R)) := by
    intro i s hs
    exact ((hfC i (γ s) (hγball s hs)).comp s ((hγ2 s hs).restrict_scalars ℝ)).contDiffWithinAt
  choose Vf hVf using fun i => exists_contDiff_two_eqOn_closedBall (c := (0 : ℂ)) hRpos
    (by linarith : R < 2 * R) (hUC i)
  refine ⟨fun i => Vf (i + J), fun i => (hVf (i + J)).1, ?_, fun i t ht => ?_⟩
  · -- uniform convergence on the closed disc
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hev := (Metric.tendstoUniformly_iff.mp hconv ε hε)
    have hev' := (tendsto_add_atTop_nat J).eventually hev
    filter_upwards [hev'] with i hi t ht
    have htR := hdisc t ht
    have ht2 := hRR htR
    have hzK := hγK t ht2
    set z := S (Γ (t, y)) with hz
    have hΓz : Γ (t, y) = π z := (hσS t ht2).symm
    rw [hΓz, heq z, hreal z, (hΨK z hzK).1, ← EReal.coe_add, EReal.toReal_coe]
    have hV : Vf (i + J) t = f (i + J) (γ t) :=
      (hVf (i + J)).2.1 (ball_subset_closedBall htR)
    simp only [hV, hfdef, hSe t ht2]
    have := hi z
    rw [dist_eq_norm, Real.norm_eq_abs] at this ⊢
    calc |((rooftopEnvelope ωt.val (fun y => (cutoffObstacle μ χ k (π y) : EReal) - Ψ (π y))
            z).toReal + ((D'.weight z).toReal + h z)) -
          (uj (i + J) z + (D'.weight z).toReal + h z)|
        = |(rooftopEnvelope ωt.val (fun y => (cutoffObstacle μ χ k (π y) : EReal) - Ψ (π y))
            z).toReal - uj (i + J) z| := by ring_nf
      _ < ε := this
  · -- the Laplacian bounds on the open disc
    have htR : t ∈ ball (0 : ℂ) R := by
      rw [mem_ball] at ht ⊢; linarith
    have ht2 := hRR htR
    have htn : ‖t‖ ≤ R := by
      rw [mem_ball, dist_zero_right] at htR; exact htR.le
    have hΔ : Δ (Vf (i + J)) t = Δ (fun s => f (i + J) (γ s)) t :=
      (InnerProductSpace.laplacian_congr_nhds ((hVf (i + J)).2.2 t htR)).eq_of_nhds
    have hchain := laplacian_comp_holomorphic_eq_smoothDDC (hfC (i + J) (γ t) (hγball t ht2))
      (hγ2 t ht2)
    have hγt : γ t ∈ e.val.target := (hcb (hγball t ht2)).1
    have hγS : e.val.symm (γ t) ∉ D'.support := (hcb (hγball t ht2)).2
    have hddc := smoothDDC_chart_resolved P D' hh (huj (i + J)) e hγt hγS
    set v := deriv γ t with hv
    have hvn : ‖v‖ ≤ Mv := hγbd y hy t htn
    obtain ⟨A, hA⟩ : ∃ A, A = (ωt + ddcClosedForm (uj (i + J)) (huj (i + J))).val.coeff e (γ t)
      ![v, Complex.I • v] := ⟨_, rfl⟩
    obtain ⟨Ω, hΩ⟩ : ∃ Ω, Ω = ωt.val.coeff e (γ t) ![v, Complex.I • v] := ⟨_, rfl⟩
    obtain ⟨Pv, hPv⟩ : ∃ Pv, Pv = P.val.coeff e (γ t) ![v, Complex.I • v] := ⟨_, rfl⟩
    have hΔeq : Δ (Vf (i + J)) t = 4 * Real.pi * (A - Pv) := by
      rw [hΔ]
      have h1 : Δ (fun s => f (i + J) (γ s)) t =
          4 * Real.pi * smoothDDC (f (i + J)) (γ t) ![v, Complex.I • v] := hchain
      have h2 : smoothDDC (f (i + J)) (γ t) =
          (ωt + ddcClosedForm (uj (i + J)) (huj (i + J))).val.coeff e (γ t) -
            P.val.coeff e (γ t) := hddc
      rw [h1, h2, ContinuousAlternatingMap.sub_apply, ← hA, ← hPv]
    -- the three line quantities
    have hA0 : 0 ≤ A := by
      rw [hA]; exact KahlerBackground.isSemipositive ⟨_, hKj (i + J)⟩ e (γ t) hγt v
    have hΩ0 : 0 ≤ Ω := by
      rw [hΩ]; exact KahlerBackground.isSemipositive ⟨ωt, hKah⟩ e (γ t) hγt v
    have hv2 : ‖v‖ ^ 2 ≤ Mv ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hvn 2
    have hΩle : Ω ≤ Mω * Mv ^ 2 := by
      have h1 := abs_apply_line_le (ωt.val.coeff e (γ t)) v
      have h2 := hMω (γ t) (hγball t ht2)
      calc Ω ≤ |Ω| := le_abs_self _
        _ ≤ ‖ωt.val.coeff e (γ t)‖ * ‖v‖ ^ 2 := by rw [hΩ]; exact h1
        _ ≤ Mω * Mv ^ 2 := mul_le_mul h2 hv2 (sq_nonneg _) hMω0
    have hPle : |Pv| ≤ MP * Mv ^ 2 := by
      have h1 := abs_apply_line_le (P.val.coeff e (γ t)) v
      have h2 := hMP (γ t) (hγball t ht2)
      calc |Pv| ≤ ‖P.val.coeff e (γ t)‖ * ‖v‖ ^ 2 := by rw [hPv]; exact h1
        _ ≤ MP * Mv ^ 2 := mul_le_mul h2 hv2 (sq_nonneg _) hMP0
    -- the line bound of WN-FL3 on the disc
    have hb : C₀ * Real.exp k * Real.exp (a * (cutoffObstacle μ χ k (π (e.val.symm (γ t))) -
        (Ψ (π (e.val.symm (γ t)))).toReal + k)) ≤ C₀ * Real.exp (a * C₁) * Real.exp k := by
      rw [hSe t ht2]
      have hzK := hγK t ht2
      have hg : cutoffObstacle μ χ k (π (S (Γ (t, y)))) ≤ -k := by
        rw [hσS t ht2]
        exact hgk t (by rw [mem_ball, dist_zero_right] at ht; exact ht.le) ht2
      have hΨz : -C₁ ≤ (Ψ (π (S (Γ (t, y))))).toReal := by
        rw [(hΨK _ hzK).1, EReal.toReal_coe]; exact (hΨK _ hzK).2
      have hexp : Real.exp (a * (cutoffObstacle μ χ k (π (S (Γ (t, y)))) -
          (Ψ (π (S (Γ (t, y))))).toReal + k)) ≤ Real.exp (a * C₁) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith) ha)
      calc C₀ * Real.exp k * Real.exp (a * (cutoffObstacle μ χ k (π (S (Γ (t, y)))) -
            (Ψ (π (S (Γ (t, y))))).toReal + k))
          ≤ C₀ * Real.exp k * Real.exp (a * C₁) :=
            mul_le_mul_of_nonneg_left hexp (by positivity)
        _ = C₀ * Real.exp (a * C₁) * Real.exp k := by ring
    have hAle : A ≤ (C₀ * Real.exp (a * C₁) * Real.exp k + 1) * Ω := by
      have h1 := hJ (i + J) (by omega) e (γ t) hγt (by rw [hSe t ht2]; exact hγK t ht2) v
      rw [hA]
      calc _ ≤ _ := h1
        _ ≤ (C₀ * Real.exp (a * C₁) * Real.exp k + 1) * Ω := by
          rw [hΩ]
          exact mul_le_mul_of_nonneg_right (by linarith) (hΩ ▸ hΩ0)
    have hek : 1 ≤ Real.exp k := Real.one_le_exp (Nat.cast_nonneg k)
    have hpi : 0 < Real.pi := Real.pi_pos
    have hMv2 : 0 ≤ Mv ^ 2 := sq_nonneg _
    have hpi4 : (0 : ℝ) ≤ 4 * Real.pi := by positivity
    have hB : 0 ≤ C₀ * Real.exp (a * C₁) := mul_nonneg hC₀ (Real.exp_pos _).le
    have hMM : 0 ≤ Mω * Mv ^ 2 := mul_nonneg hMω0 hMv2
    show -max Cb (max C₂ C₃) ≤ Δ (Vf (i + J)) t ∧
      Δ (Vf (i + J)) t ≤ max Cb (max C₂ C₃) * Real.exp k
    rw [hΔeq]
    constructor
    · -- lower bound
      have hlow : -(MP * Mv ^ 2) ≤ A - Pv := by linarith [le_abs_self Pv]
      have h1 := mul_le_mul_of_nonneg_left hlow hpi4
      have h2 : C₂ ≤ max Cb (max C₂ C₃) := (le_max_left _ _).trans (le_max_right _ _)
      have h3 : -C₂ = 4 * Real.pi * -(MP * Mv ^ 2) := by rw [hC₂]; ring
      linarith
    · -- upper bound
      have hcoef : C₀ * Real.exp (a * C₁) * Real.exp k + 1 ≤
          (C₀ * Real.exp (a * C₁) + 1) * Real.exp k := by
        have : (C₀ * Real.exp (a * C₁) + 1) * Real.exp k =
            C₀ * Real.exp (a * C₁) * Real.exp k + Real.exp k := by ring
        rw [this]; linarith
      have h1 : A ≤ (C₀ * Real.exp (a * C₁) + 1) * Real.exp k * (Mω * Mv ^ 2) := by
        calc A ≤ (C₀ * Real.exp (a * C₁) * Real.exp k + 1) * Ω := hAle
          _ ≤ (C₀ * Real.exp (a * C₁) * Real.exp k + 1) * (Mω * Mv ^ 2) :=
            mul_le_mul_of_nonneg_left hΩle (by positivity)
          _ ≤ (C₀ * Real.exp (a * C₁) + 1) * Real.exp k * (Mω * Mv ^ 2) :=
            mul_le_mul_of_nonneg_right hcoef hMM
      have h2 : -Pv ≤ MP * Mv ^ 2 * Real.exp k := by
        have h0 : MP * Mv ^ 2 ≤ MP * Mv ^ 2 * Real.exp k :=
          le_mul_of_one_le_right (mul_nonneg hMP0 hMv2) hek
        linarith [neg_le_abs Pv]
      have h3 : 4 * Real.pi * (A - Pv) ≤ C₃ * Real.exp k := by
        calc 4 * Real.pi * (A - Pv) = 4 * Real.pi * A + 4 * Real.pi * (-Pv) := by ring
          _ ≤ 4 * Real.pi * ((C₀ * Real.exp (a * C₁) + 1) * Real.exp k * (Mω * Mv ^ 2)) +
              4 * Real.pi * (MP * Mv ^ 2 * Real.exp k) :=
            add_le_add (mul_le_mul_of_nonneg_left h1 hpi4) (mul_le_mul_of_nonneg_left h2 hpi4)
          _ = C₃ * Real.exp k := by rw [hC₃]; ring
      have h4 : C₃ ≤ max Cb (max C₂ C₃) := (le_max_right _ _).trans (le_max_right _ _)
      have h5 : C₃ * Real.exp k ≤ max Cb (max C₂ C₃) * Real.exp k :=
        mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le
      linarith

/-- **`tok-wn-fl4:disc-laplacian`** (WN21 Lemma 7.5 along holomorphic families of fibre discs,
with a threshold `k₀`): `ExcDiscLaplacianStatement F` holds. -/
theorem excDiscLaplacian : ExcDiscLaplacianStatement F := by
  intro 𝒳 _ _ _ μ hμ Θ Ψ hΨ 𝒵 _ _ _ π hπ D' h hh h𝒵c h𝒵conn hexc hΨπ hKah χ hχ G Γ hG hΓ hΓμ
    y₀ hy₀ hΨy₀
  exact exists_excDisc_laplacian F hμ hΨ
    (HironakaChowLemma.isAnalyticModification_of_isBlowupSequence hπ) D' hexc hh hΨπ hKah hχ hG hΓ
    hΓμ hy₀ hΨy₀

end SGPT.Okounkov.TranscendentalWN
