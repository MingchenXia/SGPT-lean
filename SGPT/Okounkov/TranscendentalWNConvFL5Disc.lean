import SGPT.Okounkov.TranscendentalWNConvFL3Laplacian
import SGPT.Okounkov.TranscendentalWNConvFL3Disc
import SGPT.Okounkov.TranscendentalWNConvFL5Chain
import SGPT.Foundations.Analysis.Pending.HolomorphicLocalInverse

/-!
# WN21 Lemma 7.5 along the discs `t ↦ μ⁻¹(x, t)` near `X' \ ℰ`

Blueprint `claude-tok-wn-fl5`, nodes `tok-wn-fl5:disc-inverse`, `tok-wn-fl5:disc-ddc`,
`tok-wn-fl5:disc-laplacian`; source WN21 §7, Lemma 7.5 (`references/wn21-restricted-volume`),
with the threshold `k₀` of `tok-wn-fl3:disc-statement-k0`.

`strictDiscLaplacianFrom : StrictDiscLaplacianFromStatement F` (and `strictDiscLaplacian :
StrictDiscLaplacianStatement F`, the corrected statement, the same proposition): for `x₀ ∉ Z` with `Ψ(ι x₀) ≠ -∞`
there are an open `U ∋ x₀`, `C` and `k₀` such that for all `k ≥ k₀`, `x ∈ U` and every map `σ`
with `μ ∘ σ = (x, ·)`: `|v_k(σ t) + k| ≤ C` for `|t| ≤ e^{-k/2}`, and `t ↦ v_k(σ t)` is on that
closed disc the uniform limit of `C²` functions `U_j` on `ℂ` with `-C ≤ Δ U_j ≤ C e^k` on the open
disc (`v_k = P_Θ[Ψ](g_k)`).

## Proof

* The bound is `exists_strictDisc_bound`.
* **Discs in the resolution.**  `z₀ ∈ π⁻¹(ι x₀)` lies off `Supp D' ⊇ Exc(π)` and `ι x₀ ∉ ℰ = Exc(μ)`
  near `ι x₀`, so `μ ∘ π` has a holomorphic local inverse `S` at `(x₀, 0)`
  (`notMem_exceptionalLocus_comp`, TN `HolomorphicLocalInverse.exists_localInverse`).  In the chart
  `e` of `𝒵` at `z₀`, the discs `γ_x(t) = e(S(x, t))` are holomorphic in `t`
  (`contDiffAt_chart_comp_affineSlice`) and stay in a ball `B(e z₀, ρ)` whose closure lies in the
  chart and off `Supp D'` for `x ∈ U`, `|t| < 2R`; as `x ∉ Z`, `σ t = π(S(x, t))` (`μ` is injective
  off `ℰ`).  Cauchy's estimate bounds `|γ_x'|` on `|t| ≤ R` uniformly in `x`.
* **The Laplacian.**  By WN-FL3 (`exists_lineBound_cutoffEnvelope`), `v_k ∘ π = ṽ_k + Ψ ∘ π` and `ṽ_k` is
  a uniform limit of smooth `u_j` with `0 ≤ ω̃ + dd^c u_j ≤ (C₀ e^k e^{a(g_k ∘ π - Ψ ∘ π + k)} + 1) ω̃`
  on lines over the compact `K = e⁻¹(B̄(e z₀, ρ))` for large `j`.  Off `Supp D'`,
  `Ψ ∘ π = ψ_{D'} + h` is smooth with `dd^c(ψ_{D'} + h) = ω̃ - π^*Θ` (TN
  `exists_isSmoothLocalPotential_neg_curvature`), so with `F_j = u_j + ψ_{D'} + h`,
  `Δ_t (F_j ∘ γ_x) = 4π [(ω̃ + dd^c u_j) - π^*Θ](γ_x', iγ_x')` (`laplacian_comp_holomorphic_eq_smoothDDC`,
  `smoothDDC_chart_resolved`).  On the disc `g_k ≤ -k` and `Ψ ∘ π ≥ -C₁` on `K`, and the coefficients of
  `ω̃`, `π^*Θ` are bounded on `B̄(e z₀, ρ)`; this gives `-C ≤ Δ ≤ C e^k`.
* **Globalization**: `F_j ∘ γ_x` is `C²` on `B(0, 2R)`; a cutoff (`exists_contDiff_two_eqOn_closedBall`) makes it
  `C²` on `ℂ` without changing it near `B̄(0, R) ⊇ B̄(0, e^{-k/2})` (`k ≥ k₀`).
-/

set_option autoImplicit false

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
open scoped SGPT.Foundations.Analysis.Pending.ProductComplexManifold

/-! ### Holomorphic local inverses and discs -/

section Inverse

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z]

/-- A composite of holomorphic maps is unramified at a point where both factors are. -/
theorem notMem_exceptionalLocus_comp {f : Y → X} {g : Z → Y}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g) {z : Z}
    (hz : z ∉ exceptionalLocus n g) (hgz : g z ∉ exceptionalLocus n f) :
    z ∉ exceptionalLocus n (f ∘ g) := by
  simp only [exceptionalLocus, mem_ofPred_eq, not_not] at hz hgz ⊢
  rw [mfderiv_comp z ((hf (g z)).mdifferentiableAt (by simp)) ((hg z).mdifferentiableAt (by simp)),
    ContinuousLinearMap.coe_comp]
  exact hgz.comp hz

end Inverse

section Slice

variable {m : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X]

/-- `w ↦ (x, [w : 1])` is holomorphic, `ℂ¹ → X × ℙ¹`. -/
theorem contMDiff_affineSlice (x : X) :
    ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞
      (fun w : ComplexModel 1 => (x, (SGPT.Toric.projectiveModelChart false).symm w)) := by
  have hch : ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel 1) ∞
      (SGPT.Toric.projectiveModelChart false).symm := by
    have hmem : SGPT.Toric.projectiveModelChart false ∈
        IsManifold.maximalAtlas 𝓘(ℂ, ComplexModel 1) ∞ ProjectiveLine :=
      IsManifold.subset_maximalAtlas ⟨false, rfl⟩
    have h := contMDiffOn_symm_of_mem_maximalAtlas hmem
    rw [projectiveModelChart_target_eq] at h
    exact contMDiffOn_univ.mp h
  exact ProductComplexManifold.contMDiff_prodMk contMDiff_const hch

/-- **The discs `t ↦ e(S(x, t))` are holomorphic**: for `S : X × ℙ¹ → 𝒵` holomorphic at
`(x, t)` with `S(x, t)` in the preferred chart at `z₀`, the map `s ↦ e(S(x, s))` is holomorphic
at `t`. -/
theorem contDiffAt_chart_comp_affineSlice {𝒵 : Type u} [TopologicalSpace 𝒵]
    [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒵] [IsComplexManifold (m + 1 + 1) 𝒵]
    {S : X × ProjectiveLine → 𝒵} {x : X} {t : ℂ}
    (hS : ContMDiffAt 𝓘(ℂ, ComplexModel (m + 1 + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ S
      (x, affineLinePoint t)) {z₀ : 𝒵}
    (hz : S (x, affineLinePoint t) ∈ (chartAt (ComplexModel (m + 1 + 1)) z₀).source) :
    ContDiffAt ℂ ∞ (fun s => chartAt (ComplexModel (m + 1 + 1)) z₀ (S (x, affineLinePoint s))) t := by
  set c : ComplexModel 1 → X × ProjectiveLine :=
    fun w => (x, (SGPT.Toric.projectiveModelChart false).symm w) with hc
  have hcs : ∀ s : ℂ, c (SGPT.Toric.projectiveModelEquiv s) = (x, affineLinePoint s) := by
    intro s
    simp only [hc, projectiveModelChart_false_symm, SGPT.Toric.projectiveModelEquiv_apply_zero]
  have hS' : ContMDiffAt 𝓘(ℂ, ComplexModel (m + 1 + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ S
      (c (SGPT.Toric.projectiveModelEquiv t)) := by rw [hcs]; exact hS
  have hch : ContMDiffAt 𝓘(ℂ, ComplexModel (m + 1 + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞
      (chartAt (ComplexModel (m + 1 + 1)) z₀) (S (c (SGPT.Toric.projectiveModelEquiv t))) := by
    rw [hcs]
    exact (contMDiffOn_chart (n := ∞)).contMDiffAt
      ((chartAt (ComplexModel (m + 1 + 1)) z₀).open_source.mem_nhds hz)
  have hG : ContMDiffAt 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞
      ((chartAt (ComplexModel (m + 1 + 1)) z₀ ∘ S) ∘ c)
      (SGPT.Toric.projectiveModelEquiv t) :=
    (hch.comp _ hS').comp _ ((contMDiff_affineSlice x).contMDiffAt)
  rw [contMDiffAt_iff_contDiffAt] at hG
  have h := hG.comp t (SGPT.Toric.projectiveModelEquiv.contDiff.contDiffAt)
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  simp only [Function.comp_apply, hcs]

end Slice

/-! ### `dd^c` of `u + ψ_{D'} + h` in a chart, off `Supp D'` -/

section DDC

variable {N : ℕ} {𝒵 : Type*} [TopologicalSpace 𝒵] [ChartedSpace (ComplexModel N) 𝒵]
  [IsComplexManifold N 𝒵]

/-- A two-form on a complex line: `|α(v, iv)| ≤ ‖α‖ ‖v‖²`. -/
theorem abs_apply_line_le (α : ComplexModel N [⋀^Fin 2]→L[ℝ] ℝ) (v : ComplexModel N) :
    |α ![v, Complex.I • v]| ≤ ‖α‖ * ‖v‖ ^ 2 := by
  have h := α.le_opNorm ![v, Complex.I • v]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    norm_smul, Complex.norm_I, one_mul, Real.norm_eq_abs] at h
  calc |α ![v, Complex.I • v]| ≤ ‖α‖ * (‖v‖ * ‖v‖) := h
    _ = ‖α‖ * ‖v‖ ^ 2 := by ring

/-- **`dd^c(u + ψ_{D'} + h) = (ω̃ + dd^c u) - P` off `Supp D'`**, in a chart, for
`ω̃ = (P - Θ_{D'}) + dd^c h`. -/
theorem smoothDDC_chart_resolved (P : ClosedRealOneOneForm N 𝒵) (D' : MeteredEffectiveQDivisor N 𝒵)
    {h : 𝒵 → ℝ} (hh : ChartSmooth (n := N) h) {w : 𝒵 → ℝ} (hw : ChartSmooth (n := N) w)
    (e : ComplexChart N 𝒵) {y : ComplexModel N} (hy : y ∈ e.val.target)
    (hyS : e.val.symm y ∉ D'.support) :
    smoothDDC (fun ζ => w (e.val.symm ζ) + (D'.weight (e.val.symm ζ)).toReal + h (e.val.symm ζ)) y =
      (((P - D'.curvature) + ddcClosedForm h hh) + ddcClosedForm w hw).val.coeff e y -
        P.val.coeff e y := by
  obtain ⟨W, hyW, hpot⟩ :=
    MeteredDivisorSmoothOffSupport.exists_isSmoothLocalPotential_neg_curvature D' hyS e
      (e.val.map_target hy)
  rw [e.val.right_inv hy] at hyW
  obtain ⟨hWo, hWt, hρ, hρeq⟩ := hpot
  have hws : ContDiffOn ℝ ∞ (fun ζ => w (e.val.symm ζ)) W := (hw e).mono hWt
  have hhs : ContDiffOn ℝ ∞ (fun ζ => h (e.val.symm ζ)) W := (hh e).mono hWt
  rw [smoothDDC_add hWo (hws.add hρ) hhs hyW, smoothDDC_add hWo hws hρ hyW, hρeq hyW]
  rw [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_add,
    BlowupBigPullback.coeff_sub, ddcClosedForm_coeff, ddcClosedForm_coeff]
  change smoothDDC (fun ζ => w (e.val.symm ζ)) y + (-D'.curvature).val.coeff e y +
      smoothDDC (fun ζ => h (e.val.symm ζ)) y = _
  rw [ClosedRealOneOneForm.coeff_neg]
  abel

end DDC

/-! ### Lemma 7.5 along the discs -/

section Disc

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))
variable {𝒳 : Type u} [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
  [IsComplexManifold (m + 1 + 1) 𝒳] {μ : 𝒳 → F.carrier × ProjectiveLine}

/-- **WN21 Lemma 7.5 along the discs near `X' \ ℰ`, with a threshold `k₀`** (general form of
`StrictDiscLaplacianFromStatement`). -/
theorem exists_strictDisc_laplacian (hμ : IsNormalConeDeformation F μ)
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
    {ι : F.carrier → 𝒳} (hιμ : ∀ x, μ (ι x) = (x, projectiveZero))
    {x₀ : F.carrier} (hx₀ : x₀ ∉ F.flag (1 : Fin (m + 2))) (hΨx₀ : Ψ (ι x₀) ≠ ⊥) :
    ∃ U : Set F.carrier, IsOpen U ∧ x₀ ∈ U ∧ ∃ C : ℝ, ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ x ∈ U,
      ∀ σ : ℂ → 𝒳, (∀ t, μ (σ t) = (x, affineLinePoint t)) →
        (∀ t : ℂ, ‖t‖ ≤ Real.exp (-(k : ℝ) / 2) →
          prescribedEnvelope Θ (cutoffObstacle μ χ k) Ψ (σ t) ≠ ⊥ ∧
          |(prescribedEnvelope Θ (cutoffObstacle μ χ k) Ψ (σ t)).toReal + k| ≤ C) ∧
        ∃ u : ℕ → ℂ → ℝ, (∀ j, ContDiff ℝ 2 (u j)) ∧
          TendstoUniformlyOn u
            (fun t => (prescribedEnvelope Θ (cutoffObstacle μ χ k) Ψ (σ t)).toReal) atTop
            (Metric.closedBall 0 (Real.exp (-(k : ℝ) / 2))) ∧
          ∀ j, ∀ t ∈ Metric.ball (0 : ℂ) (Real.exp (-(k : ℝ) / 2)),
            -C ≤ Δ (u j) t ∧ Δ (u j) t ≤ C * Real.exp k := by
  classical
  have : CompactSpace 𝒳 := compactSpace_normalCone F hμ
  set ωt := (ClosedRealOneOneForm.pullback hπ.1 Θ - D'.curvature) + ddcClosedForm h hh with hωt
  set P := ClosedRealOneOneForm.pullback hπ.1 Θ with hP
  -- the point `z₀` over `ι x₀`, off `Supp D'`
  have hSc : IsClosed D'.support := (ResidualNef.isComplexAnalyticSubset_support D').isClosed
  obtain ⟨z₀, hz₀⟩ :=
    AnalyticModificationStrongPullback.surjective_of_isAnalyticModification hπ (ι x₀)
  have hz₀S : z₀ ∉ D'.support := by
    intro hz
    apply hΨx₀
    have hbot : D'.weight z₀ = ⊥ := hz
    rw [← hz₀, hΨπ z₀, hbot, EReal.bot_add]
  -- a holomorphic local inverse `S` of `μ ∘ π` at `(x₀, 0)`
  have hq₀ : μ (ι x₀) ∉ deformationCentre F := by
    rw [hιμ, mem_deformationCentre_iff]
    exact fun h => hx₀ h.1
  have hexcμ : ι x₀ ∉ exceptionalLocus (m + 1 + 1) μ := fun h =>
    Set.disjoint_left.mp (isIsomorphismOver_normalCone F hμ).2
      (show ι x₀ ∈ μ ⁻¹' (deformationCentre F)ᶜ from hq₀) h
  have hexcg : z₀ ∉ exceptionalLocus (m + 1 + 1) (μ ∘ π) :=
    notMem_exceptionalLocus_comp hμ.contMDiff hπ.1 (fun h => hz₀S (hexc h))
      (by rw [hz₀]; exact hexcμ)
  obtain ⟨V, S, hVo, hgV, hSg, hgS, hSs, -⟩ :=
    HolomorphicLocalInverse.exists_localInverse (hμ.contMDiff.comp hπ.1) hexcg
  have hgz₀ : (μ ∘ π) z₀ = (x₀, projectiveZero) := by
    show μ (π z₀) = _
    rw [hz₀, hιμ]
  rw [hgz₀] at hgV hSg
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
  -- the discs stay in the chart: a product neighbourhood of `(x₀, 0)`
  have hScont : ContinuousOn S V := fun q hq => (hSs q hq).continuousAt.continuousWithinAt
  set O' : Set 𝒵 := e.val.source ∩ e.val ⁻¹' ball (e.val z₀) ρ with hO'def
  have hO' : IsOpen O' := e.val.isOpen_inter_preimage isOpen_ball
  have hV' : IsOpen (V ∩ S ⁻¹' O') := hScont.isOpen_inter_preimage hVo hO'
  have hq₀V' : ((x₀, projectiveZero) : F.carrier × ProjectiveLine) ∈ V ∩ S ⁻¹' O' :=
    ⟨hgV, by rw [mem_preimage, hSg]; exact ⟨hz₀e, mem_ball_self hρpos⟩⟩
  have hj : Continuous fun p : F.carrier × ℂ => (p.1, affineLinePoint p.2) :=
    continuous_fst.prodMk ((SGPT.Toric.projectiveLineHomeomorph.continuous.comp
      OnePoint.continuous_coe).comp continuous_snd)
  have hnhds : (fun p : F.carrier × ℂ => (p.1, affineLinePoint p.2)) ⁻¹' (V ∩ S ⁻¹' O') ∈
      𝓝 ((x₀, 0) : F.carrier × ℂ) :=
    hj.continuousAt.preimage_mem_nhds (hV'.mem_nhds (by
      show (x₀, affineLinePoint 0) ∈ _
      rw [affineLinePoint_zero]; exact hq₀V'))
  obtain ⟨u, hu, w, hw, huw⟩ := mem_nhds_prod_iff.mp hnhds
  obtain ⟨r₀, hr₀, hr₀w⟩ := Metric.mem_nhds_iff.mp hw
  set R : ℝ := r₀ / 2 with hR
  have hRpos : 0 < R := by positivity
  have hmem : ∀ x ∈ u, ∀ s ∈ ball (0 : ℂ) (2 * R),
      (x, affineLinePoint s) ∈ V ∧ S (x, affineLinePoint s) ∈ O' := by
    intro x hx s hs
    have hs' : s ∈ ball (0 : ℂ) r₀ := by
      rw [mem_ball] at hs ⊢; linarith
    exact huw (mk_mem_prod hx (hr₀w hs'))
  -- WN-FL3: the bound, and Lemma 7.5 on the resolution
  obtain ⟨U₀, hU₀o, hx₀U₀, Cb, kb, hbd⟩ :=
    exists_strictDisc_bound F hμ hΨ hπ D' hh hΨπ hχ hιμ hx₀ hΨx₀
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
  -- the coefficients of `ω̃` and `P` on the closed ball
  obtain ⟨Mω, hMω⟩ := (isCompact_closedBall (e.val z₀) ρ).exists_bound_of_continuousOn
    ((ωt.val.smooth e).continuousOn.mono fun y hy => (hcb hy).1)
  obtain ⟨MP, hMP⟩ := (isCompact_closedBall (e.val z₀) ρ).exists_bound_of_continuousOn
    ((P.val.smooth e).continuousOn.mono fun y hy => (hcb hy).1)
  have hMω0 : 0 ≤ Mω := (norm_nonneg _).trans (hMω _ (mem_closedBall_self hρpos.le))
  have hMP0 : 0 ≤ MP := (norm_nonneg _).trans (hMP _ (mem_closedBall_self hρpos.le))
  -- the discs and the Cauchy bound
  have hγ : ∀ x ∈ u, ∀ s ∈ ball (0 : ℂ) (2 * R),
      ContDiffAt ℂ ∞ (fun s => e.val (S (x, affineLinePoint s))) s := fun x hx s hs =>
    contDiffAt_chart_comp_affineSlice (hSs _ (hmem x hx s hs).1) (hmem x hx s hs).2.1
  set Mv : ℝ := 2 * ρ / R with hMv
  have hMv0 : 0 ≤ Mv := by positivity
  have hγbd : ∀ x ∈ u, ∀ t : ℂ, ‖t‖ ≤ R →
      ‖deriv (fun s => e.val (S (x, affineLinePoint s))) t‖ ≤ Mv := by
    intro x hx t ht
    refine norm_deriv_le_of_mapsTo_ball hRpos (p := e.val z₀)
      (fun s hs => ((hγ x hx s hs).differentiableAt (by simp)).differentiableWithinAt)
      (fun s hs => ?_) ht
    have h2 := (hmem x hx s hs).2.2
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
  set C₂ : ℝ := 4 * Real.pi * MP * Mv ^ 2 with hC₂
  set C₃ : ℝ := 4 * Real.pi * ((C₀ * Real.exp (a * C₁) + 1) * Mω + MP) * Mv ^ 2 with hC₃
  have hZo : IsOpen (F.flag (1 : Fin (m + 2)))ᶜ := F.firstDivisor.1.isOpen_compl
  refine ⟨interior u ∩ U₀ ∩ (F.flag (1 : Fin (m + 2)))ᶜ,
    (isOpen_interior.inter hU₀o).inter hZo,
    ⟨⟨mem_interior_iff_mem_nhds.mpr hu, hx₀U₀⟩, hx₀⟩, max Cb (max C₂ C₃), max kb k₁, ?_⟩
  intro k hk x hx σ hσ
  have hkb : kb ≤ k := le_trans (le_max_left _ _) hk
  have hrk : Real.exp (-(k : ℝ) / 2) < R := hk₁ k (le_trans (le_max_right _ _) hk)
  have hxu : x ∈ u := interior_subset hx.1.1
  have hxZ : x ∉ F.flag (1 : Fin (m + 2)) := hx.2
  refine ⟨fun t ht => ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := hbd k hkb x hx.1.2 t ht (σ t) (hσ t)
    exact ⟨h1, h2.trans (le_max_left _ _)⟩
  -- the disc `γ = e ∘ S ∘ (x, ·)` and the identification `σ = π ∘ S ∘ (x, ·)`
  set γ : ℂ → ComplexModel (m + 1 + 1) := fun s => e.val (S (x, affineLinePoint s)) with hγdef
  have hσS : ∀ t ∈ ball (0 : ℂ) (2 * R), σ t = π (S (x, affineLinePoint t)) := by
    intro t ht
    have h1 : μ (π (S (x, affineLinePoint t))) = (x, affineLinePoint t) :=
      hgS _ (hmem x hxu t ht).1
    symm
    refine eq_of_map_eq_of_notMem F hμ ?_ (by rw [h1, hσ t])
    rw [h1, mem_deformationCentre_iff]
    exact fun h => hxZ h.1
  have hSe : ∀ t ∈ ball (0 : ℂ) (2 * R), e.val.symm (γ t) = S (x, affineLinePoint t) :=
    fun t ht => e.val.left_inv (hmem x hxu t ht).2.1
  have hγball : ∀ t ∈ ball (0 : ℂ) (2 * R), γ t ∈ closedBall (e.val z₀) ρ :=
    fun t ht => ball_subset_closedBall (hmem x hxu t ht).2.2
  have hγK : ∀ t ∈ ball (0 : ℂ) (2 * R), S (x, affineLinePoint t) ∈ K :=
    fun t ht => ⟨γ t, hγball t ht, hSe t ht⟩
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
    (hγ x hxu s hs).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hUC : ∀ i, ContDiffOn ℝ 2 (fun s => f i (γ s)) (ball (0 : ℂ) (2 * R)) := by
    intro i s hs
    exact ((hfC i (γ s) (hγball s hs)).comp s ((hγ2 s hs).restrict_scalars ℝ)).contDiffWithinAt
  choose Vf hVf using fun i => exists_contDiff_two_eqOn_closedBall (c := (0 : ℂ)) hRpos
    (by linarith : R < 2 * R) (hUC i)
  have hdisc : ∀ t ∈ closedBall (0 : ℂ) (Real.exp (-(k : ℝ) / 2)), t ∈ ball (0 : ℂ) R := by
    intro t ht
    rw [mem_closedBall] at ht
    rw [mem_ball]
    linarith
  have hRR : ball (0 : ℂ) R ⊆ ball (0 : ℂ) (2 * R) := ball_subset_ball (by linarith)
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
    set z := S (x, affineLinePoint t) with hz
    rw [hσS t ht2, heq z, hreal z, (hΨK z hzK).1, ← EReal.coe_add, EReal.toReal_coe]
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
    have hvn : ‖v‖ ≤ Mv := hγbd x hxu t htn
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
      have hg : cutoffObstacle μ χ k (π (S (x, affineLinePoint t))) ≤ -k := by
        show cutoffObstacleLine χ k (μ (π (S (x, affineLinePoint t)))).2 ≤ -k
        rw [show μ (π (S (x, affineLinePoint t))) = (x, affineLinePoint t) from
          hgS _ (hmem x hxu t ht2).1]
        exact cutoffObstacleLine_affineLinePoint_le hχ k
          (exp_mul_norm_sq_le_one (by rw [mem_ball, dist_zero_right] at ht; exact ht.le))
      have hΨz : -C₁ ≤ (Ψ (π (S (x, affineLinePoint t)))).toReal := by
        rw [(hΨK _ hzK).1, EReal.toReal_coe]; exact (hΨK _ hzK).2
      have hexp : Real.exp (a * (cutoffObstacle μ χ k (π (S (x, affineLinePoint t))) -
          (Ψ (π (S (x, affineLinePoint t)))).toReal + k)) ≤ Real.exp (a * C₁) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith) ha)
      calc C₀ * Real.exp k * Real.exp (a * (cutoffObstacle μ χ k (π (S (x, affineLinePoint t))) -
            (Ψ (π (S (x, affineLinePoint t)))).toReal + k))
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
    show -max Cb (max C₂ C₃) ≤ Δ (Vf (i + J)) t ∧ Δ (Vf (i + J)) t ≤ max Cb (max C₂ C₃) * Real.exp k
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

end Disc

/-! ### The statement -/

/-- **`tok-wn-fl3:disc-laplacian`** (WN21 Lemma 7.5 along the discs near `X' \ ℰ`, with a
threshold `k₀`): `StrictDiscLaplacianFromStatement F` holds. -/
theorem strictDiscLaplacianFrom {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1)) :
    StrictDiscLaplacianFromStatement F := by
  intro E _ _ 𝒳 _ _ _ μ hμ Eℰ _ θ b c _ _ _ _ ι _ hιμ η' ε _ Ψ hΨ _ 𝒵 _ _ _ π hπ D' h hh
    h𝒵c h𝒵conn hexc hΨπ hKah χ hχ x₀ hx₀ hΨx₀
  exact exists_strictDisc_laplacian F hμ hΨ
    (HironakaChowLemma.isAnalyticModification_of_isBlowupSequence hπ) D' hexc hh hΨπ hKah hχ hιμ
    hx₀ hΨx₀

/-- **`tok-wn-fl:disc-laplacian`**: the `StrictDiscLaplacianStatement F` (corrected to the
threshold `k₀`; literally the same proposition as `StrictDiscLaplacianFromStatement F`) holds. -/
theorem strictDiscLaplacian {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1)) :
    StrictDiscLaplacianStatement F :=
  strictDiscLaplacianFrom F

end SGPT.Okounkov.TranscendentalWN
