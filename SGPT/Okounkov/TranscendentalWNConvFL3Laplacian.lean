import SGPT.Okounkov.TranscendentalWNConvFL3Berman
import SGPT.Okounkov.TranscendentalWNConvFL3Obstacle

/-!
# WN21 Lemma 7.5 on the log resolution, for the cutoff obstacles `g_k`

Blueprint `claude-tok-wn-fl3`, node `tok-wn-fl3:cutoff-laplacian`; source WN21 §7, proof of
Lemma 7.5 (first two displays): with `ṽ_k = P_{ω̃}(g_k ∘ π - ψ ∘ π)`,
`Δ_{ω̃} ṽ_k ≤ (C(n+1) + sup Δ_{ω̃}(g_k ∘ π)) e^{B(g_k ∘ π - ψ ∘ π - inf(g_k ∘ π - ψ ∘ π))}` and
`sup Δ_{ω̃}(g_k ∘ π) ≤ C e^k`.

`exists_lineBound_cutoffEnvelope`: there are `a ≥ 0` and `C ≥ 0`, independent of `k`, such that for
every `k`, `v_k ∘ π = ṽ_k + Ψ ∘ π` with `ṽ_k` real-valued and, on every compact `K ⊆ 𝒵 \ Supp D'`,
`ṽ_k` is a uniform limit of smooth `u_j` with `ω̃ + dd^c u_j` Kähler and
`ω̃ + dd^c u_j ≤ (C e^k e^{a(g_k ∘ π - Ψ ∘ π + k)} + ε) ω̃` on complex lines.  (On the discs of
`exists_strictDisc_bound`, `g_k ≤ -k` and `Ψ ≥ -C₁`, so the bound is `≤ C' e^k` there.)
Ingredients: `exists_lineBound_resolvedEnvelope` (Proposition 7.1 + Berman),
`exists_ddc_cutoffObstacleLine_comp_le` (`S_k = C e^k`), and `g_k ≥ -k - 1 - log 2`
(`neg_le_cutoffObstacleLine`, for the admissible `m_k = -k - 1 - log 2 - max Ψ`).
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy

/-- **`g_k ≥ -k - 1 - log 2`** on `ℙ¹`. -/
theorem neg_le_cutoffObstacleLine {χ : ℝ → ℝ} (hχ : IsWNCutoff χ) (k : ℕ) (p : ProjectiveLine) :
    -(k : ℝ) - 1 - Real.log 2 ≤ cutoffObstacleLine χ k p := by
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  by_cases hp : p = projectiveInfinity
  · rw [hp, cutoffObstacleLine_infinity]
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  · rw [eq_affineLinePoint_of_ne_infinity hp, cutoffObstacleLine_affineLinePoint]
    set τ := projectiveAffine p
    rcases le_or_gt ‖τ‖ 1 with hτ | hτ
    · have h1 := neg_one_le_cutoffLog hχ (Real.exp k * ‖τ‖ ^ 2)
      have h2 : Real.log (1 + ‖τ‖ ^ 2) ≤ Real.log 2 :=
        Real.log_le_log (by positivity) (by nlinarith [norm_nonneg τ])
      linarith
    · have hn : 0 < ‖τ‖ ^ 2 := by positivity
      have hr : 0 < Real.exp k * ‖τ‖ ^ 2 := by positivity
      have h1 : Real.log (Real.exp k * ‖τ‖ ^ 2) ≤ cutoffLog χ (Real.exp k * ‖τ‖ ^ 2) := by
        rw [cutoffLog_of_pos χ hr]; exact hχ.le_self _
      rw [Real.log_mul (Real.exp_pos _).ne' hn.ne', Real.log_exp] at h1
      have h2 : Real.log (1 + ‖τ‖ ^ 2) ≤ Real.log (‖τ‖ ^ 2) + Real.log 2 := by
        rw [← Real.log_mul hn.ne' (by norm_num)]
        exact Real.log_le_log (by positivity) (by nlinarith)
      linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

section Lemma

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

/-- A line-bounded smooth approximation stays one for a larger bound. -/
theorem HasSmoothLineBoundApproximationOn.mono_bound {A : KahlerBackground N Y} {K : Set Y}
    {w b b' : Y → ℝ} (h : TranscendentalWNReg.HasSmoothLineBoundApproximationOn A K w b)
    (hbb : ∀ x ∈ K, b x ≤ b' x) :
    TranscendentalWNReg.HasSmoothLineBoundApproximationOn A K w b' := by
  obtain ⟨uj, huj, hconv, hK, hbd⟩ := h
  refine ⟨uj, huj, hconv, hK, fun ε hε => (hbd ε hε).mono fun j hj e z hz hzK v => ?_⟩
  have hA : 0 ≤ A.form.val.coeff e z ![v, Complex.I • v] := A.isSemipositive e z hz v
  exact (hj e z hz hzK v).trans
    (mul_le_mul_of_nonneg_right (by linarith [hbb _ hzK]) hA)

end Lemma

section Resolution

variable {X : Type*} {N : ℕ} {𝒳 : Type u} [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel N) 𝒳]
  [IsComplexManifold N 𝒳] {𝒵 : Type u} [TopologicalSpace 𝒵] [ChartedSpace (ComplexModel N) 𝒵]
  [IsComplexManifold N 𝒵]

/-- **WN21 Lemma 7.5 on the log resolution, for the cutoff obstacles**: constants `a ≥ 0`, `C ≥ 0`
independent of `k` such that for all `k`, `ṽ_k = P_{ω̃}(g_k ∘ π - Ψ ∘ π)` is real-valued,
`v_k ∘ π = ṽ_k + Ψ ∘ π`, and on every compact `K ⊆ 𝒵 \ Supp D'` the function `ṽ_k` is a
line-bounded smooth limit with bound `C e^k e^{a(g_k ∘ π - Ψ ∘ π + k)}`. -/
theorem exists_lineBound_cutoffEnvelope [CompactSpace 𝒳] [CompactSpace 𝒵] [ConnectedSpace 𝒵]
    {μ : 𝒳 → X × ProjectiveLine}
    (hμ : ContMDiff 𝓘(ℂ, ComplexModel N) 𝓘(ℂ, ComplexModel 1) ∞ fun z => (μ z).2)
    {Θ : ClosedRealOneOneForm N 𝒳} {Ψ : 𝒳 → EReal} (hΨ : IsThetaPshPotential Θ.val Ψ)
    {π : 𝒵 → 𝒳} (hπ : IsAnalyticModification (n := N) π) (D' : MeteredEffectiveQDivisor N 𝒵)
    {h : 𝒵 → ℝ} (hh : ChartSmooth (n := N) h) (hΨπ : ∀ z, Ψ (π z) = D'.weight z + (h z : EReal))
    (hK : ((ClosedRealOneOneForm.pullback hπ.1 Θ - D'.curvature) + ddcClosedForm h hh).val.IsKahler)
    {χ : ℝ → ℝ} (hχ : IsWNCutoff χ) :
    ∃ a C : ℝ, 0 ≤ a ∧ 0 ≤ C ∧ ∀ k : ℕ,
      (∀ z, rooftopEnvelope ((ClosedRealOneOneForm.pullback hπ.1 Θ - D'.curvature) +
          ddcClosedForm h hh).val (fun y => (cutoffObstacle μ χ k (π y) : EReal) - Ψ (π y)) z =
        (((rooftopEnvelope ((ClosedRealOneOneForm.pullback hπ.1 Θ - D'.curvature) +
          ddcClosedForm h hh).val (fun y => (cutoffObstacle μ χ k (π y) : EReal) - Ψ (π y))
            z).toReal : ℝ) : EReal)) ∧
      (∀ z, prescribedEnvelope Θ (cutoffObstacle μ χ k) Ψ (π z) =
        rooftopEnvelope ((ClosedRealOneOneForm.pullback hπ.1 Θ - D'.curvature) +
          ddcClosedForm h hh).val (fun y => (cutoffObstacle μ χ k (π y) : EReal) - Ψ (π y)) z +
            Ψ (π z)) ∧
      ∀ K : Set 𝒵, IsCompact K → Disjoint K D'.support →
        TranscendentalWNReg.HasSmoothLineBoundApproximationOn
          ⟨(ClosedRealOneOneForm.pullback hπ.1 Θ - D'.curvature) + ddcClosedForm h hh, hK⟩ K
          (fun z => (rooftopEnvelope ((ClosedRealOneOneForm.pullback hπ.1 Θ - D'.curvature) +
            ddcClosedForm h hh).val (fun y => (cutoffObstacle μ χ k (π y) : EReal) - Ψ (π y))
              z).toReal)
          (fun z => C * Real.exp k *
            Real.exp (a * (cutoffObstacle μ χ k (π z) - (Ψ (π z)).toReal + k))) := by
  have : Nonempty 𝒵 := ConnectedSpace.toNonempty
  have : Nonempty 𝒳 := ⟨π (Classical.arbitrary 𝒵)⟩
  set ωt := (ClosedRealOneOneForm.pullback hπ.1 Θ - D'.curvature) + ddcClosedForm h hh with hωt
  obtain ⟨a, Λ, C₀, ha, hΛ, hC₀, hres⟩ := exists_lineBound_resolvedEnvelope hΨ hπ D' hh hΨπ hK
  have hq : ContMDiff 𝓘(ℂ, ComplexModel N) 𝓘(ℂ, ComplexModel 1) ∞ fun z => (μ (π z)).2 :=
    hμ.comp hπ.1
  obtain ⟨C₁, hC₁, hddc⟩ := exists_ddc_cutoffObstacleLine_comp_le ⟨ωt, hK⟩ hq hχ
  obtain ⟨MΨ, hMΨ⟩ := hΨ.exists_global_upper_bound
  set c₂ : ℝ := 1 + Real.log 2 + MΨ with hc₂
  refine ⟨a, (1 + C₁ + C₀) * Λ * Real.exp (a * c₂), ha, by positivity, fun k => ?_⟩
  have hek : 1 ≤ Real.exp k := Real.one_le_exp (Nat.cast_nonneg k)
  have hgc : Continuous (cutoffObstacle μ χ k) := continuous_cutoffObstacle hμ hχ k
  have hgπ : ChartSmooth (n := N) (fun z => cutoffObstacle μ χ k (π z)) :=
    ProductTestForms.chartSmooth_comp hq (chartSmooth_cutoffObstacleLine hχ k)
  set m : ℝ := -(k : ℝ) - c₂ with hm
  have hmle : ∀ y, (m : EReal) ≤ (cutoffObstacle μ χ k (π y) : EReal) - Ψ (π y) := by
    intro y
    by_cases hb : Ψ (π y) = ⊥
    · rw [hb, EReal.coe_sub_bot]; exact le_top
    · have hr := (EReal.coe_toReal (hΨ.1.quasiPlurisubharmonic.ne_top (π y)) hb).symm
      have hle : (Ψ (π y)).toReal ≤ MΨ := by
        have := hMΨ (π y); rw [hr] at this; exact EReal.coe_le_coe_iff.mp this
      rw [hr, ← EReal.coe_sub]
      refine EReal.coe_le_coe_iff.mpr ?_
      have := neg_le_cutoffObstacleLine hχ k (μ (π y)).2
      show m ≤ cutoffObstacleLine χ k (μ (π y)).2 - (Ψ (π y)).toReal
      rw [hm, hc₂]; linarith
  obtain ⟨hreal, heq, happrox⟩ := hres (cutoffObstacle μ χ k) hgc hgπ (C₁ * Real.exp k)
    (by positivity) (fun e z hz v => hddc k e z hz v) m hmle
  refine ⟨hreal, heq, fun K hKc hKd =>
    HasSmoothLineBoundApproximationOn.mono_bound (happrox K hKc hKd) fun z _ => ?_⟩
  -- the bound
  have hexp : Real.exp (a * (cutoffObstacle μ χ k (π z) - (Ψ (π z)).toReal - m)) =
      Real.exp (a * c₂) * Real.exp (a * (cutoffObstacle μ χ k (π z) - (Ψ (π z)).toReal + k)) := by
    rw [← Real.exp_add, hm]; ring_nf
  rw [hexp]
  have hE : 0 < Real.exp (a * (cutoffObstacle μ χ k (π z) - (Ψ (π z)).toReal + k)) :=
    Real.exp_pos _
  have hE2 : 0 < Real.exp (a * c₂) := Real.exp_pos _
  have h1 : 1 + C₁ * Real.exp k + C₀ ≤ (1 + C₁ + C₀) * Real.exp k := by nlinarith
  calc (1 + C₁ * Real.exp k + C₀) * Λ *
        (Real.exp (a * c₂) * Real.exp (a * (cutoffObstacle μ χ k (π z) - (Ψ (π z)).toReal + k)))
      ≤ ((1 + C₁ + C₀) * Real.exp k) * Λ *
        (Real.exp (a * c₂) * Real.exp (a * (cutoffObstacle μ χ k (π z) - (Ψ (π z)).toReal + k))) := by
        gcongr
    _ = (1 + C₁ + C₀) * Λ * Real.exp (a * c₂) * Real.exp k *
        Real.exp (a * (cutoffObstacle μ χ k (π z) - (Ψ (π z)).toReal + k)) := by ring

end Resolution

end SGPT.Okounkov.TranscendentalWN
