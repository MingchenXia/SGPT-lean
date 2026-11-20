import SGPT.TestCurve.TestConfigPhongSturm
import SGPT.Foundations.Analysis.FirstPass.SubgeodesicChord

/-!
# Left continuity of the obstacle of a filtration in the parameter `τ`

Infrastructure for input (a) of `rmk:PhongSturm` ([RWN14, Proposition 7.11]; footnote to
`ex:RWN`): `P_θ[ψ_τ] = ψ_τ` for the obstacle `ψ_τ = usc sup_k k⁻¹ Γ^{𝓕,k}_τ` of a filtration `𝓕`
of `R(X, L)`.

The Skoda step of [RWN14, Proposition 7.11] produces sections in `𝓕^{kτ'}_k` only for `τ' < τ`;
the passage from `τ' < τ` to `τ` is the left continuity of `τ ↦ ψ_τ` on `(-∞, τ(𝓕))`, which
follows from the concavity of the obstacle (`SectionFiltration.obstacle_concave`, proved in
`ex:RWN`) and the fact that two `θ`-psh functions that are ordered almost everywhere are ordered
everywhere.

## Main results

* `le_obstacle_of_forall_lt`: if `η ∈ PSH(X, θ)` and `η ≤ ψ_{τ'}` for all `τ' < τ`, where
  `τ < τ(𝓕)`, then `η ≤ ψ_τ`.
* `ereal_le_of_tendsto_coe`: the limit of a real sequence bounded by `b ∈ [-∞, ∞]` is bounded by
  `b`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.TestCurve.SkodaRWN

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Filter Set SGPT.Okounkov SGPT.LineBundle
open MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open scoped Topology

/-- If real numbers `g j → l` satisfy `g j ≤ b` eventually, `b ∈ [-∞, ∞]`, then `l ≤ b`. -/
theorem ereal_le_of_tendsto_coe {g : ℕ → ℝ} {l : ℝ} {b : EReal} (hg : Tendsto g atTop (𝓝 l))
    (h : ∀ᶠ j in atTop, ((g j : ℝ) : EReal) ≤ b) : ((l : ℝ) : EReal) ≤ b :=
  le_of_tendsto ((continuous_coe_real_ereal.tendsto l).comp hg) h

/-- The sequence `t_j = 1 / (2 (j + 1)) ∈ (0, 1)` tends to `0`. -/
theorem tendsto_half_inv_succ :
    Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1) / 2) atTop (𝓝 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const 2
  rwa [zero_div] at h

theorem half_inv_succ_pos (j : ℕ) : 0 < 1 / ((j : ℝ) + 1) / 2 := by positivity

theorem half_inv_succ_lt_one (j : ℕ) : 1 / ((j : ℝ) + 1) / 2 < 1 := by
  have h1 : 1 / ((j : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  linarith

variable {X : Scheme} {f : X ⟶ Spec (.of ℂ)} {n : ℕ} [SmoothOfRelativeDimension n f]
  {E : ClosedProjectiveEmbedding f}

local instance skodaContTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance skodaContCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance skodaContManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

variable {L : X.Modules} {a : LineBundleAtlas L} [IsIntegral X]
variable (F : SectionFiltration f a) (H : SchemeLineBundleMetric f n E L)

/-- **Left continuity of the obstacle** in `τ`, in the form used for [RWN14, Prop. 7.11]: for
`τ < τ(𝓕)`, a `θ`-psh function below `ψ_{τ'}` for every `τ' < τ` is below `ψ_τ`.

Proof: for `τ < τ₁ < τ(𝓕)` and `t ∈ (0, 1)`, concavity of the obstacle gives
`t ψ_{τ₁} + (1 - t) ψ_{τ'} ≤ ψ_τ` with `τ' = (τ - tτ₁)/(1 - t) < τ`; hence
`t ψ_{τ₁} + (1 - t) η ≤ ψ_τ`, and `t → 0` gives `η ≤ ψ_τ` wherever `ψ_{τ₁} > -∞`, i.e. almost
everywhere in every chart. -/
theorem le_obstacle_of_forall_lt {τ : ℝ} (hτ : (τ : EReal) < F.slope)
    {η : SchemeComplexPoint f → EReal}
    (hη : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val η)
    (h : ∀ τ' : ℝ, τ' < τ → η ≤ F.obstacle H τ') : η ≤ F.obstacle H τ := by
  let := E.isSeparated
  let := E.quasiCompact
  obtain ⟨τ₁, hτ₁, hτ₁s⟩ := EReal.lt_iff_exists_real_btwn.mp hτ
  have hττ₁ : τ < τ₁ := EReal.coe_lt_coe_iff.mp hτ₁
  have hψ₁ := F.obstacle_isThetaPshPotential H hτ₁s
  have hψ := F.obstacle_isThetaPshPotential H hτ
  refine RooftopEnvelopeAeObstacle.ThetaPlurisubharmonic.le_of_ae_in_charts_le hη.1 hψ.1
    fun e => ?_
  filter_upwards [hψ₁.quasiPshPotential.ae_finite_chart e] with z hz
  have h1top : F.obstacle H τ₁ (e.val.symm z) ≠ ⊤ := hz.1
  have h1bot : F.obstacle H τ₁ (e.val.symm z) ≠ ⊥ := hz.2
  generalize e.val.symm z = p at h1top h1bot ⊢
  have hη0 : η p ≤ 0 := (h (τ - 1) (by linarith) p).trans (F.obstacle_le_zero H _ p)
  rcases eq_bot_or_bot_lt (η p) with hb | hb
  · rw [hb]; exact bot_le
  have hηtop : η p ≠ ⊤ := fun ht => by
    rw [ht] at hη0
    exact absurd hη0 (by simp)
  obtain ⟨s₁, hs₁⟩ : ∃ s₁ : ℝ, F.obstacle H τ₁ p = (s₁ : EReal) :=
    ⟨(F.obstacle H τ₁ p).toReal, (EReal.coe_toReal h1top h1bot).symm⟩
  obtain ⟨r, hr⟩ : ∃ r : ℝ, η p = (r : EReal) :=
    ⟨(η p).toReal, (EReal.coe_toReal hηtop hb.ne').symm⟩
  have key : ∀ t : ℝ, 0 < t → t < 1 →
      ((t * s₁ + (1 - t) * r : ℝ) : EReal) ≤ F.obstacle H τ p := by
    intro t ht0 ht1
    have h1t : 0 < 1 - t := by linarith
    have hτ'lt : (τ - t * τ₁) / (1 - t) < τ := by
      rw [div_lt_iff₀ h1t]
      nlinarith
    have hτeq : t * τ₁ + (1 - t) * ((τ - t * τ₁) / (1 - t)) = τ := by
      field_simp
      ring
    have hc := F.obstacle_concave H (τ₀ := (τ - t * τ₁) / (1 - t)) (τ₁ := τ₁)
      (hτ'lt.trans hττ₁) hτ₁s ht0 ht1 p
    rw [hτeq, ThetaPshConvexCombination.convexComb_apply, hs₁] at hc
    refine le_trans ?_ hc
    have hηle := h _ hτ'lt p
    rw [hr] at hηle
    rw [EReal.coe_add, EReal.coe_mul, EReal.coe_mul]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hηle (EReal.coe_nonneg.mpr h1t.le))
  rw [hr]
  have hlim : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1) / 2 * s₁ +
      (1 - 1 / ((j : ℝ) + 1) / 2) * r) atTop (𝓝 r) := by
    have h1 := (tendsto_half_inv_succ.mul_const s₁).add
      ((tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_half_inv_succ |>.mul_const r)
    simpa using h1
  exact ereal_le_of_tendsto_coe hlim (Eventually.of_forall fun j =>
    key _ (half_inv_succ_pos j) (half_inv_succ_lt_one j))

end SGPT.TestCurve.SkodaRWN
