import SGPT.Okounkov.TranscendentalWNConvFL3Resolution
import SGPT.Okounkov.TranscendentalWNConv7Final
import SGPT.Okounkov.TranscendentalWNConv6Obstacle
import SGPT.Okounkov.TranscendentalWNDeformation
import SGPT.Foundations.Analysis.Pending.HironakaLocalPrincipalization
import SGPT.Foundations.Analysis.Pending.ResidualNef

/-!
# WN21 Lemma 7.5 near `X' \ ℰ`: the two-sided bound `|v_k + k| ≤ C`

Blueprint `claude-tok-wn-fl3`, nodes `tok-wn-fl3:disc-statement-k0`, `tok-wn-fl3:disc-bound`;
source WN21 §7, Lemma 7.5, first assertion ("on `U_k` we have `|v_k + k| ≤ C`"), and the first
assertion of Corollary 7.6 (`references/wn21-restricted-volume`).

## The statement `StrictDiscLaplacianStatement F` needs a threshold `k₀`

`StrictDiscLaplacianStatement F` asks for one neighbourhood `U ∋ x₀` and one `C`
working for **all** `k ≥ 0`, on the discs `|t| ≤ e^{-k/2}`; at `k = 0` this is the closed unit
disc.  WN21 assumes `ψ` bounded on `U × {|τ| ≤ 1}`; under the sole hypothesis `Ψ(ι x₀) ≠ -∞` this
fails when `Ψ` has a pole on `σ_{x₀}({0 < |t| ≤ 1})` (counterexample in
`tok/WN-FL3/NEEDS.md`: `X = Bl_q ℙ²`, `ξ = H + aE_q`, `Ψ` with a pole along `μ⁻¹(E_q × {1/4})`,
`x₀ ∈ E_q`; `v_0 ≤ Ψ + C_0` is then `-∞` at `σ_{x₀}(1/4)`).  The same applies to
`StrictLipschitzStatement F`.  `StrictDiscLaplacianFromStatement F` below is the corrected
statement (`∃ k₀, ∀ k ≥ k₀`), which is all the consumers use (`k → ∞` along subsequences).

## Proved here

`exists_strictDisc_bound`: for `x₀ ∉ Z` with `Ψ(ι x₀) ≠ -∞` there are an open `U ∋ x₀`, `C` and
`k₀` with `v_k(z) ≠ -∞` and `|v_k(z) + k| ≤ C` for all `k ≥ k₀`, `x ∈ U` and **all** `z` over
`(x, t)` with `|t| ≤ e^{-k/2}` (in particular on the discs `σ_x` and at `z = ι x`).  Proof
(WN21): `v_k + k ≥ v_0 ≥ Ψ + c₀` (WN21 Proposition 7.2, `prescribedEnvelope_cutoffObstacle_sub_one_le`),
`Ψ ≥ -C₁` near `ι x₀` (log resolution: `Ψ ∘ π = ψ_{D'} + h` is bounded below on the compact
`π⁻¹(K)` for a compact neighbourhood `K` of `ι x₀` off `π(Supp D')`), the points over `(x, t)` stay
near `ι x₀` for `(x, t)` near `(x₀, 0)` (`μ` is a closed map and `ι x₀` is the only point over
`(x₀, 0)`), and `v_k ≤ g_k ≤ -k` where `e^k |t|² ≤ 1`.
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
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity
open Laplacian
open SGPT.Okounkov.TranscendentalMain
open SGPT.Okounkov.TranscendentalCore
open scoped SGPT.Foundations.Analysis.Pending.ProductComplexManifold

/-! ### The corrected statement -/

section Statement

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))

/-- **`tok-wn-fl3:disc-statement-k0`** (WN21 Lemma 7.5 along the discs `t ↦ μ⁻¹(x, t)` near
`X' \ ℰ`, **with a threshold `k₀`**): the statement `StrictDiscLaplacianStatement F` with
`∃ k₀, ∀ k ≥ k₀` in place of `∀ k` (the version for all `k ≥ 0` fails when `Ψ` has a pole on
`σ_{x₀}({0 < |t| ≤ 1})`, see the module docstring).  Statement only. -/
def StrictDiscLaplacianFromStatement : Prop :=
  ∀ E : MeteredEffectiveQDivisor (m + 1) F.carrier, IsFirstDivisorUnitMetric F E →
    (∀ x, E.weight x ≤ 0) →
    ∀ (𝒳 : Type u) [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
      [IsComplexManifold (m + 1 + 1) 𝒳] (μ : 𝒳 → F.carrier × ProjectiveLine)
      (hμ : IsNormalConeDeformation F μ) (Eℰ : MeteredEffectiveQDivisor (m + 1 + 1) 𝒳),
      IsDeformationExceptionalMetric F E hμ Eℰ →
      ∀ (θ : ClosedRealOneOneForm (m + 1) F.carrier) (b c : ℝ), 0 < c → c + 1 < b →
        IsBigMeetingFirstDivisor F (RealBottChern.ofRepresentative θ) →
        IsBigMeetingFirstDivisor F (RealBottChern.ofRepresentative θ -
          c • RealBottChern.ofRepresentative E.curvature) →
        ∀ (ι : F.carrier → 𝒳)
          (_ : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ ι),
          (∀ x, μ (ι x) = (x, projectiveZero)) →
          ∀ (η' : KahlerBackground (m + 1 + 1) 𝒳) (ε : ℝ), 0 < ε →
          ∀ Ψ : 𝒳 → EReal,
            IsThetaPshPotential (deformationForm F hμ.contMDiff θ b c Eℰ + ε • η'.form).val Ψ →
            SGPT.PSH.SingularityLE
              (thetaPshSupremum (deformationForm F hμ.contMDiff θ b c Eℰ).val) Ψ →
          ∀ (𝒵 : Type u) [TopologicalSpace 𝒵] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒵]
            [IsComplexManifold (m + 1 + 1) 𝒵] (π : 𝒵 → 𝒳)
            (hπ : IsBlowupSequence (m + 1 + 1) 𝒳 𝒵 π)
            (D' : MeteredEffectiveQDivisor (m + 1 + 1) 𝒵) (h : 𝒵 → ℝ)
            (hh : ChartSmooth (n := m + 1 + 1) h),
            CompactSpace 𝒵 → ConnectedSpace 𝒵 → exceptionalLocus (m + 1 + 1) π ⊆ D'.support →
            (∀ z, Ψ (π z) = D'.weight z + (h z : EReal)) →
            ((ClosedRealOneOneForm.pullback hπ.contMDiff
                (deformationForm F hμ.contMDiff θ b c Eℰ + ε • η'.form) - D'.curvature) +
              ddcClosedForm h hh).val.IsKahler →
          ∀ χ : ℝ → ℝ, IsWNCutoff χ →
          ∀ x₀ : F.carrier, x₀ ∉ F.flag (1 : Fin (m + 2)) → Ψ (ι x₀) ≠ ⊥ →
            ∃ U : Set F.carrier, IsOpen U ∧ x₀ ∈ U ∧ ∃ C : ℝ, ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ x ∈ U,
              ∀ σ : ℂ → 𝒳, (∀ t, μ (σ t) = (x, affineLinePoint t)) →
                (∀ t : ℂ, ‖t‖ ≤ Real.exp (-(k : ℝ) / 2) →
                  prescribedEnvelope (deformationForm F hμ.contMDiff θ b c Eℰ + ε • η'.form)
                      (cutoffObstacle μ χ k) Ψ (σ t) ≠ ⊥ ∧
                  |(prescribedEnvelope (deformationForm F hμ.contMDiff θ b c Eℰ + ε • η'.form)
                      (cutoffObstacle μ χ k) Ψ (σ t)).toReal + k| ≤ C) ∧
                ∃ u : ℕ → ℂ → ℝ, (∀ j, ContDiff ℝ 2 (u j)) ∧
                  TendstoUniformlyOn u
                    (fun t => (prescribedEnvelope
                      (deformationForm F hμ.contMDiff θ b c Eℰ + ε • η'.form)
                      (cutoffObstacle μ χ k) Ψ (σ t)).toReal) atTop
                    (Metric.closedBall 0 (Real.exp (-(k : ℝ) / 2))) ∧
                  ∀ j, ∀ t ∈ Metric.ball (0 : ℂ) (Real.exp (-(k : ℝ) / 2)),
                    -C ≤ Δ (u j) t ∧ Δ (u j) t ≤ C * Real.exp k

end Statement

/-! ### Elementary bounds of the envelopes `v_k` -/

section Bounds

variable {X : Type*} {N : ℕ} {𝒳 : Type*} [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel N) 𝒳]
  [IsComplexManifold N 𝒳] {μ : 𝒳 → X × ProjectiveLine} {χ : ℝ → ℝ}

/-- `v_k + k ≥ v_0` (WN21 Proposition 7.2, iterated). -/
theorem prescribedEnvelope_cutoffObstacle_zero_le (hχ : IsWNCutoff χ)
    (Θ : ClosedRealOneOneForm N 𝒳) (ψ : 𝒳 → EReal) (k : ℕ) (z : 𝒳) :
    prescribedEnvelope Θ (cutoffObstacle μ χ 0) ψ z + ((-(k : ℝ) : ℝ) : EReal) ≤
      prescribedEnvelope Θ (cutoffObstacle μ χ k) ψ z := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := prescribedEnvelope_cutoffObstacle_sub_one_le (μ := μ) hχ Θ ψ k z
    calc prescribedEnvelope Θ (cutoffObstacle μ χ 0) ψ z + ((-((k + 1 : ℕ) : ℝ) : ℝ) : EReal)
        = (prescribedEnvelope Θ (cutoffObstacle μ χ 0) ψ z + ((-(k : ℝ) : ℝ) : EReal)) +
            ((-1 : ℝ) : EReal) := by
          rw [add_assoc, ← EReal.coe_add]; congr 2; push_cast; ring
      _ ≤ prescribedEnvelope Θ (cutoffObstacle μ χ k) ψ z + ((-1 : ℝ) : EReal) :=
          add_le_add ih le_rfl
      _ ≤ _ := h

/-- `g_k ≤ -k` on `{e^k |τ|² ≤ 1}`. -/
theorem cutoffObstacleLine_affineLinePoint_le (hχ : IsWNCutoff χ) (k : ℕ) {t : ℂ}
    (ht : Real.exp k * ‖t‖ ^ 2 ≤ 1) : cutoffObstacleLine χ k (affineLinePoint t) ≤ -k := by
  rw [cutoffObstacleLine_affineLinePoint]
  have h1 : cutoffLog χ (Real.exp k * ‖t‖ ^ 2) ≤ 0 := by
    by_cases h0 : Real.exp k * ‖t‖ ^ 2 = 0
    · rw [h0, cutoffLog_zero]; norm_num
    · have hpos : 0 < Real.exp k * ‖t‖ ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h0)
      rw [cutoffLog_of_pos χ hpos]
      exact hχ.le_zero (Real.log_nonpos hpos.le ht)
  have h2 : 0 ≤ Real.log (1 + ‖t‖ ^ 2) := Real.log_nonneg (by nlinarith [sq_nonneg ‖t‖])
  linarith

/-- `‖t‖ ≤ e^{-k/2}` gives `e^k |t|² ≤ 1`. -/
theorem exp_mul_norm_sq_le_one {k : ℕ} {t : ℂ} (ht : ‖t‖ ≤ Real.exp (-(k : ℝ) / 2)) :
    Real.exp k * ‖t‖ ^ 2 ≤ 1 := by
  have h0 : 0 ≤ ‖t‖ := norm_nonneg t
  have hsq : ‖t‖ ^ 2 ≤ Real.exp (-(k : ℝ)) := by
    calc ‖t‖ ^ 2 ≤ Real.exp (-(k : ℝ) / 2) ^ 2 := pow_le_pow_left₀ h0 ht 2
      _ = Real.exp (-(k : ℝ)) := by rw [← Real.exp_nat_mul]; ring_nf
  calc Real.exp k * ‖t‖ ^ 2 ≤ Real.exp k * Real.exp (-(k : ℝ)) :=
        mul_le_mul_of_nonneg_left hsq (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

end Bounds

/-! ### The bound near `X' \ ℰ` -/

section Strict

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))
variable {𝒳 : Type u} [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
  [IsComplexManifold (m + 1 + 1) 𝒳] {μ : 𝒳 → F.carrier × ProjectiveLine}

/-- A lower bound of `Ψ` on a neighbourhood of a point `p` where `Ψ(p) ≠ -∞`, for `Ψ` with a log
resolution `Ψ ∘ π = ψ_{D'} + h`. -/
theorem exists_nhds_lowerBound_of_logResolution {N : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel N) M] [IsComplexManifold N M] {Ψ : M → EReal}
    {𝒵 : Type u} [TopologicalSpace 𝒵] [ChartedSpace (ComplexModel N) 𝒵] [IsComplexManifold N 𝒵]
    [CompactSpace 𝒵] {π : 𝒵 → M} (hπ : IsAnalyticModification (n := N) π)
    (D' : MeteredEffectiveQDivisor N 𝒵) {h : 𝒵 → ℝ} (hh : ChartSmooth (n := N) h)
    (hΨπ : ∀ z, Ψ (π z) = D'.weight z + (h z : EReal)) {p : M} (hp : Ψ p ≠ ⊥) :
    ∃ V : Set M, IsOpen V ∧ p ∈ V ∧ ∃ C : ℝ, ∀ y ∈ V, ((-C : ℝ) : EReal) ≤ Ψ y := by
  have hsurj := AnalyticModificationStrongPullback.surjective_of_isAnalyticModification hπ
  -- the image of the support is closed and misses `p`
  have hSc : IsClosed D'.support := (ResidualNef.isComplexAnalyticSubset_support D').isClosed
  have hW : IsOpen (π '' D'.support)ᶜ := (hπ.2.1.isClosedMap _ hSc).isOpen_compl
  have hpW : p ∈ (π '' D'.support)ᶜ := by
    rintro ⟨z, hz, rfl⟩
    apply hp
    have hbot : D'.weight z = ⊥ := hz
    rw [hΨπ z, hbot, EReal.bot_add]
  -- a compact neighbourhood of `p` off `π(Supp D')`, from a chart
  set e := complexChartAt (n := N) p with he
  have hpe : p ∈ e.val.source := mem_complexChartAt_source p
  have hO : IsOpen (e.val.target ∩ e.val.symm ⁻¹' (π '' D'.support)ᶜ) :=
    e.val.isOpen_inter_preimage_symm hW
  have hpO : e.val p ∈ e.val.target ∩ e.val.symm ⁻¹' (π '' D'.support)ᶜ :=
    ⟨e.val.map_source hpe, by rw [mem_preimage, e.val.left_inv hpe]; exact hpW⟩
  obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.mp hO _ hpO
  have hcb : Metric.closedBall (e.val p) (r / 2) ⊆
      e.val.target ∩ e.val.symm ⁻¹' (π '' D'.support)ᶜ :=
    (Metric.closedBall_subset_ball (by linarith)).trans hrO
  set K : Set M := e.val.symm '' Metric.closedBall (e.val p) (r / 2) with hK
  have hKc : IsCompact K := (isCompact_closedBall _ _).image_of_continuousOn
    (e.val.continuousOn_symm.mono fun y hy => (hcb hy).1)
  have hKW : K ⊆ (π '' D'.support)ᶜ := by
    rintro _ ⟨y, hy, rfl⟩
    exact (hcb hy).2
  set Λ := π ⁻¹' K with hΛ
  have hΛc : IsCompact Λ := hπ.2.1.isCompact_preimage hKc
  have hdisj : Disjoint Λ D'.support := by
    refine Set.disjoint_left.mpr fun z hzΛ hzS => hKW hzΛ ⟨z, hzS, rfl⟩
  obtain ⟨Cw, hCw⟩ :=
    MeteredDivisorWeightBounds.exists_bound_of_isCompact_disjoint_support D' hΛc hdisj
  obtain ⟨Bh, hBh⟩ := isCompact_univ.exists_bound_of_continuousOn
    (ProductTestForms.ChartSmooth.continuous hh).continuousOn
  refine ⟨e.val.source ∩ e.val ⁻¹' Metric.ball (e.val p) (r / 2),
    e.val.isOpen_inter_preimage Metric.isOpen_ball, ⟨hpe, Metric.mem_ball_self (by linarith)⟩,
    Cw + Bh, fun y hy => ?_⟩
  have hyK : y ∈ K := ⟨e.val y, Metric.ball_subset_closedBall hy.2, e.val.left_inv hy.1⟩
  obtain ⟨z, rfl⟩ := hsurj y
  have hzΛ : z ∈ Λ := hyK
  have hw := (hCw z hzΛ).1
  have hhz : -Bh ≤ h z := by
    have := hBh z (mem_univ z)
    rw [Real.norm_eq_abs] at this
    linarith [neg_abs_le (h z)]
  rw [hΨπ z]
  calc ((-(Cw + Bh) : ℝ) : EReal) = ((-Cw : ℝ) : EReal) + ((-Bh : ℝ) : EReal) := by
        rw [← EReal.coe_add]; ring_nf
    _ ≤ D'.weight z + (h z : EReal) := add_le_add hw (EReal.coe_le_coe_iff.mpr hhz)

/-- **WN21 Lemma 7.5, first assertion, near `X' \ ℰ`** (with a threshold `k₀`): for `x₀ ∉ Z` with
`Ψ(ι x₀) ≠ -∞` there are an open `U ∋ x₀`, `C` and `k₀` such that for all `k ≥ k₀`, `x ∈ U`,
`|t| ≤ e^{-k/2}` and every `z ∈ 𝒳` over `(x, t)`: `v_k(z) ≠ -∞` and `|v_k(z) + k| ≤ C`,
where `v_k = P_Θ[Ψ](g_k)`. -/
theorem exists_strictDisc_bound (hμ : IsNormalConeDeformation F μ)
    {Θ : ClosedRealOneOneForm (m + 1 + 1) 𝒳} {Ψ : 𝒳 → EReal} (hΨ : IsThetaPshPotential Θ.val Ψ)
    {𝒵 : Type u} [TopologicalSpace 𝒵] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒵]
    [IsComplexManifold (m + 1 + 1) 𝒵] [CompactSpace 𝒵] {π : 𝒵 → 𝒳}
    (hπ : IsAnalyticModification (n := m + 1 + 1) π) (D' : MeteredEffectiveQDivisor (m + 1 + 1) 𝒵)
    {h : 𝒵 → ℝ} (hh : ChartSmooth (n := m + 1 + 1) h)
    (hΨπ : ∀ z, Ψ (π z) = D'.weight z + (h z : EReal)) {χ : ℝ → ℝ} (hχ : IsWNCutoff χ)
    {ι : F.carrier → 𝒳} (hιμ : ∀ x, μ (ι x) = (x, projectiveZero))
    {x₀ : F.carrier} (hx₀ : x₀ ∉ F.flag (1 : Fin (m + 2))) (hΨx₀ : Ψ (ι x₀) ≠ ⊥) :
    ∃ U : Set F.carrier, IsOpen U ∧ x₀ ∈ U ∧ ∃ C : ℝ, ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ x ∈ U,
      ∀ t : ℂ, ‖t‖ ≤ Real.exp (-(k : ℝ) / 2) → ∀ z : 𝒳, μ z = (x, affineLinePoint t) →
        prescribedEnvelope Θ (cutoffObstacle μ χ k) Ψ z ≠ ⊥ ∧
        |(prescribedEnvelope Θ (cutoffObstacle μ χ k) Ψ z).toReal + k| ≤ C := by
  have : CompactSpace 𝒳 := compactSpace_normalCone F hμ
  have : Nonempty 𝒳 := ⟨ι x₀⟩
  have hμc : Continuous μ := hμ.continuous
  have hgc : ∀ k, Continuous (cutoffObstacle μ χ k) := fun k =>
    (continuous_cutoffObstacleLine hχ k).comp (continuous_snd.comp hμc)
  -- `Ψ ≥ -C₁` near `ι x₀`
  obtain ⟨V, hVo, hxV, C₁, hC₁⟩ := exists_nhds_lowerBound_of_logResolution hπ D' hh hΨπ hΨx₀
  -- the points over `(x, t)` near `(x₀, 0)` lie in `V`
  have hcl : IsClosed (μ '' Vᶜ) :=
    (HironakaLocalPrincipalization.isProperMap_of_isBlowupAlong hμ).isClosedMap _
      hVo.isClosed_compl
  have hx₀O : (x₀, affineLinePoint 0) ∈ (μ '' Vᶜ)ᶜ := by
    rintro ⟨z, hzV, hz⟩
    have hnot : μ (ι x₀) ∉ deformationCentre F := by
      rw [hιμ, mem_deformationCentre_iff]
      exact fun h => hx₀ h.1
    have hzι : ι x₀ = z :=
      eq_of_map_eq_of_notMem F hμ hnot (by rw [hz, hιμ, affineLinePoint_zero])
    exact hzV (hzι ▸ hxV)
  have hq : Continuous fun p : F.carrier × ℂ => (p.1, affineLinePoint p.2) :=
    continuous_fst.prodMk ((SGPT.Toric.projectiveLineHomeomorph.continuous.comp
      OnePoint.continuous_coe).comp continuous_snd)
  have hnhds : (fun p : F.carrier × ℂ => (p.1, affineLinePoint p.2)) ⁻¹' (μ '' Vᶜ)ᶜ ∈
      𝓝 ((x₀, 0) : F.carrier × ℂ) :=
    hq.continuousAt.preimage_mem_nhds (hcl.isOpen_compl.mem_nhds hx₀O)
  obtain ⟨u, hu, w, hw, huw⟩ := mem_nhds_prod_iff.mp hnhds
  obtain ⟨r, hr, hrw⟩ := Metric.mem_nhds_iff.mp hw
  -- the threshold
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → Real.exp (-(k : ℝ) / 2) < r := by
    have ht : Tendsto (fun k : ℕ => Real.exp (-(k : ℝ) / 2)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun k : ℕ => -(k : ℝ) / 2) atTop atBot :=
        (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop).atBot_div_const
          (by norm_num)
      exact Real.tendsto_exp_atBot.comp h1
    exact eventually_atTop.mp ((tendsto_order.mp ht).2 r hr)
  -- the constant `c₀` of the competitor `Ψ + c₀` of `v_0`
  obtain ⟨MΨ, hMΨ⟩ := hΨ.exists_global_upper_bound
  obtain ⟨y₀, -, hy₀⟩ := isCompact_univ.exists_isMinOn univ_nonempty (hgc 0).continuousOn
  set c₀ : ℝ := cutoffObstacle μ χ 0 y₀ - MΨ with hc₀
  have hmem : (fun x => Ψ x + (c₀ : EReal)) ∈ prescribedCompetitors Θ (cutoffObstacle μ χ 0) Ψ := by
    refine ⟨hΨ.add_const c₀, fun x => ?_,
      (SGPT.PSH.singularityLE_iff_exists_real _ _).mpr ⟨c₀, fun x => le_rfl⟩⟩
    calc Ψ x + (c₀ : EReal) ≤ (MΨ : EReal) + (c₀ : EReal) := add_le_add (hMΨ x) le_rfl
      _ = (cutoffObstacle μ χ 0 y₀ : EReal) := by rw [← EReal.coe_add, hc₀]; ring_nf
      _ ≤ (cutoffObstacle μ χ 0 x : EReal) := EReal.coe_le_coe_iff.mpr (hy₀ (mem_univ x))
  refine ⟨interior u, isOpen_interior, mem_interior_iff_mem_nhds.mpr hu, |C₁| + |c₀|, k₀,
    fun k hk x hx t ht z hz => ?_⟩
  -- `z ∈ V`
  have hzV : z ∈ V := by
    by_contra hzV
    have hxt : ((x, t) : F.carrier × ℂ) ∈ u ×ˢ w :=
      ⟨interior_subset hx, hrw (Metric.mem_ball.mpr (by
        rw [dist_zero_right]; exact lt_of_le_of_lt ht (hk₀ k hk)))⟩
    exact huw hxt ⟨z, hzV, hz⟩
  -- the lower bound
  have hlo : (((-C₁ + c₀ - k : ℝ)) : EReal) ≤ prescribedEnvelope Θ (cutoffObstacle μ χ k) Ψ z := by
    calc (((-C₁ + c₀ - k : ℝ)) : EReal) = (((-C₁ : ℝ) : EReal) + (c₀ : EReal)) +
          ((-(k : ℝ) : ℝ) : EReal) := by rw [← EReal.coe_add, ← EReal.coe_add]; ring_nf
      _ ≤ (Ψ z + (c₀ : EReal)) + ((-(k : ℝ) : ℝ) : EReal) :=
          add_le_add (add_le_add (hC₁ z hzV) le_rfl) le_rfl
      _ ≤ prescribedEnvelope Θ (cutoffObstacle μ χ 0) Ψ z + ((-(k : ℝ) : ℝ) : EReal) :=
          add_le_add (le_prescribedEnvelope hmem z) le_rfl
      _ ≤ _ := prescribedEnvelope_cutoffObstacle_zero_le hχ Θ Ψ k z
  -- the upper bound
  have hhi : prescribedEnvelope Θ (cutoffObstacle μ χ k) Ψ z ≤ (((-k : ℝ)) : EReal) := by
    refine (prescribedEnvelope_le (hgc k) z).trans (EReal.coe_le_coe_iff.mpr ?_)
    show cutoffObstacleLine χ k (μ z).2 ≤ -k
    rw [hz]
    exact cutoffObstacleLine_affineLinePoint_le hχ k (exp_mul_norm_sq_le_one ht)
  have hne_bot : prescribedEnvelope Θ (cutoffObstacle μ χ k) Ψ z ≠ ⊥ :=
    ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hlo
  have hne_top : prescribedEnvelope Θ (cutoffObstacle μ χ k) Ψ z ≠ ⊤ :=
    ne_top_of_le_ne_top (EReal.coe_ne_top _) hhi
  have hreal := (EReal.coe_toReal hne_top hne_bot).symm
  rw [hreal] at hlo hhi
  have h1 := EReal.coe_le_coe_iff.mp hlo
  have h2 := EReal.coe_le_coe_iff.mp hhi
  refine ⟨hne_bot, abs_le.mpr ⟨by linarith [neg_abs_le c₀, le_abs_self C₁], by
    linarith [abs_nonneg c₀, abs_nonneg C₁]⟩⟩

end Strict

end SGPT.Okounkov.TranscendentalWN
