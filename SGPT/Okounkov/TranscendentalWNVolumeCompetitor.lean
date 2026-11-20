import SGPT.Okounkov.TranscendentalWNVolumeLine
import SGPT.Okounkov.TranscendentalLiftingExtension
import SGPT.Siu.SiuLemma
import SGPT.Foundations.Analysis.Pending.GlobalDiagonalScaling
import SGPT.Foundations.Analysis.Pending.GlobalPotentialPullback
import SGPT.Foundations.Analysis.Pending.ResidualNef
import SGPT.Foundations.Analysis.Pending.ThetaPshIdentityPrinciple

/-!
# Competitors for the envelope `V_θ̃` on the deformation (package WN-VF)

Blueprint `claude-tok-wn-vf`, node `tok-wn-vf:competitor` (WN21 §4, proof of
Proposition 4.5, the inequality `v_t + λ log |τ|² ≤ u + C`, read directly on `𝒳`).

Let `μ : 𝒳 → X × ℙ¹` be the deformation to the normal cone of `Z`, `Eℰ` the metric of `𝒪(ℰ)`
with weight `log |s_ℰ|² = log W ∘ μ` (`IsDeformationExceptionalMetric`) and
`θ̃ = (π_X μ)^*θ + b (π_{ℙ¹} μ)^*ω_FS - c η_ℰ` (`deformationForm`).  For `φ ∈ PSH(X, θ)` and
`ℓ ∈ PSH(ℙ¹, ω_FS)` the function

  `w = φ ∘ π_X ∘ μ + b ℓ ∘ π_{ℙ¹} ∘ μ - c log |s_ℰ|²`   (`deformationCompetitor`)

is `θ̃`-psh off `ℰ` (`thetaPshOff_deformationCompetitor`: `-log |s_ℰ|²` is a local potential of
`η_ℰ` off `ℰ`).  If it is bounded above off `ℰ`, it extends across the analytic set `ℰ`
(`tok:ext-psh-extension`), and the extension is a competitor for `V_θ̃ = P_θ̃(0)`
(`le_thetaPshSupremum_of_thetaPshOff`).  Two instances are used:

* `φ = V_θ`, `ℓ = log N₀ = log (|τ|²/(1 + |τ|²))`: `w ≤ 0` since `W ≥ N₀` and `b ≥ c`
  (`deformationCompetitor_fibre_le_zero`); it gives the lower bound of `V_θ̃` on the fibres
  `X_τ`, `τ ≠ 0` (`tok-wn:formula-fibre`);
* `φ = V_{θ - cη} + c g`, `ℓ = log N₁ = -log (1 + |τ|²)`: `w ≤ 0` since `W ≥ e^g N₁` and `b ≥ c`
  (`deformationCompetitor_strict_le_zero`); on `X' ≅ X` (where `N₁ = 1` and
  `log |s_ℰ|² = g`) it equals `V_{θ - cη}` off `Z` (`tok-wn:formula-X-prime`).
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ThetaPshCodimTwoExtension
open SGPT.Foundations.Analysis.Pending.PshAnalyticSetExtension
open scoped SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open SGPT.Okounkov.TranscendentalMain

/-! ### Extension of a competitor across an analytic set -/

section Extension

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [ConnectedSpace M]

/-- **A competitor bounded by `0` off an analytic set lies below `V_θ`.**  If `w` is `θ`-psh off a
nowhere dense analytic set `A`, `w ≤ 0` off `A` and `w` is finite at a point off `A`, then
`w ≤ V_θ` off `A`: the extension of `w` across `A` (`tok:ext-psh-extension`) is a `θ`-psh
potential (identity principle) which is `≤ 0`. -/
theorem le_thetaPshSupremum_of_thetaPshOff (θ : ClosedRealOneOneForm n M) {A : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A) (hAi : interior A = ∅) {w : M → EReal}
    (hw : ThetaPshOff θ.val A w) (hle : ∀ z ∉ A, w z ≤ 0) (hne : ∃ z ∉ A, w z ≠ ⊥) :
    ∀ z ∉ A, w z ≤ thetaPshSupremum θ.val z := by
  have hbd : LocallyBoundedAboveOff A w := fun x =>
    ⟨univ, univ_mem, 0, fun y _ hy => by simpa using hle y hy⟩
  obtain ⟨hext, hoff, -⟩ := TranscendentalLifting.thetaPsh_extend_across_analytic θ hA hAi hw hbd
  have hle0 : extensionAcross A w ≤ 0 := by
    classical
    unfold extensionAcross
    refine uscRegularization_le (g := fun _ => (0 : EReal)) upperSemicontinuous_const ?_
    intro y
    by_cases hy : y ∈ A
    · simp [hy]
    · simp only [hy, if_false]
      exact hle y hy
  obtain ⟨z₀, hz₀A, hz₀⟩ := hne
  have hnd : LocallyNondegenerate (extensionAcross A w) :=
    ThetaPshIdentityPrinciple.locallyNondegenerate_of_exists_ne_bot hext
      ⟨z₀, by rw [hoff z₀ hz₀A]; exact hz₀⟩
  intro z hz
  rw [← hoff z hz]
  exact le_thetaPshSupremum ⟨hext, hnd⟩ hle0 z

end Extension

/-! ### The competitor -/

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))

section Deformation

variable {𝒳 : Type u} [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
  [IsComplexManifold (m + 1 + 1) 𝒳] {μ : 𝒳 → F.carrier × ProjectiveLine}

/-- The competitor `w = φ ∘ π_X ∘ μ + b ℓ ∘ π_{ℙ¹} ∘ μ - c log |s_ℰ|²` (off `ℰ`; on `ℰ` the
last term is replaced by `0`, which is irrelevant for the extension across `ℰ`). -/
def deformationCompetitor (μ : 𝒳 → F.carrier × ProjectiveLine) (φ : F.carrier → EReal)
    (ℓ : ProjectiveLine → EReal) (b c : ℝ) (Eℰ : MeteredEffectiveQDivisor (m + 1 + 1) 𝒳)
    (z : 𝒳) : EReal :=
  (φ (μ z).1 + (b : EReal) * ℓ (μ z).2) + ((-(c * (Eℰ.weight z).toReal) : ℝ) : EReal)

/-- **The competitor is `θ̃`-psh off `ℰ`**. -/
theorem thetaPshOff_deformationCompetitor (hμ : IsNormalConeDeformation F μ)
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {φ : F.carrier → EReal}
    (hφ : ThetaPlurisubharmonic θ.val φ) {ℓ : ProjectiveLine → EReal}
    (hℓ : ThetaPlurisubharmonic SGPT.Toric.projectiveNativeFSClosedForm.val ℓ) {b : ℝ}
    (hb : 0 < b) (c : ℝ) (Eℰ : MeteredEffectiveQDivisor (m + 1 + 1) 𝒳) :
    ThetaPshOff (deformationForm F hμ.contMDiff θ b c Eℰ).val Eℰ.support
      (deformationCompetitor F μ φ ℓ b c Eℰ) := by
  have h1 : ThetaPlurisubharmonic
      (ClosedRealOneOneForm.pullback (contMDiff_deformationProjX F hμ.contMDiff) θ).val
      (fun z => φ (μ z).1) :=
    GlobalPotentialPullback.thetaPlurisubharmonic_comp (contMDiff_deformationProjX F hμ.contMDiff)
      hφ
  have h2 : ThetaPlurisubharmonic
      (ClosedRealOneOneForm.pullback (contMDiff_deformationProjP1 F hμ.contMDiff)
        SGPT.Toric.projectiveNativeFSClosedForm).val (fun z => ℓ (μ z).2) :=
    GlobalPotentialPullback.thetaPlurisubharmonic_comp
      (contMDiff_deformationProjP1 F hμ.contMDiff) hℓ
  have h3 := GlobalDiagonalScaling.thetaPlurisubharmonic_add_smul one_pos hb h1 h2
  simp only [one_smul, EReal.coe_one, one_mul] at h3
  exact SGPT.Siu.thetaPshOff_sub_smul_weight h3 Eℰ c

/-- Off `ℰ` the weight of `𝒪(ℰ)` is the real number `log W ∘ μ`. -/
theorem weight_eq_coe_of_notMem {E : MeteredEffectiveQDivisor (m + 1) F.carrier}
    (hE : IsFirstDivisorUnitMetric F E) {hμ : IsNormalConeDeformation F μ}
    {Eℰ : MeteredEffectiveQDivisor (m + 1 + 1) 𝒳} (hEℰ : IsDeformationExceptionalMetric F E hμ Eℰ)
    {z : 𝒳} (hz : z ∉ exceptionalSet F μ) :
    0 < baseExceptionalWeight F E (μ z) ∧
      Eℰ.weight z = ((Real.log (baseExceptionalWeight F E (μ z)) : ℝ) : EReal) := by
  have hpos : 0 < baseExceptionalWeight F E (μ z) := baseExceptionalWeight_pos F hE hz
  exact ⟨hpos, by rw [hEℰ.weight_eq, ENNReal.log_ofReal_of_pos hpos]⟩

/-- **The competitor bound.**  Off `ℰ`, if `φ(x) + b ℓ(τ) ≤ c log W(x, τ)` then `w ≤ 0`. -/
theorem deformationCompetitor_le_zero {E : MeteredEffectiveQDivisor (m + 1) F.carrier}
    (hE : IsFirstDivisorUnitMetric F E) {hμ : IsNormalConeDeformation F μ}
    {Eℰ : MeteredEffectiveQDivisor (m + 1 + 1) 𝒳} (hEℰ : IsDeformationExceptionalMetric F E hμ Eℰ)
    {φ : F.carrier → EReal} {ℓ : ProjectiveLine → EReal} {b c : ℝ} {z : 𝒳}
    (hz : z ∉ exceptionalSet F μ)
    (hbound : φ (μ z).1 + (b : EReal) * ℓ (μ z).2 ≤
      ((c * Real.log (baseExceptionalWeight F E (μ z)) : ℝ) : EReal)) :
    deformationCompetitor F μ φ ℓ b c Eℰ z ≤ 0 := by
  obtain ⟨-, hw⟩ := weight_eq_coe_of_notMem F hE hEℰ hz
  unfold deformationCompetitor
  rw [hw, EReal.toReal_coe]
  calc φ (μ z).1 + (b : EReal) * ℓ (μ z).2 +
        ((-(c * Real.log (baseExceptionalWeight F E (μ z))) : ℝ) : EReal)
      ≤ ((c * Real.log (baseExceptionalWeight F E (μ z)) : ℝ) : EReal) +
          ((-(c * Real.log (baseExceptionalWeight F E (μ z))) : ℝ) : EReal) :=
        add_le_add_left hbound _
    _ = 0 := by rw [← EReal.coe_add, add_neg_cancel, EReal.coe_zero]

/-- `W ≥ N₀`. -/
theorem projectiveWeight_zero_le_baseExceptionalWeight
    (E : MeteredEffectiveQDivisor (m + 1) F.carrier) (q : F.carrier × ProjectiveLine) :
    projectiveWeight 0 q.2 ≤ baseExceptionalWeight F E q := by
  rw [baseExceptionalWeight_eq]
  have := mul_nonneg (ENNReal.toReal_nonneg (a := EReal.exp (E.weight q.1)))
    (projectiveWeight_nonneg 1 q.2)
  linarith

/-- `W ≥ e^g N₁`. -/
theorem exp_mul_projectiveWeight_one_le_baseExceptionalWeight
    (E : MeteredEffectiveQDivisor (m + 1) F.carrier) (q : F.carrier × ProjectiveLine) :
    (EReal.exp (E.weight q.1)).toReal * projectiveWeight 1 q.2 ≤ baseExceptionalWeight F E q := by
  rw [baseExceptionalWeight_eq]
  linarith [projectiveWeight_nonneg 0 q.2]

/-- **The fibre competitor is `≤ 0`**: `φ ≤ 0`, `ℓ = log N₀`, `0 ≤ c ≤ b`. -/
theorem deformationCompetitor_fibre_le_zero {E : MeteredEffectiveQDivisor (m + 1) F.carrier}
    (hE : IsFirstDivisorUnitMetric F E) {hμ : IsNormalConeDeformation F μ}
    {Eℰ : MeteredEffectiveQDivisor (m + 1 + 1) 𝒳} (hEℰ : IsDeformationExceptionalMetric F E hμ Eℰ)
    {φ : F.carrier → EReal} (hφ : ∀ x, φ x ≤ 0) {b c : ℝ} (hb : 0 < b) (hc : 0 ≤ c)
    (hcb : c ≤ b) {z : 𝒳} (hz : z ∉ exceptionalSet F μ) :
    deformationCompetitor F μ φ (projectiveLogWeight 0) b c Eℰ z ≤ 0 := by
  refine deformationCompetitor_le_zero F hE hEℰ hz ?_
  obtain ⟨hWpos, -⟩ := weight_eq_coe_of_notMem F hE hEℰ hz
  by_cases hp : (μ z).2 = projectiveZero
  · have hbot : projectiveLogWeight 0 (μ z).2 = ⊥ := by
      rw [hp, projectiveLogWeight, projectiveWeight_zero_projectiveZero, ENNReal.ofReal_zero,
        ENNReal.log_zero]
    rw [hbot, EReal.coe_mul_bot_of_pos hb, EReal.add_bot]
    exact bot_le
  · have hN0 := projectiveWeight_zero_pos hp
    rw [projectiveLogWeight_zero_eq_coe hp, ← EReal.coe_mul]
    have hlog0 : Real.log (projectiveWeight 0 (μ z).2) ≤ 0 :=
      Real.log_nonpos (projectiveWeight_nonneg 0 _) (projectiveWeight_le_one 0 _)
    have hlogW : Real.log (projectiveWeight 0 (μ z).2) ≤
        Real.log (baseExceptionalWeight F E (μ z)) :=
      Real.log_le_log hN0 (projectiveWeight_zero_le_baseExceptionalWeight F E (μ z))
    calc φ (μ z).1 + ((b * Real.log (projectiveWeight 0 (μ z).2) : ℝ) : EReal)
        ≤ 0 + ((b * Real.log (projectiveWeight 0 (μ z).2) : ℝ) : EReal) :=
          add_le_add (hφ _) le_rfl
      _ ≤ ((c * Real.log (baseExceptionalWeight F E (μ z)) : ℝ) : EReal) := by
          rw [zero_add, EReal.coe_le_coe_iff]
          nlinarith

end Deformation

end SGPT.Okounkov.TranscendentalWN
