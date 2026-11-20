import SGPT.Okounkov.TranscendentalWNVolumeExcRestriction
import SGPT.Okounkov.TranscendentalWNVolumeFibre
import SGPT.Okounkov.TranscendentalWNDeformationStrict
import SGPT.Okounkov.TranscendentalWNDeformationBig
import SGPT.Okounkov.TranscendentalWNCone2
import SGPT.Foundations.Analysis.Pending.BigClassEnvelopeContact
import SGPT.Foundations.Analysis.Pending.ModificationMassInvariance

/-!
# The envelope `ũ` on the exceptional divisor (package WN-VF3)

Blueprint node `tok-wn-vf3:restriction` (chapter `claude-tok-wn-vf3`), the identity (4.2)
preparation of `tok-wn:formula-E`; source D. Witt Nyström, arXiv:2103.03660 (WN21), end of §4:

  `ũ = sup_{λ ∈ [0,c]} {ψ_λ ∘ π_Y + (c - λ) ln |z̃₁|²} + c g_ℰ`   on `ℰ \ A`.

## The Legendre input (WN21 Propositions 4.2, 4.5 and Legendre duality)

On `X × ℂ* = 𝒳 \ (X₀ ∪ X_∞)`, `ũ = V_θ̃ = u - b log(1 + |τ|²) - c log W` where `u` is the
circle-invariant envelope of `tok-wn-vf:punctured` and, by Legendre duality,
`u = sup_{λ ∈ [0,b]} (û_λ + λ log |τ|²)`.  Since `λ log N₀ + (b - λ) log N₁ = λ log |τ|² -
b log(1 + |τ|²)`, this reads

  `ũ = sup_{λ ∈ [0,b]} (û_λ ∘ π_X + λ log N₀ + (b - λ) log N₁ - c log W)`   off `X₀ ∪ X_∞`.

`IsExcLegendreFamily` records exactly what WN21 proves about `û`: each `û_λ` is `θ`-psh
(Kiselman), `λ ↦ û_λ` is concave, the duality above, and Proposition 4.5's bounds
`v_{c-λ} ≤ û_λ ≤ (c - λ)⁺ g + C` with `v_t = V_{θ - tη} + t g`.  These are the conclusions of
`tok-wn-vf:punctured` and `tok-wn-vf:legendre-bounds` (package WN-VF2);
`ExcLegendreInputStatement` asserts that such a family exists.  **Nothing here proves it.**

## The formula (`thetaPshSupremum_exceptional_eq_iSup`)

Let `S₁ = strictWeight` (`= N₀ / W` off `ℰ`, the weight of `𝒪(X')`) and
`S₂ = zStrictWeight` (`= e^g / W` off `ℰ`, the weight of `𝒪(Z̃)`), and
`w_λ` the extension across `Z` of `û_λ - (c - λ) g` (`excBranch`; it is
`(θ - (c - λ) η)`-psh, with minimal singularities: `V_{θ - (c-λ)η} ≤ w_λ ≤ C`).  Off
`X₀ ∪ X_∞ ∪ π_X⁻¹ Z`, for `λ ∈ [0, c]`,

  `û_λ + λ log N₀ + (b - λ) log N₁ - c log W = w_λ ∘ π_X + (c - λ) log S₂ + λ log S₁ + (b - λ) log N₁`,

and the right side is quasi-psh near every point of `ℰ` where `S₁, S₂ > 0` (off the strict
transforms `X'` and `Z̃`).  For `p ∈ ℰ` with `S₁(p), S₂(p) > 0` and `π_X(p) ∉ E_nK(ξ_t)` for
`t ∈ [0, c]`, the abstract restriction lemma `eq_iSup_of_eq_iSup_off` gives

  `ũ(p) = sup_{λ ∈ [0, c]} (w_λ(π_X p) + (c - λ) log S₂(p) + λ log S₁(p))`.

In WN21's coordinates `(z̃₁, z', τ)`, `z₁ = z̃₁ τ`, `log S₂ - log S₁ = log |z̃₁|² - g_Z` on `ℰ`
and `log S₁ = -log(1 + |z̃₁|² e^{-g_Z}) = g_ℰ`, so this is WN21's identity (4.2) with
`ψ_λ = (w_λ - (c - λ) g_Z)|_Z`, written without coordinates.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ThetaPshCodimTwoExtension
open SGPT.Foundations.Analysis.Pending.PshAnalyticSetExtension
open scoped SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open SGPT.Okounkov.TranscendentalMain

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))

/-! ### The Legendre input -/

section Input

variable {𝒳 : Type u} [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
  [IsComplexManifold (m + 1 + 1) 𝒳]

/-- The real correction `λ log N₀ + (b - λ) log N₁ - c log W` at `q = (x, τ)`; for `τ ≠ 0, ∞` it is
`λ log |τ|² - b log(1 + |τ|²) - c log W`. -/
def excCorrection (E : MeteredEffectiveQDivisor (m + 1) F.carrier) (b c lam : ℝ)
    (q : F.carrier × ProjectiveLine) : ℝ :=
  lam * Real.log (projectiveWeight 0 q.2) + (b - lam) * Real.log (projectiveWeight 1 q.2) -
    c * Real.log (baseExceptionalWeight F E q)

/-- **The Legendre input of `tok-wn:formula-E`** (WN21 Proposition 4.2, Definition 4.3,
Proposition 4.5 and Legendre duality): a family `û_λ` (the partial Legendre transform of the
envelope `u` on `X × ℂ*`) of `θ`-psh functions, concave in `λ ∈ [0, b]`, with
`ũ = sup_{λ ∈ [0,b]} (û_λ ∘ π_X + λ log N₀ + (b - λ) log N₁ - c log W)` on `X × ℂ*` and
`V_{θ - (c-λ)η} + (c - λ) g ≤ û_λ ≤ (c - λ)⁺ g + C` off `Z`. -/
structure IsExcLegendreFamily (E : MeteredEffectiveQDivisor (m + 1) F.carrier)
    {μ : 𝒳 → F.carrier × ProjectiveLine} (hμ : IsNormalConeDeformation F μ)
    (Eℰ : MeteredEffectiveQDivisor (m + 1 + 1) 𝒳) (θ : ClosedRealOneOneForm (m + 1) F.carrier)
    (b c : ℝ) (û : ℝ → F.carrier → EReal) : Prop where
  psh : ∀ lam ∈ Icc 0 b, ThetaPlurisubharmonic θ.val (û lam)
  concave : ∀ x, IsConcaveFamilyAt û (Icc 0 b) x
  duality : ∀ z : 𝒳, (μ z).2 ≠ projectiveZero → (μ z).2 ≠ projectiveInfinity →
    thetaPshSupremum (deformationForm F hμ.contMDiff θ b c Eℰ).val z =
      ⨆ lam ∈ Icc 0 b, û lam (μ z).1 + (excCorrection F E b c lam (μ z) : EReal)
  upper : ∃ C : ℝ, ∀ lam ∈ Icc 0 b, ∀ x, x ∉ F.flag (1 : Fin (m + 2)) →
    û lam x ≤ ((max (c - lam) 0 * (E.weight x).toReal + C : ℝ) : EReal)
  lower : ∀ lam ∈ Icc 0 c, ∀ x, x ∉ F.flag (1 : Fin (m + 2)) →
    thetaPshSupremum (θ - (c - lam) • E.curvature).val x +
      (((c - lam) * (E.weight x).toReal : ℝ) : EReal) ≤ û lam x

end Input

/-- **The Legendre input exists** (WN21 Propositions 4.2, 4.5 and duality; to be supplied by
`tok-wn-vf:punctured` and `tok-wn-vf:legendre-bounds`, package WN-VF2): for the data of
`ExceptionalRestrictedVolumeStatement`, a family as in `IsExcLegendreFamily` exists. -/
def ExcLegendreInputStatement : Prop :=
  ∀ E : MeteredEffectiveQDivisor (m + 1) F.carrier, IsFirstDivisorUnitMetric F E →
    (∀ x, E.weight x ≤ 0) →
    ∀ (𝒳 : Type u) [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
      [IsComplexManifold (m + 1 + 1) 𝒳] (μ : 𝒳 → F.carrier × ProjectiveLine)
      (hμ : IsNormalConeDeformation F μ) (Eℰ : MeteredEffectiveQDivisor (m + 1 + 1) 𝒳),
      IsDeformationExceptionalMetric F E hμ Eℰ →
      ∀ (θ : ClosedRealOneOneForm (m + 1) F.carrier) (b c : ℝ), 0 < c → c < b →
        IsBigMeetingFirstDivisor F (RealBottChern.ofRepresentative θ) →
        IsBigMeetingFirstDivisor F (RealBottChern.ofRepresentative θ -
          c • RealBottChern.ofRepresentative E.curvature) →
          ∃ û : ℝ → F.carrier → EReal, IsExcLegendreFamily F E hμ Eℰ θ b c û

/-! ### The branches `w_λ` on `X` -/

section Branch

/-- `û_λ - (c - λ) g` (with the junk value `-∞` on `Z`). -/
def excBranchOff (E : MeteredEffectiveQDivisor (m + 1) F.carrier) (û : ℝ → F.carrier → EReal)
    (c lam : ℝ) (x : F.carrier) : EReal :=
  û lam x + ((-((c - lam) * (E.weight x).toReal) : ℝ) : EReal)

/-- **The branch `w_λ`**: the extension across `Z` of `û_λ - (c - λ) g`. -/
def excBranch (E : MeteredEffectiveQDivisor (m + 1) F.carrier) (û : ℝ → F.carrier → EReal)
    (c lam : ℝ) : F.carrier → EReal :=
  extensionAcross E.support (excBranchOff F E û c lam)

variable {F}

/-- `w_λ` is `(θ - (c - λ) η)`-psh, equals `û_λ - (c - λ) g` off `Z`, and is bounded above. -/
theorem excBranch_spec {E : MeteredEffectiveQDivisor (m + 1) F.carrier}
    (hE : IsFirstDivisorUnitMetric F E) {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {û : ℝ → F.carrier → EReal} {c lam : ℝ} (hψ : ThetaPlurisubharmonic θ.val (û lam))
    {C : ℝ} (hC : ∀ x, x ∉ E.support → excBranchOff F E û c lam x ≤ (C : EReal)) :
    ThetaPlurisubharmonic (θ - (c - lam) • E.curvature).val (excBranch F E û c lam) ∧
      (∀ x, x ∉ E.support → excBranch F E û c lam x = excBranchOff F E û c lam x) ∧
      ∀ x, excBranch F E û c lam x ≤ (C : EReal) := by
  obtain ⟨D, -, hsupp, -⟩ := hE
  have hA : IsComplexAnalyticSubset (n := m + 1) E.support :=
    ResidualNef.isComplexAnalyticSubset_support E
  have hAi : interior E.support = ∅ := by rw [hsupp]; exact interior_firstFlag F
  have hoff : ThetaPshOff (θ - (c - lam) • E.curvature).val E.support
      (excBranchOff F E û c lam) := SGPT.Siu.thetaPshOff_sub_smul_weight hψ E (c - lam)
  have hbd : LocallyBoundedAboveOff E.support (excBranchOff F E û c lam) := fun x =>
    ⟨univ, univ_mem, C, fun y _ hy => hC y hy⟩
  obtain ⟨hext, heq, -⟩ := TranscendentalLifting.thetaPsh_extend_across_analytic _ hA hAi hoff hbd
  refine ⟨hext, heq, fun x => ?_⟩
  classical
  unfold excBranch extensionAcross
  refine uscRegularization_le (g := fun _ => (C : EReal)) upperSemicontinuous_const ?_ x
  intro y
  by_cases hy : y ∈ E.support
  · simp [hy]
  · simp only [hy, if_false]
    exact hC y hy

end Branch

/-! ### Elementary facts on `ℙ¹` and on the weights -/

section Weights

theorem projectiveWeight_one_projectiveInfinity : projectiveWeight 1 projectiveInfinity = 0 := by
  have h : projectiveInfinity = Projectivization.mk ℂ ![1, 0] (by simp) := rfl
  rw [h, projectiveWeight_mk]
  simp

/-- `|s_Z|²_h = e^g` off `Z`. -/
theorem exp_weight_toReal_eq_exp {E : MeteredEffectiveQDivisor (m + 1) F.carrier}
    (hE : IsFirstDivisorUnitMetric F E) {x : F.carrier} (hx : x ∉ F.flag (1 : Fin (m + 2))) :
    (EReal.exp (E.weight x)).toReal = Real.exp (E.weight x).toReal := by
  obtain ⟨D, -, hsupp, -⟩ := id hE
  have hbot : E.weight x ≠ ⊥ := fun h => hx (by rw [← hsupp]; exact h)
  have htop : E.weight x ≠ ⊤ := weight_ne_top F hE x
  rw [← EReal.coe_toReal htop hbot, EReal.exp_coe, ENNReal.toReal_ofReal (Real.exp_pos _).le,
    EReal.toReal_coe]

end Weights

/-! ### The formula on `ℰ` -/

section Formula

variable {𝒳 : Type u} [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
  [IsComplexManifold (m + 1 + 1) 𝒳] {μ : 𝒳 → F.carrier × ProjectiveLine}

/-- The branch `w_λ` has minimal singularities in `ξ_{c-λ}` from below:
`V_{θ - (c - λ) η} ≤ w_λ` on `X` (WN21 Proposition 4.5, lower bound `v_t ≤ û_λ`, extended
across `Z`). -/
theorem thetaPshSupremum_le_excBranch {E : MeteredEffectiveQDivisor (m + 1) F.carrier}
    (hE : IsFirstDivisorUnitMetric F E) {hμ : IsNormalConeDeformation F μ}
    {Eℰ : MeteredEffectiveQDivisor (m + 1 + 1) 𝒳} {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {b c : ℝ} {û : ℝ → F.carrier → EReal} (hû : IsExcLegendreFamily F E hμ Eℰ θ b c û)
    (hcb : c ≤ b) {lam : ℝ} (hl : lam ∈ Icc 0 c)
    (hV : ThetaPlurisubharmonic (θ - (c - lam) • E.curvature).val
      (thetaPshSupremum (θ - (c - lam) • E.curvature).val)) (x : F.carrier) :
    thetaPshSupremum (θ - (c - lam) • E.curvature).val x ≤ excBranch F E û c lam x := by
  obtain ⟨C₀, hC₀⟩ := hû.upper
  obtain ⟨D, -, hsupp, -⟩ := id hE
  have hlb : lam ∈ Icc 0 b := ⟨hl.1, hl.2.trans hcb⟩
  have hup : ∀ y, y ∉ E.support → excBranchOff F E û c lam y ≤ (C₀ : EReal) := by
    intro y hy
    have hyZ : y ∉ F.flag (1 : Fin (m + 2)) := by rw [← hsupp]; exact hy
    have h1 := hC₀ lam hlb y hyZ
    rw [max_eq_left (by linarith [hl.2])] at h1
    have h2 := add_le_add h1 (le_refl (((-((c - lam) * (E.weight y).toReal)) : ℝ) : EReal))
    rw [← EReal.coe_add] at h2
    unfold excBranchOff
    refine h2.trans (le_of_eq ?_)
    congr 1; ring
  obtain ⟨hpsh, heq, -⟩ := excBranch_spec hE (hû.psh lam hlb) hup
  have hA : IsComplexAnalyticSubset (n := m + 1) E.support :=
    ResidualNef.isComplexAnalyticSubset_support E
  have hAi : interior E.support = ∅ := by rw [hsupp]; exact interior_firstFlag F
  refine le_of_le_off_analytic hA hAi hpsh hV (fun y hy => ?_) x
  have hyZ : y ∉ F.flag (1 : Fin (m + 2)) := by rw [← hsupp]; exact hy
  rw [heq y hy]
  have h := add_le_add (hû.lower lam hl y hyZ)
    (le_refl (((-((c - lam) * (E.weight y).toReal)) : ℝ) : EReal))
  rwa [MeteredDivisorPositivity.add_coe_add_neg_coe] at h

/-- **`ũ` on the exceptional divisor** (WN21 §4, identity (4.2), without coordinates).  Given
the Legendre input `IsExcLegendreFamily`, at every point `p ∈ ℰ` off the strict transforms
`X'` (`S₁ = 0`) and `Z̃` (`S₂ = 0`) with `π_X(p) ∉ E_nK(ξ_t)` for `t ∈ [0, c]`,

  `ũ(p) = sup_{λ ∈ [0, c]} (w_λ(π_X p) + (c - λ) log S₂(p) + λ log S₁(p))`,

`w_λ` the extension across `Z` of `û_λ - (c - λ) g` (`excBranch`). -/
theorem thetaPshSupremum_exceptional_eq_iSup {E : MeteredEffectiveQDivisor (m + 1) F.carrier}
    (hE : IsFirstDivisorUnitMetric F E) (hμ : IsNormalConeDeformation F μ)
    {Eℰ : MeteredEffectiveQDivisor (m + 1 + 1) 𝒳} (hEℰ : IsDeformationExceptionalMetric F E hμ Eℰ)
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {b c : ℝ} (hc : 0 < c) (hcb : c < b)
    (hξ : IsBigMeetingFirstDivisor F (RealBottChern.ofRepresentative θ))
    (hξc : IsBigMeetingFirstDivisor F (RealBottChern.ofRepresentative θ -
      c • RealBottChern.ofRepresentative E.curvature))
    {û : ℝ → F.carrier → EReal} (hû : IsExcLegendreFamily F E hμ Eℰ θ b c û)
    {p : 𝒳} (hp : p ∈ exceptionalSet F μ) (hS₁ : 0 < strictWeight F E μ p)
    (hS₂ : 0 < zStrictWeight F E μ p)
    (hK : ∀ t ∈ Icc 0 c, (μ p).1 ∉ nonKahlerLocus (RealBottChern.ofRepresentative θ -
      t • RealBottChern.ofRepresentative E.curvature)) :
    thetaPshSupremum (deformationForm F hμ.contMDiff θ b c Eℰ).val p =
      ⨆ lam ∈ Icc 0 c, excBranch F E û c lam (μ p).1 +
        (((c - lam) * Real.log (zStrictWeight F E μ p) +
          lam * Real.log (strictWeight F E μ p) : ℝ) : EReal) := by
  have := compactSpace_normalCone F hμ
  have : Nonempty 𝒳 := ⟨p⟩
  set Θ := deformationForm F hμ.contMDiff θ b c Eℰ with hΘ
  obtain ⟨D, -, hsupp, -⟩ := id hE
  -- `ũ` is `θ̃`-psh
  obtain ⟨hβbig, -, -, -⟩ := betaBig F E hE 𝒳 μ hμ Eℰ hEℰ.isDivisorMetric θ b c hc hcb hξ hξc.1
  have hU : ThetaPlurisubharmonic Θ.val (thetaPshSupremum Θ.val) :=
    (MinimalSingularityLelongVanishing.isThetaPshPotential_thetaPshSupremum Θ
      ((SGPT.PSH.BookCurrent.isBig_iff_isBigClass _).mp hβbig)).1
  -- `ℰ` is locally pluripolar
  have hA : ManifoldLocallyPluripolar (n := m + 1 + 1) (exceptionalSet F μ) := by
    have h1 := ResidualNef.isComplexAnalyticSubset_support Eℰ
    rw [hEℰ.support_eq] at h1
    exact ModificationMassInvariance.manifoldLocallyPluripolar_of_isComplexAnalyticSubset h1
      (interior_exceptionalSet F hμ)
  -- the weights and the neighbourhood `N`
  set S₁ := strictWeight F E μ with hS₁def
  set S₂ := zStrictWeight F E μ with hS₂def
  set N₀ : 𝒳 → ℝ := fun z => projectiveWeight 0 (μ z).2 with hN₀def
  set N₁ : 𝒳 → ℝ := fun z => projectiveWeight 1 (μ z).2 with hN₁def
  have hS₁c : Continuous S₁ :=
    continuous_iff_continuousAt.mpr (WeightFactorization.continuousAt (strictFactorization F hμ hE))
  have hS₂c : Continuous S₂ :=
    continuous_iff_continuousAt.mpr (WeightFactorization.continuousAt (zStrictFactorization F hμ hE))
  have hN₀c : Continuous N₀ := chartSmooth_continuous (chartSmooth_projectiveWeight_comp hμ 0)
  have hN₁c : Continuous N₁ := chartSmooth_continuous (chartSmooth_projectiveWeight_comp hμ 1)
  set N : Set 𝒳 := {z | 0 < S₁ z} ∩ {z | 0 < S₂ z} ∩ {z | 0 < N₁ z} with hNdef
  have hNo : IsOpen N :=
    ((isOpen_lt continuous_const hS₁c).inter (isOpen_lt continuous_const hS₂c)).inter
      (isOpen_lt continuous_const hN₁c)
  have hp0 : (μ p).2 = projectiveZero := ((mem_deformationCentre_iff F).mp hp).2
  have hN₁p : N₁ p = 1 := by
    simp only [hN₁def, hp0, projectiveWeight_one_projectiveZero]
  have hpN : p ∈ N := ⟨⟨hS₁, hS₂⟩, by rw [mem_ofPred_eq, hN₁p]; exact one_pos⟩
  -- facts at points of `N \ ℰ`
  have hoff : ∀ y ∈ N, y ∉ exceptionalSet F μ →
      (μ y).2 ≠ projectiveZero ∧ (μ y).2 ≠ projectiveInfinity ∧
        (μ y).1 ∉ F.flag (1 : Fin (m + 2)) := by
    intro y hy hyA
    refine ⟨fun h0 => ?_, fun hinf => ?_, fun hZ => ?_⟩
    · have := hy.1.1
      rw [mem_ofPred_eq, hS₁def, strictWeight_eq_of_notMem F hμ hE hyA, h0,
        projectiveWeight_zero_projectiveZero, zero_div] at this
      exact lt_irrefl _ this
    · have := hy.2
      rw [mem_ofPred_eq, hN₁def] at this
      simp only [hinf, projectiveWeight_one_projectiveInfinity] at this
      exact lt_irrefl _ this
    · have := hy.1.2
      rw [mem_ofPred_eq, hS₂def, zStrictWeight_eq_of_notMem F hμ hE hyA,
        exp_weight_toReal_eq_zero F hE hZ, zero_div] at this
      exact lt_irrefl _ this
  -- the families
  set Φ : ℝ → 𝒳 → EReal := fun lam z =>
    û lam (μ z).1 + (excCorrection F E b c lam (μ z) : EReal) with hΦdef
  set Ψ : ℝ → 𝒳 → EReal := fun lam z =>
    excBranch F E û c lam (μ z).1 + (((c - lam) * Real.log (S₂ z) + lam * Real.log (S₁ z) +
      (b - lam) * Real.log (N₁ z) : ℝ) : EReal) with hΨdef
  obtain ⟨C₀, hC₀⟩ := hû.upper
  -- the branches `w_λ`, `λ ∈ [0, c]`
  have hbranch : ∀ lam ∈ Icc 0 c,
      ThetaPlurisubharmonic (θ - (c - lam) • E.curvature).val (excBranch F E û c lam) ∧
        (∀ x, x ∉ E.support → excBranch F E û c lam x = excBranchOff F E û c lam x) ∧
        ∀ x, excBranch F E û c lam x ≤ (C₀ : EReal) := by
    intro lam hl
    have hlb : lam ∈ Icc 0 b := ⟨hl.1, hl.2.trans hcb.le⟩
    refine excBranch_spec hE (hû.psh lam hlb) fun y hy => ?_
    have hyZ : y ∉ F.flag (1 : Fin (m + 2)) := by rw [← hsupp]; exact hy
    have h1 := hC₀ lam hlb y hyZ
    rw [max_eq_left (by linarith [hl.2])] at h1
    have h2 := add_le_add h1 (le_refl (((-((c - lam) * (E.weight y).toReal)) : ℝ) : EReal))
    rw [← EReal.coe_add] at h2
    unfold excBranchOff
    refine h2.trans (le_of_eq ?_)
    congr 1; ring
  have key := eq_iSup_of_eq_iSup_off hU hA hNo hpN hp hc hcb.le (Φ := Φ) (Ψ := Ψ)
    (fun y hy hyA => hû.duality y (hoff y hy hyA).1 (hoff y hy hyA).2.1)
    (fun y hy hyA => by
      set q := μ y
      set K₁ := Real.log (projectiveWeight 0 q.2) - Real.log (projectiveWeight 1 q.2)
      set K₀ := b * Real.log (projectiveWeight 1 q.2) - c * Real.log (baseExceptionalWeight F E q)
      have hΦeq : ∀ lam, Φ lam y = (û lam q.1 + ((lam * K₁ : ℝ) : EReal)) + (K₀ : EReal) := by
        intro lam
        simp only [hΦdef, excCorrection]
        rw [add_assoc, ← EReal.coe_add]
        congr 2
        simp only [K₁, K₀, q]
        ring
      have h := ((hû.concave q.1).add_affine K₁).add_const K₀
      intro l₁ hl₁ l₂ hl₂ t ht0 ht1
      rw [hΦeq, hΦeq, hΦeq]
      exact h l₁ hl₁ l₂ hl₂ t ht0 ht1)
    (fun y _ _ lam hl => EReal.add_ne_top
      ((hû.psh lam hl).quasiPlurisubharmonic.ne_top _) (EReal.coe_ne_top _))
    (fun lam hl y hy hyA => by
      obtain ⟨-, -, hZ⟩ := hoff y hy hyA
      have hyE : (μ y).1 ∉ E.support := by rw [hsupp]; exact hZ
      have hW := baseExceptionalWeight_pos F hE hyA
      have hN0 := projectiveWeight_zero_pos (hoff y hy hyA).1
      have hS₂y : Real.log (S₂ y) = (E.weight (μ y).1).toReal -
          Real.log (baseExceptionalWeight F E (μ y)) := by
        rw [hS₂def, zStrictWeight_eq_of_notMem F hμ hE hyA, exp_weight_toReal_eq_exp F hE hZ,
          Real.log_div (Real.exp_pos _).ne' hW.ne', Real.log_exp]
      have hS₁y : Real.log (S₁ y) = Real.log (projectiveWeight 0 (μ y).2) -
          Real.log (baseExceptionalWeight F E (μ y)) := by
        rw [hS₁def, strictWeight_eq_of_notMem F hμ hE hyA, Real.log_div hN0.ne' hW.ne']
      simp only [hΨdef, hΦdef]
      rw [(hbranch lam hl).2.1 _ hyE, excBranchOff, hS₂y, hS₁y, add_assoc, ← EReal.coe_add]
      congr 2
      simp only [excCorrection, hN₁def]
      ring)
    (fun lam hl => by
      refine ⟨SmoothRealForm.pullback (contMDiff_deformationProjX F hμ.contMDiff)
          (θ - (c - lam) • E.curvature).val,
        fun z => excBranch F E û c lam (μ z).1,
        fun z => (c - lam) * Real.log (S₂ z) + lam * Real.log (S₁ z) +
          (b - lam) * Real.log (N₁ z),
        GlobalPotentialPullback.thetaPlurisubharmonic_comp
          (contMDiff_deformationProjX F hμ.contMDiff) (hbranch lam hl).1, ?_, fun y _ => rfl⟩
      refine ((continuousOn_const.mul (hS₂c.continuousOn.log fun z hz => hz.1.2.ne')).add
        (continuousOn_const.mul (hS₁c.continuousOn.log fun z hz => hz.1.1.ne'))).add
        (continuousOn_const.mul (hN₁c.continuousOn.log fun z hz => (show 0 < N₁ z from hz.2).ne')))
    ?bdd ?bot
  case bdd =>
    intro lam hl
    have ht : c - lam ∈ Icc 0 c := ⟨by linarith [hl.2], by linarith [hl.1]⟩
    have hbig : IsBigClass (RealBottChern.ofRepresentative (θ - (c - lam) • E.curvature)) := by
      rw [ofRepresentative_sub_smul]
      exact (SGPT.PSH.BookCurrent.isBig_iff_isBigClass _).mp
        (isBigMeetingFirstDivisor_sub_smul_of_mem_Icc F hξ hξc ht).1
    have hVpot := MinimalSingularityLelongVanishing.isThetaPshPotential_thetaPshSupremum _ hbig
    have hx₀ : (μ p).1 ∉ nonKahlerLocus
        (RealBottChern.ofRepresentative (θ - (c - lam) • E.curvature)) := by
      rw [ofRepresentative_sub_smul]; exact hK _ ht
    obtain ⟨𝒩, h𝒩, a₀, b₀, hab⟩ :=
      BigClassEnvelopeContact.exists_isBoundedPotentialOn_thetaPshSupremum_offNonKahlerLocus
        (Nat.succ_pos m) _ hbig hVpot hx₀
    have hlow := thetaPshSupremum_le_excBranch F hE hû hcb.le hl hVpot.1
    set Sf : 𝒳 → ℝ := fun z => (c - lam) * Real.log (S₂ z) + lam * Real.log (S₁ z) +
      (b - lam) * Real.log (N₁ z) with hSf
    have hSc : ContinuousAt Sf p := by
      have hpos1 : S₁ p ≠ 0 := hS₁.ne'
      have hpos2 : S₂ p ≠ 0 := hS₂.ne'
      have hpos3 : N₁ p ≠ 0 := by rw [hN₁p]; exact one_ne_zero
      exact ((continuousAt_const.mul (hS₂c.continuousAt.log hpos2)).add
        (continuousAt_const.mul (hS₁c.continuousAt.log hpos1))).add
        (continuousAt_const.mul (hN₁c.continuousAt.log hpos3))
    have hev1 : ∀ᶠ y in 𝓝 p, |Sf y - Sf p| < 1 := by
      have := Metric.tendsto_nhds.mp hSc 1 one_pos
      filter_upwards [this] with y hy
      simpa [Real.dist_eq] using hy
    have hev2 : ∀ᶠ y in 𝓝 p, (μ y).1 ∈ 𝒩 :=
      (contMDiff_deformationProjX F hμ.contMDiff).continuous.continuousAt.eventually h𝒩
    refine ⟨|a₀| + |C₀| + |Sf p| + 1, ?_⟩
    filter_upwards [hev1, hev2] with y hy1 hy2
    have hw1 : (a₀ : EReal) ≤ excBranch F E û c lam (μ y).1 := (hab _ hy2).1.trans (hlow _)
    have hw2 := (hbranch lam hl).2.2 (μ y).1
    have hb1 : Sf p - 1 ≤ Sf y := by linarith [(abs_lt.mp hy1).1]
    have hb2 : Sf y ≤ Sf p + 1 := by linarith [(abs_lt.mp hy1).2]
    constructor
    · have h := add_le_add hw1 (EReal.coe_le_coe_iff.mpr hb1)
      rw [← EReal.coe_add] at h
      refine le_trans ?_ h
      rw [EReal.coe_le_coe_iff]
      have := neg_abs_le a₀; have := neg_abs_le (Sf p); have := abs_nonneg C₀
      linarith
    · have h := add_le_add hw2 (EReal.coe_le_coe_iff.mpr hb2)
      rw [← EReal.coe_add] at h
      refine h.trans ?_
      rw [EReal.coe_le_coe_iff]
      have := le_abs_self C₀; have := le_abs_self (Sf p); have := abs_nonneg a₀
      linarith
  case bot =>
    intro lam hl C
    have hlc : 0 < lam - c := by linarith [hl.1]
    have hlb : lam ∈ Icc 0 b := ⟨by linarith [hl.1], hl.2⟩
    set δ := Real.exp ((C - C₀) / (lam - c)) with hδ
    have hN₀p : N₀ p = 0 := by
      simp only [hN₀def, hp0, projectiveWeight_zero_projectiveZero]
    have hev : ∀ᶠ y in 𝓝 p, N₀ y < δ := by
      exact hN₀c.continuousAt.eventually (Iio_mem_nhds (by rw [hN₀p]; exact Real.exp_pos _))
    filter_upwards [hev, hNo.mem_nhds hpN] with y hyδ hyN hyA
    obtain ⟨h0, -, hZ⟩ := hoff y hyN hyA
    have hN0 := projectiveWeight_zero_pos h0
    have hW := baseExceptionalWeight_pos F hE hyA
    have hlogN1 : Real.log (projectiveWeight 1 (μ y).2) ≤ 0 :=
      Real.log_nonpos (projectiveWeight_nonneg 1 _) (projectiveWeight_le_one 1 _)
    have hlogW : Real.log (projectiveWeight 0 (μ y).2) ≤
        Real.log (baseExceptionalWeight F E (μ y)) :=
      Real.log_le_log hN0 (projectiveWeight_zero_le_baseExceptionalWeight F E (μ y))
    have hlogδ : Real.log (projectiveWeight 0 (μ y).2) < (C - C₀) / (lam - c) := by
      rw [← Real.log_exp ((C - C₀) / (lam - c))]
      exact Real.log_lt_log hN0 hyδ
    have hû' := hC₀ lam hlb _ hZ
    rw [max_eq_right (by linarith [hl.1])] at hû'
    simp only [hΦdef]
    have h := add_le_add hû' (le_refl (excCorrection F E b c lam (μ y) : EReal))
    refine lt_of_le_of_lt h ?_
    rw [← EReal.coe_add, EReal.coe_lt_coe_iff]
    have hmul : (lam - c) * Real.log (projectiveWeight 0 (μ y).2) < C - C₀ := by
      have := mul_lt_mul_of_pos_left hlogδ hlc
      rwa [mul_div_cancel₀ _ hlc.ne'] at this
    simp only [excCorrection, zero_mul, zero_add]
    nlinarith [mul_le_mul_of_nonneg_left hlogN1 (by linarith [hl.2] : (0 : ℝ) ≤ b - lam),
      mul_le_mul_of_nonneg_left hlogW hc.le]
  rw [key]
  refine iSup_congr fun lam => iSup_congr fun _ => ?_
  simp only [hΨdef, hN₁p, Real.log_one, mul_zero, add_zero]

end Formula

end SGPT.Okounkov.TranscendentalWN
