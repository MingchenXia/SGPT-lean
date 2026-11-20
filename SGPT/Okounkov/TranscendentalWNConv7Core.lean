import SGPT.Okounkov.TranscendentalWNConv7Limit
import SGPT.Okounkov.TranscendentalWNKeyEasy
import SGPT.Okounkov.TranscendentalWNKeyGeometry
import SGPT.Foundations.Analysis.Pending.SubmanifoldKahlerRestriction

/-!
# The analytic core of WN21 §7 from the perturbed weight and the fibre limit

Blueprint `claude-tok-wn-conv7`, nodes `tok-wn-conv7:weight-perturbation`,
`tok-wn-conv7:fibre-limit` and `tok-wn-conv7:contact-limit`; source WN21 §7.

`ContactMassLimitStatement F` (the analytic core) is split into two statements and the proved
WN21 Propositions 7.1 (consequence) and 7.3:

* `PerturbedWeightStatement F` (`tok-wn-conv7:weight-perturbation`, WN21 §7, first paragraph):
  a `Θ`-psh weight `Ψ` with `ũ ⪯ Ψ ⪯ ψ₂` for some `ψ₂ ∈ Ω(Θ)`, and a finite sequence of blow-ups
  `π : 𝒵 → 𝒳` from a compact connected manifold with `Ψ ∘ π = ψ_{D'} + h`, `h` smooth, and
  `π^*Θ - Θ_{D'} + dd^c h` Kähler;
* `FibreLimitStatement F` (`tok-wn-conv7:fibre-limit`: WN21 Lemma 7.5, Corollary 7.6,
  Proposition 7.4, the smallness estimate (eqeq) and the final limit): for every such weight, the
  `liminf` of the contact masses `∫_{X_{τ_k} ∩ D'_k} MA(v_k|_{X_{τ_k}})` is at most
  `∫_{X'} MA(v_{X'}) + ∫_ℰ MA(v_ℰ)` (the limits of `v_k + k` on `X'` and `ℰ`,
  `centralLimitPotential`).

`contactMassLimit_of_perturbedWeight_of_fibreLimit` proves
`PerturbedWeightStatement F → FibreLimitStatement F → ContactMassLimitStatement F`, using WN21
Proposition 7.3 (`diagonalPotentialMass_centralLimitPotential_le_restrictedVolume`, which uses the
consequence `v_k ⪯ Ψ` of Proposition 7.1, `prescribedEnvelope_le_add_of_logSingularities`) on `X'`
and on `ℰ`.  Both new statements are **statements only** (`def … : Prop`).
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
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending
open scoped SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity
open SGPT.Okounkov.TranscendentalMain
open SGPT.Okounkov.TranscendentalCore
open SGPT.Okounkov.TranscendentalVolumeConcavity

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))

/-! ### The masses of the limits on `X'` and `ℰ` -/

section Masses

variable {𝒳 : Type u} [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
  [IsComplexManifold (m + 1 + 1) 𝒳] {μ : 𝒳 → F.carrier × ProjectiveLine}

/-- `∫_{X'} ⟨(Θ|_{X'} + dd^c v_{X'})ⁿ⟩` for the limit `v_{X'}` of `v_k ∘ ι' + k` (WN21 §7). -/
def strictLimitMass (Θ : ClosedRealOneOneForm (m + 1 + 1) 𝒳) (χ : ℝ → ℝ) (Ψ : 𝒳 → EReal)
    (ι : F.carrier → 𝒳)
    (hι : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ ι)
    (hU : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι Θ).val
      (centralLimitPotential Θ μ χ Ψ ι)) : ℝ≥0∞ :=
  letI : MeasurableSpace F.carrier := borel F.carrier
  haveI : BorelSpace F.carrier := ⟨rfl⟩
  diagonalPotentialMass (ClosedRealOneOneForm.pullback hι Θ) (centralLimitPotential Θ μ χ Ψ ι) hU

/-- `∫_ℰ ⟨(Θ|_ℰ + dd^c v_ℰ)ⁿ⟩` for the limit `v_ℰ` of `v_k|_ℰ + k` (WN21 §7). -/
def exceptionalLimitMass (hμ : IsNormalConeDeformation F μ)
    (Θ : ClosedRealOneOneForm (m + 1 + 1) 𝒳) (χ : ℝ → ℝ) (Ψ : 𝒳 → EReal)
    (hU : letI := exceptionalChartedSpace F hμ
      haveI := isComplexManifold_exceptional F hμ
      IsThetaPshPotential (ClosedRealOneOneForm.pullback (contMDiff_exceptionalInclusion F hμ) Θ).val
        (centralLimitPotential Θ μ χ Ψ (Subtype.val : exceptionalSet F μ → 𝒳))) : ℝ≥0∞ :=
  letI := exceptionalChartedSpace F hμ
  haveI := isComplexManifold_exceptional F hμ
  letI : MeasurableSpace (exceptionalSet F μ) := borel (exceptionalSet F μ)
  haveI : BorelSpace (exceptionalSet F μ) := ⟨rfl⟩
  haveI := compactSpace_exceptional F hμ
  diagonalPotentialMass (ClosedRealOneOneForm.pullback (contMDiff_exceptionalInclusion F hμ) Θ)
    (centralLimitPotential Θ μ χ Ψ (Subtype.val : exceptionalSet F μ → 𝒳)) hU

end Masses

/-! ### The two remaining statements -/

/-- **`tok-wn-conv7:weight-perturbation`** (WN21 §7, first paragraph, with the rescaling
`ψ ↦ (1 - s)ψ` that keeps `ũ ⪯ Ψ`): under the hypotheses of `KeyConvergenceStatement` (without
`ι'`), for `Θ = θ̃ + εη'` there are a `Θ`-psh `Ψ` with `ũ = V_{θ̃} ⪯ Ψ ⪯ ψ₂` for some
`ψ₂ ∈ Ω(Θ)`, a finite sequence of blow-ups with smooth centres `π : 𝒵 → 𝒳` from a compact
connected manifold whose exceptional locus lies in `Supp D'`, a metered effective `ℚ`-divisor `D'`
on `𝒵` and a smooth `h` with `Ψ ∘ π = ψ_{D'} + h` and `π^*Θ - Θ_{D'} + dd^c h` Kähler. -/
def PerturbedWeightStatement : Prop :=
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
        ∀ (η' : KahlerBackground (m + 1 + 1) 𝒳) (ε : ℝ), 0 < ε →
          ∃ Ψ : 𝒳 → EReal,
            IsThetaPshPotential (deformationForm F hμ.contMDiff θ b c Eℰ + ε • η'.form).val Ψ ∧
            SGPT.PSH.SingularityLE
              (thetaPshSupremum (deformationForm F hμ.contMDiff θ b c Eℰ).val) Ψ ∧
            (∃ ψ₂ ∈ gentleKahlerCurrents (deformationForm F hμ.contMDiff θ b c Eℰ + ε • η'.form),
              SGPT.PSH.SingularityLE Ψ ψ₂) ∧
            ∃ (𝒵 : Type u) (_ : TopologicalSpace 𝒵) (_ : ChartedSpace (ComplexModel (m + 1 + 1)) 𝒵)
              (_ : IsComplexManifold (m + 1 + 1) 𝒵) (π : 𝒵 → 𝒳)
              (hπ : IsBlowupSequence (m + 1 + 1) 𝒳 𝒵 π)
              (D' : MeteredEffectiveQDivisor (m + 1 + 1) 𝒵) (h : 𝒵 → ℝ)
              (hh : ChartSmooth (n := m + 1 + 1) h),
              CompactSpace 𝒵 ∧ ConnectedSpace 𝒵 ∧ exceptionalLocus (m + 1 + 1) π ⊆ D'.support ∧
              (∀ z, Ψ (π z) = D'.weight z + (h z : EReal)) ∧
              ((ClosedRealOneOneForm.pullback hπ.contMDiff
                  (deformationForm F hμ.contMDiff θ b c Eℰ + ε • η'.form) - D'.curvature) +
                ddcClosedForm h hh).val.IsKahler

/-- **`tok-wn-conv7:fibre-limit`** (WN21 Lemma 7.5, Corollary 7.6, Proposition 7.4, the smallness
estimate (eqeq) and the final limit of the proof of the hard inequality of Theorem 1.7): under the
hypotheses of `KeyConvergenceStatement`, for every weight `Ψ` as in `PerturbedWeightStatement`
(`Θ`-psh, `ũ ⪯ Ψ`, `Ψ ∘ π = ψ_{D'} + h` on a finite sequence of blow-ups `π` with exceptional locus
in `Supp D'` and `π^*Θ - Θ_{D'} + dd^c h` Kähler), every cutoff `χ`, every `τ_k ∈ ℂ \ {0}` with `e^{k/2}|τ_k| → 0` and
all sections `s_k` over `x ↦ (x, τ_k)`,
`liminf_k ∫_{X_{τ_k} ∩ {v_k = g_k}} ⟨((Θ + dd^c v_k)|_{X_{τ_k}})ⁿ⟩ ≤ ∫_{X'} ⟨(Θ|_{X'} + dd^c v_{X'})ⁿ⟩ +
∫_ℰ ⟨(Θ|_ℰ + dd^c v_ℰ)ⁿ⟩`, where `v_k = P_Θ[Ψ](g_k)` and `v_{X'}`, `v_ℰ` are the regularized limits of
`v_k + k` on `X'` and `ℰ`. -/
def FibreLimitStatement : Prop :=
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
          (hι : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ ι),
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
          ∀ τ : ℕ → ℂ, (∀ k, τ k ≠ 0) →
            Tendsto (fun k : ℕ => Real.exp ((k : ℝ) / 2) * ‖τ k‖) atTop (𝓝 0) →
          ∀ (s : ℕ → F.carrier → 𝒳)
            (hs : ∀ k, ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1))
              ∞ (s k)),
            (∀ k x, μ (s k x) = (x, affineLinePoint (τ k))) →
          ∀ (hw : ∀ k, IsThetaPshPotential (ClosedRealOneOneForm.pullback (hs k)
              (deformationForm F hμ.contMDiff θ b c Eℰ + ε • η'.form)).val
              (fun x => prescribedEnvelope
                (deformationForm F hμ.contMDiff θ b c Eℰ + ε • η'.form)
                (cutoffObstacle μ χ k) Ψ (s k x)))
            (hX' : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι
              (deformationForm F hμ.contMDiff θ b c Eℰ + ε • η'.form)).val
              (centralLimitPotential (deformationForm F hμ.contMDiff θ b c Eℰ + ε • η'.form)
                μ χ Ψ ι))
            (hℰ : letI := exceptionalChartedSpace F hμ
              haveI := isComplexManifold_exceptional F hμ
              IsThetaPshPotential (ClosedRealOneOneForm.pullback
                (contMDiff_exceptionalInclusion F hμ)
                (deformationForm F hμ.contMDiff θ b c Eℰ + ε • η'.form)).val
                (centralLimitPotential (deformationForm F hμ.contMDiff θ b c Eℰ + ε • η'.form)
                  μ χ Ψ (Subtype.val : exceptionalSet F μ → 𝒳))),
            liminf (fun k => envelopeContactMass F
                (deformationForm F hμ.contMDiff θ b c Eℰ + ε • η'.form)
                (cutoffObstacle μ χ k) Ψ (s k) (hs k) (hw k)) atTop ≤
              strictLimitMass F (deformationForm F hμ.contMDiff θ b c Eℰ + ε • η'.form) χ Ψ ι hι
                  hX' +
                exceptionalLimitMass F hμ (deformationForm F hμ.contMDiff θ b c Eℰ + ε • η'.form)
                  χ Ψ hℰ

/-! ### The reduction -/

/-- A potential less singular than one which is genuine on `ι(V)` is genuine on `ι(V)`. -/
private theorem isThetaPshPotential_comp_of_le {N k : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel N) X] [IsComplexManifold N X] {V : Type*} [TopologicalSpace V]
    [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V] {ι : V → X}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel N) ∞ ι)
    {Θ₀ Θ : ClosedRealOneOneForm N X} {φ ψ : X → EReal} (hψ : IsThetaPshPotential Θ.val ψ)
    (hφι : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι Θ₀).val (fun y => φ (ι y)))
    (hle : SGPT.PSH.SingularityLE φ ψ) :
    IsThetaPshPotential (ClosedRealOneOneForm.pullback hι Θ).val (fun y => ψ (ι y)) := by
  obtain ⟨C, hC⟩ := (SGPT.PSH.singularityLE_iff_exists_real _ _).mp hle
  refine ⟨GlobalPotentialPullback.thetaPlurisubharmonic_comp hι hψ.1, fun x U hU hx => ?_⟩
  obtain ⟨y, hyU, hy⟩ := hφι.2 x U hU hx
  refine ⟨y, hyU, fun hbot => hy ?_⟩
  have h := hC (ι y)
  have hbot' : ψ (ι y) = ⊥ := hbot
  rw [hbot', EReal.bot_add] at h
  exact le_bot_iff.mp h

/-- **`tok-wn-conv7:contact-limit` from the two remaining statements**:
`PerturbedWeightStatement F` and `FibreLimitStatement F` give `ContactMassLimitStatement F`
(WN21 Proposition 7.3 bounds the masses of `v_{X'}` and `v_ℰ` by the restricted volumes). -/
theorem contactMassLimit_of_perturbedWeight_of_fibreLimit (hW : PerturbedWeightStatement F)
    (hL : FibreLimitStatement F) : ContactMassLimitStatement F := by
  intro E hE hE0 𝒳 _ _ _ μ hμ Eℰ hEℰ θ b c hc hcb hξ hξc ι hι hμι η' ε hε χ hχ
  set θ₀ := deformationForm F hμ.contMDiff θ b c Eℰ with hθ₀
  set Θ := θ₀ + ε • η'.form with hΘ
  have := compactSpace_normalCone F hμ
  have := connectedSpace_normalCone F hμ
  have : Nonempty 𝒳 := ConnectedSpace.toNonempty
  obtain ⟨Ψ, hΨ, hVΨ, ⟨ψ₂, hψ₂, hΨψ₂⟩, 𝒵, t𝒵, c𝒵, m𝒵, π, hπ, D', h, hh, h𝒵c, h𝒵conn, hExc,
    hΨπ, hK⟩ := hW E hE hE0 𝒳 μ hμ Eℰ hEℰ θ b c hc hcb hξ hξc η' ε hε
  refine ⟨Ψ, hΨ, hVΨ, fun τ hτ0 hτlim s hs hμs hw => ?_⟩
  -- `β` is big and its Kähler locus meets `X'` and `ℰ`
  obtain ⟨hbig, -, hX'K, hEK⟩ := betaBig F E hE 𝒳 μ hμ Eℰ hEℰ.isDivisorMetric θ b c hc
    (by linarith) hξ hξc.1
  have hbigC : IsBigClass (RealBottChern.ofRepresentative θ₀) :=
    (SGPT.PSH.BookCurrent.isBig_iff_isBigClass _).mp hbig
  have hV : IsThetaPshPotential θ₀.val (thetaPshSupremum θ₀.val) :=
    MinimalSingularityLelongVanishing.isThetaPshPotential_thetaPshSupremum θ₀ hbigC
  -- a gentle current of `β` dominated by `V_{θ̃}` is genuine along a connected `V` meeting `K(β)`
  have hVle : ∀ φ : 𝒳 → EReal, IsThetaPshPotential θ₀.val φ →
      SGPT.PSH.SingularityLE φ (thetaPshSupremum θ₀.val) := fun φ hφ => by
    obtain ⟨Mφ, hMφ⟩ := hφ.exists_global_upper_bound
    have hle0 : (fun z => φ z + ((-Mφ : ℝ) : EReal)) ≤ 0 := fun z => by
      have h := add_le_add (hMφ z) (le_refl ((-Mφ : ℝ) : EReal))
      rwa [← EReal.coe_add, add_neg_cancel, EReal.coe_zero] at h
    have hV' := le_thetaPshSupremum (hφ.add_const (-Mφ)) hle0
    refine (SGPT.PSH.singularityLE_iff_exists_real _ _).mpr ⟨Mφ, fun z => ?_⟩
    have h1 := add_le_add (hV' z) (le_refl ((Mφ : ℝ) : EReal))
    rwa [add_assoc, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, add_zero] at h1
  -- `Ψ` and `ψ₂` are genuine on `X'`
  have hZX' : ∃ y : F.carrier, ι y ∉ nonKahlerLocus (RealBottChern.ofRepresentative θ₀) := by
    obtain ⟨z, hz, hzK⟩ := hX'K
    rw [← (range_centralLift F hμ hι hμι).1] at hz
    obtain ⟨y, rfl⟩ := hz
    exact ⟨y, hzK⟩
  obtain ⟨φX, hφX, hφXι⟩ := exists_gentle_nondegenerate hι θ₀ hbigC hZX'
  have hΨι : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι Θ).val (fun y => Ψ (ι y)) :=
    isThetaPshPotential_comp_of_le hι hΨ hφXι
      (SGPT.PSH.singularityLE_trans (hVle φX hφX.1.1) hVΨ)
  have hψ₂ι : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι Θ).val
      (fun y => ψ₂ (ι y)) := isThetaPshPotential_comp_of_le hι hψ₂.1.1 hΨι hΨψ₂
  -- `Ψ` and `ψ₂` are genuine on `ℰ`
  let := exceptionalChartedSpace F hμ
  have := isComplexManifold_exceptional F hμ
  have := connectedSpace_exceptional F hμ
  have hιE := contMDiff_exceptionalInclusion F hμ
  have hZE : ∃ y : exceptionalSet F μ,
      (y : 𝒳) ∉ nonKahlerLocus (RealBottChern.ofRepresentative θ₀) := by
    obtain ⟨z, hz, hzK⟩ := hEK
    exact ⟨⟨z, hz⟩, hzK⟩
  obtain ⟨φE, hφE, hφEι⟩ := exists_gentle_nondegenerate hιE θ₀ hbigC hZE
  have hΨE : IsThetaPshPotential (ClosedRealOneOneForm.pullback hιE Θ).val
      (fun y : exceptionalSet F μ => Ψ y) :=
    isThetaPshPotential_comp_of_le hιE hΨ hφEι
      (SGPT.PSH.singularityLE_trans (hVle φE hφE.1.1) hVΨ)
  have hψ₂E : IsThetaPshPotential (ClosedRealOneOneForm.pullback hιE Θ).val
      (fun y : exceptionalSet F μ => ψ₂ y) := isThetaPshPotential_comp_of_le hιE hψ₂.1.1 hΨE hΨψ₂
  -- the obstacles and the log resolution of `Ψ`
  have hg : ∀ j, Continuous (cutoffObstacle μ χ j) := fun j =>
    (continuous_cutoffObstacleLine hχ j).comp (continuous_snd.comp hμ.contMDiff.continuous)
  have hπm := HironakaChowLemma.isAnalyticModification_of_isBlowupSequence hπ
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ z, |h z| ≤ B := by
    have : Nonempty 𝒵 := ConnectedSpace.toNonempty
    have hc : Continuous fun z => |h z| :=
      (ProductTestForms.ChartSmooth.continuous hh).abs
    obtain ⟨z₀, -, hz₀⟩ := isCompact_univ.exists_isMaxOn univ_nonempty hc.continuousOn
    exact ⟨_, fun z => hz₀ (mem_univ z)⟩
  let Lπ : ResidualNefReduction.HasLogSingularitiesAlong D' (fun z => Ψ (π z)) :=
    { residual := h, bound := B, residual_bound := hB, weight_add := hΨπ }
  -- the limits are genuine potentials
  have hι0 : ∀ y, (μ (ι y)).2 = projectiveZero := fun y => by rw [hμι]
  have hE0' : ∀ y : exceptionalSet F μ, (μ y).2 = projectiveZero := fun y =>
    ((mem_deformationCentre_iff F).mp y.2).2
  have hX' := isThetaPshPotential_centralLimitPotential hι hg hι0 hΨ hΨι
  have hℰ := isThetaPshPotential_centralLimitPotential hιE hg hE0' hΨ hΨE
  -- the fibre limit
  have hlim := hL E hE hE0 𝒳 μ hμ Eℰ hEℰ θ b c hc hcb hξ hξc ι hι hμι η' ε hε Ψ hΨ hVΨ 𝒵 π hπ D' h
    hh h𝒵c h𝒵conn hExc hΨπ hK χ hχ τ hτ0 hτlim s hs hμs hw hX' hℰ
  refine hlim.trans (add_le_add ?_ ?_)
  · -- `X'`
    let : MeasurableSpace F.carrier := borel F.carrier
    have : BorelSpace F.carrier := ⟨rfl⟩
    have h73 := diagonalPotentialMass_centralLimitPotential_le_restrictedVolume hι F.omega hχ hg hΨ
      hΨι hπm D' Lπ hψ₂ hΨψ₂ hψ₂ι hX'
    have hclass : RealBottChern.ofRepresentative θ₀ +
        ε • RealBottChern.ofRepresentative η'.form = RealBottChern.ofRepresentative Θ := by
      rw [hΘ, RealBottChern.ofRepresentative_add, RealBottChern.ofRepresentative_smul]
    rw [hclass]
    unfold sectionRestrictedVolume
    rw [← restrictedVolume_eq_classRestrictedVolume hι Θ]
    exact h73
  · -- `ℰ`
    let : MeasurableSpace (exceptionalSet F μ) := borel (exceptionalSet F μ)
    have : BorelSpace (exceptionalSet F μ) := ⟨rfl⟩
    have := compactSpace_exceptional F hμ
    let ωE : KahlerBackground (m + 1) (exceptionalSet F μ) :=
      SubmanifoldKahlerRestriction.kahlerBackground (Nat.le_succ (m + 1))
        (fun _ hz => regularAtDim_exceptionalSet F hμ hz) η'
    have h73 := diagonalPotentialMass_centralLimitPotential_le_restrictedVolume hιE ωE hχ hg hΨ
      hΨE hπm D' Lπ hψ₂ hΨψ₂ hψ₂E hℰ
    have hclass : RealBottChern.ofRepresentative θ₀ +
        ε • RealBottChern.ofRepresentative η'.form = RealBottChern.ofRepresentative Θ := by
      rw [hΘ, RealBottChern.ofRepresentative_add, RealBottChern.ofRepresentative_smul]
    rw [hclass]
    unfold exceptionalRestrictedVolume
    rw [← restrictedVolume_eq_classRestrictedVolume hιE Θ]
    exact h73

/-- **`tok-wn:convergence`** from measure control (WN21 §6, lane WN-CONV6) and the two remaining
statements of WN21 §7. -/
theorem keyConvergence_of_perturbedWeight_of_fibreLimit (hMC : MeasureControlStatement F)
    (hW : PerturbedWeightStatement F) (hL : FibreLimitStatement F) : KeyConvergenceStatement F :=
  keyConvergence_of_contactMassLimit F hMC (contactMassLimit_of_perturbedWeight_of_fibreLimit F hW hL)

end SGPT.Okounkov.TranscendentalWN
