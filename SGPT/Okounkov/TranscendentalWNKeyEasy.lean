import SGPT.Okounkov.TranscendentalWNKeyAssembly
import SGPT.Okounkov.TranscendentalBodySingDecrease

/-!
# The key easy inequality from the lower semicontinuity of fibre masses (package WN-KEY)

Blueprint `claude-tok-wn-key`, nodes `tok-wn-key:fibre-mass-lsc` and
`tok-wn-key:key-easy-reduction`; source WN21 §5 (the easy inequality of Theorem 1.7).

WN21's proof of `vol_{𝒳|X'}(β) + vol_{𝒳|ℰ}(β) ≤ vol(ξ)` has two parts:

1. an *analytic core*: for a current `T = Θ + dd^c φ` with gentle analytic singularities on `𝒳`
   whose restrictions to `X'` and `ℰ` are not identically `-∞`, the masses of the restrictions to
   the fibres `X_τ` asymptotically dominate the sum of the masses of the restrictions to `X'` and
   `ℰ` (`FibreMassLSCStatement`, `tok-wn-key:fibre-mass-lsc`: `T` is smooth off its polar set,
   and the fibres `X_τ` converge smoothly to `X'` away from `ℰ` and to `ℰ` away from `X'`);
2. a *soft part*: choose `T₁, T₂ ∈ Ω(β)` nearly computing `vol_{𝒳|X'}(β)` and
   `vol_{𝒳|ℰ}(β)`, a current `T ∈ Ω(β)` less singular than both (`tok:sing-decrease`), use the
   monotonicity of non-pluripolar masses on `X'` and `ℰ` and `vol_{𝒳|X_τ}(β) = vol(ξ)`
   (`tok-wn:formula-fibre`).

This file states the analytic core and proves the soft part:
`keyEasy_of_fibreMassLSC : FibreMassLSCStatement F → FibreRestrictedVolumeStatement F →
BetaBigStatement F → KeyEasyStatement F`.  (`BetaBigStatement` supplies currents in `Ω(β)` that
are finite somewhere on `X'` and on `ℰ`, needed when one of the two restricted volumes vanishes.)
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
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Okounkov.TranscendentalMain
open SGPT.Okounkov.TranscendentalVolumeConcavity
open SGPT.Okounkov.TranscendentalCore

/-! ### Generic facts on restricted masses -/

section Generic

variable {N k : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel (N + 1)) X]
  [IsComplexManifold (N + 1) X]
  {V : Type*} [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  {ι : V → X} (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel (N + 1)) ∞ ι)

include hι in
/-- A potential less singular than one with nondegenerate restriction has nondegenerate
restriction. -/
theorem isThetaPshPotential_comp_of_singularityLE {Θ : ClosedRealOneOneForm (N + 1) X}
    {φ ψ : X → EReal} (hψ : IsThetaPshPotential Θ.val ψ)
    (hφι : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι Θ).val (fun y => φ (ι y)))
    (hle : SGPT.PSH.SingularityLE φ ψ) :
    IsThetaPshPotential (ClosedRealOneOneForm.pullback hι Θ).val (fun y => ψ (ι y)) := by
  obtain ⟨C, hC⟩ := hle
  refine ⟨GlobalPotentialPullback.thetaPlurisubharmonic_comp hι hψ.1, fun x U hU hx => ?_⟩
  obtain ⟨y, hyU, hy⟩ := hφι.2 x U hU hx
  refine ⟨y, hyU, fun hbot => hy ?_⟩
  have h := hC (ι y) (mem_univ _)
  have hbot' : ψ (ι y) = ⊥ := hbot
  rw [hbot', EReal.bot_add] at h
  exact le_bot_iff.mp h

variable [MeasurableSpace V] [BorelSpace V] [CompactSpace V]

include hι in
/-- Monotonicity of restricted masses in the singularity order. -/
theorem diagonalPotentialMass_comp_le_of_singularityLE (ωV : KahlerBackground k V)
    {Θ : ClosedRealOneOneForm (N + 1) X} {φ ψ : X → EReal}
    (hφι : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι Θ).val (fun y => φ (ι y)))
    (hψι : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι Θ).val (fun y => ψ (ι y)))
    (hle : SGPT.PSH.SingularityLE φ ψ) :
    diagonalPotentialMass (ClosedRealOneOneForm.pullback hι Θ) (fun y => φ (ι y)) hφι ≤
      diagonalPotentialMass (ClosedRealOneOneForm.pullback hι Θ) (fun y => ψ (ι y)) hψι := by
  obtain ⟨C, hC⟩ := hle
  exact diagonalPotentialMass_mono_of_kahler ωV hφι hψι ⟨C, fun y _ => hC (ι y) (mem_univ _)⟩

variable [CompactSpace X] [Nonempty X]

include hι in
/-- **Near-optimal currents for a restricted volume.**  If some `φ₀ ∈ Ω(Θ)` has nondegenerate
restriction, then for every `e > 0` some `φ ∈ Ω(Θ)` with nondegenerate restriction has restricted
mass at least `vol_{X|V}(Θ) - e`. -/
theorem exists_le_diagonalPotentialMass_add (ωV : KahlerBackground k V)
    (Θ : ClosedRealOneOneForm (N + 1) X) {φ₀ : X → EReal} (hφ₀ : φ₀ ∈ gentleKahlerCurrents Θ)
    (hφ₀ι : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι Θ).val (fun y => φ₀ (ι y)))
    {e : ℝ≥0∞} (he : 0 < e) :
    ∃ φ ∈ gentleKahlerCurrents Θ, ∃ hφι : IsThetaPshPotential
        (ClosedRealOneOneForm.pullback hι Θ).val (fun y => φ (ι y)),
      restrictedVolume ι hι Θ ≤
        diagonalPotentialMass (ClosedRealOneOneForm.pullback hι Θ) (fun y => φ (ι y)) hφι + e := by
  by_cases h0 : restrictedVolume ι hι Θ = 0
  · exact ⟨φ₀, hφ₀, hφ₀ι, by rw [h0]; exact zero_le⟩
  have hlt : restrictedVolume ι hι Θ - e < restrictedVolume ι hι Θ :=
    ENNReal.sub_lt_self (restrictedVolume_lt_top hι ωV Θ).ne h0 he.ne'
  conv_rhs at hlt => rw [restrictedVolume]
  obtain ⟨φ, hlt⟩ := lt_iSup_iff.mp hlt
  obtain ⟨hφ, hlt⟩ := lt_iSup_iff.mp hlt
  obtain ⟨hφι, hlt⟩ := lt_iSup_iff.mp hlt
  exact ⟨φ, hφ, hφι, tsub_le_iff_right.mp hlt.le⟩

omit [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [Nonempty X] in
include hι in
/-- **A current of `Ω(Θ)` finite on `ι(V)`**: if `{Θ}` is big and `ι(V)` meets its Kähler
locus, some `φ ∈ Ω(Θ)` has nondegenerate restriction to the connected `V` (Boucksom's current,
finite somewhere on `ι(V)`, made gentle by `tok:sing-decrease`). -/
theorem exists_gentle_nondegenerate [ConnectedSpace V] (Θ : ClosedRealOneOneForm (N + 1) X)
    (hbig : IsBigClass (RealBottChern.ofRepresentative Θ))
    (hZ : ∃ y : V, ι y ∉ nonKahlerLocus (RealBottChern.ofRepresentative Θ)) :
    ∃ φ ∈ gentleKahlerCurrents Θ,
      IsThetaPshPotential (ClosedRealOneOneForm.pullback hι Θ).val (fun y => φ (ι y)) := by
  obtain ⟨κ, ψ, hψ, y, hy⟩ := exists_kahler_potential_finite_on Θ hbig hZ
  obtain ⟨φ, hφ, -, hle⟩ := TranscendentalBody.exists_mem_gentleKahlerCurrents_ge hψ
  refine ⟨φ, hφ, GlobalPotentialPullback.thetaPlurisubharmonic_comp hι hφ.1.1.1,
    ThetaPshIdentityPrinciple.locallyNondegenerate_of_exists_ne_bot
      (GlobalPotentialPullback.thetaPlurisubharmonic_comp hι hφ.1.1.1) ⟨y, ?_⟩⟩
  intro hbot
  have h := hle (ι y)
  rw [hbot] at h
  exact hy (le_bot_iff.mp h)

end Generic

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))

/-! ### Restricted masses on the deformation -/

section Masses

variable {𝒳 : Type u} [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
  [IsComplexManifold (m + 1 + 1) 𝒳] {μ : 𝒳 → F.carrier × ProjectiveLine}

/-- The non-pluripolar mass `∫_X ⟨(s^*Θ + dd^c(φ ∘ s))^n⟩` of the restriction of `φ` along a
holomorphic map `s : X → 𝒳` (a section of `μ` over `x ↦ (x, τ)`, image `X_τ`, or the lift `ι'`,
image `X'`). -/
def sectionMass (s : F.carrier → 𝒳)
    (hs : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ s)
    (Θ : ClosedRealOneOneForm (m + 1 + 1) 𝒳) (φ : 𝒳 → EReal)
    (hw : IsThetaPshPotential (ClosedRealOneOneForm.pullback hs Θ).val (fun x => φ (s x))) :
    ℝ≥0∞ :=
  letI : MeasurableSpace F.carrier := borel F.carrier
  haveI : BorelSpace F.carrier := ⟨rfl⟩
  diagonalPotentialMass (ClosedRealOneOneForm.pullback hs Θ) (fun x => φ (s x)) hw

/-- The non-pluripolar mass `∫_ℰ ⟨(Θ|_ℰ + dd^c φ|_ℰ)^n⟩` of the restriction of `φ` to the
exceptional divisor. -/
def exceptionalMass (hμ : IsNormalConeDeformation F μ) (Θ : ClosedRealOneOneForm (m + 1 + 1) 𝒳)
    (φ : 𝒳 → EReal)
    (hw : letI := exceptionalChartedSpace F hμ
      haveI := isComplexManifold_exceptional F hμ
      IsThetaPshPotential (ClosedRealOneOneForm.pullback (contMDiff_exceptionalInclusion F hμ) Θ).val
        (fun y : exceptionalSet F μ => φ y)) : ℝ≥0∞ :=
  letI := exceptionalChartedSpace F hμ
  haveI := isComplexManifold_exceptional F hμ
  letI : MeasurableSpace (exceptionalSet F μ) := borel (exceptionalSet F μ)
  haveI : BorelSpace (exceptionalSet F μ) := ⟨rfl⟩
  haveI := compactSpace_exceptional F hμ
  diagonalPotentialMass (ClosedRealOneOneForm.pullback (contMDiff_exceptionalInclusion F hμ) Θ)
    (fun y : exceptionalSet F μ => φ y) hw

end Masses

/-! ### The analytic core -/

/-- **`tok-wn-key:fibre-mass-lsc`** (WN21 §5, the core of the easy inequality of Theorem 1.7):
let `Θ` be a closed real `(1,1)`-form on the deformation `𝒳` and `φ` a `Θ`-psh potential with
gentle analytic singularities (so `T = Θ + dd^c φ` is smooth off the polar set of `φ`) whose
restrictions to `X'` (along the lift `ι'`) and to `ℰ` are not identically `-∞`.  Then the masses
of the restrictions of `T` to the fibres `X_τ` asymptotically dominate the sum of the masses on
`X'` and `ℰ`: for every `δ > 0` and every neighbourhood `W` of `0 ∈ ℙ¹` there are `τ ∈ W \ {0}`
and the section `s` of `μ` over `x ↦ (x, τ)` with
`∫_{X'} ⟨(T|_{X'})^n⟩ + ∫_ℰ ⟨(T|_ℰ)^n⟩ ≤ ∫_{X_τ} ⟨(T|_{X_τ})^n⟩ + δ`. -/
def FibreMassLSCStatement : Prop :=
  ∀ (𝒳 : Type u) [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
    [IsComplexManifold (m + 1 + 1) 𝒳] (μ : 𝒳 → F.carrier × ProjectiveLine)
    (hμ : IsNormalConeDeformation F μ) (Θ : ClosedRealOneOneForm (m + 1 + 1) 𝒳)
    (φ : 𝒳 → EReal), φ ∈ gentleCurrents Θ →
    ∀ (ι : F.carrier → 𝒳)
      (hι : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ ι),
      (∀ x, μ (ι x) = (x, projectiveZero)) →
      ∀ (hX' : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι Θ).val (fun x => φ (ι x)))
        (hℰ : letI := exceptionalChartedSpace F hμ
          haveI := isComplexManifold_exceptional F hμ
          IsThetaPshPotential
            (ClosedRealOneOneForm.pullback (contMDiff_exceptionalInclusion F hμ) Θ).val
            (fun y : exceptionalSet F μ => φ y)),
        ∀ δ : ℝ≥0∞, 0 < δ → ∀ W ∈ 𝓝 projectiveZero, ∃ p ∈ W, p ≠ projectiveZero ∧
          ∃ (s : F.carrier → 𝒳)
            (hs : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ s),
            (∀ x, μ (s x) = (x, p)) ∧
            ∃ hw : IsThetaPshPotential (ClosedRealOneOneForm.pullback hs Θ).val
                (fun x => φ (s x)),
              sectionMass F ι hι Θ φ hX' + exceptionalMass F hμ Θ φ hℰ ≤
                sectionMass F s hs Θ φ hw + δ

/-! ### The soft part -/

/-- **`tok-wn:key-easy` from the analytic core** (`tok-wn-key:key-easy-reduction`, WN21 §5):
`FibreMassLSCStatement`, `tok-wn:formula-fibre` (`FibreRestrictedVolumeStatement`, package
WN-VF) and `tok-wn:beta-big` (`BetaBigStatement`, package WN-DEF) give the key easy inequality
`vol_{𝒳|X'}(β) + vol_{𝒳|ℰ}(β) ≤ vol(ξ)`. -/
theorem keyEasy_of_fibreMassLSC (hL : FibreMassLSCStatement F)
    (hFib : FibreRestrictedVolumeStatement F) (hBeta : BetaBigStatement F) :
    KeyEasyStatement F := by
  intro E hE hE0 𝒳 _ _ _ μ hμ Eℰ hEℰ θ b c hc hcb hξ hξc ι hι hμι
  set Θ := deformationForm F hμ.contMDiff θ b c Eℰ with hΘ
  set V := classVolumeReal F (RealBottChern.ofRepresentative θ) with hVdef
  have := compactSpace_normalCone F hμ
  have := connectedSpace_normalCone F hμ
  let : MeasurableSpace F.carrier := borel F.carrier
  have : BorelSpace F.carrier := ⟨rfl⟩
  let := exceptionalChartedSpace F hμ
  have := isComplexManifold_exceptional F hμ
  let : MeasurableSpace (exceptionalSet F μ) := borel (exceptionalSet F μ)
  have : BorelSpace (exceptionalSet F μ) := ⟨rfl⟩
  have := compactSpace_exceptional F hμ
  have := connectedSpace_exceptional F hμ
  obtain ⟨η'⟩ := nonempty_kahler_normalCone F hμ
  have hιE := contMDiff_exceptionalInclusion F hμ
  let ωE : KahlerBackground (m + 1) (exceptionalSet F μ) :=
    SubmanifoldKahlerRestriction.kahlerBackground (Nat.le_succ (m + 1))
      (fun _ hz => regularAtDim_exceptionalSet F hμ hz) η'
  -- the two restricted volumes as restricted volumes of the representative `Θ`
  set RX := restrictedVolume ι hι Θ with hRX
  set RE := restrictedVolume (Subtype.val : exceptionalSet F μ → 𝒳) hιE Θ with hRE
  have hRXc : sectionRestrictedVolume F ι hι (RealBottChern.ofRepresentative Θ) = RX :=
    (restrictedVolume_eq_classRestrictedVolume hι Θ).symm
  have hREc : exceptionalRestrictedVolume F hμ (RealBottChern.ofRepresentative Θ) = RE :=
    (restrictedVolume_eq_classRestrictedVolume hιE Θ).symm
  -- default currents of `Ω(β)` with nondegenerate restrictions (`tok-wn:beta-big`)
  obtain ⟨hbig, -, hX', hEx⟩ := hBeta E hE 𝒳 μ hμ Eℰ hEℰ.isDivisorMetric θ b c hc hcb hξ hξc.1
  have hbigC : IsBigClass (RealBottChern.ofRepresentative Θ) :=
    (SGPT.PSH.BookCurrent.isBig_iff_isBigClass _).mp hbig
  have hZX' : ∃ y : F.carrier, ι y ∉ nonKahlerLocus (RealBottChern.ofRepresentative Θ) := by
    obtain ⟨z, hz, hzK⟩ := hX'
    rw [← (range_centralLift F hμ hι hμι).1] at hz
    obtain ⟨y, rfl⟩ := hz
    exact ⟨y, hzK⟩
  have hZE : ∃ y : exceptionalSet F μ,
      (y : 𝒳) ∉ nonKahlerLocus (RealBottChern.ofRepresentative Θ) := by
    obtain ⟨z, hz, hzK⟩ := hEx
    exact ⟨⟨z, hz⟩, hzK⟩
  obtain ⟨φX, hφX, hφXι⟩ := exists_gentle_nondegenerate hι Θ hbigC hZX'
  obtain ⟨φE, hφE, hφEι⟩ := exists_gentle_nondegenerate hιE Θ hbigC hZE
  -- the main inequality in `ℝ≥0∞`
  have hmain : RX + RE ≤ ENNReal.ofReal V := by
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    set a : ℝ≥0∞ := (ε : ℝ≥0∞) / 2 with ha
    set e : ℝ≥0∞ := a / 2 with he
    have hε' : (0 : ℝ≥0∞) < ε := ENNReal.coe_pos.mpr hε
    have ha0 : 0 < a := ENNReal.half_pos hε'.ne'
    have he0 : 0 < e := ENNReal.half_pos ha0.ne'
    obtain ⟨φ₁, hφ₁, hφ₁ι, h₁⟩ :=
      exists_le_diagonalPotentialMass_add hι F.omega Θ hφX hφXι he0
    obtain ⟨φ₂, hφ₂, hφ₂ι, h₂⟩ :=
      exists_le_diagonalPotentialMass_add hιE ωE Θ hφE hφEι he0
    obtain ⟨ψ, hψ, hle₁, hle₂⟩ :=
      TranscendentalBody.exists_mem_gentleKahlerCurrents_singularityLE hφ₁.2 hφ₂.2
    have hψX := isThetaPshPotential_comp_of_singularityLE hι hψ.1.1 hφ₁ι hle₁
    have hψE := isThetaPshPotential_comp_of_singularityLE hιE hψ.1.1 hφ₂ι hle₂
    have hm₁ := diagonalPotentialMass_comp_le_of_singularityLE hι F.omega hφ₁ι hψX hle₁
    have hm₂ := diagonalPotentialMass_comp_le_of_singularityLE hιE ωE hφ₂ι hψE hle₂
    obtain ⟨p, -, hp, s, hs, hμs, hw, hlsc⟩ :=
      hL 𝒳 μ hμ Θ ψ hψ.1 ι hι hμι hψX hψE a ha0 univ univ_mem
    -- the fibre mass is at most `vol_{𝒳|X_τ}(β) = vol(ξ)`
    have hfib : sectionMass F s hs Θ ψ hw ≤ ENNReal.ofReal V := by
      have hle : sectionMass F s hs Θ ψ hw ≤ restrictedVolume s hs Θ :=
        le_iSup_of_le ψ (le_iSup_of_le hψ (le_iSup_of_le hw le_rfl))
      have hval := (hFib E hE hE0 𝒳 μ hμ Eℰ hEℰ θ b c hc hcb hξ hξc p hp s hs hμs).1
      have hfin : restrictedVolume s hs Θ ≠ ⊤ := (restrictedVolume_lt_top hs F.omega Θ).ne
      have hsec : sectionRestrictedVolume F s hs (RealBottChern.ofRepresentative Θ) =
          restrictedVolume s hs Θ := (restrictedVolume_eq_classRestrictedVolume hs Θ).symm
      rw [hsec] at hval
      have hV' : V = (restrictedVolume s hs Θ).toReal := by rw [hVdef, ← hval]
      rw [hV', ENNReal.ofReal_toReal hfin]
      exact hle
    calc RX + RE ≤ (diagonalPotentialMass (ClosedRealOneOneForm.pullback hι Θ)
            (fun y => φ₁ (ι y)) hφ₁ι + e) +
          (diagonalPotentialMass (ClosedRealOneOneForm.pullback hιE Θ)
            (fun y : exceptionalSet F μ => φ₂ y) hφ₂ι + e) := add_le_add h₁ h₂
      _ ≤ (sectionMass F ι hι Θ ψ hψX + e) + (exceptionalMass F hμ Θ ψ hψE + e) := by
          gcongr
          · exact hm₁
          · exact hm₂
      _ = (sectionMass F ι hι Θ ψ hψX + exceptionalMass F hμ Θ ψ hψE) + (e + e) := by ring
      _ ≤ (sectionMass F s hs Θ ψ hw + a) + (e + e) := by gcongr
      _ ≤ (ENNReal.ofReal V + a) + (e + e) := by gcongr
      _ = ENNReal.ofReal V + ε := by
          rw [he, ENNReal.add_halves, add_assoc, ha, ENNReal.add_halves]
  -- back to real numbers
  have hRXf : RX ≠ ⊤ := (restrictedVolume_lt_top hι F.omega Θ).ne
  have hREf : RE ≠ ⊤ := (restrictedVolume_lt_top hιE ωE Θ).ne
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  rw [hRXc, hREc, ← ENNReal.toReal_add hRXf hREf]
  calc (RX + RE).toReal ≤ (ENNReal.ofReal V).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hmain
    _ = V := ENNReal.toReal_ofReal hV0

end SGPT.Okounkov.TranscendentalWN
