import SGPT.NPP.LogConcavityDivisorRemoval
import SGPT.NPP.LogConcavityBounded
import SGPT.Foundations.Analysis.Pending.DominationLogResolution
import SGPT.Foundations.Analysis.Pending.MeteredDivisorOperations
import SGPT.Foundations.Analysis.Pending.AnalyticTypeRestriction
import SGPT.Foundations.Analysis.Pending.HironakaChowLemma
import SGPT.Foundations.Analysis.Pending.AnalyticModificationMixedMass
import SGPT.Foundations.Analysis.Pending.AnalyticModificationComposition
import SGPT.Foundations.Analysis.Pending.PrescribedBlowupDomination
import SGPT.Foundations.Analysis.Pending.BlowupSequenceTotalTransform

/-!
# Log-concavity of mixed masses: potentials with analytic singularities

Source `thm:logconc`, second assertion, for closed positive currents `Tᵢ = θᵢ + ddᶜφᵢ` whose
potentials have analytic singularities (TN `HasAnalyticSingularities`: globally
`φ = c log ∑|gⱼ|² + O(1)` for a coherent ideal and `c ∈ ℚ_{>0}`):

`∫_X ⟨T₁ ∧ ⋯ ∧ Tₙ⟩ ≥ ∏ᵢ (∫_X ⟨Tᵢⁿ⟩)^{1/n}`.

## Proof

A *common log resolution*: iterating TN's log resolution
(`DominationLogResolution.exists_logResolution`, principalization by blowups with smooth
centres) and pulling back the divisors (`MeteredDivisorOperations.pullback`), there is one
blowup sequence `π : Y → X` with `φᵢ ∘ π = ψ_{Fᵢ} + rᵢ` for metered effective `ℚ`-divisors
`Fᵢ`, where `rᵢ` agrees off `Supp Fᵢ` with a bounded `(π^*θᵢ - Θ_{Fᵢ})`-psh function `bᵢ`. Mixed
masses are invariant under blowups (TN `ActualMixedMassModification`), the divisors can be
removed (`globalMixedMeasure_univ_sub_curvature_eq`), and the remaining masses of bounded
potentials are intersection numbers of nef classes, to which the Khovanskii–Teissier
inequality applies (`prod_slotIntegral_rpow_le_slotIntegral_of_nef`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Manifold ContDiff ENNReal

universe u

namespace SGPT.NPP.LogConcavity

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open FirstPass.PositiveClasses FirstPass.HolomorphicIdealSheaves
  FirstPass.GlobalAnalyticSingularities FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending
open Pending.GlobalNonPluripolar Pending.MixedMass Pending.BoundedGlobalProduct
open Pending.AnalyticModificationLocalDiscrepancy

/-! ### Log-resolution data -/

section Data

variable {k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel k) X]
  [IsComplexManifold k X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel k) Y]
  [IsComplexManifold k Y]

/-- `π : Y → X` *log-resolves* the `θ`-psh function `φ`: `φ ∘ π = ψ_F + r` for a metered
effective `ℚ`-divisor `F` on `Y`, where `r` agrees off `Supp F` with a bounded
`(π^*θ - Θ_F)`-psh function `b`. -/
def LogResolves (π : Y → X) (hπ : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel k) ∞ π)
    (θ : ClosedRealOneOneForm k X) (φ : X → EReal) : Prop :=
  ∃ (F : MeteredEffectiveQDivisor k Y) (r : Y → ℝ) (b : Y → EReal),
    (∀ y, φ (π y) = F.weight y + (r y : EReal)) ∧
    ThetaPlurisubharmonic (ClosedRealOneOneForm.pullback hπ θ - F.curvature).val b ∧
    IsBoundedPotential b ∧
    (∀ y, y ∉ F.support → b y = (r y : EReal))

/-- Geometric equality is compatible with subtraction. -/
theorem geometricallyEq_sub_left {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel k) M] [IsComplexManifold k M]
    {a a' : ClosedRealOneOneForm k M} (h : a.val.GeometricallyEq a'.val)
    (c : ClosedRealOneOneForm k M) : (a - c).val.GeometricallyEq (a' - c).val := by
  intro e z hz
  rw [BlowupBigPullback.coeff_sub, BlowupBigPullback.coeff_sub, h e hz]

variable {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel k) Z]
  [IsComplexManifold k Z]

/-- Log-resolution data pull back along a further blowup sequence. -/
theorem LogResolves.comp {π : Y → X}
    {hπ : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel k) ∞ π}
    {θ : ClosedRealOneOneForm k X} {φ : X → EReal} (h : LogResolves π hπ θ φ)
    {g : Z → Y} (hg : IsBlowupSequence k Y Z g) :
    LogResolves (π ∘ g) (hπ.comp hg.contMDiff) θ φ := by
  obtain ⟨F, r, b, hw, hb, hbb, hoff⟩ := h
  have hint := BlowupSequenceTotalTransform.interior_exceptionalLocus_eq_empty_of_isBlowupSequence hg
  refine ⟨MeteredDivisorOperations.pullback hg.contMDiff hint F, fun z => r (g z),
    fun z => b (g z), fun z => hw (g z), ?_, ?_, ?_⟩
  · have h1 := GlobalPotentialPullback.thetaPlurisubharmonic_comp hg.contMDiff hb
    refine BlowupBigPullback.thetaPlurisubharmonic_of_geometricallyEq ?_ h1
    have h2 := BlowupBigPullback.pullback_sub_geometricallyEq hg.contMDiff
      (ClosedRealOneOneForm.pullback hπ θ) F.curvature
    refine h2.trans (geometricallyEq_sub_left ?_ _)
    exact (SmoothRealForm.pullback_comp_geometricallyEq hπ hg.contMDiff θ.val).symm
  · obtain ⟨a, c, hac⟩ := hbb
    exact ⟨a, c, fun z => hac (g z)⟩
  · intro z hz
    exact hoff (g z) hz

/-- Log-resolution data of a pulled-back potential are log-resolution data downstairs. -/
theorem LogResolves.of_pullback {π : Y → X} (hπ : IsBlowupSequence k X Y π)
    {θ : ClosedRealOneOneForm k X} {φ : X → EReal} {ρ : Z → Y}
    {hρ : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel k) ∞ ρ}
    (h : LogResolves ρ hρ (ClosedRealOneOneForm.pullback hπ.contMDiff θ) (fun y => φ (π y))) :
    LogResolves (π ∘ ρ) (hπ.contMDiff.comp hρ) θ φ := by
  obtain ⟨F, r, b, hw, hb, hbb, hoff⟩ := h
  refine ⟨F, r, b, fun z => hw z, ?_, hbb, hoff⟩
  refine BlowupBigPullback.thetaPlurisubharmonic_of_geometricallyEq ?_ hb
  refine geometricallyEq_sub_left ?_ _
  exact (SmoothRealForm.pullback_comp_geometricallyEq hπ.contMDiff hρ θ.val).symm

end Data

/-! ### Blowup sequences are analytic modifications -/

section Modification

variable {k : ℕ}

theorem isAnalyticModification_id' {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel k) X] [IsComplexManifold k X] :
    IsAnalyticModification (n := k) (id : X → X) := by
  refine ⟨contMDiff_id, isProperMap_id, ∅, ∅, id,
    isClosed_empty, isComplexAnalyticSubset_empty, ?_,
    isClosed_empty, isComplexAnalyticSubset_empty, ?_, ?_,
    contMDiff_id.contMDiffOn, fun _ _ => rfl, fun _ _ => rfl⟩ <;> simp

theorem isAnalyticModification_of_isBlowupSequence' {X Y : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel k) X] [IsComplexManifold k X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel k) Y] [IsComplexManifold k Y]
    {π : Y → X} (hπ : IsBlowupSequence k X Y π) :
    IsAnalyticModification (n := k) π := by
  induction hπ with
  | refl => exact isAnalyticModification_id'
  | step f C b _ hb ih =>
      exact AnalyticModificationComposition.isAnalyticModification_comp ih
        (PrescribedBlowupDomination.isAnalyticModification_of_isBlowupAlong hb)

end Modification

/-! ### A common log resolution -/

section Common

variable {k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel k) X]
  [IsComplexManifold k X] [CompactSpace X] [ConnectedSpace X]

/-- The pullback of a potential along a blowup sequence is a potential. -/
theorem isThetaPshPotential_comp_of_isBlowupSequence {Y : Type u} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel k) Y] [IsComplexManifold k Y] [ConnectedSpace Y]
    {π : Y → X} (hπ : IsBlowupSequence k X Y π) {θ : ClosedRealOneOneForm k X} {φ : X → EReal}
    (hφ : IsThetaPshPotential θ.val φ) :
    IsThetaPshPotential (ClosedRealOneOneForm.pullback hπ.contMDiff θ).val (fun y => φ (π y)) := by
  have hsurj := (StrictTransformComposition.IsBlowupSequence.compactSpace_surjective hπ).2
  obtain ⟨x₀⟩ : Nonempty X := by
    by_contra h
    exact (not_nonempty_iff.mp h).elim (ConnectedSpace.toNonempty.some)
  obtain ⟨x, -, hx⟩ := hφ.2 x₀ univ isOpen_univ (mem_univ x₀)
  obtain ⟨y₀, hy₀⟩ := hsurj x
  have hpsh := GlobalPotentialPullback.thetaPlurisubharmonic_comp hπ.contMDiff hφ.1
  exact ⟨hpsh, ThetaPshIdentityPrinciple.locallyNondegenerate_of_exists_ne_bot hpsh
    ⟨y₀, by simp only [hy₀]; exact hx⟩⟩

/-- **A common log resolution** of finitely many potentials with analytic singularities on a
compact connected Kähler manifold of positive dimension. -/
theorem exists_common_logResolution (hk : 0 < k) (ω0 : KahlerBackground k X) :
    ∀ (m : ℕ) (θ : Fin m → ClosedRealOneOneForm k X) (φ : Fin m → X → EReal),
      (∀ i, IsThetaPshPotential (θ i).val (φ i)) → (∀ i, HasAnalyticSingularities (n := k) (φ i)) →
      ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : ChartedSpace (ComplexModel k) Y)
        (_ : IsComplexManifold k Y) (π : Y → X) (hπ : IsBlowupSequence k X Y π),
        CompactSpace Y ∧ ConnectedSpace Y ∧ Nonempty (KahlerBackground k Y) ∧
        ∀ i, LogResolves π hπ.contMDiff (θ i) (φ i)
  | 0, _, _, _, _ =>
      ⟨X, inferInstance, inferInstance, inferInstance, id, IsBlowupSequence.refl, inferInstance,
        inferInstance, ⟨ω0⟩, fun i => i.elim0⟩
  | m + 1, θ, φ, hφ, han => by
      obtain ⟨Y, tY, cY, mY, π, hπ, hYc, hYconn, ⟨ωY⟩, hres⟩ :=
        exists_common_logResolution hk ω0 m (fun i => θ i.castSucc) (fun i => φ i.castSucc)
          (fun i => hφ i.castSucc) (fun i => han i.castSucc)
      obtain ⟨c, 𝔞, htype⟩ := han (Fin.last m)
      have hpot := isThetaPshPotential_comp_of_isBlowupSequence hπ (hφ (Fin.last m))
      have htype' := AnalyticTypeRestriction.hasAnalyticSingularitiesOfType_comp hπ.contMDiff htype
      obtain ⟨Z, tZ, cZ, mZ, ρ, hρ, hZc, hZconn, hZK, F, L, b, hb, hblow, hbupp, hboff, -⟩ :=
        DominationLogResolution.exists_logResolution hk ωY
          (ClosedRealOneOneForm.pullback hπ.contMDiff (θ (Fin.last m))) hpot htype'
      refine ⟨Z, tZ, cZ, mZ, π ∘ ρ, HironakaChowLemma.isBlowupSequence_comp hπ hρ, hZc, hZconn,
        hZK, fun i => ?_⟩
      refine Fin.lastCases ?_ (fun j => ?_) i
      · have hlast : LogResolves ρ hρ.contMDiff
            (ClosedRealOneOneForm.pullback hπ.contMDiff (θ (Fin.last m)))
            (fun y => φ (Fin.last m) (π y)) :=
          ⟨F, L.residual, b, L.weight_add, hb.1, ⟨-L.bound, L.bound, fun z => ⟨hblow z, hbupp z⟩⟩,
            hboff⟩
        exact hlast.of_pullback hπ
      · exact (hres j).comp hρ

end Common

/-! ### The inequality -/

section Inequality

variable {q : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel (q + 1)) X]
  [IsComplexManifold (q + 1) X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
  [ConnectedSpace X]

omit [ConnectedSpace X] in
/-- On a log resolution the mixed mass of the pulled-back potentials is an intersection number
of nef classes. -/
theorem globalMixedMass_toReal_eq_slotIntegral_of_logResolves
    {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel (q + 1)) Y]
    [IsComplexManifold (q + 1) Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]
    (ωY : KahlerBackground (q + 1) Y) {π : Y → X} (hπ : IsBlowupSequence (q + 1) X Y π)
    {θ : Fin (q + 1) → ClosedRealOneOneForm (q + 1) X} {φ : Fin (q + 1) → X → EReal}
    (hφ : ∀ i, IsThetaPshPotential (θ i).val (φ i))
    (hpot : ∀ i, IsThetaPshPotential (ClosedRealOneOneForm.pullback hπ.contMDiff (θ i)).val
      (fun y => φ i (π y)))
    (F : Fin (q + 1) → MeteredEffectiveQDivisor (q + 1) Y) (r : Fin (q + 1) → Y → ℝ)
    (b : Fin (q + 1) → Y → EReal)
    (hw : ∀ i y, φ i (π y) = (F i).weight y + (r i y : EReal))
    (hb : ∀ i, ThetaPlurisubharmonic
      (ClosedRealOneOneForm.pullback hπ.contMDiff (θ i) - (F i).curvature).val (b i))
    (hbb : ∀ i, IsBoundedPotential (b i))
    (hoff : ∀ i y, y ∉ (F i).support → b i y = (r i y : EReal)) :
    (globalMixedMass θ φ (fun i => (hφ i).1)).toReal =
      NefMixedMass.slotIntegral ωY
        (fun i => ClosedRealOneOneForm.pullback hπ.contMDiff (θ i) - (F i).curvature) := by
  have hmod := AnalyticModificationMixedMass.globalMixedMeasure_univ_pullback_of_isAnalyticModification
    (isAnalyticModification_of_isBlowupSequence' hπ) (θ := θ) (fun i => (hφ i).1)
  have hFnd : ∀ i, LocallyNondegenerate (F i).weight := by
    intro i y U hU hyU
    obtain ⟨y', hy'U, hy'⟩ := (hpot i).2 y U hU hyU
    refine ⟨y', hy'U, fun hbot => hy' ?_⟩
    change φ i (π y') = ⊥
    rw [hw i y', hbot, EReal.bot_add]
  have hheq : ∀ i y, y ∉ (F i).support → φ i (π y) = (F i).weight y + b i y := by
    intro i y hy
    rw [hw i y, hoff i y hy]
  have hrem := globalMixedMeasure_univ_sub_curvature_eq
    (fun i => ClosedRealOneOneForm.pullback hπ.contMDiff (θ i)) F
    (w := fun i y => φ i (π y)) (fun i => (hpot i).1) hb hheq hFnd
  have hbdd := DominationIntersectionNumbers.globalMixedMass_toReal_eq_slotIntegral_of_isBoundedPotential
    ωY hb hbb
  rw [← hbdd]
  unfold globalMixedMass
  rw [hrem, ← hmod]

/-- **`thm:logconc`, mixed-mass inequality, analytic singularities** (TN-native form). On a
compact connected Kähler manifold of dimension `n = q + 1`, for `θᵢ`-psh potentials `φᵢ` with
analytic singularities,
`∏ᵢ (∫ ⟨(θᵢ + ddᶜφᵢ)ⁿ⟩)^{1/n} ≤ ∫ ⟨(θ₁ + ddᶜφ₁) ∧ ⋯ ∧ (θₙ + ddᶜφₙ)⟩`. -/
theorem prod_globalMixedMass_rpow_le_of_analytic (ω0 : KahlerBackground (q + 1) X)
    (θ : Fin (q + 1) → ClosedRealOneOneForm (q + 1) X) (φ : Fin (q + 1) → X → EReal)
    (hφ : ∀ i, IsThetaPshPotential (θ i).val (φ i))
    (han : ∀ i, HasAnalyticSingularities (n := q + 1) (φ i)) :
    ∏ i, (globalMixedMass (fun _ => θ i) (fun _ => φ i) (fun _ => (hφ i).1)).toReal ^
        (((q + 1 : ℕ) : ℝ)⁻¹) ≤
      (globalMixedMass θ φ (fun i => (hφ i).1)).toReal := by
  obtain ⟨Y, tY, cY, mY, π, hπ, hYc, hYconn, ⟨ωY⟩, hres⟩ :=
    exists_common_logResolution (Nat.succ_pos q) ω0 (q + 1) θ φ hφ han
  let : MeasurableSpace Y := borel Y
  have : BorelSpace Y := ⟨rfl⟩
  choose F r b hw hb hbb hoff using hres
  have hpot : ∀ i, IsThetaPshPotential (ClosedRealOneOneForm.pullback hπ.contMDiff (θ i)).val
      (fun y => φ i (π y)) := fun i => isThetaPshPotential_comp_of_isBlowupSequence hπ (hφ i)
  have hmixed := globalMixedMass_toReal_eq_slotIntegral_of_logResolves ωY hπ hφ hpot F r b hw hb
    hbb hoff
  have hpure : ∀ i, (globalMixedMass (fun _ => θ i) (fun _ => φ i) (fun _ => (hφ i).1)).toReal =
      NefMixedMass.slotIntegral ωY
        (fun _ => ClosedRealOneOneForm.pullback hπ.contMDiff (θ i) - (F i).curvature) := fun i =>
    globalMixedMass_toReal_eq_slotIntegral_of_logResolves ωY hπ (fun _ => hφ i) (fun _ => hpot i)
      (fun _ => F i) (fun _ => r i) (fun _ => b i) (fun _ => hw i) (fun _ => hb i)
      (fun _ => hbb i) (fun _ => hoff i)
  simp_rw [hmixed, hpure]
  exact prod_slotIntegral_rpow_le_slotIntegral_of_nef ωY _ fun i =>
    DominationIntersectionNumbers.nefWithRespectTo_of_isBoundedPotential ωY (hb i) (hbb i)

end Inequality

/-! ### The source form -/

section Source

open SGPT.PSH.VariableComplexAtlas

variable {q : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel (q + 1)) M]
  [IsComplexManifold (q + 1) M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  [ConnectedSpace M]

/-- **`thm:logconc`, mixed-mass inequality, analytic singularities.** On a compact connected
Kähler manifold of dimension `n = q + 1`, for closed real `(1,1)`-forms `θᵢ` and `θᵢ`-psh
functions `uᵢ` with analytic singularities,
`∏ᵢ (∫ ⟨(θᵢ + ddᶜuᵢ)ⁿ⟩)^{1/n} ≤ ∫ ⟨(θ₁ + ddᶜu₁) ∧ ⋯ ∧ (θₙ + ddᶜuₙ)⟩`
for the source non-pluripolar masses (all finite, read as real numbers). -/
theorem prod_sourceMass_rpow_le_sourceMixedMass_of_analytic (ω0 : KahlerBackground (q + 1) M)
    (θ : Fin (q + 1) → AtlasClosedRealOneOneForm (ofFixedModel (q + 1) M))
    (u : Fin (q + 1) → M → EReal) (hu : ∀ i, (ofFixedModel (q + 1) M).IsThetaPSH (θ i) (u i))
    (han : ∀ i, HasAnalyticSingularities (n := q + 1) (u i)) :
    ∏ i, ((sourceMixedNonPluripolarMass (fun _ => θ i) (fun _ => u i) (fun _ => hu i)).toReal) ^
        (((q + 1 : ℕ) : ℝ)⁻¹) ≤
      (sourceMixedNonPluripolarMass θ u hu).toReal := by
  have hφ : ∀ i, IsThetaPshPotential (atlasClosedFormToNative (θ i)).val (u i) := fun i =>
    (isThetaPSH_iff_nativeThetaPotential (θ i) (u i)).mp (hu i)
  have h := prod_globalMixedMass_rpow_le_of_analytic ω0 (fun i => atlasClosedFormToNative (θ i))
    u hφ han
  simp only [sourceMixedNonPluripolarMass_eq_native]
  exact h

end Source

end SGPT.NPP.LogConcavity
