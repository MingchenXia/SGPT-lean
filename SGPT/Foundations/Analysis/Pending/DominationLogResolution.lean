import SGPT.Foundations.Analysis.Pending.ResidualNef
import SGPT.Foundations.Analysis.Pending.RelativePrincipalization
import SGPT.Foundations.Analysis.Pending.StepFourLogSingularities
import SGPT.Foundations.Analysis.Pending.IdealComparisonResidual
import SGPT.Foundations.Analysis.Pending.GlobalPotentialPullback
import SGPT.Foundations.Analysis.Pending.ThetaPshIdentityPrinciple
import SGPT.Foundations.Analysis.Pending.BlowupKahler
import SGPT.Foundations.Analysis.Pending.AnalyticTypeRestriction

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# `lem:domination`, Step 2: the log resolution of an approximant and the nef residual class

Source: Copy-4, `lem:domination`, Step 2
(`references/transcendental-nakamaye-copy4-20260911/source/main-Nulllocus.tex:700-712`):

> Let `ρ_j : Z_j → Z` be a log resolution of `v_j`, and write the Siu decomposition of the
> pullback as `ρ_j^*((γ_j)_{v_j}) = R_j + [F_j]`, where `F_j` is an effective `ℚ`-divisor and
> `R_j` is a closed positive current with locally bounded potentials.  Put `A_j := {R_j}`.  The
> class `A_j` is nef by `lem:residual-nef`.

Plan: `scratch/tn23-envelopes-qea-plan-0117.md` §7, steps 2a–2b (positive-current programme,
I-0752).

## What is proved

`exists_logResolution`: on a compact connected Kähler manifold `Z` of positive dimension, a
`θ`-psh potential `φ` with analytic singularities of type `(c, 𝔞)` has

* a blowup sequence `ρ : Z' → Z`, with `Z'` compact, connected and Kähler;
* a metered effective `ℚ`-divisor `F` on `Z'` along which `φ ∘ ρ` has log singularities:
  `φ ∘ ρ = ψ_F + b` everywhere, `b` real and bounded (`HasLogSingularitiesAlong`);
* a globally `(ρ^*θ - Θ_F)`-psh potential `b*`, with the same bounds as `b`, equal to `b` off
  `Supp F` — the potential of `R = ρ^*θ - Θ_F + ddᶜ b*`, so that
  `ρ^*θ + ddᶜ(φ ∘ ρ) = R + [F]` (Siu decomposition, `Θ_F + ddᶜψ_F = [F]`);
* `{ρ^*θ} - {F}` nef with respect to EVERY Kähler background of `Z'` (`lem:residual-nef`).

The modification is the existing Hironaka-type named statement
`RelativePrincipalization.exists_factorizationData`, used AS GIVEN with `W` a
point off the poles of `φ`: it makes `𝔞 𝒪_{Z'} = 𝒪(-H-H')` invertible, and no SNC condition is
needed for the decomposition.  `F = c(H + H')` with a smooth metric on `H` and on `H'`
(`DivisorMetric`).  The log singularities are the comparison of two weights of the same type
`(c, 𝔞𝒪_{Z'})` on a compact manifold (`IdealWeightComparison`).  `b*` is the upper regularization
of the residual across the proper analytic set `Supp F` (CADG I.5.24, proved in the tree), as in
`ResidualNef`, which also supplies nefness.

Sorry-free, and so is its closure: `exists_factorizationData` (Hironaka), once the only unproved
input in it, is proved in place from the canonical resolution invariant.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace SGPT.Foundations.Analysis.Pending.DominationLogResolution

open FirstPass FirstPass.PositiveClasses FirstPass.HolomorphicIdealSheaves
  FirstPass.GlobalAnalyticSingularities FirstPass.BlowupSequences
  FirstPass.NumericalRestrictedVolumeScaffold
  ThetaPshCodimTwoExtension PshAnalyticSetExtension ResidualNefReduction
  PshRemovableSingularity

noncomputable section

/-! ### A point is a closed connected submanifold of dimension `0` -/

section Point

variable {k : ℕ} {Z : Type*} [TopologicalSpace Z] [ChartedSpace (ComplexModel k) Z]
  [IsComplexManifold k Z]

/-- **A point is a closed connected complex submanifold of dimension `0`**: in the preferred
chart at `x`, the translation `z ↦ z - e(x)` flattens `{x}` to the origin
`= complexCoordinatePlane k 0`. -/
theorem isClosedConnectedSubmanifold_singleton (x : Z) :
    IsClosedConnectedSubmanifold k ({x} : Set Z) 0 := by
  refine ⟨isClosed_singleton, isConnected_singleton, fun y hy => ?_⟩
  rw [mem_singleton_iff] at hy
  subst hy
  set e := complexChartAt (n := k) y with he
  set a : ComplexModel k := e.val y with ha
  let Φ : LocalHolomorphicEquivAt (n := k) a :=
    { source := e.val.target
      target := (fun w => w + a) ⁻¹' e.val.target
      isOpen_source := e.val.open_target
      isOpen_target := e.val.open_target.preimage (continuous_add_const a)
      center_mem_source := e.val.map_source (mem_complexChartAt_source y)
      toFun := fun z => z - a
      invFun := fun w => w + a
      toFun_holomorphic := differentiableOn_id.sub_const a
      invFun_holomorphic := differentiableOn_id.add_const a
      mapsTo_toFun := fun z hz => by simpa only [mem_preimage, sub_add_cancel] using hz
      mapsTo_invFun := fun w hw => hw
      left_inv := fun z _ => sub_add_cancel z a
      right_inv := fun w _ => add_sub_cancel_right w a }
  refine ⟨Nat.zero_le k, mem_singleton y, Φ, subset_rfl, sub_self a, ?_⟩
  intro z hz _
  have hplane : ∀ w : ComplexModel k, w ∈ complexCoordinatePlane k 0 ↔ w = 0 := by
    intro w
    constructor
    · intro hw
      ext i
      simpa using hw i (Nat.zero_le _)
    · rintro rfl i _
      rfl
  change z ∈ ({y} : Set Z) ↔ e.val z - a ∈ complexCoordinatePlane k 0
  rw [hplane, sub_eq_zero, mem_singleton_iff]
  constructor
  · rintro rfl
    rfl
  · intro hza
    exact e.val.injOn hz (mem_complexChartAt_source y) hza

/-- On a nonempty manifold of positive dimension a point is not everything. -/
theorem singleton_ne_univ (hk : 0 < k) (x : Z) : ({x} : Set Z) ≠ univ := by
  intro hx
  set e := complexChartAt (n := k) x
  have hxt : e.val x ∈ e.val.target := e.val.map_source (mem_complexChartAt_source x)
  have : Nontrivial (ComplexModel k) := by
    have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    infer_instance
  obtain ⟨w, hwt, hwne⟩ : ∃ w ∈ e.val.target, w ≠ e.val x := by
    have hev : ∀ᶠ w in 𝓝[≠] (e.val x), w ∈ e.val.target :=
      nhdsWithin_le_nhds (e.val.open_target.mem_nhds hxt)
    obtain ⟨w, hw, hwne⟩ := (hev.and self_mem_nhdsWithin).exists
    exact ⟨w, hw, hwne⟩
  have hmem : e.val.symm w ∈ ({x} : Set Z) := hx ▸ mem_univ _
  rw [mem_singleton_iff] at hmem
  apply hwne
  rw [← hmem, e.val.right_inv hwt]

end Point

/-! ### The regularized residual -/

section Residual

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **The bounded potential of the residual current `R = θ - Θ_D + ddᶜb*`.**  If `φ` is `θ`-psh
with log singularities along `D` and `Supp D ≠ M`, the upper regularization `b*` of the residual
across `Supp D` is a globally `(θ - Θ_D)`-psh potential, bounded by the residual's bound, and
equal to the residual off `Supp D`.  This is parts 1–2 of `ResidualNef` (reduction and CADG
I.5.24), exported. -/
theorem exists_regularizedResidual [CompactSpace M] [ConnectedSpace M]
    {theta : ClosedRealOneOneForm n M} {D : MeteredEffectiveQDivisor n M} {phi : M → EReal}
    (hphi : ThetaPlurisubharmonic theta.val phi) (L : HasLogSingularitiesAlong D phi)
    (hproper : D.support ≠ univ) :
    ∃ b : M → EReal, IsThetaPshPotential (theta - D.curvature).val b ∧
      (∀ x, ((-L.bound : ℝ) : EReal) ≤ b x) ∧ (∀ x, b x ≤ (L.bound : EReal)) ∧
      ∀ x, x ∉ D.support → b x = (L.residual x : EReal) := by
  classical
  set A : Set M := D.support with hAdef
  set r : M → EReal := fun x => (L.residual x : EReal) with hrdef
  have hoff : ThetaPshOff (theta - D.curvature).val A r := thetaPshOff_residual hphi L
  have hbound : LocallyBoundedAboveOff A r := L.locallyBoundedAboveOff
  have hanalytic : IsComplexAnalyticSubset (n := n) A := ResidualNef.isComplexAnalyticSubset_support D
  have hthetaPot : HasSmoothLocalPotentials (theta - D.curvature).val :=
    ResidualNef.hasSmoothLocalPotentials_sub hphi.hasSmoothLocalPotentials
      (ResidualNef.hasSmoothLocalPotentials_curvature D)
  have hext : ThetaPlurisubharmonic (theta - D.curvature).val (extensionAcross A r) :=
    thetaPlurisubharmonic_extensionAcross_of_analyticRemovable
      (demaillyCadgI524_analyticRemovableThetaPsh _ hthetaPot A r)
      hanalytic hproper hoff hbound
  have hAint : interior A = ∅ :=
    IsComplexAnalyticSubset.interior_eq_empty_of_ne_univ hanalytic hproper
  have hupp : ∀ x, extensionAcross A r x ≤ (L.bound : EReal) :=
    ResidualNef.extensionAcross_le_of_forall_le
      (fun y => EReal.coe_le_coe_iff.mpr (L.le_bound y))
  have hlow : ∀ x, ((-L.bound : ℝ) : EReal) ≤ extensionAcross A r x :=
    ResidualNef.le_extensionAcross_of_interior_eq_empty hAint
      (fun y => EReal.coe_le_coe_iff.mpr (L.neg_bound_le y))
  refine ⟨extensionAcross A r, ⟨hext, fun x U _ hxU => ⟨x, hxU, ?_⟩⟩, hlow, hupp,
    fun x hx => extensionAcross_eq_of_notMem hanalytic.isClosed hoff hx⟩
  exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (hlow x)

end Residual

/-! ### Kähler and compact along a blowup sequence -/

section Sequence

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [CompactSpace X]

/-- A blowup sequence of a compact Kähler manifold is compact Kähler (Blanchard, by
induction). -/
theorem compactSpace_and_kahler_of_isBlowupSequence (hK : Nonempty (KahlerBackground n X))
    {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    {f : Y → X} (hf : IsBlowupSequence n X Y f) :
    CompactSpace Y ∧ Nonempty (KahlerBackground n Y) := by
  induction hf with
  | refl => exact ⟨inferInstance, hK⟩
  | step f C g _ hg ih =>
      obtain ⟨hc, hk⟩ := ih
      have := hc
      exact BlowupKahler.compactSpace_and_kahler_of_isBlowupAlong hk hg

end Sequence

/-! ### The log resolution -/

section LogResolution

variable {k : ℕ} {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel k) Z]
  [IsComplexManifold k Z] [CompactSpace Z] [ConnectedSpace Z]

/-- **Copy-4 `lem:domination`, Steps 2a–2b: log resolution, Siu decomposition, nef residual
class.**  On a compact connected Kähler manifold `Z` of positive dimension, a `θ`-psh potential
`φ` with analytic singularities of type `(c, 𝔞)` admits a blowup sequence `ρ : Z' → Z` (`Z'`
compact, connected, Kähler) and a metered effective `ℚ`-divisor `F` on `Z'` such that

* `φ ∘ ρ` has log singularities along `F` (`φ ∘ ρ = ψ_F + b`, `|b| ≤ L.bound`, everywhere);
* `b* ` is a `(ρ^*θ - Θ_F)`-psh potential with `-L.bound ≤ b* ≤ L.bound`, `b* = b` off `Supp F`
  (the bounded potential of `R = ρ^*θ - Θ_F + ddᶜb*`, `ρ^*(θ_φ) = R + [F]`);
* `{ρ^*θ} - {F}` is nef with respect to every Kähler background of `Z'`.

`ρ` comes from `RelativePrincipalization.exists_factorizationData` (Hironaka-type, used as given,
`W` a point off the poles of `φ`). -/
theorem exists_logResolution (hk : 0 < k) (omegaZ : KahlerBackground k Z)
    (θ : ClosedRealOneOneForm k Z) {φ : Z → EReal} (hφ : IsThetaPshPotential θ.val φ)
    {c : ℚ} {𝔞 : GermIdeal k Z} (htype : HasAnalyticSingularitiesOfType (n := k) φ c 𝔞) :
    ∃ (Z' : Type u) (_ : TopologicalSpace Z') (_ : ChartedSpace (ComplexModel k) Z')
      (_ : IsComplexManifold k Z') (ρ : Z' → Z) (hρ : IsBlowupSequence k Z Z' ρ),
      CompactSpace Z' ∧ ConnectedSpace Z' ∧ Nonempty (KahlerBackground k Z') ∧
      ∃ (F : MeteredEffectiveQDivisor k Z') (L : HasLogSingularitiesAlong F (fun y => φ (ρ y)))
        (b : Z' → EReal),
        IsThetaPshPotential (ClosedRealOneOneForm.pullback hρ.contMDiff θ - F.curvature).val b ∧
        (∀ y, ((-L.bound : ℝ) : EReal) ≤ b y) ∧ (∀ y, b y ≤ (L.bound : EReal)) ∧
        (∀ y, y ∉ F.support → b y = (L.residual y : EReal)) ∧
        ∀ omega' : KahlerBackground k Z',
          NefWithRespectTo omega' (ClosedRealOneOneForm.pullback hρ.contMDiff θ - F.curvature) := by
  classical
  -- a point off the poles of `φ`
  obtain ⟨x₀⟩ : Nonempty Z := inferInstance
  obtain ⟨x, -, hx⟩ := hφ.2 x₀ univ isOpen_univ (mem_univ x₀)
  have hres : ¬ 𝔞.Le (vanishingIdeal (n := k) ({x} : Set Z)) :=
    RelativePrincipalization.analyticSingularityType_not_le_vanishingIdeal_of_not_pole htype
      (mem_singleton x) hx
  -- the modification (Hironaka-type named statement, used as given)
  obtain ⟨Z', tZ', cZ', mZ', ρ, hadapt, -, -, H, H', -, -, -, hideal⟩ :=
    RelativePrincipalization.exists_factorizationData ({x} : Set Z) 0
      (isClosedConnectedSubmanifold_singleton x) (singleton_ne_univ hk x) 𝔞 htype.2.1 hres
  have hρ : IsBlowupSequence k Z Z' ρ := hadapt.isBlowupSequence
  obtain ⟨hcpt, hK⟩ := compactSpace_and_kahler_of_isBlowupSequence ⟨omegaZ⟩ hρ
  have := hcpt
  have : ConnectedSpace Z' := BlowupConnected.connectedSpace_of_isBlowupSequence ρ hρ
  have hsurj : Function.Surjective ρ :=
    (StrictTransformComposition.IsBlowupSequence.compactSpace_surjective hρ).2
  -- the divisor `F = c (H + H')` with smooth metrics
  obtain ⟨EH, -, hEH⟩ := DivisorMetric.exists_divisorMetric H
  obtain ⟨EH', -, hEH'⟩ := DivisorMetric.exists_divisorMetric H'
  have hc0 : (0 : ℚ) ≤ c := htype.1.le
  set F : MeteredEffectiveQDivisor k Z' :=
    MeteredDivisorScaling.smul hc0 (MeteredDivisorOperations.add EH EH') with hFdef
  have hFtype : HasAnalyticSingularitiesOfType (n := k) F.weight c (H.ideal.mul H'.ideal) := by
    have h1 := IdealWeightPowers.hasAnalyticSingularitiesOfType_mul
      (DivisorMetric.hasAnalyticSingularitiesOfType_of_isDivisorMetric hEH)
      (DivisorMetric.hasAnalyticSingularitiesOfType_of_isDivisorMetric hEH')
    have h2 := IdealComparisonResidual.hasAnalyticSingularitiesOfType_smul htype.1 h1
    rw [mul_one] at h2
    exact h2
  -- `φ ∘ ρ` has the same type
  have hφρ : HasAnalyticSingularitiesOfType (n := k) (φ ∘ ρ) c (H.ideal.mul H'.ideal) := by
    rw [← hideal]
    exact AnalyticTypeRestriction.hasAnalyticSingularitiesOfType_comp hρ.contMDiff htype
  have hsame : SameSingularityTypeOn (fun y => φ (ρ y)) F.weight univ :=
    IdealWeightComparison.sameSingularityTypeOn_univ_of_eq_type hφρ hFtype
  let L : HasLogSingularitiesAlong F (fun y => φ (ρ y)) :=
    StepFourLogSingularities.logSingularitiesOfSameSingularityType F hsame
      (StepFourLogSingularities.weight_ne_top F)
  -- `ρ^*θ`-plurisubharmonicity and nondegeneracy of `φ ∘ ρ`
  have hpshρ : ThetaPlurisubharmonic (ClosedRealOneOneForm.pullback hρ.contMDiff θ).val
      (fun y => φ (ρ y)) :=
    GlobalPotentialPullback.thetaPlurisubharmonic_comp hρ.contMDiff hφ.1
  obtain ⟨y₀, hy₀⟩ := hsurj x
  have hne : ∃ y, φ (ρ y) ≠ ⊥ := ⟨y₀, by rw [hy₀]; exact hx⟩
  have hpot : IsThetaPshPotential (ClosedRealOneOneForm.pullback hρ.contMDiff θ).val
      (fun y => φ (ρ y)) :=
    ⟨hpshρ, ThetaPshIdentityPrinciple.locallyNondegenerate_of_exists_ne_bot hpshρ hne⟩
  have hproper : F.support ≠ univ := fun h =>
    L.notMem_support_of_ne_bot (hy₀ ▸ hx : φ (ρ y₀) ≠ ⊥) (h ▸ mem_univ y₀)
  obtain ⟨b, hb, hblow, hbupp, hboff⟩ := exists_regularizedResidual hpshρ L hproper
  exact ⟨Z', tZ', cZ', mZ', ρ, hρ, hcpt, inferInstance, hK, F, L, b, hb, hblow, hbupp, hboff,
    fun omega' => ResidualNef.nefWithRespectTo_sub_curvature omega' hpot L⟩

end LogResolution

end

end SGPT.Foundations.Analysis.Pending.DominationLogResolution
