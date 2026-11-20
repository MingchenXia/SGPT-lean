import SGPT.Foundations.Analysis.Pending.DominationLogResolution
import SGPT.Foundations.Analysis.Pending.ModificationMassInvariance
import SGPT.Foundations.Analysis.Pending.MeteredDivisorSmoothOffSupport
import SGPT.Foundations.Analysis.Pending.MeteredDivisorPositivity
import SGPT.Foundations.Analysis.Pending.ManifoldPluripolar

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# `lem:domination`, Step 2c: the mass of the residual current is the mass of the approximant

Source: Copy-4, `lem:domination`, Step 2, `eq:dom-Ak`
(`references/transcendental-nakamaye-copy4-20260911/source/main-Nulllocus.tex:710-722`):

> Since the non-pluripolar product puts no mass on `F_j`, Bedford–Taylor theory and
> `sec:npp` `it:invariance` give `A_j^k = ∫_{Z_j} R_j^k = ∫_{Z_j} (ρ_j^*(γ_j)_{v_j})^k
> = ∫_Z (γ_j)_{v_j}^k`.

Plan: `scratch/tn23-envelopes-qea-plan-0117.md` §7, step 2c (positive-current programme, I-0752).

## Main results

* `diagonalPotentialMass_sub_curvature_eq` — **change of representative off a divisor**: if
  `w = ψ_D + b` off `Supp D` (`w` a `θ`-psh potential, `b` a `(θ - Θ_D)`-psh potential, `ψ_D`
  nondegenerate), then `∫ (θ - Θ_D)_b^n = ∫ θ_w^n`.  Off `Supp D` the two non-pluripolar measures
  coincide patch by patch — `ψ_D` is there a smooth local potential of `-Θ_D`
  (`MeteredDivisorSmoothOffSupport`), so the corrected potentials of the two patches are literally
  equal — and `Supp D`, the pole set of the quasi-psh `ψ_D`, is pluripolar, hence charged by
  neither measure.
* `exists_logResolution_mass` — **Steps 2a–2c**: `exists_logResolution` (log resolution, Siu
  decomposition, nef residual class) together with `∫_{Z'} R^k = ∫_Z θ_φ^k`, i.e.
  `∫ (ρ^*θ - Θ_F)_{b*}^k = ∫ θ_φ^k`, from the change of representative and the invariance of
  non-pluripolar masses under blowup sequences (`ModificationMassInvariance`, Xia SGPT
  Prop 2.4.2).  It also exports that `φ ∘ ρ` is a `ρ^*θ`-psh potential (needed by Step 3).

The identification `∫ R^k = A^k` (the mass of a bounded potential is the cohomological top
power) is intersection-number API (Step 2d) and is not part of this module.

Sorry-free; the only non-proved input in the closure of `exists_logResolution_mass` is
`RelativePrincipalization.exists_factorizationData` (Hironaka, used as given).
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Manifold ContDiff ENNReal

universe u

namespace SGPT.Foundations.Analysis.Pending.DominationResidualMass

open FirstPass FirstPass.PositiveClasses FirstPass.HolomorphicIdealSheaves
  FirstPass.GlobalAnalyticSingularities FirstPass.BlowupSequences
  FirstPass.NumericalRestrictedVolumeScaffold FirstPass.GlobalPotentialPatches
  FirstPass.MixedNonPluripolar MixedNonPluripolar GlobalNonPluripolar ResidualNefReduction
  ModificationMassInvariance

noncomputable section

/-! ### Change of representative off a divisor -/

section ChangeOfRepresentative

/-- `(a + B) + (c - a) = B + c` in `EReal`, for real `a, c` and every `B`. -/
theorem coe_add_add_coe_sub (a c : ℝ) (B : EReal) :
    ((a : EReal) + B) + ((c - a : ℝ) : EReal) = B + (c : EReal) := by
  induction B using EReal.rec with
  | bot => simp
  | top => simp only [EReal.coe_add_top, EReal.top_add_coe]
  | coe t =>
      rw [← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_add]
      congr 1
      ring

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- **Off `Supp D` the two patch measures coincide.**  Near a point off the support, a patch of
`(θ - Θ_D, b)` and a patch of `(θ, w)` with the same chart and domain have literally equal
corrected potentials: the second uses the potentials of the first minus `ψ_D`, a smooth local
potential of `-Θ_D` there. -/
theorem exists_patch_pair (θ : ClosedRealOneOneForm n M) (D : MeteredEffectiveQDivisor n M)
    {w b : M → EReal} (hb : ThetaPlurisubharmonic (θ - D.curvature).val b)
    (heq : ∀ x, x ∉ D.support → w x = D.weight x + b x) (hsuppc : IsOpen D.supportᶜ)
    {x : M} (hx : x ∉ D.support) :
    ∃ (P₁ : Patch (fun _ : Fin n => θ - D.curvature) (fun _ => b))
      (P₂ : Patch (fun _ : Fin n => θ) (fun _ => w)),
      x ∈ P₁.source ∧ (P₁.source : Set M) ⊆ D.supportᶜ ∧
      (P₁.source : Set M) = P₂.source ∧ patchMeasure P₁ = patchMeasure P₂ := by
  classical
  obtain ⟨P₀, hxP₀⟩ := exists_patch_containing (fun _ : Fin n => hb) x
  set e := P₀.chart with he
  have hxe : x ∈ e.val.source := P₀.source_subset hxP₀
  obtain ⟨W, hxW, hψ⟩ :=
    MeteredDivisorSmoothOffSupport.exists_isSmoothLocalPotential_neg_curvature D hx e hxe
  set ψ : ComplexModel n → ℝ := fun ζ => (D.weight (e.val.symm ζ)).toReal with hψdef
  let V : Opens (ComplexModel n) :=
    ⟨(P₀.domain : Set (ComplexModel n)) ∩ W ∩ (e.val.target ∩ e.val.symm ⁻¹' D.supportᶜ),
      (P₀.domain.isOpen.inter hψ.1).inter (e.val.isOpen_inter_preimage_symm hsuppc)⟩
  have hVP : V ≤ P₀.domain := fun _ hζ => hζ.1.1
  have hVW : (V : Set (ComplexModel n)) ⊆ W := fun _ hζ => hζ.1.2
  let P₁ := P₀.restrict V hVP
  -- on `V`, `ψ_D ∘ e⁻¹` is the real `ψ`
  have hψeq : ∀ ζ ∈ (V : Set (ComplexModel n)), D.weight (e.val.symm ζ) = (ψ ζ : EReal) := by
    intro ζ hζ
    have hne : D.weight (e.val.symm ζ) ≠ ⊥ := hζ.2.2
    exact (EReal.coe_toReal (StepFourLogSingularities.weight_ne_top D _) hne).symm
  -- the corrected potentials agree on `V`
  have hcorr : ∀ (i : Fin n), ∀ ζ ∈ (V : Set (ComplexModel n)),
      chartFunction w e ζ + ((P₀.potential i ζ - ψ ζ : ℝ) : EReal) = P₁.corrected i ζ := by
    intro i ζ hζ
    change w (e.val.symm ζ) + _ = b (e.val.symm ζ) + _
    rw [heq _ hζ.2.2, hψeq ζ hζ, coe_add_add_coe_sub]
    rfl
  let P₂ : Patch (fun _ : Fin n => θ) (fun _ => w) :=
    { chart := e
      domain := V
      domain_le_target := fun _ hζ => hζ.2.1
      potential := fun i ζ => P₀.potential i ζ - ψ ζ
      localPotential := fun i => by
        refine ⟨V.isOpen, fun _ hζ => hζ.2.1,
          ((P₀.localPotential i).2.2.1.mono hVP).sub (hψ.2.2.1.mono hVW), fun ζ hζ => ?_⟩
        rw [smoothDDC_sub V.isOpen ((P₀.localPotential i).2.2.1.mono hVP)
            (hψ.2.2.1.mono hVW) hζ, (P₀.localPotential i).2.2.2 (hVP hζ), hψ.2.2.2 (hVW hζ),
          ← BlowupBigPullback.coeff_sub]
        congr 1
        rw [sub_neg_eq_add, sub_add_cancel]
      plurisubharmonic := fun i ζ hζ => by
        refine ((P₁.plurisubharmonic i) ζ hζ).congr ?_
        filter_upwards [V.isOpen.mem_nhds hζ] with ζ' hζ'
        exact (hcorr i ζ' hζ').symm }
  have hsrc : (P₁.source : Set M) = P₂.source := rfl
  refine ⟨P₁, P₂, ?_, ?_, hsrc, ?_⟩
  · refine (Patch.mem_source_restrict P₀ V hVP).mpr ⟨hxP₀, ⟨hxP₀.2, hxW⟩, e.val.map_source hxe, ?_⟩
    show e.val.symm (e.val x) ∈ D.supportᶜ
    rw [e.val.left_inv hxe]; exact hx
  · intro y hy
    have h := (Patch.mem_source_restrict P₀ V hVP).mp hy
    have h2 : e.val.symm (e.val y) ∈ D.supportᶜ := h.2.2.2
    rwa [e.val.left_inv (P₀.source_subset h.1)] at h2
  · ext s
    rw [show patchMeasure P₁ = P₁.pushMeasure
        (mixedTruncationLimitMeasure P₁.domain P₁.corrected P₁.plurisubharmonic) from rfl,
      show patchMeasure P₂ = P₂.pushMeasure
        (mixedTruncationLimitMeasure P₂.domain P₂.corrected P₂.plurisubharmonic) from rfl,
      Patch.pushMeasure_apply, Patch.pushMeasure_apply]
    exact congrArg (fun μ : Measure (ComplexModel n) => μ _)
      (mixedTruncationLimitMeasure_congr P₁.plurisubharmonic P₂.plurisubharmonic
        fun i ζ hζ => (hcorr i ζ hζ).symm)

/-- **Change of representative off a divisor.**  If `w = ψ_D + b` off `Supp D`, with `w` a
`θ`-psh potential, `b` a `(θ - Θ_D)`-psh potential and `ψ_D` nondegenerate, then
`∫ (θ - Θ_D)_b^n = ∫ θ_w^n`. -/
theorem diagonalPotentialMass_sub_curvature_eq (θ : ClosedRealOneOneForm n M)
    (D : MeteredEffectiveQDivisor n M) {w b : M → EReal} (hw : IsThetaPshPotential θ.val w)
    (hb : IsThetaPshPotential (θ - D.curvature).val b)
    (heq : ∀ x, x ∉ D.support → w x = D.weight x + b x) (hD : LocallyNondegenerate D.weight) :
    DiagonalMass.diagonalPotentialMass (θ - D.curvature) b hb =
      DiagonalMass.diagonalPotentialMass θ w hw := by
  classical
  have hsuppc : IsOpen D.supportᶜ :=
    (ResidualNef.isComplexAnalyticSubset_support D).isClosed.isOpen_compl
  have hpol : ManifoldLocallyPluripolar (n := n) D.support :=
    Pending.quasiPsh_poles_manifoldLocallyPluripolar
      ⟨(MeteredDivisorPositivity.thetaPlurisubharmonic_weight D).quasiPlurisubharmonic, hD⟩
  set μ₁ := globalMixedMeasure (fun _ : Fin n => θ - D.curvature) (fun _ => b) (fun _ => hb.1)
    with hμ₁
  set μ₂ := globalMixedMeasure (fun _ : Fin n => θ) (fun _ => w) (fun _ => hw.1) with hμ₂
  have h0₁ : μ₁ D.support = 0 := globalMixedMeasure_doesNotChargeManifoldPluripolar _ _ hpol
  have h0₂ : μ₂ D.support = 0 := globalMixedMeasure_doesNotChargeManifoldPluripolar _ _ hpol
  have hU : μ₁.restrict D.supportᶜ = μ₂.restrict D.supportᶜ := by
    apply restrict_eq_of_locally_eq
    intro x hx
    obtain ⟨P₁, P₂, hxP, hPU, hsrc, hP⟩ := exists_patch_pair θ D hb.1 heq hsuppc hx
    refine ⟨P₁.source, P₁.source.isOpen, hxP, hPU, ?_⟩
    rw [globalMixedMeasure_restrict_patch _ P₁, hP, hsrc, globalMixedMeasure_restrict_patch _ P₂]
  have hcompl : ∀ μ : Measure M, μ D.support = 0 → μ univ = μ D.supportᶜ := by
    intro μ hμ
    refine le_antisymm ?_ (measure_mono (subset_univ _))
    calc μ univ ≤ μ (D.supportᶜ ∪ D.support) := by rw [compl_union_self]
      _ ≤ μ D.supportᶜ + μ D.support := measure_union_le _ _
      _ = μ D.supportᶜ := by rw [hμ, add_zero]
  change μ₁ univ = μ₂ univ
  rw [hcompl μ₁ h0₁, hcompl μ₂ h0₂, ← Measure.restrict_apply_univ, hU,
    Measure.restrict_apply_univ]

end ChangeOfRepresentative

/-! ### Steps 2a–2c -/

section LogResolutionMass

variable {k : ℕ} {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel k) Z]
  [IsComplexManifold k Z] [CompactSpace Z] [ConnectedSpace Z] [MeasurableSpace Z] [BorelSpace Z]

/-- **Copy-4 `lem:domination`, Steps 2a–2c.**  On a compact connected Kähler manifold `Z` of
positive dimension, a `θ`-psh potential `φ` with analytic singularities of type `(c, 𝔞)` admits a
blowup sequence `ρ : Z' → Z` (`Z'` compact, connected, Kähler; `φ ∘ ρ` a `ρ^*θ`-psh potential) and
a metered effective `ℚ`-divisor `F` on `Z'` with

* `φ ∘ ρ = ψ_F + b` everywhere, `b` real with `|b| ≤ L.bound` (`HasLogSingularitiesAlong`);
* `b*` a `(ρ^*θ - Θ_F)`-psh potential, `-L.bound ≤ b* ≤ L.bound`, `b* = b` off `Supp F`
  (`R = ρ^*θ - Θ_F + ddᶜb*`, the residual current of the Siu decomposition);
* `{ρ^*θ} - {F}` nef with respect to every Kähler background of `Z'`;
* **`∫_{Z'} R^k = ∫_Z θ_φ^k`**: `∫ (ρ^*θ - Θ_F)_{b*}^k = ∫ θ_φ^k` (Borel structure on `Z'`).

`ρ` comes from `RelativePrincipalization.exists_factorizationData` (Hironaka, as given). -/
theorem exists_logResolution_mass (hk : 0 < k) (omegaZ : KahlerBackground k Z)
    (θ : ClosedRealOneOneForm k Z) {φ : Z → EReal} (hφ : IsThetaPshPotential θ.val φ)
    {c : ℚ} {𝔞 : GermIdeal k Z} (htype : HasAnalyticSingularitiesOfType (n := k) φ c 𝔞) :
    ∃ (Z' : Type u) (_ : TopologicalSpace Z') (_ : ChartedSpace (ComplexModel k) Z')
      (_ : IsComplexManifold k Z') (ρ : Z' → Z) (hρ : IsBlowupSequence k Z Z' ρ)
      (_ : CompactSpace Z'), ConnectedSpace Z' ∧ Nonempty (KahlerBackground k Z') ∧
      IsThetaPshPotential (ClosedRealOneOneForm.pullback hρ.contMDiff θ).val (fun y => φ (ρ y)) ∧
      ∃ (F : MeteredEffectiveQDivisor k Z') (L : HasLogSingularitiesAlong F (fun y => φ (ρ y)))
        (b : Z' → EReal)
        (hb : IsThetaPshPotential
          (ClosedRealOneOneForm.pullback hρ.contMDiff θ - F.curvature).val b),
        (∀ y, ((-L.bound : ℝ) : EReal) ≤ b y) ∧ (∀ y, b y ≤ (L.bound : EReal)) ∧
        (∀ y, y ∉ F.support → b y = (L.residual y : EReal)) ∧
        (∀ omega' : KahlerBackground k Z',
          NefWithRespectTo omega' (ClosedRealOneOneForm.pullback hρ.contMDiff θ - F.curvature)) ∧
        (letI : MeasurableSpace Z' := borel Z'
         haveI : BorelSpace Z' := ⟨rfl⟩
         DiagonalMass.diagonalPotentialMass
            (ClosedRealOneOneForm.pullback hρ.contMDiff θ - F.curvature) b hb =
          DiagonalMass.diagonalPotentialMass θ φ hφ) := by
  obtain ⟨Z', tZ', cZ', mZ', ρ, hρ, hcpt, hconn, hK, F, L, b, hb, hblow, hbupp, hboff, hnef⟩ :=
    DominationLogResolution.exists_logResolution hk omegaZ θ hφ htype
  have hsurj := (StrictTransformComposition.IsBlowupSequence.compactSpace_surjective hρ).2
  obtain ⟨x₀⟩ : Nonempty Z := inferInstance
  obtain ⟨x, -, hx⟩ := hφ.2 x₀ univ isOpen_univ (mem_univ x₀)
  obtain ⟨y₀, hy₀⟩ := hsurj x
  have hpshρ := GlobalPotentialPullback.thetaPlurisubharmonic_comp hρ.contMDiff hφ.1
  have hpot : IsThetaPshPotential (ClosedRealOneOneForm.pullback hρ.contMDiff θ).val
      (fun y => φ (ρ y)) :=
    ⟨hpshρ, ThetaPshIdentityPrinciple.locallyNondegenerate_of_exists_ne_bot hpshρ
      ⟨y₀, by rw [hy₀]; exact hx⟩⟩
  refine ⟨Z', tZ', cZ', mZ', ρ, hρ, hcpt, hconn, hK, hpot, F, L, b, hb, hblow, hbupp, hboff,
    hnef, ?_⟩
  let : MeasurableSpace Z' := borel Z'
  have : BorelSpace Z' := ⟨rfl⟩
  have hFnd : LocallyNondegenerate F.weight := by
    intro y U hU hyU
    obtain ⟨y', hy'U, hy'⟩ := hpot.2 y U hU hyU
    refine ⟨y', hy'U, fun hbot => hy' ?_⟩
    change φ (ρ y') = ⊥
    rw [L.weight_add y', hbot, EReal.bot_add]
  have heq : ∀ y, y ∉ F.support → φ (ρ y) = F.weight y + b y := fun y hy =>
    (L.weight_add y).trans (by rw [hboff y hy])
  show DiagonalMass.diagonalPotentialMass _ b hb = _
  rw [diagonalPotentialMass_sub_curvature_eq _ F hpot hb heq hFnd]
  exact ModificationMassInvariance.diagonalPotentialMass_pullback_of_isBlowupSequence hρ θ hφ hpot

end LogResolutionMass

end

end SGPT.Foundations.Analysis.Pending.DominationResidualMass
