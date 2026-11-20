import SGPT.Foundations.Analysis.Pending.HironakaPrincipalization
import SGPT.Foundations.Analysis.Pending.ResidualNef
import SGPT.Foundations.Analysis.Pending.IdealComparisonResidual
import SGPT.Foundations.Analysis.Pending.GlobalPotentialPullback
import SGPT.Foundations.Analysis.Pending.ThetaPshIdentityPrinciple
import SGPT.Foundations.Analysis.Pending.BlowupKahler
import SGPT.Foundations.Analysis.Pending.AnalyticTypeRestriction
import SGPT.Foundations.Analysis.Pending.ModificationMassInvariance
import SGPT.Foundations.Analysis.Pending.MeteredDivisorSmoothOffSupport
import SGPT.Foundations.Analysis.Pending.MeteredDivisorPositivity
import SGPT.Foundations.Analysis.Pending.ManifoldPluripolar
import SGPT.Foundations.Analysis.Pending.NefBoundedMixedMass
import SGPT.Foundations.Analysis.Pending.ExceptionalMetric
import SGPT.Foundations.Analysis.Pending.DivisorMetric
import SGPT.Foundations.Analysis.Pending.BlowupConnected
import SGPT.Foundations.Analysis.Pending.BlowupBigPullback
import SGPT.Foundations.Analysis.Pending.MeteredDivisorScaling

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Resolving a potential of analytic type: the nef part and its mass (Boucksom)

Blueprint `bou:resolved-nef-part` (`blueprint/src/analytic.tex`; Boucksom 2002, Corollary 2.4, Lemma 2.9 and the proof of
Theorem 4.8, `bou02-volume:2.4`, `bou02-volume:2.9`, `bou02-volume:4.8`).

Let `(X, ω)` be a connected compact Kähler manifold of dimension `n ≥ 1`, `β` a smooth closed real `(1,1)`-form and `ψ` a
`β`-psh potential with analytic singularities of type `(c, 𝔞)`.  There are a modification `μ : X̃ → X` (a finite sequence of
blowups with smooth centres), a metered effective `ℚ`-divisor `D` and a metered effective `ℚ`-divisor `F` supported in
`Exc μ`, and a Kähler form `ω̃ = μ^*ω - Θ_F` on `X̃`, such that

1. `ψ ∘ μ` has logarithmic singularities along `D`;
2. the class `b = μ^*{β} - {D}`, represented by `μ^*β - Θ_D`, is nef, and `b^n = ∫_X ⟨β_ψ^n⟩`;
3. `{ω̃} = μ^*{ω} - {F}`, as the equality of forms `ω̃ = μ^*ω - Θ_F`.

The class of a metered divisor is that of its curvature form (as in `pc:domination-log-resolution`); that it is also the class
of the integration current `[D]` is `bou:divisor-class`.

**Route.**  This is the log resolution of `DominationLogResolution` / `DominationResidualMass` with the modification taken from
the proved principalization theorem `HironakaPrincipalization.exists_principalization` (H+2): `μ^*𝔞 = 𝒪(-G)` for an
effective divisor `G`, and `D = c G` with a smooth metric.  The relative principalization statement
`RelativePrincipalization.exists_factorizationData` is NOT used; this module does not import
`Pending.RelativePrincipalization`, and the few lemmas of `DominationLogResolution`, `DominationResidualMass` and
`StepFourLogSingularities` that are needed (those modules import it) are proved again here.

## Main results

* `isNonzeroAlongAt_of_hasAnalyticSingularitiesOfType`: the ideal of a nondegenerate weight of analytic type is nonzero at
  every point (the hypothesis of principalization);
* `logSingularitiesOfSameSingularityType`, `weight_ne_top`, `exists_regularizedResidual`,
  `diagonalPotentialMass_sub_curvature_eq` (change of representative off a divisor);
* `exists_logResolution_of_pullback_eq`: the log resolution, Siu decomposition, nef residual class and mass, along ANY blowup
  sequence that makes `𝔞` invertible;
* **`exists_resolvedNefPart`** (the node).

Sorry-free.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Manifold ContDiff ENNReal

universe u

namespace SGPT.Foundations.Analysis.Pending.ResolvedNefPart

open FirstPass FirstPass.PositiveClasses FirstPass.HolomorphicIdealSheaves
  FirstPass.GlobalAnalyticSingularities FirstPass.BlowupSequences
  FirstPass.NumericalRestrictedVolumeScaffold FirstPass.GlobalPotentialPatches
  FirstPass.MixedNonPluripolar MixedNonPluripolar GlobalNonPluripolar ResidualNefReduction
  ThetaPshCodimTwoExtension PshAnalyticSetExtension PshRemovableSingularity
  SGPT.Foundations.Analysis.Pending.DivisorExponentAlong

noncomputable section

/-! ### The ideal of a weight of analytic type is nonzero at every point -/

section Nonzero

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **The ideal of a nondegenerate weight of analytic type is nonzero at every point**: if `φ` has analytic singularities of
type `(c, 𝔞)` and is not identically `-∞` near any point, then at every point some germ of `𝔞` does not vanish identically
nearby (one of the local generators). -/
theorem isNonzeroAlongAt_of_hasAnalyticSingularitiesOfType {φ : M → EReal} {c : ℚ} {𝔞 : GermIdeal n M}
    (htype : HasAnalyticSingularitiesOfType (n := n) φ c 𝔞) (hnd : LocallyNondegenerate φ) (x : M) :
    IsNonzeroAlongAt univ 𝔞 x := by
  obtain ⟨hcQ, -, hlocal⟩ := htype
  obtain ⟨U, hU, hxU, N, g, hgDiff, hgMem, R, C, -, hformula⟩ := hlocal x
  have hc : 0 < (c : ℝ) := by exact_mod_cast hcQ
  have hfreq : ∃ᶠ y in 𝓝 x, ∃ j, g j y ≠ 0 := by
    rw [Filter.frequently_iff]
    intro V hV
    obtain ⟨W, hWV, hWo, hxW⟩ := mem_nhds_iff.mp hV
    obtain ⟨y, hyWU, hy⟩ := hnd x (W ∩ U) (hWo.inter hU) ⟨hxW, hxU⟩
    refine ⟨y, hWV hyWU.1, ?_⟩
    by_contra hzero
    push Not at hzero
    apply hy
    rw [hformula y hyWU.2]
    exact (scaled_generatorLog_add_eq_bot_iff g y hc (R y)).mpr hzero
  obtain ⟨j, hj⟩ : ∃ j, ∃ᶠ y in 𝓝 x, g j y ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨y, ⟨j, hj⟩, hy⟩ := (hfreq.and_eventually (eventually_all.mpr h)).exists
    exact hj (hy j)
  have hgj : HolomorphicAt n (g j) x := by
    rw [HolomorphicAt]
    filter_upwards [hU.mem_nhds hxU] with y hy
    exact (hgDiff j y hy).mdifferentiableAt (hU.mem_nhds hy)
  have hone : HolomorphicAt n (fun _ : M => (1 : ℂ)) x := by
    rw [HolomorphicAt]
    filter_upwards with y
    exact mdifferentiableAt_const (c := (1 : ℂ))
  have hmem : 𝔞.mem x (g j) := (hgMem x hxU (g j)).mpr (by
    refine ⟨hgj, 1, fun _ => g j, fun _ => 1, ?_, ?_, ?_⟩
    · intro i
      exact ⟨j, rfl⟩
    · intro i
      exact hone
    · filter_upwards with y
      simp)
  exact ⟨g j, hmem, hj.mono fun y hy => ⟨mem_univ y, hy⟩⟩

end Nonzero

/-! ### Log singularities from a singularity-type comparison -/

section LogSingularities

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- An extended real that is not `⊤` is `⊥` or real (`StepFourLogSingularities.eq_bot_or_exists_coe`). -/
theorem eq_bot_or_exists_coe {x : EReal} (hx : x ≠ ⊤) : x = ⊥ ∨ ∃ t : ℝ, x = t := by
  induction x using EReal.rec with
  | bot => exact Or.inl rfl
  | coe t => exact Or.inr ⟨t, rfl⟩
  | top => exact absurd rfl hx

/-- Pointwise content of a two-sided additive comparison with a function that is never `+∞`: at each point both are `-∞`,
or both are real and differ by at most `|C₁| + |C₂|` (`StepFourLogSingularities.bot_or_coe_of_le_of_le`). -/
theorem bot_or_coe_of_le_of_le {u v : EReal} {C₁ C₂ : ℝ} (hv : v ≠ ⊤)
    (h₁ : u ≤ v + (C₁ : EReal)) (h₂ : v ≤ u + (C₂ : EReal)) :
    (v = ⊥ ∧ u = ⊥) ∨ ∃ d f : ℝ, v = d ∧ u = f ∧ |f - d| ≤ |C₁| + |C₂| := by
  rcases eq_bot_or_exists_coe hv with rfl | ⟨d, rfl⟩
  · rw [EReal.bot_add] at h₁
    exact Or.inl ⟨rfl, le_bot_iff.mp h₁⟩
  have hutop : u ≠ ⊤ := by
    have : (d : EReal) + (C₁ : EReal) ≠ ⊤ := by
      rw [← EReal.coe_add]
      exact EReal.coe_ne_top _
    exact ne_top_of_le_ne_top this h₁
  rcases eq_bot_or_exists_coe hutop with rfl | ⟨f, rfl⟩
  · rw [EReal.bot_add] at h₂
    exact absurd (le_bot_iff.mp h₂) (EReal.coe_ne_bot _)
  rw [← EReal.coe_add, EReal.coe_le_coe_iff] at h₁ h₂
  refine Or.inr ⟨d, f, rfl, rfl, abs_le.mpr ⟨?_, ?_⟩⟩ <;>
    linarith [le_abs_self C₁, le_abs_self C₂, neg_abs_le C₁, neg_abs_le C₂]

/-- **Two weights of the same singularity type, one of them `ψ_D`, give log singularities along `D`**
(`StepFourLogSingularities.logSingularitiesOfSameSingularityType`). -/
def logSingularitiesOfSameSingularityType (D : MeteredEffectiveQDivisor n M)
    {φ : M → EReal} (hφ : SameSingularityTypeOn φ D.weight univ)
    (hne : ∀ x, D.weight x ≠ ⊤) : HasLogSingularitiesAlong D φ := by
  classical
  choose C₁ h₁ using hφ.1
  choose C₂ h₂ using hφ.2
  have key := fun x => bot_or_coe_of_le_of_le (hne x) (h₁ x (mem_univ x)) (h₂ x (mem_univ x))
  refine ⟨fun x => if D.weight x = ⊥ then 0 else (φ x).toReal - (D.weight x).toReal,
    |C₁| + |C₂|, fun x => ?_, fun x => ?_⟩
  · rcases key x with ⟨hx, -⟩ | ⟨d, f, hd, hf, hb⟩
    · simp only [hx, if_true, abs_zero]
      positivity
    · simp only [hd, hf, EReal.coe_ne_bot, if_false, EReal.toReal_coe]
      exact hb
  · rcases key x with ⟨hx, hφx⟩ | ⟨d, f, hd, hf, -⟩
    · simp [hx, hφx]
    · simp only [hd, hf, EReal.coe_ne_bot, if_false, EReal.toReal_coe, ← EReal.coe_add]
      congr 1
      ring

/-- A metered divisor's weight is never `+∞` on a compact manifold (`StepFourLogSingularities.weight_ne_top`). -/
theorem weight_ne_top [CompactSpace M] (E : MeteredEffectiveQDivisor n M) (y : M) :
    E.weight y ≠ ⊤ := by
  obtain ⟨K, hK⟩ := MeteredDivisorScaling.exists_forall_weight_le E
  exact ne_top_of_le_ne_top (EReal.coe_ne_top K) (hK y)

end LogSingularities

/-! ### The regularized residual -/

section Residual

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **The bounded potential of the residual current `R = θ - Θ_D + ddᶜb*`** (`DominationLogResolution.
exists_regularizedResidual`): if `φ` is `θ`-psh with log singularities along `D` and `Supp D ≠ M`, the upper regularization
`b*` of the residual across `Supp D` is a globally `(θ - Θ_D)`-psh potential, bounded by the residual's bound, equal to the
residual off `Supp D`. -/
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

/-- **Off `Supp D` the two patch measures coincide** (`DominationResidualMass.exists_patch_pair`): near a point off the
support, a patch of `(θ - Θ_D, b)` and a patch of `(θ, w)` with the same chart and domain have equal corrected potentials. -/
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
  have hψeq : ∀ ζ ∈ (V : Set (ComplexModel n)), D.weight (e.val.symm ζ) = (ψ ζ : EReal) := by
    intro ζ hζ
    have hne : D.weight (e.val.symm ζ) ≠ ⊥ := hζ.2.2
    exact (EReal.coe_toReal (weight_ne_top D _) hne).symm
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

/-- **Change of representative off a divisor** (`DominationResidualMass.diagonalPotentialMass_sub_curvature_eq`): if
`w = ψ_D + b` off `Supp D`, with `w` a `θ`-psh potential, `b` a `(θ - Θ_D)`-psh potential and `ψ_D` nondegenerate, then
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
    apply ModificationMassInvariance.restrict_eq_of_locally_eq
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

/-! ### The log resolution along any blowup sequence that makes `𝔞` invertible -/

section LogResolution

variable {k : ℕ} {Z : Type u} [TopologicalSpace Z] [ChartedSpace (ComplexModel k) Z]
  [IsComplexManifold k Z] [CompactSpace Z] [ConnectedSpace Z]

/-- A blowup sequence of a compact Kähler manifold is compact Kähler (Blanchard, by induction;
`DominationLogResolution.compactSpace_and_kahler_of_isBlowupSequence`). -/
theorem compactSpace_and_kahler_of_isBlowupSequence (hK : Nonempty (KahlerBackground k Z))
    {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel k) Y] [IsComplexManifold k Y]
    {f : Y → Z} (hf : IsBlowupSequence k Z Y f) :
    CompactSpace Y ∧ Nonempty (KahlerBackground k Y) := by
  induction hf with
  | refl => exact ⟨inferInstance, hK⟩
  | step f C g _ hg ih =>
      obtain ⟨hc, hk⟩ := ih
      have := hc
      exact BlowupKahler.compactSpace_and_kahler_of_isBlowupAlong hk hg

/-- **Log resolution, Siu decomposition, nef residual class and mass along any blowup sequence that makes the ideal
invertible**: let `Z` be a connected compact Kähler manifold, `θ` a smooth closed real `(1,1)`-form, `φ` a `θ`-psh potential
with analytic singularities of type `(c, 𝔞)`, and `ρ : Z' → Z` a blowup sequence with `ρ^*𝔞 = 𝒪(-G)` for an effective divisor
`G`.  Then `Z'` is compact, connected and Kähler, `φ ∘ ρ` is a `ρ^*θ`-psh potential, and there are a metered effective
`ℚ`-divisor `F` (`= c G` with a smooth metric) along which `φ ∘ ρ` has log singularities, and a `(ρ^*θ - Θ_F)`-psh potential
`b*`, bounded by the bound of the residual and equal to it off `Supp F`, such that `{ρ^*θ} - {F}` is nef with respect to every
Kähler background and `∫ (ρ^*θ - Θ_F)_{b*}^k = ∫ θ_φ^k`. -/
theorem exists_logResolution_of_pullback_eq (omegaZ : KahlerBackground k Z)
    (θ : ClosedRealOneOneForm k Z) {φ : Z → EReal} (hφ : IsThetaPshPotential θ.val φ)
    {c : ℚ} {𝔞 : GermIdeal k Z} (htype : HasAnalyticSingularitiesOfType (n := k) φ c 𝔞)
    {Z' : Type u} [TopologicalSpace Z'] [ChartedSpace (ComplexModel k) Z'] [IsComplexManifold k Z']
    {ρ : Z' → Z} (hρ : IsBlowupSequence k Z Z' ρ) (G : EffectiveDivisor k Z')
    (hideal : GermIdeal.pullback (m := k) ρ 𝔞 = G.ideal) :
    ∃ _ : CompactSpace Z', ConnectedSpace Z' ∧ Nonempty (KahlerBackground k Z') ∧
      IsThetaPshPotential (ClosedRealOneOneForm.pullback hρ.contMDiff θ).val (fun y => φ (ρ y)) ∧
      ∃ (F : MeteredEffectiveQDivisor k Z') (L : HasLogSingularitiesAlong F (fun y => φ (ρ y))),
        F.support = G.support ∧
        ∃ (b : Z' → EReal) (hb : IsThetaPshPotential
          (ClosedRealOneOneForm.pullback hρ.contMDiff θ - F.curvature).val b),
        (∀ y, ((-L.bound : ℝ) : EReal) ≤ b y) ∧ (∀ y, b y ≤ (L.bound : EReal)) ∧
        (∀ y, y ∉ F.support → b y = (L.residual y : EReal)) ∧
        (∀ omega' : KahlerBackground k Z',
          NefWithRespectTo omega' (ClosedRealOneOneForm.pullback hρ.contMDiff θ - F.curvature)) ∧
        ∀ [MeasurableSpace Z] [BorelSpace Z],
          (letI : MeasurableSpace Z' := borel Z'
           haveI : BorelSpace Z' := ⟨rfl⟩
           DiagonalMass.diagonalPotentialMass
              (ClosedRealOneOneForm.pullback hρ.contMDiff θ - F.curvature) b hb =
            DiagonalMass.diagonalPotentialMass θ φ hφ) := by
  classical
  obtain ⟨hcpt, hK⟩ := compactSpace_and_kahler_of_isBlowupSequence ⟨omegaZ⟩ hρ
  have := hcpt
  have hconn : ConnectedSpace Z' := BlowupConnected.connectedSpace_of_isBlowupSequence ρ hρ
  have hsurj : Function.Surjective ρ :=
    (StrictTransformComposition.IsBlowupSequence.compactSpace_surjective hρ).2
  -- a point off the poles of `φ`
  obtain ⟨x₀⟩ : Nonempty Z := inferInstance
  obtain ⟨x, -, hx⟩ := hφ.2 x₀ univ isOpen_univ (mem_univ x₀)
  -- the divisor `F = c G` with a smooth metric
  obtain ⟨EG, hEGs, hEG⟩ := DivisorMetric.exists_divisorMetric G
  have hc0 : (0 : ℚ) ≤ c := htype.1.le
  set F : MeteredEffectiveQDivisor k Z' := MeteredDivisorScaling.smul hc0 EG with hFdef
  have hFtype : HasAnalyticSingularitiesOfType (n := k) F.weight c G.ideal := by
    have h2 := IdealComparisonResidual.hasAnalyticSingularitiesOfType_smul htype.1
      (DivisorMetric.hasAnalyticSingularitiesOfType_of_isDivisorMetric hEG)
    rw [mul_one] at h2
    exact h2
  -- `φ ∘ ρ` has the same type
  have hφρ : HasAnalyticSingularitiesOfType (n := k) (φ ∘ ρ) c G.ideal := by
    rw [← hideal]
    exact AnalyticTypeRestriction.hasAnalyticSingularitiesOfType_comp hρ.contMDiff htype
  have hsame : SameSingularityTypeOn (fun y => φ (ρ y)) F.weight univ :=
    IdealWeightComparison.sameSingularityTypeOn_univ_of_eq_type hφρ hFtype
  let L : HasLogSingularitiesAlong F (fun y => φ (ρ y)) :=
    logSingularitiesOfSameSingularityType F hsame (weight_ne_top F)
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
  have hFsupp : F.support = G.support := by
    rw [hFdef, MeteredDivisorScaling.smul_support hc0 htype.1.ne' EG, hEGs]
  refine ⟨hcpt, hconn, hK, hpot, F, L, hFsupp, b, hb, hblow, hbupp, hboff,
    fun omega' => ResidualNef.nefWithRespectTo_sub_curvature omega' hpot L, ?_⟩
  intro _ _
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

end LogResolution

/-! ### `bou:resolved-nef-part` -/

section ResolvedNefPart

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [CompactSpace X] [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X]

/-- **Resolving a potential of analytic type: the nef part and its mass** (Boucksom; `bou:resolved-nef-part`): let `(X, ω)` be
a connected compact Kähler manifold of dimension `n ≥ 1`, `β` a smooth closed real `(1,1)`-form and `ψ` a `β`-psh potential
with analytic singularities of type `(c, 𝔞)`.  There are a modification `μ : X̃ → X` (a blowup sequence; `X̃` compact and
connected), a Kähler form `ω̃` on `X̃`, and metered effective `ℚ`-divisors `D` and `F` on `X̃`, `Supp F ⊆ Exc μ`, such that
1. `ψ ∘ μ` has logarithmic singularities along `D`;
2. the class `b = μ^*{β} - {D}` (the form `μ^*β - Θ_D`) is nef with respect to every Kähler background, and
   `b^n = ∫_X ⟨β_ψ^n⟩` (the intersection number `∫_{X̃} b^n`, computed with any Kähler background of `X̃`; the mass is
   finite, and the equality is stated in `ℝ≥0∞`);
3. `ω̃ = μ^*ω - Θ_F`, so `{ω̃} = μ^*{ω} - {F}`.

The modification is the principalization of `𝔞` (`HironakaPrincipalization.exists_principalization`, H+2). -/
theorem exists_resolvedNefPart (hn : 0 < n) (omega : KahlerBackground n X) (β : ClosedRealOneOneForm n X)
    {ψ : X → EReal} (hψ : IsThetaPshPotential β.val ψ) {c : ℚ} {𝔞 : GermIdeal n X}
    (htype : HasAnalyticSingularitiesOfType (n := n) ψ c 𝔞) :
    ∃ (Xt : Type u) (_ : TopologicalSpace Xt) (_ : ChartedSpace (ComplexModel n) Xt)
      (_ : IsComplexManifold n Xt) (μ : Xt → X) (hμ : IsBlowupSequence n X Xt μ) (_ : CompactSpace Xt),
      ConnectedSpace Xt ∧
      ∃ (ωt : KahlerBackground n Xt) (D F : MeteredEffectiveQDivisor n Xt),
        Nonempty (HasLogSingularitiesAlong D (fun y => ψ (μ y))) ∧
        (∀ w : KahlerBackground n Xt,
          NefWithRespectTo w (ClosedRealOneOneForm.pullback hμ.contMDiff β - D.curvature)) ∧
        (letI : MeasurableSpace Xt := borel Xt
         haveI : BorelSpace Xt := ⟨rfl⟩
         ∀ w : KahlerBackground n Xt,
          ENNReal.ofReal
              (NefMixedMass.slotIntegral w (fun _ => ClosedRealOneOneForm.pullback hμ.contMDiff β - D.curvature)) =
            DiagonalMass.diagonalPotentialMass β ψ hψ) ∧
        F.support ⊆ exceptionalLocus n μ ∧
        ωt.form = ClosedRealOneOneForm.pullback hμ.contMDiff omega.form - F.curvature := by
  classical
  -- the principalization of `𝔞` (H+2)
  have hne : ∀ x, IsNonzeroAlongAt univ 𝔞 x :=
    isNonzeroAlongAt_of_hasAnalyticSingularitiesOfType htype hψ.2
  obtain ⟨Xt, tX, cX, mX, μ, hμ, G, -, hideal, -, -, -, -⟩ :=
    HironakaPrincipalization.exists_principalization htype.2.1 hne
  obtain ⟨hcpt, hconn, -, -, D, L, -, b, hb, hblow, hbupp, -, hnef, hmass⟩ :=
    exists_logResolution_of_pullback_eq omega β hψ htype hμ G hideal
  have := hcpt
  -- the Kähler correction (3)
  obtain ⟨F, hFsupp, hFK, -⟩ := ExceptionalMetric.exists_exceptionalMetric omega μ hμ
  refine ⟨Xt, tX, cX, mX, μ, hμ, hcpt, hconn,
    ⟨ClosedRealOneOneForm.pullback hμ.contMDiff omega.form - F.curvature, hFK⟩, D, F, ⟨L⟩, hnef, ?_,
    hFsupp, rfl⟩
  -- the intersection number (2)
  let : MeasurableSpace Xt := borel Xt
  have : BorelSpace Xt := ⟨rfl⟩
  intro w
  have hbd : BoundedGlobalProduct.IsBoundedPotential b :=
    ⟨-L.bound, L.bound, fun x => ⟨hblow x, hbupp x⟩⟩
  have h := NefBoundedMixedMass.globalMixedMass_toReal_eq_slotIntegral hn w (θ := fun _ => _)
    (u := fun _ => b) (fun _ => hnef w) (fun _ => hb) (fun _ => hbd)
  have hfin : DiagonalMass.diagonalPotentialMass β ψ hψ ≠ ⊤ :=
    (MixedMass.globalMixedMass_lt_top omega (θ := fun _ => β) (u := fun _ => ψ) (fun _ => hψ.1)).ne
  rw [← h, ← ENNReal.ofReal_toReal hfin, ← hmass]
  rfl

end ResolvedNefPart

end

end SGPT.Foundations.Analysis.Pending.ResolvedNefPart
