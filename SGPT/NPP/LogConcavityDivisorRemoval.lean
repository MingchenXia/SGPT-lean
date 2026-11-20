import SGPT.Foundations.Analysis.Pending.DominationResidualMass

/-!
# Removing divisors from mixed non-pluripolar masses

Support for the log-concavity of mixed masses for currents with analytic singularities (source
`thm:logconc`). This is the mixed (several independent slots) version of TN's
`DominationResidualMass.diagonalPotentialMass_sub_curvature_eq`: if in every slot
`wᵢ = ψ_{Dᵢ} + bᵢ` off the support of a metered effective `ℚ`-divisor `Dᵢ`, where `wᵢ` is a
`θᵢ`-psh potential and `bᵢ` a `(θᵢ - Θ_{Dᵢ})`-psh potential, then the total mixed
non-pluripolar masses of `(θᵢ - Θ_{Dᵢ}, bᵢ)` and of `(θᵢ, wᵢ)` agree.

The proof is the diagonal one: off the (pluripolar) union of the supports the two tuples have
patches with literally equal corrected potentials, and neither mixed measure charges the union.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Manifold ContDiff ENNReal

namespace SGPT.NPP.LogConcavity

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open FirstPass.PositiveClasses FirstPass.HolomorphicIdealSheaves
  FirstPass.GlobalAnalyticSingularities FirstPass.GlobalPotentialPatches
  FirstPass.MixedNonPluripolar
open SGPT.Foundations.Analysis.Pending
open Pending.MixedNonPluripolar Pending.GlobalNonPluripolar Pending.ResidualNefReduction
  Pending.ModificationMassInvariance Pending.DominationResidualMass

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- The union of the supports of finitely many metered divisors. -/
def unionSupport (D : Fin n → MeteredEffectiveQDivisor n M) : Set M :=
  ⋃ i, (D i).support

omit [MeasurableSpace M] [BorelSpace M] in
theorem isOpen_compl_unionSupport (D : Fin n → MeteredEffectiveQDivisor n M) :
    IsOpen (unionSupport D)ᶜ := by
  rw [unionSupport, compl_iUnion]
  exact isOpen_iInter_of_finite fun i =>
    (ResidualNef.isComplexAnalyticSubset_support (D i)).isClosed.isOpen_compl

/-- **Off the supports the two patch measures coincide** (mixed version of
`DominationResidualMass.exists_patch_pair`). -/
theorem exists_patch_pair_mixed (θ : Fin n → ClosedRealOneOneForm n M)
    (D : Fin n → MeteredEffectiveQDivisor n M) {w b : Fin n → M → EReal}
    (hb : ∀ i, ThetaPlurisubharmonic (θ i - (D i).curvature).val (b i))
    (heq : ∀ i x, x ∉ (D i).support → w i x = (D i).weight x + b i x)
    {x : M} (hx : x ∉ unionSupport D) :
    ∃ (P₁ : Patch (fun i => θ i - (D i).curvature) b) (P₂ : Patch θ w),
      x ∈ P₁.source ∧ (P₁.source : Set M) ⊆ (unionSupport D)ᶜ ∧
      (P₁.source : Set M) = P₂.source ∧ patchMeasure P₁ = patchMeasure P₂ := by
  classical
  have hxi : ∀ i, x ∉ (D i).support := fun i h => hx (mem_iUnion.mpr ⟨i, h⟩)
  obtain ⟨P₀, hxP₀⟩ := exists_patch_containing hb x
  set e := P₀.chart with he
  have hxe : x ∈ e.val.source := P₀.source_subset hxP₀
  choose W hxW hψ using fun i =>
    MeteredDivisorSmoothOffSupport.exists_isSmoothLocalPotential_neg_curvature (D i) (hxi i) e hxe
  set ψ : Fin n → ComplexModel n → ℝ := fun i ζ => ((D i).weight (e.val.symm ζ)).toReal
    with hψdef
  have hWopen : IsOpen (⋂ i, W i) := isOpen_iInter_of_finite fun i => (hψ i).1
  let V : Opens (ComplexModel n) :=
    ⟨(P₀.domain : Set (ComplexModel n)) ∩ (⋂ i, W i) ∩
        (e.val.target ∩ e.val.symm ⁻¹' (unionSupport D)ᶜ),
      (P₀.domain.isOpen.inter hWopen).inter
        (e.val.isOpen_inter_preimage_symm (isOpen_compl_unionSupport D))⟩
  have hVP : V ≤ P₀.domain := fun _ hζ => hζ.1.1
  have hVW : ∀ i, (V : Set (ComplexModel n)) ⊆ W i := fun i _ hζ => mem_iInter.mp hζ.1.2 i
  let P₁ := P₀.restrict V hVP
  have hψeq : ∀ i, ∀ ζ ∈ (V : Set (ComplexModel n)),
      (D i).weight (e.val.symm ζ) = (ψ i ζ : EReal) := by
    intro i ζ hζ
    have hnot : e.val.symm ζ ∉ (D i).support := fun h =>
      hζ.2.2 (mem_iUnion.mpr ⟨i, h⟩)
    have hne : (D i).weight (e.val.symm ζ) ≠ ⊥ := hnot
    exact (EReal.coe_toReal (StepFourLogSingularities.weight_ne_top (D i) _) hne).symm
  have hcorr : ∀ (i : Fin n), ∀ ζ ∈ (V : Set (ComplexModel n)),
      chartFunction (w i) e ζ + ((P₀.potential i ζ - ψ i ζ : ℝ) : EReal) = P₁.corrected i ζ := by
    intro i ζ hζ
    have hnot : e.val.symm ζ ∉ (D i).support := fun h =>
      hζ.2.2 (mem_iUnion.mpr ⟨i, h⟩)
    change w i (e.val.symm ζ) + _ = b i (e.val.symm ζ) + _
    rw [heq i _ hnot, hψeq i ζ hζ, coe_add_add_coe_sub]
    rfl
  let P₂ : Patch θ w :=
    { chart := e
      domain := V
      domain_le_target := fun _ hζ => hζ.2.1
      potential := fun i ζ => P₀.potential i ζ - ψ i ζ
      localPotential := fun i => by
        refine ⟨V.isOpen, fun _ hζ => hζ.2.1,
          ((P₀.localPotential i).2.2.1.mono hVP).sub ((hψ i).2.2.1.mono (hVW i)), fun ζ hζ => ?_⟩
        rw [smoothDDC_sub V.isOpen ((P₀.localPotential i).2.2.1.mono hVP)
            ((hψ i).2.2.1.mono (hVW i)) hζ, (P₀.localPotential i).2.2.2 (hVP hζ),
          (hψ i).2.2.2 (hVW i hζ), ← BlowupBigPullback.coeff_sub]
        congr 1
        rw [sub_neg_eq_add, sub_add_cancel]
      plurisubharmonic := fun i ζ hζ => by
        refine ((P₁.plurisubharmonic i) ζ hζ).congr ?_
        filter_upwards [V.isOpen.mem_nhds hζ] with ζ' hζ'
        exact (hcorr i ζ' hζ').symm }
  have hsrc : (P₁.source : Set M) = P₂.source := rfl
  refine ⟨P₁, P₂, ?_, ?_, hsrc, ?_⟩
  · refine (Patch.mem_source_restrict P₀ V hVP).mpr ⟨hxP₀, ⟨hxP₀.2, mem_iInter.mpr hxW⟩,
      e.val.map_source hxe, ?_⟩
    show e.val.symm (e.val x) ∈ (unionSupport D)ᶜ
    rw [e.val.left_inv hxe]; exact hx
  · intro y hy
    have h := (Patch.mem_source_restrict P₀ V hVP).mp hy
    have h2 : e.val.symm (e.val y) ∈ (unionSupport D)ᶜ := h.2.2.2
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

/-- **Removing divisors from mixed masses.** If in every slot `wᵢ = ψ_{Dᵢ} + bᵢ` off
`Supp Dᵢ`, with `wᵢ` a `θᵢ`-psh potential, `bᵢ` a `(θᵢ - Θ_{Dᵢ})`-psh potential and `ψ_{Dᵢ}`
nondegenerate, then `∫ ⟨⋀ (θᵢ - Θ_{Dᵢ})_{bᵢ}⟩ = ∫ ⟨⋀ (θᵢ)_{wᵢ}⟩`. -/
theorem globalMixedMeasure_univ_sub_curvature_eq (θ : Fin n → ClosedRealOneOneForm n M)
    (D : Fin n → MeteredEffectiveQDivisor n M) {w b : Fin n → M → EReal}
    (hw : ∀ i, ThetaPlurisubharmonic (θ i).val (w i))
    (hb : ∀ i, ThetaPlurisubharmonic (θ i - (D i).curvature).val (b i))
    (heq : ∀ i x, x ∉ (D i).support → w i x = (D i).weight x + b i x)
    (hD : ∀ i, LocallyNondegenerate (D i).weight) :
    globalMixedMeasure (fun i => θ i - (D i).curvature) b hb univ =
      globalMixedMeasure θ w hw univ := by
  classical
  have hpol : ManifoldLocallyPluripolar (n := n) (unionSupport D) := by
    have hi : ∀ i, ManifoldLocallyPluripolar (n := n) (D i).support := fun i =>
      Pending.quasiPsh_poles_manifoldLocallyPluripolar
        ⟨(MeteredDivisorPositivity.thetaPlurisubharmonic_weight (D i)).quasiPlurisubharmonic,
          hD i⟩
    have hfin : ∀ s : Finset (Fin n),
        ManifoldLocallyPluripolar (n := n) (⋃ i ∈ s, (D i).support) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simpa using (manifoldLocallyPluripolar_empty (n := n) (M := M))
      | insert j s hj ih =>
          rw [Finset.set_biUnion_insert]
          exact Pending.manifoldLocallyPluripolar_union (hi j) ih
    have h := hfin Finset.univ
    simpa [unionSupport] using h
  set μ₁ := globalMixedMeasure (fun i => θ i - (D i).curvature) b hb with hμ₁
  set μ₂ := globalMixedMeasure θ w hw with hμ₂
  have h0₁ : μ₁ (unionSupport D) = 0 :=
    globalMixedMeasure_doesNotChargeManifoldPluripolar _ _ hpol
  have h0₂ : μ₂ (unionSupport D) = 0 :=
    globalMixedMeasure_doesNotChargeManifoldPluripolar _ _ hpol
  have hU : μ₁.restrict (unionSupport D)ᶜ = μ₂.restrict (unionSupport D)ᶜ := by
    apply restrict_eq_of_locally_eq
    intro x hx
    obtain ⟨P₁, P₂, hxP, hPU, hsrc, hP⟩ := exists_patch_pair_mixed θ D hb heq hx
    refine ⟨P₁.source, P₁.source.isOpen, hxP, hPU, ?_⟩
    rw [globalMixedMeasure_restrict_patch _ P₁, hP, hsrc, globalMixedMeasure_restrict_patch _ P₂]
  have hcompl : ∀ μ : Measure M, μ (unionSupport D) = 0 → μ univ = μ (unionSupport D)ᶜ := by
    intro μ hμ
    refine le_antisymm ?_ (measure_mono (subset_univ _))
    calc μ univ ≤ μ ((unionSupport D)ᶜ ∪ unionSupport D) := by rw [compl_union_self]
      _ ≤ μ (unionSupport D)ᶜ + μ (unionSupport D) := measure_union_le _ _
      _ = μ (unionSupport D)ᶜ := by rw [hμ, add_zero]
  rw [hcompl μ₁ h0₁, hcompl μ₂ h0₂, ← Measure.restrict_apply_univ, hU,
    Measure.restrict_apply_univ]

end SGPT.NPP.LogConcavity
