import SGPT.Foundations.Analysis.Pending.DominationResidualMass

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Change of representative off a divisor, for MIXED global non-pluripolar measures

Source: Copy-4, `lem:domination`, Step 2 (`eq:dom-Ak`: the non-pluripolar product puts no mass on
the divisor); Boucksom, proof of Theorem 4.8 (`bou02-volume:4.8`, the mixed masses of the residual
part after the resolution).  Mixed form of
`DominationResidualMass.diagonalPotentialMass_sub_curvature_eq` (TN23), with the same proof.

Let `D` be a metered effective `ℚ`-divisor with weight `ψ_D` and curvature `Θ_D`, `θ` a family of
closed real `(1,1)`-forms and `S` a set of slots.  Correct the slots of `S` by `-Θ_D`
(`subCurvatureOn θ D S`).  If the potentials `u` of the corrected family and `w` of `θ` satisfy
`w i = ψ_D + u i` (`i ∈ S`) and `w i = u i` (`i ∉ S`) off `Supp D`, the two mixed measures have the
same total mass (`globalMixedMeasure_univ_subCurvatureOn_eq`): off `Supp D` the patches have
literally equal corrected potentials (`ψ_D` is a smooth local potential of `-Θ_D` there), and
`Supp D`, the pole set of `ψ_D`, is pluripolar, hence charged by neither measure.

Sorry-free.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Manifold ContDiff ENNReal

namespace SGPT.Foundations.Analysis.Pending.DivisorMixedMass

open FirstPass FirstPass.PositiveClasses FirstPass.HolomorphicIdealSheaves
  FirstPass.GlobalPotentialPatches FirstPass.MixedNonPluripolar MixedNonPluripolar
  GlobalNonPluripolar ResidualNefReduction ModificationMassInvariance DominationResidualMass

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- The family `θ` with the slots of `S` corrected by `-Θ_D`. -/
def subCurvatureOn (θ : Fin n → ClosedRealOneOneForm n M) (D : MeteredEffectiveQDivisor n M)
    (S : Finset (Fin n)) : Fin n → ClosedRealOneOneForm n M :=
  fun i => if i ∈ S then θ i - D.curvature else θ i

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- **Off `Supp D` the two patch measures coincide** (mixed form of
`DominationResidualMass.exists_patch_pair`). -/
theorem exists_patch_pair_on (θ : Fin n → ClosedRealOneOneForm n M)
    (D : MeteredEffectiveQDivisor n M) (S : Finset (Fin n)) {u w : Fin n → M → EReal}
    (hu : ∀ i, ThetaPlurisubharmonic (subCurvatureOn θ D S i).val (u i))
    (heq : ∀ i, ∀ x, x ∉ D.support → w i x = if i ∈ S then D.weight x + u i x else u i x)
    (hsuppc : IsOpen D.supportᶜ) {x : M} (hx : x ∉ D.support) :
    ∃ (P₁ : Patch (subCurvatureOn θ D S) u) (P₂ : Patch θ w),
      x ∈ P₁.source ∧ (P₁.source : Set M) ⊆ D.supportᶜ ∧
      (P₁.source : Set M) = P₂.source ∧ patchMeasure P₁ = patchMeasure P₂ := by
  classical
  obtain ⟨P₀, hxP₀⟩ := exists_patch_containing hu x
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
    exact (EReal.coe_toReal (StepFourLogSingularities.weight_ne_top D _) hne).symm
  set pot : Fin n → ComplexModel n → ℝ :=
    fun i ζ => if i ∈ S then P₀.potential i ζ - ψ ζ else P₀.potential i ζ with hpot
  have hcorr : ∀ (i : Fin n), ∀ ζ ∈ (V : Set (ComplexModel n)),
      chartFunction (w i) e ζ + ((pot i ζ : ℝ) : EReal) = P₁.corrected i ζ := by
    intro i ζ hζ
    change w i (e.val.symm ζ) + _ = u i (e.val.symm ζ) + _
    rw [heq i _ hζ.2.2]
    by_cases hi : i ∈ S
    · simp only [if_pos hi, hpot]
      rw [hψeq ζ hζ, coe_add_add_coe_sub]
      rfl
    · simp only [if_neg hi, hpot]
      rfl
  let P₂ : Patch θ w :=
    { chart := e
      domain := V
      domain_le_target := fun _ hζ => hζ.2.1
      potential := pot
      localPotential := fun i => by
        have hloc := P₀.localPotential i
        by_cases hi : i ∈ S
        · simp only [subCurvatureOn, if_pos hi] at hloc
          have hpi : pot i = fun ζ => P₀.potential i ζ - ψ ζ := by
            funext ζ; simp only [hpot, if_pos hi]
          rw [hpi]
          refine ⟨V.isOpen, fun _ hζ => hζ.2.1,
            (hloc.2.2.1.mono hVP).sub (hψ.2.2.1.mono hVW), fun ζ hζ => ?_⟩
          rw [smoothDDC_sub V.isOpen (hloc.2.2.1.mono hVP)
              (hψ.2.2.1.mono hVW) hζ, hloc.2.2.2 (hVP hζ), hψ.2.2.2 (hVW hζ),
            ← BlowupBigPullback.coeff_sub]
          congr 1
          rw [sub_neg_eq_add, sub_add_cancel]
        · simp only [subCurvatureOn, if_neg hi] at hloc
          have hpi : pot i = P₀.potential i := by
            funext ζ; simp only [hpot, if_neg hi]
          rw [hpi]
          exact hloc.mono V.isOpen hVP
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

/-- **Change of representative off a divisor, mixed form.**  If `w i = ψ_D + u i` for `i ∈ S` and
`w i = u i` for `i ∉ S` off `Supp D`, with `ψ_D` nondegenerate, then the mixed measures of
`(subCurvatureOn θ D S, u)` and `(θ, w)` have the same total mass. -/
theorem globalMixedMeasure_univ_subCurvatureOn_eq (θ : Fin n → ClosedRealOneOneForm n M)
    (D : MeteredEffectiveQDivisor n M) (S : Finset (Fin n)) {u w : Fin n → M → EReal}
    (hu : ∀ i, ThetaPlurisubharmonic (subCurvatureOn θ D S i).val (u i))
    (hw : ∀ i, ThetaPlurisubharmonic (θ i).val (w i))
    (heq : ∀ i, ∀ x, x ∉ D.support → w i x = if i ∈ S then D.weight x + u i x else u i x)
    (hD : LocallyNondegenerate D.weight) :
    globalMixedMeasure (subCurvatureOn θ D S) u hu univ = globalMixedMeasure θ w hw univ := by
  classical
  have hsuppc : IsOpen D.supportᶜ :=
    (ResidualNef.isComplexAnalyticSubset_support D).isClosed.isOpen_compl
  have hpol : ManifoldLocallyPluripolar (n := n) D.support :=
    Pending.quasiPsh_poles_manifoldLocallyPluripolar
      ⟨(MeteredDivisorPositivity.thetaPlurisubharmonic_weight D).quasiPlurisubharmonic, hD⟩
  set μ₁ := globalMixedMeasure (subCurvatureOn θ D S) u hu with hμ₁
  set μ₂ := globalMixedMeasure θ w hw with hμ₂
  have h0₁ : μ₁ D.support = 0 := globalMixedMeasure_doesNotChargeManifoldPluripolar _ _ hpol
  have h0₂ : μ₂ D.support = 0 := globalMixedMeasure_doesNotChargeManifoldPluripolar _ _ hpol
  have hU : μ₁.restrict D.supportᶜ = μ₂.restrict D.supportᶜ := by
    apply restrict_eq_of_locally_eq
    intro x hx
    obtain ⟨P₁, P₂, hxP, hPU, hsrc, hP⟩ := exists_patch_pair_on θ D S hu heq hsuppc hx
    refine ⟨P₁.source, P₁.source.isOpen, hxP, hPU, ?_⟩
    rw [globalMixedMeasure_restrict_patch _ P₁, hP, hsrc, globalMixedMeasure_restrict_patch _ P₂]
  have hcompl : ∀ μ : Measure M, μ D.support = 0 → μ univ = μ D.supportᶜ := by
    intro μ hμ
    refine le_antisymm ?_ (measure_mono (subset_univ _))
    calc μ univ ≤ μ (D.supportᶜ ∪ D.support) := by rw [compl_union_self]
      _ ≤ μ D.supportᶜ + μ D.support := measure_union_le _ _
      _ = μ D.supportᶜ := by rw [hμ, add_zero]
  rw [hcompl μ₁ h0₁, hcompl μ₂ h0₂, ← Measure.restrict_apply_univ, hU,
    Measure.restrict_apply_univ]

end

end SGPT.Foundations.Analysis.Pending.DivisorMixedMass
