import SGPT.Okounkov.TranscendentalWNKeyLSCSlice

/-!
# Null sets of the restricted non-pluripolar measures (package WN-KEY, lane WN-LSC)

Blueprint `claude-tok-wn-lsc`, node `tok-wn-lsc:null-sets`; source WN21 §5 ("the non-pluripolar
measures put no mass on the polar set and on the analytic set `X' ∩ ℰ`").

Non-pluripolar measures do not charge pluripolar sets
(`GlobalNonPluripolar.globalMixedMeasure_doesNotChargeManifoldPluripolar`), so:

* `fibreMeasure_flag_eq_zero`: `⟨(T|_{X'})ⁿ⟩(Z) = 0` (`Z` is a closed submanifold with empty
  interior, hence an analytic set with empty interior, hence pluripolar);
* `fibreMeasure_poles_eq_zero`: the pole set of a quasi-psh potential is not charged;
* `fibreMeasure_strict_eq_zero`: `⟨(T|_ℰ)ⁿ⟩(X' ∩ ℰ) = 0`: `X' ∩ ℰ` is an analytic subset of `ℰ`
  (preimage of the closed submanifold `X'`) with empty interior in `ℰ`
  (`interior_strict_inter_exceptional`): near `q ∈ X' ∩ ℰ` the monomial chart is `j = m`, in which
  `ℰ = {w_m = 0}` and `X' ∩ ℰ ⊆ {w_{m+1} = 0}` (`ExcChart.W_idxT_eq_zero_of_mem_strict`), a
  hyperplane of the coordinates `y` of `ℰ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

universe u

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Manifold ContDiff

namespace SGPT.Okounkov.TranscendentalWN.LSC

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending.GlobalNonPluripolar
open SGPT.Foundations.Analysis.Pending.BlowupMonomialCharts
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open scoped SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open SGPT.Okounkov.TranscendentalMain
open SGPT.Okounkov.TranscendentalWN

/-! ### Generic null sets -/

section Generic

variable {k N : ℕ} {V : Type*} [TopologicalSpace V] [ChartedSpace (ComplexModel k) V]
  [IsComplexManifold k V] [MeasurableSpace V] [BorelSpace V] [CompactSpace V]
  {𝒳 : Type*} [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel N) 𝒳] [IsComplexManifold N 𝒳]

theorem fibreMeasure_eq_zero_of_pluripolar {j : V → 𝒳}
    (hj : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel N) ∞ j)
    (Θ : ClosedRealOneOneForm N 𝒳) (φ : 𝒳 → EReal) (hφ : ThetaPlurisubharmonic Θ.val φ)
    {S : Set V} (hS : ManifoldLocallyPluripolar (n := k) S) : fibreMeasure hj Θ φ hφ S = 0 :=
  globalMixedMeasure_doesNotChargeManifoldPluripolar _ S hS

/-- The pole set of the restriction is not charged. -/
theorem fibreMeasure_poles_eq_zero {j : V → 𝒳}
    (hj : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel N) ∞ j)
    (Θ : ClosedRealOneOneForm N 𝒳) (φ : 𝒳 → EReal) (hφ : ThetaPlurisubharmonic Θ.val φ)
    (hw : IsThetaPshPotential (ClosedRealOneOneForm.pullback hj Θ).val (fun x => φ (j x))) :
    fibreMeasure hj Θ φ hφ {x | φ (j x) = ⊥} = 0 :=
  fibreMeasure_eq_zero_of_pluripolar hj Θ φ hφ
    (quasiPsh_poles_manifoldLocallyPluripolar
      ⟨hw.1.quasiPlurisubharmonic, hw.2⟩)

/-- An analytic subset with empty interior is not charged. -/
theorem fibreMeasure_analytic_eq_zero {j : V → 𝒳}
    (hj : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel N) ∞ j)
    (Θ : ClosedRealOneOneForm N 𝒳) (φ : 𝒳 → EReal) (hφ : ThetaPlurisubharmonic Θ.val φ)
    {A : Set V} (hA : IsComplexAnalyticSubset (n := k) A) (hint : interior A = ∅) :
    fibreMeasure hj Θ φ hφ A = 0 :=
  fibreMeasure_eq_zero_of_pluripolar hj Θ φ hφ
    (ModificationMassInvariance.manifoldLocallyPluripolar_of_isComplexAnalyticSubset hA hint)

end Generic

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))

variable {𝒳 : Type u} [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
  [IsComplexManifold (m + 1 + 1) 𝒳] {μ : 𝒳 → F.carrier × ProjectiveLine}

/-- `Z` is not charged by the restriction to `X` of a non-pluripolar measure. -/
theorem fibreMeasure_flag_eq_zero [MeasurableSpace F.carrier] [BorelSpace F.carrier]
    {ι : F.carrier → 𝒳}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ ι)
    (Θ : ClosedRealOneOneForm (m + 1 + 1) 𝒳) (φ : 𝒳 → EReal) (hφ : ThetaPlurisubharmonic Θ.val φ) :
    fibreMeasure hι Θ φ hφ (F.flag (1 : Fin (m + 2))) = 0 := by
  have hsub : IsClosedSubmanifold (m + 1) (F.flag (1 : Fin (m + 2))) :=
    ⟨F.firstDivisor.1, fun x hx => ⟨m, F.firstDivisor.2.2 x hx⟩⟩
  exact fibreMeasure_analytic_eq_zero hι Θ φ hφ
    (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hsub)
    (interior_firstFlag F)

/-- **`X' ∩ ℰ` has empty interior in `ℰ`.** -/
theorem interior_strict_inter_exceptional (hμ : IsNormalConeDeformation F μ) :
    letI := exceptionalChartedSpace F hμ
    interior ((Subtype.val : exceptionalSet F μ → 𝒳) ⁻¹' strictCentralFibre F μ) = ∅ := by
  classical
  refine eq_empty_of_forall_notMem fun z hz => ?_
  obtain ⟨U', hU'o, hU'⟩ := isOpen_induced_iff.mp (isOpen_interior (s := (Subtype.val :
    exceptionalSet F μ → 𝒳) ⁻¹' strictCentralFibre F μ))
  have hzU : z.1 ∈ U' := by
    have : z ∈ Subtype.val ⁻¹' U' := by rw [hU']; exact hz
    exact this
  have hU'X : ∀ w : 𝒳, w ∈ exceptionalSet F μ → w ∈ U' → w ∈ strictCentralFibre F μ := by
    intro w hwE hwU
    have : (⟨w, hwE⟩ : exceptionalSet F μ) ∈ interior ((Subtype.val : exceptionalSet F μ → 𝒳) ⁻¹'
        strictCentralFibre F μ) := by rw [← hU']; exact hwU
    exact (interior_subset (s := (Subtype.val : exceptionalSet F μ → 𝒳) ⁻¹'
      strictCentralFibre F μ) this : _)
  set q₁ : 𝒳 := z.1
  have hqE : q₁ ∈ exceptionalSet F μ := z.2
  have hqX : q₁ ∈ strictCentralFibre F μ := hU'X q₁ hqE hzU
  obtain ⟨C⟩ := nonempty_excChart F hμ hqE
  rcases C.hj with hj | hj
  swap
  · have := C.inter_strict_eq_empty hj
    exact (eq_empty_iff_forall_notMem.mp this) q₁ ⟨C.hqO, hqX⟩
  -- the chart `j = m`: the coordinates `y ↦ ℓ(Λ₀ y)` of `ℰ`
  set D := monomialDomain C.Ψ m C.j with hD
  have hWqD : C.W q₁ ∈ D := C.W_mem_monomialDomain C.hqO
  set p₀ : LiftedOpen.{u} D := LiftedOpen.mk D (C.W q₁) hWqD
  set Λ₀ : ComplexModel (m + 1) → ComplexModel (m + 1 + 1) := fun y =>
    swapNormal m (splitL m (y, 0)) with hΛ₀
  have hΛ₀c : Continuous Λ₀ := (swapNormal m).continuous.comp
    ((splitL m).continuous.comp (continuous_id.prodMk continuous_const))
  set y₀ := SliceCoords.nuZ m (C.W q₁) with hy₀
  have hWqZ : C.W q₁ (idxZ m) = 0 := by
    have := (C.mem_exceptional_iff C.hqO).mp hqE
    rwa [hj] at this
  have hΛ₀y₀ : Λ₀ y₀ = C.W q₁ := by
    apply (swapNormal m).symm.injective
    rw [hΛ₀, ContinuousLinearEquiv.symm_apply_apply, swapNormal_symm_apply,
      SliceCoords.splitL_eq_iff]
    refine ⟨rfl, ?_⟩
    simp [hWqZ]
  set g : ComplexModel (m + 1) → 𝒳 := fun y => C.ℓ (liftMk D p₀ (Λ₀ y)) with hg
  have hgc : ContinuousAt g y₀ := by
    have h1 : ContinuousAt (fun v => C.ℓ (liftMk D p₀ v)) (Λ₀ y₀) := by
      rw [hΛ₀y₀]
      exact ((C.hℓ _).comp _ (contMDiffAt_liftMk p₀ hWqD)).continuousAt
    exact h1.comp hΛ₀c.continuousAt
  have hgq : g y₀ = q₁ := by
    simp only [hg]
    rw [hΛ₀y₀]
    exact C.ℓ_W C.hqO
  -- near `y₀` the coordinate `y_m` vanishes
  have hev : ∀ᶠ y in 𝓝 y₀, y (Fin.last m) = 0 := by
    have h1 : ∀ᶠ y in 𝓝 y₀, Λ₀ y ∈ D :=
      hΛ₀c.continuousAt.preimage_mem_nhds (D.isOpen.mem_nhds (by rw [hΛ₀y₀]; exact hWqD))
    have h2 : ∀ᶠ y in 𝓝 y₀, g y ∈ C.O ∩ U' :=
      hgc.preimage_mem_nhds ((C.hO.inter hU'o).mem_nhds (by rw [hgq]; exact ⟨C.hqO, hzU⟩))
    filter_upwards [h1, h2] with y hy1 hy2
    have hWg : C.W (g y) = Λ₀ y := C.W_ℓ hy1 hy2.1
    have hgE : g y ∈ exceptionalSet F μ := by
      rw [C.mem_exceptional_iff hy2.1, hWg, hj]
      simp [hΛ₀]
    have hgX := hU'X (g y) hgE hy2.2
    have h0 := C.W_idxT_eq_zero_of_mem_strict hj hy2.1 hgX
    rw [hWg] at h0
    simpa [hΛ₀] using h0
  -- contradiction along the direction of `y_m`
  set v : ℂ → ComplexModel (m + 1) := fun ε => y₀ + ε • EuclideanSpace.single (Fin.last m) 1
    with hv
  have hvc : Continuous v := continuous_const.add (continuous_id.smul continuous_const)
  have hvt : Tendsto v (𝓝[≠] 0) (𝓝 y₀) := by
    have : v 0 = y₀ := by simp [hv]
    rw [← this]
    exact hvc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hy₀0 : y₀ (Fin.last m) = 0 := hev.self_of_nhds
  obtain ⟨ε, hε, hε0⟩ := ((hvt.eventually hev).and self_mem_nhdsWithin).exists
  apply hε0
  simpa [hv, hy₀0] using hε

/-- **`X' ∩ ℰ` is not charged** by the restriction to `ℰ` of a non-pluripolar measure. -/
theorem fibreMeasure_strict_eq_zero (hμ : IsNormalConeDeformation F μ)
    (Θ : ClosedRealOneOneForm (m + 1 + 1) 𝒳) (φ : 𝒳 → EReal) (hφ : ThetaPlurisubharmonic Θ.val φ) :
    letI := exceptionalChartedSpace F hμ
    haveI := isComplexManifold_exceptional F hμ
    letI : MeasurableSpace (exceptionalSet F μ) := borel (exceptionalSet F μ)
    haveI : BorelSpace (exceptionalSet F μ) := ⟨rfl⟩
    haveI := compactSpace_exceptional F hμ
    fibreMeasure (contMDiff_exceptionalInclusion F hμ) Θ φ hφ
      ((Subtype.val : exceptionalSet F μ → 𝒳) ⁻¹' strictCentralFibre F μ) = 0 := by
  let _ := exceptionalChartedSpace F hμ
  have _ := isComplexManifold_exceptional F hμ
  let _ : MeasurableSpace (exceptionalSet F μ) := borel (exceptionalSet F μ)
  have _ : BorelSpace (exceptionalSet F μ) := ⟨rfl⟩
  have _ := compactSpace_exceptional F hμ
  have hsub : IsClosedSubmanifold (m + 1 + 1) (strictCentralFibre F μ) :=
    ⟨isClosed_strictCentralFibre F, fun z hz => ⟨m + 1, regularAtDim_strictCentralFibre F hμ hz⟩⟩
  exact fibreMeasure_analytic_eq_zero _ Θ φ hφ
    (AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage (contMDiff_exceptionalInclusion F hμ)
      (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hsub))
    (interior_strict_inter_exceptional F hμ)

end SGPT.Okounkov.TranscendentalWN.LSC
