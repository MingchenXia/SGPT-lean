import SGPT.Okounkov.TranscendentalWNConvFLChart
import SGPT.Foundations.Analysis.Pending.BedfordTaylorHolomorphic
import SGPT.Foundations.Analysis.Pending.BedfordTaylorCapacity
import SGPT.Foundations.Analysis.Pending.LocalCurrentPullbackDdc

/-!
# Restricted test masses through holomorphic parametrizations

Blueprint `claude-tok-wn-fl4`, node `tok-wn-fl4:param-measure`; source WN21 §7, proof of
Proposition 7.4 (the fibre measures near `ℰ \ X'` are computed in the coordinates `(z̃₁, z')`, in
which the fibres `X_τ` are the slices `τ = const`).

`restrictedTestMass_eq_of_param`: let `e` be a chart of `V`, `A` an open set of chart coordinates
and `φ : B → A` a biholomorphism (inverse `σ`) from an open `B ⊆ ℂ^{k+1}`.  If `P` is a smooth local
potential of `j^*Θ` on `A` and the corrected potential `f = u ∘ e⁻¹ ∘ φ + P ∘ φ` is a locally
bounded psh function on `B`, then for every test function `ρ ≥ 0` with `ρ ∘ j` supported in
`e⁻¹(A)` and every continuous `χ` vanishing off a compact `K ⊆ B` with `χ = ρ ∘ j ∘ e⁻¹ ∘ φ` on
`B`, `∫ ρ ∘ j d⟨(j^*Θ + dd^c u)ᵏ⁺¹⟩ = ∫ χ d(dd^c f)ᵏ⁺¹` (the Bedford--Taylor measure on `B`).

Proof: the measure is the Bedford--Taylor measure of `f ∘ σ` on `A`
(`lintegral_diagonalPotentialMeasure_eq_canonical`, lane WN-FL), which is the push-forward under
`φ` of the Bedford--Taylor measure of `f` on `B` (holomorphic covariance of Bedford--Taylor
limits, TN `IsBTLimit.comp_biholomorphic`, and their uniqueness `IsBTLimit.unique`).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.BedfordTaylor

section Param

variable {k N : ℕ} {V : Type*} [TopologicalSpace V] [ChartedSpace (ComplexModel (k + 1)) V]
  [IsComplexManifold (k + 1) V] [CompactSpace V] {𝒳 : Type*} [TopologicalSpace 𝒳]
  [ChartedSpace (ComplexModel N) 𝒳] [IsComplexManifold N 𝒳]

/-- The inverse pair of a biholomorphic pair. -/
theorem isBiholomorphicPair_swap {A B : Opens (ComplexModel (k + 1))}
    {φ σ : ComplexModel (k + 1) → ComplexModel (k + 1)} (h : IsBiholomorphicPair B A φ σ) :
    IsBiholomorphicPair A B σ φ :=
  ⟨h.holo_inv, h.holo, h.mapsTo_inv, h.mapsTo, h.right_inv, h.left_inv⟩

/-- **The Bedford--Taylor measure of a composition with a biholomorphism** is the push-forward. -/
theorem canonicalBedfordTaylorMeasure_comp_eq_map {A B : Opens (ComplexModel (k + 1))}
    {φ σ : ComplexModel (k + 1) → ComplexModel (k + 1)} (hφ : IsBiholomorphicPair B A φ σ)
    {f : ComplexModel (k + 1) → ℝ} (hf : IsLocallyBoundedPshOn B f)
    (hg : IsLocallyBoundedPshOn A (fun z => f (σ z))) :
    MongeAmpere.canonicalBedfordTaylorMeasure A (fun z => f (σ z)) hg =
      ((MongeAmpere.canonicalBedfordTaylorMeasure B f hf).restrict B).map φ :=
  IsBTLimit.unique (isBTLimit_canonicalBedfordTaylorMeasure hg)
    ((isBTLimit_canonicalBedfordTaylorMeasure hf).comp_biholomorphic (isBiholomorphicPair_swap hφ))

/-- **Restricted test masses through a holomorphic parametrization of a chart domain.** -/
theorem restrictedTestMass_eq_of_param (Θ : ClosedRealOneOneForm N 𝒳) {j : V → 𝒳}
    (hj : ContMDiff 𝓘(ℂ, ComplexModel (k + 1)) 𝓘(ℂ, ComplexModel N) ∞ j) {u : V → EReal}
    (hu : IsThetaPshPotential (ClosedRealOneOneForm.pullback hj Θ).val u)
    (e : ComplexChart (k + 1) V) (A B : Opens (ComplexModel (k + 1)))
    {φ σ : ComplexModel (k + 1) → ComplexModel (k + 1)} (hφ : IsBiholomorphicPair B A φ σ)
    {P : ComplexModel (k + 1) → ℝ}
    (hP : IsSmoothLocalPotential (ClosedRealOneOneForm.pullback hj Θ).val e A P)
    {f : ComplexModel (k + 1) → ℝ} (hf : IsLocallyBoundedPshOn B f)
    (hfeq : ∀ y ∈ B, u (e.val.symm (φ y)) + (P (φ y) : EReal) = (f y : EReal))
    (ρ : 𝒳 → ℝ) (hρ0 : ∀ z, 0 ≤ ρ z)
    (hsupp : ∀ x, ρ (j x) ≠ 0 → x ∈ e.val.source ∧ e.val x ∈ A)
    {χ : ComplexModel (k + 1) → ℝ} (hχc : Continuous χ) {K : Set (ComplexModel (k + 1))}
    (hK : IsCompact K) (hKB : K ⊆ B) (hχK : ∀ y, y ∉ K → χ y = 0)
    (hχeq : ∀ y ∈ B, ρ (j (e.val.symm (φ y))) = χ y) :
    restrictedTestMass hj Θ u hu ρ =
      ENNReal.ofReal (∫ y, χ y ∂(MongeAmpere.canonicalBedfordTaylorMeasure B f hf)) := by
  classical
  let _ : MeasurableSpace V := borel V
  have _ : BorelSpace V := ⟨rfl⟩
  have hAB := (isBiholomorphicPair_swap hφ)
  -- the corrected potential on `A`
  have hg : IsLocallyBoundedPshOn A (fun z => f (σ z)) :=
    LocalCurrentPullbackDdc.isLocallyBoundedPshOn_comp hAB hf
  have hgeq : ∀ z ∈ A, chartFunction u e z + (P z : EReal) = ((fun z => f (σ z)) z : EReal) := by
    intro z hz
    have hy : σ z ∈ B := hφ.mapsTo_inv hz
    have h1 := hfeq (σ z) hy
    rw [hφ.right_inv z hz] at h1
    exact h1
  have hG : ∀ x, ENNReal.ofReal (ρ (j x)) ≠ 0 → x ∈ e.val.source ∧ e.val x ∈ A :=
    fun x hx => hsupp x fun h0 => hx (by rw [h0, ENNReal.ofReal_zero])
  unfold restrictedTestMass
  rw [lintegral_diagonalPotentialMeasure_eq_canonical _ hu e A hP hg hgeq _ hG]
  -- the transported test function on `A`
  set χ' : ComplexModel (k + 1) → ℝ := (A : Set (ComplexModel (k + 1))).indicator
    (fun z => χ (σ z)) with hχ'
  have hφc : ContinuousOn φ B := hφ.holo.continuousOn
  have hσc : ContinuousOn σ A := hφ.holo_inv.continuousOn
  have hKimg : IsCompact (φ '' K) := hK.image_of_continuousOn (hφc.mono hKB)
  have hKimgA : φ '' K ⊆ A := image_subset_iff.mpr fun y hy => hφ.mapsTo (hKB hy)
  have hsuppχ' : Function.support χ' ⊆ φ '' K := by
    intro z hz
    have hz' : χ' z ≠ 0 := hz
    by_cases hzA : z ∈ (A : Set (ComplexModel (k + 1)))
    · rw [hχ', indicator_of_mem hzA] at hz'
      refine ⟨σ z, ?_, hφ.right_inv z hzA⟩
      by_contra hK'
      exact hz' (hχK _ hK')
    · rw [hχ', indicator_of_notMem hzA] at hz'
      exact absurd rfl hz'
  have hχ'c : Continuous χ' := by
    refine continuous_of_continuousOn_of_tsupport_subset A.isOpen ?_
      ((closure_minimal hsuppχ' hKimg.isClosed).trans hKimgA)
    exact (hχc.comp_continuousOn hσc).congr fun z hz => indicator_of_mem hz _
  have hAe : ∀ᵐ z ∂(MongeAmpere.canonicalBedfordTaylorMeasure A (fun z => f (σ z)) hg),
      z ∈ (A : Set (ComplexModel (k + 1))) :=
    ae_iff.mpr (by
      have := MongeAmpere.canonicalBedfordTaylorMeasure_compl A (fun z => f (σ z)) hg
      simpa [compl_def] using this)
  rw [lintegral_congr_ae (hAe.mono fun z hz => by
    show ENNReal.ofReal (ρ (j (e.val.symm z))) = ENNReal.ofReal (χ' z)
    have h1 := hχeq (σ z) (hφ.mapsTo_inv hz)
    rw [hφ.right_inv z hz] at h1
    rw [h1, hχ', indicator_of_mem hz])]
  rw [canonicalBedfordTaylorMeasure_comp_eq_map hφ hf hg]
  have hφm : AEMeasurable φ ((MongeAmpere.canonicalBedfordTaylorMeasure B f hf).restrict B) :=
    hφc.aemeasurable B.isOpen.measurableSet
  rw [lintegral_map' (f := fun z => ENNReal.ofReal (χ' z))
    (ENNReal.measurable_ofReal.comp hχ'c.measurable).aemeasurable hφm]
  rw [setLIntegral_congr_fun B.isOpen.measurableSet (fun y hy => by
    show ENNReal.ofReal (χ' (φ y)) = ENNReal.ofReal (χ y)
    rw [hχ', indicator_of_mem (hφ.mapsTo hy), hφ.left_inv y hy])]
  have hBe : ∀ᵐ y ∂(MongeAmpere.canonicalBedfordTaylorMeasure B f hf),
      y ∈ (B : Set (ComplexModel (k + 1))) :=
    ae_iff.mpr (by
      have := MongeAmpere.canonicalBedfordTaylorMeasure_compl B f hf
      simpa [compl_def] using this)
  rw [Measure.restrict_eq_self_of_ae_mem hBe]
  have hχnn : ∀ y, 0 ≤ χ y := by
    intro y
    by_cases hy : y ∈ K
    · rw [← hχeq y (hKB hy)]
      exact hρ0 _
    · rw [hχK y hy]
  have hμK := MongeAmpere.canonicalBedfordTaylorMeasure_finiteOnCompacts hf hK hKB
  exact (ofReal_integral_eq_lintegral_ofReal
    (integrable_of_continuous_of_vanishing hχc hK hμK hχK) (Eventually.of_forall hχnn)).symm

end Param

end SGPT.Okounkov.TranscendentalWN
