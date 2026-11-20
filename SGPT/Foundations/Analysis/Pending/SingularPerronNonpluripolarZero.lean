import SGPT.Foundations.Analysis.Pending.SingularMaximalNonpluripolarZero

set_option autoImplicit false

/-! # The actual extended-real singular Perron strip satisfies the non-pluripolar homogeneous equation -/

open Set TopologicalSpace

namespace SGPT.Foundations.Analysis.Pending.SingularPerronNonpluripolarZero

open FirstPass FiniteGeodesicMaximality SingularPerronBoundaryMaximality
  SingularMaximalNonpluripolarZero MongeAmpere

noncomputable section

/-- Genuine homeomorphism transport of actual closures, frontiers and PSH competitors preserves extended-real ordinary boundary maximality. -/
theorem IsBoundaryMaximalPshOn.comp_continuousLinearEquiv
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {U : Set F} {u : F → EReal} (hu : IsBoundaryMaximalPshOn U u) (L : E ≃L[ℂ] F) :
    IsBoundaryMaximalPshOn (L ⁻¹' U) (fun z => u (L z)) := by
  refine ⟨hu.1.preimage L.continuous,
    hu.2.1.comp_continuousLinearMap (L : E →L[ℂ] F), ?_⟩
  intro D hD hDc hDU v hv hvusc hvu z hz
  have hcl : closure (L '' D) = L '' closure D := (L.toHomeomorph.image_closure D).symm
  have hclU : closure (L '' D) ⊆ U := by
    rw [hcl]
    rintro y ⟨x, hx, rfl⟩
    exact hDU hx
  have hv' : PlurisubharmonicOn (fun y => v (L.symm y)) (L '' D) :=
    (hv.comp_continuousLinearMap (L.symm : F →L[ℂ] E)).mono (by
      rintro y ⟨x, hx, rfl⟩
      simpa using hx)
  have hvusc' : UpperSemicontinuousOn (fun y => v (L.symm y)) (closure (L '' D)) :=
    hvusc.comp L.symm.continuous.continuousOn (by
      rw [hcl]
      rintro y ⟨x, hx, rfl⟩
      simpa using hx)
  have hvu' : ∀ y ∈ frontier (L '' D), v (L.symm y) ≤ u y := by
    have hfr : frontier (L '' D) = L '' frontier D :=
      (L.toHomeomorph.image_frontier D).symm
    rw [hfr]
    rintro y ⟨x, hx, rfl⟩
    simpa using hvu x hx
  have h := hu.2.2 (L '' D) (L.toHomeomorph.isOpen_image.mpr hD)
    (hcl ▸ hDc.image L.continuous) hclU (fun y => v (L.symm y)) hv' hvusc' hvu'
    (L z) ⟨z, hz, rfl⟩
  simpa using h

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]

/-- The actual corrected model potential remains extended real, preserving poles. -/
def erealModelChartFunction (curve : ℝ → M → EReal) (e : ComplexChart n M)
    (ρ : ComplexModel n → ℝ) : ComplexModel (n + 1) → EReal :=
  fun q => subgeodesicChartFunction curve e ρ (stripModelEquiv n q)

variable [IsComplexManifold n M] [CompactSpace M]

/-- Actual Perron ordinary boundary maximality transports to its actual extended-real model strip potential. -/
theorem isBoundaryMaximalPshOn_erealModel_finiteGeodesic
    {θ : SmoothRealForm n M 2} {u₀ u₁ : M → EReal}
    (hsub : IsSubgeodesicFrom θ (finiteGeodesic θ u₀ u₁) u₀ u₁)
    (e : ComplexChart n M) {W : Set (ComplexModel n)} {ρ : ComplexModel n → ℝ}
    (hρ : IsSmoothLocalPotential θ e W ρ)
    (hpsh : PlurisubharmonicOn (subgeodesicChartFunction (finiteGeodesic θ u₀ u₁) e ρ)
      (geodesicChartDomain W)) :
    IsBoundaryMaximalPshOn (modelStripOpens W hρ.1 : Set (ComplexModel (n + 1)))
      (erealModelChartFunction (finiteGeodesic θ u₀ u₁) e ρ) :=
  IsBoundaryMaximalPshOn.comp_continuousLinearEquiv
    (isBoundaryMaximalPshOn_finiteGeodesic hsub e hρ hpsh) (stripModelEquiv n)

/-- The genuine actual singular Perron strip has zero selected non-pluripolar measure in its actual model chart. -/
theorem truncationLimitMeasure_erealModel_finiteGeodesic_eq_zero
    {θ : SmoothRealForm n M 2} {u₀ u₁ : M → EReal}
    (hsub : IsSubgeodesicFrom θ (finiteGeodesic θ u₀ u₁) u₀ u₁)
    (e : ComplexChart n M) {W : Set (ComplexModel n)} {ρ : ComplexModel n → ℝ}
    (hρ : IsSmoothLocalPotential θ e W ρ)
    (hpsh : PlurisubharmonicOn (subgeodesicChartFunction (finiteGeodesic θ u₀ u₁) e ρ)
      (geodesicChartDomain W)) :
    truncationLimitMeasure (modelStripOpens W hρ.1)
      (erealModelChartFunction (finiteGeodesic θ u₀ u₁) e ρ)
      (isBoundaryMaximalPshOn_erealModel_finiteGeodesic hsub e hρ hpsh).2.1 = 0 :=
  truncationLimitMeasure_eq_zero_of_boundaryMaximal (Nat.succ_pos n)
    (isBoundaryMaximalPshOn_erealModel_finiteGeodesic hsub e hρ hpsh)

/-- Actual subgeodesic witnesses internally give homogeneous singular model neighborhoods in every actual chart, with no PSH, maximality, or zero-measure input. -/
theorem exists_local_erealModel_finiteGeodesic_np_zero
    {θ : SmoothRealForm n M 2} {u₀ u₁ : M → EReal}
    (hsub : IsSubgeodesicFrom θ (finiteGeodesic θ u₀ u₁) u₀ u₁)
    (e : ComplexChart n M) {z : ComplexModel n} (hz : z ∈ e.val.target) :
    ∃ (W : Set (ComplexModel n)) (ρ : ComplexModel n → ℝ)
      (hρ : IsSmoothLocalPotential θ e W ρ), z ∈ W ∧
      IsBoundaryMaximalPshOn (modelStripOpens W hρ.1 : Set (ComplexModel (n + 1)))
        (erealModelChartFunction (finiteGeodesic θ u₀ u₁) e ρ) ∧
      ∀ hpsh : PlurisubharmonicOn (erealModelChartFunction (finiteGeodesic θ u₀ u₁) e ρ)
        (modelStripOpens W hρ.1),
        truncationLimitMeasure (modelStripOpens W hρ.1)
          (erealModelChartFunction (finiteGeodesic θ u₀ u₁) e ρ) hpsh = 0 := by
  obtain ⟨W, ρ, hzW, hρ, hpsh⟩ := hsub.2.2.1.complexified_psh e hz
  refine ⟨W, ρ, hρ, hzW, isBoundaryMaximalPshOn_erealModel_finiteGeodesic hsub e hρ hpsh, ?_⟩
  intro _
  exact truncationLimitMeasure_erealModel_finiteGeodesic_eq_zero hsub e hρ hpsh

end

end SGPT.Foundations.Analysis.Pending.SingularPerronNonpluripolarZero
