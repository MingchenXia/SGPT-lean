import SGPT.Foundations.Analysis.Pending.SingularPerronSymmetrization
import SGPT.Foundations.Analysis.Pending.SingularPerronUpperBound

set_option autoImplicit false

/-! # Actual extended-real ordinary boundary maximality of the singular Perron strip -/

open Set

namespace SGPT.Foundations.Analysis.Pending.SingularPerronBoundaryMaximality

open FirstPass FiniteGeodesicMaximality SingularPerronChartModification
  SingularPerronSymmetrization SingularPerronUpperBound

noncomputable section

/-- The actual ordinary-open boundary-comparison definition for actual extended-real PSH functions. -/
def IsBoundaryMaximalPshOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Ω : Set E) (u : E → EReal) : Prop :=
  IsOpen Ω ∧ PlurisubharmonicOn u Ω ∧
    ∀ (D : Set E), IsOpen D → IsCompact (closure D) → closure D ⊆ Ω →
      ∀ (v : E → EReal), PlurisubharmonicOn v D → UpperSemicontinuousOn v (closure D) →
        (∀ p ∈ frontier D, v p ≤ u p) → ∀ p ∈ D, v p ≤ u p

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

/-- Actual singular boundary competitors lie below the actual corrected Perron function, without a finite lower bound. -/
theorem finiteGeodesic_boundary_competitor_le
    {θ : SmoothRealForm n M 2} {u₀ u₁ : M → EReal}
    (hsub : IsSubgeodesicFrom θ (finiteGeodesic θ u₀ u₁) u₀ u₁)
    (e : ComplexChart n M) {W : Set (ComplexModel n)} {ρ : ComplexModel n → ℝ}
    (hρ : IsSmoothLocalPotential θ e W ρ)
    (hpsh : PlurisubharmonicOn (subgeodesicChartFunction (finiteGeodesic θ u₀ u₁) e ρ)
      (geodesicChartDomain W))
    {D : Set (ComplexModel n × ℂ)} (hD : IsOpen D)
    (hDc : IsCompact (closure D)) (hDW : closure D ⊆ geodesicChartDomain W)
    {v : ComplexModel n × ℂ → EReal}
    (hv : PlurisubharmonicOn v D) (hvusc : UpperSemicontinuousOn v (closure D))
    (hvu : ∀ p ∈ frontier D, v p ≤ subgeodesicChartFunction (finiteGeodesic θ u₀ u₁) e ρ p) :
    ∀ p ∈ D, v p ≤ subgeodesicChartFunction (finiteGeodesic θ u₀ u₁) e ρ p := by
  intro p hp
  obtain ⟨C, hC⟩ := exists_finiteGeodesic_uniform_upper_bound hsub.1 hsub.2.1
  have hV := isSubgeodesicFrom_symmetrized_boundaryModification hsub e hρ hpsh
    hD hDc hDW ⟨p, hp⟩ hv hvusc (fun q hq => hvu q hq.2) hC
  let F := boundaryModification (finiteGeodesic θ u₀ u₁) e ρ D v
  have hF : F (e.val.symm p.1) p.2 ≤ finiteGeodesic θ u₀ u₁ p.2.re (e.val.symm p.1) :=
    (le_symmetrizedCurve F (e.val.symm p.1) p.2).trans
      (subgeodesic_slice_le_finiteGeodesic hV p.2.re (e.val.symm p.1))
  have hpW := hDW (subset_closure hp)
  calc
    v p ≤ gluedMax D v (subgeodesicChartFunction (finiteGeodesic θ u₀ u₁) e ρ) p := by
      rw [gluedMax_eq_max hp]
      exact le_max_left _ _
    _ = stripChartFunction F e ρ p :=
      (corrected_boundaryModification_apply (finiteGeodesic θ u₀ u₁) e ρ D v p
        (hρ.2.1 hpW.1)).symm
    _ ≤ subgeodesicChartFunction (finiteGeodesic θ u₀ u₁) e ρ p :=
      add_le_add hF le_rfl

/-- The actual corrected singular Perron strip satisfies the source ordinary boundary maximality definition. -/
theorem isBoundaryMaximalPshOn_finiteGeodesic
    {θ : SmoothRealForm n M 2} {u₀ u₁ : M → EReal}
    (hsub : IsSubgeodesicFrom θ (finiteGeodesic θ u₀ u₁) u₀ u₁)
    (e : ComplexChart n M) {W : Set (ComplexModel n)} {ρ : ComplexModel n → ℝ}
    (hρ : IsSmoothLocalPotential θ e W ρ)
    (hpsh : PlurisubharmonicOn (subgeodesicChartFunction (finiteGeodesic θ u₀ u₁) e ρ)
      (geodesicChartDomain W)) :
    IsBoundaryMaximalPshOn (geodesicChartDomain W)
      (subgeodesicChartFunction (finiteGeodesic θ u₀ u₁) e ρ) := by
  refine ⟨isOpen_geodesicChartDomain hρ.1, hpsh, ?_⟩
  intro D hD hDc hDW v hv hvusc hvu
  exact finiteGeodesic_boundary_competitor_le hsub e hρ hpsh hD hDc hDW hv hvusc hvu

/-- Actual subgeodesic witnesses internally produce ordinary maximal corrected neighborhoods in every actual chart. -/
theorem exists_isBoundaryMaximalPshOn_finiteGeodesic
    {θ : SmoothRealForm n M 2} {u₀ u₁ : M → EReal}
    (hsub : IsSubgeodesicFrom θ (finiteGeodesic θ u₀ u₁) u₀ u₁)
    (e : ComplexChart n M) {z : ComplexModel n} (hz : z ∈ e.val.target) :
    ∃ (W : Set (ComplexModel n)) (ρ : ComplexModel n → ℝ),
      z ∈ W ∧ IsSmoothLocalPotential θ e W ρ ∧
      IsBoundaryMaximalPshOn (geodesicChartDomain W)
        (subgeodesicChartFunction (finiteGeodesic θ u₀ u₁) e ρ) := by
  obtain ⟨W, ρ, hzW, hρ, hpsh⟩ := hsub.2.2.1.complexified_psh e hz
  exact ⟨W, ρ, hzW, hρ, isBoundaryMaximalPshOn_finiteGeodesic hsub e hρ hpsh⟩

end

end SGPT.Foundations.Analysis.Pending.SingularPerronBoundaryMaximality
