import SGPT.Foundations.Analysis.Pending.SubgeodesicChartPotential

set_option autoImplicit false

/-!
# Slice versus joint regularization on the chart strip

`finiteGeodesic` regularizes the Perron slice supremum in the *space* variable
only, for each time separately.  The strip envelope of
`Pending.SubgeodesicChartPotential` regularizes the corrected competitor family
*jointly* in space and complexified time.  Xia's Proposition 4.1.3
(`xia-sgpt:page-0150`--`xia-sgpt:page-0152`) says the two agree.

This file proves the easy half of that identity, unconditionally, and records
it as an explicit sandwich:

  `sSup family  ≤  corrected finiteGeodesic  ≤  joint regularization`.

The left inequality is the definition of a regularization; the right one is
the general fact that regularizing in fewer variables gives a smaller
function.  What Proposition 4.1.3 adds is the reverse of the right-hand
inequality; it is proved in `Pending.FiniteGeodesicsJointUsc` from joint upper
semicontinuity of `sup*`, and with it
`Pending.finiteGeodesic_isSubgeodesicInterior_of_relativeFullMass` is proved.
-/

open Filter Set
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.StripSliceRegularization

open SGPT.Foundations.Analysis.FirstPass

noncomputable section

/-- Regularizing in fewer variables gives a smaller function: the upper
semicontinuous regularization of a slice is at most the slice of the joint
regularization. -/
theorem uscRegularization_slice_le {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (f : X × Y → EReal) (x : X) (y : Y) :
    uscRegularization (fun x' => f (x', y)) x ≤ uscRegularization f (x, y) := by
  refine le_iInf fun U => le_iInf fun hU => ?_
  have hcont : ContinuousAt (fun x' : X => (x', y)) x :=
    (continuous_id.prodMk continuous_const).continuousAt
  have hslice : (fun x' : X => (x', y)) ⁻¹' U ∈ 𝓝 x := hcont.preimage_mem_nhds hU
  refine (uscRegularization_le_localSup _ hslice).trans ?_
  exact iSup_le fun x' => iSup_le fun hx' =>
    le_iSup_of_le (x', y) (le_iSup_of_le hx' le_rfl)

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The raw supremum of the corrected competitor family, evaluated at a
point, is the corrected raw slice supremum. -/
theorem sSup_image_apply (theta : SmoothRealForm n M 2) (u₀ u₁ : M → EReal)
    (e : ComplexChart n M) (rho : ComplexModel n → ℝ)
    (p : ComplexModel n × ℂ) :
    sSup ((fun curve => subgeodesicChartFunction curve e rho) ''
        finiteGeodesicCompetitors theta u₀ u₁) p =
      subgeodesicChartFunction (finiteGeodesicSliceSupremum theta u₀ u₁) e rho p := by
  rw [← SubgeodesicChartPotential.iSup_subgeodesicChartFunction_apply
    theta u₀ u₁ e rho p]
  simp only [sSup_apply, iSup_subtype, iSup_image]

/-- The corrected chart representative of the Perron geodesic is the spatial
regularization of the corrected slice supremum. -/
theorem subgeodesicChartFunction_finiteGeodesic_apply
    (theta : SmoothRealForm n M 2) (u₀ u₁ : M → EReal)
    (e : ComplexChart n M) {W : Set (ComplexModel n)}
    {rho : ComplexModel n → ℝ} (hrho : IsSmoothLocalPotential theta e W rho)
    {z : ComplexModel n} (hz : z ∈ W) (tau : ℂ) :
    subgeodesicChartFunction (finiteGeodesic theta u₀ u₁) e rho (z, tau) =
      uscRegularization (fun z' => subgeodesicChartFunction
        (finiteGeodesicSliceSupremum theta u₀ u₁) e rho (z', tau)) z := by
  have hrhoc : ContinuousAt rho z :=
    ((hrho.2.2.1 z hz).contDiffAt (hrho.1.mem_nhds hz)).continuousAt
  have hRHS : (fun z' => subgeodesicChartFunction
      (finiteGeodesicSliceSupremum theta u₀ u₁) e rho (z', tau)) =
      fun z' => chartFunction (finiteGeodesicSliceSupremum theta u₀ u₁ tau.re)
        e z' + (rho z' : EReal) := rfl
  rw [hRHS, uscRegularization_add_coe_continuousAt_apply _ hrhoc,
    uscRegularization_chartFunction_apply _ e (hrho.2.1 hz)]
  rfl

/-- The raw corrected slice supremum lies below the corrected Perron
geodesic. -/
theorem sSup_image_le_subgeodesicChartFunction_finiteGeodesic
    (theta : SmoothRealForm n M 2) (u₀ u₁ : M → EReal)
    (e : ComplexChart n M) (rho : ComplexModel n → ℝ) :
    sSup ((fun curve => subgeodesicChartFunction curve e rho) ''
        finiteGeodesicCompetitors theta u₀ u₁) ≤
      subgeodesicChartFunction (finiteGeodesic theta u₀ u₁) e rho := by
  intro p
  rw [sSup_image_apply theta u₀ u₁ e rho p]
  exact add_le_add
    (le_uscRegularization (finiteGeodesicSliceSupremum theta u₀ u₁ p.2.re)
      (e.val.symm p.1)) le_rfl

/-- **The easy half of Xia's Proposition 4.1.3.**  The corrected Perron
geodesic is squeezed between the raw corrected competitor supremum and its
joint strip regularization. -/
theorem subgeodesicChartFunction_finiteGeodesic_le_strip_envelope
    (theta : SmoothRealForm n M 2) (u₀ u₁ : M → EReal)
    (e : ComplexChart n M) {W : Set (ComplexModel n)}
    {rho : ComplexModel n → ℝ} (hrho : IsSmoothLocalPotential theta e W rho)
    {p : ComplexModel n × ℂ} (hp : p.1 ∈ W) :
    subgeodesicChartFunction (finiteGeodesic theta u₀ u₁) e rho p ≤
      uscRegularization (sSup
        ((fun curve => subgeodesicChartFunction curve e rho) ''
          finiteGeodesicCompetitors theta u₀ u₁)) p := by
  obtain ⟨z, tau⟩ := p
  rw [subgeodesicChartFunction_finiteGeodesic_apply theta u₀ u₁ e hrho hp tau]
  refine le_trans (uscRegularization_mono (fun z' => ?_) z)
    (uscRegularization_slice_le _ z tau)
  exact le_of_eq (sSup_image_apply theta u₀ u₁ e rho (z', tau)).symm

end

end SGPT.Foundations.Analysis.Pending.StripSliceRegularization
