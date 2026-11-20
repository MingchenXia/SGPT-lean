import SGPT.Foundations.Analysis.Pending.SubgeodesicSupremumEndpoints
import SGPT.Foundations.Analysis.Pending.ThetaPshDominatedL1
import SGPT.Foundations.Analysis.Pending.SubgeodesicInfimumThetaPsh

/-!
# Perron stability of subgeodesics

The slice-wise spatially regularized supremum of a nonempty family of
subgeodesics with uniformly bounded-above endpoints joins the regularized
endpoint suprema. Interior closure and endpoint quasi-everywhere recovery
are actual producers. The genuine slice infimum of one family member gives
an integrable lower barrier for dominated endpoint L1 convergence.

Source: Xia, SGPT Proposition 4.1.3, PDF pages 0150--0152.
-/

set_option autoImplicit false

open Filter MeasureTheory Set
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SubgeodesicPerronStability

open FirstPass FirstPass.PositiveClasses

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- Actual chart-local L1 convergence at the left endpoint of the
arbitrary-family regularized supremum. -/
theorem manifoldL1LocallyTendsto_left_uscRegularization_iSup {ι : Type*} [Nonempty ι]
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    {curve : ι → ℝ → M → EReal} {u₀ u₁ : ι → M → EReal}
    (h : ∀ i, IsSubgeodesicFrom theta.val (curve i) (u₀ i) (u₁ i)) {C : ℝ}
    (h₀ : ∀ i x, u₀ i x ≤ (C : EReal)) (h₁ : ∀ i x, u₁ i x ≤ (C : EReal)) :
    ManifoldL1LocallyTendsto (n := n)
      (fun t => uscRegularization (fun x => ⨆ i, curve i t x)) (𝓝[>] (0 : ℝ))
      (uscRegularization (fun x => ⨆ i, u₀ i x)) := by
  classical
  let U : ℝ → M → EReal := fun t => uscRegularization (fun x => ⨆ i, curve i t x)
  let v₀ : M → EReal := uscRegularization (fun x => ⨆ i, u₀ i x)
  let i₀ : ι := Classical.choice inferInstance
  let w : M → EReal := SubgeodesicInfimum.sliceInfimum (curve i₀)
  have hC := SubgeodesicSupremumSlices.uniform_upper_bound_of_endpoint_bounds h h₀ h₁
  have hU : IsSubgeodesicInterior theta.val U :=
    SubgeodesicSupremumInterior.isSubgeodesicInterior_uscRegularization_iSup
      (fun i => (h i).interior) hC
  have hv₀ : IsThetaPshPotential theta.val v₀ :=
    SubgeodesicSupremumInterior.isThetaPshPotential_uscRegularization_iSup
      (fun i => (h i).left_endpoint) h₀
  have hw : IsThetaPshPotential theta.val w :=
    SubgeodesicInfimumThetaPsh.isThetaPshPotential_sliceInfimum (h i₀).interior
  have hwU : ∀ t ∈ Ioo (0 : ℝ) 1, w ≤ U t := by
    intro t ht x
    exact (iInf_le_of_le ⟨t, ht⟩ le_rfl).trans
      ((le_iSup (fun i => curve i t x) i₀).trans
        (le_uscRegularization (fun x => ⨆ i, curve i t x) x))
  have hUC : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x, U t x ≤ (C : EReal) := by
    intro t ht
    exact uscRegularization_le upperSemicontinuous_const
      (fun x => iSup_le fun i => hC i t ht x)
  have hQ := SubgeodesicSupremumEndpoints.leftLimit_uscRegularization_iSup_quasiEverywhereEq
    omega theta h h₀ h₁
  intro e K hK hKe
  rw [Filter.tendsto_iff_seq_tendsto]
  intro s hs
  let r : ℕ → ℝ := fun j => if s j ∈ Ioo (0 : ℝ) 1 then s j else 1 / 2
  have hrI : ∀ j, r j ∈ Ioo (0 : ℝ) 1 := by
    intro j
    dsimp [r]
    split_ifs with hj
    · exact hj
    · norm_num
  have hrs : r =ᶠ[atTop] s := by
    filter_upwards [hs.eventually (Ioo_mem_nhdsGT zero_lt_one)] with j hj
    simp [r, hj]
  have hrtime : Tendsto r atTop (𝓝[>] (0 : ℝ)) := hs.congr' hrs.symm
  have hlim : ∀ e' : ComplexChart n M, ∀ᵐ z ∂(volume.restrict e'.val.target),
      Tendsto (fun j => chartFunction (U (r j)) e' z) atTop
        (𝓝 (chartFunction v₀ e' z)) := by
    intro e'
    filter_upwards [hQ.ae_in_chart e' volume] with z hz
    change SubgeodesicEndpointLimits.leftLimit U (e'.val.symm z) = v₀ (e'.val.symm z) at hz
    have hpoint := (SubgeodesicEndpointLimits.tendsto_leftLimit hU (e'.val.symm z)).comp hrtime
    simpa only [chartFunction, Function.comp_def, hz] using hpoint
  have hrL1 := (ThetaPshDominatedL1.manifoldL1LocallyTendsto_of_ae_tendsto_of_bounds
    (fun j => hU.thetaPshPotential (hrI j)) hv₀ hw
    (fun j x => hUC _ (hrI j) x) (fun j => hwU _ (hrI j)) hlim) e K hK hKe
  apply hrL1.congr'
  filter_upwards [hrs] with j hj
  simp [Function.comp_apply, hj, U, v₀]

/-- The right endpoint L1 convergence is the left convergence of the
time-reversed family, transported by the one-sided time-reversal filter. -/
theorem manifoldL1LocallyTendsto_right_uscRegularization_iSup {ι : Type*} [Nonempty ι]
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    {curve : ι → ℝ → M → EReal} {u₀ u₁ : ι → M → EReal}
    (h : ∀ i, IsSubgeodesicFrom theta.val (curve i) (u₀ i) (u₁ i)) {C : ℝ}
    (h₀ : ∀ i x, u₀ i x ≤ (C : EReal)) (h₁ : ∀ i x, u₁ i x ≤ (C : EReal)) :
    ManifoldL1LocallyTendsto (n := n)
      (fun t => uscRegularization (fun x => ⨆ i, curve i t x)) (𝓝[<] (1 : ℝ))
      (uscRegularization (fun x => ⨆ i, u₁ i x)) := by
  have hleft := manifoldL1LocallyTendsto_left_uscRegularization_iSup omega theta
    (fun i => (h i).timeReversed) h₁ h₀
  simpa [timeReversedCurve] using hleft.comp tendsto_one_sub_nhdsLT_one

/-- **Xia, SGPT Proposition 4.1.3.** The regularized supremum of an arbitrary
nonempty family of subgeodesics joins the regularized endpoint suprema when
the endpoint families have a common finite upper bound. -/
theorem isSubgeodesicFrom_uscRegularization_iSup {ι : Type*} [Nonempty ι]
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    {curve : ι → ℝ → M → EReal} {u₀ u₁ : ι → M → EReal}
    (h : ∀ i, IsSubgeodesicFrom theta.val (curve i) (u₀ i) (u₁ i)) {C : ℝ}
    (h₀ : ∀ i x, u₀ i x ≤ (C : EReal)) (h₁ : ∀ i x, u₁ i x ≤ (C : EReal)) :
    IsSubgeodesicFrom theta.val
      (fun t => uscRegularization (fun x => ⨆ i, curve i t x))
      (uscRegularization (fun x => ⨆ i, u₀ i x))
      (uscRegularization (fun x => ⨆ i, u₁ i x)) :=
  ⟨SubgeodesicSupremumInterior.isThetaPshPotential_uscRegularization_iSup
      (fun i => (h i).left_endpoint) h₀,
    SubgeodesicSupremumInterior.isThetaPshPotential_uscRegularization_iSup
      (fun i => (h i).right_endpoint) h₁,
    SubgeodesicSupremumInterior.isSubgeodesicInterior_uscRegularization_iSup
      (fun i => (h i).interior)
      (SubgeodesicSupremumSlices.uniform_upper_bound_of_endpoint_bounds h h₀ h₁),
    manifoldL1LocallyTendsto_left_uscRegularization_iSup omega theta h h₀ h₁,
    manifoldL1LocallyTendsto_right_uscRegularization_iSup omega theta h h₀ h₁⟩

/-- Perron stability with separate existential finite upper bounds for the
two endpoint families, as in the source statement. -/
theorem isSubgeodesicFrom_uscRegularization_iSup_of_bounded_endpoints
    {ι : Type*} [Nonempty ι]
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    {curve : ι → ℝ → M → EReal} {u₀ u₁ : ι → M → EReal}
    (h : ∀ i, IsSubgeodesicFrom theta.val (curve i) (u₀ i) (u₁ i))
    (h₀ : ∃ C : ℝ, ∀ i x, u₀ i x ≤ (C : EReal))
    (h₁ : ∃ C : ℝ, ∀ i x, u₁ i x ≤ (C : EReal)) :
    IsSubgeodesicFrom theta.val
      (fun t => uscRegularization (fun x => ⨆ i, curve i t x))
      (uscRegularization (fun x => ⨆ i, u₀ i x))
      (uscRegularization (fun x => ⨆ i, u₁ i x)) := by
  obtain ⟨A, hA⟩ := h₀
  obtain ⟨B, hB⟩ := h₁
  exact isSubgeodesicFrom_uscRegularization_iSup omega theta h
    (C := max A B)
    (fun i x => (hA i x).trans (EReal.coe_le_coe_iff.mpr (le_max_left A B)))
    (fun i x => (hB i x).trans (EReal.coe_le_coe_iff.mpr (le_max_right A B)))

end

end SGPT.Foundations.Analysis.Pending.SubgeodesicPerronStability
