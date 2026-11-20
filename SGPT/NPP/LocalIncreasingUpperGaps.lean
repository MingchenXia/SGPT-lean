import SGPT.NPP.Capacity2MonotoneLocal
import SGPT.Foundations.Analysis.Pending.QuasiPshAlmostEverywhereComparison

/-!
# The upper-gap half of revised increasing local-capacity convergence

Actual local quasi-psh regularity, monotonicity and chartwise Lebesgue-a.e.
convergence imply order everywhere on the original open domain. Hence every
upper source order gap is empty. No capacity convergence is an input.
This does not prove the remaining lower-gap capacity convergence.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.NPP

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.PSH.VariableComplexAtlas

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Source a.e. convergence of a directed net on an arbitrary original open
domain, measured by Lebesgue measure in each restricted coordinate chart. -/
def NetChartTendstoAEOn (U : Opens M) {I : Type*} [Preorder I]
    (φ : I → M → EReal) (φ₀ : M → EReal) : Prop :=
  ∀ e : ComplexChart n M,
    ∀ᵐ z ∂volume.restrict (e.val.target ∩ e.val.symm ⁻¹' (U : Set M)),
      Tendsto (fun i => φ i (e.val.symm z)) atTop (𝓝 (φ₀ (e.val.symm z)))

omit [IsComplexManifold n M] in
/-- Local quasi-psh functions retain their canonical a.e. representatives on
the actual open subset, without connectedness or compactness. -/
theorem le_of_local_chartAELE {U : Opens M} {u v : M → EReal}
    (hu : IsLocalQuasiPshOn (n := n) (U : Set M) u)
    (hv : IsLocalQuasiPshOn (n := n) (U : Set M) v)
    (hae : ∀ e : ComplexChart n M,
      ∀ᵐ z ∂volume.restrict (e.val.target ∩ e.val.symm ⁻¹' (U : Set M)),
        u (e.val.symm z) ≤ v (e.val.symm z)) :
    ∀ x ∈ (U : Set M), u x ≤ v x := by
  intro x hx
  let e : ComplexChart n M := complexChartAt (n := n) x
  have hxs : x ∈ e.val.source := mem_complexChartAt_source x
  have hDo : IsOpen (e.val.target ∩ e.val.symm ⁻¹' (U : Set M)) :=
    e.val.isOpen_inter_preimage_symm U.isOpen
  have hz : e.val x ∈ e.val.target ∩ e.val.symm ⁻¹' (U : Set M) := by
    refine ⟨e.val.map_source hxs, ?_⟩
    simpa only [mem_preimage, e.val.left_inv hxs] using hx
  have h := QuasiPshAlmostEverywhereComparison.le_of_ae_le (hu.1 e) hDo
    (hv.1 e).upperSemicontinuousOn volume (hae e) (e.val x) hz
  simpa only [chartFunction, e.val.left_inv hxs] using h

omit [IsComplexManifold n M] in
/-- Every term of an increasing local quasi-psh net lies below its local
quasi-psh a.e. limit, throughout the original domain. -/
theorem increasing_local_le_limit {U : Opens M} {I : Type*} [Preorder I]
    [IsDirected I (· ≤ ·)] {φ : I → M → EReal} {φ₀ : M → EReal}
    (hφ : ∀ i, IsLocalQuasiPshOn (n := n) (U : Set M) (φ i))
    (hφ₀ : IsLocalQuasiPshOn (n := n) (U : Set M) φ₀)
    (hmono : ∀ x ∈ (U : Set M), Monotone fun i => φ i x)
    (hae : NetChartTendstoAEOn (n := n) U φ φ₀) :
    ∀ i, ∀ x ∈ (U : Set M), φ i x ≤ φ₀ x := by
  intro i
  apply le_of_local_chartAELE (hφ i) hφ₀
  intro e
  have hDo : IsOpen (e.val.target ∩ e.val.symm ⁻¹' (U : Set M)) :=
    e.val.isOpen_inter_preimage_symm U.isOpen
  filter_upwards [hae e, ae_restrict_mem hDo.measurableSet] with z hz hzD
  exact (hmono (e.val.symm z) hzD.2).ge_of_tendsto hz i

/-- The upper order gaps in the increasing clause are literally empty on
the original open set; this includes common infinite poles. -/
theorem sourceCapacityUpperGap_eq_empty_of_monotone_aeOn
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {U : Opens M}
    {I : Type*} [Preorder I] [IsDirected I (· ≤ ·)]
    {φ : I → M → EReal} {φ₀ : M → EReal}
    (hφ : ∀ i, (ofFixedModel n M).IsThetaPSHOn θ (φ i) U)
    (hφ₀ : (ofFixedModel n M).IsThetaPSHOn θ φ₀ U)
    (hmono : ∀ x ∈ (U : Set M), Monotone fun i => φ i x)
    (hae : NetChartTendstoAEOn (n := n) U φ φ₀) {δ : ℝ} (hδ : 0 ≤ δ) (i : I) :
    sourceCapacityUpperGap U (fun x => φ i x.1) (fun x => φ₀ x.1) δ = ∅ := by
  have hle := increasing_local_le_limit
    (fun j => isLocalQuasiPshOn_of_isThetaPSHOn U.isOpen (hφ j))
    (isLocalQuasiPshOn_of_isThetaPSHOn U.isOpen hφ₀) hmono hae
  apply eq_empty_iff_forall_notMem.mpr
  rintro _ ⟨x, hx, rfl⟩
  have hc : φ₀ x.1 ≤ φ₀ x.1 + (δ : EReal) :=
    le_add_of_nonneg_right (EReal.coe_nonneg.mpr hδ)
  exact (not_lt_of_ge (hle i x.1 x.2)) (hc.trans_lt hx)

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

omit [BorelSpace M] in
/-- The upper-gap conclusion of revised `prop:mono_psh_cap` (2) holds on
every subset of U, not merely compact cores. The lower-gap conclusion remains
a separate obligation. -/
theorem sourceMonoPshCap_increasing_upper_locally
    (θc θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (U : Opens M)
    {I : Type*} [Preorder I] [IsDirected I (· ≤ ·)]
    {φ : I → M → EReal} {φ₀ : M → EReal}
    (hφ : ∀ i, (ofFixedModel n M).IsThetaPSHOn θ (φ i) U)
    (hφ₀ : (ofFixedModel n M).IsThetaPSHOn θ φ₀ U)
    (hmono : ∀ x ∈ (U : Set M), Monotone fun i => φ i x)
    (hae : NetChartTendstoAEOn (n := n) U φ φ₀) (K : Set M) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun i => sourceThetaCapacity θc
      (K ∩ sourceCapacityUpperGap U (fun x => φ i x.1) (fun x => φ₀ x.1) δ))
      atTop (𝓝 0) := by
  simp only [sourceCapacityUpperGap_eq_empty_of_monotone_aeOn hφ hφ₀ hmono hae hδ.le,
    inter_empty, sourceThetaCapacity_empty]
  exact tendsto_const_nhds

end SGPT.NPP
