import SGPT.PSH.HermitianComparisonGlobalOneFactor

/-!
# Actual compact coordinate localization of the original partition

Each original partition weight supplies a genuine scalar compact test.
An inner coordinate domain and a second cutoff are manufactured inside the
original correction patch. The restricted patches and the unchanged
manifold weights form another genuine global partition, before any
potential is chosen.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianComparisonGlobalOneFactor

open Set Metric Filter MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open ChartPartitionRelativeSupports
open Hermitian HermitianGlobalProducts
open scoped Topology ContDiff Distributions

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
  {omega : Background (m + 1) M}

/-- Exact chart-weight readback retains the full manifold support inside
the scalar test's original coordinate domain. -/
theorem support_in_test_domain (P : BackgroundPatch omega)
    (χ : M → ℝ) (hsupp : tsupport χ ⊆ P.geometry.source)
    {U : Opens (ComplexModel (m + 1))} (θ : 𝓓(U, ℝ))
    (hθ : ∀ z, θ z = chartWeight P.geometry.chart χ z) :
    tsupport χ ⊆ P.geometry.chart.val.source ∩ P.geometry.chart.val ⁻¹' U := by
  let e := P.geometry.chart
  have hImage : e.val '' Function.support χ ⊆ Function.support θ := by
    rintro _ ⟨x, hx, rfl⟩
    have hxs : x ∈ e.val.source := (hsupp (subset_tsupport χ hx)).1
    change θ (e.val x) ≠ 0
    rw [hθ, chartWeight, indicator_of_mem (e.val.map_source hxs), e.val.left_inv hxs]
    exact hx
  intro x hx
  have hxs : x ∈ e.val.source := (hsupp hx).1
  have htarget : e.val x ∈ tsupport θ :=
    closure_mono hImage (mem_closure_image (e.val.continuousAt hxs) hx)
  exact ⟨hxs, θ.tsupport_subset htarget⟩

/-- Geometric compact localization data only: original smooth weights,
original correction patches, real compact inner domains and scalar tests.
No current, measure, covariance or comparison conclusion is a field. -/
structure CompactPartition (omega : Background (m + 1) M) where
  outer : MixedCurrentPartition omega
  domain : Fin outer.count → Opens (ComplexModel (m + 1))
  relativelyCompact : ∀ i, RelativelyCompactIn (domain i) (outer.patch i).geometry.domain
  weight : ∀ i, 𝓓(domain i, ℝ)
  auxiliary : ∀ i, 𝓓(domain i, ℝ)
  weight_eq : ∀ i z, weight i z = chartWeight (outer.patch i).geometry.chart (outer.weight i) z
  auxiliary_one : ∀ i, ∀ᶠ z in 𝓝ˢ (tsupport (weight i)), auxiliary i z = 1

namespace CompactPartition

theorem domain_le_outer (C : CompactPartition omega) (i : Fin C.outer.count) :
    C.domain i ≤ (C.outer.patch i).geometry.domain :=
  subset_closure.trans (C.relativelyCompact i).2

/-- Restricting the original background correction gives the actual inner patch. -/
def patch (C : CompactPartition omega) (i : Fin C.outer.count) : BackgroundPatch omega where
  geometry := ⟨(C.outer.patch i).geometry.chart, C.domain i,
    fun _ hz => (C.outer.patch i).geometry.domain_le_target (C.domain_le_outer i hz)⟩
  correction := (C.outer.patch i).correction
  smooth := (C.outer.patch i).smooth.mono (C.domain_le_outer i)
  dominates := fun z hz v => (C.outer.patch i).dominates z (C.domain_le_outer i hz) v

/-- The original smooth manifold weights form a genuine partition on the
actual smaller correction patches. -/
def partition (C : CompactPartition omega) : MixedCurrentPartition omega where
  count := C.outer.count
  patch := C.patch
  weight := C.outer.weight
  smooth := C.outer.smooth
  nonneg := C.outer.nonneg
  supported := fun i => support_in_test_domain (C.outer.patch i) (C.outer.weight i)
    (C.outer.supported i) (C.weight i) (C.weight_eq i)
  sum_one := C.outer.sum_one

theorem weight_nonneg (C : CompactPartition omega) (i : Fin C.outer.count)
    (z : ComplexModel (m + 1)) : 0 ≤ C.weight i z := by
  rw [C.weight_eq, chartWeight]
  by_cases hz : z ∈ (C.outer.patch i).geometry.chart.val.target
  · rw [indicator_of_mem hz]
    exact C.outer.nonneg i _
  · rw [indicator_of_notMem hz]

theorem weight_eq_partition (C : CompactPartition omega) (i : Fin C.outer.count)
    (z : ComplexModel (m + 1)) :
    C.weight i z = chartWeight (C.partition.patch i).geometry.chart (C.partition.weight i) z :=
  C.weight_eq i z

end CompactPartition

variable [CompactSpace M]

/-- The compact Hermitian manifold manufactures this geometric compact
partition independently of all distinguished and mixed potentials. -/
theorem nonempty_compactPartition (omega : Background (m + 1) M) :
    Nonempty (CompactPartition omega) := by
  obtain ⟨D⟩ := nonempty_mixedCurrentPartition omega
  choose U hUV θ η hθ hη using fun i => exists_compact_partition_weight_tests
    (D.patch i) (D.weight i) (D.smooth i) (D.supported i)
  exact ⟨⟨D, U, hUV, θ, η, hθ, hη⟩⟩

end SGPT.PSH.HermitianComparisonGlobalOneFactor
