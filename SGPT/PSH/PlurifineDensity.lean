import SGPT.PSH.PlurifineManifold
import SGPT.PSH.Pluripolar
import SGPT.Foundations.Analysis.PlurisubharmonicAE

namespace SGPT.PSH
open Set TopologicalSpace MeasureTheory Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology

/-- Every nonempty actual fine-open set meets the complement of an actual
Haar-null set. No measurability of either original set is required. -/
theorem exists_mem_domainPlurifine_notMem_null {n : ℕ}
    (Ω : Opens (ComplexModel n)) {S : Set Ω}
    (hS : IsOpen[domainPlurifineTopology Ω] S) {x : Ω} (hx : x ∈ S)
    {Z : Set (ComplexModel n)} (μ : Measure (ComplexModel n)) [μ.IsAddHaarMeasure]
    (hZ : μ Z = 0) : ∃ z : Ω, z ∈ S ∧ z.val ∉ Z := by
  by_contra hno
  have hSZ (z : Ω) (hz : z ∈ S) : z.val ∈ Z := by
    by_contra hn
    exact hno ⟨z, hz, hn⟩
  obtain ⟨T, ⟨U, u, hU, hUΩ, hu, rfl⟩, hxT, hTS⟩ :=
    exists_sourcePlurifineBasis_subset Ω hS hx
  have hnull : ∀ᵐ z ∂μ, z ∉ Z := ae_iff.mpr (by simpa using hZ)
  have hae : ∀ᵐ z ∂μ.restrict U, u z ≤ (0 : EReal) := by
    filter_upwards [ae_restrict_of_ae hnull, ae_restrict_mem hU.measurableSet] with z hn hzU
    by_contra hle
    have hpos : (0 : EReal) < u z := lt_of_not_ge hle
    exact hn (hSZ ⟨z, hUΩ hzU⟩ (hTS ⟨hzU, hpos⟩))
  have hraw := raw_pshOn_of_identityAtlas hu
  have hle := hraw.le_of_ae_le hU upperSemicontinuousOn_const μ hae x.val hxT.1
  exact (not_lt_of_ge hle) hxT.2

/-- The actual complement of every Haar-null set is dense in the genuine
domain fine topology, including dimension zero. -/
theorem dense_domainPlurifine_compl_null {n : ℕ}
    (Ω : Opens (ComplexModel n)) {Z : Set (ComplexModel n)}
    (μ : Measure (ComplexModel n)) [μ.IsAddHaarMeasure] (hZ : μ Z = 0) :
    @Dense Ω (domainPlurifineTopology Ω) {z : Ω | z.val ∉ Z} := by
  apply (@dense_iff_inter_open Ω (domainPlurifineTopology Ω) _).mpr
  intro S hS hne
  obtain ⟨x, hx⟩ := hne
  obtain ⟨z, hzS, hzZ⟩ := exists_mem_domainPlurifine_notMem_null Ω hS hx μ hZ
  exact ⟨z, hzS, hzZ⟩

end SGPT.PSH

namespace SGPT.PSH.VariableComplexAtlas
open Set TopologicalSpace MeasureTheory
open SGPT.Foundations.Analysis.FirstPass
open scoped Topology
universe u
variable {X : Type u} [TopologicalSpace X] {A : VariableComplexAtlas X}

/-- Actual chart outer nullity and the exact fine basis give the entire
source pluripolar-complement density statement on the actual manifold. -/
theorem LocallyPluripolar.dense_plurifine_compl {Z : Set X}
    (hZ : A.LocallyPluripolar Z) : @Dense X A.plurifineTopology Zᶜ := by
  apply (@dense_iff_inter_open X A.plurifineTopology Zᶜ).mpr
  intro S hS hne
  obtain ⟨x, hx⟩ := hne
  obtain ⟨i, hi⟩ := A.cover x
  let z : A.chartDomain i := ⟨(A.chart i) x, (A.chart i).map_source hi⟩
  have hz : z ∈ (A.chartInverse i) ⁻¹' S := by
    change (A.chart i).symm ((A.chart i) x) ∈ S
    rwa [(A.chart i).left_inv hi]
  obtain ⟨w, hwS, hwZ⟩ := exists_mem_domainPlurifine_notMem_null
    (A.chartDomain i) ((A.isOpen_plurifine_iff S).mp hS i) hz volume
    (hZ.chart_volume_eq_zero i)
  refine ⟨A.chartInverse i w, hwS, ?_⟩
  intro hyZ
  exact hwZ ⟨w.property, hyZ⟩

/-- Exact source lma:pshfunfinitelocuspfdense in its original closure form. -/
theorem LocallyPluripolar.closure_plurifine_compl {Z : Set X}
    (hZ : A.LocallyPluripolar Z) : @closure X A.plurifineTopology Zᶜ = univ :=
  (@dense_iff_closure_eq X A.plurifineTopology Zᶜ).mp hZ.dense_plurifine_compl

end SGPT.PSH.VariableComplexAtlas
