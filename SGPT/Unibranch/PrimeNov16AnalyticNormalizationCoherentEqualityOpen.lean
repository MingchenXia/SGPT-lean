import SGPT.Unibranch.PrimeNov16AnalyticNormalizationCoherentChartDictionary
import SGPT.Foundations.Analysis.Pending.HomogenizedGlueing

/-! Whole coherent equality on ONE original manifold open; no neighbourhood supplier.
Blueprint: prime-nov16-analytic-normalization-coherent-equality-open.tex. -/
set_option autoImplicit false
noncomputable section
open Set Filter TopologicalSpace
open scoped Topology
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationCoherentEqualityOpen
variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

theorem exists_open_coherent_inclusion (I J : GermIdeal n M) (hI : I.IsCoherent) (hJ : J.IsCoherent)
    (x : M) (hIJ : ∀ f,I.mem x f → J.mem x f) :
    ∃ U : Set M,IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U,∀ f,I.mem y f → J.mem y f := by
  obtain ⟨U,hU,hx,s,G,hG,hgen⟩ := hI x
  have hGx : ∀ i,I.mem x (G i) := fun i =>
    IdealWeightComparison.mem_of_isPresentation hU hx hG hgen i
  have he : ∀ᶠ y in 𝓝 x,∀ i,J.mem y (G i) :=
    eventually_all.mpr fun i => HomogenizedGlueing.eventually_mem hJ (hIJ _ (hGx i))
  obtain ⟨V,hVe,hV,hxV⟩ := mem_nhds_iff.mp he
  refine ⟨U ∩ V,hU.inter hV,⟨hx,hxV⟩,?_⟩
  intro y hy f hf
  obtain ⟨hfh,t,a,c,ha,hc,hfc⟩ := (hgen y hy.1 f).mp hf
  apply HomogenizedIdeal.mem_of_isInSpanAt hJ
  refine ⟨hfh,t,a,c,?_,hc,hfc⟩
  intro i
  obtain ⟨j,hj⟩ := ha i
  rw [← hj]
  exact hVe hy.2 j

theorem exists_open_coherent_equality (I J : GermIdeal n M) (hI : I.IsCoherent) (hJ : J.IsCoherent)
    (x : M) (hIJ : ∀ f,I.mem x f ↔ J.mem x f) :
    ∃ U : Set M,IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U,∀ f,I.mem y f ↔ J.mem y f := by
  obtain ⟨U,hU,hx,hUJ⟩ := exists_open_coherent_inclusion I J hI hJ x (fun f => (hIJ f).mp)
  obtain ⟨V,hV,hxV,hVI⟩ := exists_open_coherent_inclusion J I hJ hI x (fun f => (hIJ f).mpr)
  exact ⟨U ∩ V,hU.inter hV,⟨hx,hxV⟩,fun y hy f => ⟨hUJ y hy.1 f,hVI y hy.2 f⟩⟩

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationCoherentEqualityOpen
