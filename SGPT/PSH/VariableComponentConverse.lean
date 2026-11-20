import SGPT.PSH.VariableComponentIrreducibility
import SGPT.PSH.VariableComponentLelong
import SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
import SGPT.Foundations.Analysis.FirstPass.RegularLocusDense

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH

open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff

/-- Actual preferred generators transported to any specified genuine native chart. -/
theorem nativeAnalytic_chartEquations {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {S : Set M} (hS : IsComplexAnalyticSubset (n := n) S) (e : ComplexChart n M) :
    ∀ z ∈ e.val.target,
      ∃ W : Set (ComplexModel n), IsOpen W ∧ z ∈ W ∧ W ⊆ e.val.target ∧
        ∃ (N : ℕ) (g : Fin N → ComplexModel n → ℂ),
          (∀ j, DifferentiableOn ℂ (g j) W) ∧
            ∀ y ∈ W, e.val.symm y ∈ S ↔ ∀ j, g j y = 0 := by
  intro z hz
  let p := e.val.symm z
  let d := complexChartAt (n := n) p
  obtain ⟨pres⟩ := hS p
  let T := chartTransition e d
  have hzT : z ∈ T.source := ⟨hz, mem_complexChartAt_source p⟩
  have hzV : T z ∈ pres.coordinateNeighborhood := pres.center_mem_coordinateNeighborhood
  let W := T.source ∩ T ⁻¹' pres.coordinateNeighborhood
  refine ⟨W, T.continuousOn.isOpen_inter_preimage T.open_source
    pres.isOpen_coordinateNeighborhood, ⟨hzT, hzV⟩,
    (fun y hy ↦ hy.1.1), pres.generatorCount,
    (fun j y ↦ pres.generator j (T y)), ?_, ?_⟩
  · intro j
    apply (pres.generator_holomorphic j).comp ?_ (fun y hy ↦ hy.2)
    intro y hy
    exact ((HolomorphicMaps.chartTransition_contDiffAt e d hy.1).differentiableAt
      (by simp)).differentiableWithinAt
  · intro y hy
    exact pres.zeroLocus hy.1.2 hy.2

namespace VariableComplexAtlas

universe u
variable {X : Type u} [TopologicalSpace X] (A : VariableComplexAtlas X)

private def converseTransportChart {d n : ℕ} (e : OpenPartialHomeomorph X (ComplexModel d))
    (h : d = n) : OpenPartialHomeomorph X (ComplexModel n) := h ▸ e

private theorem componentImageEquations_subtypeRestr_cast {d n : ℕ}
    (e : OpenPartialHomeomorph X (ComplexModel d)) (hd : d = n)
    (U : Opens X) (hU : Nonempty U) (S : Set U)
    (hEq : ∀ z ∈ ((converseTransportChart e hd).subtypeRestr hU).target,
      ∃ W : Set (ComplexModel n), IsOpen W ∧ z ∈ W ∧
        W ⊆ ((converseTransportChart e hd).subtypeRestr hU).target ∧
        ∃ (N : ℕ) (g : Fin N → ComplexModel n → ℂ),
          (∀ j, DifferentiableOn ℂ (g j) W) ∧
            ∀ y ∈ W, ((converseTransportChart e hd).subtypeRestr hU).symm y ∈ S ↔
              ∀ j, g j y = 0) :
    ∀ z ∈ e.target, e.symm z ∈ U →
      ∃ W : Set (ComplexModel d), IsOpen W ∧ z ∈ W ∧ W ⊆ e.target ∧
        ∃ (N : ℕ) (g : Fin N → ComplexModel d → ℂ),
          (∀ j, DifferentiableOn ℂ (g j) W) ∧
            ∀ y ∈ W, e.symm y ∈ Subtype.val '' S ↔ ∀ j, g j y = 0 := by
  subst n
  intro z hz hzc
  have hzR : z ∈ (e.subtypeRestr hU).target := by
    rw [OpenPartialHomeomorph.subtypeRestr_def, OpenPartialHomeomorph.trans_target,
      Opens.openPartialHomeomorphSubtypeCoe_target]
    refine ⟨hz, ?_⟩
    change e.symm z ∈ (U : Set X)
    simpa using hzc
  obtain ⟨W, hW, hzW, hWt, N, g, hg, hzero⟩ := hEq z hzR
  refine ⟨W, hW, hzW, hWt.trans (e.subtypeRestr_target_subset hU), N, g, hg, ?_⟩
  intro y hy
  have hval := e.subtypeRestr_symm_apply hU (hWt hy)
  change ((e.subtypeRestr hU).symm y).val = e.symm y at hval
  rw [← hval]
  rw [← hzero y hy]
  constructor
  · rintro ⟨q, hq, heq⟩
    exact Subtype.val_injective heq ▸ hq
  · intro hq
    exact ⟨(e.subtypeRestr hU).symm y, hq, rfl⟩

/-- Genuine native analytic subsets have literal original equations after component inclusion. -/
theorem hasAnalyticChartEquations_componentImage [T2Space X] [ParacompactSpace X]
    (x : X) :
    letI := A.componentChartedSpace x
    letI := A.componentComplexManifold_of_paracompact x
    ∀ S : Set (A.componentOpen x), IsComplexAnalyticSubset (n := A.pointDimension x) S →
      A.HasAnalyticChartEquations (Subtype.val '' S) := by
  let := A.componentChartedSpace x
  let := A.componentComplexManifold_of_paracompact x
  intro S hS i z hz
  by_cases hcenter : (A.chart i).symm z ∈ connectedComponent x
  · let j : A.ComponentChartIndex x :=
      ⟨i, ⟨(A.chart i).symm z, (A.chart i).map_target hz, hcenter⟩⟩
    exact componentImageEquations_subtypeRestr_cast (A.chart i)
      (A.componentChartDimension x j) (A.componentOpen x) (A.componentNonempty x) S
      (nativeAnalytic_chartEquations hS (A.componentComplexChart x j)) z hz hcenter
  · refine ⟨(A.chart i).target ∩ (A.chart i).symm ⁻¹' (connectedComponent x)ᶜ,
      (A.chart i).isOpen_inter_preimage_symm isClosed_connectedComponent.isOpen_compl,
      ⟨hz, hcenter⟩, inter_subset_left, 1, (fun _ _ ↦ (1 : ℂ)),
      (fun _ ↦ differentiableOn_const _), ?_⟩
    intro y hy
    constructor
    · rintro ⟨q, _hq, heq⟩
      exact (hy.2 (heq ▸ q.property)).elim
    · intro hzero
      exact (one_ne_zero (hzero 0)).elim

variable {A}

/-- Literal original analytic irreducibility manufactures genuine native irreducibility. -/
theorem HasIrreducibleAnalyticChartEquations.componentIrreducible
    [T2Space X] [ParacompactSpace X] {F : Set X}
    (hF : A.HasIrreducibleAnalyticChartEquations F) {x : X} (hx : x ∈ F) :
    letI := A.componentChartedSpace x
    letI := A.componentComplexManifold_of_paracompact x
    IsComplexAnalyticallyIrreducible (n := A.pointDimension x)
      (Subtype.val ⁻¹' F : Set (A.componentOpen x)) := by
  let := A.componentChartedSpace x
  let := A.componentComplexManifold_of_paracompact x
  let D : Set (A.componentOpen x) := Subtype.val ⁻¹' F
  have hFC := hF.subset_connectedComponent hx
  have himage : Subtype.val '' D = F := by
    ext y
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact hq
    · intro hy
      exact ⟨⟨y, hFC hy⟩, hy, rfl⟩
  refine ⟨hF.1.componentAnalytic x, ⟨⟨x, mem_connectedComponent⟩, hx⟩, ?_⟩
  intro B C hB hC hBD hCD hsplit
  have hBsrc := A.hasAnalyticChartEquations_componentImage x B hB
  have hCsrc := A.hasAnalyticChartEquations_componentImage x C hC
  have hBF : Subtype.val '' B ⊆ F := by
    rintro y ⟨q, hq, rfl⟩
    exact hBD hq
  have hCF : Subtype.val '' C ⊆ F := by
    rintro y ⟨q, hq, rfl⟩
    exact hCD hq
  change D = B ∪ C at hsplit
  have hsplitSrc : F = Subtype.val '' B ∪ Subtype.val '' C := by
    rw [← himage, hsplit, image_union]
  rcases hF.2.2 _ _ hBsrc hCsrc hBF hCF hsplitSrc with hleft | hright
  · exact Or.inl ((Set.image_injective.mpr Subtype.val_injective)
      (himage.trans hleft))
  · exact Or.inr ((Set.image_injective.mpr Subtype.val_injective)
      (himage.trans hright))

/-- The native carrier record and realized regular dimension are internally manufactured. -/
theorem HasIrreducibleAnalyticChartEquations.exists_componentSubvariety
    [T2Space X] [ParacompactSpace X] {F : Set X}
    (hF : A.HasIrreducibleAnalyticChartEquations F) {x : X} (hx : x ∈ F) :
    letI := A.componentChartedSpace x
    letI := A.componentComplexManifold_of_paracompact x
    ∃ V : ClosedIrreducibleAnalyticSubvariety (A.pointDimension x) (A.componentOpen x),
      V.carrier = Subtype.val ⁻¹' F := by
  let := A.componentChartedSpace x
  let := A.componentComplexManifold_of_paracompact x
  have hirr := hF.componentIrreducible hx
  obtain ⟨p, hp⟩ := hirr.nonempty
  obtain ⟨y, _hy, k, hreg⟩ := RegularLocusDense.exists_regularAtDim_mem_nhds
    hirr.analytic hp (U := univ) (univ_mem)
  exact ⟨{ carrier := Subtype.val ⁻¹' F
           isClosed_carrier := (hF.1.isClosed A).preimage continuous_subtype_val
           irreducible_carrier := hirr
           dim := k
           dim_le := hreg.1
           regularLocus_nonempty := ⟨y, hreg⟩ }, rfl⟩

/-- Genuine attained minimum on the ENTIRE literal original irreducible analytic carrier. -/
theorem IsPSH.exists_sourceLelong_irreducible_minimum [T2Space X] [ParacompactSpace X]
    {u : X → EReal} (hu : A.IsPSH u) {F : Set X}
    (hF : A.HasIrreducibleAnalyticChartEquations F) :
    ∃ p ∈ F, A.sourceLelong u p = ⨅ q ∈ F, A.sourceLelong u q := by
  obtain ⟨x, hx⟩ := hF.2.1
  let := A.componentChartedSpace x
  let := A.componentComplexManifold_of_paracompact x
  obtain ⟨V, hV⟩ := hF.exists_componentSubvariety hx
  have hmeet : (V.carrier ∩ univ).Nonempty := by
    refine ⟨⟨x, mem_connectedComponent⟩, ?_, mem_univ _⟩
    rw [hV]
    exact hx
  obtain ⟨p, hp, hmin⟩ := hu.exists_sourceLelong_component_minimum x V univ isOpen_univ hmeet
  have hpF : p.val ∈ F := by
    have h := hp.1
    rwa [hV] at h
  have hFC := hF.subset_connectedComponent hx
  have hinf : (⨅ q : A.componentOpen x, ⨅ _ : q.val ∈ F, A.sourceLelong u q.val) =
      ⨅ q ∈ F, A.sourceLelong u q := by
    apply le_antisymm
    · refine le_iInf fun q ↦ le_iInf fun hq ↦ ?_
      exact iInf_le_of_le (⟨q, hFC hq⟩ : A.componentOpen x) (iInf_le_of_le hq le_rfl)
    · refine le_iInf fun q ↦ le_iInf fun hq ↦ ?_
      exact iInf_le_of_le q.val (iInf_le_of_le hq le_rfl)
  refine ⟨p.val, hpF, ?_⟩
  rw [hV] at hmin
  exact hmin.trans hinf

end VariableComplexAtlas
end SGPT.PSH
