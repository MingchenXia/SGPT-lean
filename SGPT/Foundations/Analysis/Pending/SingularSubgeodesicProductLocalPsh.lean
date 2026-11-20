import SGPT.Foundations.Analysis.Pending.SubgeodesicChartPotential
import SGPT.Foundations.Analysis.Pending.ProductComplexManifold
import SGPT.Foundations.Analysis.Pending.GlobalPotentialPullback
import SGPT.Foundations.Analysis.Pending.FiniteGeodesicMaximality
import SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData

set_option autoImplicit false

/-! # Actual joint extended-real strip PSH transported to every product-manifold chart -/

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.SingularSubgeodesicProductLocalPsh

open scoped ProductComplexManifold

open FirstPass FirstPass.HolomorphicMaps FirstPass.AnalyticGluingData
  ProductComplexManifold LocalPotentialPullback FiniteGeodesicMaximality

noncomputable section

variable {n : ℕ} {M T : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [TopologicalSpace T] [ChartedSpace (ComplexModel 1) T] [IsComplexManifold 1 T]

/-- The actual joint subgeodesic and a genuinely holomorphic local time coordinate produce actual localized first-projection theta-PSH on the product, retaining poles and the full local-potential tensor identity. -/
theorem thetaPlurisubharmonicOn_product_time_pullback
    {θ : SmoothRealForm n M 2} {U : ℝ → M → EReal}
    (hU : IsSubgeodesicInterior θ U) {V : Set T} (hV : IsOpen V) {τ : T → ℂ}
    (hτ : ∀ b : ComplexChart 1 T, DifferentiableOn ℂ (τ ∘ b.val.symm)
      (b.val.target ∩ b.val.symm ⁻¹' V))
    (htime : ∀ y ∈ V, (τ y).re ∈ Ioo (0 : ℝ) 1) :
    ThetaPlurisubharmonicOn (SmoothRealForm.pullback (contMDiff_fst (n := n) (m := 1) (X := M) (Y := T)) θ)
      (fun p : M × T => U (τ p.2).re p.1) (univ ×ˢ V) := by
  intro e z hz hzV
  let d : ComplexChart n M := complexChartAt (e.val.symm z).1
  have hzd : z ∈ coordinateDomain (Prod.fst : M × T → M) e d :=
    ⟨hz, mem_complexChartAt_source _⟩
  obtain ⟨W, ρ, hzW, hρ, hpsh⟩ :=
    hU.complexified_psh d (coordinateMap_mem_target hzd)
  let D := potentialDomain (Prod.fst : M × T → M) e d W
  let O : Set (ComplexModel (n + 1)) := e.val.target ∩ e.val.symm ⁻¹' (Prod.snd ⁻¹' V)
  have hD : IsOpen D := potentialDomain_isOpen (contMDiff_fst (n := n) (m := 1) (X := M) (Y := T)) e d hρ.1
  have hO : IsOpen O := e.val.continuousOn_symm.isOpen_inter_preimage
    e.val.open_target (hV.preimage continuous_snd)
  let R := D ∩ O
  have hR : IsOpen R := hD.inter hO
  have hzR : z ∈ R := ⟨⟨hzd, hzW⟩, hz, hzV.2⟩
  have hρR : IsSmoothLocalPotential (SmoothRealForm.pullback (contMDiff_fst (n := n) (m := 1) (X := M) (Y := T)) θ)
      e R (ρ ∘ coordinateMap Prod.fst e d) :=
    (isSmoothLocalPotential_pullback (contMDiff_fst (n := n) (m := 1) (X := M) (Y := T)) e hρ).mono hR inter_subset_left
  obtain ⟨a, -, b, hb, hab⟩ := e.property
  let b' : ComplexChart 1 T := ⟨b, hb⟩
  let Q : ComplexModel (n + 1) →L[ℂ] ComplexModel 1 :=
    (ContinuousLinearMap.snd ℂ (ComplexModel n) (ComplexModel 1)).comp
      (prodModelEquiv n 1).symm.toContinuousLinearMap
  have htime_eq : (fun q : ComplexModel (n + 1) => τ (e.val.symm q).2) =
      (τ ∘ b.symm) ∘ Q := by
    funext q
    rw [← hab, prodChart_symm_apply]
    rfl
  have hQmaps : MapsTo Q R (b.target ∩ b.symm ⁻¹' V) := by
    intro q hq
    have hqt : q ∈ (prodChart a b).target := hab ▸ hq.1.1.1
    rw [prodChart_target] at hqt
    refine ⟨hqt.2, ?_⟩
    have hqV := hq.2.2
    change (e.val.symm q).2 ∈ V at hqV
    rw [← hab, prodChart_symm_apply] at hqV
    exact hqV
  have htime_diff : DifferentiableOn ℂ
      (fun q : ComplexModel (n + 1) => τ (e.val.symm q).2) R := by
    rw [htime_eq]
    exact (hτ b').comp Q.differentiable.differentiableOn hQmaps
  have hspace_diff : DifferentiableOn ℂ (coordinateMap (Prod.fst : M × T → M) e d) R :=
    ((coordinateMap_contDiffOn (contMDiff_fst (n := n) (m := 1) (X := M) (Y := T)) e d).differentiableOn (by simp)).mono
      (fun _ hq => hq.1.1)
  let G : ComplexModel (n + 1) → ComplexModel (n + 1) := fun q =>
    (stripModelEquiv n).symm (coordinateMap Prod.fst e d q, τ (e.val.symm q).2)
  have hG : DifferentiableOn ℂ G R :=
    (stripModelEquiv n).symm.differentiable.comp_differentiableOn
      (hspace_diff.prodMk htime_diff)
  have hmaps : MapsTo G R (stripModelEquiv n ⁻¹' geodesicChartDomain W) := by
    intro q hq
    change stripModelEquiv n (G q) ∈ geodesicChartDomain W
    simp only [G, ContinuousLinearEquiv.apply_symm_apply]
    exact ⟨hq.1.2, htime (e.val.symm q).2 hq.2.2⟩
  have hpull := HolomorphicPullback.plurisubharmonicOn_comp_holomorphic hR hG hmaps
    (plurisubharmonicOn_comp_stripModelEquiv hpsh)
  refine ⟨R, ρ ∘ coordinateMap Prod.fst e d, hzR, hρR, ?_⟩
  intro q hq
  apply (hpull q hq).congr
  filter_upwards [hR.mem_nhds hq] with w hw
  change subgeodesicChartFunction U d ρ (stripModelEquiv n (G w)) =
    U (τ (e.val.symm w).2).re (e.val.symm w).1 +
      (ρ (coordinateMap Prod.fst e d w) : EReal)
  simp only [G, ContinuousLinearEquiv.apply_symm_apply, subgeodesicChartFunction, chartFunction]
  rw [show d.val.symm (coordinateMap Prod.fst e d w) = (e.val.symm w).1 from
    d.val.left_inv hw.1.1.2]

end

end SGPT.Foundations.Analysis.Pending.SingularSubgeodesicProductLocalPsh
