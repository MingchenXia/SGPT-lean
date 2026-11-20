import SGPT.Unibranch.PrimeNov16AnalyticNormalizationGraphFinite
import SGPT.Foundations.Analysis.Pending.GermParametrizationSets
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-! Actual compact-preimage properness for the SAME original denominator graph
projection, from internally spread monic equations and actual scalar root bounds.
Blueprint: prime-nov16-analytic-normalization-graph-proper.tex. -/
set_option autoImplicit false
noncomputable section
open Set Metric TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.GermParametrizationData
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationGraphProper
open PrimeNov16AnalyticNormalizationDenominatorGraph
open PrimeNov16AnalyticNormalizationGraphFinite

private theorem sourceBound_continuous {n k : ℕ} (U : Opens (ComplexModel n)) (C : Set U)
    (d : Fin k → ℕ) (a : Fin k → ℕ → ComplexModel n → ℂ)
    (ha : ∀ i j,j < d i → DifferentiableOn ℂ (a i j) U) :
    Continuous (fun x : C => ‖x.val.val‖ +
      ∑ i : Fin k,max 1 (∑ j ∈ Finset.range (d i),‖a i j x.val.val‖)) := by
  have hbase : Continuous (fun x : C => x.val.val) :=
    continuous_subtype_val.comp continuous_subtype_val
  apply hbase.norm.add
  apply continuous_finsetSum Finset.univ
  intro i hi
  apply continuous_const.max
  apply continuous_finsetSum (Finset.range (d i))
  intro j hj
  exact ((ha i j (Finset.mem_range.mp hj)).continuousOn.comp_continuous hbase
    (fun x => x.val.property)).norm

/-- Properness of the actual original SHEAF morphism is a theorem about its
SAME entire point map, with no incoming properness/compactness certificate. -/
theorem projection_isProperMap {n k : ℕ} (U : Opens (ComplexModel n)) {C : Set U}
    (hC : IsComplexAnalyticSubset (n := n) C)
    (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ)
    (hH : DifferentiableOn ℂ H U) (hG : ∀ i,DifferentiableOn ℂ (G i) U)
    (d : Fin k → ℕ) (a : Fin k → ℕ → ComplexModel n → ℂ)
    (ha : ∀ i j,j < d i → DifferentiableOn ℂ (a i j) U)
    (hmonic : ∀ x : C,H x.val.val ≠ 0 → ∀ i,
      monicEval (d i) (a i) x.val.val (G i x.val.val/H x.val.val) = 0) :
    IsProperMap (projection U hC H G hH hG).hom.left.base := by
  let S := graphClosure U C H G
  let f : S → C := (projection U hC H G hH hG).hom.left.base
  have hcont : Continuous f := by
    change Continuous (fun c : S =>
      (⟨basePoint U c.val,(graphClosure_subset_denominatorSet U hC H G hH hG c.property).1⟩ : C))
    exact ((((baseProjection n k).continuous.comp continuous_subtype_val).comp
      continuous_subtype_val).subtype_mk _).subtype_mk _
  change IsProperMap f
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨hcont,?_⟩
  intro K hK
  let F : C → ℝ := fun x => ‖x.val.val‖ +
    ∑ i : Fin k,max 1 (∑ j ∈ Finset.range (d i),‖a i j x.val.val‖)
  obtain ⟨R,hR⟩ := hK.bddAbove_image (sourceBound_continuous U C d a ha).continuousOn
  have hSc : IsClosed S := (graphClosure_analytic U hC H G hH hG).isClosed
  obtain ⟨D,hDc,hDS⟩ := isClosed_induced_iff.mp hSc
  let B : Set (ComplexModel n) := (fun x : C => x.val.val) '' K
  have hB : IsCompact B := hK.image (continuous_subtype_val.comp continuous_subtype_val)
  let L : Set (ComplexModel (n+k)) := D ∩ baseProjection n k ⁻¹' B
  have hLc : IsClosed L := hDc.inter (hB.isClosed.preimage (baseProjection n k).continuous)
  have hLnorm : ∀ v ∈ L,‖v‖ ≤
      ‖(EuclideanSpace.finAddEquivProd (𝕜 := ℂ) (n := n) (m := k)).symm.toContinuousLinearMap‖ * max R 0 := by
    intro v hv
    obtain ⟨x,hxK,hxv⟩ := hv.2
    have hvU : v ∈ wideDomain k U := by
      change baseProjection n k v ∈ U
      rw [← hxv]
      exact x.val.property
    let z : wideDomain k U := ⟨v,hvU⟩
    have hzS : z ∈ S := by
      rw [← hDS]
      exact hv.1
    have hFx : F x ≤ R := hR (mem_image_of_mem F hxK)
    have hsum : 0 ≤ ∑ i : Fin k,max 1 (∑ j ∈ Finset.range (d i),‖a i j x.val.val‖) :=
      Finset.sum_nonneg fun i _ => zero_le_one.trans (le_max_left _ _)
    have hbnd : ‖baseProjection n k v‖ ≤ R := by
      rw [← hxv]
      exact (le_add_of_nonneg_right hsum).trans hFx
    have hfbnd : ‖fibreProjection n k v‖ ≤ R := by
      have hcoords : ∀ i : Fin k,‖fibreProjection n k v i‖ ≤
          max 1 (∑ j ∈ Finset.range (d i),‖a i j x.val.val‖) := by
        intro i
        have ht := coordinate_bound_on_graphClosure U H G d a ha hmonic hzS i
        change ‖fibreProjection n k v i‖ ≤ max 1
          (∑ j ∈ Finset.range (d i),‖a i j (baseProjection n k v)‖) at ht
        rw [← hxv] at ht
        exact ht
      exact ((norm_le_sum_norm (fibreProjection n k v)).trans
        (Finset.sum_le_sum fun i _ => hcoords i)).trans
          ((le_add_of_nonneg_left (norm_nonneg x.val.val)).trans hFx)
    have hp : ‖(baseProjection n k v,fibreProjection n k v)‖ ≤ max R 0 :=
      max_le (hbnd.trans (le_max_left _ _)) (hfbnd.trans (le_max_left _ _))
    let E := EuclideanSpace.finAddEquivProd (𝕜 := ℂ) (n := n) (m := k)
    have hcoord : E v = (baseProjection n k v,fibreProjection n k v) := rfl
    calc ‖v‖ = ‖E.symm (baseProjection n k v,fibreProjection n k v)‖ := by
          rw [← hcoord,E.symm_apply_apply]
      _ ≤ ‖E.symm.toContinuousLinearMap‖ * ‖(baseProjection n k v,fibreProjection n k v)‖ :=
        E.symm.toContinuousLinearMap.le_opNorm _
      _ ≤ ‖E.symm.toContinuousLinearMap‖ * max R 0 :=
        mul_le_mul_of_nonneg_left hp (norm_nonneg _)
  have hL : IsCompact L :=
    (isCompact_closedBall (0 : ComplexModel (n+k))
      (‖(EuclideanSpace.finAddEquivProd (𝕜 := ℂ) (n := n) (m := k)).symm.toContinuousLinearMap‖ * max R 0)).of_isClosed_subset
      hLc (fun v hv => mem_closedBall_zero_iff.mpr (hLnorm v hv))
  have himage : (fun c : S => c.val.val) '' (f ⁻¹' K) = L := by
    ext v
    constructor
    · rintro ⟨c,hcK,rfl⟩
      refine ⟨?_,f c,hcK,?_⟩
      · have ht : c.val ∈ (Subtype.val ⁻¹' D : Set (wideDomain k U)) := by
          rw [hDS]
          exact c.property
        exact ht
      · rfl
    · intro hv
      obtain ⟨x,hxK,hxv⟩ := hv.2
      have hvU : v ∈ wideDomain k U := by
        change baseProjection n k v ∈ U
        rw [← hxv]
        exact x.val.property
      let z : wideDomain k U := ⟨v,hvU⟩
      have hzS : z ∈ S := by
        rw [← hDS]
        exact hv.1
      let c : S := ⟨z,hzS⟩
      have hfc : f c = x := by
        apply Subtype.ext
        apply Subtype.ext
        exact hxv.symm
      refine ⟨c,?_,rfl⟩
      change f c ∈ K
      rwa [hfc]
  have hcimage : IsCompact ((fun c : S => c.val.val) '' (f ⁻¹' K)) := himage.symm ▸ hL
  change IsCompact (f ⁻¹' K : Set S)
  rw [Subtype.isCompact_iff,Subtype.isCompact_iff]
  simpa only [Set.image_image,Function.comp_def] using hcimage

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationGraphProper
