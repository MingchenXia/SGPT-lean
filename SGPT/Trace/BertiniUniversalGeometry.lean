import SGPT.Trace.BertiniPencilFamily

/-! Actual full affine universal incidence: original literal subtype,
produced native complex atlas and actual holomorphic q/pi maps.
No member smoothness, excision, native geometry or output certificate. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniUniversal
open Set Filter Metric
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.RegularLocusDense
open SGPT.Foundations.Analysis.Pending.DerivativeIdeal
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Trace.Bertini SGPT.Trace.BertiniPencilFamily
open scoped ProductComplexManifold

variable {n N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1))

def affineIncidence : Set (ComplexModel N × X) :=
  {q | q.2 ∈ member p (affinePoint i q.1)}

def localEquation (j : Fin (N + 1)) (q : ComplexModel N × X) : ℂ :=
  pairing (affineLift i q.1) (affineLift j (affineChart j (p q.2)))

theorem holomorphicAt_localEquation (j : Fin (N + 1)) {q : ComplexModel N × X}
    (hq : p q.2 ∈ (affineChart j).source) :
    HolomorphicAt (N + n) (localEquation p i j) q := by
  have ht : ContMDiff 𝓘(ℂ, ComplexModel (N + n)) 𝓘(ℂ, ComplexModel N) ∞
      (Prod.fst : ComplexModel N × X → ComplexModel N) := contMDiff_fst
  change HolomorphicAt (N + n)
    (fun q : ComplexModel N × X => ∑ k, affineLift i q.1 k * affineLift j (affineChart j (p q.2)) k) q
  apply HolomorphicAt.sum Finset.univ
  intro k _
  have hleft : HolomorphicAt (N + n) (fun q : ComplexModel N × X => affineLift i q.1 k) q := by
    filter_upwards [] with q'
    exact (differentiable_affineLift_apply i k _).mdifferentiableAt.comp q'
      (ht.contMDiffAt.mdifferentiableAt (by simp))
  have hright : HolomorphicAt (N + n)
      (fun q : ComplexModel N × X => affineLift j (affineChart j (p q.2)) k) q :=
    (holomorphicAt_affineLift_affineChart_comp p p.contMDiff j k hq).comp_contMDiff (f := Prod.snd)
      (Eventually.of_forall fun _ =>
        (contMDiff_snd (n := N) (m := n) (X := ComplexModel N) (Y := X)).contMDiffAt)
  exact hleft.mul hright

omit [IsComplexManifold n X] in
theorem mem_affineIncidence_iff_localEquation (j : Fin (N + 1)) {q : ComplexModel N × X}
    (hq : p q.2 ∈ (affineChart j).source) :
    q ∈ affineIncidence p i ↔ localEquation p i j q = 0 := by
  change IsIncident (mk (affineLift i q.1) (affineLift_ne_zero i _)) (p q.2) ↔ _
  conv_lhs => rw [eq_mk_affineLift_affineChart j hq]
  exact isIncident_mk_mk_iff (affineLift_ne_zero i _) (affineLift_ne_zero j _)

theorem chartDeriv_product_horizontal {a : ℕ} {Y : Type} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel a) Y] [IsComplexManifold a Y]
    (c : ComplexChart a Y) (e : ComplexChart n X) {y : Y} {x : X}
    (hy : y ∈ c.val.source) (hx : x ∈ e.val.source) {F : Y × X → ℂ}
    (hF : HolomorphicAt (a + n) F (y,x)) (v : ComplexModel a) :
    chartDeriv (productComplexChart c e) (prodModelEquiv a n (v,0)) F (y,x) =
      chartDeriv c v (fun z => F (z,x)) y := by
  let b := productComplexChart c e
  let H : ComplexModel (a + n) → ℂ := F ∘ b.val.symm
  let J : ComplexModel a → ComplexModel (a + n) := fun z => prodModelEquiv a n (z,e.val x)
  have hsource : (y,x) ∈ b.val.source := by
    simpa only [b,productComplexChart,prodChart_source] using (show (y,x) ∈ c.val.source ×ˢ e.val.source from ⟨hy,hx⟩)
  have hH : DifferentiableAt ℂ H (b.val (y,x)) :=
    (eventually_differentiableAt_comp_symm b hsource hF).self_of_nhds
  have hJ : HasFDerivAt J
      ((prodModelEquiv a n : ComplexModel a × ComplexModel n →L[ℂ] ComplexModel (a + n)).comp
        ((ContinuousLinearMap.id ℂ (ComplexModel a)).prod (0 : ComplexModel a →L[ℂ] ComplexModel n)))
      (c.val y) :=
    (prodModelEquiv a n).hasFDerivAt.comp (c.val y)
      ((hasFDerivAt_id (c.val y)).prodMk (hasFDerivAt_const (e.val x) (c.val y)))
  have hpoint : J (c.val y) = b.val (y,x) := rfl
  have hcomp : H ∘ J = fun z => F (c.val.symm z,x) := by
    funext z
    simp only [H,J,b,productComplexChart,Function.comp_apply,prodChart_symm_apply,
      ContinuousLinearEquiv.symm_apply_apply,e.val.left_inv hx]
  have hd := hH.hasFDerivAt.comp (c.val y) hJ
  rw [hcomp] at hd
  have hv := congrArg (fun L : ComplexModel a →L[ℂ] ℂ => L v) hd.fderiv
  simpa only [chartDeriv,H,hpoint,Function.comp_def,ContinuousLinearEquiv.coe_coe,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,zero_apply,ContinuousLinearMap.id_apply,b] using hv.symm

omit [IsComplexManifold n X] in
theorem exists_parameter_deriv_localEquation (j : Fin (N + 1)) {q : ComplexModel N × X}
    (hq : q ∈ affineIncidence p i) (hqj : p q.2 ∈ (affineChart j).source) :
    ∃ (c : ComplexChart N (ComplexModel N)) (k : Fin N), q.1 ∈ c.val.source ∧
      chartDeriv c (EuclideanSpace.single k 1) (fun ζ => localEquation p i j (ζ,q.2)) q.1 ≠ 0 := by
  have hzero := (mem_affineIncidence_iff_localEquation p i j hqj).mp hq
  obtain ⟨k,hk⟩ := exists_succAbove_ne_zero_of_pairing_eq_zero (affineLift_ne_zero j _) hzero
  let c := complexChartAt (n := N) q.1
  refine ⟨c,k,mem_complexChartAt_source q.1,?_⟩
  have hfun : (fun ζ => localEquation p i j (ζ,q.2)) ∘ c.val.symm =
      fun ζ => pairing (affineLift j (affineChart j (p q.2))) (affineLift i ζ) := by
    funext ζ
    change pairing (affineLift i ζ) _ = _
    exact pairing_comm _ _
  rw [chartDeriv,hfun,(hasFDerivAt_pairing_affineLift _ i _).fderiv,hyperplaneLinearPart_apply]
  simpa using hk

theorem regularAtDim_affineIncidence {q : ComplexModel N × X} (hq : q ∈ affineIncidence p i) :
    RegularAtDim (n := N + n) (affineIncidence p i) q (N + n - 1) := by
  let j := chartIndex (p q.2)
  let W : Set (ComplexModel N × X) := {y | p y.2 ∈ (affineChart j).source}
  have hWo : IsOpen W := (affineChart j).open_source.preimage (p.contMDiff.continuous.comp continuous_snd)
  have hqW : q ∈ W := mem_affineChart_chartIndex (p q.2)
  have hreg := LocalGiraudTransform.regularAtDim_zeroSet hWo
    (fun y hy => holomorphicAt_localEquation p i j hy)
    (fun y hy hy0 => by
      have hym := (mem_affineIncidence_iff_localEquation p i j hy).mpr hy0
      obtain ⟨c,k,hc,hd⟩ := exists_parameter_deriv_localEquation p i j hym hy
      let e := complexChartAt (n := n) y.2
      have he : y.2 ∈ e.val.source := mem_complexChartAt_source y.2
      refine ⟨productComplexChart c e,prodModelEquiv N n (EuclideanSpace.single k 1,0),?_,?_⟩
      · simpa only [productComplexChart,prodChart_source] using (show y ∈ c.val.source ×ˢ e.val.source from ⟨hc,he⟩)
      · rw [chartDeriv_product_horizontal c e hc he (holomorphicAt_localEquation p i j hy)]
        exact hd)
    hqW ((mem_affineIncidence_iff_localEquation p i j hqW).mp hq)
  apply RegularPointDimension.regularAtDim_of_inter_eq hWo hqW ?_ hreg
  ext y
  simp only [mem_inter_iff,Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨hy0,hy⟩,_⟩
    exact ⟨(mem_affineIncidence_iff_localEquation p i j hy).mpr hy0,hy⟩
  · rintro ⟨hym,hy⟩
    exact ⟨⟨(mem_affineIncidence_iff_localEquation p i j hy).mp hym,hy⟩,hy⟩

@[instance_reducible] def affineChartedSpace : ChartedSpace (ComplexModel (N + n - 1)) (affineIncidence p i) :=
  SubmanifoldChartedSpace.chartedSpace (Nat.sub_le _ _)
    (fun _ hq => regularAtDim_affineIncidence p i hq)

theorem affineComplex :
    letI := affineChartedSpace p i
    IsComplexManifold (N + n - 1) (affineIncidence p i) :=
  SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.sub_le _ _)
    (fun _ hq => regularAtDim_affineIncidence p i hq)

theorem contMDiff_affineInclusion :
    letI := affineChartedSpace p i
    ContMDiff 𝓘(ℂ, ComplexModel (N + n - 1)) 𝓘(ℂ, ComplexModel (N + n)) ∞
      (Subtype.val : affineIncidence p i → ComplexModel N × X) :=
  SubmanifoldChartedSpace.contMDiff_val (Nat.sub_le _ _)
    (fun _ hq => regularAtDim_affineIncidence p i hq)

def nativeXMap :
    letI := affineChartedSpace p i
    letI := affineComplex p i
    ContMDiffMap 𝓘(ℂ, ComplexModel (N + n - 1)) 𝓘(ℂ, ComplexModel n) (affineIncidence p i) X ∞ := by
  let := affineChartedSpace p i
  let := affineComplex p i
  exact ⟨fun q => q.val.2,contMDiff_snd.comp (contMDiff_affineInclusion p i)⟩

def nativeParameterMap :
    letI := affineChartedSpace p i
    letI := affineComplex p i
    ContMDiffMap 𝓘(ℂ, ComplexModel (N + n - 1)) 𝓘(ℂ, ComplexModel N) (affineIncidence p i) (ComplexModel N) ∞ := by
  let := affineChartedSpace p i
  let := affineComplex p i
  exact ⟨fun q => q.val.1,contMDiff_fst.comp (contMDiff_affineInclusion p i)⟩

theorem contMDiffAt_affineIncidence_of_val {m : ℕ} {Y : Type} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel m) Y] [IsComplexManifold m Y]
    (f : Y → affineIncidence p i) (y : Y)
    (hf : ContMDiffAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel (N + n)) ∞ (fun z => (f z).val) y) :
    letI := affineChartedSpace p i
    letI := affineComplex p i
    ContMDiffAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel (N + n - 1)) ∞ f y := by
  let := affineChartedSpace p i
  let := affineComplex p i
  let G := SubmanifoldChartedSpace.FlatData.ofRegularAtDim
    (regularAtDim_affineIncidence p i (f y).property)
  have hgy : (f y).val ∈ G.ambSource := SubmanifoldChartedSpace.FlatData.mem_ambSource_ofRegularAtDim _
  have hchart : f y ∈ (chartAt (ComplexModel (N + n - 1)) (f y)).source := mem_chart_source _ _
  rw [contMDiffAt_iff_target_of_mem_source hchart]
  refine ⟨tendsto_subtype_rng.mpr hf.continuousAt,?_⟩
  change ContMDiffAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel (N + n - 1)) ∞
    (fun z => coordinateProjection (N + n) (N + n - 1) (G.flat (G.amb.val (f z).val))) y
  have hfa := (contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas G.amb.property) hgy.1).comp y hf
  have hfb := (contDiffAt_of_differentiableOn_complex G.differentiableOn_flat G.flat.open_source hgy.2).contMDiffAt
  exact (coordinateProjection (N + n) (N + n - 1)).contDiff.contMDiff.contMDiffAt.comp y (hfb.comp y hfa)

end SGPT.Trace.BertiniUniversal
