import SGPT.Okounkov.SchemeLineBundleStructuralMetric

/-! A genuine metric of the SAME original sheaf preserving prescribed
physical atlas weights. Blueprint: original-atlas-weighted-metric.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter
open SGPT.Okounkov
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open scoped Topology Manifold ContDiff

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)

local instance weightedMetricTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance weightedMetricCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n

variable {L : X.Modules} {a : LineBundleAtlas L}

/-- ONE true original partition, with genuine prescribed physical weights. -/
def atlasWeightedFrameNormSq (P : SchemeLineBundlePartition f n a)
    (w : a.I → SchemeComplexPoint f → ℝ) {U : X.Opens}
    (α : LocalBundleFrame L U) (p : SchemeComplexPoint f) : ℝ :=
  ∑ i, P.part i p *
    (Complex.normSq (schemeFrameTransition f n E α (a.frame (P.idx i)) p) * w (P.idx i) p)

private theorem weightedTerm_nonneg (P : SchemeLineBundlePartition f n a)
    (w : a.I → SchemeComplexPoint f → ℝ)
    (hw : ∀ i p, schemeComplexPointImage f p ∈ a.opens i → 0 < w i p)
    {U : X.Opens} (α : LocalBundleFrame L U) (p : SchemeComplexPoint f) (i : Fin P.card) :
    0 ≤ P.part i p *
      (Complex.normSq (schemeFrameTransition f n E α (a.frame (P.idx i)) p) * w (P.idx i) p) := by
  by_cases hi : P.part i p = 0
  · simp only [hi, zero_mul, le_refl]
  · exact mul_nonneg (P.nonneg i p) (mul_nonneg (Complex.normSq_nonneg _)
      (hw _ _ (P.support i (subset_tsupport _ hi))).le)

theorem atlasWeightedFrameNormSq_positive (P : SchemeLineBundlePartition f n a)
    (w : a.I → SchemeComplexPoint f → ℝ)
    (hw : ∀ i p, schemeComplexPointImage f p ∈ a.opens i → 0 < w i p)
    {U : X.Opens} (α : LocalBundleFrame L U) (p : SchemeComplexPoint f)
    (hp : schemeComplexPointImage f p ∈ U) :
    0 < atlasWeightedFrameNormSq f n E P w α p := by
  classical
  have hex : ∃ i, P.part i p ≠ 0 := by
    by_contra h
    push Not at h
    have hz : (∑ i, P.part i p) = 0 := Finset.sum_eq_zero fun i _ ↦ h i
    have hone := P.sum_eq_one p
    rw [hz] at hone
    exact zero_ne_one hone
  obtain ⟨i, hi⟩ := hex
  have hip := P.support i (subset_tsupport _ hi)
  have hnorm : 0 < Complex.normSq (schemeFrameTransition f n E α (a.frame (P.idx i)) p) :=
    Complex.normSq_pos.mpr (schemeFrameTransition_ne_zero f n E _ _ p hp hip)
  exact lt_of_lt_of_le (mul_pos (lt_of_le_of_ne (P.nonneg i p) (Ne.symm hi))
    (mul_pos hnorm (hw _ _ hip)))
      (Finset.single_le_sum (f := fun j ↦ P.part j p *
        (Complex.normSq (schemeFrameTransition f n E α (a.frame (P.idx j)) p) * w (P.idx j) p))
          (fun j _ ↦ weightedTerm_nonneg f n E P w hw α p j) (Finset.mem_univ i))

theorem atlasWeightedFrameNormSq_smooth (P : SchemeLineBundlePartition f n a)
    (w : a.I → SchemeComplexPoint f → ℝ)
    (hw : ∀ i (e : ComplexChart n (SchemeComplexPoint f)),
      ContDiffOn ℝ ∞ (fun z ↦ w i (e.val.symm z))
        (e.val.target ∩ e.val.symm ⁻¹' (schemeComplexPointImage f ⁻¹' a.opens i)))
    {U : X.Opens} (α : LocalBundleFrame L U) (e : ComplexChart n (SchemeComplexPoint f)) :
    ContDiffOn ℝ ∞ (fun z ↦ atlasWeightedFrameNormSq f n E P w α (e.val.symm z))
      (e.val.target ∩ e.val.symm ⁻¹' (schemeComplexPointImage f ⁻¹' U)) := by
  let := E.isSeparated
  let := E.quasiCompact
  let := schemeAnalyticTN_isComplexManifold f n
  intro z hz
  refine ContDiffAt.contDiffWithinAt ?_
  unfold atlasWeightedFrameNormSq
  refine ContDiffAt.sum fun i _ ↦ ?_
  have hχ := (P.smooth i e).contDiffAt (e.val.open_target.mem_nhds hz.1)
  by_cases hs : e.val.symm z ∈ tsupport (P.part i)
  · have hip := P.support i hs
    have hO : IsOpen (schemeComplexPointImage f ⁻¹' a.opens (P.idx i)) :=
      (a.opens (P.idx i)).isOpen.preimage (schemeComplexPointImage_continuous f)
    have hwsm := (hw (P.idx i) e).contDiffAt
      ((e.val.isOpen_inter_preimage_symm hO).mem_nhds ⟨hz.1, hip⟩)
    refine hχ.mul (ContDiffAt.mul ?_ hwsm)
    refine BlanchardWeight.BlanchardData.contDiffAt_normSq_comp ?_
    have hU : IsOpen ((schemeComplexPointImage f ⁻¹' U) ∩
        (schemeComplexPointImage f ⁻¹' a.opens (P.idx i))) :=
      (U.isOpen.preimage (schemeComplexPointImage_continuous f)).inter hO
    filter_upwards [(e.val.isOpen_inter_preimage_symm hU).mem_nhds ⟨hz.1, hz.2, hip⟩]
      with y hy
    exact FactorizedWeightForm.differentiableAt_comp_chart_symm e hy.1
      (schemeFrameTransition_holomorphicAt f n E α (a.frame (P.idx i))
        (e.val.symm y) hy.2.1 hy.2.2).mdifferentiableAt
  · have heq : (fun y ↦ P.part i (e.val.symm y) *
        (Complex.normSq (schemeFrameTransition f n E α (a.frame (P.idx i)) (e.val.symm y)) *
          w (P.idx i) (e.val.symm y))) =ᶠ[𝓝 z] fun _ ↦ (0 : ℝ) := by
      filter_upwards [(e.val.isOpen_inter_preimage_symm
        (isClosed_tsupport (P.part i)).isOpen_compl).mem_nhds ⟨hz.1, hs⟩] with y hy
      rw [image_eq_zero_of_notMem_tsupport hy.2, zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq heq

theorem atlasWeightedFrameNormSq_transition (P : SchemeLineBundlePartition f n a)
    (w : a.I → SchemeComplexPoint f → ℝ) {U V : X.Opens}
    (α : LocalBundleFrame L U) (β : LocalBundleFrame L V) (p : SchemeComplexPoint f)
    (hpU : schemeComplexPointImage f p ∈ U) (hpV : schemeComplexPointImage f p ∈ V) :
    atlasWeightedFrameNormSq f n E P w α p =
      Complex.normSq (schemeFrameTransition f n E α β p) *
        atlasWeightedFrameNormSq f n E P w β p := by
  classical
  unfold atlasWeightedFrameNormSq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : P.part i p = 0
  · simp only [hi, zero_mul, mul_zero]
  · have hip := P.support i (subset_tsupport _ hi)
    rw [schemeFrameTransition_cocycle f n E α β (a.frame (P.idx i)) p hpU hpV hip,
      Complex.normSq_mul]
    ring

/-- An actual metric on the SAME sheaf; the partition is manufactured internally. -/
def atlasWeightedMetric (a : LineBundleAtlas L) (w : a.I → SchemeComplexPoint f → ℝ)
    (hsm : ∀ i (e : ComplexChart n (SchemeComplexPoint f)),
      ContDiffOn ℝ ∞ (fun z ↦ w i (e.val.symm z))
        (e.val.target ∩ e.val.symm ⁻¹' (schemeComplexPointImage f ⁻¹' a.opens i)))
    (hpos : ∀ i p, schemeComplexPointImage f p ∈ a.opens i → 0 < w i p) :
    SchemeLineBundleMetric f n E L := by
  let P := Classical.choice (exists_schemeLineBundlePartition f n E a)
  exact
    { frameNormSq := atlasWeightedFrameNormSq f n E P w
      smooth := atlasWeightedFrameNormSq_smooth f n E P w hsm
      positive := atlasWeightedFrameNormSq_positive f n E P w hpos
      transition := atlasWeightedFrameNormSq_transition f n E P w }

/-- Compatible physical weights are retained EXACTLY in every original atlas frame. -/
theorem atlasWeightedMetric_frame (a : LineBundleAtlas L) (w : a.I → SchemeComplexPoint f → ℝ)
    (hsm : ∀ i (e : ComplexChart n (SchemeComplexPoint f)),
      ContDiffOn ℝ ∞ (fun z ↦ w i (e.val.symm z))
        (e.val.target ∩ e.val.symm ⁻¹' (schemeComplexPointImage f ⁻¹' a.opens i)))
    (hpos : ∀ i p, schemeComplexPointImage f p ∈ a.opens i → 0 < w i p)
    (hc : ∀ i j p, schemeComplexPointImage f p ∈ a.opens i →
      schemeComplexPointImage f p ∈ a.opens j →
        w i p = Complex.normSq (schemeFrameTransition f n E (a.frame i) (a.frame j) p) * w j p)
    (i : a.I) (p : SchemeComplexPoint f) (hp : schemeComplexPointImage f p ∈ a.opens i) :
    (atlasWeightedMetric f n E a w hsm hpos).frameNormSq (a.frame i) p = w i p := by
  classical
  let P := Classical.choice (exists_schemeLineBundlePartition f n E a)
  change (∑ j, P.part j p *
    (Complex.normSq (schemeFrameTransition f n E (a.frame i) (a.frame (P.idx j)) p) *
      w (P.idx j) p)) = w i p
  calc
    _ = ∑ j, P.part j p * w i p := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : P.part j p = 0
      · simp only [hj, zero_mul]
      · rw [← hc i (P.idx j) p hp (P.support j (subset_tsupport _ hj))]
    _ = w i p := by rw [← Finset.sum_mul, P.sum_eq_one p, one_mul]

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
