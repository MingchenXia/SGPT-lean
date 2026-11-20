import SGPT.Trace.BertiniFamilyNormalCollar
import SGPT.Foundations.Analysis.Pending.NaturalHermitianRiemannianBundle
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-! Produced actual REAL smooth compact cutoffs on the original full incidence. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniFamilyCanonical

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Trace.Bertini SGPT.Trace.BertiniPencilFamily SGPT.Trace.BertiniPencilNormal SGPT.Trace.OTMargin

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (a v : ComplexModel N) (U : TopologicalSpace.Opens (ComplexModel 1))
  (hsm : ∀ t : U, IsSmoothHypersurfaceMember (d + 1) p (affinePoint i (a - t.val 0 • v)))

theorem exists_family_real_collar_cutoff (r : ℝ) (hr : 0 < r)
    (hrU : Metric.closedBall (0 : ComplexModel 1) r ⊆ U) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∃ ξ : ContMDiffMap 𝓘(ℝ, ComplexModel (d + 1)) 𝓘(ℝ) (familyIncidence p i a v U) ℝ ∞,
      (∀ q, 0 ≤ ξ q ∧ ξ q ≤ 1) ∧
      (∀ q ∈ familyClosedParameterCollar p i a v U (r / 2), ξ q = 1) ∧
      HasCompactSupport ξ ∧ tsupport ξ ⊆ {q | q.val.1.val ∈ Metric.ball (0 : ComplexModel 1) r} := by
  classical
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let : IsManifold 𝓘(ℝ, ComplexModel (d + 1)) ∞ (familyIncidence p i a v U) :=
    NaturalHermitianRiemannianBundle.real_smooth_manifold
  let : LocallyCompactSpace (familyIncidence p i a v U) :=
    ChartedSpace.locallyCompactSpace (ComplexModel (d + 1)) (familyIncidence p i a v U)
  let O : Set (familyIncidence p i a v U) := {q | q.val.1.val ∈ Metric.ball (0 : ComplexModel 1) r}
  have hO : IsOpen O := Metric.isOpen_ball.preimage
    (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val))
  have hK := isCompact_familyClosedParameterCollar p i a v U (r / 2)
    ((Metric.closedBall_subset_closedBall (by linarith)).trans hrU)
  have hKO : familyClosedParameterCollar p i a v U (r / 2) ⊆ O :=
    fun _ hq => Metric.closedBall_subset_ball (by linarith) hq
  obtain ⟨f,hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, ComplexModel (d + 1))
    hK.isClosed (fun _ : Unit => O) (fun _ => hO)
    (fun q hq => mem_iUnion.mpr ⟨(),hKO hq⟩)
  refine ⟨f (),?_,?_,?_,hf ()⟩
  · intro q
    refine ⟨f.nonneg () q,?_⟩
    simpa only [finsum_eq_sum_of_fintype,Fintype.sum_unique] using f.sum_le_one q
  · intro q hq
    simpa only [finsum_eq_sum_of_fintype,Fintype.sum_unique] using f.sum_eq_one hq
  · exact (isCompact_familyClosedParameterCollar p i a v U r hrU).of_isClosed_subset
      (isClosed_tsupport _) (fun q hq => Metric.ball_subset_closedBall (hf () hq))

theorem exists_family_finite_real_normal_cutoffs (h0 : (0 : ComplexModel 1) ∈ U) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∃ (k : ℕ) (F : Fin k → FlatData (d + 1) d (familyIncidence p i a v U)
        {y | scalarParameter p i a v U y = 0}) (r : ℝ)
      (ψ : Fin k → ContMDiffMap 𝓘(ℝ, ComplexModel (d + 1)) 𝓘(ℝ) (familyIncidence p i a v U) ℝ ∞),
      0 < r ∧ Metric.closedBall (0 : ComplexModel 1) r ⊆ U ∧
      IsCompact (familyClosedParameterCollar p i a v U r) ∧
      (∀ j, ∀ y ∈ (F j).ambSource, fcoord (F j) y (Fin.last d) = scalarParameter p i a v U y) ∧
      (∀ j q, 0 ≤ ψ j q) ∧ (∀ j, HasCompactSupport (ψ j)) ∧
      (∀ j, tsupport (ψ j) ⊆ (F j).ambSource) ∧
      (∀ q, (∑ j, ψ j q) ≤ 1) ∧
      ∀ q ∈ familyClosedParameterCollar p i a v U (r / 2), (∑ j, ψ j q) = 1 := by
  classical
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let : IsManifold 𝓘(ℝ, ComplexModel (d + 1)) ∞ (familyIncidence p i a v U) :=
    NaturalHermitianRiemannianBundle.real_smooth_manifold
  let : LocallyCompactSpace (familyIncidence p i a v U) :=
    ChartedSpace.locallyCompactSpace (ComplexModel (d + 1)) (familyIncidence p i a v U)
  obtain ⟨k,F,r,hr,hrU,hrK,hF,_hcent,hcover⟩ := exists_family_finite_normal_collar p i a v U hsm h0
  obtain ⟨ξ,hξ,hξone,hξc,hξs⟩ := exists_family_real_collar_cutoff p i a v U hsm r hr hrU
  obtain ⟨f,hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, ComplexModel (d + 1))
    hrK.isClosed (fun j => (F j).ambSource) (fun j => (F j).isOpen_ambSource) hcover
  let ψ : Fin k → ContMDiffMap 𝓘(ℝ, ComplexModel (d + 1)) 𝓘(ℝ) (familyIncidence p i a v U) ℝ ∞ :=
    fun j => ⟨fun q => ξ q * f j q,ξ.contMDiff.mul (f j).contMDiff⟩
  have hsum (q : familyIncidence p i a v U) : (∑ j, ψ j q) = ξ q := by
    change (∑ j, ξ q * f j q) = ξ q
    rw [← Finset.mul_sum]
    by_cases hq : q ∈ familyClosedParameterCollar p i a v U r
    · have h := f.sum_eq_one hq
      rw [finsum_eq_sum_of_fintype] at h
      rw [h,mul_one]
    · have hz : ξ q = 0 := image_eq_zero_of_notMem_tsupport (fun hs => hq (Metric.ball_subset_closedBall (hξs hs)))
      rw [hz,zero_mul]
  refine ⟨k,F,r,ψ,hr,hrU,hrK,hF,?_,?_,?_,?_,?_⟩
  · intro j q
    exact mul_nonneg (hξ q).1 (f.nonneg j q)
  · intro j
    exact hξc.mul_right
  · intro j
    exact tsupport_mul_subset_right.trans (hf j)
  · intro q
    rw [hsum]
    exact (hξ q).2
  · intro q hq
    rw [hsum]
    exact hξone q hq

end SGPT.Trace.BertiniFamilyCanonical
