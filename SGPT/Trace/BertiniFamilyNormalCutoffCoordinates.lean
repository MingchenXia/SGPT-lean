import SGPT.Trace.BertiniFamilyRealNormalCutoffs

/-! Actual compact normal-coordinate tests manufactured from genuine original compact cutoffs. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace
open SGPT.Trace.OTMargin

namespace SGPT.Trace.Bertini

variable {n k : ℕ} {Y : Type} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y] {W : Set Y}
  (F : FlatData n k Y W) (ψ : Y → ℝ)

def flatDataCoordinateCutoff (z : ComplexModel n) : ℝ := by
  classical
  exact if z ∈ F.flat.target then ψ (finv F z) else 0

theorem flatDataCoordinateCutoff_apply (q : Y) (hq : q ∈ F.ambSource) :
    flatDataCoordinateCutoff F ψ (fcoord F q) = ψ q := by
  classical
  unfold flatDataCoordinateCutoff
  rw [if_pos (fcoord_mem F hq),finv_fcoord F hq]

theorem flatDataCoordinateCutoff_support (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ F.ambSource) :
    tsupport (flatDataCoordinateCutoff F ψ) ⊆ fcoord F '' tsupport ψ ∧
      IsCompact (fcoord F '' tsupport ψ) ∧ (fcoord F '' tsupport ψ) ⊆ F.flat.target := by
  have hcoord : ContinuousOn (fcoord F) F.ambSource :=
    F.flat.continuousOn.comp (F.amb.val.continuousOn.mono (fun _ hx => hx.1)) (fun _ hx => hx.2)
  have hK : IsCompact (fcoord F '' tsupport ψ) := hψc.isCompact.image_of_continuousOn (hcoord.mono hψs)
  have hKt : (fcoord F '' tsupport ψ) ⊆ F.flat.target := by
    rintro _ ⟨q,hq,rfl⟩
    exact fcoord_mem F (hψs hq)
  have hsupp : Function.support (flatDataCoordinateCutoff F ψ) ⊆ fcoord F '' tsupport ψ := by
    classical
    intro z hz
    change flatDataCoordinateCutoff F ψ z ≠ 0 at hz
    have hzt : z ∈ F.flat.target := by
      by_contra h
      exact hz (if_neg h)
    refine ⟨finv F z,subset_tsupport ψ ?_,fcoord_finv F hzt⟩
    change ψ (finv F z) ≠ 0
    simpa only [flatDataCoordinateCutoff,if_pos hzt] using hz
  exact ⟨closure_minimal hsupp hK.isClosed,hK,hKt⟩

theorem flatDataCoordinateCutoff_continuous (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ F.ambSource) :
    Continuous (flatDataCoordinateCutoff F ψ) := by
  classical
  obtain ⟨hs,hK,hKt⟩ := flatDataCoordinateCutoff_support F ψ hψc hψs
  apply continuous_iff_continuousAt.mpr
  intro z
  by_cases hz : z ∈ F.flat.target
  · apply ((hψ.comp_continuousOn (continuousOn_finv F)).continuousAt
      (F.flat.open_target.mem_nhds hz)).congr_of_eventuallyEq
    filter_upwards [F.flat.open_target.mem_nhds hz] with y hy
    exact if_pos hy
  · have hzK : z ∉ fcoord F '' tsupport ψ := fun h => hz (hKt h)
    apply (continuousAt_const : ContinuousAt (fun _ : ComplexModel n => (0 : ℝ)) z).congr_of_eventuallyEq
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hzK] with y hy
    exact image_eq_zero_of_notMem_tsupport (fun h => hy (hs h))

theorem flatDataCoordinateCutoff_compactSupport (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ F.ambSource) :
    HasCompactSupport (flatDataCoordinateCutoff F ψ) := by
  obtain ⟨hs,hK,_⟩ := flatDataCoordinateCutoff_support F ψ hψc hψs
  exact hK.of_isClosed_subset (isClosed_tsupport _) hs

omit [IsComplexManifold n Y] in
theorem flatDataCoordinateCutoff_nonneg (hψ : ∀ q, 0 ≤ ψ q) (z : ComplexModel n) :
    0 ≤ flatDataCoordinateCutoff F ψ z := by
  classical
  unfold flatDataCoordinateCutoff
  split_ifs <;> first | exact hψ _ | exact le_rfl

omit [IsComplexManifold n Y] in
def flatDataCutoffReadback (χ : ComplexModel n → ℝ) (q : Y) : ℝ := by
  classical
  exact if q ∈ F.ambSource then χ (fcoord F q) else 0

theorem flatDataCutoffReadback_coordinateCutoff (hψs : tsupport ψ ⊆ F.ambSource) (q : Y) :
    flatDataCutoffReadback F (flatDataCoordinateCutoff F ψ) q = ψ q := by
  classical
  unfold flatDataCutoffReadback
  by_cases hq : q ∈ F.ambSource
  · rw [if_pos hq,flatDataCoordinateCutoff_apply F ψ q hq]
  · rw [if_neg hq]
    exact (image_eq_zero_of_notMem_tsupport (fun h => hq (hψs h))).symm

end SGPT.Trace.Bertini
namespace SGPT.Trace.BertiniFamilyCanonical

open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Trace.Bertini SGPT.Trace.BertiniPencilFamily SGPT.Trace.BertiniPencilNormal

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (a v : ComplexModel N) (U : TopologicalSpace.Opens (ComplexModel 1))
  (hsm : ∀ t : U, IsSmoothHypersurfaceMember (d + 1) p (affinePoint i (a - t.val 0 • v)))

theorem exists_family_finite_normal_coordinate_cutoffs (h0 : (0 : ComplexModel 1) ∈ U) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∃ (k : ℕ) (F : Fin k → FlatData (d + 1) d (familyIncidence p i a v U)
        {y | scalarParameter p i a v U y = 0}) (r : ℝ) (χ : Fin k → ComplexModel (d + 1) → ℝ),
      0 < r ∧ Metric.closedBall (0 : ComplexModel 1) r ⊆ U ∧
      IsCompact (familyClosedParameterCollar p i a v U r) ∧
      (∀ j, ∀ y ∈ (F j).ambSource, fcoord (F j) y (Fin.last d) = scalarParameter p i a v U y) ∧
      (∀ j, Continuous (χ j) ∧ HasCompactSupport (χ j) ∧ tsupport (χ j) ⊆ (F j).flat.target ∧ ∀ z, 0 ≤ χ j z) ∧
      (∀ q, (∑ j, flatDataCutoffReadback (F j) (χ j) q) ≤ 1) ∧
      ∀ q ∈ familyClosedParameterCollar p i a v U (r / 2), (∑ j, flatDataCutoffReadback (F j) (χ j) q) = 1 := by
  classical
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  obtain ⟨k,F,r,ψ,hr,hrU,hrK,hF,hψ,hψc,hψs,hsum,hone⟩ := exists_family_finite_real_normal_cutoffs p i a v U hsm h0
  let χ : Fin k → ComplexModel (d + 1) → ℝ := fun j => flatDataCoordinateCutoff (F j) (ψ j)
  have hread (j : Fin k) (q : familyIncidence p i a v U) : flatDataCutoffReadback (F j) (χ j) q = ψ j q :=
    flatDataCutoffReadback_coordinateCutoff (F j) (ψ j) (hψs j) q
  refine ⟨k,F,r,χ,hr,hrU,hrK,hF,?_,?_,?_⟩
  · intro j
    refine ⟨flatDataCoordinateCutoff_continuous (F j) (ψ j) (ψ j).contMDiff.continuous (hψc j) (hψs j),
      flatDataCoordinateCutoff_compactSupport (F j) (ψ j) (hψc j) (hψs j),?_,?_⟩
    · have h := flatDataCoordinateCutoff_support (F j) (ψ j) (hψc j) (hψs j)
      exact h.1.trans h.2.2
    · exact flatDataCoordinateCutoff_nonneg (F j) (ψ j) (hψ j)
  · intro q
    simpa only [hread] using hsum q
  · intro q hq
    simpa only [hread] using hone q hq

end SGPT.Trace.BertiniFamilyCanonical
