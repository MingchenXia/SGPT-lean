import SGPT.Okounkov.SchemeLineBundleAnalyticTransitions
import SGPT.Foundations.Analysis.Pending.ChartPartition
import SGPT.Foundations.Analysis.Pending.BlanchardWeight
import SGPT.Foundations.Analysis.Pending.FactorizedWeightForm

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Okounkov

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open scoped Topology Manifold ContDiff

variable {X : Scheme} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f]

local instance structuralMetricPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance structuralMetricPointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n

/-- A structural Hermitian metric assigns a positive smooth squared frame
norm to every original local frame, with the actual original transition law. -/
structure SchemeLineBundleMetric (E : ClosedProjectiveEmbedding f) (L : X.Modules) where
  frameNormSq : ∀ {U : X.Opens}, LocalBundleFrame L U → SchemeComplexPoint f → ℝ
  smooth : ∀ {U : X.Opens} (α : LocalBundleFrame L U)
    (e : ComplexChart n (SchemeComplexPoint f)),
    ContDiffOn ℝ ∞ (fun z ↦ frameNormSq α (e.val.symm z))
      (e.val.target ∩ e.val.symm ⁻¹' (schemeComplexPointImage f ⁻¹' U))
  positive : ∀ {U : X.Opens} (α : LocalBundleFrame L U) (p : SchemeComplexPoint f),
    schemeComplexPointImage f p ∈ U → 0 < frameNormSq α p
  transition : ∀ {U V : X.Opens} (α : LocalBundleFrame L U) (β : LocalBundleFrame L V)
    (p : SchemeComplexPoint f), schemeComplexPointImage f p ∈ U →
    schemeComplexPointImage f p ∈ V → frameNormSq α p =
      Complex.normSq (schemeFrameTransition f n E α β p) * frameNormSq β p

/-- Finite smooth data manufactured subordinate to an original frame cover. -/
structure SchemeLineBundlePartition {L : X.Modules} (a : LineBundleAtlas L) where
  card : ℕ
  idx : Fin card → a.I
  part : Fin card → SchemeComplexPoint f → ℝ
  smooth : ∀ i (e : ComplexChart n (SchemeComplexPoint f)),
    ContDiffOn ℝ ∞ (fun z ↦ part i (e.val.symm z)) e.val.target
  nonneg : ∀ i p, 0 ≤ part i p
  support : ∀ i, tsupport (part i) ⊆ schemeComplexPointImage f ⁻¹' a.opens (idx i)
  sum_eq_one : ∀ p, ∑ i, part i p = 1

/-- The actual compact complex manifold supplies the finite partition;
no subordinate functions are supplied by the caller. -/
theorem exists_schemeLineBundlePartition (E : ClosedProjectiveEmbedding f)
    {L : X.Modules} (a : LineBundleAtlas L) : Nonempty (SchemeLineBundlePartition f n a) := by
  let := E.isSeparated
  let := E.quasiCompact
  let := schemeAnalyticTN_isComplexManifold f n
  let := E.analyticCompact
  let S : a.I → TopologicalSpace.Opens (SchemeComplexPoint f) := fun i ↦
    ⟨schemeComplexPointImage f ⁻¹' a.opens i,
      (a.opens i).isOpen.preimage (schemeComplexPointImage_continuous f)⟩
  obtain ⟨m, χ, idx, hsm, hnn, hs, _, hsum⟩ :=
    ChartPartition.exists_chartSmooth_partitionOfUnity (n := n) S
      (fun p ↦ a.covers (schemeComplexPointImage f p))
  exact ⟨⟨m, idx, χ, hsm, hnn, hs, hsum⟩⟩

namespace SchemeLineBundlePartition

variable {f n} {L : X.Modules} {a : LineBundleAtlas L}

/-- ONE partition glues squared norms simultaneously for every original frame. -/
def frameNormSq (P : SchemeLineBundlePartition f n a) (E : ClosedProjectiveEmbedding f)
    {U : X.Opens} (α : LocalBundleFrame L U) (p : SchemeComplexPoint f) : ℝ :=
  ∑ i, P.part i p * Complex.normSq (schemeFrameTransition f n E α (a.frame (P.idx i)) p)

theorem frameNormSq_nonneg (P : SchemeLineBundlePartition f n a)
    (E : ClosedProjectiveEmbedding f) {U : X.Opens} (α : LocalBundleFrame L U)
    (p : SchemeComplexPoint f) : 0 ≤ P.frameNormSq E α p := by
  exact Finset.sum_nonneg fun i _ ↦ mul_nonneg (P.nonneg i p) (Complex.normSq_nonneg _)

theorem frameNormSq_positive (P : SchemeLineBundlePartition f n a)
    (E : ClosedProjectiveEmbedding f) {U : X.Opens} (α : LocalBundleFrame L U)
    (p : SchemeComplexPoint f) (hp : schemeComplexPointImage f p ∈ U) :
    0 < P.frameNormSq E α p := by
  classical
  have hex : ∃ i, P.part i p ≠ 0 := by
    by_contra h
    push Not at h
    have hz : (∑ i, P.part i p) = 0 := Finset.sum_eq_zero fun i _ ↦ h i
    have hone := P.sum_eq_one p
    rw [hz] at hone
    exact zero_ne_one hone
  obtain ⟨i, hi⟩ := hex
  have hip : schemeComplexPointImage f p ∈ a.opens (P.idx i) :=
    P.support i (subset_tsupport _ hi)
  have hpos : 0 < P.part i p := lt_of_le_of_ne (P.nonneg i p) (Ne.symm hi)
  have hnorm : 0 < Complex.normSq (schemeFrameTransition f n E α (a.frame (P.idx i)) p) :=
    Complex.normSq_pos.mpr (schemeFrameTransition_ne_zero f n E α (a.frame (P.idx i)) p hp hip)
  exact lt_of_lt_of_le (mul_pos hpos hnorm)
    (Finset.single_le_sum (f := fun j ↦ P.part j p *
      Complex.normSq (schemeFrameTransition f n E α (a.frame (P.idx j)) p))
      (fun j _ ↦ mul_nonneg (P.nonneg j p) (Complex.normSq_nonneg _))
      (Finset.mem_univ i))

theorem frameNormSq_smooth (P : SchemeLineBundlePartition f n a)
    (E : ClosedProjectiveEmbedding f) {U : X.Opens} (α : LocalBundleFrame L U)
    (e : ComplexChart n (SchemeComplexPoint f)) :
    ContDiffOn ℝ ∞ (fun z ↦ P.frameNormSq E α (e.val.symm z))
      (e.val.target ∩ e.val.symm ⁻¹' (schemeComplexPointImage f ⁻¹' U)) := by
  let := E.isSeparated
  let := E.quasiCompact
  let := schemeAnalyticTN_isComplexManifold f n
  intro z hz
  refine ContDiffAt.contDiffWithinAt ?_
  unfold frameNormSq
  refine ContDiffAt.sum fun i _ ↦ ?_
  have hχ := (P.smooth i e).contDiffAt (e.val.open_target.mem_nhds hz.1)
  by_cases hs : e.val.symm z ∈ tsupport (P.part i)
  · have hip := P.support i hs
    refine hχ.mul (BlanchardWeight.BlanchardData.contDiffAt_normSq_comp ?_)
    have hU : IsOpen ((schemeComplexPointImage f ⁻¹' U) ∩
        (schemeComplexPointImage f ⁻¹' a.opens (P.idx i))) :=
      ((U.isOpen.preimage (schemeComplexPointImage_continuous f)).inter
        ((a.opens (P.idx i)).isOpen.preimage (schemeComplexPointImage_continuous f)))
    filter_upwards [(e.val.isOpen_inter_preimage_symm hU).mem_nhds ⟨hz.1, hz.2, hip⟩]
      with w hw
    exact FactorizedWeightForm.differentiableAt_comp_chart_symm e hw.1
      (schemeFrameTransition_holomorphicAt f n E α (a.frame (P.idx i))
        (e.val.symm w) hw.2.1 hw.2.2).mdifferentiableAt
  · have heq : (fun w ↦ P.part i (e.val.symm w) *
        Complex.normSq (schemeFrameTransition f n E α (a.frame (P.idx i)) (e.val.symm w)))
        =ᶠ[𝓝 z] fun _ ↦ (0 : ℝ) := by
      filter_upwards [(e.val.isOpen_inter_preimage_symm
        (isClosed_tsupport (P.part i)).isOpen_compl).mem_nhds ⟨hz.1, hs⟩] with w hw
      rw [image_eq_zero_of_notMem_tsupport hw.2, zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq heq

theorem frameNormSq_transition (P : SchemeLineBundlePartition f n a)
    (E : ClosedProjectiveEmbedding f) {U V : X.Opens}
    (α : LocalBundleFrame L U) (β : LocalBundleFrame L V) (p : SchemeComplexPoint f)
    (hpU : schemeComplexPointImage f p ∈ U) (hpV : schemeComplexPointImage f p ∈ V) :
    P.frameNormSq E α p = Complex.normSq (schemeFrameTransition f n E α β p) *
      P.frameNormSq E β p := by
  classical
  unfold frameNormSq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : P.part i p = 0
  · simp only [hi, zero_mul, mul_zero]
  · have hip := P.support i (subset_tsupport _ hi)
    rw [schemeFrameTransition_cocycle f n E α β (a.frame (P.idx i)) p hpU hpV hip,
      Complex.normSq_mul]
    ring

/-- A genuine positive smooth structural Hermitian metric manufactured
from the original atlas and ONE finite subordinate partition. -/
def toMetric (P : SchemeLineBundlePartition f n a) (E : ClosedProjectiveEmbedding f) :
    SchemeLineBundleMetric f n E L where
  frameNormSq := P.frameNormSq E
  smooth := P.frameNormSq_smooth E
  positive := P.frameNormSq_positive E
  transition := P.frameNormSq_transition E

end SchemeLineBundlePartition

/-- Existence of a structural metric takes only the original algebraic
frame atlas and projectivity, not a local metric or Chern certificate. -/
theorem exists_schemeLineBundleMetric (E : ClosedProjectiveEmbedding f)
    {L : X.Modules} (a : LineBundleAtlas L) : Nonempty (SchemeLineBundleMetric f n E L) := by
  obtain ⟨P⟩ := exists_schemeLineBundlePartition f n E a
  exact ⟨P.toMetric E⟩

/-- The fixed structural metric is chosen once, before any section or divisor. -/
def schemeLineBundleMetric (E : ClosedProjectiveEmbedding f)
    {L : X.Modules} (a : LineBundleAtlas L) : SchemeLineBundleMetric f n E L :=
  Classical.choice (exists_schemeLineBundleMetric f n E a)


end SGPT.Okounkov
