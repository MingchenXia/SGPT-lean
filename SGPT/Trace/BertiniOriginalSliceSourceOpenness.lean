import SGPT.Trace.BertiniPreferredSliceSource

/-! Actual joint full-parameter openness for the SAME original slice source. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.Bertini.SliceChart
open Set Filter Metric
open scoped Manifold ContDiff Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open ProductComplexManifold
open scoped ProductComplexManifold

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X]
  {p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞}
  {φ : X → EReal} (c : SliceChart (d + 1) (p : X → ComplexProjectiveSpace N) φ)

def originalSliceJointSource : TopologicalSpace.Opens (ComplexModel N × X) := by
  let A : Set (ComplexModel N × X) := univ ×ˢ c.e.val.source
  have hA : IsOpen A := isOpen_univ.prod c.e.val.open_source
  have hE : ContinuousOn (fun q : ComplexModel N × X => c.e.val q.2) A :=
    c.e.val.continuousOn.comp continuous_snd.continuousOn (fun _ hq => hq.2)
  have hArg : ContinuousOn (fun q : ComplexModel N × X => prodModelEquiv N (d + 1) (q.1,c.e.val q.2)) A :=
    (prodModelEquiv N (d + 1)).continuous.comp_continuousOn (continuous_fst.continuousOn.prodMk hE)
  have hDel : ContinuousOn (fun q : ComplexModel N × X => originalMemberCoordinateDelete c.m (c.e.val q.2)) A :=
    (originalMemberCoordinateDelete c.m).continuous.comp_continuousOn hE
  have hB : IsOpen {q : ComplexModel N × X | q.1 ∈ ball c.ζ₀ c.r} := isOpen_ball.preimage continuous_fst
  have hO := (hB.inter (hArg.isOpen_inter_preimage hA c.Φ.isOpen_source)).inter
    (hDel.isOpen_inter_preimage hA c.isOpen_tangentPatch)
  refine ⟨{q | q.1 ∈ ball c.ζ₀ c.r ∧ q.2 ∈ c.originalSliceAmbientSource q.1},?_⟩
  convert hO using 1
  ext q
  simp only [originalSliceAmbientSource,A,mem_inter_iff,mem_preimage,mem_prod,mem_univ,true_and]
  change (q.1 ∈ ball c.ζ₀ c.r ∧ q.2 ∈ c.e.val.source ∧
      prodModelEquiv N (d + 1) (q.1,c.e.val q.2) ∈ c.Φ.source ∧
      originalMemberCoordinateDelete c.m (c.e.val q.2) ∈ c.tangentPatch) ↔
    ((q.1 ∈ ball c.ζ₀ c.r ∧ q.2 ∈ c.e.val.source ∧
      prodModelEquiv N (d + 1) (q.1,c.e.val q.2) ∈ c.Φ.source) ∧
      q.2 ∈ c.e.val.source ∧ originalMemberCoordinateDelete c.m (c.e.val q.2) ∈ c.tangentPatch)
  tauto

end SGPT.Trace.Bertini.SliceChart
