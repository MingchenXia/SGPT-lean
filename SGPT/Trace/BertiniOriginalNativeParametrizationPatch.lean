import SGPT.Trace.BertiniOriginalNativeParametrization

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace SGPT.Trace.Bertini.SliceChart

open Bundle Set Filter Metric
open scoped Manifold ContDiff Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace

variable {d N : ℕ} {Y : Type} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (d + 1)) Y] [IsComplexManifold (d + 1) Y]
  {p : Y → ComplexProjectiveSpace N} {φ : Y → EReal}
  (c : SliceChart (d + 1) p φ)

theorem contMDiffOn_originalMemberParameter
    (hp : ContMDiff 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) ∞ p)
    (q : (ball c.ζ₀ c.r) × c.tangentPatch)
    (hsm : IsSmoothMemberOfDim p hp (affinePoint c.i q.1.val) d) :
    letI := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ d) hsm.1
    letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ d) hsm.1
    ContMDiffOn 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel d) ∞ (c.originalMemberParameter q) c.tangentPatch := by
  let := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ d) hsm.1
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ d) hsm.1
  intro b hb
  have heq : c.originalMemberParameter q =ᶠ[𝓝 b] c.originalMemberParameter (q.1, ⟨b, hb⟩) := by
    filter_upwards [c.isOpen_tangentPatch.mem_nhds hb] with z hz
    rw [c.originalMemberParameter_apply q hz, c.originalMemberParameter_apply (q.1, ⟨b, hb⟩) hz]
  apply ContMDiffAt.contMDiffWithinAt
  have h : ContMDiffAt 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel d) ∞
      (c.originalMemberParameter (q.1, ⟨b, hb⟩)) b :=
    c.contMDiffAt_originalMemberParameter hp (q.1, ⟨b, hb⟩) hsm
  exact h.congr_of_eventuallyEq heq

end SGPT.Trace.Bertini.SliceChart
