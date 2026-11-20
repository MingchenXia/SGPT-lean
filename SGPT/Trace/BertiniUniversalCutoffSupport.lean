import SGPT.Trace.BertiniUniversalLocalMass
import SGPT.Trace.BertiniOriginalPreferredCutoffs

/-! Actual FULL affine-base compact cutoff support in ORIGINAL tangent
coordinates, manufactured from literal incidence closedness and compactness. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniUniversal
open Set Filter Metric
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Trace.Bertini

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  {φ : X → EReal} (c : SliceChart (d + 1) (p : X → ComplexProjectiveSpace N) φ)

def originalCutoffCoordinateSupport (C : Set (ComplexModel N)) (β : X → ℝ) : Set (ComplexModel (N + d)) :=
  (fun q : ComplexModel N × X => prodModelEquiv N d (q.1,originalMemberCoordinateDelete c.m (c.e.val q.2))) ''
    ((C ×ˢ tsupport β) ∩ affineIncidence p c.i)

theorem isCompact_originalCutoffCoordinateSupport
    {C : Set (ComplexModel N)} (hC : IsCompact C) (β : X → ℝ) (hβ : HasCompactSupport β)
    (hsource : ∀ ζ ∈ C, tsupport β ⊆ c.originalSliceAmbientSource ζ) :
    IsCompact (originalCutoffCoordinateSupport p c C β) := by
  let S := (C ×ˢ tsupport β) ∩ affineIncidence p c.i
  have hS : IsCompact S := (hC.prod hβ).inter_right (isClosed_originalAffineIncidence p c.i)
  have hchart : ContinuousOn (fun q : ComplexModel N × X => c.e.val q.2) S :=
    c.e.val.continuousOn.comp continuous_snd.continuousOn (fun q hq => (hsource q.1 hq.1.1 hq.1.2).1)
  have hcoords : ContinuousOn (fun q : ComplexModel N × X => originalMemberCoordinateDelete c.m (c.e.val q.2)) S :=
    (originalMemberCoordinateDelete c.m).continuous.comp_continuousOn hchart
  exact hS.image_of_continuousOn ((prodModelEquiv N d).continuous.comp_continuousOn
    (continuous_fst.continuousOn.prodMk hcoords))

theorem originalCutoffCoordinateSupport_subset_source
    {C : Set (ComplexModel N)} (hCb : C ⊆ ball c.ζ₀ c.r) (β : X → ℝ)
    (hsource : ∀ ζ ∈ C, tsupport β ⊆ c.originalSliceAmbientSource ζ) :
    originalCutoffCoordinateSupport p c C β ⊆ originalQSourceDomain p c := by
  rintro _ ⟨q,hq,rfl⟩
  change (prodModelEquiv N d).symm (prodModelEquiv N d (q.1,originalMemberCoordinateDelete c.m (c.e.val q.2))) ∈
    ((ball c.ζ₀ c.r) ×ˢ c.tangentPatch)
  rw [ContinuousLinearEquiv.symm_apply_apply]
  exact ⟨hCb hq.1.1,(hsource q.1 hq.1.1 hq.1.2).2.2⟩

theorem originalPoint_mem_cutoffCoordinateSupport
    {C : Set (ComplexModel N)} (β : X → ℝ) (q : (ball c.ζ₀ c.r) × c.tangentPatch)
    (hζ : q.1.val ∈ C) (hβ : c.tangentPoint q ∈ tsupport β) :
    prodModelEquiv N d (q.1.val,q.2.val) ∈ originalCutoffCoordinateSupport p c C β := by
  have hd : originalMemberCoordinateDelete c.m (c.e.val (c.tangentPoint q)) = q.2.val := by
    rw [(c.tangentPoint_chart_coordinates q).2.1]
    ext j
    exact c.originalTangentCoordinateMap_succAbove q j
  refine ⟨(q.1.val,c.tangentPoint q),⟨⟨hζ,hβ⟩,c.tangentPoint_mem_member q⟩,?_⟩
  dsimp only
  rw [hd]

end SGPT.Trace.BertiniUniversal
