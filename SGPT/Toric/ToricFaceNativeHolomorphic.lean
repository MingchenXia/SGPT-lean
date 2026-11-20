import SGPT.Toric.ToricFaceNativeEmbedding
import SGPT.Foundations.Analysis.Pending.SubmanifoldCodRestrict

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Filter SGPT.AlmostSemigroup.Counting
open SGPT.Foundations.Analysis.FirstPass
open scoped Topology BigOperators Manifold ContDiff Classical
attribute [local instance] monomialProjectiveTopology
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- The actual homogeneous zero-coordinate embedding of the original toric
face model is holomorphic into the SAME original ambient native manifold.
Analytic whole polynomial representatives and genuine nonzero vertex ratios
produce the proof; no compatible-atlas or holomorphy certificate is supplied. -/
theorem contMDiff_toricFaceNativeEmbedding (v : latticePolytopeVertices γ) (J : Set (Fin n)) :
    letI := originalPolytopeNativeChartedSpace (toricFaceProjectedFamily (hs := hs) v J)
      (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J)
    letI := originalPolytopeNativeChartedSpace γ hs
    ContMDiff 𝓘(ℂ, ComplexModel (toricFaceDimension J)) 𝓘(ℂ, ComplexModel n) ∞
      (toricFaceNativeEmbedding (hs := hs) v J) := by
  let γY := toricFaceProjectedFamily (hs := hs) v J
  let hY := latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J
  let := originalPolytopeNativeChartedSpace γY hY
  let := originalPolytopeNativeChartedSpace γ hs
  let := originalPolytopeNativeIsManifold γY hY ∞
  let := originalPolytopeNativeIsManifold γ hs ∞
  intro p
  obtain ⟨vY, hp⟩ := originalPolytopeNativeModelChart_cover γY hY p
  obtain ⟨w, hfp⟩ := originalPolytopeNativeModelChart_cover γ hs (toricFaceNativeEmbedding (hs := hs) v J p)
  let cY := originalPolytopeNativeModelChart γY hY vY
  let cX := originalPolytopeNativeModelChart γ hs w
  let y₀ := cY p
  let L := toricFaceHomogeneousZeroExtension (hs := hs) v J
  let V := fun y : ComplexModel (toricFaceDimension J) =>
    L (originalPolytopeNativeVector γY hY vY ((originalPolytopeNativeModelEquiv _ ) y))
  have hVne (y : ComplexModel (toricFaceDimension J)) : V y ≠ 0 := by
    simpa only [map_zero] using (toricFaceHomogeneousZeroExtension_injective (hs := hs) v J).ne
      (originalPolytopeNativeVector_ne_zero γY hY vY ((originalPolytopeNativeModelEquiv _) y))
  have hV (i : Fin (originalPolytopeFullIndexSize γ + 1))
      (y : ComplexModel (toricFaceDimension J)) : AnalyticAt ℂ (fun z => V z i) y := by
    change AnalyticAt ℂ (fun z => if hi : integerCast (originalPolytopeFullExponents γ i) ∈
        toricNativeVertexFace (hs := hs) v J then
        originalPolytopeNativeVector γY hY vY ((originalPolytopeNativeModelEquiv _) z)
          ((toricFaceHomogeneousIndexEquiv (hs := hs) v J).symm ⟨i, hi⟩) else 0) y
    by_cases hi : integerCast (originalPolytopeFullExponents γ i) ∈ toricNativeVertexFace (hs := hs) v J
    · simp only [dif_pos hi]
      exact (analyticAt_originalPolytopeNativeVector_coord γY hY vY _ _).comp
        ((originalPolytopeNativeModelEquiv _).analyticAt y)
    · simp only [dif_neg hi]
      exact analyticAt_const
  have hrep (y : ComplexModel (toricFaceDimension J)) :
      (toricFaceNativeEmbedding (hs := hs) v J (vertexPoint hY vY y)).val =
        Projectivization.mk ℂ (V y) (hVne y) := by
    change Projectivization.map L (toricFaceHomogeneousZeroExtension_injective (hs := hs) v J)
      (vertexPoint hY vY y).val = _
    have hyrep : (vertexPoint hY vY y).val = Projectivization.mk ℂ
        (originalPolytopeNativeVector γY hY vY ((originalPolytopeNativeModelEquiv _) y))
        (originalPolytopeNativeVector_ne_zero γY hY vY ((originalPolytopeNativeModelEquiv _) y)) :=
      originalPolytopeNativePiChart_symm_val γY hY vY ((originalPolytopeNativeModelEquiv _) y)
    rw [hyrep]
    rfl
  have hread (y : ComplexModel (toricFaceDimension J))
      (hy : toricFaceNativeEmbedding (hs := hs) v J (vertexPoint hY vY y) ∈ cX.source) :
      V y (originalPolytopeNativeVertexIndex γ w) ≠ 0 ∧ ∀ j,
        cX (toricFaceNativeEmbedding (hs := hs) v J (vertexPoint hY vY y)) j =
          V y (originalPolytopeNativeNeighborIndex γ hs w j) /
            V y (originalPolytopeNativeVertexIndex γ w) := by
    have hyPi : toricFaceNativeEmbedding (hs := hs) v J (vertexPoint hY vY y) ∈
        (originalPolytopeNativePiChart γ hs w).source := by
      rwa [originalPolytopeNativeModelChart_source] at hy
    have hr := (originalPolytopeNativePiChart_spec γ hs w).2.2.2.2.2 _ hyPi (V y) (hVne y) (hrep y)
    exact ⟨hr.1, fun j => hr.2 j⟩
  have hpoint : vertexPoint hY vY y₀ = p := vertexPoint_chart vY hp
  have hden : V y₀ (originalPolytopeNativeVertexIndex γ w) ≠ 0 :=
    (hread y₀ (by rw [hpoint]; exact hfp)).1
  have hcont : Continuous (fun y => toricFaceNativeEmbedding (hs := hs) v J (vertexPoint hY vY y)) :=
    (continuous_toricFaceNativeEmbedding (hs := hs) v J).comp (continuous_vertexPoint (hs := hY) vY)
  have hn : ∀ᶠ y in 𝓝 y₀,
      toricFaceNativeEmbedding (hs := hs) v J (vertexPoint hY vY y) ∈ cX.source := by
    apply hcont.continuousAt.preimage_mem_nhds
    rw [hpoint]
    exact cX.open_source.mem_nhds hfp
  have hratio : ContDiffAt ℂ ∞
      (fun y => modelPoint fun j => V y (originalPolytopeNativeNeighborIndex γ hs w j) /
        V y (originalPolytopeNativeVertexIndex γ w)) y₀ := by
    apply (originalPolytopeNativeModelEquiv n).symm.contDiff.contDiffAt.comp y₀
    apply contDiffAt_pi.mpr
    intro j
    exact ((hV _ y₀).div (hV _ y₀) hden).contDiffAt
  have hcoord : ContDiffAt ℂ ∞
      (fun y => cX (toricFaceNativeEmbedding (hs := hs) v J (vertexPoint hY vY y))) y₀ := by
    apply hratio.congr_of_eventuallyEq
    filter_upwards [hn] with y hy
    ext j
    exact (hread y hy).2 j
  have hmY : cY ∈ IsManifold.maximalAtlas 𝓘(ℂ, ComplexModel (toricFaceDimension J)) ∞
      (originalPolytopeNativeSpace γY) :=
    IsManifold.subset_maximalAtlas ⟨vY, rfl⟩
  have hmX : cX ∈ IsManifold.maximalAtlas 𝓘(ℂ, ComplexModel n) ∞ (originalPolytopeNativeSpace γ) :=
    IsManifold.subset_maximalAtlas ⟨w, rfl⟩
  apply (contMDiffAt_iff_of_mem_maximalAtlas hmY hmX hp hfp).mpr
  refine ⟨(continuous_toricFaceNativeEmbedding (hs := hs) v J).continuousAt, ?_⟩
  simp only [mfld_simps, contDiffWithinAt_univ]
  exact hcoord

end SGPT.Toric
