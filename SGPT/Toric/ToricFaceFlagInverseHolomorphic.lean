import SGPT.Toric.ToricFaceFlagComplex
import SGPT.Toric.ToricFaceInverseRatios

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

/-- The INVERSE of the same actual face-model/orbit-closure homeomorphism
is holomorphic in the genuine native/inherited atlases. Every inverse chart
coordinate is the actual selected ambient homogeneous ratio; analytic
representatives, the genuine holomorphic inclusion and actual nonzero
vertex denominators prove the claim on ALL original boundary points. -/
theorem contMDiff_toricFaceFlagHomeomorph_symm (v : latticePolytopeVertices γ)
    (e : Fin n ≃ Fin n) (i : Fin (n + 1)) :
    letI := originalPolytopeNativeChartedSpace
      (toricFaceProjectedFamily (hs := hs) v (toricFlagSelectedIndices e i))
      (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v (toricFlagSelectedIndices e i))
    letI := toricFaceFlagCharts (hs := hs) v e i
    ContMDiff 𝓘(ℂ, ComplexModel (toricFaceDimension (toricFlagSelectedIndices e i)))
      𝓘(ℂ, ComplexModel (toricFaceDimension (toricFlagSelectedIndices e i))) ∞
      (toricFaceFlagHomeomorph (hs := hs) v e i).symm := by
  let J := toricFlagSelectedIndices e i
  let γY := toricFaceProjectedFamily (hs := hs) v J
  let hY := latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J
  let := originalPolytopeNativeChartedSpace γY hY
  let := originalPolytopeNativeChartedSpace γ hs
  let := toricFaceFlagCharts (hs := hs) v e i
  have := originalPolytopeNativeIsComplexManifold γY hY
  have := originalPolytopeNativeIsComplexManifold γ hs
  have := toricFaceFlag_isComplexManifold (hs := hs) v e i
  intro q
  let f := toricFaceFlagHomeomorph (hs := hs) v e i
  let p := f.symm q
  obtain ⟨wY, hp⟩ := originalPolytopeNativeModelChart_cover γY hY p
  obtain ⟨wX, hq⟩ := originalPolytopeNativeModelChart_cover γ hs q.val
  let cY := originalPolytopeNativeModelChart γY hY wY
  let cX := originalPolytopeNativeModelChart γ hs wX
  let index := fun j => (toricFaceHomogeneousIndexEquiv (hs := hs) v J j).val
  let V := fun z : ComplexModel n => originalPolytopeNativeVector γ hs wX
    ((originalPolytopeNativeModelEquiv n) z)
  let R := fun z : ComplexModel n => modelPoint fun j =>
    V z (index (originalPolytopeNativeNeighborIndex γY hY wY j)) /
      V z (index (originalPolytopeNativeVertexIndex γY wY))
  have hV (j : Fin (originalPolytopeFullIndexSize γ + 1)) (z : ComplexModel n) :
      AnalyticAt ℂ (fun z => V z j) z :=
    (analyticAt_originalPolytopeNativeVector_coord γ hs wX j _).comp
      ((originalPolytopeNativeModelEquiv n).analyticAt z)
  have hRepX (y : toricFlag hs v e i) (hy : y.val ∈ cX.source) :
      y.val.val = Projectivization.mk ℂ (V (cX y.val))
        (originalPolytopeNativeVector_ne_zero γ hs wX ((originalPolytopeNativeModelEquiv n) (cX y.val))) := by
    have hr := originalPolytopeNativePiChart_symm_val γ hs wX ((originalPolytopeNativeModelEquiv n) (cX y.val))
    change (vertexPoint hs wX (cX y.val)).val = _ at hr
    rw [vertexPoint_chart wX hy] at hr
    exact hr
  have hpoint (y : toricFlag hs v e i) :
      toricFaceNativeEmbedding (hs := hs) v J (f.symm y) = y.val := by
    have heq := congrArg Subtype.val (f.apply_symm_apply y)
    exact heq
  have hRead (y : toricFlag hs v e i) (hyX : y.val ∈ cX.source)
      (hyY : f.symm y ∈ cY.source) :
      V (cX y.val) (index (originalPolytopeNativeVertexIndex γY wY)) ≠ 0 ∧
      cY (f.symm y) = R (cX y.val) := by
    have hyPi : f.symm y ∈ (originalPolytopeNativePiChart γY hY wY).source := by
      rwa [originalPolytopeNativeModelChart_source] at hyY
    have hr := toricFaceNativeEmbedding_inverse_chart_ratios (hs := hs) v J wY (f.symm y) hyPi
      (V (cX y.val))
      (originalPolytopeNativeVector_ne_zero γ hs wX ((originalPolytopeNativeModelEquiv n) (cX y.val)))
      (by rw [hpoint]; exact hRepX y hyX)
    refine ⟨hr.1, ?_⟩
    ext j
    exact hr.2 j
  have hden : V (cX q.val) (index (originalPolytopeNativeVertexIndex γY wY)) ≠ 0 :=
    (hRead q hq hp).1
  have hR : ContDiffAt ℂ ∞ R (cX q.val) := by
    apply (originalPolytopeNativeModelEquiv (toricFaceDimension J)).symm.contDiff.contDiffAt.comp
      (cX q.val)
    apply contDiffAt_pi.mpr
    intro j
    exact ((hV _ _).div (hV _ _) hden).contDiffAt
  have hmX : cX ∈ IsManifold.maximalAtlas 𝓘(ℂ, ComplexModel n) ∞ (originalPolytopeNativeSpace γ) :=
    IsManifold.subset_maximalAtlas ⟨wX, rfl⟩
  have hmY : cY ∈ IsManifold.maximalAtlas 𝓘(ℂ, ComplexModel (toricFaceDimension J)) ∞
      (originalPolytopeNativeSpace γY) :=
    IsManifold.subset_maximalAtlas ⟨wY, rfl⟩
  have hcX : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ cX q.val :=
    (contMDiffOn_of_mem_maximalAtlas hmX).contMDiffAt (cX.open_source.mem_nhds hq)
  have hIncl := contMDiff_toricFaceFlag_val (hs := hs) v e i
  have hCoordX : ContMDiffAt 𝓘(ℂ, ComplexModel (toricFaceDimension J)) 𝓘(ℂ, ComplexModel n) ∞
      (fun y : toricFlag hs v e i => cX y.val) q := hcX.comp q (hIncl q)
  have hRm : ContMDiffAt 𝓘(ℂ, ComplexModel n)
      𝓘(ℂ, ComplexModel (toricFaceDimension J)) ∞ R (cX q.val) := hR.contMDiffAt
  have hcomp : ContMDiffAt 𝓘(ℂ, ComplexModel (toricFaceDimension J))
      𝓘(ℂ, ComplexModel (toricFaceDimension J)) ∞ (fun y : toricFlag hs v e i => R (cX y.val)) q :=
    ContMDiffAt.comp (f := fun y : toricFlag hs v e i => cX y.val) (g := R) q hRm hCoordX
  have hnX : ∀ᶠ y : toricFlag hs v e i in 𝓝 q, y.val ∈ cX.source :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds (cX.open_source.mem_nhds hq)
  have hnY : ∀ᶠ y : toricFlag hs v e i in 𝓝 q, f.symm y ∈ cY.source :=
    f.symm.continuous.continuousAt.preimage_mem_nhds (cY.open_source.mem_nhds hp)
  have hcoord : ContMDiffAt 𝓘(ℂ, ComplexModel (toricFaceDimension J))
      𝓘(ℂ, ComplexModel (toricFaceDimension J)) ∞
      (fun y : toricFlag hs v e i => cY (f.symm y)) q := by
    apply hcomp.congr_of_eventuallyEq
    filter_upwards [hnX, hnY] with y hyX hyY
    exact (hRead y hyX hyY).2
  rw [← contMDiffWithinAt_univ, contMDiffWithinAt_iff_target_of_mem_maximalAtlas hmY hp]
  refine ⟨f.symm.continuous.continuousAt.continuousWithinAt, ?_⟩
  simp only [mfld_simps]
  change ContMDiffWithinAt 𝓘(ℂ, ComplexModel (toricFaceDimension J))
    𝓘(ℂ, ComplexModel (toricFaceDimension J)) ∞
    (fun y : toricFlag hs v e i => cY (f.symm y)) Set.univ q
  exact hcoord.contMDiffWithinAt

end SGPT.Toric
