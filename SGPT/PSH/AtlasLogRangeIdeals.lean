import SGPT.PSH.AtlasLogRangeScalar

/-! Entire original/native scalar ideals on a genuine component-open range. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas.SourceLogReverseDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.PSH.VariableComplexAtlas.SourceLogTransportDraft
open scoped Topology Manifold ContDiff Classical
universe u
variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
  (A : VariableComplexAtlas X) (x : X)

/-- The ENTIRE reduced ideal on the actual original range is native for
EVERY scalar and EVERY set, including singular stalks and disconnected opens. -/
theorem range_reducedIdeal_mem_iff
    (O : Opens (A.componentOpen x)) (S : Set (flattenOpen (A.componentOpen x) O))
    (q : O) (g : flattenOpen (A.componentOpen x) O → ℂ) :
    letI := A.componentChartedSpace x
    letI := A.componentComplexManifold_of_paracompact x
    (atlasVanishingIdeal (A.openRestriction (flattenOpen (A.componentOpen x) O)) S).mem
      (flattenHomeomorph (A.componentOpen x) O q) g ↔
    (vanishingIdeal (n := A.pointDimension x)
      ((flattenHomeomorph (A.componentOpen x) O) ⁻¹' S)).mem q
      (g ∘ flattenHomeomorph (A.componentOpen x) O) := by
  let := A.componentChartedSpace x
  let := A.componentComplexManifold_of_paracompact x
  let e := flattenHomeomorph (A.componentOpen x) O
  change ((A.openRestriction (flattenOpen (A.componentOpen x) O)).AtlasHolomorphicAt g (e q) ∧
    ∀ᶠ y in 𝓝 (e q),y∈S → g y=0) ↔
    (HolomorphicAt (A.pointDimension x) (g ∘ e) q ∧
      ∀ᶠ y in 𝓝 q,y∈e ⁻¹' S → (g ∘ e) y=0)
  apply and_congr (range_atlasHolomorphicAt_iff A x O q g)
  constructor
  · intro h
    exact (e.continuous.tendsto q).eventually h
  · intro h
    have ht : Tendsto e.symm (𝓝 (e q)) (𝓝 q) := by
      simpa only [e.symm_apply_apply] using e.symm.continuous.tendsto (e q)
    filter_upwards [ht.eventually h] with y hy
    simpa only [mem_preimage,Function.comp_apply,e.apply_symm_apply] using hy

/-- Both ENTIRE finite principal-span directions retain every original and
native cofactor, finite sum and SAME defining function on the actual range. -/
theorem range_principalSpan_iff
    (O : Opens (A.componentOpen x)) (f g : flattenOpen (A.componentOpen x) O → ℂ) (q : O) :
    letI := A.componentChartedSpace x
    letI := A.componentComplexManifold_of_paracompact x
    (A.openRestriction (flattenOpen (A.componentOpen x) O)).AtlasIsInSpanAt (· = f)
      (flattenHomeomorph (A.componentOpen x) O q) g ↔
    IsInSpanAt (n := A.pointDimension x) (· = f ∘ flattenHomeomorph (A.componentOpen x) O) q
      (g ∘ flattenHomeomorph (A.componentOpen x) O) := by
  let := A.componentChartedSpace x
  let := A.componentComplexManifold_of_paracompact x
  let e := flattenHomeomorph (A.componentOpen x) O
  constructor
  · rintro ⟨hg,N,s,a,hs,ha,heq⟩
    refine ⟨(range_atlasHolomorphicAt_iff A x O q g).mp hg,N,
      (fun i => s i ∘ e),(fun i => a i ∘ e),
      (fun i => congrArg (fun h => h ∘ e) (hs i)),
      (fun i => (range_atlasHolomorphicAt_iff A x O q (a i)).mp (ha i)),?_⟩
    exact (e.continuous.tendsto q).eventually heq
  · rintro ⟨hg,N,s,a,hs,ha,heq⟩
    refine ⟨(range_atlasHolomorphicAt_iff A x O q g).mpr hg,N,
      (fun i => s i ∘ e.symm),(fun i => a i ∘ e.symm),?_,?_,?_⟩
    · intro i
      funext y
      change s i (e.symm y)=f y
      rw [hs i]
      change f (e (e.symm y))=f y
      rw [e.apply_symm_apply]
    · intro i
      apply (range_atlasHolomorphicAt_iff A x O q (a i ∘ e.symm)).mpr
      have hfun : (a i ∘ e.symm) ∘ e=a i := by
        funext y
        simp only [Function.comp_apply,e.symm_apply_apply]
      change HolomorphicAt (A.pointDimension x) ((a i ∘ e.symm) ∘ e) q
      rw [hfun]
      exact ha i
    · have ht : Tendsto e.symm (𝓝 (e q)) (𝓝 q) := by
        simpa only [e.symm_apply_apply] using e.symm.continuous.tendsto (e q)
      filter_upwards [ht.eventually heq] with y hy
      change g (e (e.symm y))=∑ i,a i (e.symm y)*s i (e.symm y) at hy
      rwa [e.apply_symm_apply] at hy

omit [T2Space X] [ParacompactSpace X] in
/-- Actual every-point original holomorphic germs give actual all-chart
holomorphy, by the original chart target's genuine open neighborhoods. -/
theorem chartHolomorphicOn_of_all_original_germs (f : X → ℂ)
    (hf : ∀ y,A.AtlasHolomorphicAt f y) : A.ChartHolomorphicOn f univ := by
  intro i z hz
  obtain ⟨V,hV,hzV,hfV⟩ := hf ((A.chart i).symm z)
  exact ((hfV i).differentiableAt
    (((A.chart i).isOpen_inter_preimage_symm hV).mem_nhds ⟨hz.1,hzV⟩)).differentiableWithinAt

/-- The literal whole-open all-chart original equation condition is exactly
holomorphy of its SAME native equation at every point of the actual range. -/
theorem range_chartHolomorphicOn_iff
    (O : Opens (A.componentOpen x)) (g : flattenOpen (A.componentOpen x) O → ℂ) :
    letI := A.componentChartedSpace x
    letI := A.componentComplexManifold_of_paracompact x
    (A.openRestriction (flattenOpen (A.componentOpen x) O)).ChartHolomorphicOn g univ ↔
    ∀ q : O,HolomorphicAt (A.pointDimension x)
      (g ∘ flattenHomeomorph (A.componentOpen x) O) q := by
  let := A.componentChartedSpace x
  let := A.componentComplexManifold_of_paracompact x
  let e := flattenHomeomorph (A.componentOpen x) O
  constructor
  · intro h q
    exact (range_atlasHolomorphicAt_iff A x O q g).mp ⟨univ,isOpen_univ,mem_univ _,h⟩
  · intro h
    apply chartHolomorphicOn_of_all_original_germs
    intro y
    have hy := (range_atlasHolomorphicAt_iff A x O (e.symm y) g).mpr (h (e.symm y))
    change (A.openRestriction (flattenOpen (A.componentOpen x) O)).AtlasHolomorphicAt g (e (e.symm y)) at hy
    rwa [e.apply_symm_apply] at hy

end SGPT.PSH.VariableComplexAtlas.SourceLogReverseDraft
