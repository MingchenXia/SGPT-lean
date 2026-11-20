import SGPT.PSH.AtlasLogRangeCoefficients

/-! Complete literal source reconstruction from the actual native component
logarithms, retaining the source's ORIGINAL QPSH field explicitly. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas.SourceLogReverseDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.PSH.VariableComplexAtlas.SourceLogTransportDraft
open SGPT.PSH.VariableComplexAtlas.SourceLogSingularitiesDraft
open scoped Topology Manifold ContDiff Classical
universe u
variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
  {A : VariableComplexAtlas X}

/-- Actual complete native component logarithms reconstruct EVERY literal
original finite-prime/equation/coefficient/bounded-remainder field. Original
QPSH is the SAME explicit source-definition field; no metric, compactness,
uniform dimension, catalog or compatibility certificate is a premise. -/
theorem original_log_of_native_components
    {D : AtlasEffectiveGeometricQDivisor A} {u : X → EReal} (hu : A.IsQPSH u)
    (hnat : ∀ x : X,
      letI := A.componentChartedSpace x
      letI := A.componentComplexManifold_of_paracompact x
      NativeHasLogSingularitiesAlongAnyDimension (D.nativeComponent x)
        (fun q : A.componentOpen x => u q.val)) : SourceHasLogSingularitiesAlong D u := by
  refine ⟨hu,?_⟩
  intro x
  let := A.componentChartedSpace x
  let := A.componentComplexManifold_of_paracompact x
  obtain ⟨O,hxO,r,Z,a,p,R,C,hZ,ha,hp,hideal,hcoeff,hC,hR,hlog⟩ :=
    (hnat x).2 ⟨x,mem_connectedComponent⟩
  let U := flattenOpen (A.componentOpen x) O
  let e := flattenHomeomorph (A.componentOpen x) O
  let := A.openRestriction_paracompactSpace U
  have hinj := (originalPrimeOnRange_bijective A x O).1
  have hfun (i : Fin r) : (p i ∘ e.symm) ∘ e=p i := by
    funext q
    simp only [Function.comp_apply,e.symm_apply_apply]
  refine ⟨U,⟨⟨⟨x,mem_connectedComponent⟩,hxO⟩,rfl⟩,r,
    (fun i => originalPrimeOnRange A x O (Z i)),a,
    (fun i => p i ∘ e.symm),R ∘ e.symm,C,(hinj.comp hZ),ha,?_,?_,?_,hC,
    (fun y => hR (e.symm y)),?_⟩
  · intro i
    apply (range_chartHolomorphicOn_iff A x O (p i ∘ e.symm)).mpr
    intro q
    change HolomorphicAt (A.pointDimension x) ((p i ∘ e.symm) ∘ e) q
    rw [hfun i]
    exact hp i q
  · intro i y b
    let q := e.symm y
    have hcarrier : e ⁻¹' (originalPrimeOnRange A x O (Z i)).val=(Z i).val := by
      rw [originalPrimeOnRange_carrier]
      exact Set.preimage_image_eq (Z i).val e.injective
    have hred := range_reducedIdeal_mem_iff A x O (originalPrimeOnRange A x O (Z i)).val q b
    change (atlasVanishingIdeal (A.openRestriction U) (originalPrimeOnRange A x O (Z i)).val).mem
      (e q) b ↔
      (vanishingIdeal (n := A.pointDimension x) (e ⁻¹' (originalPrimeOnRange A x O (Z i)).val)).mem q
        (b ∘ e) at hred
    rw [hcarrier] at hred
    have hspan := range_principalSpan_iff A x O (p i ∘ e.symm) b q
    change (A.openRestriction U).AtlasIsInSpanAt (· = p i ∘ e.symm) (e q) b ↔
      IsInSpanAt (n := A.pointDimension x) (· = (p i ∘ e.symm) ∘ e) q (b ∘ e) at hspan
    rw [hfun i] at hspan
    have h := hred.trans ((hideal i q (b ∘ e)).trans hspan.symm)
    have hq : e q=y := e.apply_symm_apply y
    rwa [hq] at h
  · intro Q
    obtain ⟨P,rfl⟩ := (originalPrimeOnRange_bijective A x O).2 Q
    rw [original_range_coefficient D x O P,hcoeff P]
    apply Finset.sum_congr rfl
    intro i _
    have heq : originalPrimeOnRange A x O (Z i)=originalPrimeOnRange A x O P ↔ Z i=P :=
      hinj.eq_iff
    simp only [heq]
  · intro y
    have h := hlog (e.symm y)
    have hv : (e.symm y).val.val=y.val := flattenHomeomorph_symm_val (A.componentOpen x) O y
    simpa only [Function.comp_apply,hv] using h

/-- Exact two-way dictionary for the literal source logarithmic condition.
The original QPSH field is explicit, and every remaining native/source field
is genuinely transported by actual ideal, prime and full coefficient proofs. -/
theorem original_log_iff_native_components
    (D : AtlasEffectiveGeometricQDivisor A) (u : X → EReal) :
    SourceHasLogSingularitiesAlong D u ↔ A.IsQPSH u ∧
      ∀ x : X,
        letI := A.componentChartedSpace x
        letI := A.componentComplexManifold_of_paracompact x
        NativeHasLogSingularitiesAlongAnyDimension (D.nativeComponent x)
          (fun q : A.componentOpen x => u q.val) := by
  constructor
  · intro h
    exact ⟨h.1,fun x => original_log_nativeComponent h x⟩
  · intro h
    exact original_log_of_native_components h.1 h.2

end SGPT.PSH.VariableComplexAtlas.SourceLogReverseDraft
