import SGPT.PSH.AtlasNativeComponentInclusion
import SGPT.PSH.SourceSubgeodesicL1

/-! The original connected atlas supplies every native chart, its dimension,
and the whole pulled form.  The original point set and topology are retained.
The complete chosen proofs precede this file in the compactness blueprint. -/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter TopologicalSpace MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff ENNReal

universe u
variable {X : Type u} [TopologicalSpace X]

private theorem connected_castChart_source {d n : ℕ}
    (e : OpenPartialHomeomorph X (ComplexModel d)) (h : d = n) :
    (nativeCoordinateDimensionTransport e h).source = e.source := by
  subst n
  rfl

private theorem connected_castChart_transition {d m n : ℕ}
    (e : OpenPartialHomeomorph X (ComplexModel d))
    (f : OpenPartialHomeomorph X (ComplexModel m)) (hd : d = n) (hm : m = n)
    (hh : DifferentiableOn ℂ (e.symm.trans f) (e.symm.trans f).source) :
    DifferentiableOn ℂ
      ((nativeCoordinateDimensionTransport e hd).symm.trans
        (nativeCoordinateDimensionTransport f hm))
      ((nativeCoordinateDimensionTransport e hd).symm.trans
        (nativeCoordinateDimensionTransport f hm)).source := by
  subst d
  subst m
  exact hh

/-- Every chart which meets the manufactured component is one unchanged
original chart, with its PROVED model dimension substituted. -/
def sourceConnectedNativeChart (A : VariableComplexAtlas X) (x : X)
    (i : A.ComponentChartIndex x) :
    OpenPartialHomeomorph X (ComplexModel (A.pointDimension x)) :=
  nativeCoordinateDimensionTransport (A.chart i.val) (A.componentChartDimension x i)

@[simp] theorem sourceConnectedNativeChart_source (A : VariableComplexAtlas X)
    (x : X) (i : A.ComponentChartIndex x) :
    (A.sourceConnectedNativeChart x i).source = (A.chart i.val).source :=
  connected_castChart_source _ _

variable [ConnectedSpace X]

/-- Connectedness makes the original component qualification automatic;
the chart index and its original dimension remain unchanged. -/
def sourceConnectedChartIndex (A : VariableComplexAtlas X) (x : X) (i : A.Index)
    (hi : (A.chart i).source.Nonempty) : A.ComponentChartIndex x := by
  refine ⟨i, ?_⟩
  obtain ⟨y, hy⟩ := hi
  refine ⟨y, hy, ?_⟩
  rw [PreconnectedSpace.connectedComponent_eq_univ]
  exact mem_univ y

theorem sourceConnectedNativeChart_cover (A : VariableComplexAtlas X) (x p : X) :
    ∃ i : A.ComponentChartIndex x, p ∈ (A.sourceConnectedNativeChart x i).source := by
  obtain ⟨i, hi⟩ := A.cover p
  let j := A.sourceConnectedChartIndex x i ⟨p, hi⟩
  refine ⟨j, ?_⟩
  rw [sourceConnectedNativeChart_source]
  change p ∈ (A.chart i).source
  exact hi

/-- The manufactured native atlas on the SAME original point set and topology.
Its atlas consists of precisely the nonempty inherited original charts. -/
@[instance_reducible]
def sourceConnectedNativeChartedSpace (A : VariableComplexAtlas X) (x : X) :
    ChartedSpace (ComplexModel (A.pointDimension x)) X where
  atlas := range (A.sourceConnectedNativeChart x)
  chartAt := fun p => A.sourceConnectedNativeChart x
    (Classical.choose (A.sourceConnectedNativeChart_cover x p))
  mem_chart_source := fun p => Classical.choose_spec (A.sourceConnectedNativeChart_cover x p)
  chart_mem_atlas := fun p => ⟨Classical.choose (A.sourceConnectedNativeChart_cover x p), rfl⟩

/-- Each inherited original chart is an actual member of the manufactured atlas. -/
def sourceConnectedNativeComplexChart (A : VariableComplexAtlas X) (x : X)
    (i : A.ComponentChartIndex x) :
    letI := A.sourceConnectedNativeChartedSpace x
    ComplexChart (A.pointDimension x) X := by
  let := A.sourceConnectedNativeChartedSpace x
  exact ⟨A.sourceConnectedNativeChart x i, ⟨i, rfl⟩⟩

/-- All native holomorphic transitions are the genuine original transitions,
after substitution of the internally proved dimensions. -/
theorem sourceConnectedNativeIsManifold (A : VariableComplexAtlas X) (x : X) :
    letI := A.sourceConnectedNativeChartedSpace x
    IsManifold (𝓘(ℂ, ComplexModel (A.pointDimension x))) ∞ X := by
  let := A.sourceConnectedNativeChartedSpace x
  apply isManifold_of_contDiffOn (𝓘(ℂ, ComplexModel (A.pointDimension x))) ∞ X
  intro e f he hf
  obtain ⟨i, rfl⟩ := he
  obtain ⟨j, rfl⟩ := hf
  simpa [sourceConnectedNativeChart, connected_castChart_source] using
    contDiffOn_of_differentiableOn_complex
    (connected_castChart_transition (A.chart i.val) (A.chart j.val)
      (A.componentChartDimension x i) (A.componentChartDimension x j)
      (A.holomorphic i.val j.val))
    ((A.sourceConnectedNativeChart x i).symm.trans
      (A.sourceConnectedNativeChart x j)).open_source

/-- Original Hausdorff/paracompact geometry manufactures all native fields;
second countability and uniform dimension are outputs, not extra inputs. -/
theorem sourceConnectedNativeComplexManifold [T2Space X] [ParacompactSpace X]
    (A : VariableComplexAtlas X) (x : X) :
    letI := A.sourceConnectedNativeChartedSpace x
    IsComplexManifold (A.pointDimension x) X := by
  let := A.sourceConnectedNativeChartedSpace x
  let := SGPT.PSH.secondCountable_of_paracompact_connected_charted
    (ComplexModel (A.pointDimension x)) X
  exact {
    toT2Space := inferInstance
    toSecondCountableTopology := inferInstance
    toIsManifold := A.sourceConnectedNativeIsManifold x }

omit [ConnectedSpace X] in
private theorem connected_castChart_psh {d n : ℕ}
    (e : OpenPartialHomeomorph X (ComplexModel d)) (h : d = n)
    (f : X → EReal) (U : Set X) :
    PlurisubharmonicOn (f ∘ (nativeCoordinateDimensionTransport e h).symm)
        ((nativeCoordinateDimensionTransport e h).target ∩
          (nativeCoordinateDimensionTransport e h).symm ⁻¹' U) ↔
      PlurisubharmonicOn (f ∘ e.symm) (e.target ∩ e.symm ⁻¹' U) := by
  subst n
  rfl

omit [ConnectedSpace X] in
private theorem connected_castChart_sourceMap {d n m : ℕ}
    (e : OpenPartialHomeomorph X (ComplexModel d))
    (f : OpenPartialHomeomorph X (ComplexModel m)) (h : d = n)
    (hh : DifferentiableOn ℂ (f ∘ e.symm) (e.target ∩ e.symm ⁻¹' f.source)) :
    DifferentiableOn ℂ (f ∘ (nativeCoordinateDimensionTransport e h).symm)
      ((nativeCoordinateDimensionTransport e h).target ∩
        (nativeCoordinateDimensionTransport e h).symm ⁻¹' f.source) := by
  subst n
  exact hh

variable [T2Space X] [ParacompactSpace X]

/-- The SAME pointwise identity has genuine all-chart holomorphy from the
manufactured native atlas to the original independently dimensional atlas. -/
theorem sourceConnectedNative_identity_isHolomorphic (A : VariableComplexAtlas X) (x : X) :
    letI := A.sourceConnectedNativeChartedSpace x
    letI := A.sourceConnectedNativeComplexManifold x
    (ofFixedModel (A.pointDimension x) X).IsHolomorphic A id := by
  let := A.sourceConnectedNativeChartedSpace x
  let := A.sourceConnectedNativeComplexManifold x
  refine ⟨continuous_id, ?_⟩
  intro e j
  obtain ⟨i, hi⟩ := e.property
  change DifferentiableOn ℂ (A.chart j ∘ id ∘ e.val.symm)
    (e.val.target ∩ e.val.symm ⁻¹' (id ⁻¹' (A.chart j).source))
  rw [← hi]
  have hh : DifferentiableOn ℂ (A.chart j ∘ (A.chart i.val).symm)
      ((A.chart i.val).target ∩ (A.chart i.val).symm ⁻¹' (A.chart j).source) := by
    simpa only [OpenPartialHomeomorph.coe_trans, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.symm_source] using A.holomorphic i.val j
  simpa only [sourceConnectedNativeChart, Function.comp_id, Function.id_comp, preimage_id] using
    connected_castChart_sourceMap (A.chart i.val) (A.chart j)
      (A.componentChartDimension x i) hh

/-- Every original open-set PSH test, with its full local nondegeneracy,
is exactly the same test in the manufactured native atlas. -/
theorem sourceConnected_isPSHOn_iff (A : VariableComplexAtlas X) (x : X)
    (f : X → EReal) {U : Set X} (hU : IsOpen U) :
    letI := A.sourceConnectedNativeChartedSpace x
    letI := A.sourceConnectedNativeComplexManifold x
    A.IsPSHOn f U ↔ (ofFixedModel (A.pointDimension x) X).IsPSHOn f U := by
  let := A.sourceConnectedNativeChartedSpace x
  let := A.sourceConnectedNativeComplexManifold x
  rw [isPSHOn_iff_chart_and_nondegenerate hU,
    isPSHOn_iff_chart_and_nondegenerate hU]
  constructor
  · rintro ⟨hc, hn⟩
    refine ⟨?_, hn⟩
    intro e
    obtain ⟨i, hi⟩ := e.property
    change PlurisubharmonicOn (f ∘ e.val.symm)
      (e.val.target ∩ e.val.symm ⁻¹' U)
    rw [← hi]
    exact (connected_castChart_psh (A.chart i.val) (A.componentChartDimension x i) f U).mpr
      (hc i.val)
  · rintro ⟨hc, hn⟩
    refine ⟨?_, hn⟩
    intro i
    by_cases hi : (A.chart i).source.Nonempty
    · let j : A.ComponentChartIndex x := ⟨i, by
        obtain ⟨y, hy⟩ := hi
        refine ⟨y, hy, ?_⟩
        rw [PreconnectedSpace.connectedComponent_eq_univ]
        exact mem_univ y⟩
      let e : ComplexChart (A.pointDimension x) X :=
        ⟨A.sourceConnectedNativeChart x j, ⟨j, rfl⟩⟩
      have hh := (connected_castChart_psh (A.chart i)
        (A.componentChartDimension x j) f U).mp (hc e)
      exact hh
    · intro z hz
      exact (hi ⟨(A.chart i).symm z, (A.chart i).map_target hz.1⟩).elim

/-- The ENTIRE actual original closed tensor is pulled through the same
identity map; no scalar potential or cohomology class replaces the form. -/
def sourceConnectedNativeAtlasForm (A : VariableComplexAtlas X) (x : X)
    (θ : AtlasClosedRealOneOneForm A) :
    letI := A.sourceConnectedNativeChartedSpace x
    letI := A.sourceConnectedNativeComplexManifold x
    AtlasClosedRealOneOneForm (ofFixedModel (A.pointDimension x) X) := by
  let := A.sourceConnectedNativeChartedSpace x
  let := A.sourceConnectedNativeComplexManifold x
  exact θ.holomorphicPullback (A.sourceConnectedNative_identity_isHolomorphic x)

/-- The manufactured native background retains the full closed (1,1) form. -/
def sourceConnectedNativeForm (A : VariableComplexAtlas X) (x : X)
    (θ : AtlasClosedRealOneOneForm A) :
    letI := A.sourceConnectedNativeChartedSpace x
    letI := A.sourceConnectedNativeComplexManifold x
    ClosedRealOneOneForm (A.pointDimension x) X := by
  let := A.sourceConnectedNativeChartedSpace x
  let := A.sourceConnectedNativeComplexManifold x
  exact atlasClosedFormToNative (A.sourceConnectedNativeAtlasForm x θ)

/-- ENTIRE original universal local-potential theta-PSH is equivalent to
genuine native theta-PSH of the SAME function in the manufactured WHOLE form. -/
theorem sourceConnected_isThetaPSH_iff (A : VariableComplexAtlas X) (x : X)
    (θ : AtlasClosedRealOneOneForm A) (f : X → EReal) :
    letI := A.sourceConnectedNativeChartedSpace x
    letI := A.sourceConnectedNativeComplexManifold x
    A.IsThetaPSH θ f ↔ IsThetaPshPotential (A.sourceConnectedNativeForm x θ).val f := by
  let := A.sourceConnectedNativeChartedSpace x
  let := A.sourceConnectedNativeComplexManifold x
  change A.IsThetaPSH θ f ↔
    IsThetaPshPotential (atlasClosedFormToNative (A.sourceConnectedNativeAtlasForm x θ)).val f
  rw [← isThetaPSH_iff_nativeThetaPotential]
  constructor
  · intro hf
    have hn : ∀ p : X, ∃ q ∈ connectedComponent p, f (id q) ≠ ⊥ := by
      intro p
      obtain ⟨q, _, hq⟩ := (IsQPSH.locallyNondegenerate ⟨θ, hf⟩)
        p univ isOpen_univ (mem_univ p)
      refine ⟨q, ?_, hq⟩
      rw [PreconnectedSpace.connectedComponent_eq_univ]
      exact mem_univ q
    simpa only [sourceConnectedNativeAtlasForm, Function.comp_id] using
      (hf.comp_holomorphic_iff_component_nonbot
        (A.sourceConnectedNative_identity_isHolomorphic x)).mpr hn
  · intro hf
    refine ⟨hf.1, ?_⟩
    intro U g hg
    have hgN : (ofFixedModel (A.pointDimension x) X).IsAtlasLocalPotential
        (A.sourceConnectedNativeAtlasForm x θ) U g := by
      simpa only [sourceConnectedNativeAtlasForm, preimage_id, Function.comp_id] using
        hg.comp_holomorphic (A.sourceConnectedNative_identity_isHolomorphic x)
    exact (A.sourceConnected_isPSHOn_iff x (fun y => f y + (g y : EReal)) hg.1).mpr
      (hf.2 U g hgN)

omit [ConnectedSpace X] [T2Space X] [ParacompactSpace X] in
private theorem connected_castChart_pullbackCoeff {d n : ℕ}
    (e : OpenPartialHomeomorph X (ComplexModel d)) (h : d = n)
    (a : ComplexModel d → (ComplexModel d) [⋀^Fin 2]→L[ℝ] ℝ)
    (z : ComplexModel n) (hz : z ∈ (nativeCoordinateDimensionTransport e h).target) :
    (a (e ((nativeCoordinateDimensionTransport e h).symm z))).compContinuousLinearMap
        (fderiv ℝ (e ∘ (nativeCoordinateDimensionTransport e h).symm) z) =
      (h ▸ a) z := by
  subst n
  simp only [nativeCoordinateDimensionTransport] at hz ⊢
  have he : e ∘ e.symm =ᶠ[𝓝 z] id := by
    filter_upwards [e.open_target.mem_nhds hz] with y hy
    exact e.right_inv hy
  rw [he.fderiv_eq, fderiv_id, e.right_inv hz]
  ext w
  rfl

/-- Every inherited nonempty original chart reads EXACTLY its original
whole alternating coefficient, after its proved dimension equality. -/
theorem sourceConnectedNativeForm_coeff (A : VariableComplexAtlas X) (x : X)
    (θ : AtlasClosedRealOneOneForm A) (i : A.ComponentChartIndex x) :
    letI := A.sourceConnectedNativeChartedSpace x
    letI := A.sourceConnectedNativeComplexManifold x
    ∀ z, z ∈ (A.sourceConnectedNativeChart x i).target →
      (A.sourceConnectedNativeForm x θ).val.coeff (A.sourceConnectedNativeComplexChart x i) z =
        ((A.componentChartDimension x i) ▸ θ.coeff i.val) z := by
  let := A.sourceConnectedNativeChartedSpace x
  let := A.sourceConnectedNativeComplexManifold x
  intro z hz
  let e := A.sourceConnectedNativeComplexChart x i
  have hdomain : z ∈ atlasCoordinateDomain (ofFixedModel (A.pointDimension x) X) A id e i.val := by
    refine ⟨hz, ?_⟩
    change (A.sourceConnectedNativeChart x i).symm z ∈ (A.chart i.val).source
    rw [← sourceConnectedNativeChart_source A x i]
    exact (A.sourceConnectedNativeChart x i).map_target hz
  have hh := θ.holomorphicPullback_coeff
    (A.sourceConnectedNative_identity_isHolomorphic x) e i.val hdomain
  change (θ.holomorphicPullback
    (A.sourceConnectedNative_identity_isHolomorphic x)).coeff e z = _
  rw [hh]
  exact connected_castChart_pullbackCoeff (A.chart i.val)
    (A.componentChartDimension x i) (θ.coeff i.val) z hz

/-- The ACTUAL original compact-chart canonical error, in its original
coordinate dimension and original canonical Haar volume, including poles. -/
def sourceAtlasChartL1EDistance (A : VariableComplexAtlas X) (f g : X → EReal)
    (i : A.Index) (K : Set (ComplexModel (A.dimension i))) : ℝ≥0∞ :=
  ∫⁻ z in K, canonicalERealAbsDiff (A.coordinate f i z) (A.coordinate g i z) ∂volume

/-- All original chart seminorms, along ANY original index filter. -/
def SourceAtlasCanonicalL1Tendsto (A : VariableComplexAtlas X) {I : Type*}
    (f : I → X → EReal) (F : Filter I) (g : X → EReal) : Prop :=
  ∀ (i : A.Index) (K : Set (ComplexModel (A.dimension i))),
    IsCompact K → K ⊆ (A.chart i).target →
      Tendsto (fun j => A.sourceAtlasChartL1EDistance (f j) g i K) F (𝓝 0)

omit [ConnectedSpace X] [T2Space X] [ParacompactSpace X] in
private theorem connected_castChart_canonicalTendsto_iff {d n : ℕ} {I : Type*}
    (e : OpenPartialHomeomorph X (ComplexModel d)) (h : d = n)
    (f : I → X → EReal) (F : Filter I) (g : X → EReal) :
    (∀ (K : Set (ComplexModel n)), IsCompact K →
      K ⊆ (nativeCoordinateDimensionTransport e h).target →
      Tendsto (fun j => ∫⁻ z in K, canonicalERealAbsDiff
        (f j ((nativeCoordinateDimensionTransport e h).symm z))
        (g ((nativeCoordinateDimensionTransport e h).symm z)) ∂volume) F (𝓝 0)) ↔
    (∀ (K : Set (ComplexModel d)), IsCompact K → K ⊆ e.target →
      Tendsto (fun j => ∫⁻ z in K, canonicalERealAbsDiff
        (f j (e.symm z)) (g (e.symm z)) ∂volume) F (𝓝 0)) := by
  subst n
  rfl

omit [T2Space X] [ParacompactSpace X] in
/-- EVERY original nonempty chart is inherited, and empty chart targets
give zero errors. Thus the genuine canonical convergence readers agree
for ALL index types and filters, with no PSH assumption needed here. -/
theorem sourceConnected_manifoldL1_iff (A : VariableComplexAtlas X) (x : X)
    {I : Type*} (f : I → X → EReal) (F : Filter I) (g : X → EReal) :
    letI := A.sourceConnectedNativeChartedSpace x
    ManifoldL1LocallyTendsto (n := A.pointDimension x) f F g ↔
      A.SourceAtlasCanonicalL1Tendsto f F g := by
  let := A.sourceConnectedNativeChartedSpace x
  constructor
  · intro hf i K hK hKt
    by_cases hi : (A.chart i).source.Nonempty
    · let j : A.ComponentChartIndex x := ⟨i, by
        obtain ⟨y, hy⟩ := hi
        refine ⟨y, hy, ?_⟩
        rw [PreconnectedSpace.connectedComponent_eq_univ]
        exact mem_univ y⟩
      have hnative : ∀ (L : Set (ComplexModel (A.pointDimension x))), IsCompact L →
          L ⊆ (nativeCoordinateDimensionTransport (A.chart i)
            (A.componentChartDimension x j)).target →
          Tendsto (fun k => ∫⁻ z in L, canonicalERealAbsDiff
            (f k ((nativeCoordinateDimensionTransport (A.chart i)
              (A.componentChartDimension x j)).symm z))
            (g ((nativeCoordinateDimensionTransport (A.chart i)
              (A.componentChartDimension x j)).symm z)) ∂volume) F (𝓝 0) := by
        intro L hL hLt
        simpa only [chartL1EDistance, chartFunction, sourceConnectedNativeComplexChart,
          sourceConnectedNativeChart] using
          hf (A.sourceConnectedNativeComplexChart x j) L hL hLt
      exact ((connected_castChart_canonicalTendsto_iff (A.chart i)
        (A.componentChartDimension x j) f F g).mp hnative) K hK hKt
    · have hKe : K = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro z hz
        exact hi ⟨(A.chart i).symm z, (A.chart i).map_target (hKt hz)⟩
      subst K
      simpa [sourceAtlasChartL1EDistance] using
        (tendsto_const_nhds (x := (0 : ℝ≥0∞)))
  · intro hf e K hK hKt
    obtain ⟨i, hi⟩ := e.property
    have horiginal : ∀ (L : Set (ComplexModel (A.dimension i.val))), IsCompact L →
        L ⊆ (A.chart i.val).target →
        Tendsto (fun k => ∫⁻ z in L, canonicalERealAbsDiff
          (f k ((A.chart i.val).symm z)) (g ((A.chart i.val).symm z)) ∂volume) F (𝓝 0) :=
      hf i.val
    have hnative := (connected_castChart_canonicalTendsto_iff (A.chart i.val)
      (A.componentChartDimension x i) f F g).mpr horiginal
    change Tendsto (fun j => ∫⁻ z in K, canonicalERealAbsDiff
      (f j (e.val.symm z)) (g (e.val.symm z)) ∂volume) F (𝓝 0)
    rw [← hi]
    rw [← hi] at hKt
    exact hnative K hK hKt

/-- The ENTIRE original potential class, on the unchanged original X. -/
def SourceAtlasThetaPotentialL1 (A : VariableComplexAtlas X)
    (θ : AtlasClosedRealOneOneForm A) := {f : X → EReal // A.IsThetaPSH θ f}

/-- SAME-function equivalence of the full original and manufactured native
classes; every native predicate is produced by the original universal test. -/
def sourceConnectedThetaL1EquivNative (A : VariableComplexAtlas X) (x : X)
    (θ : AtlasClosedRealOneOneForm A) :
    letI := A.sourceConnectedNativeChartedSpace x
    letI := A.sourceConnectedNativeComplexManifold x
    A.SourceAtlasThetaPotentialL1 θ ≃
      SGPT.Foundations.Analysis.Pending.ThetaPshL1Topology.ThetaPshL1
        (A.sourceConnectedNativeForm x θ).val := by
  let := A.sourceConnectedNativeChartedSpace x
  let := A.sourceConnectedNativeComplexManifold x
  exact {
    toFun f := ⟨f.val, (A.sourceConnected_isThetaPSH_iff x θ f.val).mp f.property⟩
    invFun f := ⟨f.val, (A.sourceConnected_isThetaPSH_iff x θ f.val).mpr f.property⟩
    left_inv f := Subtype.ext rfl
    right_inv f := Subtype.ext rfl }

/-- Actual original L1 topology induced by genuine chart Lp classes.
Its EVERY-original-chart interpretation is proved below for all filters. -/
@[instance_reducible]
def sourceAtlasThetaPotentialL1Topology (A : VariableComplexAtlas X) (x : X)
    (θ : AtlasClosedRealOneOneForm A) : TopologicalSpace (A.SourceAtlasThetaPotentialL1 θ) := by
  let := A.sourceConnectedNativeChartedSpace x
  let := A.sourceConnectedNativeComplexManifold x
  exact TopologicalSpace.induced (A.sourceConnectedThetaL1EquivNative x θ) inferInstance

/-- The full same-function dictionary is a homeomorphism for the genuine
original and native chart-Lp topologies. -/
def sourceConnectedThetaL1Homeomorph (A : VariableComplexAtlas X) (x : X)
    (θ : AtlasClosedRealOneOneForm A) :
    letI := A.sourceConnectedNativeChartedSpace x
    letI := A.sourceConnectedNativeComplexManifold x
    letI := A.sourceAtlasThetaPotentialL1Topology x θ
    A.SourceAtlasThetaPotentialL1 θ ≃ₜ
      SGPT.Foundations.Analysis.Pending.ThetaPshL1Topology.ThetaPshL1
        (A.sourceConnectedNativeForm x θ).val := by
  let := A.sourceConnectedNativeChartedSpace x
  let := A.sourceConnectedNativeComplexManifold x
  let := A.sourceAtlasThetaPotentialL1Topology x θ
  exact (A.sourceConnectedThetaL1EquivNative x θ).toHomeomorphOfIsInducing
    (Topology.IsInducing.induced _)

/-- EXACT actual original chart-local L1 semantics for every original
index filter, including every original chart and all pole values. -/
theorem sourceAtlasThetaPotentialL1_tendsto_iff (A : VariableComplexAtlas X) (x : X)
    (θ : AtlasClosedRealOneOneForm A) {I : Type*} {F : Filter I}
    (f : I → A.SourceAtlasThetaPotentialL1 θ) (g : A.SourceAtlasThetaPotentialL1 θ) :
    letI := A.sourceAtlasThetaPotentialL1Topology x θ
    Tendsto f F (𝓝 g) ↔ A.SourceAtlasCanonicalL1Tendsto (fun i => (f i).val) F g.val := by
  let := A.sourceConnectedNativeChartedSpace x
  let := A.sourceConnectedNativeComplexManifold x
  let := A.sourceAtlasThetaPotentialL1Topology x θ
  rw [(A.sourceConnectedThetaL1Homeomorph x θ).isInducing.tendsto_nhds_iff,
    SGPT.Foundations.Analysis.Pending.ThetaPshL1Topology.tendsto_iff_manifoldL1LocallyTendsto]
  exact A.sourceConnected_manifoldL1_iff x (fun i => (f i).val) F g.val

/-- The full original L1 topology is independent of the point used to
manufacture its native presentation: every original chart error is the same. -/
theorem sourceAtlasThetaPotentialL1Topology_independent (A : VariableComplexAtlas X)
    (x y : X) (θ : AtlasClosedRealOneOneForm A) :
    A.sourceAtlasThetaPotentialL1Topology x θ = A.sourceAtlasThetaPotentialL1Topology y θ := by
  apply TopologicalSpace.ext_nhds
  intro g
  apply le_antisymm
  · have hc := (A.sourceAtlasThetaPotentialL1_tendsto_iff x θ
      (F := @nhds _ (A.sourceAtlasThetaPotentialL1Topology x θ) g) id g).mp tendsto_id
    exact tendsto_id'.mp ((A.sourceAtlasThetaPotentialL1_tendsto_iff y θ
      (F := @nhds _ (A.sourceAtlasThetaPotentialL1Topology x θ) g) id g).mpr hc)
  · have hc := (A.sourceAtlasThetaPotentialL1_tendsto_iff y θ
      (F := @nhds _ (A.sourceAtlasThetaPotentialL1Topology y θ) g) id g).mp tendsto_id
    exact tendsto_id'.mp ((A.sourceAtlasThetaPotentialL1_tendsto_iff x θ
      (F := @nhds _ (A.sourceAtlasThetaPotentialL1Topology y θ) g) id g).mpr hc)

end SGPT.PSH.VariableComplexAtlas
