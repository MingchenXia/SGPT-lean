import SGPT.PSH.AtlasComponentHomeomorphism
import SGPT.PSH.AtlasNativeReanchor
import SGPT.PSH.AtlasNativeComponentHolomorphicOn
import SGPT.PSH.NativeQPSHPullback
import SGPT.PSH.LogResolution
import SGPT.Foundations.Analysis.Pending.NormalCrossingsInvariance
import SGPT.Foundations.Analysis.Pending.MarkedIdealBiholomorphism

/-!
# Disjoint unions of native manifolds as varying-dimension manifolds

Infrastructure for `thm:resolvelogsing` on complex manifolds whose connected components have
different dimensions (`chapter_pshfunctions.tex`, `def:logres`, `thm:resolvelogsing`).

* `contMDiffOn_native_toComponent`, `contMDiffOn_component_toNative`: maps between a native
  pure-dimensional manifold and the native structure of a connected component of a varying-
  dimension manifold (`VariableComplexAtlas.componentChartedSpace`) are holomorphic as soon as
  the underlying maps are holomorphic in the original charts.
* `isHolomorphic_comp`: composition of holomorphic maps between varying-dimension manifolds.
* For the disjoint union `Σ c, C c` of native manifolds with its varying-dimension atlas
  `sigmaNativeAtlas`: the inclusions `Sigma.mk c` are holomorphic (`sigmaMk_isHolomorphic`), the
  projections `sigmaProj c y₀` are holomorphic on the open piece `range (Sigma.mk c)`
  (`sigmaProj_isHolomorphicOn`), maps out of the union are holomorphic iff they are on every
  piece (`isHolomorphic_sigma_of_forall`), and for a connected piece `C c` the connected
  component of `⟨c, y⟩` with its native structure is biholomorphic to `C c`
  (`sigmaComponentHomeomorph`, `sigmaComponentHomeomorph_contMDiff`,
  `sigmaComponentHomeomorph_symm_contMDiff`).
* `isSNC_geometricQDivisorBiholomorphicPreimage` (and the version with a dimension equality):
  simple normal crossing divisors pull back to simple normal crossing divisors along
  biholomorphisms.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas.LogResFin

open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.PSH.VariableComplexAtlas.SourceCohomologyDraft
open scoped Topology Manifold ContDiff

universe u v

/-! ### Dimension transport of charts -/

section Transport

variable {Z : Type*} [TopologicalSpace Z]

private theorem transport_apply {d m : ℕ} (e : OpenPartialHomeomorph Z (ComplexModel d))
    (h : d = m) (z : Z) :
    nativeCoordinateDimensionTransport e h z = h ▸ e z := by
  subst h
  rfl

private theorem transport_apply_contDiffOn {d m k : ℕ}
    (e : OpenPartialHomeomorph Z (ComplexModel d)) (h : d = m) (G : ComplexModel k → Z)
    (s : Set (ComplexModel k)) (hs : ContDiffOn ℂ ∞ (e ∘ G) s) :
    ContDiffOn ℂ ∞ (nativeCoordinateDimensionTransport e h ∘ G) s := by
  subst h
  exact hs

private theorem transport_symm_contDiffOn {d m k : ℕ}
    (e : OpenPartialHomeomorph Z (ComplexModel d)) (h : d = m) (H : Z → ComplexModel k)
    (S : Set Z) (hs : ContDiffOn ℂ ∞ (H ∘ e.symm) (e.target ∩ e.symm ⁻¹' S)) :
    ContDiffOn ℂ ∞ (H ∘ (nativeCoordinateDimensionTransport e h).symm)
      ((nativeCoordinateDimensionTransport e h).target ∩
        (nativeCoordinateDimensionTransport e h).symm ⁻¹' S) := by
  subst h
  exact hs

end Transport

/-! ### Native manifolds and native components -/

section NativeComponent

variable {Y : Type v} [TopologicalSpace Y] {B : VariableComplexAtlas Y}
  {k : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel k) M]
  [IsManifold 𝓘(ℂ, ComplexModel k) ∞ M]

/-- A map from a native manifold into a connected component of a varying-dimension manifold is
holomorphic on an open set where it agrees with a map holomorphic in the original charts. -/
theorem contMDiffOn_native_toComponent {f : M → Y} {Q : Set M} (hQ : IsOpen Q)
    (hf : (ofFixedModel k M).IsHolomorphicOn B f Q) (y : Y) (F : M → B.componentOpen y)
    (hF : ∀ p ∈ Q, (F p : Y) = f p) :
    letI := B.componentChartedSpace y
    ContMDiffOn 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel (B.pointDimension y)) ∞ F Q := by
  let := B.componentChartedSpace y
  let := B.componentIsManifold y
  apply contMDiffOn_iff.mpr
  refine ⟨(Topology.IsInducing.continuousOn_iff Topology.IsInducing.subtypeVal).mpr
    (hf.1.congr fun p hp => hF p hp), ?_⟩
  intro x q
  let j := Classical.choose (B.componentChart_cover y q)
  simp only [extChartAt_coe, extChartAt_coe_symm, extChartAt_source, extChartAt_target,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.range_id, Set.preimage_id,
    Set.inter_univ, Function.comp_id, Function.id_comp]
  change ContDiffOn ℂ ∞ ((B.componentChart y j) ∘ F ∘ (chartAt (ComplexModel k) x).symm)
    ((chartAt (ComplexModel k) x).target ∩ (chartAt (ComplexModel k) x).symm ⁻¹'
      (Q ∩ F ⁻¹' (B.componentChart y j).source))
  let e := chartAt (ComplexModel k) x
  let S := e.target ∩ e.symm ⁻¹' (Q ∩ f ⁻¹' (B.chart j.val).source)
  have hS : IsOpen S :=
    e.isOpen_inter_preimage_symm (hf.1.isOpen_inter_preimage hQ (B.chart j.val).open_source)
  have hamb : ContDiffOn ℂ ∞ (B.chart j.val ∘ f ∘ e.symm) S :=
    contDiffOn_of_differentiableOn_complex
      (hf.2 ⟨e, chart_mem_atlas (ComplexModel k) x⟩ j.val) hS
  have ht := transport_apply_contDiffOn (B.chart j.val) (B.componentChartDimension y j)
    (f ∘ e.symm) S hamb
  refine (ht.mono ?_).congr ?_
  · rintro z ⟨hz, hzQ, hzF⟩
    refine ⟨hz, hzQ, ?_⟩
    rw [mem_preimage, B.componentChart_source y j, mem_preimage, hF _ hzQ] at hzF
    exact hzF
  · rintro z ⟨_, hzQ, _⟩
    change nativeCoordinateDimensionTransport (B.chart j.val) (B.componentChartDimension y j)
      (F (e.symm z)).val = nativeCoordinateDimensionTransport (B.chart j.val)
        (B.componentChartDimension y j) (f (e.symm z))
    rw [hF _ hzQ]

/-- A map from a connected component of a varying-dimension manifold into a native manifold is
holomorphic on (the trace of) an open set where it agrees with a map holomorphic in the original
charts. -/
theorem contMDiffOn_component_toNative {g : Y → M} {Q : Set Y} (hQ : IsOpen Q)
    (hg : B.IsHolomorphicOn (ofFixedModel k M) g Q) (y : Y) (G : B.componentOpen y → M)
    (hG : ∀ p : B.componentOpen y, p.val ∈ Q → G p = g p.val) :
    letI := B.componentChartedSpace y
    ContMDiffOn 𝓘(ℂ, ComplexModel (B.pointDimension y)) 𝓘(ℂ, ComplexModel k) ∞ G
      (Subtype.val ⁻¹' Q) := by
  let := B.componentChartedSpace y
  let := B.componentIsManifold y
  apply contMDiffOn_iff.mpr
  refine ⟨(hg.1.comp continuous_subtype_val.continuousOn (fun _ hp => hp)).congr
    fun p hp => hG p hp, ?_⟩
  intro p q
  let i := Classical.choose (B.componentChart_cover y p)
  simp only [extChartAt_coe, extChartAt_coe_symm, extChartAt_source, extChartAt_target,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.range_id, Set.preimage_id,
    Set.inter_univ, Function.comp_id, Function.id_comp]
  change ContDiffOn ℂ ∞ ((chartAt (ComplexModel k) q) ∘ G ∘ (B.componentChart y i).symm)
    ((B.componentChart y i).target ∩ (B.componentChart y i).symm ⁻¹'
      (Subtype.val ⁻¹' Q ∩ G ⁻¹' (chartAt (ComplexModel k) q).source))
  let e := chartAt (ComplexModel k) q
  let S := (B.chart i.val).target ∩ (B.chart i.val).symm ⁻¹' (Q ∩ g ⁻¹' e.source)
  have hS : IsOpen S := (B.chart i.val).isOpen_inter_preimage_symm
    (hg.1.isOpen_inter_preimage hQ e.open_source)
  have hamb : ContDiffOn ℂ ∞ (e ∘ g ∘ (B.chart i.val).symm) S :=
    contDiffOn_of_differentiableOn_complex
      (hg.2 i.val ⟨e, chart_mem_atlas (ComplexModel k) q⟩) hS
  have ht := transport_symm_contDiffOn (B.chart i.val) (B.componentChartDimension y i)
    (e ∘ g) (Q ∩ g ⁻¹' e.source) hamb
  let c := nativeCoordinateDimensionTransport (B.chart i.val) (B.componentChartDimension y i)
  have hsymm : ∀ z ∈ (B.componentChart y i).target,
      ((B.componentChart y i).symm z).val = c.symm z := fun z hz =>
    c.subtypeRestr_symm_apply (B.componentNonempty y) hz
  refine (ht.mono ?_).congr ?_
  · rintro z ⟨hz, hzQ, hzG⟩
    have hval := hsymm z hz
    refine ⟨c.subtypeRestr_target_subset (B.componentNonempty y) hz, ?_, ?_⟩
    · change c.symm z ∈ Q
      rw [← hval]
      exact hzQ
    · change g (c.symm z) ∈ e.source
      rw [← hval, ← hG _ hzQ]
      exact hzG
  · rintro z ⟨hz, hzQ, _⟩
    change e (G ((B.componentChart y i).symm z)) = e (g (c.symm z))
    rw [hG _ hzQ, hsymm z hz]

end NativeComponent

/-! ### Composition of holomorphic maps -/

section Composition

variable {X : Type u} {Y : Type v} {W : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace W] {A : VariableComplexAtlas X} {B : VariableComplexAtlas Y}
  {C : VariableComplexAtlas W}

/-- Holomorphic maps between varying-dimension manifolds compose. -/
theorem isHolomorphic_comp {f : X → Y} {g : Y → W} (hf : A.IsHolomorphic B f)
    (hg : B.IsHolomorphic C g) : A.IsHolomorphic C (g ∘ f) := by
  refine ⟨hg.1.comp hf.1, ?_⟩
  intro i k z hz
  obtain ⟨hzt, hzs⟩ := hz
  set x := (A.chart i).symm z with hx
  obtain ⟨j, hj⟩ := B.cover (f x)
  have hOf : IsOpen ((A.chart i).target ∩ (A.chart i).symm ⁻¹' (f ⁻¹' (B.chart j).source)) :=
    (A.chart i).isOpen_inter_preimage_symm ((B.chart j).open_source.preimage hf.1)
  have hzOf : z ∈ (A.chart i).target ∩ (A.chart i).symm ⁻¹' (f ⁻¹' (B.chart j).source) :=
    ⟨hzt, hj⟩
  have hOg : IsOpen ((B.chart j).target ∩ (B.chart j).symm ⁻¹' (g ⁻¹' (C.chart k).source)) :=
    (B.chart j).isOpen_inter_preimage_symm ((C.chart k).open_source.preimage hg.1)
  have hwOg : B.chart j (f x) ∈
      (B.chart j).target ∩ (B.chart j).symm ⁻¹' (g ⁻¹' (C.chart k).source) := by
    refine ⟨(B.chart j).map_source hj, ?_⟩
    rw [mem_preimage, (B.chart j).left_inv hj]
    exact hzs
  have hdf : DifferentiableAt ℂ (fun w => B.chart j (f ((A.chart i).symm w))) z :=
    (hf.2 i j z hzOf).differentiableAt (hOf.mem_nhds hzOf)
  have hdg : DifferentiableAt ℂ (fun w => C.chart k (g ((B.chart j).symm w)))
      (B.chart j (f x)) :=
    (hg.2 j k _ hwOg).differentiableAt (hOg.mem_nhds hwOg)
  have hcomp : DifferentiableAt ℂ
      ((fun w => C.chart k (g ((B.chart j).symm w))) ∘
        (fun w => B.chart j (f ((A.chart i).symm w)))) z := hdg.comp z hdf
  apply DifferentiableAt.differentiableWithinAt
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [hOf.mem_nhds hzOf] with w hw
  change C.chart k (g (f ((A.chart i).symm w))) =
    C.chart k (g ((B.chart j).symm (B.chart j (f ((A.chart i).symm w)))))
  rw [(B.chart j).left_inv hw.2]

end Composition

/-! ### Disjoint unions of native manifolds -/

section Sigma

variable {I : Type u} {C : I → Type u} [∀ c, TopologicalSpace (C c)] {n : I → ℕ}
  [∀ c, ChartedSpace (ComplexModel (n c)) (C c)] [∀ c, IsComplexManifold (n c) (C c)]

local notation "SA" => sigmaNativeAtlas (n := n) (C := C)

/-- The inclusion of a piece into the disjoint union is holomorphic. -/
theorem sigmaMk_isHolomorphic (c : I) :
    (ofFixedModel (n c) (C c)).IsHolomorphic (SA) (Sigma.mk c) := by
  classical
  refine ⟨continuous_sigmaMk, ?_⟩
  rintro e ⟨d, f⟩
  by_cases hdc : d = c
  · subst hdc
    refine (((ofFixedModel (n d) (C d)).holomorphic e f).mono ?_).congr ?_
    · rintro z ⟨hzt, hzs⟩
      obtain ⟨w, hw, hwz⟩ := hzs
      refine ⟨hzt, ?_⟩
      have h2 : w = e.val.symm z := sigma_mk_injective hwz
      change e.val.symm z ∈ f.val.source
      rw [← h2]
      exact hw
    · intro z _
      exact OpenPartialHomeomorph.lift_openEmbedding_apply _ Topology.IsOpenEmbedding.sigmaMk
  · rintro z ⟨_, hzs⟩
    exfalso
    obtain ⟨w, _, hw⟩ := hzs
    exact hdc (congrArg Sigma.fst hw)

open Classical in
/-- The projection of the disjoint union onto one piece (a default point off the piece). -/
def sigmaProj (c : I) (y₀ : C c) (p : (c : I) × C c) : C c :=
  if h : p.1 = c then h ▸ p.2 else y₀

omit [∀ c, TopologicalSpace (C c)] in
@[simp]
theorem sigmaProj_mk (c : I) (y₀ : C c) (z : C c) : sigmaProj c y₀ ⟨c, z⟩ = z := by
  simp [sigmaProj]

omit [∀ c, TopologicalSpace (C c)] in
theorem sigmaProj_comp_mk (c : I) (y₀ : C c) : sigmaProj c y₀ ∘ Sigma.mk c = id :=
  funext fun z => sigmaProj_mk c y₀ z

/-- The projection onto a piece is holomorphic on that (open) piece. -/
theorem sigmaProj_isHolomorphicOn (c : I) (y₀ : C c) :
    (SA).IsHolomorphicOn (ofFixedModel (n c) (C c)) (sigmaProj c y₀) (range (Sigma.mk c)) := by
  classical
  refine ⟨?_, ?_⟩
  · rintro _ ⟨z, rfl⟩
    apply ContinuousAt.continuousWithinAt
    apply (Topology.IsOpenEmbedding.sigmaMk.continuousAt_iff).mp
    rw [sigmaProj_comp_mk]
    exact continuousAt_id
  · rintro ⟨d, f⟩ e
    by_cases hdc : d = c
    · subst hdc
      refine (((ofFixedModel (n d) (C d)).holomorphic f e).mono ?_).congr ?_
      · rintro z ⟨hzt, _, hze⟩
        refine ⟨hzt, ?_⟩
        change sigmaProj d y₀ (Sigma.mk d (f.val.symm z)) ∈ e.val.source at hze
        rw [sigmaProj_mk] at hze
        exact hze
      · intro z _
        change e.val (sigmaProj d y₀ (Sigma.mk d (f.val.symm z))) = e.val (f.val.symm z)
        rw [sigmaProj_mk]
    · rintro z ⟨_, ⟨w, hw⟩, _⟩
      exfalso
      change Sigma.mk c w = Sigma.mk d (f.val.symm z) at hw
      exact hdc (congrArg Sigma.fst hw).symm

/-- A map out of the disjoint union is holomorphic as soon as it is holomorphic on every piece. -/
theorem isHolomorphic_sigma_of_forall {X : Type v} [TopologicalSpace X]
    (A : VariableComplexAtlas X) (F : ((c : I) × C c) → X)
    (hF : ∀ c, (ofFixedModel (n c) (C c)).IsHolomorphic A (F ∘ Sigma.mk c)) :
    (SA).IsHolomorphic A F := by
  refine ⟨continuous_sigma fun c => (hF c).1, ?_⟩
  rintro ⟨d, f⟩ i
  exact (hF d).2 f i

/-- The native dimension of the component of `⟨c, y⟩` in the disjoint union is that of `C c`. -/
theorem sigma_pointDimension (c : I) (y : C c) : (SA).pointDimension ⟨c, y⟩ = n c :=
  (SA).pointDimension_eq_chart ⟨c, y⟩ ⟨c, complexChartAt (n := n c) y⟩
    ⟨y, mem_complexChartAt_source y, rfl⟩

variable (c : I) (y : C c) [ConnectedSpace (C c)]

omit [ConnectedSpace (C c)] in
theorem sigma_connectedComponent_subset_range :
    connectedComponent (⟨c, y⟩ : (c : I) × C c) ⊆ range (Sigma.mk c) :=
  (isClopen_range_sigmaMk : IsClopen (range (Sigma.mk c : C c → (c : I) × C c))).connectedComponent_subset ⟨y, rfl⟩

theorem sigma_mk_mem_connectedComponent (z : C c) :
    (⟨c, z⟩ : (c : I) × C c) ∈ connectedComponent (⟨c, y⟩ : (c : I) × C c) :=
  (isPreconnected_range continuous_sigmaMk).subset_connectedComponent ⟨y, rfl⟩ ⟨z, rfl⟩

/-- For a connected piece `C c`, the connected component of `⟨c, y⟩` in the disjoint union is
homeomorphic to `C c` (by the projection). -/
def sigmaComponentHomeomorph : (SA).componentOpen ⟨c, y⟩ ≃ₜ C c where
  toFun p := sigmaProj c y p.val
  invFun z := ⟨⟨c, z⟩, sigma_mk_mem_connectedComponent c y z⟩
  left_inv p := by
    obtain ⟨w, hw⟩ := sigma_connectedComponent_subset_range c y p.property
    apply Subtype.ext
    change (⟨c, sigmaProj c y p.val⟩ : (c : I) × C c) = p.val
    rw [← hw, sigmaProj_mk]
  right_inv z := sigmaProj_mk c y z
  continuous_toFun := by
    have h := (sigmaProj_isHolomorphicOn (n := n) c y).1.comp
      (continuous_subtype_val.continuousOn (s := (univ : Set ((SA).componentOpen ⟨c, y⟩))))
      (fun p _ => sigma_connectedComponent_subset_range c y p.property)
    exact continuousOn_univ.mp h
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_sigmaMk

theorem sigmaComponentHomeomorph_apply (p : (SA).componentOpen ⟨c, y⟩) :
    sigmaComponentHomeomorph (n := n) c y p = sigmaProj c y p.val := rfl

theorem sigmaComponentHomeomorph_symm_apply (z : C c) :
    ((sigmaComponentHomeomorph (n := n) c y).symm z).val = ⟨c, z⟩ := rfl

/-- The component homeomorphism is holomorphic. -/
theorem sigmaComponentHomeomorph_contMDiff :
    letI := (SA).componentChartedSpace ⟨c, y⟩
    ContMDiff 𝓘(ℂ, ComplexModel ((SA).pointDimension ⟨c, y⟩)) 𝓘(ℂ, ComplexModel (n c)) ∞
      (sigmaComponentHomeomorph (n := n) c y) := by
  let := (SA).componentChartedSpace ⟨c, y⟩
  have h := contMDiffOn_component_toNative (isOpen_range_sigmaMk)
    (sigmaProj_isHolomorphicOn (n := n) c y) ⟨c, y⟩ (sigmaComponentHomeomorph (n := n) c y) (fun _ _ => rfl)
  have huniv : (Subtype.val ⁻¹' range (Sigma.mk c) : Set ((SA).componentOpen ⟨c, y⟩)) = univ :=
    eq_univ_of_forall fun p => sigma_connectedComponent_subset_range c y p.property
  rw [huniv] at h
  exact contMDiffOn_univ.mp h

/-- The inverse of the component homeomorphism is holomorphic. -/
theorem sigmaComponentHomeomorph_symm_contMDiff :
    letI := (SA).componentChartedSpace ⟨c, y⟩
    ContMDiff 𝓘(ℂ, ComplexModel (n c)) 𝓘(ℂ, ComplexModel ((SA).pointDimension ⟨c, y⟩)) ∞
      (sigmaComponentHomeomorph (n := n) c y).symm := by
  let := (SA).componentChartedSpace ⟨c, y⟩
  have hf : (ofFixedModel (n c) (C c)).IsHolomorphicOn (SA) (Sigma.mk c) univ := by
    refine ⟨(sigmaMk_isHolomorphic (n := n) c).1.continuousOn, ?_⟩
    intro i j
    exact ((sigmaMk_isHolomorphic (n := n) c).2 i j).mono fun z hz => ⟨hz.1, hz.2.2⟩
  have h := contMDiffOn_native_toComponent isOpen_univ hf ⟨c, y⟩
    (sigmaComponentHomeomorph (n := n) c y).symm (fun _ _ => rfl)
  exact contMDiffOn_univ.mp h

end Sigma

/-! ### Simple normal crossing divisors along biholomorphisms -/

section SNC

variable {m : ℕ} {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (ComplexModel m) M] [IsComplexManifold m M]
  [ChartedSpace (ComplexModel m) N] [IsComplexManifold m N]

/-- The preimage of a simple normal crossing divisor under a biholomorphism is simple normal
crossing. -/
theorem isSNC_geometricQDivisorBiholomorphicPreimage (D : EffectiveGeometricQDivisor m N)
    (e : M ≃ₜ N) (he : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel m) ∞ e)
    (hei : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel m) ∞ e.symm) (hD : D.IsSNC) :
    (geometricQDivisorBiholomorphicPreimage D e he hei).IsSNC := by
  obtain ⟨ι, H, hLF, hcl, hsupp, hloc⟩ := hD
  refine ⟨ι, fun i => e ⁻¹' H i, hLF.preimage_continuous e.continuous,
    fun i => (hcl i).preimage e.continuous, ?_, ?_⟩
  · rw [geometricQDivisorBiholomorphicPreimage_support, hsupp, preimage_iUnion]
  · intro x
    obtain ⟨S, hS, hcard, hinj⟩ := hloc (e x)
    refine ⟨S, ?_, fun i hi => hcard i hi, fun i hi j hj hij => hinj hi hj hij⟩
    exact Pending.NormalCrossingsInvariance.isCoordinateFamilyAt_of_preimage he
      (Pending.MarkedIdealBiholomorphism.notMem_exceptionalLocus_of_inverse he hei
        e.apply_symm_apply e.symm_apply_apply x)
      isOpen_univ (mem_univ x) (fun _ _ _ => Iff.rfl) hS

/-- The same, with a substitution of equal native dimensions. -/
theorem isSNC_geometricQDivisorBiholomorphicPreimageOfDimensionEq {a b : ℕ}
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (ComplexModel a) M] [IsComplexManifold a M]
    [ChartedSpace (ComplexModel b) N] [IsComplexManifold b N]
    (h : a = b) (D : EffectiveGeometricQDivisor b N) (e : M ≃ₜ N)
    (he : ContMDiff 𝓘(ℂ, ComplexModel a) 𝓘(ℂ, ComplexModel b) ∞ e)
    (hei : ContMDiff 𝓘(ℂ, ComplexModel b) 𝓘(ℂ, ComplexModel a) ∞ e.symm) (hD : D.IsSNC) :
    (geometricQDivisorBiholomorphicPreimageOfDimensionEq h D e he hei).IsSNC := by
  subst h
  exact isSNC_geometricQDivisorBiholomorphicPreimage D e he hei hD

end SNC

end SGPT.PSH.VariableComplexAtlas.LogResFin
