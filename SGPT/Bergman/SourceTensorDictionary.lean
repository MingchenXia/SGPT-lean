import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Topology.VectorBundle.Constructions
import Mathlib.Analysis.Normed.Module.FiniteDimension
import SGPT.Foundations.Analysis.FirstPass.ComplexManifold
import SGPT.Bergman.SourceCompactHolomorphicSections

-- PORT-SOURCE quantization-tensor-dictionary/SourceTensorDictionary.lean; mathematical source retained.

set_option autoImplicit false
noncomputable section

namespace SGPT.Bergman.TensorDictionaryDraft

open Bundle Set Filter TensorProduct Topology
open scoped TensorProduct Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass

variable {X : Type*} [TopologicalSpace X]
  (V W : X → Type*)
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℂ (V x)]
  [∀ x, NormedAddCommGroup (W x)] [∀ x, InnerProductSpace ℂ (W x)]
  [TopologicalSpace (TotalSpace ℂ V)] [FiberBundle ℂ V] [VectorBundle ℂ ℂ V]
  [TopologicalSpace (TotalSpace ℂ W)] [FiberBundle ℂ W] [VectorBundle ℂ ℂ W]

/-- Literal original tensor fibers with the SAME canonical Hermitian tensor product. -/
abbrev TensorFiber (x : X) := V x ⊗[ℂ] W x

/-- Total algebraic tensor-coordinate map from actual original frame maps. -/
def tensorCoordinate
    (e : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ V → X))
    (f : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ W → X))
    [MemTrivializationAtlas e] [MemTrivializationAtlas f] (x : X) :
    TensorFiber V W x →ₗ[ℂ] ℂ :=
  (TensorProduct.lid ℂ ℂ).toLinearMap.comp
    (TensorProduct.map (e.linearMapAt ℂ x) (f.linearMapAt ℂ x))

/-- The coordinate is a true whole-fiber linear equivalence on its actual base. -/
def tensorCoordinateEquiv
    (e : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ V → X))
    (f : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ W → X))
    [MemTrivializationAtlas e] [MemTrivializationAtlas f] (x : X)
    (hx : x ∈ e.baseSet) (hy : x ∈ f.baseSet) : TensorFiber V W x ≃ₗ[ℂ] ℂ :=
  (TensorProduct.congr (e.linearEquivAt ℂ x hx) (f.linearEquivAt ℂ x hy)).trans
    (TensorProduct.lid ℂ ℂ)

theorem tensorCoordinate_tmul
    (e : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ V → X))
    (f : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ W → X))
    [MemTrivializationAtlas e] [MemTrivializationAtlas f] (x : X) (u : V x) (v : W x) :
    tensorCoordinate V W e f x (u ⊗ₜ[ℂ] v) =
      e.linearMapAt ℂ x u * f.linearMapAt ℂ x v := by
  simp [tensorCoordinate, TensorProduct.map_tmul, TensorProduct.lid_tmul, smul_eq_mul]

theorem tensorCoordinate_eq_equiv
    (e : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ V → X))
    (f : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ W → X))
    [MemTrivializationAtlas e] [MemTrivializationAtlas f] (x : X)
    (hx : x ∈ e.baseSet) (hy : x ∈ f.baseSet) :
    tensorCoordinate V W e f x = (tensorCoordinateEquiv V W e f x hx hy).toLinearMap := by
  ext u v
  change tensorCoordinate V W e f x (u ⊗ₜ[ℂ] v) =
    tensorCoordinateEquiv V W e f x hx hy (u ⊗ₜ[ℂ] v)
  simp only [tensorCoordinate_tmul, tensorCoordinateEquiv,
    LinearEquiv.trans_apply, TensorProduct.congr_tmul, TensorProduct.lid_tmul, smul_eq_mul]
  rw [Trivialization.coe_linearMapAt_of_mem e hx, Trivialization.coe_linearMapAt_of_mem f hy]
  rfl

/-- The exact inverse uses the SAME original frame tensor, on every scalar. -/
theorem tensorCoordinateEquiv_symm_apply
    (e : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ V → X))
    (f : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ W → X))
    [MemTrivializationAtlas e] [MemTrivializationAtlas f] (x : X)
    (hx : x ∈ e.baseSet) (hy : x ∈ f.baseSet) (z : ℂ) :
    (tensorCoordinateEquiv V W e f x hx hy).symm z =
      z • (e.symm x 1 ⊗ₜ[ℂ] f.symm x 1) := by
  let A := tensorCoordinateEquiv V W e f x hx hy
  have he : e.linearEquivAt ℂ x hx (e.symm x 1) = 1 := congrArg Prod.snd (e.apply_mk_symm hx (1 : ℂ))
  have hf : f.linearEquivAt ℂ x hy (f.symm x 1) = 1 := congrArg Prod.snd (f.apply_mk_symm hy (1 : ℂ))
  apply A.injective
  rw [A.apply_symm_apply, map_smul]
  have hframe : A (e.symm x 1 ⊗ₜ[ℂ] f.symm x 1) = 1 := by
    simp only [A, tensorCoordinateEquiv, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
      TensorProduct.lid_tmul, he, hf, smul_eq_mul, mul_one]
  rw [hframe, smul_eq_mul, mul_one]

/-- Genuine pretrivialization on literal tensor fibers, before total-space topology. -/
def tensorPretrivialization
    (e : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ V → X))
    (f : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ W → X))
    [MemTrivializationAtlas e] [MemTrivializationAtlas f] :
    Pretrivialization ℂ (TotalSpace.proj : TotalSpace ℂ (TensorFiber V W) → X) where
  toFun p := (p.proj, tensorCoordinate V W e f p.proj p.snd)
  invFun p := ⟨p.1, p.2 • (e.symm p.1 1 ⊗ₜ[ℂ] f.symm p.1 1)⟩
  source := TotalSpace.proj ⁻¹' (e.baseSet ∩ f.baseSet)
  target := (e.baseSet ∩ f.baseSet) ×ˢ Set.univ
  map_source' := fun _ h => ⟨h, Set.mem_univ _⟩
  map_target' := fun _ h => h.1
  left_inv' := by
    rintro ⟨x, t⟩ ⟨hx, hy⟩
    simp only [TotalSpace.mk_inj]
    rw [← tensorCoordinateEquiv_symm_apply V W e f x hx hy,
      tensorCoordinate_eq_equiv V W e f x hx hy]
    exact (tensorCoordinateEquiv V W e f x hx hy).symm_apply_apply t
  right_inv' := by
    rintro ⟨x, z⟩ ⟨⟨hx, hy⟩, _⟩
    change (x, tensorCoordinate V W e f x (z • (e.symm x 1 ⊗ₜ[ℂ] f.symm x 1))) = (x, z)
    apply Prod.ext
    · rfl
    change tensorCoordinate V W e f x (z • (e.symm x 1 ⊗ₜ[ℂ] f.symm x 1)) = z
    rw [← tensorCoordinateEquiv_symm_apply V W e f x hx hy,
      tensorCoordinate_eq_equiv V W e f x hx hy]
    exact (tensorCoordinateEquiv V W e f x hx hy).apply_symm_apply z
  open_target := (e.open_baseSet.inter f.open_baseSet).prod isOpen_univ
  baseSet := e.baseSet ∩ f.baseSet
  open_baseSet := e.open_baseSet.inter f.open_baseSet
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

instance tensorPretrivialization_isLinear
    (e : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ V → X))
    (f : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ W → X))
    [MemTrivializationAtlas e] [MemTrivializationAtlas f] :
    (tensorPretrivialization V W e f).IsLinear ℂ where
  linear x _ :=
    { map_add := by intro u v; exact map_add (tensorCoordinate V W e f x) u v
      map_smul := by intro c u; exact map_smul (tensorCoordinate V W e f x) c u }

theorem tensorPretrivialization_symm
    (e : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ V → X))
    (f : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ W → X))
    [MemTrivializationAtlas e] [MemTrivializationAtlas f] {x : X}
    (hx : x ∈ e.baseSet ∩ f.baseSet) (z : ℂ) :
    (tensorPretrivialization V W e f).symm x z = z • (e.symm x 1 ⊗ₜ[ℂ] f.symm x 1) := by
  have h := (tensorPretrivialization V W e f).mk_symm hx z
  change (⟨x, (tensorPretrivialization V W e f).symm x z⟩ : TotalSpace ℂ (TensorFiber V W)) =
    ⟨x, z • (e.symm x 1 ⊗ₜ[ℂ] f.symm x 1)⟩ at h
  simpa only [TotalSpace.mk_inj] using h

/-- The literal product of the two ORIGINAL transition coefficients. -/
def tensorCoordChange
    (e e' : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ V → X))
    (f f' : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ W → X))
    [MemTrivializationAtlas e] [MemTrivializationAtlas e']
    [MemTrivializationAtlas f] [MemTrivializationAtlas f'] (x : X) : ℂ →L[ℂ] ℂ :=
  ContinuousLinearMap.smulRightL ℂ ℂ ℂ (ContinuousLinearMap.id ℂ ℂ)
    ((e.coordChangeL ℂ e' x) 1 * (f.coordChangeL ℂ f' x) 1)

theorem tensorCoordChange_apply
    (e e' : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ V → X))
    (f f' : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ W → X))
    [MemTrivializationAtlas e] [MemTrivializationAtlas e']
    [MemTrivializationAtlas f] [MemTrivializationAtlas f'] {x : X}
    (hx : x ∈ (e.baseSet ∩ f.baseSet) ∩ (e'.baseSet ∩ f'.baseSet)) (z : ℂ) :
    tensorCoordChange V W e e' f f' x z =
      ((tensorPretrivialization V W e' f')
        ⟨x, (tensorPretrivialization V W e f).symm x z⟩).2 := by
  rw [tensorPretrivialization_symm V W e f hx.1]
  change z * ((e.coordChangeL ℂ e' x) 1 * (f.coordChangeL ℂ f' x) 1) =
    tensorCoordinate V W e' f' x (z • (e.symm x 1 ⊗ₜ[ℂ] f.symm x 1))
  rw [map_smul, tensorCoordinate_tmul]
  rw [Trivialization.coordChangeL_apply e e' ⟨hx.1.1, hx.2.1⟩,
    Trivialization.coordChangeL_apply f f' ⟨hx.1.2, hx.2.2⟩,
    Trivialization.coe_linearMapAt_of_mem e' hx.2.1,
    Trivialization.coe_linearMapAt_of_mem f' hx.2.2]
  rfl

theorem tensorCoordChange_continuousOn
    (e e' : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ V → X))
    (f f' : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ W → X))
    [MemTrivializationAtlas e] [MemTrivializationAtlas e']
    [MemTrivializationAtlas f] [MemTrivializationAtlas f'] :
    ContinuousOn (tensorCoordChange V W e e' f f')
      ((e.baseSet ∩ f.baseSet) ∩ (e'.baseSet ∩ f'.baseSet)) := by
  have he : ContinuousOn (fun x => (e.coordChangeL ℂ e' x) (1 : ℂ))
      ((e.baseSet ∩ f.baseSet) ∩ (e'.baseSet ∩ f'.baseSet)) :=
    ((continuousOn_coordChange ℂ e e').clm_apply continuousOn_const).mono
    (fun _ h => ⟨h.1.1, h.2.1⟩)
  have hf : ContinuousOn (fun x => (f.coordChangeL ℂ f' x) (1 : ℂ))
      ((e.baseSet ∩ f.baseSet) ∩ (e'.baseSet ∩ f'.baseSet)) :=
    ((continuousOn_coordChange ℂ f f').clm_apply continuousOn_const).mono
    (fun _ h => ⟨h.1.2, h.2.2⟩)
  exact (ContinuousLinearMap.smulRightL ℂ ℂ ℂ (ContinuousLinearMap.id ℂ ℂ)).continuous.comp_continuousOn
    (he.mul hf)

/-- The actual topology/bundle is manufactured from ALL original atlas pairs. -/
def tensorVectorPrebundle : VectorPrebundle ℂ ℂ (TensorFiber V W) where
  pretrivializationAtlas := {a | ∃ (e : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ V → X))
    (f : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ W → X))
    (_ : MemTrivializationAtlas e) (_ : MemTrivializationAtlas f), a = tensorPretrivialization V W e f}
  pretrivialization_linear' := by
    rintro _ ⟨e, f, he, hf, rfl⟩
    infer_instance
  pretrivializationAt x := tensorPretrivialization V W (trivializationAt ℂ V x) (trivializationAt ℂ W x)
  mem_base_pretrivializationAt x :=
    ⟨mem_baseSet_trivializationAt ℂ V x, mem_baseSet_trivializationAt ℂ W x⟩
  pretrivialization_mem_atlas x :=
    ⟨trivializationAt ℂ V x, trivializationAt ℂ W x, inferInstance, inferInstance, rfl⟩
  exists_coordChange := by
    rintro _ ⟨e, f, he, hf, rfl⟩ _ ⟨e', f', he', hf', rfl⟩
    exact ⟨tensorCoordChange V W e e' f f', tensorCoordChange_continuousOn V W e e' f f',
      fun x hx z => tensorCoordChange_apply V W e e' f f' hx z⟩
  totalSpaceMk_isInducing := by
    intro x
    let e := trivializationAt ℂ V x
    let f := trivializationAt ℂ W x
    have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt ℂ V x
    have hy : x ∈ f.baseSet := mem_baseSet_trivializationAt ℂ W x
    let : FiniteDimensional ℂ (V x) := (e.linearEquivAt ℂ x hx).symm.finiteDimensional
    let : FiniteDimensional ℂ (W x) := (f.linearEquivAt ℂ x hy).symm.finiteDimensional
    let A := (tensorCoordinateEquiv V W e f x hx hy).toContinuousLinearEquiv
    have h : IsInducing (fun t : TensorFiber V W x => (x, A t)) :=
      isInducing_const_prod.mpr A.toHomeomorph.isInducing
    change IsInducing (fun t : TensorFiber V W x => (x, tensorCoordinate V W e f x t))
    have heq : (fun t : TensorFiber V W x => (x, tensorCoordinate V W e f x t)) =
        fun t => (x, A t) := by
      funext t
      rw [tensorCoordinate_eq_equiv V W e f x hx hy]
      rfl
    rw [heq]
    exact h

instance tensorTotalSpaceTopology : TopologicalSpace (TotalSpace ℂ (TensorFiber V W)) :=
  (tensorVectorPrebundle V W).totalSpaceTopology

instance tensorFiberBundle : FiberBundle ℂ (TensorFiber V W) :=
  (tensorVectorPrebundle V W).toFiberBundle

instance tensorVectorBundle : VectorBundle ℂ ℂ (TensorFiber V W) :=
  (tensorVectorPrebundle V W).toVectorBundle

/-- All actual tensor transitions are holomorphic products of ORIGINAL transitions. -/
instance tensorPrebundle_isContMDiff {n : ℕ} [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X]
    [ContMDiffVectorBundle ∞ ℂ V (𝓘(ℂ, ComplexModel n))]
    [ContMDiffVectorBundle ∞ ℂ W (𝓘(ℂ, ComplexModel n))] :
    (tensorVectorPrebundle V W).IsContMDiff (𝓘(ℂ, ComplexModel n)) ∞ where
  exists_contMDiffCoordChange := by
    rintro _ ⟨e, f, he, hf, rfl⟩ _ ⟨e', f', he', hf', rfl⟩
    refine ⟨tensorCoordChange V W e e' f f', ?_,
      fun x hx z => tensorCoordChange_apply V W e e' f f' hx z⟩
    have h₁ : ContMDiffOn (𝓘(ℂ, ComplexModel n)) (𝓘(ℂ, ℂ)) ∞
        (fun x => (e.coordChangeL ℂ e' x) (1 : ℂ))
        ((e.baseSet ∩ f.baseSet) ∩ (e'.baseSet ∩ f'.baseSet)) :=
      ((contMDiffOn_coordChangeL e e').clm_apply contMDiffOn_const).mono
        (fun _ h => ⟨h.1.1, h.2.1⟩)
    have h₂ : ContMDiffOn (𝓘(ℂ, ComplexModel n)) (𝓘(ℂ, ℂ)) ∞
        (fun x => (f.coordChangeL ℂ f' x) (1 : ℂ))
        ((e.baseSet ∩ f.baseSet) ∩ (e'.baseSet ∩ f'.baseSet)) :=
      ((contMDiffOn_coordChangeL f f').clm_apply contMDiffOn_const).mono
        (fun _ h => ⟨h.1.2, h.2.2⟩)
    exact (ContinuousLinearMap.smulRightL ℂ ℂ ℂ (ContinuousLinearMap.id ℂ ℂ)).contMDiff.comp_contMDiffOn
      (h₁.mul h₂)

instance tensorHolomorphicBundle {n : ℕ} [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X]
    [ContMDiffVectorBundle ∞ ℂ V (𝓘(ℂ, ComplexModel n))]
    [ContMDiffVectorBundle ∞ ℂ W (𝓘(ℂ, ComplexModel n))] :
    ContMDiffVectorBundle ∞ ℂ (TensorFiber V W) (𝓘(ℂ, ComplexModel n)) :=
  (tensorVectorPrebundle V W).contMDiffVectorBundle (𝓘(ℂ, ComplexModel n))

/-- ALL actual original product frames survive as genuine tensor-bundle charts. -/
def tensorTrivialization
    (e : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ V → X))
    (f : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ W → X))
    [MemTrivializationAtlas e] [MemTrivializationAtlas f] :
    Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ (TensorFiber V W) → X) :=
  (tensorVectorPrebundle V W).trivializationOfMemPretrivializationAtlas ⟨e, f, inferInstance, inferInstance, rfl⟩

instance tensorTrivialization_memAtlas
    (e : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ V → X))
    (f : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ W → X))
    [MemTrivializationAtlas e] [MemTrivializationAtlas f] :
    MemTrivializationAtlas (tensorTrivialization V W e f) where
  out := ⟨_, ⟨e, f, inferInstance, inferInstance, rfl⟩, rfl⟩

theorem tensorTrivialization_symm
    (e : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ V → X))
    (f : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ W → X))
    [MemTrivializationAtlas e] [MemTrivializationAtlas f] {x : X}
    (hx : x ∈ e.baseSet ∩ f.baseSet) (z : ℂ) :
    (tensorTrivialization V W e f).symm x z = z • (e.symm x 1 ⊗ₜ[ℂ] f.symm x 1) :=
  tensorPretrivialization_symm V W e f hx z

/-- Whole-fiber SAME-metric identity in every actual original product frame. -/
theorem tensor_norm_eq_coordinates
    (e : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ V → X))
    (f : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ W → X))
    [MemTrivializationAtlas e] [MemTrivializationAtlas f] {x : X}
    (hx : x ∈ e.baseSet) (hy : x ∈ f.baseSet) (t : TensorFiber V W x) :
    ‖t‖ = ‖tensorCoordinate V W e f x t‖ * (‖e.symm x 1‖ * ‖f.symm x 1‖) := by
  let A := tensorCoordinateEquiv V W e f x hx hy
  have h : t = A t • (e.symm x 1 ⊗ₜ[ℂ] f.symm x 1) := by
    have hh := tensorCoordinateEquiv_symm_apply V W e f x hx hy (A t)
    rw [A.symm_apply_apply] at hh
    exact hh
  calc
    ‖t‖ = ‖A t • (e.symm x 1 ⊗ₜ[ℂ] f.symm x 1)‖ := congrArg norm h
    _ = ‖A t‖ * (‖e.symm x 1‖ * ‖f.symm x 1‖) := by rw [norm_smul, TensorProduct.norm_tmul]
    _ = _ := by rw [tensorCoordinate_eq_equiv V W e f x hx hy]; rfl

/-- The SAME induced Hermitian tensor metric is genuinely continuous on the actual total space. -/
instance tensorContinuousFiberNorm
    [SGPT.Bergman.CompactHolomorphicSectionsDraft.ContinuousFiberNorm V]
    [SGPT.Bergman.CompactHolomorphicSectionsDraft.ContinuousFiberNorm W] :
    SGPT.Bergman.CompactHolomorphicSectionsDraft.ContinuousFiberNorm (TensorFiber V W) where
  continuous := by
    apply continuous_iff_continuousAt.mpr
    intro p
    let e := trivializationAt ℂ V p.proj
    let f := trivializationAt ℂ W p.proj
    let q := tensorTrivialization V W e f
    have he : p.proj ∈ e.baseSet := mem_baseSet_trivializationAt ℂ V p.proj
    have hf : p.proj ∈ f.baseSet := mem_baseSet_trivializationAt ℂ W p.proj
    have hp : p ∈ q.source := q.mem_source.mpr ⟨he, hf⟩
    have hq : ContinuousAt (fun z : TotalSpace ℂ (TensorFiber V W) => (q z).2) p :=
      (q.continuousAt hp).snd
    have hproj : ContinuousAt (TotalSpace.proj : TotalSpace ℂ (TensorFiber V W) → X) p :=
      (FiberBundle.continuous_proj ℂ (TensorFiber V W)).continuousAt
    have h₁ : ContinuousAt (fun z : TotalSpace ℂ (TensorFiber V W) => ‖e.symm z.proj 1‖) p :=
      ((SGPT.Bergman.CompactHolomorphicSectionsDraft.frameNorm_continuousOn V e).continuousAt
        (e.open_baseSet.mem_nhds he)).comp hproj
    have h₂ : ContinuousAt (fun z : TotalSpace ℂ (TensorFiber V W) => ‖f.symm z.proj 1‖) p :=
      ((SGPT.Bergman.CompactHolomorphicSectionsDraft.frameNorm_continuousOn W f).continuousAt
        (f.open_baseSet.mem_nhds hf)).comp hproj
    have hbase : ∀ᶠ z : TotalSpace ℂ (TensorFiber V W) in 𝓝 p,
        z.proj ∈ e.baseSet ∩ f.baseSet :=
      ((e.open_baseSet.inter f.open_baseSet).preimage
        (FiberBundle.continuous_proj ℂ (TensorFiber V W))).mem_nhds ⟨he, hf⟩
    apply (hq.norm.mul (h₁.mul h₂)).congr_of_eventuallyEq
    filter_upwards [hbase] with z hz
    exact tensor_norm_eq_coordinates V W e f hz.1 hz.2 z.snd

universe u v w

/-- Genuine native bundle/metric data only; no H0, comparison, basis or dimension fields. -/
structure HermitianHolomorphicLineBundle (n : ℕ) (M : Type u) [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] where
  Fiber : M → Type v
  normedFiber : ∀ x, NormedAddCommGroup (Fiber x)
  hermitianFiber : letI := normedFiber; ∀ x, InnerProductSpace ℂ (Fiber x)
  totalTopology : TopologicalSpace (TotalSpace ℂ Fiber)
  fiberBundle : letI := normedFiber; letI := totalTopology; FiberBundle ℂ Fiber
  vectorBundle : letI := normedFiber; letI := hermitianFiber; letI := totalTopology;
    letI := fiberBundle; VectorBundle ℂ ℂ Fiber
  holomorphic : letI := normedFiber; letI := hermitianFiber; letI := totalTopology;
    letI := fiberBundle; letI := vectorBundle;
    ContMDiffVectorBundle ∞ ℂ Fiber (𝓘(ℂ, ComplexModel n))
  normContinuous : letI := normedFiber; letI := totalTopology;
    SGPT.Bergman.CompactHolomorphicSectionsDraft.ContinuousFiberNorm Fiber

attribute [instance] HermitianHolomorphicLineBundle.normedFiber
  HermitianHolomorphicLineBundle.hermitianFiber HermitianHolomorphicLineBundle.totalTopology
  HermitianHolomorphicLineBundle.fiberBundle HermitianHolomorphicLineBundle.vectorBundle
  HermitianHolomorphicLineBundle.holomorphic HermitianHolomorphicLineBundle.normContinuous

namespace HermitianHolomorphicLineBundle

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Original native geometry enters without any desired tensor/H0/norm comparison field. -/
def ofNative (V : M → Type v) [∀ x, NormedAddCommGroup (V x)]
    [∀ x, InnerProductSpace ℂ (V x)] [TopologicalSpace (TotalSpace ℂ V)]
    [FiberBundle ℂ V] [VectorBundle ℂ ℂ V]
    [ContMDiffVectorBundle ∞ ℂ V (𝓘(ℂ, ComplexModel n))]
    [SGPT.Bergman.CompactHolomorphicSectionsDraft.ContinuousFiberNorm V] :
    HermitianHolomorphicLineBundle.{u,v} n M where
  Fiber := V
  normedFiber := inferInstance
  hermitianFiber := inferInstance
  totalTopology := inferInstance
  fiberBundle := inferInstance
  vectorBundle := inferInstance
  holomorphic := inferInstance
  normContinuous := inferInstance

/-- The genuine literal Hermitian tensor construction, applied to original bundle data. -/
def tensor (L : HermitianHolomorphicLineBundle.{u,v} n M)
    (T : HermitianHolomorphicLineBundle.{u,w} n M) :
    HermitianHolomorphicLineBundle.{u,max v w} n M where
  Fiber := TensorFiber L.Fiber T.Fiber
  normedFiber := inferInstance
  hermitianFiber := inferInstance
  totalTopology := inferInstance
  fiberBundle := inferInstance
  vectorBundle := inferInstance
  holomorphic := inferInstance
  normContinuous := inferInstance

/-- The actual scalar tensor unit has the standard metric and the native trivial bundle. -/
def unit : HermitianHolomorphicLineBundle.{u,0} n M where
  Fiber := Bundle.Trivial M ℂ
  normedFiber := inferInstance
  hermitianFiber := inferInstance
  totalTopology := inferInstance
  fiberBundle := inferInstance
  vectorBundle := inferInstance
  holomorphic := inferInstance
  normContinuous := ⟨(Bundle.Trivial.homeomorphProd M ℂ).continuous.snd.norm⟩

/-- Positive powers use literal successive tensor products, beginning with the SAME L. -/
def positivePower (L : HermitianHolomorphicLineBundle.{u,v} n M) :
    ℕ → HermitianHolomorphicLineBundle.{u,v} n M
  | 0 => L
  | k + 1 => tensor (positivePower L k) L

/-- ALL original degree-k twists: literal scalar-unit tensor T at zero, true positive power tensor T otherwise. -/
def twistedPower (L T : HermitianHolomorphicLineBundle.{u,v} n M) :
    ℕ → HermitianHolomorphicLineBundle.{u,v} n M
  | 0 => tensor unit T
  | k + 1 => tensor (positivePower L k) T

/-- ALL sections of the actual source tensor/twist bundle, rather than a chosen family. -/
abbrev twistedSections (L T : HermitianHolomorphicLineBundle.{u,v} n M) (k : ℕ) :=
  SGPT.Bergman.QuantizationDraft.HolomorphicSections (n := n) (twistedPower L T k).Fiber

/-- The actual constructed family satisfies the general compact H0 theorem internally. -/
theorem twistedSections_finiteDimensional [CompactSpace M]
    (L T : HermitianHolomorphicLineBundle.{u,v} n M) (k : ℕ) :
    FiniteDimensional ℂ (twistedSections L T k) :=
  SGPT.Bergman.CompactHolomorphicSectionsDraft.holomorphicSections_finiteDimensional (twistedPower L T k).Fiber

/-- The literal degree-zero fiber unit is a genuine isometry, proved from tensor algebra. -/
def zeroTwistFiberIsometry (T : HermitianHolomorphicLineBundle.{u,v} n M) (x : M) :
    (tensor unit T).Fiber x ≃ₗᵢ[ℂ] T.Fiber x :=
  TensorProduct.lidIsometry ℂ (T.Fiber x)

/-- Original atlas frames, with only their actual membership proof bundled. -/
def AtlasFrame (L : HermitianHolomorphicLineBundle.{u,v} n M) :=
  {e : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ L.Fiber → M) // MemTrivializationAtlas e}

def tensorAtlasFrame {L : HermitianHolomorphicLineBundle.{u,v} n M}
    {T : HermitianHolomorphicLineBundle.{u,w} n M} (e : AtlasFrame L) (f : AtlasFrame T) :
    AtlasFrame (tensor L T) := by
  letI := e.property
  letI := f.property
  exact ⟨tensorTrivialization L.Fiber T.Fiber e.val f.val,
    tensorTrivialization_memAtlas L.Fiber T.Fiber e.val f.val⟩

def unitAtlasFrame : AtlasFrame (unit (n := n) (M := M)) :=
  ⟨Bundle.Trivial.trivialization M ℂ, ⟨by rfl⟩⟩

def positivePowerAtlasFrame {L : HermitianHolomorphicLineBundle.{u,v} n M} (e : AtlasFrame L) :
    ∀ k : ℕ, AtlasFrame (positivePower L k)
  | 0 => e
  | k + 1 => tensorAtlasFrame (positivePowerAtlasFrame e k) e

def twistedPowerAtlasFrame {L T : HermitianHolomorphicLineBundle.{u,v} n M}
    (e : AtlasFrame L) (f : AtlasFrame T) : ∀ k : ℕ, AtlasFrame (twistedPower L T k)
  | 0 => tensorAtlasFrame unitAtlasFrame f
  | k + 1 => tensorAtlasFrame (positivePowerAtlasFrame e k) f

theorem tensorAtlasFrame_symm {L : HermitianHolomorphicLineBundle.{u,v} n M}
    {T : HermitianHolomorphicLineBundle.{u,w} n M} (e : AtlasFrame L) (f : AtlasFrame T)
    {x : M} (hx : x ∈ e.val.baseSet ∩ f.val.baseSet) (z : ℂ) :
    (tensorAtlasFrame e f).val.symm x z = z • (e.val.symm x 1 ⊗ₜ[ℂ] f.val.symm x 1) := by
  let := e.property
  let := f.property
  exact tensorTrivialization_symm L.Fiber T.Fiber e.val f.val hx z

theorem tensorAtlasFrame_norm_one {L : HermitianHolomorphicLineBundle.{u,v} n M}
    {T : HermitianHolomorphicLineBundle.{u,w} n M} (e : AtlasFrame L) (f : AtlasFrame T)
    {x : M} (hx : x ∈ e.val.baseSet ∩ f.val.baseSet) :
    ‖(tensorAtlasFrame e f).val.symm x 1‖ = ‖e.val.symm x 1‖ * ‖f.val.symm x 1‖ := by
  calc
    _ = ‖(1 : ℂ) • (e.val.symm x 1 ⊗ₜ[ℂ] f.val.symm x 1)‖ :=
      congrArg norm (tensorAtlasFrame_symm e f hx 1)
    _ = _ := by rw [one_smul, TensorProduct.norm_tmul]

theorem positivePowerAtlasFrame_mem {L : HermitianHolomorphicLineBundle.{u,v} n M}
    (e : AtlasFrame L) {x : M} (hx : x ∈ e.val.baseSet) :
    ∀ k, x ∈ (positivePowerAtlasFrame e k).val.baseSet
  | 0 => hx
  | k + 1 => ⟨positivePowerAtlasFrame_mem e hx k, hx⟩

theorem twistedPowerAtlasFrame_mem {L T : HermitianHolomorphicLineBundle.{u,v} n M}
    (e : AtlasFrame L) (f : AtlasFrame T) {x : M}
    (hx : x ∈ e.val.baseSet) (hy : x ∈ f.val.baseSet) :
    ∀ k, x ∈ (twistedPowerAtlasFrame e f k).val.baseSet
  | 0 => ⟨Set.mem_univ x, hy⟩
  | k + 1 => ⟨positivePowerAtlasFrame_mem e hx k, hy⟩

/-- SAME original metric in EVERY original frame, in all positive powers. -/
theorem positivePower_frame_norm {L : HermitianHolomorphicLineBundle.{u,v} n M}
    (e : AtlasFrame L) {x : M} (hx : x ∈ e.val.baseSet) :
    ∀ k, ‖(positivePowerAtlasFrame e k).val.symm x 1‖ = ‖e.val.symm x 1‖ ^ (k + 1)
  | 0 => by
    change ‖e.val.symm x 1‖ = ‖e.val.symm x 1‖ ^ 1
    exact (pow_one _).symm
  | k + 1 => by
    have hn : ‖(positivePowerAtlasFrame e (k + 1)).val.symm x 1‖ =
        ‖(positivePowerAtlasFrame e k).val.symm x 1‖ * ‖e.val.symm x 1‖ :=
      tensorAtlasFrame_norm_one (positivePowerAtlasFrame e k) e ⟨positivePowerAtlasFrame_mem e hx k, hx⟩
    rw [hn, positivePower_frame_norm e hx k]
    exact (pow_succ ‖e.val.symm x 1‖ (k + 1)).symm

/-- The SAME h^k tensor h_T metric, including literal degree zero. -/
theorem twistedPower_frame_norm {L T : HermitianHolomorphicLineBundle.{u,v} n M}
    (e : AtlasFrame L) (f : AtlasFrame T) {x : M}
    (hx : x ∈ e.val.baseSet) (hy : x ∈ f.val.baseSet) :
    ∀ k, ‖(twistedPowerAtlasFrame e f k).val.symm x 1‖ =
      ‖e.val.symm x 1‖ ^ k * ‖f.val.symm x 1‖
  | 0 => by
    have hn : ‖(twistedPowerAtlasFrame e f 0).val.symm x 1‖ =
        ‖(unitAtlasFrame (n := n) (M := M)).val.symm x 1‖ * ‖f.val.symm x 1‖ :=
      tensorAtlasFrame_norm_one unitAtlasFrame f ⟨Set.mem_univ x, hy⟩
    have hu : ‖(unitAtlasFrame (n := n) (M := M)).val.symm x 1‖ = 1 := by
      change ‖(Bundle.Trivial.trivialization M ℂ).symm x 1‖ = 1
      rw [Bundle.Trivial.trivialization_symm_apply, norm_one]
    rw [hn, hu, pow_zero, one_mul]
  | k + 1 => by
    have hn : ‖(twistedPowerAtlasFrame e f (k + 1)).val.symm x 1‖ =
        ‖(positivePowerAtlasFrame e k).val.symm x 1‖ * ‖f.val.symm x 1‖ :=
      tensorAtlasFrame_norm_one (positivePowerAtlasFrame e k) f ⟨positivePowerAtlasFrame_mem e hx k, hy⟩
    rw [hn, positivePower_frame_norm e hx k]

/-- Exact WHOLE-section original squared norm, in every genuine original product frame. -/
theorem twistedSection_norm_sq_frame {L T : HermitianHolomorphicLineBundle.{u,v} n M}
    (e : AtlasFrame L) (f : AtlasFrame T) (k : ℕ) (s : twistedSections L T k)
    {x : M} (hx : x ∈ e.val.baseSet) (hy : x ∈ f.val.baseSet) :
    ‖s x‖ ^ 2 =
      ‖((twistedPowerAtlasFrame e f k).val ⟨x, s x⟩).2‖ ^ 2 *
        (‖e.val.symm x 1‖ ^ 2) ^ k * ‖f.val.symm x 1‖ ^ 2 := by
  let g := twistedPowerAtlasFrame e f k
  let := g.property
  have h := SGPT.Bergman.CompactHolomorphicSectionsDraft.norm_eq_coefficient_mul_frameNorm
    (twistedPower L T k).Fiber g.val s (twistedPowerAtlasFrame_mem e f hx hy k)
  change ‖s x‖ = ‖(g.val ⟨x, s x⟩).2‖ * ‖g.val.symm x 1‖ at h
  rw [h, twistedPower_frame_norm e f hx hy k, mul_pow, mul_pow]
  rw [← pow_mul, ← pow_mul]
  ring

/-- Actual left-unit tensor coordinate agrees with the SAME original T coordinate. -/
theorem zeroTwist_coordinate {T : HermitianHolomorphicLineBundle.{u,v} n M}
    (f : AtlasFrame T) {x : M} (hx : x ∈ f.val.baseSet)
    (t : (tensor unit T).Fiber x) :
    ((tensorAtlasFrame unitAtlasFrame f).val ⟨x, t⟩).2 =
      (f.val ⟨x, zeroTwistFiberIsometry T x t⟩).2 := by
  let := f.property
  let : MemTrivializationAtlas (Bundle.Trivial.trivialization M ℂ) := ⟨by rfl⟩
  have h : tensorCoordinate (Bundle.Trivial M ℂ) T.Fiber
      (Bundle.Trivial.trivialization M ℂ) f.val x =
      (f.val.linearMapAt ℂ x).comp (TensorProduct.lid ℂ (T.Fiber x)).toLinearMap := by
    apply TensorProduct.ext'
    intro a b
    change tensorCoordinate (Bundle.Trivial M ℂ) T.Fiber
      (Bundle.Trivial.trivialization M ℂ) f.val x (a ⊗ₜ[ℂ] b) =
      f.val.linearMapAt ℂ x (TensorProduct.lid ℂ (T.Fiber x) (a ⊗ₜ[ℂ] b))
    simp [tensorCoordinate_tmul, TensorProduct.lid_tmul, map_smul, smul_eq_mul]
  change tensorCoordinate (Bundle.Trivial M ℂ) T.Fiber
    (Bundle.Trivial.trivialization M ℂ) f.val x t = _
  rw [h]
  exact congrFun (Trivialization.coe_linearMapAt_of_mem f.val hx) (zeroTwistFiberIsometry T x t)

/-- The true degree-zero left unit maps EVERY holomorphic section to a holomorphic section. -/
def zeroTwistSection (T : HermitianHolomorphicLineBundle.{u,v} n M)
    (s : SGPT.Bergman.QuantizationDraft.HolomorphicSections (n := n) (tensor unit T).Fiber) :
    SGPT.Bergman.QuantizationDraft.HolomorphicSections (n := n) T.Fiber where
  toFun := fun x => zeroTwistFiberIsometry T x (s x)
  contMDiff_toFun := by
    intro x
    let f : AtlasFrame T := ⟨trivializationAt ℂ T.Fiber x, inferInstance⟩
    let := f.property
    let q := tensorAtlasFrame unitAtlasFrame f
    let := q.property
    have hx : x ∈ f.val.baseSet := mem_baseSet_trivializationAt ℂ T.Fiber x
    apply (f.val.contMDiffAt_section_iff hx).mpr
    have hs := (q.val.contMDiffAt_section_iff (show x ∈ q.val.baseSet from ⟨Set.mem_univ x, hx⟩)).mp (s.contMDiff x)
    apply hs.congr_of_eventuallyEq
    filter_upwards [f.val.open_baseSet.mem_nhds hx] with y hy
    exact (zeroTwist_coordinate f hy (s y)).symm

/-- The literal inverse 1 tensor t maps EVERY original holomorphic T-section back. -/
def zeroTwistSectionInv (T : HermitianHolomorphicLineBundle.{u,v} n M)
    (s : SGPT.Bergman.QuantizationDraft.HolomorphicSections (n := n) T.Fiber) :
    SGPT.Bergman.QuantizationDraft.HolomorphicSections (n := n) (tensor unit T).Fiber where
  toFun := fun x => (zeroTwistFiberIsometry T x).symm (s x)
  contMDiff_toFun := by
    intro x
    let f : AtlasFrame T := ⟨trivializationAt ℂ T.Fiber x, inferInstance⟩
    let := f.property
    let q := tensorAtlasFrame unitAtlasFrame f
    let := q.property
    have hx : x ∈ f.val.baseSet := mem_baseSet_trivializationAt ℂ T.Fiber x
    apply (q.val.contMDiffAt_section_iff (show x ∈ q.val.baseSet from ⟨Set.mem_univ x, hx⟩)).mpr
    have hs := (f.val.contMDiffAt_section_iff hx).mp (s.contMDiff x)
    apply hs.congr_of_eventuallyEq
    filter_upwards [f.val.open_baseSet.mem_nhds hx] with y hy
    rw [zeroTwist_coordinate f hy, LinearIsometryEquiv.apply_symm_apply]

/-- Actual complex linear equivalence of ALL degree-zero sections with ALL original T-sections. -/
def zeroTwistSectionsEquiv (T : HermitianHolomorphicLineBundle.{u,v} n M) :
    SGPT.Bergman.QuantizationDraft.HolomorphicSections (n := n) (tensor unit T).Fiber ≃ₗ[ℂ]
      SGPT.Bergman.QuantizationDraft.HolomorphicSections (n := n) T.Fiber where
  toFun := zeroTwistSection T
  invFun := zeroTwistSectionInv T
  left_inv s := by ext x; exact (zeroTwistFiberIsometry T x).symm_apply_apply (s x)
  right_inv s := by ext x; exact (zeroTwistFiberIsometry T x).apply_symm_apply (s x)
  map_add' s t := by ext x; exact map_add (zeroTwistFiberIsometry T x) (s x) (t x)
  map_smul' a s := by ext x; exact map_smul (zeroTwistFiberIsometry T x) a (s x)

/-- The full degree-zero equivalence preserves the SAME pointwise metric. -/
theorem zeroTwistSectionsEquiv_norm (T : HermitianHolomorphicLineBundle.{u,v} n M)
    (s : SGPT.Bergman.QuantizationDraft.HolomorphicSections (n := n) (tensor unit T).Fiber) (x : M) :
    ‖zeroTwistSectionsEquiv T s x‖ = ‖s x‖ :=
  (zeroTwistFiberIsometry T x).norm_map (s x)

/-- Genuine base-preserving left-unit map on the literal total space. -/
def zeroTwistTotalMap (T : HermitianHolomorphicLineBundle.{u,v} n M)
    (p : TotalSpace ℂ (tensor unit T).Fiber) : TotalSpace ℂ T.Fiber :=
  ⟨p.proj, zeroTwistFiberIsometry T p.proj p.snd⟩

/-- Genuine inverse on the SAME original T total space. -/
def zeroTwistTotalMapInv (T : HermitianHolomorphicLineBundle.{u,v} n M)
    (p : TotalSpace ℂ T.Fiber) : TotalSpace ℂ (tensor unit T).Fiber :=
  ⟨p.proj, (zeroTwistFiberIsometry T p.proj).symm p.snd⟩

/-- The actual forward total-space map is holomorphic in the produced native atlases. -/
theorem zeroTwistTotalMap_contMDiff (T : HermitianHolomorphicLineBundle.{u,v} n M) :
    ContMDiff ((𝓘(ℂ, ComplexModel n)).prod (𝓘(ℂ, ℂ)))
      ((𝓘(ℂ, ComplexModel n)).prod (𝓘(ℂ, ℂ))) ∞ (zeroTwistTotalMap T) := by
  intro p
  let f : AtlasFrame T := ⟨trivializationAt ℂ T.Fiber p.proj, inferInstance⟩
  let := f.property
  let q := tensorAtlasFrame unitAtlasFrame f
  let := q.property
  have hx : p.proj ∈ f.val.baseSet := mem_baseSet_trivializationAt ℂ T.Fiber p.proj
  have hp : p ∈ q.val.source := q.val.mem_source.mpr ⟨Set.mem_univ p.proj, hx⟩
  apply (f.val.contMDiffAt_iff (f.val.mem_source.mpr hx)).mpr
  refine ⟨contMDiffAt_proj _, ?_⟩
  have hq := ((q.val.contMDiffOn (IB := 𝓘(ℂ, ComplexModel n)) (n := ∞)).contMDiffAt (q.val.open_source.mem_nhds hp)).snd
  apply hq.congr_of_eventuallyEq
  have hbase : ∀ᶠ z : TotalSpace ℂ (tensor unit T).Fiber in 𝓝 p,
      z.proj ∈ f.val.baseSet :=
    (FiberBundle.continuous_proj ℂ (tensor unit T).Fiber).continuousAt.eventually (f.val.open_baseSet.mem_nhds hx)
  filter_upwards [hbase] with z hz
  exact (zeroTwist_coordinate f hz z.snd).symm

/-- The actual inverse total-space map is holomorphic as well. -/
theorem zeroTwistTotalMapInv_contMDiff (T : HermitianHolomorphicLineBundle.{u,v} n M) :
    ContMDiff ((𝓘(ℂ, ComplexModel n)).prod (𝓘(ℂ, ℂ)))
      ((𝓘(ℂ, ComplexModel n)).prod (𝓘(ℂ, ℂ))) ∞ (zeroTwistTotalMapInv T) := by
  intro p
  let f : AtlasFrame T := ⟨trivializationAt ℂ T.Fiber p.proj, inferInstance⟩
  let := f.property
  let q := tensorAtlasFrame unitAtlasFrame f
  let := q.property
  have hx : p.proj ∈ f.val.baseSet := mem_baseSet_trivializationAt ℂ T.Fiber p.proj
  have hp : p ∈ f.val.source := f.val.mem_source.mpr hx
  apply (q.val.contMDiffAt_iff (q.val.mem_source.mpr ⟨Set.mem_univ p.proj, hx⟩)).mpr
  refine ⟨contMDiffAt_proj _, ?_⟩
  have hf := ((f.val.contMDiffOn (IB := 𝓘(ℂ, ComplexModel n)) (n := ∞)).contMDiffAt (f.val.open_source.mem_nhds hp)).snd
  apply hf.congr_of_eventuallyEq
  have hbase : ∀ᶠ z : TotalSpace ℂ T.Fiber in 𝓝 p, z.proj ∈ f.val.baseSet :=
    (FiberBundle.continuous_proj ℂ T.Fiber).continuousAt.eventually (f.val.open_baseSet.mem_nhds hx)
  filter_upwards [hbase] with z hz
  exact (zeroTwist_coordinate f hz ((zeroTwistFiberIsometry T z.proj).symm z.snd)).trans
    (by rw [LinearIsometryEquiv.apply_symm_apply])

/-- Actual inverse laws on the entire original total spaces, with both holomorphic maps above. -/
def zeroTwistTotalEquiv (T : HermitianHolomorphicLineBundle.{u,v} n M) :
    TotalSpace ℂ (tensor unit T).Fiber ≃ TotalSpace ℂ T.Fiber where
  toFun := zeroTwistTotalMap T
  invFun := zeroTwistTotalMapInv T
  left_inv p := by
    cases p with
    | mk x t =>
      exact congrArg (fun z => (⟨x, z⟩ : TotalSpace ℂ (tensor unit T).Fiber))
        ((zeroTwistFiberIsometry T x).symm_apply_apply t)
  right_inv p := by
    cases p with
    | mk x t =>
      exact congrArg (fun z => (⟨x, z⟩ : TotalSpace ℂ T.Fiber))
        ((zeroTwistFiberIsometry T x).apply_symm_apply t)

/-- Literal weighted densities commute with the actual full degree-zero equivalence. -/
theorem zeroTwistSectionsEquiv_density (T : HermitianHolomorphicLineBundle.{u,v} n M)
    {K : Set M} (j : ℕ) (a : K → EReal)
    (s : SGPT.Bergman.QuantizationDraft.HolomorphicSections (n := n) (tensor unit T).Fiber) (x : K) :
    SGPT.Bergman.QuantizationDraft.weightedSectionDensity T.Fiber j a (zeroTwistSectionsEquiv T s) x =
      SGPT.Bergman.QuantizationDraft.weightedSectionDensity (tensor unit T).Fiber j a s x := by
  simp only [SGPT.Bergman.QuantizationDraft.weightedSectionDensity, zeroTwistSectionsEquiv_norm]

/-- The SAME pole-deleted supremum is preserved, including j=0 and all extended-real poles. -/
theorem zeroTwistSectionsEquiv_supNorm (T : HermitianHolomorphicLineBundle.{u,v} n M)
    {K : Set M} (j : ℕ) (a : K → EReal)
    (s : SGPT.Bergman.QuantizationDraft.HolomorphicSections (n := n) (tensor unit T).Fiber) :
    SGPT.Bergman.QuantizationDraft.weightedSupNorm T.Fiber j a (zeroTwistSectionsEquiv T s) =
      SGPT.Bergman.QuantizationDraft.weightedSupNorm (tensor unit T).Fiber j a s := by
  simp only [SGPT.Bergman.QuantizationDraft.weightedSupNorm, zeroTwistSectionsEquiv_density]

/-- The SAME subtype integral is preserved, with no finiteness or pole-set assumption. -/
theorem zeroTwistSectionsEquiv_L2Norm (T : HermitianHolomorphicLineBundle.{u,v} n M)
    {K : Set M} [MeasurableSpace K] (j : ℕ) (a : K → EReal) (μ : MeasureTheory.Measure K)
    (s : SGPT.Bergman.QuantizationDraft.HolomorphicSections (n := n) (tensor unit T).Fiber) :
    SGPT.Bergman.QuantizationDraft.weightedL2Norm T.Fiber j a μ (zeroTwistSectionsEquiv T s) =
      SGPT.Bergman.QuantizationDraft.weightedL2Norm (tensor unit T).Fiber j a μ s := by
  simp only [SGPT.Bergman.QuantizationDraft.weightedL2Norm, zeroTwistSectionsEquiv_density]

/-- Exact all-degree extended-real source density in SAME original L,T frames. -/
theorem twistedSectionDensity_frame {L T : HermitianHolomorphicLineBundle.{u,v} n M}
    (e : AtlasFrame L) (f : AtlasFrame T) (k : ℕ) (s : twistedSections L T k)
    {K : Set M} (a : K → EReal) (x : K)
    (hx : x.val ∈ e.val.baseSet) (hy : x.val ∈ f.val.baseSet) :
    SGPT.Bergman.QuantizationDraft.weightedSectionDensity (twistedPower L T k).Fiber k a s x =
      ENNReal.ofReal (‖((twistedPowerAtlasFrame e f k).val ⟨x.val, s x.val⟩).2‖ ^ 2 *
        (‖e.val.symm x.val 1‖ ^ 2) ^ k * ‖f.val.symm x.val 1‖ ^ 2) *
          SGPT.Foundations.Analysis.multiplierWeight (k : ℝ) (a x) := by
  unfold SGPT.Bergman.QuantizationDraft.weightedSectionDensity
  rw [twistedSection_norm_sq_frame e f k s hx hy]

/-- The literal real-weight density used in the book: original coefficients times h^k h_T exp(-ka). -/
theorem twistedSectionDensity_real_frame {L T : HermitianHolomorphicLineBundle.{u,v} n M}
    (e : AtlasFrame L) (f : AtlasFrame T) (k : ℕ) (s : twistedSections L T k)
    {K : Set M} (a : K → ℝ) (x : K)
    (hx : x.val ∈ e.val.baseSet) (hy : x.val ∈ f.val.baseSet) :
    SGPT.Bergman.QuantizationDraft.weightedSectionDensity (twistedPower L T k).Fiber k
      (fun x => (a x : EReal)) s x =
      ENNReal.ofReal (‖((twistedPowerAtlasFrame e f k).val ⟨x.val, s x.val⟩).2‖ ^ 2 *
        (‖e.val.symm x.val 1‖ ^ 2) ^ k * ‖f.val.symm x.val 1‖ ^ 2 * Real.exp (-((k : ℝ) * a x))) := by
  rw [twistedSectionDensity_frame e f k s _ x hx hy, multiplierWeight_coe]
  exact (ENNReal.ofReal_mul (by positivity)).symm

/-- Original WHOLE supremum monotonicity now consumes the SAME constructed all-degree source bundle. -/
theorem twistedSupNorm_antitone (L T : HermitianHolomorphicLineBundle.{u,v} n M)
    (k : ℕ) {K : Set M} {a b : K → EReal} (hab : a ≤ b)
    (hpoles : {x | a x = ⊥} = {x | b x = ⊥}) (s : twistedSections L T k) :
    SGPT.Bergman.QuantizationDraft.weightedSupNorm (twistedPower L T k).Fiber k b s ≤
      SGPT.Bergman.QuantizationDraft.weightedSupNorm (twistedPower L T k).Fiber k a s :=
  SGPT.Bergman.QuantizationDraft.weightedSupNorm_antitone (twistedPower L T k).Fiber k hab hpoles s

/-- Original integral monotonicity on the SAME source family, with all extended-real values retained. -/
theorem twistedL2Norm_antitone (L T : HermitianHolomorphicLineBundle.{u,v} n M)
    (k : ℕ) {K : Set M} [MeasurableSpace K] {a b : K → EReal} (hab : a ≤ b)
    (μ : MeasureTheory.Measure K) (s : twistedSections L T k) :
    SGPT.Bergman.QuantizationDraft.weightedL2Norm (twistedPower L T k).Fiber k b μ s ≤
      SGPT.Bergman.QuantizationDraft.weightedL2Norm (twistedPower L T k).Fiber k a μ s :=
  SGPT.Bergman.QuantizationDraft.weightedL2Norm_antitone (twistedPower L T k).Fiber k hab μ s

/-- The SAME canonical source weighted subset detects every actual tensor/twist section. -/
theorem twistedSupNorm_weightedSubset_eq_zero_iff [ConnectedSpace M]
    (L T : HermitianHolomorphicLineBundle.{u,v} n M)
    (A : SGPT.Bergman.WeightedSubset.WeightedSubset n M) (k : ℕ) (s : twistedSections L T k) :
    SGPT.Bergman.QuantizationDraft.weightedSupNorm (twistedPower L T k).Fiber k A.erealWeight s = 0 ↔ s = 0 :=
  SGPT.Bergman.QuantizationDraft.weightedSupNorm_weightedSubset_eq_zero_iff (twistedPower L T k).Fiber A k s

/-- Original atlas membership supplies the native linearity/transition instances. -/
instance atlasFrame_memAtlas {L : HermitianHolomorphicLineBundle.{u,v} n M} (e : AtlasFrame L) :
    MemTrivializationAtlas e.val := e.property

/-- The genuine tensor atlas retains the product of the two ORIGINAL overlap multipliers. -/
theorem tensorAtlasFrame_transition {L : HermitianHolomorphicLineBundle.{u,v} n M}
    {T : HermitianHolomorphicLineBundle.{u,w} n M}
    (e e' : AtlasFrame L) (f f' : AtlasFrame T) {x : M}
    (hx : x ∈ e.val.baseSet) (hx' : x ∈ e'.val.baseSet)
    (hy : x ∈ f.val.baseSet) (hy' : x ∈ f'.val.baseSet) :
    ((tensorAtlasFrame e f).val.coordChangeL ℂ (tensorAtlasFrame e' f').val x) 1 =
      (e.val.coordChangeL ℂ e'.val x) 1 * (f.val.coordChangeL ℂ f'.val x) 1 := by
  have he : e'.val.linearMapAt ℂ x (e.val.symm x 1) = (e.val.coordChangeL ℂ e'.val x) 1 :=
    (congrFun (Trivialization.coe_linearMapAt_of_mem e'.val hx') (e.val.symm x 1)).trans
      (Trivialization.coordChangeL_apply e.val e'.val ⟨hx, hx'⟩ 1).symm
  have hf : f'.val.linearMapAt ℂ x (f.val.symm x 1) = (f.val.coordChangeL ℂ f'.val x) 1 :=
    (congrFun (Trivialization.coe_linearMapAt_of_mem f'.val hy') (f.val.symm x 1)).trans
      (Trivialization.coordChangeL_apply f.val f'.val ⟨hy, hy'⟩ 1).symm
  calc
    _ = ((tensorAtlasFrame e' f').val ⟨x, (tensorAtlasFrame e f).val.symm x 1⟩).2 :=
      Trivialization.coordChangeL_apply (tensorAtlasFrame e f).val
        (tensorAtlasFrame e' f').val ⟨⟨hx, hy⟩, ⟨hx', hy'⟩⟩ 1
    _ = tensorCoordinate L.Fiber T.Fiber e'.val f'.val x (e.val.symm x 1 ⊗ₜ[ℂ] f.val.symm x 1) := by
      change tensorCoordinate L.Fiber T.Fiber e'.val f'.val x ((tensorAtlasFrame e f).val.symm x 1) = _
      exact congrArg (tensorCoordinate L.Fiber T.Fiber e'.val f'.val x)
        ((tensorAtlasFrame_symm e f ⟨hx, hy⟩ 1).trans (one_smul _ _))
    _ = _ := (tensorCoordinate_tmul L.Fiber T.Fiber e'.val f'.val x _ _).trans (congrArg₂ (· * ·) he hf)

/-- Actual positive-power transitions in the original L frames, with exponent k+1. -/
theorem positivePower_frame_transition {L : HermitianHolomorphicLineBundle.{u,v} n M}
    (e e' : AtlasFrame L) {x : M} (hx : x ∈ e.val.baseSet) (hx' : x ∈ e'.val.baseSet) :
    ∀ k, ((positivePowerAtlasFrame e k).val.coordChangeL ℂ
      (positivePowerAtlasFrame e' k).val x) 1 = ((e.val.coordChangeL ℂ e'.val x) 1) ^ (k + 1)
  | 0 => by exact (pow_one _).symm
  | k + 1 => by
    have h : ((positivePowerAtlasFrame e (k + 1)).val.coordChangeL ℂ
        (positivePowerAtlasFrame e' (k + 1)).val x) 1 =
        ((positivePowerAtlasFrame e k).val.coordChangeL ℂ (positivePowerAtlasFrame e' k).val x) 1 *
          (e.val.coordChangeL ℂ e'.val x) 1 :=
      tensorAtlasFrame_transition (positivePowerAtlasFrame e k) (positivePowerAtlasFrame e' k)
        e e' (positivePowerAtlasFrame_mem e hx k) (positivePowerAtlasFrame_mem e' hx' k) hx hx'
    rw [h, positivePower_frame_transition e e' hx hx' k]
    exact (pow_succ _ _).symm

/-- The actual all-degree source transition is g_L^k g_T, including the scalar unit at zero. -/
theorem twistedPower_frame_transition {L T : HermitianHolomorphicLineBundle.{u,v} n M}
    (e e' : AtlasFrame L) (f f' : AtlasFrame T) {x : M}
    (hx : x ∈ e.val.baseSet) (hx' : x ∈ e'.val.baseSet)
    (hy : x ∈ f.val.baseSet) (hy' : x ∈ f'.val.baseSet) :
    ∀ k, ((twistedPowerAtlasFrame e f k).val.coordChangeL ℂ
      (twistedPowerAtlasFrame e' f' k).val x) 1 =
        ((e.val.coordChangeL ℂ e'.val x) 1) ^ k * (f.val.coordChangeL ℂ f'.val x) 1
  | 0 => by
    have h : ((twistedPowerAtlasFrame e f 0).val.coordChangeL ℂ
        (twistedPowerAtlasFrame e' f' 0).val x) 1 =
        ((unitAtlasFrame (n := n) (M := M)).val.coordChangeL ℂ unitAtlasFrame.val x) 1 *
          (f.val.coordChangeL ℂ f'.val x) 1 :=
      tensorAtlasFrame_transition unitAtlasFrame unitAtlasFrame f f' (Set.mem_univ x) (Set.mem_univ x) hy hy'
    have hu : ((unitAtlasFrame (n := n) (M := M)).val.coordChangeL ℂ unitAtlasFrame.val x) 1 = 1 := by
      change ((Bundle.Trivial.trivialization M ℂ).coordChangeL ℂ (Bundle.Trivial.trivialization M ℂ) x) 1 = 1
      rw [Bundle.Trivial.trivialization.coordChangeL]
      rfl
    rw [h, hu, pow_zero, one_mul]
  | k + 1 => by
    have h : ((twistedPowerAtlasFrame e f (k + 1)).val.coordChangeL ℂ
        (twistedPowerAtlasFrame e' f' (k + 1)).val x) 1 =
        ((positivePowerAtlasFrame e k).val.coordChangeL ℂ (positivePowerAtlasFrame e' k).val x) 1 *
          (f.val.coordChangeL ℂ f'.val x) 1 :=
      tensorAtlasFrame_transition (positivePowerAtlasFrame e k) (positivePowerAtlasFrame e' k) f f'
        (positivePowerAtlasFrame_mem e hx k) (positivePowerAtlasFrame_mem e' hx' k) hy hy'
    rw [h, positivePower_frame_transition e e' hx hx' k]

end HermitianHolomorphicLineBundle

end SGPT.Bergman.TensorDictionaryDraft
