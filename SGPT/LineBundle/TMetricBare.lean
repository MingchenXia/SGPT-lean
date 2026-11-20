import SGPT.LineBundle.TMetricExists
import SGPT.LineBundle.TMetricSections

/-!
# Holomorphic line bundles without metric data

Lane T-METRIC, blueprint `claude-t-metric`, node `claude-t-metric:bare`. Source `thm:DXmain1`
(chapter *`𝓘`-good singularities*), whose twist `T` is an arbitrary holomorphic line bundle.

The library represents line bundles by `HermitianHolomorphicLineBundle`, which bundles a continuous
Hermitian metric. Here a holomorphic line bundle is taken in Mathlib's sense, with no metric data:
fibres `E x` that are only complex vector spaces with a topology, a fibre bundle with fibre `ℂ`, a
vector bundle and a holomorphic (`ContMDiffVectorBundle`) structure. On a compact base:

* `FramePartition n E`: finitely many atlas frames `eₐ` and a chart-smooth partition of unity
  `χₐ` with `supp χₐ ⊆ dom eₐ`; one exists (`exists_framePartition`).
* `FramePartition.toHHLB`: the same holomorphic line bundle `E` (same fibres, topologies,
  fibre-bundle, vector-bundle and holomorphic structure) with the Hermitian metric
  `⟨v, w⟩_x = ∑ₐ χₐ(x) conj(eₐ(v)) eₐ(w)`; its metric is smooth
  (`FramePartition.isSourceSmoothHermitianMetric_toHHLB`).
* `FramePartition.equivToHHLB`: every `HermitianHolomorphicLineBundle T` is isomorphic, by the
  identity (`FrameIdentityEquiv`), to the bundle built from its underlying metric-free bundle; and
  `FramePartition.toHHLBEquiv`: the result does not depend on the partition. Hence
  `h⁰(X, T ⊗ L^k ⊗ 𝓘(kφ))` is a function of the metric-free holomorphic line bundles.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.LineBundle.TMetric

open Bundle Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff ComplexConjugate
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Bergman.TensorDictionaryDraft HermitianHolomorphicLineBundle
open SGPT.Bergman.CompactHolomorphicSectionsDraft
open SGPT.Bergman.PolynomialH0Growth

universe u v

section Bare

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]
  (E : M → Type v) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)] [∀ x, TopologicalSpace (E x)]
  [TopologicalSpace (TotalSpace ℂ E)] [FiberBundle ℂ E] [VectorBundle ℂ ℂ E]

/-! ### Fibres of a vector bundle are topological vector spaces -/

/-- The fibres of a vector bundle are topological additive groups. -/
theorem fiber_isTopologicalAddGroup (x : M) : IsTopologicalAddGroup (E x) :=
  Topology.IsInducing.topologicalAddGroup
    ((trivializationAt ℂ E x).continuousLinearEquivAt ℂ x (mem_baseSet_trivializationAt ℂ E x))
    ((trivializationAt ℂ E x).continuousLinearEquivAt ℂ x
      (mem_baseSet_trivializationAt ℂ E x)).toHomeomorph.isInducing

/-- Scalar multiplication by a constant is continuous on the fibres of a vector bundle. -/
theorem fiber_continuousConstSMul (x : M) : ContinuousConstSMul ℂ (E x) := by
  let φ := (trivializationAt ℂ E x).continuousLinearEquivAt ℂ x (mem_baseSet_trivializationAt ℂ E x)
  refine ⟨fun c => ?_⟩
  have h : (fun v : E x => c • v) = fun v => φ.symm (c • φ v) := by
    funext v
    rw [map_smul, ContinuousLinearEquiv.symm_apply_apply]
  rw [h]
  exact φ.symm.continuous.comp ((continuous_const_smul c).comp φ.continuous)

attribute [local instance] fiber_isTopologicalAddGroup fiber_continuousConstSMul

/-! ### Partitions of unity subordinate to atlas frames -/

variable (n) in
/-- Finitely many atlas frames `eₐ` and a partition of unity `χₐ`, smooth in every chart, with
`supp χₐ ⊆ dom eₐ`. -/
structure FramePartition where
  /-- The number of frames. -/
  card : ℕ
  /-- The frames. -/
  frame : Fin card → Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ E → M)
  /-- The frames belong to the atlas. -/
  mem : ∀ a, MemTrivializationAtlas (frame a)
  /-- The partition of unity. -/
  part : Fin card → M → ℝ
  smooth : ∀ a, ChartSmooth (n := n) (part a)
  nonneg : ∀ a y, 0 ≤ part a y
  support : ∀ a, tsupport (part a) ⊆ (frame a).baseSet
  sum_eq_one : ∀ y, ∑ a, part a y = 1

omit [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)] [VectorBundle ℂ ℂ E] in
/-- On a compact base, partitions of unity subordinate to atlas frames exist. -/
theorem exists_framePartition [CompactSpace M] : Nonempty (FramePartition n E) := by
  let S : M → Opens M := fun x =>
    ⟨(trivializationAt ℂ E x).baseSet, (trivializationAt ℂ E x).open_baseSet⟩
  obtain ⟨m, χ, idx, hsm, hnn, hs, -, hsum⟩ :=
    ChartPartition.exists_chartSmooth_partitionOfUnity (n := n) S
      (fun x => ⟨x, mem_baseSet_trivializationAt ℂ E x⟩)
  exact ⟨⟨m, fun a => trivializationAt ℂ E (idx a), fun a => inferInstance, χ, hsm, hnn, hs, hsum⟩⟩

namespace FramePartition

variable {E} (P : FramePartition n E)

instance frame_memAtlas (a : Fin P.card) : MemTrivializationAtlas (P.frame a) := P.mem a

/-- The coordinate `eₐ` on the fibre `E_x` (zero off the frame domain). -/
def coord (a : Fin P.card) (x : M) : E x →L[ℂ] ℂ :=
  (P.frame a).continuousLinearMapAt ℂ x

omit [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)] [VectorBundle ℂ ℂ E] in
theorem exists_part_pos (x : M) : ∃ a, 0 < P.part a x := by
  by_contra h
  push Not at h
  have hz : (∑ a, P.part a x) = 0 :=
    Finset.sum_eq_zero fun a _ => le_antisymm (h a) (P.nonneg a x)
  rw [P.sum_eq_one x] at hz
  exact one_ne_zero hz

/-- The Hermitian form `∑ₐ χₐ(x) conj(eₐ(v)) eₐ(w)`. -/
def innerSum (x : M) (v w : E x) : ℂ :=
  ∑ a, (P.part a x : ℂ) * (conj (P.coord a x v) * P.coord a x w)

theorem innerSum_self (x : M) (v : E x) :
    P.innerSum x v v = ((∑ a, P.part a x * Complex.normSq (P.coord a x v) : ℝ) : ℂ) := by
  rw [innerSum, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self]

/-- The fibre inner product, as an `InnerProductSpace.Core`. -/
@[instance_reducible]
def core (x : M) : InnerProductSpace.Core ℂ (E x) where
  inner := P.innerSum x
  conj_inner_symm v w := by
    simp only [innerSum, map_sum, map_mul, Complex.conj_ofReal, Complex.conj_conj]
    exact Finset.sum_congr rfl fun a _ => by ring
  re_inner_nonneg v := by
    change 0 ≤ (P.innerSum x v v).re
    rw [innerSum_self, Complex.ofReal_re]
    exact Finset.sum_nonneg fun a _ => mul_nonneg (P.nonneg a x) (Complex.normSq_nonneg _)
  add_left v w z := by
    simp only [innerSum, map_add, add_mul, mul_add, Finset.sum_add_distrib]
  smul_left v w r := by
    simp only [innerSum, map_smul, smul_eq_mul, map_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring
  definite v h := by
    have h0 : (∑ a, P.part a x * Complex.normSq (P.coord a x v)) = 0 := by
      have h' := h
      change P.innerSum x v v = 0 at h'
      rw [innerSum_self] at h'
      exact_mod_cast h'
    obtain ⟨a, ha⟩ := P.exists_part_pos x
    have hx : x ∈ (P.frame a).baseSet := P.support a (subset_tsupport _ ha.ne')
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ =>
      mul_nonneg (P.nonneg b x) (Complex.normSq_nonneg (P.coord b x v)))).mp h0 a
      (Finset.mem_univ a)
    have hc : P.coord a x v = 0 :=
      Complex.normSq_eq_zero.mp ((mul_eq_zero.mp hterm).resolve_left ha.ne')
    rw [← Trivialization.symmL_continuousLinearMapAt (R := ℂ) (P.frame a) hx v]
    change (P.frame a).symmL ℂ x (P.coord a x v) = 0
    rw [hc, map_zero]

theorem core_re (x : M) (v : E x) :
    RCLike.re ((P.core x).inner v v) = ∑ a, P.part a x * Complex.normSq (P.coord a x v) := by
  change (P.innerSum x v v).re = _
  rw [innerSum_self, Complex.ofReal_re]

theorem core_continuousAt (x : M) :
    ContinuousAt (fun v : E x => (P.core x).inner v v) 0 := by
  refine Continuous.continuousAt ?_
  change Continuous fun v => P.innerSum x v v
  unfold innerSum
  exact continuous_finsetSum _ fun a _ => continuous_const.mul
    ((Complex.continuous_conj.comp (P.coord a x).continuous).mul (P.coord a x).continuous)

theorem core_isVonNBounded (x : M) :
    Bornology.IsVonNBounded ℂ {v : E x | RCLike.re ((P.core x).inner v v) < 1} := by
  obtain ⟨a, ha⟩ := P.exists_part_pos x
  have hx : x ∈ (P.frame a).baseSet := P.support a (subset_tsupport _ ha.ne')
  let φ := (P.frame a).continuousLinearEquivAt ℂ x hx
  have hball : Bornology.IsVonNBounded ℂ
      ((φ.symm : ℂ →L[ℂ] E x) '' Metric.ball (0 : ℂ) (1 + (P.part a x)⁻¹)) :=
    (NormedSpace.isVonNBounded_ball ℂ ℂ _).image _
  refine Bornology.IsVonNBounded.subset ?_ hball
  intro v hv
  refine ⟨φ v, ?_, by simp⟩
  have hv' : P.part a x * Complex.normSq (P.coord a x v) < 1 := by
    have hle : P.part a x * Complex.normSq (P.coord a x v) ≤
        ∑ b, P.part b x * Complex.normSq (P.coord b x v) :=
      Finset.single_le_sum (f := fun b => P.part b x * Complex.normSq (P.coord b x v))
        (fun b _ => mul_nonneg (P.nonneg b x) (Complex.normSq_nonneg _)) (Finset.mem_univ a)
    have hv'' : RCLike.re ((P.core x).inner v v) < 1 := hv
    rw [core_re] at hv''
    exact lt_of_le_of_lt hle hv''
  have hφ : P.coord a x v = φ v := by
    change (P.frame a).continuousLinearMapAt ℂ x v = _
    rw [Trivialization.continuousLinearMapAt_apply_of_mem (R := ℂ) (P.frame a) hx]
    rfl
  rw [hφ, Complex.normSq_eq_norm_sq] at hv'
  rw [Metric.mem_ball, dist_zero_right]
  set t := ‖φ v‖
  have ht : 0 ≤ t := norm_nonneg _
  have hinv : 0 < (P.part a x)⁻¹ := inv_pos.mpr ha
  by_cases ht1 : t < 1
  · linarith
  · push Not at ht1
    have h2 : t ≤ t ^ 2 := by nlinarith
    have h3 : t ^ 2 < (P.part a x)⁻¹ := by
      have h4 : t ^ 2 < 1 / P.part a x := (lt_div_iff₀ ha).mpr (by linarith)
      rwa [one_div] at h4
    linarith

/-- The fibre norm `(∑ₐ χₐ |eₐ(v)|²)^{1/2}`, with the given fibre topology kept definitionally. -/
@[instance_reducible]
def normed (x : M) : NormedAddCommGroup (E x) :=
  (P.core x).toNormedAddCommGroupOfTopology (P.core_continuousAt x) (P.core_isVonNBounded x)

/-- The fibre inner product space. -/
@[instance_reducible]
def inner (x : M) : letI := P.normed x; InnerProductSpace ℂ (E x) :=
  InnerProductSpace.ofCoreOfTopology (P.core x) (P.core_continuousAt x) (P.core_isVonNBounded x)

theorem normed_norm (x : M) (v : E x) :
    @Norm.norm (E x) (P.normed x).toNorm v =
      Real.sqrt (∑ a, P.part a x * Complex.normSq (P.coord a x v)) := by
  change Real.sqrt (RCLike.re ((P.core x).inner v v)) = _
  rw [core_re]

/-- Each term `χₐ(π p) |eₐ(p)|²` is continuous on the total space. -/
theorem continuous_term (a : Fin P.card) :
    Continuous (fun p : TotalSpace ℂ E =>
      P.part a p.proj * Complex.normSq (P.coord a p.proj p.2)) := by
  refine continuous_iff_continuousAt.mpr fun p => ?_
  have hproj : Continuous (TotalSpace.proj : TotalSpace ℂ E → M) := FiberBundle.continuous_proj ℂ E
  have hχ : Continuous (P.part a) := ProductTestForms.ChartSmooth.continuous (P.smooth a)
  by_cases hp : p.proj ∈ (P.frame a).baseSet
  · have hsrc : p ∈ (P.frame a).source := (P.frame a).mem_source.mpr hp
    have hc : ContinuousAt (fun q : TotalSpace ℂ E => ((P.frame a) q).2) p :=
      ((P.frame a).continuousAt hsrc).snd
    refine ((hχ.comp hproj).continuousAt.mul (Complex.continuous_normSq.continuousAt.comp hc)).congr
      ?_
    filter_upwards [(P.frame a).open_source.mem_nhds hsrc] with q hq
    have hq' : q.proj ∈ (P.frame a).baseSet := (P.frame a).mem_source.mp hq
    change P.part a q.proj * Complex.normSq (((P.frame a) q).2) =
      P.part a q.proj * Complex.normSq ((P.frame a).continuousLinearMapAt ℂ q.proj q.2)
    rw [Trivialization.continuousLinearMapAt_apply_of_mem (R := ℂ) (P.frame a) hq']
  · have hp' : p.proj ∉ tsupport (P.part a) := fun h => hp (P.support a h)
    refine continuousAt_const.congr (f := fun _ => (0 : ℝ)) ?_
    filter_upwards [((isClosed_tsupport (P.part a)).isOpen_compl.preimage hproj).mem_nhds hp']
      with q hq
    rw [image_eq_zero_of_notMem_tsupport hq, zero_mul]

theorem continuous_normed_norm :
    Continuous (fun p : TotalSpace ℂ E =>
      @Norm.norm (E p.proj) (P.normed p.proj).toNorm p.2) := by
  have h : (fun p : TotalSpace ℂ E => @Norm.norm (E p.proj) (P.normed p.proj).toNorm p.2) =
      fun p => Real.sqrt (∑ a, P.part a p.proj * Complex.normSq (P.coord a p.proj p.2)) := by
    funext p
    exact P.normed_norm p.proj p.2
  rw [h]
  exact (continuous_finsetSum _ fun a _ => P.continuous_term a).sqrt

variable [ContMDiffVectorBundle ∞ ℂ E (𝓘(ℂ, ComplexModel n))]

/-- **The holomorphic line bundle `E` with the glued metric** `∑ₐ χₐ |·|²_{eₐ}`: the same fibres,
fibre topologies, total-space topology, fibre-bundle, vector-bundle and holomorphic structure. -/
def toHHLB : HermitianHolomorphicLineBundle.{u, v} n M where
  Fiber := E
  normedFiber := P.normed
  hermitianFiber := P.inner
  totalTopology := ‹TopologicalSpace (TotalSpace ℂ E)›
  fiberBundle := ‹FiberBundle ℂ E›
  vectorBundle := ‹VectorBundle ℂ ℂ E›
  holomorphic := ‹ContMDiffVectorBundle ∞ ℂ E (𝓘(ℂ, ComplexModel n))›
  normContinuous := @ContinuousFiberNorm.mk M _ E P.normed _ P.continuous_normed_norm

/-- The atlas frames of the partition, as frames of `toHHLB`. -/
def atlasFrame (a : Fin P.card) : AtlasFrame P.toHHLB :=
  ⟨P.frame a, P.mem a⟩

theorem toHHLB_norm_sq (x : M) (w : P.toHHLB.Fiber x) :
    ‖w‖ ^ 2 = ∑ a, P.part a x * Complex.normSq (P.coord a x w) := by
  change (@Norm.norm (E x) (P.normed x).toNorm w) ^ 2 = _
  rw [P.normed_norm x w, Real.sq_sqrt (Finset.sum_nonneg fun a _ =>
    mul_nonneg (P.nonneg a x) (Complex.normSq_nonneg _))]

/-- **The glued metric is smooth.** -/
theorem isSourceSmoothHermitianMetric_toHHLB : IsSourceSmoothHermitianMetric P.toHHLB := by
  intro c e
  have hsmooth : ContDiffOn ℝ ∞ (fun z => ∑ a, P.part a (c.val.symm z) *
      Complex.normSq (frameTransition e (P.atlasFrame a) (c.val.symm z)))
      (c.val.target ∩ c.val.symm ⁻¹' e.val.baseSet) :=
    ContDiffOn.sum fun a _ =>
      contDiffOn_mul_normSq_frameTransition c e (P.atlasFrame a) (P.smooth a) (P.support a)
  refine hsmooth.congr fun z hz => ?_
  rw [toHHLB_norm_sq]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases ha : P.part a (c.val.symm z) = 0
  · rw [ha, zero_mul, zero_mul]
  · have hya : c.val.symm z ∈ (P.frame a).baseSet := P.support a (subset_tsupport _ ha)
    congr 2
    let := e.property
    have h1 : P.coord a (c.val.symm z) (e.val.symm (c.val.symm z) 1) =
        ((P.frame a) ⟨c.val.symm z, e.val.symm (c.val.symm z) 1⟩).2 :=
      Trivialization.continuousLinearMapAt_apply_of_mem (R := ℂ) (P.frame a) hya _
    have h2 : frameTransition e (P.atlasFrame a) (c.val.symm z) =
        ((P.frame a) ⟨c.val.symm z, e.val.symm (c.val.symm z) 1⟩).2 :=
      Trivialization.coordChangeL_apply e.val (P.atlasFrame a).val ⟨hz.2, hya⟩ 1
    rw [h1, h2]

end FramePartition

end Bare

/-! ### Every Hermitian holomorphic line bundle comes from its metric-free bundle -/

section Equiv

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- A Hermitian holomorphic line bundle `T` is isomorphic, by the identity, to the bundle
`P.toHHLB` built from its underlying metric-free holomorphic line bundle: its metric plays no
role. -/
def FramePartition.equivToHHLB (T : HermitianHolomorphicLineBundle.{0, 0} n X)
    (P : FramePartition n T.Fiber) : FrameIdentityEquiv T.Fiber P.toHHLB.Fiber where
  equiv _ :=
    { toFun := fun w => w
      invFun := fun w => w
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exists_frames x :=
    ⟨⟨trivializationAt ℂ T.Fiber x, inferInstance⟩,
      ⟨trivializationAt ℂ P.toHHLB.Fiber x, inferInstance⟩,
      mem_baseSet_trivializationAt ℂ T.Fiber x, mem_baseSet_trivializationAt ℂ P.toHHLB.Fiber x,
      fun _ _ _ => rfl⟩

/-- The bundle `P.toHHLB` does not depend on the partition `P`, up to the identity
isomorphism. -/
def FramePartition.toHHLBEquiv (E : X → Type) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace ℂ E)] [FiberBundle ℂ E]
    [VectorBundle ℂ ℂ E] [ContMDiffVectorBundle ∞ ℂ E (𝓘(ℂ, ComplexModel n))]
    (P P' : FramePartition n E) : FrameIdentityEquiv P.toHHLB.Fiber P'.toHHLB.Fiber where
  equiv _ :=
    { toFun := fun w => w
      invFun := fun w => w
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exists_frames x :=
    ⟨⟨trivializationAt ℂ P.toHHLB.Fiber x, inferInstance⟩,
      ⟨trivializationAt ℂ P'.toHHLB.Fiber x, inferInstance⟩,
      mem_baseSet_trivializationAt ℂ P.toHHLB.Fiber x,
      mem_baseSet_trivializationAt ℂ P'.toHHLB.Fiber x, fun _ _ _ => rfl⟩

end Equiv

end SGPT.LineBundle.TMetric
