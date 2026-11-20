import SGPT.Bergman.SourceBergmanNorms
import SGPT.Foundations.Analysis.Pending.HolomorphicNormalFamilies
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.InnerProductSpace.Basic

-- PORT-SOURCE compact-holomorphic-sections/SourceCompactHolomorphicSections.lean; mathematical source retained.

set_option autoImplicit false
noncomputable section

namespace SGPT.Bergman.CompactHolomorphicSectionsDraft

open Bundle Set Filter Metric
open scoped Manifold ContDiff Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.QuantizationDraft

/-- Actual geometric continuity of the given fiber norms, before any section-space norm. -/
class ContinuousFiberNorm {X : Type*} [TopologicalSpace X] (V : X → Type*)
    [∀ x, NormedAddCommGroup (V x)] [TopologicalSpace (TotalSpace ℂ V)] : Prop where
  continuous : Continuous (fun p : TotalSpace ℂ V => ‖p.2‖)

/-- A genuinely continuous Hermitian diagonal gives the required norm regularity. -/
theorem continuousFiberNorm_of_hermitianDiagonal {X : Type*} [TopologicalSpace X]
    (V : X → Type*) [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℂ (V x)]
    [TopologicalSpace (TotalSpace ℂ V)]
    (h : Continuous (fun p : TotalSpace ℂ V => (inner ℂ p.2 p.2).re)) :
    ContinuousFiberNorm V := by
  constructor
  have heq : (fun p : TotalSpace ℂ V => ‖p.2‖) =
      fun p => Real.sqrt ((inner ℂ p.2 p.2).re) := by
    funext p
    have hi : (inner ℂ p.2 p.2).re = ‖p.2‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) p.2
    rw [hi, Real.sqrt_sq_eq_abs, abs_norm]
  rw [heq]
  exact h.sqrt

variable {n : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  (V : X → Type*) [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℂ (V x)]
  [TopologicalSpace (TotalSpace ℂ V)] [FiberBundle ℂ V] [VectorBundle ℂ ℂ V]
  [ContMDiffVectorBundle ∞ ℂ V (𝓘(ℂ, ComplexModel n))] [ContinuousFiberNorm V]

/-- The SAME actual section's fiber norm is a genuine global continuous real function. -/
def sectionNormMap (s : HolomorphicSections (n := n) V) : C(X, ℝ) :=
  ⟨fun x => ‖s x‖, ContinuousFiberNorm.continuous.comp s.contMDiff.continuous⟩

/-- Compactness supplies a finite real supremum for EVERY actual holomorphic section. -/
def sectionSize [CompactSpace X] (s : HolomorphicSections (n := n) V) : ℝ :=
  ‖sectionNormMap V s‖

omit [IsComplexManifold n X] [ContMDiffVectorBundle ∞ ℂ V (𝓘(ℂ, ComplexModel n))]
  [∀ x, NormedSpace ℂ (V x)] [VectorBundle ℂ ℂ V] in
theorem sectionSize_nonneg [CompactSpace X] (s : HolomorphicSections (n := n) V) :
    0 ≤ sectionSize V s := norm_nonneg _

omit [IsComplexManifold n X] [ContMDiffVectorBundle ∞ ℂ V (𝓘(ℂ, ComplexModel n))]
  [∀ x, NormedSpace ℂ (V x)] [VectorBundle ℂ ℂ V] in
/-- Actual pointwise bound; no finite norm bound is supplied as data. -/
theorem norm_apply_le_sectionSize [CompactSpace X] (s : HolomorphicSections (n := n) V) (x : X) :
    ‖s x‖ ≤ sectionSize V s := by
  have h := (sectionNormMap V s).norm_coe_le_norm x
  change ‖‖s x‖‖ ≤ sectionSize V s at h
  simpa only [norm_norm] using h

omit [IsComplexManifold n X] [ContMDiffVectorBundle ∞ ℂ V (𝓘(ℂ, ComplexModel n))]
  [∀ x, NormedSpace ℂ (V x)] [VectorBundle ℂ ℂ V] in
/-- The exact finite real supremum criterion for the SAME original fiber values. -/
theorem sectionSize_le_iff [CompactSpace X] (s : HolomorphicSections (n := n) V)
    {C : ℝ} (hC : 0 ≤ C) : sectionSize V s ≤ C ↔ ∀ x, ‖s x‖ ≤ C := by
  change ‖sectionNormMap V s‖ ≤ C ↔ _
  rw [ContinuousMap.norm_le _ hC]
  apply forall_congr'
  intro x
  change ‖‖s x‖‖ ≤ C ↔ ‖s x‖ ≤ C
  rw [norm_norm]

omit [IsComplexManifold n X] [ContMDiffVectorBundle ∞ ℂ V (𝓘(ℂ, ComplexModel n))] in
theorem sectionSize_zero [CompactSpace X] : sectionSize V (n := n) 0 = 0 := by
  have h : sectionNormMap V (n := n) 0 = 0 := by ext x; simp [sectionNormMap]
  change ‖sectionNormMap V (n := n) 0‖ = 0
  rw [h, norm_zero]

omit [IsComplexManifold n X] [ContMDiffVectorBundle ∞ ℂ V (𝓘(ℂ, ComplexModel n))] in
theorem sectionSize_eq_zero_iff [CompactSpace X] (s : HolomorphicSections (n := n) V) :
    sectionSize V s = 0 ↔ s = 0 := by
  constructor
  · intro hz
    apply ContMDiffSection.ext
    intro x
    have h := norm_apply_le_sectionSize V s x
    rw [hz] at h
    exact norm_eq_zero.mp (le_antisymm h (norm_nonneg _))
  · rintro rfl
    exact sectionSize_zero V

omit [IsComplexManifold n X] [ContMDiffVectorBundle ∞ ℂ V (𝓘(ℂ, ComplexModel n))] in
theorem sectionSize_add_le [CompactSpace X] (s t : HolomorphicSections (n := n) V) :
    sectionSize V (s + t) ≤ sectionSize V s + sectionSize V t := by
  apply (sectionSize_le_iff V _ (add_nonneg (sectionSize_nonneg V s) (sectionSize_nonneg V t))).mpr
  intro x
  exact (norm_add_le (s x) (t x)).trans
    (add_le_add (norm_apply_le_sectionSize V s x) (norm_apply_le_sectionSize V t x))

omit [IsComplexManifold n X] [ContMDiffVectorBundle ∞ ℂ V (𝓘(ℂ, ComplexModel n))] in
theorem sectionSize_smul [CompactSpace X] (a : ℂ) (s : HolomorphicSections (n := n) V) :
    sectionSize V (a • s) = ‖a‖ * sectionSize V s := by
  have h : sectionNormMap V (a • s) = ‖a‖ • sectionNormMap V s := by
    ext x
    exact norm_smul a (s x)
  change ‖sectionNormMap V (a • s)‖ = _
  rw [h, norm_smul, norm_norm]
  rfl

/-- The actual coordinate of an original section in a genuine bundle trivialization. -/
def sectionCoefficient (e : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ V → X))
    (s : HolomorphicSections (n := n) V) : X → ℂ := fun y => (e ⟨y, s y⟩).2

/-- The true inverse-trivialization frame of the SAME original line bundle. -/
def frameNorm (e : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ V → X)) : X → ℝ :=
  fun y => ‖e.symm y 1‖

omit [IsComplexManifold n X] [ContMDiffVectorBundle ∞ ℂ V (𝓘(ℂ, ComplexModel n))]
  [∀ x, NormedSpace ℂ (V x)] [VectorBundle ℂ ℂ V] [FiberBundle ℂ V] in
theorem frameNorm_continuousOn
    (e : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ V → X)) :
    ContinuousOn (frameNorm V e) e.baseSet := by
  have h : ContinuousOn (fun y => (⟨y, e.symm y 1⟩ : TotalSpace ℂ V)) e.baseSet :=
    e.continuousOn_symm.comp (continuous_id.prodMk continuous_const).continuousOn
    (fun y hy => ⟨hy, Set.mem_univ _⟩)
  exact ContinuousFiberNorm.continuous.comp_continuousOn h

omit [IsComplexManifold n X] [ContMDiffVectorBundle ∞ ℂ V (𝓘(ℂ, ComplexModel n))]
  [ContinuousFiberNorm V] in
theorem frameNorm_pos
    (e : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ V → X))
    [MemTrivializationAtlas e] {y : X} (hy : y ∈ e.baseSet) : 0 < frameNorm V e y := by
  apply norm_pos_iff.mpr
  intro h
  have hh := e.apply_mk_symm hy (1 : ℂ)
  have heq : (e.linearEquivAt ℂ y hy) (e.symm y 1) = 1 := congrArg Prod.snd hh
  rw [h, map_zero] at heq
  exact one_ne_zero heq.symm

omit [IsComplexManifold n X] [ContMDiffVectorBundle ∞ ℂ V (𝓘(ℂ, ComplexModel n))]
  [ContinuousFiberNorm V] in
/-- Exact same-frame coefficient/norm identity, not a supplied metric comparison. -/
theorem norm_eq_coefficient_mul_frameNorm
    (e : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ V → X))
    [MemTrivializationAtlas e] (s : HolomorphicSections (n := n) V) {y : X}
    (hy : y ∈ e.baseSet) : ‖s y‖ = ‖sectionCoefficient V e s y‖ * frameNorm V e y := by
  let A := e.linearEquivAt ℂ y hy
  have h : s y = sectionCoefficient V e s y • e.symm y 1 := by
    apply A.injective
    rw [map_smul]
    have hone : A (e.symm y 1) = 1 := congrArg Prod.snd (e.apply_mk_symm hy (1 : ℂ))
    rw [hone, smul_eq_mul, mul_one]
    rfl
  rw [h, norm_smul]
  rfl

omit [IsComplexManifold n X] [ContMDiffVectorBundle ∞ ℂ V (𝓘(ℂ, ComplexModel n))] in
/-- Metric/chart neighborhoods and bounds are chosen BEFORE every section. -/
theorem exists_frame_chart_ball (x : X) :
    let e := trivializationAt ℂ V x
    let c := complexChartAt (n := n) x
    ∃ R : ℝ, 0 < R ∧ ball (c.val x) R ⊆ c.val.target ∧
      ∀ z ∈ ball (c.val x) R, c.val.symm z ∈ e.baseSet ∧
        frameNorm V e x / 2 ≤ frameNorm V e (c.val.symm z) ∧
        frameNorm V e (c.val.symm z) ≤ 2 * frameNorm V e x := by
  let e := trivializationAt ℂ V x
  let c := complexChartAt (n := n) x
  have hxbase : x ∈ e.baseSet := mem_baseSet_trivializationAt ℂ V x
  have ha : 0 < frameNorm V e x := frameNorm_pos V e hxbase
  have hf : ContinuousAt (frameNorm V e) x :=
    (frameNorm_continuousOn V e).continuousAt (e.open_baseSet.mem_nhds hxbase)
  have hbase : ∀ᶠ y in 𝓝 x, y ∈ e.baseSet := e.open_baseSet.mem_nhds hxbase
  have hev : ∀ᶠ y in 𝓝 x, y ∈ e.baseSet ∧
      frameNorm V e x / 2 < frameNorm V e y ∧ frameNorm V e y < 2 * frameNorm V e x :=
    hbase.and (hf.eventually (Ioo_mem_nhds (by linarith) (by linarith)))
  obtain ⟨U, hUsub, hUopen, hxU⟩ := mem_nhds_iff.mp hev
  let D := c.val.target ∩ c.val.symm ⁻¹' U
  have hD : IsOpen D := c.val.isOpen_inter_preimage_symm hUopen
  have hxD : c.val x ∈ D :=
    ⟨c.val.map_source (mem_complexChartAt_source x), by
      change c.val.symm (c.val x) ∈ U
      rwa [c.val.left_inv (mem_complexChartAt_source x)]⟩
  obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.mp hD _ hxD
  refine ⟨R, hR, fun z hz => (hball hz).1, ?_⟩
  intro z hz
  have h := hUsub (hball hz).2
  exact ⟨h.1, h.2.1.le, h.2.2.le⟩

omit [ContinuousFiberNorm V] in
/-- ALL actual section coefficients are holomorphic in the true local chart. -/
theorem sectionCoefficient_chart_differentiable
    (e : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ V → X))
    [MemTrivializationAtlas e] (x : X) (s : HolomorphicSections (n := n) V) :
    let c := complexChartAt (n := n) x
    DifferentiableOn ℂ (sectionCoefficient V e s ∘ c.val.symm)
      (c.val.target ∩ c.val.symm ⁻¹' e.baseSet) := by
  intro c z hz
  have hg : ContMDiffAt (𝓘(ℂ, ComplexModel n)) (𝓘(ℂ, ℂ)) ∞
      (sectionCoefficient V e s) (c.val.symm z) :=
    (e.contMDiffAt_section_iff hz.2).mp (s.contMDiff (c.val.symm z))
  have hc : ContMDiffAt (𝓘(ℂ, ComplexModel n)) (𝓘(ℂ, ComplexModel n)) ∞
      c.val.symm z := contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x) hz.1
  exact ((hg.comp z hc).contDiffAt.differentiableAt (by simp)).differentiableWithinAt

/-- Cauchy estimates produce local half-supremum control uniformly over ALL sections. -/
theorem exists_local_half_sectionSize [CompactSpace X] (x : X) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ s : HolomorphicSections (n := n) V, s x = 0 →
        ∀ y ∈ U, ‖s y‖ ≤ sectionSize V s / 2 := by
  let e := trivializationAt ℂ V x
  let c := complexChartAt (n := n) x
  let a := frameNorm V e x
  have ha : 0 < a := frameNorm_pos V e (mem_baseSet_trivializationAt ℂ V x)
  obtain ⟨R, hR, hRT, hframe⟩ := exists_frame_chart_ball (n := n) V x
  let U := c.val.source ∩ c.val ⁻¹' ball (c.val x) (R / 32)
  refine ⟨U, c.val.isOpen_inter_preimage isOpen_ball,
    ⟨mem_complexChartAt_source x, mem_ball_self (by positivity)⟩, ?_⟩
  intro s hs y hy
  let F := sectionCoefficient V e s ∘ c.val.symm
  have hhol : DifferentiableOn ℂ F (ball (c.val x) R) :=
    (sectionCoefficient_chart_differentiable V e x s).mono
      (fun z hz => ⟨hRT hz, (hframe z hz).1⟩)
  have hbound : ∀ z ∈ ball (c.val x) R, ‖F z‖ ≤ sectionSize V s / (a / 2) := by
    intro z hz
    have hfr := hframe z hz
    apply (le_div_iff₀ (half_pos ha)).mpr
    calc
      ‖F z‖ * (a / 2) ≤ ‖F z‖ * frameNorm V e (c.val.symm z) :=
        mul_le_mul_of_nonneg_left hfr.2.1 (norm_nonneg _)
      _ = ‖s (c.val.symm z)‖ := (norm_eq_coefficient_mul_frameNorm V e s hfr.1).symm
      _ ≤ sectionSize V s := norm_apply_le_sectionSize V s _
  have hyR : c.val y ∈ ball (c.val x) R :=
    (ball_subset_ball (by linarith : R / 32 ≤ R)) hy.2
  have hyhalf : c.val y ∈ ball (c.val x) (R / 2) :=
    (ball_subset_ball (by linarith : R / 32 ≤ R / 2)) hy.2
  have hxhalf : c.val x ∈ ball (c.val x) (R / 2) := mem_ball_self (half_pos hR)
  have hzero : F (c.val x) = 0 := by
    change (e ⟨c.val.symm (c.val x), s (c.val.symm (c.val x))⟩).2 = 0
    rw [c.val.left_inv (mem_complexChartAt_source x), hs]
    exact map_zero (e.linearEquivAt ℂ x (mem_baseSet_trivializationAt ℂ V x))
  have hLip := SGPT.Foundations.Analysis.Pending.norm_sub_le_of_forall_norm_le hR hhol hbound hyhalf hxhalf
  rw [hzero, sub_zero] at hLip
  have hydist : ‖c.val y - c.val x‖ ≤ R / 32 := by
    have hyball : c.val y ∈ ball (c.val x) (R / 32) := hy.2
    exact (by simpa only [mem_ball, dist_eq_norm] using hyball : ‖c.val y - c.val x‖ < R / 32).le
  have hyfr := hframe (c.val y) hyR
  have hybase : y ∈ e.baseSet := by
    have h := hyfr.1
    change c.val.symm (c.val y) ∈ e.baseSet at h
    rwa [c.val.left_inv hy.1] at h
  have hynorm : frameNorm V e y ≤ 2 * a := by
    have h := hyfr.2.2
    change frameNorm V e (c.val.symm (c.val y)) ≤ 2 * a at h
    rwa [c.val.left_inv hy.1] at h
  have hFy : F (c.val y) = sectionCoefficient V e s y := by
    change sectionCoefficient V e s (c.val.symm (c.val y)) = _
    rw [c.val.left_inv hy.1]
  rw [norm_eq_coefficient_mul_frameNorm V e s hybase, ← hFy]
  have hS : 0 ≤ sectionSize V s := sectionSize_nonneg V s
  calc
    ‖F (c.val y)‖ * frameNorm V e y ≤
        (sectionSize V s / (a / 2) / (R / 2) * (R / 32)) * (2 * a) := by
      exact mul_le_mul (hLip.trans (mul_le_mul_of_nonneg_left hydist (by positivity)))
        hynorm (norm_nonneg _) (by positivity)
    _ = sectionSize V s / 4 := by field_simp; ring
    _ ≤ sectionSize V s / 2 := by have h := sectionSize_nonneg V s; linarith

/-- Compactness INTERNALLY selects finitely many actual points detecting ALL sections. -/
theorem exists_finite_section_detecting_set [CompactSpace X] :
    ∃ A : Finset X, ∀ s : HolomorphicSections (n := n) V,
      (∀ x ∈ A, s x = 0) → s = 0 := by
  classical
  choose U hU hxU hcontrol using exists_local_half_sectionSize (n := n) V
  have hcover : (Set.univ : Set X) ⊆ ⋃ x, U x := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, hxU x⟩
  obtain ⟨A, hA⟩ := isCompact_univ.elim_finite_subcover U hU hcover
  refine ⟨A, fun s hs => ?_⟩
  have hbound : sectionSize V s ≤ sectionSize V s / 2 := by
    apply (sectionSize_le_iff V s (div_nonneg (sectionSize_nonneg V s) (by norm_num))).mpr
    intro y
    obtain ⟨x, hxA, hyU⟩ := Set.mem_iUnion₂.mp (hA (Set.mem_univ y))
    exact hcontrol x s (hs x hxA) y hyU
  have hzero : sectionSize V s = 0 := by
    have hnonneg := sectionSize_nonneg V s
    linarith
  exact (sectionSize_eq_zero_iff V s).mp hzero

omit [IsComplexManifold n X] [ContMDiffVectorBundle ∞ ℂ V (𝓘(ℂ, ComplexModel n))]
  [ContinuousFiberNorm V] in
/-- Actual simultaneous evaluation into the SAME native rank-one fibers. -/
def sectionEvaluation (A : Finset X) :
    HolomorphicSections (n := n) V →ₗ[ℂ] (∀ x : A, V x.val) where
  toFun s x := s x.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The genuine full holomorphic section module is finite-dimensional from compact geometry. -/
theorem holomorphicSections_finiteDimensional [CompactSpace X] :
    FiniteDimensional ℂ (HolomorphicSections (n := n) V) := by
  classical
  obtain ⟨A, hA⟩ := exists_finite_section_detecting_set (n := n) V
  have hinj : Function.Injective (sectionEvaluation (n := n) V A) := by
    intro s t h
    have hzero : s - t = 0 := hA (s - t) (fun x hx => by
      change s x - t x = 0
      exact sub_eq_zero.mpr (congrFun h ⟨x, hx⟩))
    exact sub_eq_zero.mp hzero
  let : ∀ x : A, FiniteDimensional ℂ (V x.val) := fun x =>
    FiniteDimensional.of_injective
      ((trivializationAt ℂ V x.val).linearEquivAt ℂ x.val
        (mem_baseSet_trivializationAt ℂ V x.val)).toLinearMap
      ((trivializationAt ℂ V x.val).linearEquivAt ℂ x.val
        (mem_baseSet_trivializationAt ℂ V x.val)).injective
  exact FiniteDimensional.of_injective (sectionEvaluation (n := n) V A) hinj

/-- The actual finite global supremum is the norm on the SAME full section module. -/
instance sectionNorm [CompactSpace X] : Norm (HolomorphicSections (n := n) V) :=
  ⟨sectionSize V⟩

omit [IsComplexManifold n X] [ContMDiffVectorBundle ∞ ℂ V (𝓘(ℂ, ComplexModel n))] in
/-- Genuine metric compactness and pointwise vector axioms supply every normed-space axiom. -/
theorem sectionNormCore [CompactSpace X] : NormedSpace.Core ℂ (HolomorphicSections (n := n) V) where
  norm_nonneg := sectionSize_nonneg V
  norm_smul := sectionSize_smul V
  norm_triangle := sectionSize_add_le V
  norm_eq_zero_iff := sectionSize_eq_zero_iff V

/-- The actual supremum norm constructs the section topology, rather than assuming one. -/
instance sectionNormedAddCommGroup [CompactSpace X] :
    NormedAddCommGroup (HolomorphicSections (n := n) V) :=
  NormedAddCommGroup.ofCore (sectionNormCore V)

instance sectionNormedSpace [CompactSpace X] :
    NormedSpace ℂ (HolomorphicSections (n := n) V) :=
  NormedSpace.ofCore (sectionNormCore V)

omit [IsComplexManifold n X] [∀ x, NormedSpace ℂ (V x)] [VectorBundle ℂ ℂ V]
  [ContMDiffVectorBundle ∞ ℂ V (𝓘(ℂ, ComplexModel n))] in
/-- The constructed norm retains exact equality with the genuine finite real supremum. -/
theorem norm_section_eq_sectionSize [CompactSpace X] (s : HolomorphicSections (n := n) V) :
    ‖s‖ = sectionSize V s := rfl

/-- The genuine closed balls are compact, as a consequence of produced finite dimension. -/
theorem isCompact_section_closedBall [CompactSpace X]
    (s : HolomorphicSections (n := n) V) (r : ℝ) : IsCompact (closedBall s r) := by
  let := holomorphicSections_finiteDimensional (n := n) V
  let := FiniteDimensional.proper ℂ (HolomorphicSections (n := n) V)
  exact isCompact_closedBall s r

end SGPT.Bergman.CompactHolomorphicSectionsDraft
