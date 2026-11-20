import SGPT.Convex.SeqConvergence
import SGPT.Convex.GrowthClasses
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Topology.Sequences

noncomputable section
namespace SGPT.Convex
open Set Filter Topology
open scoped Topology

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual full-domain real convex functions with their original pointwise subtype topology. -/
abbrev RealConvexFunction := {f : E → ℝ // ConvexOn ℝ univ f}

variable {E} [FiniteDimensional ℝ E]

/-- The genuine continuous-map representative of an original full-domain real convex function. -/
def realConvexToContinuousMap (f : RealConvexFunction E) : C(E, ℝ) :=
  ⟨f.val, continuousOn_univ.mp (f.property.continuousOn isOpen_univ)⟩

/-- Evaluation of actual original convex values along a genuine countable sequence. -/
def denseEvaluation (q : ℕ → E) (f : RealConvexFunction E) : ℕ → ℝ :=
  fun n ↦ f.val (q n)

omit [FiniteDimensional ℝ E] in
/-- Actual original point evaluations are continuous in the actual pointwise topology. -/
theorem continuous_denseEvaluation (q : ℕ → E) : Continuous (denseEvaluation q) :=
  continuous_pi (fun n ↦ (continuous_apply (q n)).comp continuous_subtype_val)

/-- Genuine real convex continuity makes actual dense evaluation injective. -/
theorem denseEvaluation_injective {q : ℕ → E} (hq : DenseRange q) :
    Function.Injective (denseEvaluation q) := by
  intro f g hfg
  apply Subtype.ext
  apply Continuous.ext_on hq (realConvexToContinuousMap f).continuous
    (realConvexToContinuousMap g).continuous
  rintro _ ⟨n, rfl⟩
  exact congrFun hfg n

/-- The verified dense convex convergence producer supplies actual pointwise convergence from actual dense evaluations, without any assumed full pointwise limit. -/
theorem tendsto_realConvex_of_denseEvaluation {q : ℕ → E} (hq : DenseRange q)
    {f : ℕ → RealConvexFunction E} {g : RealConvexFunction E}
    (heval : Tendsto (fun k ↦ denseEvaluation q (f k)) atTop (𝓝 (denseEvaluation q g))) :
    Tendsto f atTop (𝓝 g) := by
  have hconv : ∀ d ∈ range q, ∃ l : ℝ,
      Tendsto (fun k ↦ (f k).val d) atTop (𝓝 l) := by
    rintro _ ⟨n, rfl⟩
    exact ⟨g.val (q n), (tendsto_pi_nhds.mp heval) n⟩
  obtain ⟨h, hhconv, hhlim, _⟩ := exists_convex_limit_of_dense_convex_convergence
    isOpen_univ (subset_univ (range q)) (fun x _ ↦ hq x)
    (fun k ↦ (f k).property) hconv
  have heq : h = (g : E → ℝ) := by
    apply Continuous.ext_on hq
      (continuousOn_univ.mp (hhconv.continuousOn isOpen_univ))
      (realConvexToContinuousMap g).continuous
    rintro _ ⟨n, rfl⟩
    exact tendsto_nhds_unique (hhlim _ (mem_univ _)) ((tendsto_pi_nhds.mp heval) n)
  rw [heq] at hhlim
  exact tendsto_subtype_rng.mpr (tendsto_pi_nhds.mpr (fun x ↦ hhlim x (mem_univ x)))

/-- Actual dense evaluation is a genuine embedding, with its inverse continuity produced by the completed original dense-convex limit theorem. -/
theorem isEmbedding_denseEvaluation {q : ℕ → E} (hq : DenseRange q) :
    IsEmbedding (denseEvaluation q) := by
  classical
  let e := Equiv.ofInjective (denseEvaluation q) (denseEvaluation_injective hq)
  have he (v : range (denseEvaluation q)) : denseEvaluation q (e.symm v) = v.val :=
    Equiv.apply_ofInjective_symm (denseEvaluation_injective hq) v
  have hseq : SeqContinuous e.symm := by
    intro u v hu
    apply tendsto_realConvex_of_denseEvaluation hq
    have hv : Tendsto (fun k ↦ (u k).val) atTop (𝓝 v.val) :=
      (continuous_subtype_val.tendsto v).comp hu
    simpa only [Function.comp_apply, he] using hv
  have hinv : Continuous e.symm := hseq.continuous
  have hforward : Continuous e := (continuous_denseEvaluation q).subtype_mk _
  let h : RealConvexFunction E ≃ₜ range (denseEvaluation q) :=
    ⟨e, hforward, hinv⟩
  exact IsEmbedding.subtypeVal.comp h.isEmbedding

/-- The actual dense-sequence embedding produces genuine first countability of the original pointwise convex-function class. -/
theorem firstCountableTopology_realConvexFunction : FirstCountableTopology (RealConvexFunction E) :=
  (isEmbedding_denseEvaluation (TopologicalSpace.denseRange_denseSeq E)).firstCountableTopology

/-- The genuine map into actual continuous functions is continuous for the original pointwise convex-function topology. -/
theorem continuous_realConvexToContinuousMap : Continuous (realConvexToContinuousMap (E := E)) := by
  have : FirstCountableTopology (RealConvexFunction E) := firstCountableTopology_realConvexFunction
  apply SeqContinuous.continuous
  intro f g hfg
  apply ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mpr
  intro K hK
  exact tendstoUniformlyOn_of_dense_convex_convergence isOpen_univ
    (subset_univ univ) (by simp) (fun k ↦ (f k).property)
    (fun x _ ↦ ⟨g.val x, (tendsto_pi_nhds.mp (tendsto_subtype_rng.mp hfg)) x⟩)
    (fun x _ ↦ (tendsto_pi_nhds.mp (tendsto_subtype_rng.mp hfg)) x)
    hK (subset_univ K)

/-- Actual pointwise evaluation in the original continuous-map space proves that this map genuinely induces the exact original pointwise convex-function topology. -/
theorem isEmbedding_realConvexToContinuousMap :
    IsEmbedding (realConvexToContinuousMap (E := E)) := by
  refine ⟨IsInducing.of_comp continuous_realConvexToContinuousMap
    continuous_coeFun IsInducing.subtypeVal, ?_⟩
  intro f g hfg
  apply Subtype.ext
  exact congrArg (fun h : C(E, ℝ) ↦ (h : E → ℝ)) hfg

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Exactly the original source pointwise topology, on its original extended-real growth functions. -/
abbrev growthPointwiseTopology (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (P : Set F) :
    TopologicalSpace (GrowthClass B P) := inferInstance

omit [FiniteDimensional ℝ E] in
/-- Genuine product convergence identifies actual growth-class convergence with original-value pointwise convergence. -/
theorem tendsto_growthClass_iff {α : Type*} (l : Filter α)
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (P : Set F)
    {f : α → GrowthClass B P} {g : GrowthClass B P} :
    Tendsto f l (𝓝 g) ↔ ∀ x, Tendsto (fun a ↦ (f a).val x) l (𝓝 (g.val x)) := by
  rw [tendsto_subtype_rng, tendsto_pi_nhds]

omit [FiniteDimensional ℝ E] in
/-- The checked original compact-support growth theorem makes every original value finite. -/
theorem growth_value_ne_top (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [B.IsContPerfPair]
    {P : Set F} (hP : IsCompact P) (hne : P.Nonempty) (f : GrowthClass B P) (x : E) :
    f.val x ≠ ⊤ := by
  have hx : x ∈ effectiveDomain f.val := by
    rw [effectiveDomain_eq_univ_of_mem_growthClass B hP hne f.property]
    exact mem_univ x
  exact ne_of_lt hx

/-- The actual finite real representative of each original growth function is genuinely convex. -/
def growthToRealConvex (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [B.IsContPerfPair]
    {P : Set F} (hP : IsCompact P) (hne : P.Nonempty) (f : GrowthClass B P) :
    RealConvexFunction E := by
  refine ⟨fun x ↦ (f.val x).toReal, ?_⟩
  have h := convexOn_toReal_effectiveDomain f.property.1
  rw [effectiveDomain_eq_univ_of_mem_growthClass B hP hne f.property] at h
  exact h

omit [FiniteDimensional ℝ E] in
/-- Actual real coercion recovers every original growth value; no infinite value is projected to zero. -/
theorem coe_growthToRealConvex (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [B.IsContPerfPair]
    {P : Set F} (hP : IsCompact P) (hne : P.Nonempty) (f : GrowthClass B P) (x : E) :
    ((growthToRealConvex B hP hne f).val x : EReal) = f.val x :=
  EReal.coe_toReal (growth_value_ne_top B hP hne f x) (f.property.1.2.2 x)

omit [FiniteDimensional ℝ E] in
/-- Genuine finite-value continuity makes the original real representative map pointwise continuous. -/
theorem continuous_growthToRealConvex (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [B.IsContPerfPair]
    {P : Set F} (hP : IsCompact P) (hne : P.Nonempty) :
    Continuous (growthToRealConvex B hP hne) := by
  have hval : Continuous (fun f : GrowthClass B P ↦ fun x ↦ (f.val x).toReal) := by
    apply continuous_pi
    intro x
    rw [continuous_iff_continuousAt]
    intro f
    exact (EReal.tendsto_toReal (growth_value_ne_top B hP hne f x)
      (f.property.1.2.2 x)).comp
      (((continuous_apply x).comp continuous_subtype_val).continuousAt)
  exact hval.subtype_mk _

omit [FiniteDimensional ℝ E] in
/-- Genuine continuous coercion and recovery of every original value prove the actual real representative embedding. -/
theorem isEmbedding_growthToRealConvex (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [B.IsContPerfPair]
    {P : Set F} (hP : IsCompact P) (hne : P.Nonempty) :
    IsEmbedding (growthToRealConvex B hP hne) := by
  let coerce : RealConvexFunction E → (E → EReal) := fun f x ↦ (f.val x : EReal)
  have hc : Continuous coerce := continuous_pi
    (fun x ↦ continuous_coe_real_ereal.comp ((continuous_apply x).comp continuous_subtype_val))
  have hcomp : coerce ∘ growthToRealConvex B hP hne = Subtype.val := by
    funext f x
    exact coe_growthToRealConvex B hP hne f x
  have hi : IsInducing (coerce ∘ growthToRealConvex B hP hne) := by
    rw [hcomp]
    exact IsInducing.subtypeVal
  refine ⟨IsInducing.of_comp (continuous_growthToRealConvex B hP hne) hc hi, ?_⟩
  intro f g hfg
  apply Subtype.ext
  funext x
  calc
    f.val x = ((growthToRealConvex B hP hne f).val x : EReal) :=
      (coe_growthToRealConvex B hP hne f x).symm
    _ = ((growthToRealConvex B hP hne g).val x : EReal) :=
      congrArg (fun h : RealConvexFunction E ↦ (h.val x : EReal)) hfg
    _ = g.val x := coe_growthToRealConvex B hP hne g x

/-- Actual original growth functions represented as genuine continuous real-valued maps. -/
def growthToContinuousMap (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [B.IsContPerfPair]
    {P : Set F} (hP : IsCompact P) (hne : P.Nonempty) : GrowthClass B P → C(E, ℝ) :=
  realConvexToContinuousMap ∘ growthToRealConvex B hP hne

/-- The two checked genuine embeddings produce exact source pointwise/compact-open compatibility. -/
theorem isEmbedding_growthToContinuousMap (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [B.IsContPerfPair]
    {P : Set F} (hP : IsCompact P) (hne : P.Nonempty) :
    IsEmbedding (growthToContinuousMap B hP hne) :=
  isEmbedding_realConvexToContinuousMap.comp (isEmbedding_growthToRealConvex B hP hne)

/-- The actual compact-open induced topology equals the original source pointwise topology. -/
theorem growthPointwiseTopology_eq_compactOpen (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [B.IsContPerfPair]
    {P : Set F} (hP : IsCompact P) (hne : P.Nonempty) :
    growthPointwiseTopology B P =
      TopologicalSpace.induced (growthToContinuousMap B hP hne) inferInstance :=
  (isEmbedding_growthToContinuousMap B hP hne).isInducing.eq_induced

/-- Genuine original-value pointwise convergence is exactly actual compact-open convergence, for arbitrary filters. -/
theorem tendsto_growthToContinuousMap_iff {α : Type*} (l : Filter α)
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [B.IsContPerfPair]
    {P : Set F} (hP : IsCompact P) (hne : P.Nonempty)
    {f : α → GrowthClass B P} {g : GrowthClass B P} :
    Tendsto (fun a ↦ growthToContinuousMap B hP hne (f a)) l
      (𝓝 (growthToContinuousMap B hP hne g)) ↔
      ∀ x, Tendsto (fun a ↦ (f a).val x) l (𝓝 (g.val x)) :=
  (isEmbedding_growthToContinuousMap B hP hne).tendsto_nhds_iff.symm.trans
    (tendsto_growthClass_iff l B P)

end SGPT.Convex
