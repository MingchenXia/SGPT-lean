import SGPT.Okounkov.SchemeLineBundleMetricGeometry
import SGPT.Bergman.SourceSmoothMetricPolynomialBound
import SGPT.PSH.GlobalL2Statement
import SGPT.Foundations.Analysis.Pending.HolomorphicGermAlgebra

/-!
# The analytification of a metrized algebraic line bundle

Blueprint `claude-gagamult2:bundle`.  Let `X` be smooth of relative dimension `n` over `ℂ`
with a closed projective embedding, `L` an algebraic line bundle on `X` (an `X.Modules` with a
rank-one atlas `a`) and `H` a smooth Hermitian metric on `L`
(`SGPT.Okounkov.SchemeLineBundleMetric`: a positive smooth squared norm `|α|²_H` for every
algebraic local frame `α`, with the transition law).  We construct the analytic line bundle
`(L, H)^an` on the complex manifold `X(ℂ)` as a `HermitianHolomorphicLineBundle` (the bundled
form used by the global `L²` theory and Siu's theorem):

* the fibre at `p` is `ℂ`, with its standard Hermitian norm, read as the multiples of the
  `H`-unit vector of the preferred atlas frame at `p`;
* the holomorphic atlas consists of one trivialization for every *algebraic* local frame
  `α` of `L` (`schemeHermitianAtlasFrame`), with base set the complex points of the domain of
  `α`; its transition functions are the analytic realizations of the algebraic transition units
  (`schemeFrameTransition`), so the bundle is holomorphic;
* `‖α(p)‖² = |α|²_H(p)` (`schemeHermitianAtlasFrame_norm_sq`); hence the metric is smooth
  (`isSourceSmoothHermitianMetric_schemeHermitianLineBundle`) and its first Chern form is the
  existing Chern form `H.curvature a` (`isOwnFirstChernForm_schemeHermitianLineBundle`).

Every atlas frame of the bundle is one of the `schemeHermitianAtlasFrame α`
(`exists_eq_schemeHermitianAtlasFrame`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.GAGAMult

open Set Filter Bundle
open scoped Topology Manifold ContDiff
open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves SGPT.Foundations.Analysis.Pending
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
open SGPT.Bergman.PolynomialH0Growth SGPT.PSH.GlobalL2 Topology

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ) [SmoothOfRelativeDimension n f]
  (E : ClosedProjectiveEmbedding f) {L : X.Modules} (a : LineBundleAtlas L)
  (H : SchemeLineBundleMetric f n E L)

local instance schemeHermitianPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance schemeHermitianPointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n

/-! ### Fibres and frame coefficients -/

/-- The fibre of `(L, H)^an` at `p`: a copy of `ℂ`, read as the multiples of the `H`-unit vector
of the preferred atlas frame at `p`. -/
@[nolint unusedArguments]
def SchemeHermitianFiber (_a : LineBundleAtlas L) (_H : SchemeLineBundleMetric f n E L)
    (_p : SchemeComplexPoint f) : Type := ℂ

instance (p : SchemeComplexPoint f) : NormedAddCommGroup (SchemeHermitianFiber f n E a H p) :=
  inferInstanceAs (NormedAddCommGroup ℂ)

instance (p : SchemeComplexPoint f) : InnerProductSpace ℂ (SchemeHermitianFiber f n E a H p) :=
  inferInstanceAs (InnerProductSpace ℂ ℂ)

/-- The preferred atlas index at `p`. -/
def prefIndex (p : SchemeComplexPoint f) : a.I :=
  (schemeLineBundleCore f n E a).indexAt p

theorem mem_prefIndex (p : SchemeComplexPoint f) :
    schemeComplexPointImage f p ∈ a.opens (prefIndex f n E a p) :=
  (schemeLineBundleCore f n E a).mem_baseSet_at p

/-- The coefficient, in the algebraic frame `α`, of the unit vector of the fibre at `p`:
`g_{iα}(p) / |e_i(p)|_H`, `e_i` the preferred atlas frame. -/
def frameCoef {U : X.Opens} (α : LocalBundleFrame L U) (p : SchemeComplexPoint f) : ℂ :=
  schemeFrameTransition f n E (a.frame (prefIndex f n E a p)) α p *
    ((Real.sqrt (H.frameNormSq (a.frame (prefIndex f n E a p)) p))⁻¹ : ℝ)

theorem frameCoef_ne_zero {U : X.Opens} (α : LocalBundleFrame L U) {p : SchemeComplexPoint f}
    (hp : schemeComplexPointImage f p ∈ U) : frameCoef f n E a H α p ≠ 0 := by
  unfold frameCoef
  refine mul_ne_zero (schemeFrameTransition_ne_zero f n E _ _ p (mem_prefIndex f n E a p) hp) ?_
  have hpos := H.positive (a.frame (prefIndex f n E a p)) p (mem_prefIndex f n E a p)
  exact_mod_cast (inv_pos.mpr (Real.sqrt_pos.mpr hpos)).ne'

/-- Change of algebraic frame: `c_β = g_{αβ} c_α`. -/
theorem frameCoef_transition {U V : X.Opens} (α : LocalBundleFrame L U)
    (β : LocalBundleFrame L V) {p : SchemeComplexPoint f} (hpU : schemeComplexPointImage f p ∈ U)
    (hpV : schemeComplexPointImage f p ∈ V) :
    frameCoef f n E a H β p = schemeFrameTransition f n E α β p * frameCoef f n E a H α p := by
  unfold frameCoef
  rw [schemeFrameTransition_cocycle f n E (a.frame (prefIndex f n E a p)) α β p
    (mem_prefIndex f n E a p) hpU hpV]
  ring

/-- `|c_α(p)|² · |α|²_H(p) = 1`. -/
theorem normSq_frameCoef_mul {U : X.Opens} (α : LocalBundleFrame L U)
    {p : SchemeComplexPoint f} (hp : schemeComplexPointImage f p ∈ U) :
    Complex.normSq (frameCoef f n E a H α p) * H.frameNormSq α p = 1 := by
  set i := prefIndex f n E a p
  have hi := mem_prefIndex f n E a p
  have hpos := H.positive (a.frame i) p hi
  have htr := H.transition (a.frame i) α p hi hp
  unfold frameCoef
  rw [Complex.normSq_mul, Complex.normSq_ofReal]
  have hs : (Real.sqrt (H.frameNormSq (a.frame i) p))⁻¹ * (Real.sqrt (H.frameNormSq (a.frame i) p))⁻¹ =
      (H.frameNormSq (a.frame i) p)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hpos.le]
  rw [mul_assoc, hs]
  rw [htr] at hpos ⊢
  have hα : 0 < H.frameNormSq α p := H.positive α p hp
  have hg : Complex.normSq (schemeFrameTransition f n E (a.frame i) α p) ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hpos; exact lt_irrefl 0 hpos
  field_simp
  rfl

/-! ### The holomorphic atlas -/

/-- The trivialization of `(L, H)^an` given by the algebraic local frame `α` on `U`. -/
def schemeHermitianPretrivialization {U : X.Opens} (α : LocalBundleFrame L U) :
    Pretrivialization ℂ (TotalSpace.proj :
      TotalSpace ℂ (SchemeHermitianFiber f n E a H) → SchemeComplexPoint f) where
  toFun q := (q.proj, frameCoef f n E a H α q.proj * (show ℂ from q.snd))
  invFun q := ⟨q.1, (frameCoef f n E a H α q.1)⁻¹ * q.2⟩
  source := TotalSpace.proj ⁻¹' (schemeComplexPointImage f ⁻¹' U)
  target := (schemeComplexPointImage f ⁻¹' U) ×ˢ Set.univ
  map_source' := fun _ hq => ⟨hq, Set.mem_univ _⟩
  map_target' := fun _ hq => hq.1
  left_inv' := by
    rintro ⟨p, z⟩ hp
    simp only [TotalSpace.mk_inj]
    change (frameCoef f n E a H α p)⁻¹ * (frameCoef f n E a H α p * (show ℂ from z)) =
      (show ℂ from z)
    rw [← mul_assoc, inv_mul_cancel₀ (frameCoef_ne_zero f n E a H α hp), one_mul]
  right_inv' := by
    rintro ⟨p, z⟩ ⟨hp, _⟩
    change (p, frameCoef f n E a H α p * ((frameCoef f n E a H α p)⁻¹ * z)) = (p, z)
    rw [← mul_assoc, mul_inv_cancel₀ (frameCoef_ne_zero f n E a H α hp), one_mul]
  open_target := (U.isOpen.preimage (schemeComplexPointImage_continuous f)).prod isOpen_univ
  baseSet := schemeComplexPointImage f ⁻¹' U
  open_baseSet := U.isOpen.preimage (schemeComplexPointImage_continuous f)
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

instance schemeHermitianPretrivialization_isLinear {U : X.Opens} (α : LocalBundleFrame L U) :
    (schemeHermitianPretrivialization f n E a H α).IsLinear ℂ where
  linear p _ := {
    map_add := by
      intro z t
      change frameCoef f n E a H α p * ((show ℂ from z) + (show ℂ from t)) =
        frameCoef f n E a H α p * (show ℂ from z) + frameCoef f n E a H α p * (show ℂ from t)
      ring
    map_smul := by
      intro c z
      change frameCoef f n E a H α p * (c * (show ℂ from z)) =
        c * (frameCoef f n E a H α p * (show ℂ from z))
      ring }

theorem schemeHermitianPretrivialization_symm {U : X.Opens} (α : LocalBundleFrame L U)
    {p : SchemeComplexPoint f} (hp : schemeComplexPointImage f p ∈ U) (z : ℂ) :
    (schemeHermitianPretrivialization f n E a H α).symm p z =
      (frameCoef f n E a H α p)⁻¹ * z := by
  have hh := (schemeHermitianPretrivialization f n E a H α).mk_symm hp z
  change (⟨p, (schemeHermitianPretrivialization f n E a H α).symm p z⟩ :
      TotalSpace ℂ (SchemeHermitianFiber f n E a H)) =
        ⟨p, (frameCoef f n E a H α p)⁻¹ * z⟩ at hh
  simpa only [TotalSpace.mk_inj] using hh

/-- The algebraic local frames, as the index set of the holomorphic atlas. -/
abbrev AlgebraicFrame (L : X.Modules) := Σ U : X.Opens, LocalBundleFrame L U

/-- The coordinate change between two algebraic frames: multiplication by the analytic
transition unit. -/
def schemeHermitianCoordChange {U V : X.Opens} (α : LocalBundleFrame L U)
    (β : LocalBundleFrame L V) (p : SchemeComplexPoint f) : ℂ →L[ℂ] ℂ :=
  ContinuousLinearMap.smulRightL ℂ ℂ ℂ (ContinuousLinearMap.id ℂ ℂ)
    (schemeFrameTransition f n E α β p)

theorem schemeHermitianCoordChange_apply {U V : X.Opens} (α : LocalBundleFrame L U)
    (β : LocalBundleFrame L V) {p : SchemeComplexPoint f} (hpU : schemeComplexPointImage f p ∈ U)
    (hpV : schemeComplexPointImage f p ∈ V) (z : ℂ) :
    schemeHermitianCoordChange f n E α β p z =
      ((schemeHermitianPretrivialization f n E a H β)
        ⟨p, (schemeHermitianPretrivialization f n E a H α).symm p z⟩).2 := by
  rw [schemeHermitianPretrivialization_symm f n E a H α hpU z]
  change z * schemeFrameTransition f n E α β p =
    frameCoef f n E a H β p * ((frameCoef f n E a H α p)⁻¹ * z)
  rw [frameCoef_transition f n E a H α β hpU hpV]
  field_simp [frameCoef_ne_zero f n E a H α hpU]

variable [IsSeparated f] [QuasiCompact f]

local instance schemeHermitianPointManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

theorem contMDiffOn_schemeFrameTransition {U V : X.Opens} (α : LocalBundleFrame L U)
    (β : LocalBundleFrame L V) :
    ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) ∞ (schemeFrameTransition f n E α β)
      (schemeComplexPointImage f ⁻¹' U ∩ schemeComplexPointImage f ⁻¹' V) := by
  intro p hp
  exact (contMDiffAt_of_eventually_mdifferentiableAt
    (schemeFrameTransition_holomorphicAt f n E α β p hp.1 hp.2)).contMDiffWithinAt

theorem contMDiffOn_schemeHermitianCoordChange {U V : X.Opens} (α : LocalBundleFrame L U)
    (β : LocalBundleFrame L V) :
    ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ∞
      (schemeHermitianCoordChange f n E α β)
      (schemeComplexPointImage f ⁻¹' U ∩ schemeComplexPointImage f ⁻¹' V) :=
  (ContinuousLinearMap.smulRightL ℂ ℂ ℂ (ContinuousLinearMap.id ℂ ℂ)).contMDiff.comp_contMDiffOn
    (contMDiffOn_schemeFrameTransition f n E α β)

/-- The vector prebundle of `(L, H)^an`, with one trivialization per algebraic local frame. -/
def schemeHermitianVectorPrebundle :
    VectorPrebundle ℂ ℂ (SchemeHermitianFiber f n E a H) where
  pretrivializationAtlas :=
    Set.range fun α : AlgebraicFrame L => schemeHermitianPretrivialization f n E a H α.2
  pretrivialization_linear' := by
    rintro _ ⟨α, rfl⟩
    infer_instance
  pretrivializationAt p :=
    schemeHermitianPretrivialization f n E a H (a.frame (prefIndex f n E a p))
  mem_base_pretrivializationAt p := mem_prefIndex f n E a p
  pretrivialization_mem_atlas p := ⟨⟨_, a.frame (prefIndex f n E a p)⟩, rfl⟩
  exists_coordChange := by
    rintro _ ⟨α, rfl⟩ _ ⟨β, rfl⟩
    exact ⟨schemeHermitianCoordChange f n E α.2 β.2,
      (contMDiffOn_schemeHermitianCoordChange f n E α.2 β.2).continuousOn,
      fun p hp z => schemeHermitianCoordChange_apply f n E a H α.2 β.2 hp.1 hp.2 z⟩
  totalSpaceMk_isInducing := by
    intro p
    have hne := frameCoef_ne_zero f n E a H (a.frame (prefIndex f n E a p))
      (mem_prefIndex f n E a p)
    change IsInducing (fun z : ℂ => (p, frameCoef f n E a H (a.frame (prefIndex f n E a p)) p * z))
    exact isInducing_const_prod.mpr (Homeomorph.mulLeft₀ _ hne).isInducing

instance schemeHermitianTotalSpaceTopology :
    TopologicalSpace (TotalSpace ℂ (SchemeHermitianFiber f n E a H)) :=
  (schemeHermitianVectorPrebundle f n E a H).totalSpaceTopology

instance schemeHermitianFiberBundle : FiberBundle ℂ (SchemeHermitianFiber f n E a H) :=
  (schemeHermitianVectorPrebundle f n E a H).toFiberBundle

instance schemeHermitianVectorBundle : VectorBundle ℂ ℂ (SchemeHermitianFiber f n E a H) :=
  (schemeHermitianVectorPrebundle f n E a H).toVectorBundle

instance schemeHermitianPrebundleHolomorphic :
    (schemeHermitianVectorPrebundle f n E a H).IsContMDiff (𝓘(ℂ, ComplexModel n)) ∞ where
  exists_contMDiffCoordChange := by
    rintro _ ⟨α, rfl⟩ _ ⟨β, rfl⟩
    exact ⟨schemeHermitianCoordChange f n E α.2 β.2,
      contMDiffOn_schemeHermitianCoordChange f n E α.2 β.2,
      fun p hp z => schemeHermitianCoordChange_apply f n E a H α.2 β.2 hp.1 hp.2 z⟩

instance schemeHermitianHolomorphicBundle :
    ContMDiffVectorBundle ∞ ℂ (SchemeHermitianFiber f n E a H) (𝓘(ℂ, ComplexModel n)) :=
  (schemeHermitianVectorPrebundle f n E a H).contMDiffVectorBundle (𝓘(ℂ, ComplexModel n))

/-- The trivialization of the bundle given by the algebraic local frame `α`. -/
def schemeHermitianTrivialization {U : X.Opens} (α : LocalBundleFrame L U) :
    Trivialization ℂ (TotalSpace.proj :
      TotalSpace ℂ (SchemeHermitianFiber f n E a H) → SchemeComplexPoint f) :=
  (schemeHermitianVectorPrebundle f n E a H).trivializationOfMemPretrivializationAtlas
    ⟨⟨U, α⟩, rfl⟩

instance schemeHermitianTrivialization_memAtlas {U : X.Opens} (α : LocalBundleFrame L U) :
    MemTrivializationAtlas (schemeHermitianTrivialization f n E a H α) where
  out := ⟨_, ⟨⟨U, α⟩, rfl⟩, rfl⟩

theorem schemeHermitianTrivialization_baseSet {U : X.Opens} (α : LocalBundleFrame L U) :
    (schemeHermitianTrivialization f n E a H α).baseSet = schemeComplexPointImage f ⁻¹' U :=
  rfl

theorem schemeHermitianTrivialization_apply {U : X.Opens} (α : LocalBundleFrame L U)
    (p : SchemeComplexPoint f) (v : SchemeHermitianFiber f n E a H p) :
    ((schemeHermitianTrivialization f n E a H α) ⟨p, v⟩).2 =
      frameCoef f n E a H α p * (show ℂ from v) :=
  rfl

theorem schemeHermitianTrivialization_symm {U : X.Opens} (α : LocalBundleFrame L U)
    {p : SchemeComplexPoint f} (hp : schemeComplexPointImage f p ∈ U) (z : ℂ) :
    (schemeHermitianTrivialization f n E a H α).symm p z = (frameCoef f n E a H α p)⁻¹ * z :=
  schemeHermitianPretrivialization_symm f n E a H α hp z

/-- `‖v‖² = |v_α|² · |α|²_H`, `v_α` the coefficient of `v` in the frame `α`. -/
theorem schemeHermitian_norm_sq_eq {U : X.Opens} (α : LocalBundleFrame L U)
    {p : SchemeComplexPoint f} (hp : schemeComplexPointImage f p ∈ U)
    (v : SchemeHermitianFiber f n E a H p) :
    ‖v‖ ^ 2 = Complex.normSq (((schemeHermitianTrivialization f n E a H α) ⟨p, v⟩).2) *
      H.frameNormSq α p := by
  have h1 := normSq_frameCoef_mul f n E a H α hp
  have hv : ‖v‖ ^ 2 = Complex.normSq (show ℂ from v) := (Complex.normSq_eq_norm_sq _).symm
  rw [schemeHermitianTrivialization_apply, Complex.normSq_mul, hv]
  linear_combination (-(Complex.normSq (show ℂ from v))) * h1

omit [IsSeparated f] [QuasiCompact f] in
theorem continuousAt_frameNormSq {U : X.Opens} (α : LocalBundleFrame L U)
    {p : SchemeComplexPoint f} (hp : schemeComplexPointImage f p ∈ U) :
    ContinuousAt (H.frameNormSq α) p := by
  let c : ComplexChart n (SchemeComplexPoint f) := complexChartAt (n := n) p
  have hpc : p ∈ c.val.source := mem_complexChartAt_source p
  have hD : IsOpen (c.val.target ∩ c.val.symm ⁻¹' (schemeComplexPointImage f ⁻¹' U)) :=
    c.val.isOpen_inter_preimage_symm (U.isOpen.preimage (schemeComplexPointImage_continuous f))
  have hz : c.val p ∈ c.val.target ∩ c.val.symm ⁻¹' (schemeComplexPointImage f ⁻¹' U) :=
    ⟨c.val.map_source hpc, by rw [mem_preimage, c.val.left_inv hpc]; exact hp⟩
  have h1 : ContinuousAt (fun z => H.frameNormSq α (c.val.symm z)) (c.val p) :=
    ((H.smooth α c).continuousOn).continuousAt (hD.mem_nhds hz)
  have h2 : ContinuousAt c.val p := c.val.continuousAt hpc
  have h3 := h1.comp h2
  refine h3.congr_of_eventuallyEq ?_
  filter_upwards [c.val.open_source.mem_nhds hpc] with q hq
  simp only [Function.comp_apply, c.val.left_inv hq]

/-- The norm of `(L, H)^an` is continuous on the total space. -/
theorem continuous_schemeHermitian_norm_sq :
    Continuous (fun q : TotalSpace ℂ (SchemeHermitianFiber f n E a H) => ‖q.snd‖ ^ 2) := by
  rw [continuous_iff_continuousAt]
  intro q
  let α := a.frame (prefIndex f n E a q.proj)
  have hq : schemeComplexPointImage f q.proj ∈ a.opens (prefIndex f n E a q.proj) :=
    mem_prefIndex f n E a q.proj
  let e := schemeHermitianTrivialization f n E a H α
  have hqe : q ∈ e.source := hq
  have he : ContinuousAt (fun r : TotalSpace ℂ (SchemeHermitianFiber f n E a H) => (e r).2) q :=
    (e.continuousOn.continuousAt (e.open_source.mem_nhds hqe)).snd
  have hp : ContinuousAt
      (fun r : TotalSpace ℂ (SchemeHermitianFiber f n E a H) => r.proj) q :=
    (FiberBundle.continuous_proj ℂ (SchemeHermitianFiber f n E a H)).continuousAt
  have hw : ContinuousAt
      (fun r : TotalSpace ℂ (SchemeHermitianFiber f n E a H) => H.frameNormSq α r.proj) q :=
    (continuousAt_frameNormSq f n E H α hq).comp hp
  have hexpr := (Complex.continuous_normSq.continuousAt.comp he).mul hw
  apply hexpr.congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hqe] with r hr
  exact schemeHermitian_norm_sq_eq f n E a H α hr r.snd

instance schemeHermitianContinuousFiberNorm :
    ContinuousFiberNorm (SchemeHermitianFiber f n E a H) := by
  refine ⟨?_⟩
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm] using
    Real.continuous_sqrt.comp (continuous_schemeHermitian_norm_sq f n E a H)

/-- **The analytification `(L, H)^an`** of the metrized algebraic line bundle `(L, H)`, as a
Hermitian holomorphic line bundle on the complex manifold `X(ℂ)`. -/
def schemeHermitianLineBundle : HermitianHolomorphicLineBundle.{0, 0} n (SchemeComplexPoint f) :=
  HermitianHolomorphicLineBundle.ofNative (SchemeHermitianFiber f n E a H)

/-- The atlas frame of `(L, H)^an` given by an algebraic local frame `α`. -/
def schemeHermitianAtlasFrame {U : X.Opens} (α : LocalBundleFrame L U) :
    HermitianHolomorphicLineBundle.AtlasFrame (schemeHermitianLineBundle f n E a H) :=
  ⟨schemeHermitianTrivialization f n E a H α, inferInstance⟩

theorem schemeHermitianAtlasFrame_baseSet {U : X.Opens} (α : LocalBundleFrame L U) :
    (schemeHermitianAtlasFrame f n E a H α).val.baseSet = schemeComplexPointImage f ⁻¹' U :=
  rfl

/-- The frame vector `α(p)` has `H`-squared norm `|α|²_H(p)`. -/
theorem schemeHermitianAtlasFrame_norm_sq {U : X.Opens} (α : LocalBundleFrame L U)
    {p : SchemeComplexPoint f} (hp : schemeComplexPointImage f p ∈ U) :
    ‖(schemeHermitianAtlasFrame f n E a H α).val.symm p 1‖ ^ 2 = H.frameNormSq α p := by
  change ‖(schemeHermitianTrivialization f n E a H α).symm p 1‖ ^ 2 = _
  rw [schemeHermitian_norm_sq_eq f n E a H α hp,
    (schemeHermitianTrivialization f n E a H α).apply_mk_symm hp, Complex.normSq_one, one_mul]

/-- Every atlas frame of `(L, H)^an` is the frame of an algebraic local frame. -/
theorem exists_eq_schemeHermitianAtlasFrame
    (e : HermitianHolomorphicLineBundle.AtlasFrame (schemeHermitianLineBundle f n E a H)) :
    ∃ (U : X.Opens) (α : LocalBundleFrame L U), e.val = schemeHermitianTrivialization f n E a H α := by
  obtain ⟨e, he⟩ := e
  obtain ⟨e', ⟨⟨U, α⟩, rfl⟩, rfl⟩ := he.out
  exact ⟨U, α, rfl⟩

/-- The metric of `(L, H)^an` is smooth. -/
theorem isSourceSmoothHermitianMetric_schemeHermitianLineBundle :
    IsSourceSmoothHermitianMetric (schemeHermitianLineBundle f n E a H) := by
  intro c e
  obtain ⟨U, α, he⟩ := exists_eq_schemeHermitianAtlasFrame f n E a H e
  have hb : e.val.baseSet = schemeComplexPointImage f ⁻¹' U := by rw [he]; rfl
  rw [hb]
  refine (H.smooth α c).congr fun z hz => ?_
  have h := schemeHermitianAtlasFrame_norm_sq f n E a H α (p := c.val.symm z) hz.2
  rw [← h]
  change ‖e.val.symm (c.val.symm z) 1‖ ^ 2 = ‖(schemeHermitianTrivialization f n E a H α).symm
    (c.val.symm z) 1‖ ^ 2
  rw [he]

/-- The first Chern form of `(L, H)^an` is the Chern form `H.curvature a` of `(L, H)`. -/
theorem isOwnFirstChernForm_schemeHermitianLineBundle :
    IsOwnFirstChernForm (schemeHermitianLineBundle f n E a H)
      (letI := E.isSeparated; letI := E.quasiCompact; H.curvature a) := by
  intro c e z hz hze
  obtain ⟨U, α, he⟩ := exists_eq_schemeHermitianAtlasFrame f n E a H e
  have hzU : schemeComplexPointImage f (c.val.symm z) ∈ U := by
    have : c.val.symm z ∈ e.val.baseSet := hze
    rw [he] at this
    exact this
  rw [H.curvature_coeff_frame a α c hz hzU]
  apply smoothDDC_congr
  have hD : IsOpen (c.val.target ∩ c.val.symm ⁻¹' (schemeComplexPointImage f ⁻¹' U)) :=
    c.val.isOpen_inter_preimage_symm (U.isOpen.preimage (schemeComplexPointImage_continuous f))
  filter_upwards [hD.mem_nhds ⟨hz, hzU⟩] with w hw
  have h := schemeHermitianAtlasFrame_norm_sq f n E a H α (p := c.val.symm w) hw.2
  change -Real.log (H.frameNormSq α (c.val.symm w)) =
    -Real.log (‖e.val.symm (c.val.symm w) 1‖ ^ 2)
  rw [he]
  change _ = -Real.log (‖(schemeHermitianAtlasFrame f n E a H α).val.symm (c.val.symm w) 1‖ ^ 2)
  rw [h]

end SGPT.NAPotential.GAGAMult
