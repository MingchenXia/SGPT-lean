import SGPT.PSH.SourceSubgeodesicRays
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open scoped ProductComplexManifold
open FirstPass.AnalyticGluingData

/-- The actual complex coordinate on ANY original open time domain. -/
def sourceComplexOpenTime (U : Opens (ComplexModel 1)) (z : U) : ℂ :=
  sourceRayTimeModelEquiv z.val

/-- Every actual open-time chart reads the SAME genuine complex coordinate.
The actual center supplies nonemptiness, without a chosen global chart. -/
theorem sourceComplexOpenTime_chart_holomorphic (U : Opens (ComplexModel 1))
    (z₀ : U) (b : ComplexChart 1 U) :
    DifferentiableOn ℂ (sourceComplexOpenTime U ∘ b.val.symm) b.val.target := by
  have hchart (z : U) : b.val z = z.val := by
    obtain ⟨x, hx⟩ := Opens.chart_eq (show Nonempty U from ⟨z₀⟩) b.property
    rw [hx]
    rfl
  have hsymm (z : ComplexModel 1) (hz : z ∈ b.val.target) :
      (b.val.symm z).val = z := by
    have hh := b.val.right_inv hz
    rwa [hchart] at hh
  apply sourceRayTimeModelEquiv.differentiable.differentiableOn.congr
  intro z hz
  change sourceRayTimeModelEquiv (b.val.symm z).val = sourceRayTimeModelEquiv z
  rw [hsymm z hz]

/-- Genuine continuity of that SAME original complex coordinate. -/
theorem sourceComplexOpenTime_continuous (U : Opens (ComplexModel 1)) :
    Continuous (sourceComplexOpenTime U) :=
  sourceRayTimeModelEquiv.continuous.comp continuous_subtype_val

/-- The actual slit-plane neighborhood of an actual center. -/
def sourceLogBranchDomain (U : Opens (ComplexModel 1)) (z₀ : U) : Set U :=
  {z | sourceComplexOpenTime U z / sourceComplexOpenTime U z₀ ∈ Complex.slitPlane}

/-- The local branch domain is genuinely open in the actual time manifold. -/
theorem sourceLogBranchDomain_isOpen (U : Opens (ComplexModel 1)) (z₀ : U) :
    IsOpen (sourceLogBranchDomain U z₀) :=
  Complex.isOpen_slitPlane.preimage ((sourceComplexOpenTime_continuous U).div_const _)

/-- A genuine LOCAL logarithm, used holomorphically ONLY on its proved slit
neighborhood. The constant principal-log term is a finite fixed number. -/
def sourceLogBranch (U : Opens (ComplexModel 1)) (z₀ z : U) : ℂ :=
  Complex.log (sourceComplexOpenTime U z / sourceComplexOpenTime U z₀) +
    Complex.log (sourceComplexOpenTime U z₀)

/-- Actual exponential identity for the LOCAL branch, including its genuine
nonzero-center and actual slit-domain hypotheses. -/
theorem sourceLogBranch_exp (U : Opens (ComplexModel 1)) (z₀ : U)
    (h₀ : sourceComplexOpenTime U z₀ ≠ 0) (z : U) (hz : z ∈ sourceLogBranchDomain U z₀) :
    Complex.exp (sourceLogBranch U z₀ z) = sourceComplexOpenTime U z := by
  have hquot : sourceComplexOpenTime U z / sourceComplexOpenTime U z₀ ≠ 0 :=
    Complex.slitPlane_ne_zero hz
  rw [sourceLogBranch, Complex.exp_add, Complex.exp_log hquot, Complex.exp_log h₀]
  exact div_mul_cancel₀ _ h₀

/-- The branch real part is EXACTLY the actual logarithmic modulus, by its
actual exponential identity. No potential readback or global branch. -/
theorem sourceLogBranch_re (U : Opens (ComplexModel 1)) (z₀ : U)
    (h₀ : sourceComplexOpenTime U z₀ ≠ 0) (z : U) (hz : z ∈ sourceLogBranchDomain U z₀) :
    (sourceLogBranch U z₀ z).re = Real.log ‖sourceComplexOpenTime U z‖ := by
  have hh := congrArg (fun w : ℂ ↦ Real.log ‖w‖) (sourceLogBranch_exp U z₀ h₀ z hz)
  simpa only [Complex.norm_exp, Real.log_exp] using hh

/-- GENUINE holomorphicity in EVERY original chart on the actual local slit
neighborhood. No holomorphicity of global principal log is assumed. -/
theorem sourceLogBranch_chart_holomorphic (U : Opens (ComplexModel 1)) (z₀ : U)
    (b : ComplexChart 1 U) :
    DifferentiableOn ℂ (sourceLogBranch U z₀ ∘ b.val.symm)
      (b.val.target ∩ b.val.symm ⁻¹' sourceLogBranchDomain U z₀) := by
  have htime := ((sourceComplexOpenTime_chart_holomorphic U z₀ b).mul_const
    (sourceComplexOpenTime U z₀)⁻¹).mono
      (inter_subset_left (t := b.val.symm ⁻¹' sourceLogBranchDomain U z₀))
  have hquot : DifferentiableOn ℂ
      (fun z ↦ sourceComplexOpenTime U (b.val.symm z) / sourceComplexOpenTime U z₀)
      (b.val.target ∩ b.val.symm ⁻¹' sourceLogBranchDomain U z₀) := by
    simpa only [Function.comp_def, div_eq_mul_inv] using htime
  exact (hquot.clog (fun _ hz ↦ hz.2)).add_const _

/-- The LITERAL original annulus exp(-1)<|w|<1. -/
def sourceLogStripTime : Opens (ComplexModel 1) :=
  ⟨{z | Real.exp (-1) < ‖sourceRayTimeModelEquiv z‖ ∧ ‖sourceRayTimeModelEquiv z‖ < 1},
    (isOpen_lt continuous_const sourceRayTimeModelEquiv.continuous.norm).inter
      (isOpen_lt sourceRayTimeModelEquiv.continuous.norm continuous_const)⟩

/-- The LITERAL original punctured unit disc 0<|w|<1. -/
def sourceLogRayTime : Opens (ComplexModel 1) :=
  ⟨{z | 0 < ‖sourceRayTimeModelEquiv z‖ ∧ ‖sourceRayTimeModelEquiv z‖ < 1},
    (isOpen_lt continuous_const sourceRayTimeModelEquiv.continuous.norm).inter
      (isOpen_lt sourceRayTimeModelEquiv.continuous.norm continuous_const)⟩

/-- EVERY original annular index has genuine nonzero coordinate and actual
logarithmic time STRICTLY inside the original interval. -/
theorem sourceLogStripTime_mem (z : sourceLogStripTime) :
    sourceComplexOpenTime sourceLogStripTime z ≠ 0 ∧
      -Real.log ‖sourceComplexOpenTime sourceLogStripTime z‖ ∈ Ioo (0 : ℝ) 1 := by
  have hp : 0 < ‖sourceComplexOpenTime sourceLogStripTime z‖ :=
    (Real.exp_pos (-1)).trans z.property.1
  have hlo := Real.log_lt_log (Real.exp_pos (-1)) z.property.1
  have hhi := Real.log_lt_log hp z.property.2
  rw [Real.log_exp] at hlo
  rw [Real.log_one] at hhi
  change -1 < Real.log ‖sourceComplexOpenTime sourceLogStripTime z‖ at hlo
  exact ⟨norm_pos_iff.mp hp, by constructor <;> linarith⟩

/-- EVERY original punctured-disc index has genuine nonzero coordinate and
STRICTLY positive original logarithmic ray time. -/
theorem sourceLogRayTime_pos (z : sourceLogRayTime) :
    sourceComplexOpenTime sourceLogRayTime z ≠ 0 ∧
      0 < -Real.log ‖sourceComplexOpenTime sourceLogRayTime z‖ := by
  have hhi := Real.log_lt_log z.property.1 z.property.2
  rw [Real.log_one] at hhi
  change Real.log ‖sourceComplexOpenTime sourceLogRayTime z‖ < 0 at hhi
  exact ⟨norm_pos_iff.mp z.property.1, by linarith⟩

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- ENTIRE original first-projection pullback on ANY actual open complex
time domain, retaining every original smooth/closed/type/tensor field. -/
def sourceLogProductBackground (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (U : Opens (ComplexModel 1)) : AtlasClosedRealOneOneForm (ofFixedModel (n + 1) (M × U)) :=
  nativeClosedFormToAtlas (ClosedRealOneOneForm.pullback
    (ProductComplexManifold.contMDiff_fst (n := n) (m := 1)) (atlasClosedFormToNative θ))

/-- The LITERAL original annular complexification, with its ACTUAL original
interior-time value at EVERY original product point. -/
def sourceAnnularComplexification (curve : ℝ → M → EReal)
    (p : M × sourceLogStripTime) : EReal :=
  curve (-Real.log ‖sourceComplexOpenTime sourceLogStripTime p.2‖) p.1

/-- The LITERAL original punctured-disc ray complexification, read DIRECTLY
on the original positive/nonnegative ray subtype without an off-time value. -/
def sourcePuncturedRayComplexification (ℓ : SourceRayFamily M)
    (p : M × sourceLogRayTime) : EReal :=
  ℓ ⟨-Real.log ‖sourceComplexOpenTime sourceLogRayTime p.2‖, by
    change 0 ≤ -Real.log ‖sourceComplexOpenTime sourceLogRayTime p.2‖
    exact (sourceLogRayTime_pos p.2).2.le⟩ p.1

/-- The actual original exponential map from the strip to the literal
annulus. It is not claimed to be a homeomorphism. -/
def sourceStripAnnulusExp (z : sourceRayTimeStrip) : sourceLogStripTime :=
  ⟨sourceRayTimeModelEquiv.symm (Complex.exp (-sourceRayTime z)), by
    change Real.exp (-1) < ‖sourceRayTimeModelEquiv
      (sourceRayTimeModelEquiv.symm (Complex.exp (-sourceRayTime z)))‖ ∧
        ‖sourceRayTimeModelEquiv (sourceRayTimeModelEquiv.symm (Complex.exp (-sourceRayTime z)))‖ < 1
    rw [ContinuousLinearEquiv.apply_symm_apply, Complex.norm_exp, Complex.neg_re]
    constructor
    · exact Real.exp_lt_exp.mpr (neg_lt_neg z.property.2)
    · calc
        Real.exp (-(sourceRayTime z).re) < Real.exp 0 := Real.exp_lt_exp.mpr (neg_neg_of_pos z.property.1)
        _ = 1 := Real.exp_zero⟩

/-- The actual original exponential map from the half-plane to the literal
punctured disc, with both strict original modulus bounds. -/
def sourceHalfPlaneDiskExp (z : sourceSubgeodesicRayTimeHalfPlane) : sourceLogRayTime :=
  ⟨sourceRayTimeModelEquiv.symm (Complex.exp (-sourceSubgeodesicRayTime z)), by
    change 0 < ‖sourceRayTimeModelEquiv
      (sourceRayTimeModelEquiv.symm (Complex.exp (-sourceSubgeodesicRayTime z)))‖ ∧
        ‖sourceRayTimeModelEquiv (sourceRayTimeModelEquiv.symm (Complex.exp (-sourceSubgeodesicRayTime z)))‖ < 1
    rw [ContinuousLinearEquiv.apply_symm_apply, Complex.norm_exp, Complex.neg_re]
    refine ⟨Real.exp_pos _, ?_⟩
    calc
      Real.exp (-(sourceSubgeodesicRayTime z).re) < Real.exp 0 :=
        Real.exp_lt_exp.mpr (neg_neg_of_pos z.property)
      _ = 1 := Real.exp_zero⟩

/-- Actual surjectivity onto the WHOLE literal annulus. Principal log
selects only a pointwise preimage; no global holomorphic selection. -/
theorem sourceStripAnnulusExp_surjective : Function.Surjective sourceStripAnnulusExp := by
  intro w
  let τ : ℂ := -Complex.log (sourceComplexOpenTime sourceLogStripTime w)
  let z : sourceRayTimeStrip := ⟨sourceRayTimeModelEquiv.symm τ, by
    change (sourceRayTimeModelEquiv (sourceRayTimeModelEquiv.symm τ)).re ∈ Ioo (0 : ℝ) 1
    rw [ContinuousLinearEquiv.apply_symm_apply]
    simpa only [τ, Complex.neg_re, Complex.log_re] using (sourceLogStripTime_mem w).2⟩
  refine ⟨z, Subtype.ext ?_⟩
  apply sourceRayTimeModelEquiv.injective
  change sourceRayTimeModelEquiv
    (sourceRayTimeModelEquiv.symm (Complex.exp (-sourceRayTime z))) = sourceRayTimeModelEquiv w.val
  rw [ContinuousLinearEquiv.apply_symm_apply]
  change Complex.exp (-sourceRayTimeModelEquiv (sourceRayTimeModelEquiv.symm τ)) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  simp only [τ, neg_neg]
  exact Complex.exp_log (sourceLogStripTime_mem w).1

/-- Actual surjectivity onto the WHOLE literal punctured unit disc. -/
theorem sourceHalfPlaneDiskExp_surjective : Function.Surjective sourceHalfPlaneDiskExp := by
  intro w
  let τ : ℂ := -Complex.log (sourceComplexOpenTime sourceLogRayTime w)
  let z : sourceSubgeodesicRayTimeHalfPlane := ⟨sourceRayTimeModelEquiv.symm τ, by
    change 0 < (sourceRayTimeModelEquiv (sourceRayTimeModelEquiv.symm τ)).re
    rw [ContinuousLinearEquiv.apply_symm_apply]
    simpa only [τ, Complex.neg_re, Complex.log_re] using (sourceLogRayTime_pos w).2⟩
  refine ⟨z, Subtype.ext ?_⟩
  apply sourceRayTimeModelEquiv.injective
  change sourceRayTimeModelEquiv
    (sourceRayTimeModelEquiv.symm (Complex.exp (-sourceSubgeodesicRayTime z))) = sourceRayTimeModelEquiv w.val
  rw [ContinuousLinearEquiv.apply_symm_apply]
  change Complex.exp (-sourceRayTimeModelEquiv (sourceRayTimeModelEquiv.symm τ)) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  simp only [τ, neg_neg]
  exact Complex.exp_log (sourceLogRayTime_pos w).1

omit [TopologicalSpace M] in
/-- EXACT source annular/strip potential readback at EVERY original point,
including every extended pole; no AE or real-valued replacement. -/
theorem sourceAnnularComplexification_pullback_exp (curve : ℝ → M → EReal)
    (x : M) (z : sourceRayTimeStrip) :
    sourceAnnularComplexification curve (x, sourceStripAnnulusExp z) = curve (sourceRayTime z).re x := by
  change curve (-Real.log ‖sourceRayTimeModelEquiv
    (sourceRayTimeModelEquiv.symm (Complex.exp (-sourceRayTime z)))‖) x = _
  rw [ContinuousLinearEquiv.apply_symm_apply, Complex.norm_exp, Complex.neg_re, Real.log_exp, neg_neg]

omit [TopologicalSpace M] in
/-- EXACT source punctured-disc/half-plane potential readback at EVERY
original point. The original positive ray index is retained literally. -/
theorem sourcePuncturedRayComplexification_pullback_exp (ℓ : SourceRayFamily M)
    (x : M) (z : sourceSubgeodesicRayTimeHalfPlane) :
    sourcePuncturedRayComplexification ℓ (x, sourceHalfPlaneDiskExp z) =
      sourceSubgeodesicRayComplexification ℓ (x, z) := by
  have ht : -Real.log ‖sourceComplexOpenTime sourceLogRayTime (sourceHalfPlaneDiskExp z)‖ =
      (sourceSubgeodesicRayTime z).re := by
    change -Real.log ‖sourceRayTimeModelEquiv
      (sourceRayTimeModelEquiv.symm (Complex.exp (-sourceSubgeodesicRayTime z)))‖ = _
    rw [ContinuousLinearEquiv.apply_symm_apply, Complex.norm_exp, Complex.neg_re, Real.log_exp, neg_neg]
  rw [sourceSubgeodesicRayComplexification_read]
  exact congrArg (fun t : Ici (0 : ℝ) ↦ ℓ t x) (Subtype.ext ht)

private theorem annular_locallyNondegenerate
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {curve : ℝ → M → EReal}
    (h : SourceSubgeodesicInterior θ curve) :
    LocallyNondegenerate (sourceAnnularComplexification curve) := by
  intro p O hO hp
  let V : Set M := (fun x : M ↦ (x, p.2)) ⁻¹' O
  have hV : IsOpen V := hO.preimage (continuous_id.prodMk continuous_const)
  have hslice := (isThetaPSH_iff_nativeThetaPotential θ _).mp
    (h.1 _ (sourceLogStripTime_mem p.2).2)
  obtain ⟨y, hy, hny⟩ := hslice.2 p.1 V hV hp
  exact ⟨(y, p.2), hy, hny⟩

private theorem annular_thetaPlurisubharmonic
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {curve : ℝ → M → EReal}
    (h : SourceSubgeodesicInterior θ curve) :
    ThetaPlurisubharmonic
      (SmoothRealForm.pullback
        (ProductComplexManifold.contMDiff_fst (n := n) (m := 1)
          (X := M) (Y := sourceLogStripTime))
        (atlasClosedFormToNative θ).val)
      (sourceAnnularComplexification curve) := by
  intro e z hz
  let p := e.val.symm z
  let V : Set sourceLogStripTime := sourceLogBranchDomain sourceLogStripTime p.2
  have hV : IsOpen V := sourceLogBranchDomain_isOpen _ _
  have hpV : p.2 ∈ V := by
    change sourceComplexOpenTime sourceLogStripTime p.2 /
      sourceComplexOpenTime sourceLogStripTime p.2 ∈ Complex.slitPlane
    rw [div_self (sourceLogStripTime_mem p.2).1]
    exact Complex.one_mem_slitPlane
  let τ : sourceLogStripTime → ℂ := fun y ↦ -sourceLogBranch sourceLogStripTime p.2 y
  have hτ (c : ComplexChart 1 sourceLogStripTime) :
      DifferentiableOn ℂ (τ ∘ c.val.symm) (c.val.target ∩ c.val.symm ⁻¹' V) :=
    (sourceLogBranch_chart_holomorphic _ p.2 c).neg
  have hre (y : sourceLogStripTime) (hy : y ∈ V) :
      (τ y).re = -Real.log ‖sourceComplexOpenTime sourceLogStripTime y‖ := by
    change -(sourceLogBranch sourceLogStripTime p.2 y).re = _
    rw [sourceLogBranch_re _ _ (sourceLogStripTime_mem p.2).1 y hy]
  have htime (y : sourceLogStripTime) (hy : y ∈ V) : (τ y).re ∈ Ioo (0 : ℝ) 1 := by
    rw [hre y hy]
    exact (sourceLogStripTime_mem y).2
  have hlocal := SingularSubgeodesicProductLocalPsh.thetaPlurisubharmonicOn_product_time_pullback
    ((sourceInterior_iff_native θ curve).mp h) hV hτ htime
  have heq : EqOn (fun q : M × sourceLogStripTime ↦ curve (τ q.2).re q.1)
      (sourceAnnularComplexification curve) (univ ×ˢ V) := by
    intro q hq
    change curve (τ q.2).re q.1 = curve (-Real.log ‖sourceComplexOpenTime sourceLogStripTime q.2‖) q.1
    rw [hre q.2 hq.2]
  have hactual := OpensRestriction.thetaPlurisubharmonicOn_congr
    (isOpen_univ.prod hV) hlocal heq
  exact hactual e z hz ⟨mem_univ _, hpV⟩

variable [MeasurableSpace M] [CompactSpace M]

/-- WHOLE original annular convention: the SAME literal complexification
is full first-projection source theta-PSH on the ENTIRE actual annulus.
Local log branches and same-time slice nondegeneracy are manufactured. -/
theorem sourceAnnularComplexification_thetaPSH
    {omega : KahlerBackground n M}
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    {curve : ℝ → M → EReal} {u₀ u₁ : M → EReal}
    (h : SourceSubgeodesicFrom omega θ curve u₀ u₁) :
    (ofFixedModel (n + 1) (M × sourceLogStripTime)).IsThetaPSH
      (sourceLogProductBackground θ sourceLogStripTime) (sourceAnnularComplexification curve) := by
  apply (isThetaPSH_iff_nativeThetaPotential (sourceLogProductBackground θ sourceLogStripTime) _).mpr
  exact ⟨annular_thetaPlurisubharmonic h.2.2.1, annular_locallyNondegenerate h.2.2.1⟩

private theorem puncturedRay_locallyNondegenerate
    {omega : KahlerBackground n M}
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {ℓ : SourceRayFamily M}
    (h : SourceIsSubgeodesicRay omega θ ℓ) :
    LocallyNondegenerate (sourcePuncturedRayComplexification ℓ) := by
  intro p O hO hp
  let V : Set M := (fun x : M ↦ (x, p.2)) ⁻¹' O
  have hV : IsOpen V := hO.preimage (continuous_id.prodMk continuous_const)
  let t : Ici (0 : ℝ) := ⟨-Real.log ‖sourceComplexOpenTime sourceLogRayTime p.2‖,
    (sourceLogRayTime_pos p.2).2.le⟩
  have hslice := (isThetaPSH_iff_nativeThetaPotential θ (ℓ t)).mp (h.thetaPSH t)
  obtain ⟨y, hy, hny⟩ := hslice.2 p.1 V hV hp
  exact ⟨(y, p.2), hy, hny⟩

variable [BorelSpace M]

private theorem puncturedRay_thetaPlurisubharmonic
    {omega : KahlerBackground n M}
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {ℓ : SourceRayFamily M}
    (h : SourceIsSubgeodesicRay omega θ ℓ) :
    ThetaPlurisubharmonic
      (SmoothRealForm.pullback
        (ProductComplexManifold.contMDiff_fst (n := n) (m := 1)
          (X := M) (Y := sourceLogRayTime))
        (atlasClosedFormToNative θ).val)
      (sourcePuncturedRayComplexification ℓ) := by
  intro e z hz
  let p := e.val.symm z
  let s₀ : ℝ := -Real.log ‖sourceComplexOpenTime sourceLogRayTime p.2‖
  let b : ℝ := 2 * s₀ + 1
  have hp : 0 < s₀ := (sourceLogRayTime_pos p.2).2
  have hb : 0 < b := by dsimp [b]; linarith
  have hpb : s₀ < b := by dsimp [b]; linarith
  have hn := (sourceSubgeodesicFrom_iff_native omega θ _ _ _).mp
    (h 0 b le_rfl hb.le).2
  have hstrip : IsSubgeodesicInterior (atlasClosedFormToNative θ).val
      (fun s ↦ sourceRayExtension ℓ (s * b)) := by
    simpa only [mul_zero, add_zero] using hn.interior
  let V : Set sourceLogRayTime := sourceLogBranchDomain sourceLogRayTime p.2 ∩
    {y | Real.exp (-b) < ‖sourceComplexOpenTime sourceLogRayTime y‖}
  have hV : IsOpen V := (sourceLogBranchDomain_isOpen _ _).inter
    (isOpen_lt continuous_const (sourceComplexOpenTime_continuous _).norm)
  have hpV : p.2 ∈ V := by
    constructor
    · change sourceComplexOpenTime sourceLogRayTime p.2 /
        sourceComplexOpenTime sourceLogRayTime p.2 ∈ Complex.slitPlane
      rw [div_self (sourceLogRayTime_pos p.2).1]
      exact Complex.one_mem_slitPlane
    · calc
        Real.exp (-b) < Real.exp (Real.log ‖sourceComplexOpenTime sourceLogRayTime p.2‖) :=
          Real.exp_lt_exp.mpr (by dsimp [s₀] at hpb; linarith)
        _ = ‖sourceComplexOpenTime sourceLogRayTime p.2‖ := Real.exp_log p.2.property.1
  let τ : sourceLogRayTime → ℂ :=
    fun y ↦ ((b⁻¹ : ℝ) : ℂ) * (-sourceLogBranch sourceLogRayTime p.2 y)
  have hτ (c : ComplexChart 1 sourceLogRayTime) :
      DifferentiableOn ℂ (τ ∘ c.val.symm) (c.val.target ∩ c.val.symm ⁻¹' V) := by
    apply (((sourceLogBranch_chart_holomorphic _ p.2 c).neg).const_mul
      ((b⁻¹ : ℝ) : ℂ)).mono
    exact fun _ hy ↦ ⟨hy.1, hy.2.1⟩
  have hre (y : sourceLogRayTime) (hy : y ∈ V) :
      (τ y).re = b⁻¹ * (-Real.log ‖sourceComplexOpenTime sourceLogRayTime y‖) := by
    change (((b⁻¹ : ℝ) : ℂ) * (-sourceLogBranch sourceLogRayTime p.2 y)).re = _
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.neg_re, sourceLogBranch_re _ _ (sourceLogRayTime_pos p.2).1 y hy.1]
  have htime (y : sourceLogRayTime) (hy : y ∈ V) : (τ y).re ∈ Ioo (0 : ℝ) 1 := by
    have htimeUpper : -Real.log ‖sourceComplexOpenTime sourceLogRayTime y‖ < b := by
      have hh := Real.log_lt_log (Real.exp_pos (-b)) hy.2
      rw [Real.log_exp] at hh
      linarith
    rw [hre y hy]
    refine ⟨mul_pos (inv_pos.mpr hb) (sourceLogRayTime_pos y).2, ?_⟩
    simpa only [div_eq_mul_inv, mul_comm] using (div_lt_one hb).mpr htimeUpper
  have hlocal := SingularSubgeodesicProductLocalPsh.thetaPlurisubharmonicOn_product_time_pullback
    hstrip hV hτ htime
  have heq : EqOn (fun q : M × sourceLogRayTime ↦
      sourceRayExtension ℓ ((τ q.2).re * b) q.1)
      (sourcePuncturedRayComplexification ℓ) (univ ×ˢ V) := by
    intro q hq
    have hcancel : (τ q.2).re * b = -Real.log ‖sourceComplexOpenTime sourceLogRayTime q.2‖ := by
      rw [hre q.2 hq.2]
      calc
        (b⁻¹ * (-Real.log ‖sourceComplexOpenTime sourceLogRayTime q.2‖)) * b =
          (b⁻¹ * b) * (-Real.log ‖sourceComplexOpenTime sourceLogRayTime q.2‖) := by ring
        _ = -Real.log ‖sourceComplexOpenTime sourceLogRayTime q.2‖ := by
          rw [inv_mul_cancel₀ hb.ne', one_mul]
    change sourceRayExtension ℓ ((τ q.2).re * b) q.1 =
      ℓ ⟨-Real.log ‖sourceComplexOpenTime sourceLogRayTime q.2‖, _⟩ q.1
    rw [hcancel]
    exact congrFun (sourceRayExtension_nonneg ℓ _ (sourceLogRayTime_pos q.2).2.le) q.1
  have hactual := OpensRestriction.thetaPlurisubharmonicOn_congr
    (isOpen_univ.prod hV) hlocal heq
  exact hactual e z hz ⟨mem_univ _, hpV⟩

/-- WHOLE original punctured-disc convention: genuine full JOINT source
theta-PSH for the literal original ray values on EVERY punctured-disc point.
Actual finite segments and local log neighborhoods produce the conclusion. -/
theorem sourcePuncturedRayComplexification_thetaPSH
    {omega : KahlerBackground n M}
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {ℓ : SourceRayFamily M}
    (h : SourceIsSubgeodesicRay omega θ ℓ) :
    (ofFixedModel (n + 1) (M × sourceLogRayTime)).IsThetaPSH
      (sourceLogProductBackground θ sourceLogRayTime) (sourcePuncturedRayComplexification ℓ) := by
  apply (isThetaPSH_iff_nativeThetaPotential (sourceLogProductBackground θ sourceLogRayTime) _).mpr
  exact ⟨puncturedRay_thetaPlurisubharmonic h, puncturedRay_locallyNondegenerate h⟩

end SGPT.PSH.VariableComplexAtlas
