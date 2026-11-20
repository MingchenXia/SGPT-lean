import SGPT.PSH.BookCurrentMetrics
import SGPT.PSH.SourceAnalyticIGood
import SGPT.PSH.SourceIGoodOperations
import SGPT.Foundations.Analysis.Pending.IGoodGlobalPStability
import SGPT.Foundations.Analysis.Pending.FiniteAnalyticMaxima
import SGPT.Foundations.Analysis.Pending.QuasiEquisingularRationalScaling
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp

/-!
# The original elementary-metric I-good example

Source: SGPT `ex:eleIgood`, source commit
`69360cfdc1f1d0c0472a4e6fce1f281176ada70b`, `chapter_Igood.tex:332–336`.

The actual finite FS metric data produce local rational analytic type in every
smooth reference. Induction on the original generalized-FS metric and genuine
global P-stability prove I-goodness of every original elementary metric in all
natural dimensions, including original zero mass and every pole.

Blueprint: `elementary-metric-igood.tex`. Private kernel/type/recursive-axiom
receipts are preserved under `validation/elementary-metric-igood-20261105`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Set Filter Bundle
open scoped Topology Manifold ContDiff ENNReal TensorProduct InnerProductSpace

namespace SGPT.PSH.LineBundleMetric

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SGPT.Foundations.Analysis.Pending
open SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle

universe u v

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

private theorem atlasFrame_ne_zero
    {L : HermitianHolomorphicLineBundle.{u,v} n M} (e : AtlasFrame L)
    {x : M} (hx : x ∈ e.val.baseSet) : e.val.symm x 1 ≠ 0 := by
  intro hzero
  have hframe : (e.val (TotalSpace.mk' ℂ x (e.val.symm x 1))).2 = 1 := by
    rw [e.val.apply_mk_symm hx]
  have h0 : (e.val (TotalSpace.mk' ℂ x (0 : L.Fiber x))).2 = 0 :=
    (e.val.continuousLinearEquivAt ℂ x hx).map_zero
  rw [hzero, h0] at hframe
  exact zero_ne_one hframe

/-- The literal tensor power of an original frame is the already-constructed
actual tensor-power frame, not a supplied tensor-identification certificate. -/
theorem powVec_atlasFrame
    {L : HermitianHolomorphicLineBundle.{u,v} n M} (e : AtlasFrame L)
    {x : M} (hx : x ∈ e.val.baseSet) :
    ∀ k, powVec L k (e.val.symm x 1) = (positivePowerAtlasFrame e k).val.symm x 1
  | 0 => rfl
  | k + 1 => by
    change powVec L k (e.val.symm x 1) ⊗ₜ[ℂ] e.val.symm x 1 =
      (tensorAtlasFrame (positivePowerAtlasFrame e k) e).val.symm x 1
    rw [powVec_atlasFrame e hx k]
    simpa only [one_smul] using
      (tensorAtlasFrame_symm (positivePowerAtlasFrame e k) e
        ⟨positivePowerAtlasFrame_mem e hx k, hx⟩ (1 : ℂ)).symm

private theorem atlasFrame_coeff_smul
    {L : HermitianHolomorphicLineBundle.{u,v} n M} (e : AtlasFrame L)
    {x : M} (hx : x ∈ e.val.baseSet) (w : L.Fiber x) :
    w = (e.val (TotalSpace.mk' ℂ x w)).2 • e.val.symm x 1 := by
  have hsmul (c : ℂ) : e.val.symm x c = c • e.val.symm x 1 := by
    rw [← e.val.symmL_apply (R := ℂ) hx c,
      ← e.val.symmL_apply (R := ℂ) hx 1, ← map_smul, smul_eq_mul, mul_one]
  conv_lhs => rw [← e.val.symm_apply_apply_mk hx w]
  rw [hsmul]

/-- Every original section coefficient is read in the original constructed
positive-power frame, at every point of its true frame domain. -/
theorem section_eq_coeff_smul_powVec
    {L : HermitianHolomorphicLineBundle.{u,v} n M} (e : AtlasFrame L)
    {x : M} (hx : x ∈ e.val.baseSet) (k : ℕ)
    (w : (positivePower L k).Fiber x) :
    w = ((positivePowerAtlasFrame e k).val (TotalSpace.mk' ℂ x w)).2 •
      powVec L k (e.val.symm x 1) := by
  rw [powVec_atlasFrame e hx k]
  exact atlasFrame_coeff_smul (positivePowerAtlasFrame e k)
    (positivePowerAtlasFrame_mem e hx k) w

/-- The original inner-product quotient is exactly the coefficient in the
same power-frame vector, including a zero section coefficient. -/
theorem inner_ratio_eq_coefficient
    {L : HermitianHolomorphicLineBundle.{u,v} n M} (e : AtlasFrame L)
    {x : M} (hx : x ∈ e.val.baseSet) (k : ℕ)
    (w : (positivePower L k).Fiber x) :
    ⟪powVec L k (e.val.symm x 1), w⟫_ℂ /
        ((‖powVec L k (e.val.symm x 1)‖ : ℂ) ^ 2) =
      ((positivePowerAtlasFrame e k).val (TotalSpace.mk' ℂ x w)).2 := by
  have hv : powVec L k (e.val.symm x 1) ≠ 0 := by
    rw [powVec_atlasFrame e hx k]
    exact atlasFrame_ne_zero (positivePowerAtlasFrame e k)
      (positivePowerAtlasFrame_mem e hx k)
  have hd : ((‖powVec L k (e.val.symm x 1)‖ : ℂ) ^ 2) ≠ 0 :=
    pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hv))
  conv_lhs => rw [section_eq_coeff_smul_powVec e hx k w]
  rw [inner_smul_right, inner_self_eq_norm_sq_to_K]
  exact mul_div_cancel_right₀ _ hd

/-- Extended logarithms read the literal original FS term. The coefficient-zero
branch remains a pole; no nonvanishing-section hypothesis is added. -/
theorem neg_log_fsTerm_atlasFrame
    {L : HermitianHolomorphicLineBundle.{u,v} n M} (e : AtlasFrame L)
    {x : M} (hx : x ∈ e.val.baseSet) (k : ℕ)
    (w : (positivePower L k).Fiber x) (lam : ℚ) :
    -ENNReal.log (fsTerm L k w lam (e.val.symm x 1)) =
      (((1 : ℝ) / (k + 1) : ℝ) : EReal) *
        (ENNReal.log (ENNReal.ofReal
          (‖((positivePowerAtlasFrame e k).val (TotalSpace.mk' ℂ x w)).2‖ ^ 2)) +
          ((lam : ℝ) : EReal)) := by
  rw [fsTerm, inner_ratio_eq_coefficient e hx k w, ENNReal.log_rpow]
  simp only [div_eq_mul_inv]
  rw [ENNReal.log_mul_add, ENNReal.log_inv,
    ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp]
  let c : ℂ := ((positivePowerAtlasFrame e k).val (TotalSpace.mk' ℂ x w)).2
  have hr : 0 < (1 : ℝ) / (k + 1) := by positivity
  by_cases hc : c = 0
  · dsimp only [c] at hc
    simp only [hc, norm_zero, zero_pow (by omega : (2 : ℕ) ≠ 0),
      ENNReal.ofReal_zero, ENNReal.log_zero, EReal.neg_bot,
      EReal.coe_add_top, EReal.bot_add]
    have hr' : 0 < (1 : ℝ) * ((k : ℝ) + 1)⁻¹ := by positivity
    rw [EReal.coe_mul_top_of_pos hr', EReal.neg_top, EReal.coe_mul_bot_of_pos hr']
  · have hpos : 0 < ‖c‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hc)
    rw [show ENNReal.log (ENNReal.ofReal
      (‖((positivePowerAtlasFrame e k).val (TotalSpace.mk' ℂ x w)).2‖ ^ 2)) =
        (Real.log (‖c‖ ^ 2) : EReal) from ENNReal.log_ofReal_of_pos hpos]
    norm_cast
    simp only [Rat.cast_neg]
    ring

private theorem neg_log_iInf {N : ℕ} (f : Fin N → ℝ≥0∞) :
    -ENNReal.log (⨅ i, f i) = ⨆ i, -ENNReal.log (f i) := by
  have hlog : ENNReal.log (⨅ i, f i) = ⨅ i, ENNReal.log (f i) :=
    ENNReal.logOrderIso.map_iInf f
  rw [hlog]
  exact EReal.negOrderIso.map_iInf (fun i => ENNReal.log (f i))

private theorem neg_log_twistedForm
    {L : HermitianHolomorphicLineBundle.{u,v} n M}
    (h₀ : HermitianMetric (n := n) L.Fiber) (φ : M → EReal)
    (x : M) (w : L.Fiber x) (hw : w ≠ 0) :
    -ENNReal.log (twistedForm h₀ φ x w) =
      φ x + ((-Real.log ((h₀.form x).normSq w) : ℝ) : EReal) := by
  rw [twistedForm, if_neg hw, ENNReal.log_mul_add,
    ENNReal.log_ofReal_of_pos ((h₀.form x).normSq_pos hw), EReal.log_exp,
    EReal.neg_add (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))]
  simp only [sub_eq_add_neg, neg_neg, ← EReal.coe_neg, add_comm]

private theorem atlasFrame_holomorphic
    {L : HermitianHolomorphicLineBundle.{u,v} n M} (e : AtlasFrame L) :
    IsHolomorphicSectionOn (n := n) L.Fiber
      (fun x => e.val.symm x 1) e.val.baseSet := by
  let := e.property
  rw [IsHolomorphicSectionOn, e.val.mdifferentiableOn_section_baseSet_iff]
  apply (mdifferentiableOn_const (c := (1 : ℂ))).congr
  intro x hx
  rw [e.val.apply_mk_symm hx]

private theorem powerCoefficient_differentiableOn
    {L : HermitianHolomorphicLineBundle.{u,v} n M} (e : AtlasFrame L)
    (k : ℕ)
    (s : SGPT.Bergman.QuantizationDraft.HolomorphicSections (n := n)
      (positivePower L k).Fiber) (c : ComplexChart n M) :
    DifferentiableOn ℂ
      (fun y => ((positivePowerAtlasFrame e k).val
        (TotalSpace.mk' ℂ (c.val.symm y) (s (c.val.symm y)))).2)
      (c.val.target ∩ c.val.symm ⁻¹' e.val.baseSet) := by
  let E := positivePowerAtlasFrame e k
  let := E.property
  intro y hy
  have hbase : c.val.symm y ∈ E.val.baseSet := positivePowerAtlasFrame_mem e hy.2 k
  have hcoeff : ContMDiffAt (𝓘(ℂ, ComplexModel n)) (𝓘(ℂ, ℂ)) ∞
      (fun x => (E.val (TotalSpace.mk' ℂ x (s x))).2) (c.val.symm y) :=
    (E.val.contMDiffAt_section_iff hbase).mp (s.contMDiff (c.val.symm y))
  exact (differentiableAt_comp_chart_symm c hy.1
    (hcoeff.mdifferentiableAt (by simp))).differentiableWithinAt

/-- The actual original FS sections, tensor degree and rational weights
internally produce analytic type for the SAME potential in ANY given smooth
reference. No logarithmic presentation is a hypothesis. -/
theorem IsFubiniStudyMetric.hasManifoldAnalyticType
    (L : HermitianHolomorphicLineBundle.{u,v} n M)
    {q : (x : M) → L.Fiber x → ℝ≥0∞}
    (hq : IsFubiniStudyMetric L q)
    {h₀ : HermitianMetric (n := n) L.Fiber}
    {φ : M → EReal} (hφ : IsPSHMetricWith q h₀ φ) :
    HasManifoldAnalyticSingularityType (n := n) φ := by
  obtain ⟨_, k, N, hN, s, lam, hFS⟩ := hq
  cases N with
  | zero => omega
  | succ N =>
    intro c z hz
    let p : M := c.val.symm z
    let e : AtlasFrame L := ⟨trivializationAt ℂ L.Fiber p, inferInstance⟩
    let S : Set (ComplexModel n) := c.val.target ∩ c.val.symm ⁻¹' e.val.baseSet
    have hS : IsOpen S := c.val.isOpen_inter_preimage_symm e.val.open_baseSet
    have hzS : z ∈ S := ⟨hz, mem_baseSet_trivializationAt ℂ L.Fiber p⟩
    let f : Fin (N + 1) → ComplexModel n → ℂ := fun i y =>
      ((positivePowerAtlasFrame e k).val
        (TotalSpace.mk' ℂ (c.val.symm y) (s i (c.val.symm y)))).2
    let r : ℚ := 1 / (k + 1 : ℚ)
    have hr : (0 : ℝ) < (r : ℝ) := by dsimp only [r]; positivity
    have hrEq : (r : ℝ) = (1 : ℝ) / (k + 1) := by dsimp only [r]; push_cast; rfl
    let a : Fin (N + 1) → ComplexModel n → EReal := fun i y =>
      ((r : ℝ) : EReal) *
        (ENNReal.log (ENNReal.ofReal (‖f i y‖ ^ 2)) + ((lam i : ℝ) : EReal))
    have ha : ∀ i, ∃ P : ℕ, ∃ g : Fin P → ComplexModel n → ℂ,
        LogarithmicTypeAt (a i) (r : ℝ) g z := by
      intro i
      refine ⟨1, fun _ => f i, hr, ?_, fun _ => (r : ℝ) * (lam i : ℝ), ?_, ?_⟩
      · exact ⟨S, hS, hzS, fun _ => powerCoefficient_differentiableOn e k (s i) c⟩
      · exact ⟨|(r : ℝ) * (lam i : ℝ)|, abs_nonneg _,
          Eventually.of_forall fun _ => le_rfl⟩
      · apply Eventually.of_forall
        intro y
        simp only [a, generatorLog_eq_log_sum, Fin.sum_univ_one]
        rw [EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr hr.le)
          (EReal.coe_ne_top _), ← EReal.coe_mul]
    have hsup : HasAnalyticSingularityTypeAt (fun y => ⨆ i, a i y) z :=
      DemaillyAnalyticType.hasAnalyticSingularityTypeAt_fin_iSup_of_same_coefficient a ha
    let b : ComplexModel n → ℝ := fun y =>
      -localWeight h₀ (fun x => e.val.symm x 1) c y
    have hb : BoundedRealGermAt b z := by
      apply boundedRealGermAt_of_continuousAt
      exact (((chartSmooth_localWeight h₀ e.val.open_baseSet (atlasFrame_holomorphic e)
        (fun x hx => atlasFrame_ne_zero e hx) c).contDiffAt (hS.mem_nhds hzS)).continuousAt).neg
    apply DemaillyAnalyticType.HasAnalyticSingularityTypeAt.of_eventuallyEq_add_bounded hsup hb
    filter_upwards [hS.mem_nhds hzS] with y hy
    have hmetric := hFS (fun x => e.val.symm x 1) e.val.baseSet e.val.open_baseSet
      (atlasFrame_holomorphic e) (fun x hx => atlasFrame_ne_zero e hx)
      (c.val.symm y) hy.2
    have hlog := congrArg (fun t : ℝ≥0∞ => -ENNReal.log t) hmetric
    rw [hφ.eq_twisted, neg_log_twistedForm h₀ φ _ _ (atlasFrame_ne_zero e hy.2),
      neg_log_iInf] at hlog
    have hread : ∀ i, -ENNReal.log
        (fsTerm L k (s i (c.val.symm y)) (lam i) (e.val.symm (c.val.symm y) 1)) = a i y := by
      intro i
      simpa only [a, f, hrEq] using
        neg_log_fsTerm_atlasFrame e hy.2 k (s i (c.val.symm y)) (lam i)
    simp only [hread] at hlog
    change φ (c.val.symm y) = (⨆ i, a i y) + (b y : EReal)
    calc
      φ (c.val.symm y) =
          (φ (c.val.symm y) + (localWeight h₀ (fun x => e.val.symm x 1) c y : EReal)) +
            (b y : EReal) := by simp only [b, add_assoc, ← EReal.coe_add, add_neg_cancel,
              EReal.coe_zero, add_zero]
      _ = (⨆ i, a i y) + (b y : EReal) := congrArg (fun t => t + (b y : EReal)) hlog

/-- Induction on the ACTUAL original generalized-FS metric constructs its
analytic type; no finite decomposition or analytic certificate is supplied. -/
theorem IsGeneralizedFubiniStudyMetric.hasManifoldAnalyticType
    (L : HermitianHolomorphicLineBundle.{u,v} n M)
    {q : (x : M) → L.Fiber x → ℝ≥0∞}
    (hq : IsGeneralizedFubiniStudyMetric L q)
    {h₀ : HermitianMetric (n := n) L.Fiber}
    {φ : M → EReal} (hφ : IsPSHMetricWith q h₀ φ) :
    HasManifoldAnalyticSingularityType (n := n) φ := by
  induction hq generalizing h₀ φ with
  | fs hFS => exact IsFubiniStudyMetric.hasManifoldAnalyticType L hFS hφ
  | @convex q₁ q₂ t ht0 ht1 h₁ h₂ ih₁ ih₂ =>
    obtain ⟨φ₁, hp₁⟩ := (isPSHMetric_iff_exists_potential h₀ q₁).mp h₁.isPSHMetric
    obtain ⟨φ₂, hp₂⟩ := (isPSHMetric_iff_exists_potential h₀ q₂).mp h₂.isPSHMetric
    have ht0R : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht0
    have ht1R : (t : ℝ) < 1 := by exact_mod_cast ht1
    have hEq : φ = ThetaPshConvexCombination.convexComb (t : ℝ) φ₁ φ₂ := by
      apply twistedForm_injective h₀
      funext x w
      rw [← hφ.eq_twisted x w]
      rw [hp₁.eq_twisted, hp₂.eq_twisted]
      exact congrFun (congrFun (twistedForm_convex h₀
        (fun y => hp₁.thetaPsh.1.quasiPlurisubharmonic.ne_top y)
        (fun y => hp₂.thetaPsh.1.quasiPlurisubharmonic.ne_top y) ht0R ht1R) x) w
    rw [hEq]
    intro e z hz
    have hA₁ := QuasiEquisingularRationalScaling.hasAnalyticSingularityTypeAt_pos_rat_smul
      (ih₁ hp₁ e z hz) ht0
    have hA₂ := QuasiEquisingularRationalScaling.hasAnalyticSingularityTypeAt_pos_rat_smul
      (ih₂ hp₂ e z hz) (show (0 : ℚ) < 1 - t by linarith)
    change HasAnalyticSingularityTypeAt
      (fun y => ((t : ℝ) : EReal) * φ₁ (e.val.symm y) +
        ((1 - (t : ℝ) : ℝ) : EReal) * φ₂ (e.val.symm y)) z
    simpa only [FirstPass.chartFunction, Rat.cast_sub, Rat.cast_one] using
      RationalAnalyticAddition.hasAnalyticSingularityTypeAt_add hA₁ hA₂
  | @min q₁ q₂ h₁ h₂ ih₁ ih₂ =>
    obtain ⟨φ₁, hp₁⟩ := (isPSHMetric_iff_exists_potential h₀ q₁).mp h₁.isPSHMetric
    obtain ⟨φ₂, hp₂⟩ := (isPSHMetric_iff_exists_potential h₀ q₂).mp h₂.isPSHMetric
    have hEq : φ = fun x => max (φ₁ x) (φ₂ x) := by
      apply twistedForm_injective h₀
      funext x w
      rw [← hφ.eq_twisted x w]
      rw [hp₁.eq_twisted, hp₂.eq_twisted]
      exact congrFun (congrFun (twistedForm_min h₀ φ₁ φ₂) x) w
    rw [hEq]
    intro e z hz
    exact RationalAnalyticMaximum.hasAnalyticSingularityTypeAt_max
      (ih₁ hp₁ e z hz) (ih₂ hp₂ e z hz)

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

/-- WHOLE original `ex:eleIgood`: every actual original elementary metric,
read in ANY actual smooth-reference presentation, has a globally I-good
potential. Arbitrary n, original zero mass, and every pole are retained.
The original elementary witness, analytic type, positive common background
and P-transport are all consumed/produced internally. -/
theorem sourceElementaryMetric_iGood
    (omega : KahlerBackground n M)
    (L : HermitianHolomorphicLineBundle.{u,v} n M)
    {h : (x : M) → L.Fiber x → ℝ≥0∞}
    (hh : IsElementaryMetric L h)
    (h₀ : HermitianMetric (n := n) L.Fiber)
    (φ : M → EReal) (hφ : IsPSHMetricWith h h₀ φ) :
    SGPT.PSH.VariableComplexAtlas.sourceIGood (n := n) φ := by
  obtain ⟨ψ, hGFS, hψ, hP⟩ :=
    (isElementaryMetric_iff_of_reference omega L h₀ hφ).mp hh
  have hmetricψ : IsPSHMetricWith (twistedForm h₀ ψ) h₀ ψ := ⟨hψ, fun _ _ => rfl⟩
  have hanalytic : HasManifoldAnalyticSingularityType (n := n) ψ :=
    IsGeneralizedFubiniStudyMetric.hasManifoldAnalyticType L hGFS hmetricψ
  have hgoodψ : IGood (n := n) ψ :=
    AnalyticPotentialsIGood.iGood_of_globalQuasiPsh_of_analytic_type omega
      hψ.quasiPshPotential hanalytic
  obtain ⟨θ, hψθ, hφθ, hψpos, hφpos⟩ :=
    SGPT.PSH.GlobalPComparison.exists_positive_common_background_of_quasiPsh omega
      hψ.quasiPshPotential hφ.thetaPsh.quasiPshPotential
  obtain ⟨σ, hψσ, hgoodσ⟩ := hgoodψ
  have hgoodθ : IGoodWith θ ψ hψθ :=
    (IGoodPositiveBackgroundIndependence.iGoodWith_iff_positive_common_potential
      omega σ θ hψσ hψθ hgoodσ.positiveMass hψpos).mp hgoodσ
  have hgoodφ : IGoodWith θ φ hφθ :=
    IGoodGlobalPStability.iGoodWith_of_sourcePEquivalent omega hψθ hφθ hgoodθ
      ⟨hP.2, hP.1⟩
  exact (SGPT.PSH.VariableComplexAtlas.sourceIGood_iff_native φ).mpr ⟨θ, hφθ, hgoodφ⟩

end SGPT.PSH.LineBundleMetric
