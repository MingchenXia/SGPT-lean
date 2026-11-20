import SGPT.Trace.OptimalNormalRegularization
import SGPT.Trace.OTExt5Weight
import SGPT.Trace.BertiniPencilNormal
import SGPT.Foundations.Analysis.Pending.BergmanSupWeight

/-!
# The actual native logarithmic normal weight

Original holomorphic submersion geometry produces admissibility of the
literal logarithmic normal and actual annular optimal-weight profiles.
Blueprint: work/sgpt-resume-20261114/bert-e2-native-weight/blueprint/bert-e2-native-weight.tex.
-/
set_option autoImplicit false
noncomputable section
namespace SGPT.Trace.OptimalNativeNormalWeight
open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.Trace.OptimalNormalRegularization SGPT.Trace.OptimalExtensionODE
open SGPT.Trace.OptimalExtensionGainMass SGPT.Trace.OptimalTwistedExhaustion SGPT.Trace.TwistedL2

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- Squared norm of the SAME original native scalar normal. -/
def nativeRadius (f : X → ℂ) (x : X) : ℝ := ‖f x‖ ^ 2

/-- The original extended logarithmic norm plus a literal finite weight. -/
def normalWeight (f : X → ℂ) (k : X → ℝ) (x : X) : EReal :=
  logNormSq (f x) + (k x : EReal)

theorem differentiableOn_native_normal_chart {f : X → ℂ}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) ∞ f) (c : ComplexChart n X) :
    DifferentiableOn ℂ (fun z => f (c.val.symm z)) c.val.target := by
  simpa only [preimage_univ, inter_univ] using
    SGPT.Trace.OTExt5.differentiableOn_chart_comp isOpen_univ (hf.mdifferentiable (by simp)).mdifferentiableOn c

theorem chartSmooth_nativeRadius {f : X → ℂ}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) ∞ f) :
    ChartSmooth (n := n) (nativeRadius f) := by
  intro c z hz
  exact (contDiffAt_normalRadius c.val.open_target
    (differentiableOn_native_normal_chart hf c) hz).contDiffWithinAt

theorem chartSmooth_nativeTime {f : X → ℂ}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) ∞ f) {ε : ℝ} (hε : 0 < ε) :
    ChartSmooth (n := n) (fun x => normalTime ε (nativeRadius f x)) := by
  intro c z hz
  exact (contDiffAt_normalTime
    ((chartSmooth_nativeRadius hf c).contDiffAt (c.val.open_target.mem_nhds hz))
      hε (sq_nonneg _)).contDiffWithinAt

theorem chartSmooth_nativeCutoff {f : X → ℂ}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) ∞ f) {ε : ℝ} (hε : 0 < ε) :
    ChartSmooth (n := n) (fun x => normalCutoff ε (nativeRadius f x)) := by
  intro c z hz
  exact (contDiffAt_normalCutoff
    ((chartSmooth_nativeRadius hf c).contDiffAt (c.val.open_target.mem_nhds hz))
      hε (sq_nonneg _)).contDiffWithinAt

/-- Analytic nullity is produced from the original native submersion,
using local congruence of its ACTUAL differential. -/
theorem isLocallyAnalyticNull_native_zeroSet {f : X → ℂ}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) ∞ f)
    (hsub : ∀ x, Function.Surjective (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) f x)) :
    IsLocallyAnalyticNull (n := n) {x | f x = 0} := by
  intro x
  let c := complexChartAt (n := n) x
  refine ⟨c, c.val.target, fun z => f (c.val.symm z), mem_complexChartAt_source x,
    c.val.open_target, c.val.map_source (mem_complexChartAt_source x), subset_rfl,
    differentiableOn_native_normal_chart hf c, ?_, fun _ _ h => h⟩
  intro W hW hWo hWne
  classical
  by_contra hne
  have hzall : ∀ z ∈ W, f (c.val.symm z) = 0 := by
    intro z hz
    by_contra hnz
    exact hne ⟨z, hz, hnz⟩
  obtain ⟨z, hz⟩ := hWne
  have hzt : z ∈ c.val.target := hW hz
  let q := c.val.symm z
  have hqs : q ∈ c.val.source := c.val.map_target hzt
  have hqW : q ∈ c.val.source ∩ c.val ⁻¹' W := by
    refine ⟨hqs, ?_⟩
    change c.val (c.val.symm z) ∈ W
    rwa [c.val.right_inv hzt]
  have heq : f =ᶠ[𝓝 q] fun _ => (0 : ℂ) := by
    filter_upwards [(c.val.isOpen_inter_preimage hWo).mem_nhds hqW] with y hy
    have hh := hzall (c.val y) hy.2
    rwa [c.val.left_inv hy.1] at hh
  have hd : mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) f q = 0 := by
    rw [heq.mfderiv_eq, mfderiv_const]
    rfl
  obtain ⟨w, hw⟩ := hsub q (1 : ℂ)
  rw [hd] at hw
  change (0 : ℂ) = 1 at hw
  exact zero_ne_one hw

omit [TopologicalSpace X] in
theorem normalWeight_eq_bot_iff (f : X → ℂ) (k : X → ℝ) (x : X) :
    normalWeight f k x = ⊥ ↔ f x = 0 := by
  simp only [normalWeight, EReal.add_eq_bot_iff, EReal.coe_ne_bot, or_false, logNormSq_eq_bot_iff]

omit [TopologicalSpace X] in
theorem normalWeight_toReal {f : X → ℂ} (k : X → ℝ) {x : X} (hfx : f x ≠ 0) :
    (normalWeight f k x).toReal = Real.log (nativeRadius f x) + k x := by
  rw [normalWeight, logNormSq_of_ne_zero hfx, ← EReal.coe_add, EReal.toReal_coe]
  rfl

theorem normalWeight_quasiPlurisubharmonic {f : X → ℂ}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) ∞ f) {k : X → ℝ}
    (hk : ChartSmooth (n := n) k) :
    ManifoldQuasiPlurisubharmonic (n := n) (normalWeight f k) := by
  have hlog : ManifoldQuasiPlurisubharmonic (n := n) (fun x => logNormSq (f x)) := by
    intro c z hz
    exact (BergmanSupWeight.plurisubharmonicOn_logNormSq_comp c.val.open_target
      (differentiableOn_native_normal_chart hf c) z hz).quasiPlurisubharmonicAt
  exact hlog.add_smooth hk

theorem chartSmoothOn_normalWeight_toReal {f : X → ℂ}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) ∞ f) {k : X → ℝ}
    (hk : ChartSmooth (n := n) k) :
    SGPT.PSH.LineBundleMetric.ChartSmoothOn (n := n)
      (fun x => (normalWeight f k x).toReal) {x | normalWeight f k x ≠ ⊥} := by
  intro c z hz
  have hfx : f (c.val.symm z) ≠ 0 := fun h => hz.2 ((normalWeight_eq_bot_iff f k _).mpr h)
  have hr : 0 < nativeRadius f (c.val.symm z) := sq_pos_of_pos (norm_pos_iff.mpr hfx)
  have hR := chartSmooth_nativeRadius hf
  let O := c.val.target ∩ (fun y => nativeRadius f (c.val.symm y)) ⁻¹' Ioi 0
  have hOo : IsOpen O := (hR c).continuousOn.isOpen_inter_preimage c.val.open_target isOpen_Ioi
  have hzO : z ∈ O := ⟨hz.1, hr⟩
  have hreal : ContDiffAt ℝ ∞ (fun y => Real.log (nativeRadius f (c.val.symm y)) +
      k (c.val.symm y)) z :=
    (((hR c).contDiffAt (c.val.open_target.mem_nhds hz.1)).log hr.ne').add
      ((hk c).contDiffAt (c.val.open_target.mem_nhds hz.1))
  refine (hreal.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [hOo.mem_nhds hzO] with y hy
  have hfy : f (c.val.symm y) ≠ 0 := by
    intro h
    have hh := hy.2
    change 0 < nativeRadius f (c.val.symm y) at hh
    simp only [nativeRadius, h, norm_zero, zero_pow (by decide : 2 ≠ 0), lt_self_iff_false] at hh
  exact normalWeight_toReal k hfy

/-- No supplied pole/nullness/regularity certificate. -/
theorem isAdmissible_normalWeight {f : X → ℂ}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) ∞ f)
    (hsub : ∀ x, Function.Surjective (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) f x))
    {k : X → ℝ} (hk : ChartSmooth (n := n) k) :
    IsAdmissibleSingularWeight (n := n) (normalWeight f k) := by
  have hq := normalWeight_quasiPlurisubharmonic hf hk
  have hset : {x | normalWeight f k x = ⊥} = {x | f x = 0} :=
    Set.ext fun x => normalWeight_eq_bot_iff f k x
  refine ⟨hq, hq.ne_top, ?_, ?_, chartSmoothOn_normalWeight_toReal hf hk⟩
  · rw [hset]
    exact isClosed_eq hf.continuous continuous_const
  · rw [hset]
    exact isLocallyAnalyticNull_native_zeroSet hf hsub

theorem chartSmooth_nativeOptimalPotential {f : X → ℂ}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) ∞ f) {ε σ δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) (hR : ∀ x, nativeRadius f x < 1) :
    ChartSmooth (n := n) (fun x => potential (annularDensity σ δ) (normalTime ε (nativeRadius f x))) := by
  intro c z hz
  have ht := normalTime_pos hε (sq_nonneg ‖f (c.val.symm z)‖) (hR _)
  have hp := contDiffAt_potential (contDiff_annularDensity σ δ)
    (fun t _ => annularDensity_pos σ hδ t) ht
  exact (hp.comp z ((chartSmooth_nativeTime hf hε c).contDiffAt
    (c.val.open_target.mem_nhds hz))).contDiffWithinAt

/-- Both true twists and their finite upper sum bound are produced. -/
theorem actual_native_normal_twist_data {f : X → ℂ}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) ∞ f) {ε σ δ : ℝ}
    (hε : 0 < ε) (hσ : 0 < σ) (hδ : 0 < δ) (hR : ∀ x, nativeRadius f x < 1) :
    ChartSmooth (n := n) (fun x => twist (annularDensity σ δ) (normalTime ε (nativeRadius f x))) ∧
    ChartSmooth (n := n) (fun x => (correction (annularDensity σ δ) (normalTime ε (nativeRadius f x)))⁻¹) ∧
    (∀ x, 0 < twist (annularDensity σ δ) (normalTime ε (nativeRadius f x))) ∧
    (∀ x, 0 < (correction (annularDensity σ δ) (normalTime ε (nativeRadius f x)))⁻¹) ∧
    ∃ M : ℝ, ∀ x, twist (annularDensity σ δ) (normalTime ε (nativeRadius f x)) +
      (correction (annularDensity σ δ) (normalTime ε (nativeRadius f x)))⁻¹ ≤ M :=
  actual_native_optimal_twist_data hσ hδ (chartSmooth_nativeTime hf hε)
    (fun x => normalTime_pos hε (sq_nonneg _) (hR x))
    (fun _ => normalTime_le hε (sq_nonneg _))

theorem isAdmissible_actual_native_annular_weight {f : X → ℂ}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) ∞ f)
    (hsub : ∀ x, Function.Surjective (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) f x))
    {φ₀ : X → ℝ} (hφ : ChartSmooth (n := n) φ₀) {ε σ δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) (hR : ∀ x, nativeRadius f x < 1) :
    IsAdmissibleSingularWeight (n := n) (normalWeight f (fun x =>
      φ₀ x + potential (annularDensity σ δ) (normalTime ε (nativeRadius f x)))) :=
  isAdmissible_normalWeight hf hsub fun c =>
    (hφ c).add (chartSmooth_nativeOptimalPotential hf hε hδ hR c)

/-- The original pencil instantiates the native submersion hypothesis. -/
theorem isAdmissible_actual_pencil_weight {N : ℕ}
    (p : X → SGPT.Projective.ComplexProjectiveSpace N)
    (i : Fin (N + 1)) (a v : ComplexModel N)
    (U : TopologicalSpace.Opens (ComplexModel 1))
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p)
    (hsm : ∀ t : U, SGPT.Trace.Bertini.IsSmoothHypersurfaceMember n p
      (SGPT.Trace.BertiniPencilFamily.pencilParameter i a v t.val)) :
    letI := SGPT.Trace.BertiniPencilFamily.familyChartedSpace p i a v U hp hsm
    haveI := SGPT.Trace.BertiniPencilFamily.isComplexManifold_family p i a v U hp hsm
    ∀ k : SGPT.Trace.BertiniPencilFamily.familyIncidence p i a v U → ℝ,
      ChartSmooth (n := n) k → IsAdmissibleSingularWeight (n := n)
        (normalWeight (SGPT.Trace.BertiniPencilNormal.scalarParameter p i a v U) k) := by
  let := SGPT.Trace.BertiniPencilFamily.familyChartedSpace p i a v U hp hsm
  have := SGPT.Trace.BertiniPencilFamily.isComplexManifold_family p i a v U hp hsm
  intro k hk
  exact isAdmissible_normalWeight
    (SGPT.Trace.BertiniPencilNormal.contMDiff_scalarParameter p i a v U hp hsm)
    (SGPT.Trace.BertiniPencilNormal.surjective_mfderiv_scalarParameter p i a v U hp hsm) hk

end SGPT.Trace.OptimalNativeNormalWeight
