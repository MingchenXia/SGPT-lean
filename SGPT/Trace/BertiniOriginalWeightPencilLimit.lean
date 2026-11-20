import SGPT.Trace.BertiniDiscExhaustion
import SGPT.Trace.OptimalRelativeNormalCurvature
import SGPT.Trace.BertiniRelativeBasePositivity
import SGPT.Trace.BertiniCriticalFibreCorrection
import SGPT.Trace.OptimalNormalEpsilonLimit
import SGPT.Trace.BertiniRelativePencilExtension
import SGPT.Trace.BertiniRelativePencilLimit
import SGPT.Trace.OptimalSingularWeightLimit
import SGPT.Trace.BertiniSingularPencilLimit
import SGPT.Trace.BertiniRealApproximationPullback

/-!
# The SAME original qpsh data manufacture the actual pencil sharp pipeline

C and original GLOBAL X real approximants are manufactured BEFORE every
pencil/disc and auxiliary metric. Family weights are LITERAL X pullbacks.
No approximant or resulting extension output certificate is supplied.
Blueprint: work/sgpt-resume-20261114/bert-e2-original-weight/blueprint/bert-e2-original-weight.tex.
-/
set_option autoImplicit false
noncomputable section
namespace SGPT.Trace.BertiniOriginalWeightPencilLimit
open Set Filter MeasureTheory Bundle
open scoped Topology ENNReal Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Okounkov.TranscendentalRelGen
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open HermitianHolomorphicLineBundle
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace SGPT.Trace.Bertini
open SGPT.Trace.BertiniPencilFamily SGPT.Trace.BertiniNormalMetric SGPT.Trace.BertiniDiscExhaustion
open SGPT.Trace.OptimalExtensionODE SGPT.Trace.OptimalExtensionGainMass SGPT.Trace.OptimalNormalRegularization
open SGPT.Trace.TwistedL2 SGPT.Trace.OptimalNativeNormalWeight SGPT.Trace.OptimalNativeNormalDatum
open SGPT.Trace.OptimalNativeNormalBackground SGPT.Trace.OptimalNativeNormalCorrection
open SGPT.Trace.OptimalRelativeNormalCurvature SGPT.Trace.BertiniRelativeBasePositivity
open SGPT.Trace.BertiniCriticalFibreCorrection
open SGPT.Trace.OptimalNormalEpsilonLimit SGPT.Trace.BertiniRelativePencilExtension
open SGPT.Trace.BertiniRelativePencilLimit SGPT.Trace.OptimalSingularWeightLimit
open SGPT.Trace.OptimalGainCompactBounds
open SGPT.Trace.BertiniGlobalRealApproximation SGPT.Trace.BertiniRealApproximationPullback
open SGPT.Trace.BertiniSingularPencilLimit
open SubmanifoldRestrictionPositivity
open ProductComplexManifold
open scoped ProductComplexManifold

theorem original_localWeight_levi_add {n : ℕ} {X : Type} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    (B : HermitianHolomorphicLineBundle.{0, 0} n X) (hB : IsSourceSmoothHermitianMetric B)
    {u : X → ℝ} (hu : ChartSmooth (n := n) u) (c : ComplexChart n X) (e : AtlasFrame B)
    {d : ComplexModel n → ℝ} {z : ComplexModel n} (hz : z ∈ chartFrameDomain B c e)
    (hd : ContDiffAt ℝ ∞ d z) (hd0 : 0 < d z) (v : ComplexModel n) :
    leviForm (SGPT.Trace.TwistedL2.localWeight B c e d u) z v =
      leviForm (SGPT.Trace.TwistedL2.localWeight B c e d (fun _ => 0)) z v +
        leviForm (fun y => u (c.val.symm y)) z v := by
  have h0 : ChartSmooth (n := n) (fun _ : X => (0 : ℝ)) := fun _ => contDiffOn_const
  have hp := contDiffAt_original_localWeight B hB h0 c e hz hd hd0
  have hU : ContDiffAt ℝ 2 (fun y => u (c.val.symm y)) z := ((hu c).contDiffAt (c.val.open_target.mem_nhds hz.1)).of_le
    (WithTop.coe_le_coe.mpr le_top)
  have heq : SGPT.Trace.TwistedL2.localWeight B c e d u =
      SGPT.Trace.TwistedL2.localWeight B c e d (fun _ => 0) + (fun y => u (c.val.symm y)) := by
    funext y
    simp only [SGPT.Trace.TwistedL2.localWeight, Pi.add_apply]
    ring
  rw [heq, leviForm_add hp hU]

variable {m : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

theorem exists_original_qpsh_manufactured_pencil_pipeline
    (omega : KahlerBackground (m + 1) X) (φ : X → EReal)
    (hφ : IsGlobalQuasiPshPotential (n := m + 1) φ) :
    ∃ (C : ℝ) (u : ℕ → X → ℝ), 0 < C ∧ (∀ j, ChartSmooth (n := m + 1) (u j)) ∧
      (∀ x, Antitone (fun j => u j x)) ∧ (∀ j x, φ x ≤ (u j x : EReal)) ∧
      (∀ x, Tendsto (fun j => (u j x : EReal)) atTop (𝓝 (φ x))) ∧
      (∀ j, IsThetaPshPotential (C • omega.form).val (fun x => (u j x : EReal))) ∧
      ∀ (N : ℕ) (p : X → ComplexProjectiveSpace N) (i : Fin (N + 1)) (a v : ComplexModel N)
        (ρ σ δ : ℝ) (_hρ : 0 < ρ), 0 < σ → 0 < δ →
      ∀ (hp : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel N) ∞ p)
        (hsm : ∀ t : parameterDisc ρ, IsSmoothHypersurfaceMember (m + 1) p (pencilParameter i a v t.val)),
      letI := familyChartedSpace p i a v (parameterDisc ρ) hp hsm
      haveI := isComplexManifold_family p i a v (parameterDisc ρ) hp hsm
      ∀ κ : ℝ, 0 < κ →
      ∀ (B : HermitianHolomorphicLineBundle.{0, 0} (m + 1) (familyIncidence p i a v (parameterDisc ρ)))
        (μ : Measure (familyIncidence p i a v (parameterDisc ρ))),
        IsSmoothPositiveVolume (n := m + 1) μ → IsSourceSmoothHermitianMetric B →
      (∀ (c : ComplexChart (m + 1) (familyIncidence p i a v (parameterDisc ρ))) (e : AtlasFrame B)
        (d : ComplexModel (m + 1) → ℝ), IsChartDensity μ c d → ∀ z ∈ chartFrameDomain B c e,
        ∀ b : ComplexModel (m + 1), Real.pi * (C + κ) * familyXQuad p i a v (parameterDisc ρ) hp hsm omega c z b ≤
          leviForm (SGPT.Trace.TwistedL2.localWeight B c e d (fun _ => 0)) z b) →
      ∀ F : (q : familyIncidence p i a v (parameterDisc ρ)) → B.Fiber q,
        SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := m + 1) B.Fiber F univ →
      ∀ ε : ℕ → ℝ, (∀ k, 0 < ε k) → Tendsto ε atTop (𝓝 0) →
      ∀ J : ℕ → ℝ≥0∞,
      (∀ j, Tendsto (fun k => actualPreliminaryKernelEnergy B μ
        (normalizedPencilNormal p i a v (parameterDisc ρ) ρ) (fun q => u j q.val.2) (ε k) σ δ F)
          atTop (𝓝 (J j))) →
      ∀ I : ℝ≥0∞, I < ⊤ → (∀ j, J j ≤ I) →
      ∃ S : (q : familyIncidence p i a v (parameterDisc ρ)) → B.Fiber q,
        SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := m + 1) B.Fiber S univ ∧
        (∀ q, normalizedPencilNormal p i a v (parameterDisc ρ) ρ q = 0 → S q = F q) ∧
        (∫⁻ q, ENNReal.ofReal (gain (annularDensity σ δ)
          (-Real.log (nativeRadius (normalizedPencilNormal p i a v (parameterDisc ρ) ρ) q)) *
          ‖S q‖ ^ 2) * multiplierWeight 1 (φ q.val.2) ∂μ) ≤ I := by
  obtain ⟨C, u, hC, hu, hmono, hdom, hlim, hpsh⟩ := exists_original_global_qpsh_real_approximation omega φ hφ
  refine ⟨C, u, hC, hu, hmono, hdom, hlim, hpsh, ?_⟩
  intro N p i a v ρ σ δ hρ hσ hδ hp hsm
  let := familyChartedSpace p i a v (parameterDisc ρ) hp hsm
  have := isComplexManifold_family p i a v (parameterDisc ρ) hp hsm
  intro κ hκ B μ hμ hB hbase0 F hF ε hεpos hε J hJlim I hI hJbound
  have hq := contMDiff_snd.comp (contMDiff_familyInclusion p i a v (parameterDisc ρ) hp hsm)
  have hw : ∀ j, ChartSmooth (n := m + 1) (fun q : familyIncidence p i a v (parameterDisc ρ) => u j q.val.2) :=
    fun j => chartSmooth_comp hq (hu j)
  have hbase : ∀ j (c : ComplexChart (m + 1) (familyIncidence p i a v (parameterDisc ρ))) (e : AtlasFrame B)
      (d : ComplexModel (m + 1) → ℝ), IsChartDensity μ c d → ∀ z ∈ chartFrameDomain B c e,
      ∀ b : ComplexModel (m + 1), (Real.pi * κ) * familyXQuad p i a v (parameterDisc ρ) hp hsm omega c z b ≤
        leviForm (SGPT.Trace.TwistedL2.localWeight B c e d (fun q => u j q.val.2)) z b := by
    intro j c e d hd z hz b
    rw [original_localWeight_levi_add B hB (hw j) c e hz
      (hd.1.contDiffAt (c.val.open_target.mem_nhds hz.1)) (hd.2.1 z hz.1) b]
    have hlower := original_smooth_psh_pullback_levi_lower omega hq (hu j) (hpsh j) c hz.1 b
    change 0 ≤ C * familyXQuad p i a v (parameterDisc ρ) hp hsm omega c z b +
      leviForm (fun y => u j (c.val.symm y).val.2) z b / Real.pi at hlower
    have hπ := mul_nonneg Real.pi_pos.le hlower
    rw [mul_add, mul_div_cancel₀ _ Real.pi_ne_zero] at hπ
    have hraw := hbase0 c e d hd z hz b
    nlinarith
  exact exists_actual_singular_pencil_sharp_extension p i a v hρ hσ hδ (mul_pos Real.pi_pos hκ) hp hsm omega
    B μ hμ hB (fun j q => u j q.val.2) hw (fun q => hmono q.val.2)
    (fun q => φ q.val.2) (fun q => hlim q.val.2) hbase F hF ε hεpos hε J hJlim I hI hJbound

end SGPT.Trace.BertiniOriginalWeightPencilLimit
