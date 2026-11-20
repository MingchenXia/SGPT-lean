import SGPT.Foundations.Analysis.Pending.PshAnalyticRemovable
import SGPT.Foundations.Analysis.Pending.MeteredDivisorSmoothOffSupport
import SGPT.Foundations.Analysis.Pending.BergmanGeneratorFrameChange
import SGPT.Foundations.Analysis.FirstPass.LocalPotentialIndependence

set_option autoImplicit false

/-! # A genuine PSH residual with a merely bounded analytic remainder

The actual analytic removable-singularity construction supplies the
residual PSH function.  No smoothness of the real remainder at poles,
residual PSH certificate, or current decomposition is assumed.
-/

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace SGPT.Foundations.Analysis.Pending.ActualAnalyticFactorResidualPsh
open FirstPass PshCodimTwoExtension

variable {n N : ℕ}

/-- Any real multiple of the finite holomorphic logarithm is PSH off its zeros. -/
theorem plurisubharmonicOn_real_log_normSq_off_zeros
    {Ω : Set (ComplexModel n)} (hΩ : IsOpen Ω)
    {d : ComplexModel n → ℂ} (hd : DifferentiableOn ℂ d Ω) (a : ℝ) :
    PlurisubharmonicOn (fun x => ((a * Real.log (Complex.normSq (d x)) : ℝ) : EReal))
      (Ω \ {x | d x = 0}) := by
  have hW : IsOpen (Ω \ {x | d x = 0}) :=
    hd.continuousOn.isOpen_inter_preimage hΩ isOpen_compl_singleton
  have hlog : ContDiffOn ℝ ∞ (fun x => Real.log (Complex.normSq (d x)))
      (Ω \ {x | d x = 0}) := by
    intro x hx
    exact (MeteredDivisorSmoothOffSupport.contDiffAt_log_normSq hΩ hd hx.1 hx.2).contDiffWithinAt
  apply plurisubharmonicOn_coe_of_smoothDDC_eq_zero hW (contDiffOn_const.mul hlog)
  intro x hx
  change smoothDDC (fun y => a • Real.log (Complex.normSq (d y))) x = 0
  rw [smoothDDC_smul hW hlog a hx]
  have hdnear : ∀ᶠ y in 𝓝 x, DifferentiableAt ℂ d y := by
    filter_upwards [hΩ.mem_nhds hx.1] with y hy
    exact (hd y hy).differentiableAt (hΩ.mem_nhds hy)
  rw [PluriharmonicLogNorm.smoothDDC_log_normSq_eq_zero hdnear hx.2, smul_zero]

/-- A bounded-above analytic remainder produces the actual noncollapsed
PSH extension after removal of a holomorphic common factor. -/
theorem factorResidual_extension_psh
    {Ω : Set (ComplexModel n)} (hΩ : IsOpen Ω)
    {p : ComplexModel n → EReal} (hp : PlurisubharmonicOn p Ω)
    (hne : ∃ x ∈ Ω, p x ≠ ⊥)
    (f g : Fin N → ComplexModel n → ℂ) (d : ComplexModel n → ℂ)
    (hd : DifferentiableOn ℂ d Ω) (hg : ∀ i, DifferentiableOn ℂ (g i) Ω)
    (hfactor : ∀ x ∈ Ω, ∀ i, f i x = d x * g i x)
    {c : ℝ} (hc : 0 < c) (b : ComplexModel n → ℝ)
    (hb : ∃ B : ℝ, ∀ x ∈ Ω, b x ≤ B)
    (hrep : ∀ x ∈ Ω, p x = (c : EReal) * generatorLog f x + (b x : EReal)) :
    let ψ := fun x => p x + ((-c * Real.log (Complex.normSq (d x)) : ℝ) : EReal)
    let q := extension {x | d x = 0} ψ
    PlurisubharmonicOn q Ω ∧ (∃ x ∈ Ω, q x ≠ ⊥) ∧
      EqOn q (fun x => (c : EReal) * generatorLog g x + (b x : EReal))
        (Ω \ {x | d x = 0}) := by
  classical
  let ψ := fun x => p x + ((-c * Real.log (Complex.normSq (d x)) : ℝ) : EReal)
  let A : Set (ComplexModel n) := {x | d x = 0}
  let q := extension A ψ
  have hW : IsOpen (Ω \ A) :=
    hd.continuousOn.isOpen_inter_preimage hΩ isOpen_compl_singleton
  have hψ : PlurisubharmonicOn ψ (Ω \ A) :=
    (hp.mono sdiff_subset).add (plurisubharmonicOn_real_log_normSq_off_zeros hΩ hd (-c))
  have heq : EqOn ψ (fun x => (c : EReal) * generatorLog g x + (b x : EReal))
      (Ω \ A) := by
    intro x hx
    have hdx : d x ≠ 0 := hx.2
    have hlog : generatorLog f x = generatorLog g x +
        (Real.log (Complex.normSq (d x)) : EReal) :=
      (BergmanGeneratorFrameChange.generatorLog_congr_at (hfactor x hx.1)).trans
        (BergmanGeneratorFrameChange.generatorLog_mul_scalar (d x) hdx g x)
    dsimp only [ψ]
    rw [hrep x hx.1, hlog, EReal.left_distrib_of_nonneg_of_ne_top
      (EReal.coe_nonneg.mpr hc.le) (EReal.coe_ne_top _), ← EReal.coe_mul]
    simp only [add_assoc, ← EReal.coe_add]
    congr 2
    ring
  have hw : PlurisubharmonicOn (fun x => (c : EReal) * generatorLog g x) Ω := by
    intro x hx
    exact plurisubharmonicAt_scaled_generatorLog ⟨Ω, hΩ, hx, hg⟩ hc
  obtain ⟨B, hB⟩ := hb
  have hbound : PshHypersurfaceRemovable.LocallyBoundedAboveOff A Ω ψ := by
    intro x hx
    obtain ⟨L, hL, -⟩ := EReal.lt_iff_exists_real_btwn.mp
      (lt_top_iff_ne_top.mpr (hw x hx).ne_top)
    let U := {y | y ∈ Ω ∧ (c : EReal) * generatorLog g y < (L : EReal)}
    have hU : U ∈ 𝓝 x :=
      inter_mem (hΩ.mem_nhds hx) ((hw x hx).upperSemicontinuousAt L hL)
    refine ⟨U, hU, L + B, ?_⟩
    intro y hy hyA
    rw [heq ⟨hy.1, hyA⟩]
    calc (c : EReal) * generatorLog g y + (b y : EReal)
        ≤ (L : EReal) + (B : EReal) :=
          add_le_add hy.2.le (EReal.coe_le_coe_iff.mpr (hB y hy.1))
      _ = ((L + B : ℝ) : EReal) := (EReal.coe_add L B).symm
  have hq : PlurisubharmonicOn q Ω :=
    PshAnalyticRemovable.plurisubharmonicOn_extension_of_zeroLocus hΩ hψ hbound
      (g := fun _ : Fin 1 => d) (fun _ => hd) (by
        intro y _
        change d y = 0 ↔ ∀ _ : Fin 1, d y = 0
        exact ⟨fun h _ => h, fun h => h 0⟩)
  have hqeq : EqOn q (fun x => (c : EReal) * generatorLog g x + (b x : EReal))
      (Ω \ A) := fun x hx => (extension_eq hψ hW hx).trans (heq hx)
  obtain ⟨x, hx, hpx⟩ := hne
  have hfne : ¬ ∀ i, f i x = 0 := by
    intro h
    exact hpx ((hrep x hx).trans ((scaled_generatorLog_add_eq_bot_iff f x hc (b x)).mpr h))
  obtain ⟨i, hi⟩ := not_forall.mp hfne
  have hdx : d x ≠ 0 := by
    intro h
    exact hi (by rw [hfactor x hx i, h, zero_mul])
  have hgi : g i x ≠ 0 := by
    intro h
    exact hi (by rw [hfactor x hx i, h, mul_zero])
  have hqne : q x ≠ ⊥ := by
    rw [hqeq ⟨hx, hdx⟩]
    intro h
    exact hgi ((scaled_generatorLog_add_eq_bot_iff g x hc (b x)).mp h i)
  exact ⟨hq, ⟨x, hx, hqne⟩, hqeq⟩

end SGPT.Foundations.Analysis.Pending.ActualAnalyticFactorResidualPsh
