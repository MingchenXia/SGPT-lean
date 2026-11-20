import SGPT.Foundations.Analysis.Pending.TraceRepresentativeRationalScaling
import SGPT.Foundations.Analysis.Pending.TracePositiveCoefficientNativeLimits
import SGPT.Foundations.Analysis.Pending.TraceIdealOrderMonotonicity
import SGPT.Foundations.Analysis.Pending.SingularNativeCommonBackground
import Mathlib.Topology.Order.IsLUB

set_option autoImplicit false


/-! # Genuine positive REAL homogeneity of the trace with every original choice -/

open Set Filter
open scoped Topology Manifold ENNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.TracePositiveRealHomogeneity

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  FirstPass.QuasiEquisingularApproximation FirstPass.TraceBackground
  FirstPass.IEnvelope TraceRepresentativeConstruction SingularGlobalPOrder
  ThetaPshL1Topology SingularCanonicalSingularityDistance PluripolarCapacityDichotomy

noncomputable section

private theorem scalar_comparison_of_upper_bound {E : Type*} (u : E → EReal)
    {C a b : ℝ} (hC : ∀ x, u x ≤ (C : EReal))
    (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a) :
    ∀ x, (a : EReal) * u x ≤ (b : EReal) * u x + (((a - b) * C : ℝ) : EReal) := by
  intro x
  have hx := hC x
  induction hu : u x using EReal.rec with
  | bot =>
    simp only [EReal.coe_mul_bot_of_pos ha, EReal.coe_mul_bot_of_pos hb ]
    exact bot_le
  | top => rw [hu] at hx; exact (EReal.coe_ne_top C (top_le_iff.mp hx)).elim
  | coe r =>
    rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff]
    have hr : r ≤ C := EReal.coe_le_coe_iff.mp (hu ▸ hx)
    nlinarith [mul_nonneg (sub_nonneg.mpr hba) (sub_nonneg.mpr hr)]

variable {n k : ℕ} {M Y : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel k) Y] [IsComplexManifold k Y]
  [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] [ConnectedSpace Y]

/-- Actual rational FULL readers, two actual native coefficient limits,
and global closed order internally prove the original real homogeneity. -/
theorem sourcePEquivalent_pos_smul_of_isTraceRepresentativeAlong
    {omega₀ omega₁ : KahlerBackground n M} (omegaY₀ omegaY₁ : KahlerBackground k Y)
    {ι : Y → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    {u : M → EReal} {τ τℓ : Y → EReal}
    (hT : IsTraceRepresentativeAlong omega₀ omegaY₀ hι u τ)
    {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hTℓ : IsTraceRepresentativeAlong omega₁ omegaY₁ hι
      (fun x => (ℓ : EReal) * u x) τℓ) :
    SourcePEquivalent (n := k) τℓ (fun y => (ℓ : EReal) * τ y) := by
  have hTkeep := hT
  have hTℓkeep := hTℓ
  obtain ⟨_, θ, _, _, hu, β, _, hτ, _, _⟩ := hT
  obtain ⟨_, _, _, _, _, η, _, hτℓ, _, _⟩ := hTℓ
  let : Nonempty M := Nonempty.map ι (inferInstance : Nonempty Y)
  obtain ⟨C, hC⟩ := hu.target.exists_global_upper_bound
  obtain ⟨r, _, hrmem, hrlim⟩ :=
    (Rat.denseRange_cast : DenseRange ((↑) : ℚ → ℝ)).exists_seq_strictMono_tendsto_of_lt
      Rat.cast_mono hℓ
  obtain ⟨s, _, hsmem, hslim⟩ :=
    (Rat.denseRange_cast : DenseRange ((↑) : ℚ → ℝ)).exists_seq_strictAnti_tendsto_of_lt
      Rat.cast_mono (show ℓ < ℓ + 1 by linarith)
  have hrpos (j : ℕ) : 0 < r j := by exact_mod_cast (hrmem j).1
  have hspos (j : ℕ) : 0 < s j := by exact_mod_cast hℓ.trans (hsmem j).1
  let rr : ℕ → Ioo (0 : ℝ) ℓ := fun j => ⟨(r j : ℝ), hrmem j⟩
  let ss : ℕ → Ioo ℓ (ℓ + 1) := fun j => ⟨(s j : ℝ), hsmem j⟩
  obtain ⟨hℓβ, hrβ, hrnative⟩ :=
    TracePositiveCoefficientNativeLimits.tendsto_native_lower_coefficients
      omegaY₀ β hτ hℓ atTop rr hrlim
  obtain ⟨_, hsβ, hsnative⟩ :=
    TracePositiveCoefficientNativeLimits.tendsto_native_upper_coefficients
      omegaY₀ β hτ hℓ atTop ss hslim
  let βℓ : KahlerBackground k Y := KahlerBackground.smul (show 0 < ℓ + 1 by linarith) β
  let B : Bool → ClosedRealOneOneForm k Y := fun b => if b then η.form else βℓ.form
  obtain ⟨D, hD, hdom⟩ := KahlerDomination.exists_pos_forall_isSemipositive_add_smul
    omegaY₀ (fun b : Bool => -(B b))
  let γ : KahlerBackground k Y := KahlerBackground.smul hD omegaY₀
  have hγof (b : Bool) {p : Y → EReal} (hp : IsThetaPshPotential (B b).val p) :
      IsThetaPshPotential γ.form.val p := by
    have heq : B b + (-B b + D • omegaY₀.form) = γ.form := by
      dsimp only [γ, KahlerBackground.smul_form]
      module
    simpa only [heq] using LocalPotentials.isThetaPshPotential_add_of_semipositive hp (hdom b)
  have hℓγ : IsThetaPshPotential γ.form.val (fun y => (ℓ : EReal) * τ y) := hγof false hℓβ
  have hτℓγ : IsThetaPshPotential γ.form.val τℓ := hγof true hτℓ
  have hrγ (j : ℕ) : IsThetaPshPotential γ.form.val (fun y => ((r j : ℝ) : EReal) * τ y) :=
    hγof false (hrβ j)
  have hsγ (j : ℕ) : IsThetaPshPotential γ.form.val (fun y => ((s j : ℝ) : EReal) * τ y) :=
    hγof false (hsβ j)
  have hrfinal := (SingularNativeCommonBackground.tendsto_native_iff_kahler_targets
    omegaY₀ βℓ γ atTop hrβ hℓβ hrγ hℓγ).mp hrnative
  have hsfinal := (SingularNativeCommonBackground.tendsto_native_iff_kahler_targets
    omegaY₀ βℓ γ atTop hsβ hℓβ hsγ hℓγ).mp hsnative
  let R : ℕ → ThetaPshL1 γ.form.val := fun j => ⟨fun y => ((r j : ℝ) : EReal) * τ y, hrγ j⟩
  let S : ℕ → ThetaPshL1 γ.form.val := fun j => ⟨fun y => ((s j : ℝ) : EReal) * τ y, hsγ j⟩
  let T : ThetaPshL1 γ.form.val := ⟨τℓ, hτℓγ⟩
  let L : ThetaPshL1 γ.form.val := ⟨fun y => (ℓ : EReal) * τ y, hℓγ⟩
  have htconst : Tendsto (fun _ : ℕ => T) atTop
      (@nhds (ThetaPshL1 γ.form.val)
        (singularityPseudoMetricSpace omegaY₀ γ.form (isBigClass_kahler γ)).toUniformSpace.toTopologicalSpace T) :=
    @tendsto_const_nhds (ThetaPshL1 γ.form.val)
      (singularityPseudoMetricSpace omegaY₀ γ.form (isBigClass_kahler γ)).toUniformSpace.toTopologicalSpace
      ℕ T atTop
  have hlow : ∀ᶠ j : ℕ in atTop, SourcePOrder (n := k) T.val (R j).val := by
    apply Eventually.of_forall
    intro j
    have hjr := TraceRepresentativeRationalScaling.isTraceRepresentativeAlong_pos_rat_smul
      omegaY₀ hι hTkeep (hrpos j)
    have hjpsh := RestrictedApproximantComparison.isThetaPshPotential_smul hu.target
      ((hrmem j).1)
    have hI := iOrderOnManifold_of_le_add hjpsh.1.quasiPlurisubharmonic
      (scalar_comparison_of_upper_bound u hC hℓ (hrmem j).1 (hrmem j).2.le)
    exact TraceIdealOrderMonotonicity.sourcePOrder_of_iOrder_of_isTraceRepresentativeAlong
      omegaY₁ omegaY₀ hι hTℓkeep hjr hI
  have hhigh : ∀ᶠ j : ℕ in atTop, SourcePOrder (n := k) (S j).val T.val := by
    apply Eventually.of_forall
    intro j
    have hjs := TraceRepresentativeRationalScaling.isTraceRepresentativeAlong_pos_rat_smul
      omegaY₀ hι hTkeep (hspos j)
    have hℓpsh := RestrictedApproximantComparison.isThetaPshPotential_smul hu.target hℓ
    have hI := iOrderOnManifold_of_le_add hℓpsh.1.quasiPlurisubharmonic
      (scalar_comparison_of_upper_bound u hC (hℓ.trans (hsmem j).1) hℓ (hsmem j).1.le)
    exact TraceIdealOrderMonotonicity.sourcePOrder_of_iOrder_of_isTraceRepresentativeAlong
      omegaY₀ omegaY₁ hι hjs hTℓkeep hI
  exact ⟨SingularNativeGlobalPOrderClosed.sourcePOrder_of_native_limits
      omegaY₀ γ.form (isBigClass_kahler γ) atTop (fun _ => T) R T L htconst hrfinal hlow,
    SingularNativeGlobalPOrderClosed.sourcePOrder_of_native_limits
      omegaY₀ γ.form (isBigClass_kahler γ) atTop S (fun _ => T) L T hsfinal htconst hhigh⟩

end

end SGPT.Foundations.Analysis.Pending.TracePositiveRealHomogeneity
