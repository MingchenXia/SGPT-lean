import SGPT.Foundations.Analysis.Pending.QuasiEquisingularBackgroundDomination
import SGPT.Foundations.Analysis.Pending.TraceRepresentativeConstruction
import SGPT.Foundations.Analysis.Pending.SingularNativeCommonBackground
import SGPT.Foundations.Analysis.Pending.QuasiEquisingularRestrictionAnyBigBackground
import SGPT.Foundations.Analysis.Pending.SingularCanonicalDistanceZeroPEquivalence

set_option autoImplicit false

/-! # Actual trace representatives are globally P-equivalent -/

open Set Filter
open scoped Topology Manifold ENNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.TraceRepresentativeGlobalPEquivalence

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  FirstPass.QuasiEquisingularApproximation TraceRepresentativeConstruction
  SingularGlobalPOrder ThetaPshL1Topology SingularCanonicalSingularityDistance
  PluripolarCapacityDichotomy

noncomputable section

variable {n k : ℕ} {M V : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]

/-- All original approximation and target choices are internally unified.
The actual finite canonical distance then identifies the two trace classes. -/
theorem sourcePEquivalent_of_isTraceRepresentativeAlong
    {omega : KahlerBackground n M} (omegaV : KahlerBackground k V)
    {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    {u : M → EReal} {τ₀ τ₁ : V → EReal}
    (hT₀ : IsTraceRepresentativeAlong omega omegaV hι u τ₀)
    (hT₁ : IsTraceRepresentativeAlong omega omegaV hι u τ₁) :
    SourcePEquivalent (n := k) τ₀ τ₁ := by
  obtain ⟨hg, θ₀, ε, uSeq, hU, β₀, _, hτ₀, hv₀, hlim₀⟩ := hT₀
  obtain ⟨_, θ₁, δ, vSeq, hV, β₁, _, hτ₁, hv₁, hlim₁⟩ := hT₁
  obtain ⟨κ, hUc, hVc⟩ :=
    QuasiEquisingularBackgroundDomination.exists_common_kahler_background hU hV
  let B : Bool → ClosedRealOneOneForm k V := fun b => if b then β₁.form else β₀.form
  obtain ⟨C, hC, hsemi⟩ := KahlerDomination.exists_pos_forall_isSemipositive_add_smul
    omegaV (fun b : Bool => -(B b))
  have hCp : 0 < C + 1 := by linarith
  let γ : KahlerBackground k V := KahlerBackground.smul hCp omegaV
  have hγof (b : Bool) {p : V → EReal} (hp : IsThetaPshPotential (B b).val p) :
      IsThetaPshPotential γ.form.val p := by
    have hmid : B b + (-B b + C • omegaV.form) = C • omegaV.form := by module
    have hpm : IsThetaPshPotential (C • omegaV.form).val p := by
      simpa only [hmid] using
        LocalPotentials.isThetaPshPotential_add_of_semipositive hp (hsemi b)
    have hform : C • omegaV.form + omegaV.form = γ.form := by
      dsimp only [γ, KahlerBackground.smul_form]
      module
    simpa only [hform] using
      LocalPotentials.isThetaPshPotential_add_of_semipositive hpm omegaV.isSemipositive
  have hUγ (j : ℕ) : IsThetaPshPotential γ.form.val (fun y => uSeq j (ι y)) :=
    hγof false (hv₀ j)
  have hVγ (j : ℕ) : IsThetaPshPotential γ.form.val (fun y => vSeq j (ι y)) :=
    hγof true (hv₁ j)
  have hτ₀γ : IsThetaPshPotential γ.form.val τ₀ := hγof false hτ₀
  have hτ₁γ : IsThetaPshPotential γ.form.val τ₁ := hγof true hτ₁
  have hlim₀γ := (SingularNativeCommonBackground.tendsto_native_iff_kahler_targets
    omegaV β₀ γ atTop hv₀ hτ₀ hUγ hτ₀γ).mp hlim₀
  have hlim₁γ := (SingularNativeCommonBackground.tendsto_native_iff_kahler_targets
    omegaV β₁ γ atTop hv₁ hτ₁ hVγ hτ₁γ).mp hlim₁
  have hreal :=
    (QuasiEquisingularRestrictionAnyBigBackground.restricted_distance_tendsto_zero_in_any_big_background
      omegaV hUc hVc hι hg γ.form (isBigClass_kahler γ) hUγ hVγ).1
  let := singularityPseudoMetricSpace omegaV γ.form (isBigClass_kahler γ)
  let : TopologicalSpace (ThetaPshL1 γ.form.val) :=
    (singularityPseudoMetricSpace omegaV γ.form
      (isBigClass_kahler γ)).toUniformSpace.toTopologicalSpace
  let X : ℕ → ThetaPshL1 γ.form.val := fun j => ⟨fun y => uSeq j (ι y), hUγ j⟩
  let Y : ℕ → ThetaPshL1 γ.form.val := fun j => ⟨fun y => vSeq j (ι y), hVγ j⟩
  let A : ThetaPshL1 γ.form.val := ⟨τ₀, hτ₀γ⟩
  let B₁ : ThetaPshL1 γ.form.val := ⟨τ₁, hτ₁γ⟩
  have hx : Tendsto X atTop (𝓝 A) := hlim₀γ
  have hy : Tendsto Y atTop (𝓝 B₁) := hlim₁γ
  have hd : Tendsto (fun j => dist (X j) (Y j)) atTop (𝓝 (0 : ℝ)) := by
    simp only [dist_eq_singularityDistance_toReal omegaV γ.form (isBigClass_kahler γ)]
    exact hreal
  have hz : dist A B₁ = 0 := tendsto_nhds_unique (hx.dist hy) hd
  rw [dist_eq_singularityDistance_toReal] at hz
  obtain ⟨m, _, _, _, hD⟩ := exists_tendsto_singularityDistance omegaV γ.form
    (isBigClass_kahler γ) A.property B₁.property
  have hm : m = 0 := by simpa only [hD, EReal.toReal_coe] using hz
  have hzero : singularityDistance omegaV γ.form (isBigClass_kahler γ) A.val B₁.val = 0 := by
    simpa only [hm, EReal.coe_zero] using hD
  exact (SingularCanonicalDistanceZeroPEquivalence.singularityDistance_eq_zero_iff_sourcePEquivalent
    omegaV γ.form (isBigClass_kahler γ) A.property B₁.property).mp hzero

end

end SGPT.Foundations.Analysis.Pending.TraceRepresentativeGlobalPEquivalence
