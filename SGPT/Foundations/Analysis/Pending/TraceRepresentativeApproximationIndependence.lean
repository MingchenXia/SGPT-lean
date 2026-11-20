import SGPT.Foundations.Analysis.Pending.TraceRepresentativeGlobalPEquivalenceAuxiliaries

set_option autoImplicit false

/-! # Actual native trace convergence for every legitimate approximation -/

open Set Filter
open scoped Topology Manifold ENNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.TraceRepresentativeApproximationIndependence

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  FirstPass.QuasiEquisingularApproximation FirstPass.TraceBackground
  TraceRepresentativeConstruction ThetaPshL1Topology
  SingularCanonicalSingularityDistance PluripolarCapacityDichotomy

noncomputable section

variable {n k : ℕ} {M V : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]

/-- Every genuine new QEA and legitimate target internally acquire their
restricted-stage PSH witnesses and the original candidate's native limit. -/
theorem native_limit_of_isTraceRepresentativeAlong
    {omega₀ omega₁ : KahlerBackground n M} (omegaV : KahlerBackground k V)
    {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    {u : M → EReal} {τ : V → EReal}
    (htrace : IsTraceRepresentativeAlong omega₀ omegaV hι u τ)
    {θ : ClosedRealOneOneForm n M} {ε : ℕ → ℝ} {vSeq : ℕ → M → EReal}
    (happ : IsQuasiEquisingularApproximation omega₁ θ u ε vSeq)
    (β : KahlerBackground k V)
    (hadm : IsAdmissibleTraceBackground hι omega₁ θ ε β.form)
    (hτ : IsThetaPshPotential β.form.val τ) :
    ∃ hv : ∀ j, IsThetaPshPotential β.form.val (fun y => vSeq j (ι y)),
      Tendsto (fun j => (⟨fun y => vSeq j (ι y), hv j⟩ : ThetaPshL1 β.form.val))
        atTop (@nhds (ThetaPshL1 β.form.val)
          (singularityPseudoMetricSpace omegaV β.form
            (isBigClass_kahler β)).toUniformSpace.toTopologicalSpace ⟨τ, hτ⟩) ∧
      IsTraceRepresentativeAlong omega₁ omegaV hι u τ := by
  have hg := htrace.1
  have hvβ (j : ℕ) : IsThetaPshPotential β.form.val (fun y => vSeq j (ι y)) := by
    have hp := AnalyticQuasiEquisingularRestriction.isThetaPshPotential_ordinaryRestriction_term
      happ hι hg j
    have hform : ClosedRealOneOneForm.pullback hι (θ + ε j • omega₁.form) +
        (β.form - ClosedRealOneOneForm.pullback hι (θ + ε j • omega₁.form)) = β.form := by module
    simpa only [hform] using
      LocalPotentials.isThetaPshPotential_add_of_semipositive hp (hadm.2 j)
  obtain ⟨κ, h₀, h₁⟩ :=
    QuasiEquisingularAuxiliaryDomination.exists_common_auxiliary_kahler_background omega₀ omega₁
  have htraceκ := TraceRepresentativeAuxiliaryDomination.isTraceRepresentativeAlong_of_auxiliary_domination
    omegaV hι htrace h₀
  have happκ :=
    QuasiEquisingularAuxiliaryDomination.isQuasiEquisingularApproximation_of_auxiliary_domination
      happ h₁
  obtain ⟨_, θ₀, δ, uSeq, hU, β₀, _, hτ₀, hv₀, hlim₀⟩ := htraceκ
  obtain ⟨κθ, hUc, hVc⟩ :=
    QuasiEquisingularBackgroundDomination.exists_common_kahler_background hU happκ
  let B : Bool → ClosedRealOneOneForm k V := fun b => if b then β.form else β₀.form
  obtain ⟨C, hC, hsemi⟩ := KahlerDomination.exists_pos_forall_isSemipositive_add_smul
    omegaV (fun b : Bool => -(B b))
  let γ : KahlerBackground k V := KahlerBackground.smul hC omegaV
  have hγof (b : Bool) {p : V → EReal} (hp : IsThetaPshPotential (B b).val p) :
      IsThetaPshPotential γ.form.val p := by
    have hform : B b + (-B b + C • omegaV.form) = γ.form := by
      dsimp only [γ, KahlerBackground.smul_form]
      module
    simpa only [hform] using
      LocalPotentials.isThetaPshPotential_add_of_semipositive hp (hsemi b)
  have hUγ (j : ℕ) : IsThetaPshPotential γ.form.val (fun y => uSeq j (ι y)) :=
    hγof false (hv₀ j)
  have hVγ (j : ℕ) : IsThetaPshPotential γ.form.val (fun y => vSeq j (ι y)) :=
    hγof true (hvβ j)
  have hτγ : IsThetaPshPotential γ.form.val τ := hγof true hτ
  have hlim₀γ := (SingularNativeCommonBackground.tendsto_native_iff_kahler_targets
    omegaV β₀ γ atTop hv₀ hτ₀ hUγ hτγ).mp hlim₀
  have hreal :=
    (QuasiEquisingularRestrictionAnyBigBackground.restricted_distance_tendsto_zero_in_any_big_background
      omegaV hUc hVc hι hg γ.form (isBigClass_kahler γ) hUγ hVγ).1
  let := singularityPseudoMetricSpace omegaV γ.form (isBigClass_kahler γ)
  let : TopologicalSpace (ThetaPshL1 γ.form.val) :=
    (singularityPseudoMetricSpace omegaV γ.form
      (isBigClass_kahler γ)).toUniformSpace.toTopologicalSpace
  let X : ℕ → ThetaPshL1 γ.form.val := fun j => ⟨fun y => uSeq j (ι y), hUγ j⟩
  let Y : ℕ → ThetaPshL1 γ.form.val := fun j => ⟨fun y => vSeq j (ι y), hVγ j⟩
  let T : ThetaPshL1 γ.form.val := ⟨τ, hτγ⟩
  have hx : Tendsto X atTop (𝓝 T) := hlim₀γ
  have hxy : Tendsto (fun j => dist (X j) (Y j)) atTop (𝓝 (0 : ℝ)) := by
    simp only [dist_eq_singularityDistance_toReal omegaV γ.form (isBigClass_kahler γ)]
    exact hreal
  have hxT : Tendsto (fun j => dist (X j) T) atTop (𝓝 (0 : ℝ)) :=
    tendsto_iff_dist_tendsto_zero.mp hx
  have hy : Tendsto Y atTop (𝓝 T) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    exact squeeze_zero (fun _ => dist_nonneg)
      (fun j => by simpa only [dist_comm (Y j) (X j)] using dist_triangle (Y j) (X j) T)
      (by simpa only [zero_add] using hxy.add hxT)
  have hyβ := (SingularNativeCommonBackground.tendsto_native_iff_kahler_targets
    omegaV β γ atTop hvβ hτ hVγ hτγ).mpr hy
  exact ⟨hvβ, hyβ, hg, θ, ε, vSeq, happ, β, hadm, hτ, hvβ, hyβ⟩

end

end SGPT.Foundations.Analysis.Pending.TraceRepresentativeApproximationIndependence
