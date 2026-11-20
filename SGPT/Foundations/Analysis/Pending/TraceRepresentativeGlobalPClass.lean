import SGPT.Foundations.Analysis.Pending.TraceRepresentativeAllChoices

set_option autoImplicit false

/-! # The complete actual trace predicate is stable on its global P-class -/

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.TraceRepresentativeGlobalPClass

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  FirstPass.QuasiEquisingularApproximation FirstPass.TraceBackground
  TraceRepresentativeConstruction SingularGlobalPOrder ThetaPshL1Topology
  SingularCanonicalSingularityDistance PluripolarCapacityDichotomy

noncomputable section

variable {n k : ℕ} {M V : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]

/-- The actual global witness supplies genuine PSH for the new function;
the original full QEA acquires a produced admissible target and native limit. -/
theorem isTraceRepresentativeAlong_of_sourcePEquivalent
    {omega : KahlerBackground n M} (omegaV : KahlerBackground k V)
    {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    {u : M → EReal} {τ ψ : V → EReal}
    (htrace : IsTraceRepresentativeAlong omega omegaV hι u τ)
    (heq : SourcePEquivalent (n := k) τ ψ) :
    IsTraceRepresentativeAlong omega omegaV hι u ψ := by
  obtain ⟨hg, θ, ε, U, happ, β, hadm, hτ, hterms, hlim⟩ := htrace
  obtain ⟨σ, _, hψ, _, _, _⟩ := heq.1
  let B : Bool → ClosedRealOneOneForm k V := fun b => if b then σ else β.form
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
  have hτγ : IsThetaPshPotential γ.form.val τ := hγof false hτ
  have hψγ : IsThetaPshPotential γ.form.val ψ := hγof true hψ
  have hUγ (j : ℕ) : IsThetaPshPotential γ.form.val (fun y => U j (ι y)) :=
    hγof false (hterms j)
  have hadmγ : IsAdmissibleTraceBackground hι omega θ ε γ.form := by
    refine ⟨γ.isKahler, fun j => ?_⟩
    change (γ.form - ClosedRealOneOneForm.pullback hι (θ + ε j • omega.form)).val.IsSemipositive
    have hform : γ.form - ClosedRealOneOneForm.pullback hι (θ + ε j • omega.form) =
        (β.form - ClosedRealOneOneForm.pullback hι (θ + ε j • omega.form)) +
          (-β.form + C • omegaV.form) := by
      dsimp only [γ, KahlerBackground.smul_form]
      module
    rw [hform]
    intro e z hz v
    exact add_nonneg (hadm.2 j e z hz v) (hsemi false e z hz v)
  have hlimγ := (SingularNativeCommonBackground.tendsto_native_iff_kahler_targets
    omegaV β γ atTop hterms hτ hUγ hτγ).mp hlim
  have hd :=
    (SingularCanonicalDistanceZeroPEquivalence.singularityDistance_eq_zero_iff_sourcePEquivalent
      omegaV γ.form (isBigClass_kahler γ) hτγ hψγ).mpr heq
  let := singularityPseudoMetricSpace omegaV γ.form (isBigClass_kahler γ)
  let : TopologicalSpace (ThetaPshL1 γ.form.val) :=
    (singularityPseudoMetricSpace omegaV γ.form
      (isBigClass_kahler γ)).toUniformSpace.toTopologicalSpace
  let A : ℕ → ThetaPshL1 γ.form.val := fun j => ⟨fun y => U j (ι y), hUγ j⟩
  let T : ThetaPshL1 γ.form.val := ⟨τ, hτγ⟩
  let S : ThetaPshL1 γ.form.val := ⟨ψ, hψγ⟩
  have hzero : dist T S = 0 := by
    rw [dist_eq_singularityDistance_toReal]
    change (singularityDistance omegaV γ.form (isBigClass_kahler γ) τ ψ).toReal = 0
    rw [hd, EReal.toReal_zero]
  have hdist (j : ℕ) : dist (A j) S = dist (A j) T := by
    apply le_antisymm
    · simpa only [hzero, add_zero] using dist_triangle (A j) T S
    · have hh := dist_triangle (A j) S T
      rw [dist_comm S T, hzero, add_zero] at hh
      exact hh
  have hnew : Tendsto A atTop (𝓝 S) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    have hgiven : Tendsto A atTop (𝓝 T) := hlimγ
    simpa only [hdist] using tendsto_iff_dist_tendsto_zero.mp hgiven
  exact ⟨hg, θ, ε, U, happ, γ, hadmγ, hψγ, hUγ, hnew⟩

/-- In the compact source domain, the complete reader predicate is exactly
membership in the actual global P-class of any given full reader. -/
theorem isTraceRepresentativeAlong_iff_sourcePEquivalent [CompactSpace M]
    {omega : KahlerBackground n M} (omegaV : KahlerBackground k V)
    {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    {u : M → EReal} {τ ψ : V → EReal}
    (htrace : IsTraceRepresentativeAlong omega omegaV hι u τ) :
    IsTraceRepresentativeAlong omega omegaV hι u ψ ↔ SourcePEquivalent (n := k) τ ψ := by
  exact ⟨fun hψ => TraceRepresentativeAllChoices.sourcePEquivalent_of_isTraceRepresentativeAlong
      omegaV omegaV hι htrace hψ,
    isTraceRepresentativeAlong_of_sourcePEquivalent omegaV hι htrace⟩

end

end SGPT.Foundations.Analysis.Pending.TraceRepresentativeGlobalPClass
