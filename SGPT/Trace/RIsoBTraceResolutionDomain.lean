import SGPT.Trace.RIsoBResolutionVolume
import SGPT.Trace.TraceEnvelope
import SGPT.Foundations.Analysis.Pending.PositiveNormalizedTraceCurrentDomain
import SGPT.Foundations.Analysis.Pending.TraceFreeLimit
import SGPT.Foundations.Analysis.Pending.AmbientMassBackgroundMonotone
import SGPT.Foundations.Analysis.Pending.BoucksomMassBigness
import SGPT.Foundations.Analysis.Pending.NonBigPotentialMass

/-!
# The two observations after `def:traceop2` for an arbitrary irreducible `Y`

Source `def:traceop2` (`chapter_trace.tex`): *if `φ ∈ PSH(X, θ)`, then for any Kähler form `ω`
on `X` the trace operator `Tr^{θ+ω}_Y(φ)` is always defined. In particular, if `θ_φ` is a Kähler
current, `Tr^θ_Y(φ)` is always defined.* The existing proofs
(`SGPT.Trace.hasPositiveSourceTraceAlong_add_kahler`,
`SGPT.Trace.hasPositiveSourceTraceAlong_of_kahlerCurrent`) need the pullback `ι^*ω` to the
target to be Kähler, which holds for submanifolds but fails on a resolution `Y' → Y` of a
singular `Y`, where `ι^*ω` is only semipositive.

Here the target is an arbitrary resolution target `(Y', ι)` of `Y` (`Trace2Resolution`), and the
argument of `PositiveNormalizedTraceCurrentDomain` is run with the semipositive form
`κ = δ ι^*ω` in place of a Kähler form: what is used is

* the uniform mass floor `∫ (γ + κ)_v^k ≥ ∫ κ^k` for `v ∈ PSH(γ)` and semipositive `κ`
  (`diagonalPotentialMass_zero_le_add_semipositive`, from the Kähler case by perturbing `κ` by
  `ε ω_{Y'}` and letting `ε → 0`), and
* `∫_{Y'} (ι^*ω)^{dim Y} > 0` (`RIsoB.diagonalPotentialMass_pullback_kahler_pos`: a resolution is
  generically an immersion), which also makes the restricted class big (Boucksom).

## Main results

* `hasPositiveTraceRepresentativeAlong_of_current_margin`: the native domain statement.
* `hasPositiveSourceTraceAlong_of_kahlerCurrent`, `hasPositiveSourceTraceAlong_add_kahler`:
  source `def:traceop2`, the two observations, on every resolution target of every irreducible
  `Y` (no Kähler-pullback hypothesis).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal ContDiff

universe u

namespace SGPT.Trace.RIsoB

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
  SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.DiagonalMass

/-! ### The mass floor for a semipositive enlargement -/

section Floor

variable {k : ℕ} {V : Type*} [TopologicalSpace V] [ChartedSpace (ComplexModel k) V]
  [IsComplexManifold k V] [MeasurableSpace V] [BorelSpace V] [CompactSpace V]

omit [MeasurableSpace V] [BorelSpace V] [CompactSpace V] in
/-- A Kähler form plus a semipositive closed `(1,1)`-form is a Kähler form. -/
def kahlerAddSemipositive {κ : ClosedRealOneOneForm k V} (hκ : κ.val.IsSemipositive)
    (a : KahlerBackground k V) : KahlerBackground k V where
  form := κ + a.form
  isKahler := by
    refine ⟨fun e z hz => ⟨?_, ?_⟩, (κ + a.form).property.1⟩
    · exact isOneOne_add (κ.property.2 e z hz) (a.isKahler.1 e z hz).1
    · intro v hv
      simpa only [ClosedRealOneOneForm.coeff_add, ContinuousAlternatingMap.add_apply] using
        add_pos_of_nonneg_of_pos (hκ e z hz v) ((a.isKahler.1 e z hz).2 v hv)

omit [MeasurableSpace V] [BorelSpace V] [CompactSpace V] in
theorem kahlerAddSemipositive_form {κ : ClosedRealOneOneForm k V}
    (hκ : κ.val.IsSemipositive) (a : KahlerBackground k V) :
    (kahlerAddSemipositive hκ a).form = κ + a.form := rfl

omit [BorelSpace V] in
private theorem diagonalPotentialMass_congr_form {a b : ClosedRealOneOneForm k V} (h : a = b)
    {v : V → EReal} (ha : IsThetaPshPotential a.val v) (hb : IsThetaPshPotential b.val v) :
    diagonalPotentialMass a v ha = diagonalPotentialMass b v hb := by
  subst h
  rfl

/-- **The mass floor for a semipositive enlargement**: for `v ∈ PSH(γ)` and a semipositive
closed `(1,1)`-form `κ`, `∫ κ^k ≤ ∫ (γ + κ + dd^c v)^k`. -/
theorem diagonalPotentialMass_zero_le_add_semipositive (omegaV : KahlerBackground k V)
    {κ : ClosedRealOneOneForm k V} (hκ : κ.val.IsSemipositive)
    {γ : ClosedRealOneOneForm k V} {v : V → EReal} (hv : IsThetaPshPotential γ.val v) :
    diagonalPotentialMass κ (fun _ => 0) ((LocalPotentials.isThetaPshPotential_zero_iff κ).mpr hκ) ≤
      diagonalPotentialMass (γ + κ) v
        (LocalPotentials.isThetaPshPotential_add_of_semipositive hv hκ) := by
  set hv' := LocalPotentials.isThetaPshPotential_add_of_semipositive hv hκ
  obtain ⟨K, hK, hle⟩ := TraceFreeLimit.exists_diagonalPotentialMass_add_smul_le omegaV hv'
  have hstep : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      diagonalPotentialMass κ (fun _ => 0) ((LocalPotentials.isThetaPshPotential_zero_iff κ).mpr hκ)
        ≤ diagonalPotentialMass (γ + κ) v hv' + ENNReal.ofReal ε * K := by
    intro ε hε hε1
    let Kε := kahlerAddSemipositive hκ (KahlerBackground.smul hε omegaV)
    have hKε : Kε.form = κ + ε • omegaV.form := rfl
    have h1 := AmbientMassBackgroundMonotone.diagonalPotentialMass_le_add_smul
      omegaV.isSemipositive hε ((LocalPotentials.isThetaPshPotential_zero_iff κ).mpr hκ)
      (PluripolarCapacityDichotomy.isThetaPshPotential_zero Kε)
    have h2 := AnalyticRestrictedApproximantUniformMass.diagonalPotentialMass_zero_le_add_unit Kε hv
    have hform : γ + Kε.form = γ + κ + ε • omegaV.form := by
      rw [hKε, add_assoc]
    have h3 := hle ε hε hε1 (hform ▸ LocalPotentials.isThetaPshPotential_add_of_semipositive hv
      Kε.isSemipositive)
    calc _ ≤ diagonalPotentialMass (κ + ε • omegaV.form) (fun _ => 0)
          (PluripolarCapacityDichotomy.isThetaPshPotential_zero Kε) := h1
      _ = diagonalPotentialMass Kε.form (fun _ => 0)
          (PluripolarCapacityDichotomy.isThetaPshPotential_zero Kε) := rfl
      _ ≤ diagonalPotentialMass (γ + Kε.form) v
          (LocalPotentials.isThetaPshPotential_add_of_semipositive hv Kε.isSemipositive) := h2
      _ = diagonalPotentialMass (γ + κ + ε • omegaV.form) v
          (hform ▸ LocalPotentials.isThetaPshPotential_add_of_semipositive hv
            Kε.isSemipositive) := diagonalPotentialMass_congr_form hform _ _
      _ ≤ _ := h3
  have hlim : Tendsto (fun ε : ℝ => diagonalPotentialMass (γ + κ) v hv' + ENNReal.ofReal ε * K)
      (𝓝[>] 0) (𝓝 (diagonalPotentialMass (γ + κ) v hv' + 0)) := by
    refine tendsto_const_nhds.add ?_
    have h0 : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    have h := ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal h0) (b := K) (Or.inr hK.ne)
    simpa only [ENNReal.ofReal_zero, zero_mul] using h
  rw [add_zero] at hlim
  refine ge_of_tendsto hlim ?_
  filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 from one_pos)] with ε hε
  exact hstep ε hε.1 hε.2

end Floor

/-! ### The domain of the normalized trace for semipositive pullbacks of positive volume -/

section Domain

open FirstPass.QuasiEquisingularApproximation FirstPass.TraceBackground
  TraceRepresentativeConstruction GlobalNonPluripolar ThetaPshL1Topology
  SingularCanonicalSingularityDistance PositiveNormalizedTrace PluripolarCapacityDichotomy

variable {n k : ℕ} {M V : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]

omit [CompactSpace M] [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V] in
private theorem pullback_smul_form {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (c : ℝ) (a : ClosedRealOneOneForm n M) :
    ClosedRealOneOneForm.pullback hι (c • a) = c • ClosedRealOneOneForm.pullback hι a := by
  apply ClosedRealOneOneForm.ext
  intro e z
  ext v
  rfl

/-- **The domain of `Tr^θ_Y` from a current margin, for semipositive pullbacks.** If every
Kähler form of `M` pulls back to a form of positive volume on `V` (which holds on every
resolution target, `RIsoB.diagonalPotentialMass_pullback_kahler_pos`), `u ∈ PSH(M, θ - δω)` for
some `δ > 0` and the generic Lelong number of `u` along `ι` vanishes, then some trace operator
of `u` along `ι` lies in `PSH(V, ι^*θ)_{>0}`. (The Kähler-pullback hypothesis of
`PositiveNormalizedTraceCurrentDomain.hasPositiveTraceRepresentativeAlong_of_current_margin` is
not needed.) -/
theorem hasPositiveTraceRepresentativeAlong_of_current_margin
    (omega : KahlerBackground n M) (omegaV : KahlerBackground k V) {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (hvol : ∀ w : KahlerBackground n M,
      0 < diagonalPotentialMass (ClosedRealOneOneForm.pullback hι w.form) (fun _ => 0)
        ((LocalPotentials.isThetaPshPotential_zero_iff _).mpr
          (ClosedRealOneOneForm.pullback_isSemipositive hι w.isSemipositive)))
    {θ : ClosedRealOneOneForm n M} {u : M → EReal} {δ : ℝ} (hδ : 0 < δ)
    (hu : IsThetaPshPotential (θ - δ • omega.form).val u)
    (hgeneric : (⨅ y : V, lelongNumber (n := n) u (ι y)) = 0) :
    HasPositiveTraceRepresentativeAlong omega omegaV hι θ u := by
  obtain ⟨ε, U, happ, _, hstrict⟩ :=
    CalibratedQuasiEquisingularApproximation.exists_full_qea_with_original_background_stage_margin
      omega θ hδ hu
  have hd : 0 < δ / 2 := half_pos hδ
  let η := ClosedRealOneOneForm.pullback hι θ
  let w := KahlerBackground.smul hd omega
  let κ : ClosedRealOneOneForm k V := ClosedRealOneOneForm.pullback hι w.form
  have hκ : κ.val.IsSemipositive :=
    ClosedRealOneOneForm.pullback_isSemipositive hι w.isSemipositive
  have hpullSmall : ClosedRealOneOneForm.pullback hι (θ - (δ / 2) • omega.form) = η - κ := by
    have hsub : θ - (δ / 2) • omega.form = θ + (-(δ / 2)) • omega.form := by module
    have hκeq : κ = (δ / 2) • ClosedRealOneOneForm.pullback hι omega.form :=
      pullback_smul_form hι (δ / 2) omega.form
    rw [hsub, NefCoreKahlerCurrent.pullback_add_smul, hκeq]
    module
  have hsmall (j : ℕ) : IsThetaPshPotential (η - κ).val (fun y => U j (ι y)) := by
    rw [← hpullSmall]
    apply CompactAnalyticPoleLelongGap.isThetaPshPotential_comp_of_analytic_generic_inf_eq_zero
      hι (hstrict j).1
    · intro x _
      exact happ.term_hasAnalyticSingularityType j (complexChartAt (n := n) x)
        ((complexChartAt (n := n) x).val x)
        ((complexChartAt (n := n) x).val.map_source (mem_complexChartAt_source x))
    · exact AnalyticQuasiEquisingularRestriction.term_generic_lelong_inf_eq_zero
        happ ι hgeneric j
  have hv (j : ℕ) : IsThetaPshPotential η.val (fun y => U j (ι y)) := by
    simpa only [sub_add_cancel] using
      LocalPotentials.isThetaPshPotential_add_of_semipositive (hsmall j) hκ
  let hzero := (LocalPotentials.isThetaPshPotential_zero_iff κ).mpr hκ
  let b : ℝ := (diagonalPotentialMass κ (fun _ => 0) hzero).toReal
  have hb : 0 < b := ENNReal.toReal_pos (hvol w).ne'
    (globalMixedMeasure_apply_lt_top omegaV (fun _ : Fin k => hzero.1) univ).ne
  have hbound (j : ℕ) : ENNReal.ofReal b ≤
      diagonalPotentialMass η (fun y => U j (ι y)) (hv j) := by
    have hfloor := diagonalPotentialMass_zero_le_add_semipositive omegaV hκ (hsmall j)
    exact ENNReal.ofReal_toReal_le.trans
      (hfloor.trans_eq (diagonalPotentialMass_congr_form (sub_add_cancel η κ) _ _))
  have hbig : IsBigClass (RealBottChern.ofRepresentative η) := by
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · exact NonBigPotentialMass.isBigClass_of_dim_zero hk0 omegaV η
    · exact BoucksomMassBigness.isBigClass_of_diagonalPotentialMass_pos hkpos omegaV η (hv 0)
        ((ENNReal.ofReal_pos.mpr hb).trans_le (hbound 0))
  have hA (j : ℕ) : HasManifoldAnalyticSingularityType (n := k) (fun y => U j (ι y)) :=
    AnalyticTypeHolomorphicPullback.hasManifoldAnalyticSingularityType_comp
      hι (happ.term_hasAnalyticSingularityType j)
  have hanti : Antitone (fun j y => U j (ι y)) := fun i j hij y =>
    happ.term_antitone (ι y) hij
  obtain ⟨hτ, _, hlimη⟩ :=
    AnalyticAntitoneBigIGoodLimit.exists_iGood_native_model_limit_of_analytic_antitone_uniform_mass
      omegaV η hbig hv hA hanti hb hbound
  let τ := ⨅ j, singularityEnvelope η.val (fun y => U j (ι y))
  obtain ⟨C, hC, hadm, _, _, _, _⟩ :=
    AnalyticRestrictedApproximantUniformMass.exists_admissible_background_uniform_positive_restricted_mass
      omegaV happ hι hgeneric
  obtain ⟨D, hD, hsemi⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul omegaV (-η)
  have hCD : 0 < C + D := add_pos hC hD
  let γ := KahlerBackground.smul hCD omegaV
  have hdiff : γ.form - η = (-η + D • omegaV.form) + C • omegaV.form := by
    dsimp only [γ, KahlerBackground.smul_form]
    module
  have hdiffSemi : (γ.form - η).val.IsSemipositive := by
    rw [hdiff]
    intro e z hz v
    exact add_nonneg (hsemi e z hz v)
      (KahlerDomination.isSemipositive_smul omegaV.isSemipositive hC.le e z hz v)
  have henlarge {v : V → EReal} (hp : IsThetaPshPotential η.val v) :
      IsThetaPshPotential γ.form.val v := by
    simpa only [add_sub_cancel] using
      LocalPotentials.isThetaPshPotential_add_of_semipositive hp hdiffSemi
  have hτγ : IsThetaPshPotential γ.form.val τ := henlarge hτ.plurisubharmonic
  have hUγ (j : ℕ) : IsThetaPshPotential γ.form.val (fun y => U j (ι y)) := henlarge (hv j)
  have hadmγ : IsAdmissibleTraceBackground hι omega θ ε γ.form := by
    refine ⟨γ.isKahler, fun j => ?_⟩
    have hform : γ.form - ClosedRealOneOneForm.pullback hι (θ + ε j • omega.form) =
        (C • omegaV.form - ClosedRealOneOneForm.pullback hι (θ + ε j • omega.form)) +
          D • omegaV.form := by
      dsimp only [γ, KahlerBackground.smul_form]
      module
    change (γ.form - ClosedRealOneOneForm.pullback hι (θ + ε j • omega.form)).val.IsSemipositive
    rw [hform]
    intro e z hz v
    exact add_nonneg (hadm.2 j e z hz v)
      (KahlerDomination.isSemipositive_smul omegaV.isSemipositive hD.le e z hz v)
  have hlimγ := (SingularNativeCommonBackground.tendsto_native_iff_common_backgrounds
    omegaV η γ.form hbig (isBigClass_kahler γ) atTop hv hτ.plurisubharmonic hUγ hτγ).mp hlimη
  exact ⟨τ, ⟨hgeneric, θ, ε, U, happ, γ, hadmγ, hτγ, hUγ, hlimγ⟩,
    hτ.plurisubharmonic, hτ.positive_mass⟩

end Domain

/-! ### Source `def:traceop2`, the two observations, on every resolution target -/

section Resolution

open SGPT.Trace.Trace2Resolution SourceTraceRepresentativeDefinition

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [CompactSpace X] {Y : ClosedIrreducibleAnalyticSubvariety n X}

/-- **Source `def:traceop2`, second observation, for an arbitrary irreducible `Y` (read on any
resolution target `Y'`).** If `θ_φ` is a Kähler current (`θ - δω + dd^c φ ≥ 0`, `δ > 0`, `ω`
Kähler) and `ν(φ, Y) = 0`, then `Tr^θ_Y(φ)` is defined: some trace operator of `φ` along `Y` lies
in `PSH(Y', θ|_{Y'})_{>0}`. -/
theorem hasPositiveSourceTraceAlong_of_kahlerCurrent (R : ResolutionTarget Y)
    (omega₀ omega : KahlerBackground n X) (omegaV : KahlerBackground Y.dim R.V)
    {θ : ClosedRealOneOneForm n X} {u : X → EReal} {δ : ℝ} (hδ : 0 < δ)
    (hu : IsThetaPshPotential (θ - δ • omega.form).val u)
    (hν : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n X).sourceGenericLelong u Y.carrier = 0) :
    HasPositiveSourceTraceAlong omega₀ omegaV R.contMDiff θ u := by
  have hgeneric : sourceGenericLelongNumber (n := n) R.ι u = 0 :=
    (sourceGenericLelongNumber_eq_sourceGenericLelong R.isResolutionOf.range_eq u).trans hν
  by_cases hn : n = 0
  · obtain ⟨τ, hT⟩ := SGPT.TraceOperations.exists_sourceTrace_of_globalQuasiPshPotential
      Y.dim_le omega₀ omegaV hu.quasiPshPotential R.contMDiff hgeneric
    exact hasPositiveSourceTraceAlong_of_dim_zero Y.dim_le hn θ hT
  apply (hasPositiveSourceTraceAlong_iff_auxiliary_choices Y.dim_le omega omega₀ omegaV omegaV
    R.contMDiff θ u).mp
  apply (hasPositiveSourceTraceAlong_iff_native hn omega omegaV R.contMDiff θ u).mpr
  exact hasPositiveTraceRepresentativeAlong_of_current_margin omega omegaV R.contMDiff
    (fun w => diagonalPotentialMass_pullback_kahler_pos R w) hδ hu
    ((nativeGeneric_zero_iff_source hn R.ι u).mpr hgeneric)

/-- **Source `def:traceop2`, first observation, for an arbitrary irreducible `Y` (read on any
resolution target `Y'`).** If `φ ∈ PSH(X, θ)` and `ν(φ, Y) = 0`, then for every Kähler form `ω`
on `X` the trace operator `Tr^{θ+ω}_Y(φ)` is defined. -/
theorem hasPositiveSourceTraceAlong_add_kahler (R : ResolutionTarget Y)
    (omega₀ omega : KahlerBackground n X) (omegaV : KahlerBackground Y.dim R.V)
    {θ : ClosedRealOneOneForm n X} {u : X → EReal} (hu : IsThetaPshPotential θ.val u)
    (hν : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n X).sourceGenericLelong u Y.carrier = 0) :
    HasPositiveSourceTraceAlong omega₀ omegaV R.contMDiff (θ + omega.form) u := by
  apply hasPositiveSourceTraceAlong_of_kahlerCurrent R omega₀ omega omegaV zero_lt_one _ hν
  simpa only [one_smul, add_sub_cancel_right] using hu

end Resolution

end SGPT.Trace.RIsoB

end
