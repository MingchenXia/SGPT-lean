import SGPT.Trace.RIsoBTraceResolutionDomain
import SGPT.Trace.TraceMass
import SGPT.Trace.Trace2Mass
import SGPT.Foundations.Analysis.Pending.NormalizedTraceFixedPotentialPerturbation

/-!
# `ex:tracedefinedposmass` for an arbitrary irreducible `Y`

Source `ex:tracedefinedposmass` (`chapter_trace.tex`): for `φ ∈ PSH(X, θ)` with `ν(φ, Y) = 0`,
`∫_Ỹ (θ|_Ỹ + dd^c Tr^θ_Y(φ))^{dim Y}` (`0` if `Tr^θ_Y(φ)` is not defined) is
`lim_{ε ↘ 0} ∫_Ỹ (θ|_Ỹ + εω|_Ỹ + dd^c Tr^{θ+εω}_Y(φ))^{dim Y}`; if this limit is positive,
`Tr^θ_Y(φ)` is defined and its mass is the limit.

The existing proof (`SGPT.Trace.tendsto_sourceTraceMass_add_smul_right`, from
`NormalizedTraceFixedPotentialRightLimit`) needs `ι^*ω` Kähler on the target. Here the target is
an arbitrary resolution target `(Y', ι)` of `Y`, where `κ = ι^*ω` is only semipositive (of
positive volume, `RIsoB.diagonalPotentialMass_pullback_kahler_pos`). The proof squeezes the
masses between Kähler perturbations on `Y'`: with `ω'` a Kähler form of `Y'` and `C` such that
`C ω' - κ ≥ 0`,

* `ε ↦ ∫ (θ|_{Y'} + εκ)_{Tr^{θ+εω}}^k` is nondecreasing (`numericalTraceMass_add_smul_mono`), and
  bounded below by the mass of `Tr^θ_Y(φ)` (`0` if undefined);
* `W_j = P_{θ|_{Y'} + s_j ω'}[Tr^{θ + (s_j/C) ω}_Y(φ)]` (`s_j ↘ 0`) are decreasing models and
  `𝓘`-models in Kähler-perturbed backgrounds of `Y'` dominating the masses at `ε = s_j / C`; by
  `IEnvelopeVaryingBackgroundModelInfimum` / `VaryingBackgroundIModelGlobalClass` (`prop:vol_limit_model`
  with a genuine Kähler form `ω'`) their masses converge to the mass of `U = inf_j W_j`, and if
  that is positive, `U` is a trace operator of `φ` in `PSH(Y', θ|_{Y'})_{>0}`, so `Tr^θ_Y(φ)` is
  defined with mass `∫ θ_U^k`.

## Main results

* `tendsto_numericalTraceMass_add_smul_right` (native, any target whose Kähler pullbacks have
  positive volume).
* `tendsto_sourceTraceMass_add_smul_right`, `hasPositiveSourceTraceAlong_of_tendsto_pos`:
  source `ex:tracedefinedposmass` on every resolution target of every irreducible `Y`, all
  ambient dimensions.
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
  SGPT.Foundations.Analysis.FirstPass.IEnvelope
  SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.DiagonalMass
  SGPT.Foundations.Analysis.Pending.TraceRepresentativeConstruction
  SGPT.Foundations.Analysis.Pending.PositiveNormalizedTrace
  SGPT.Foundations.Analysis.Pending.NumericalTraceMass
  SGPT.Foundations.Analysis.Pending.NormalizedTraceBackgroundMonotonicity
  SGPT.Foundations.Analysis.Pending.IEnvelopeVaryingBackgroundModelInfimum
  SGPT.Foundations.Analysis.Pending.VaryingBackgroundIModelGlobalClass
  SGPT.Foundations.Analysis.Pending.SingularGlobalPOrder
  SGPT.Foundations.Analysis.Pending.IGoodPositiveBackgroundIndependence

section Native

variable {n k : ℕ} {M V : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]

/-- Positive volume of all Kähler pullbacks (true on every resolution target). -/
def PullbackKahlerVolumePos {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι) : Prop :=
  ∀ w : KahlerBackground n M,
    0 < diagonalPotentialMass (ClosedRealOneOneForm.pullback hι w.form) (fun _ => 0)
      ((LocalPotentials.isThetaPshPotential_zero_iff _).mpr
        (ClosedRealOneOneForm.pullback_isSemipositive hι w.isSemipositive))

omit [CompactSpace M] [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V] in
private theorem pullback_add_form {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (a b : ClosedRealOneOneForm n M) :
    ClosedRealOneOneForm.pullback hι (a + b) =
      ClosedRealOneOneForm.pullback hι a + ClosedRealOneOneForm.pullback hι b := by
  apply ClosedRealOneOneForm.ext
  intro e z
  ext v
  rfl

omit [CompactSpace M] [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V] in
private theorem pullback_add_smul_split {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (θ w : ClosedRealOneOneForm n M) (a b : ℝ) :
    ClosedRealOneOneForm.pullback hι (θ + b • w) =
      ClosedRealOneOneForm.pullback hι (θ + a • w) +
        ClosedRealOneOneForm.pullback hι ((b - a) • w) := by
  rw [← pullback_add_form hι]
  congr 1
  module

omit [CompactSpace M] [BorelSpace V] [ConnectedSpace V] in
private theorem massCongrForm {α β : ClosedRealOneOneForm k V} (h : α = β) {v : V → EReal}
    (hα : IsThetaPshPotential α.val v) (hβ : IsThetaPshPotential β.val v) :
    diagonalPotentialMass α v hα = diagonalPotentialMass β v hβ := by
  subst h
  rfl

omit [CompactSpace M] [ConnectedSpace V] in
/-- Mass comparison across a semipositive enlargement of the background: if `v ≤ w`,
`v ∈ PSH(α)`, `w ∈ PSH(α + σ)` with `σ ≥ 0`, then `∫ α_v^k ≤ ∫ (α + σ)_w^k`. -/
theorem diagonalPotentialMass_le_of_le_add_semipositive (omegaV : KahlerBackground k V)
    {α σ : ClosedRealOneOneForm k V} (hσ : σ.val.IsSemipositive) {v w : V → EReal}
    (hv : IsThetaPshPotential α.val v) (hw : IsThetaPshPotential (α + σ).val w) (hvw : v ≤ w) :
    diagonalPotentialMass α v hv ≤ diagonalPotentialMass (α + σ) w hw := by
  have hv' : IsThetaPshPotential (α + σ).val v :=
    LocalPotentials.isThetaPshPotential_add_of_semipositive hv hσ
  have h1 : diagonalPotentialMass α v hv ≤ diagonalPotentialMass (α + (1 : ℝ) • σ) v
      (by simpa only [one_smul] using hv') :=
    AmbientMassBackgroundMonotone.diagonalPotentialMass_le_add_smul hσ one_pos hv _
  have h1' : diagonalPotentialMass (α + (1 : ℝ) • σ) v (by simpa only [one_smul] using hv') =
      diagonalPotentialMass (α + σ) v hv' := massCongrForm (by rw [one_smul]) _ _
  calc diagonalPotentialMass α v hv ≤ diagonalPotentialMass (α + σ) v hv' := h1.trans_eq h1'
    _ ≤ diagonalPotentialMass (α + σ) w hw :=
      SGPT.Foundations.Analysis.Pending.diagonalPotentialMass_mono_of_kahler omegaV hv' hw
        (MoreSingularOn.of_le fun x _ => hvw x)

/-- The normalized traces with positive perturbations are defined. -/
theorem hasPositiveTraceRepresentativeAlong_add_smul (omega : KahlerBackground n M)
    (omegaV : KahlerBackground k V) {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (hvol : PullbackKahlerVolumePos hι) (θ : ClosedRealOneOneForm n M) {u : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (hgeneric : (⨅ y : V, lelongNumber (n := n) u (ι y)) = 0)
    {r : ℝ} (hr : 0 < r) :
    HasPositiveTraceRepresentativeAlong omega omegaV hι (θ + r • omega.form) u :=
  hasPositiveTraceRepresentativeAlong_of_current_margin omega omegaV hι hvol hr
    (by simpa only [add_sub_cancel_right] using hu) hgeneric

/-- The masses `∫ (θ|_V + aκ)_{Tr^{θ+aω}}^k` are nondecreasing in `a` (with value `0` when
undefined). -/
theorem numericalTraceMass_add_smul_mono (omega : KahlerBackground n M)
    (omegaV : KahlerBackground k V) {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (θ : ClosedRealOneOneForm n M) (u : M → EReal) {a b : ℝ} (hab : a ≤ b) :
    numericalTraceMass omega omegaV hι (θ + a • omega.form) u ≤
      numericalTraceMass omega omegaV hι (θ + b • omega.form) u := by
  classical
  by_cases hdA : HasPositiveTraceRepresentativeAlong omega omegaV hι (θ + a • omega.form) u
  swap
  · simp only [numericalTraceMass, dif_neg hdA]
    exact bot_le
  have hdB : HasPositiveTraceRepresentativeAlong omega omegaV hι (θ + b • omega.form) u := by
    obtain ⟨τ, hT, hτ, hpos⟩ := hdA
    have hsemi : (ClosedRealOneOneForm.pullback hι ((b - a) • omega.form)).val.IsSemipositive :=
      ClosedRealOneOneForm.pullback_isSemipositive hι
        (KahlerDomination.isSemipositive_smul omega.isSemipositive (sub_nonneg.mpr hab))
    have hform := pullback_add_smul_split hι θ omega.form a b
    have hτ' : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι (θ + b • omega.form)).val τ :=
      hform ▸ LocalPotentials.isThetaPshPotential_add_of_semipositive hτ hsemi
    refine ⟨τ, hT, hτ', ?_⟩
    have hm := diagonalPotentialMass_le_of_le_add_semipositive omegaV hsemi hτ
      (hform ▸ hτ') le_rfl
    unfold HasPositivePotentialMass at hpos ⊢
    refine hpos.trans_le (hm.trans_eq ?_)
    congr 1
    exact hform.symm
  have hsemiX : (θ + b • omega.form - (θ + a • omega.form)).val.IsSemipositive := by
    rw [show θ + b • omega.form - (θ + a • omega.form) = (b - a) • omega.form by module]
    exact KahlerDomination.isSemipositive_smul omega.isSemipositive (sub_nonneg.mpr hab)
  have hAB := normalizedTraceAlong_le_of_semipositive_difference omega omega omegaV omegaV hι
    (θ + a • omega.form) (θ + b • omega.form) u hsemiX hdA hdB
  have hsemi : (ClosedRealOneOneForm.pullback hι ((b - a) • omega.form)).val.IsSemipositive :=
    ClosedRealOneOneForm.pullback_isSemipositive hι
      (KahlerDomination.isSemipositive_smul omega.isSemipositive (sub_nonneg.mpr hab))
  have hform := pullback_add_smul_split hι θ omega.form a b
  have hA := (normalizedTraceAlong_models omega omegaV hι _ u hdA).1.plurisubharmonic
  have hB := (normalizedTraceAlong_models omega omegaV hι _ u hdB).1.plurisubharmonic
  have hm := diagonalPotentialMass_le_of_le_add_semipositive omegaV hsemi hA (hform ▸ hB) hAB
  simp only [numericalTraceMass, dif_pos hdA, dif_pos hdB]
  refine hm.trans_eq ?_
  congr 1
  exact hform.symm

/-- **Source `ex:tracedefinedposmass`, the formula, for targets whose Kähler pullbacks have
positive volume (native form).** For `u ∈ PSH(M, θ)` with vanishing generic Lelong number along
`ι`, the mass of `Tr^θ_Y(u)` (`0` if undefined) is the right limit, as `ε ↘ 0`, of the masses of
`Tr^{θ+εω}_Y(u)`. No Kähler-pullback hypothesis. -/
theorem tendsto_numericalTraceMass_add_smul_right (omega : KahlerBackground n M)
    (omegaV : KahlerBackground k V) {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (hvol : PullbackKahlerVolumePos hι) (θ : ClosedRealOneOneForm n M) {u : M → EReal}
    (hu : IsThetaPshPotential θ.val u)
    (hgeneric : (⨅ y : V, lelongNumber (n := n) u (ι y)) = 0) :
    Tendsto (fun ε : ℝ => numericalTraceMass omega omegaV hι (θ + ε • omega.form) u)
      (𝓝[>] 0) (𝓝 (numericalTraceMass omega omegaV hι θ u)) := by
  classical
  set L0 := numericalTraceMass omega omegaV hι θ u with hL0
  have h0form : θ + (0 : ℝ) • omega.form = θ := by rw [zero_smul, add_zero]
  -- monotonicity and the lower bound
  have hmono : ∀ {a b : ℝ}, a ≤ b → numericalTraceMass omega omegaV hι (θ + a • omega.form) u ≤
      numericalTraceMass omega omegaV hι (θ + b • omega.form) u := fun hab =>
    numericalTraceMass_add_smul_mono omega omegaV hι θ u hab
  have hlower : ∀ ε : ℝ, 0 < ε → L0 ≤ numericalTraceMass omega omegaV hι (θ + ε • omega.form) u := by
    intro ε hε
    have h := hmono hε.le
    rwa [h0form] at h
  -- the comparison constant `C`: `C ω_V - ι^*ω ≥ 0`
  let η := ClosedRealOneOneForm.pullback hι θ
  let κ := ClosedRealOneOneForm.pullback hι omega.form
  obtain ⟨C, hC, hsemiC⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul omegaV (-κ)
  -- the sequence of perturbations
  let s : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have hspos : ∀ j, 0 < s j := fun j => Nat.one_div_pos_of_nat
  have hsanti : Antitone s := fun i j hij => by
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right hij 1
  have hslim : Tendsto s atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let ε : ℕ → ℝ := fun j => s j / C
  have hεpos : ∀ j, 0 < ε j := fun j => div_pos (hspos j) hC
  have hεanti : Antitone ε := fun i j hij => div_le_div_of_nonneg_right (hsanti hij) hC.le
  have hdef : ∀ j, HasPositiveTraceRepresentativeAlong omega omegaV hι
      (θ + ε j • omega.form) u := fun j =>
    hasPositiveTraceRepresentativeAlong_add_smul omega omegaV hι hvol θ hu hgeneric (hεpos j)
  let T : ℕ → V → EReal := fun j =>
    normalizedTraceAlong omega omegaV hι (θ + ε j • omega.form) u (hdef j)
  have hTmod : ∀ j, IsModelPotential (ClosedRealOneOneForm.pullback hι (θ + ε j • omega.form))
      (T j) := fun j => (normalizedTraceAlong_models omega omegaV hι _ u (hdef j)).1
  have hTtrace : ∀ j, IsTraceRepresentativeAlong omega omegaV hι u (T j) := fun j =>
    isTraceRepresentativeAlong_normalizedTraceAlong omega omegaV hι _ u (hdef j)
  have hTanti : ∀ x, Antitone fun j => T j x := by
    intro x i j hij
    have hsemiX : (θ + ε i • omega.form - (θ + ε j • omega.form)).val.IsSemipositive := by
      rw [show θ + ε i • omega.form - (θ + ε j • omega.form) = (ε i - ε j) • omega.form by
        module]
      exact KahlerDomination.isSemipositive_smul omega.isSemipositive
        (sub_nonneg.mpr (hεanti hij))
    exact normalizedTraceAlong_le_of_semipositive_difference omega omega omegaV omegaV hι
      (θ + ε j • omega.form) (θ + ε i • omega.form) u hsemiX (hdef j) (hdef i) x
  -- the Kähler-perturbed backgrounds `β_j = ι^*θ + s_j ω_V` dominate `ι^*(θ + ε_j ω)`
  let σ : ℕ → ClosedRealOneOneForm k V := fun j => (s j / C) • (-κ + C • omegaV.form)
  have hσ : ∀ j, (σ j).val.IsSemipositive := fun j =>
    KahlerDomination.isSemipositive_smul hsemiC (hεpos j).le
  have hβeq : ∀ j, ClosedRealOneOneForm.pullback hι (θ + ε j • omega.form) + σ j =
      η + s j • omegaV.form := by
    intro j
    rw [NefCoreKahlerCurrent.pullback_add_smul]
    simp only [σ, ε]
    rw [smul_add, smul_neg, smul_smul, div_mul_cancel₀ (s j) hC.ne']
    abel
  have hTβ : ∀ j, IsThetaPshPotential (η + s j • omegaV.form).val (T j) := fun j =>
    hβeq j ▸ LocalPotentials.isThetaPshPotential_add_of_semipositive (hTmod j).plurisubharmonic
      (hσ j)
  have hmassTβ : ∀ j, diagonalPotentialMass _ (T j) (hTmod j).plurisubharmonic ≤
      diagonalPotentialMass (η + s j • omegaV.form) (T j) (hTβ j) := fun j =>
    (diagonalPotentialMass_le_of_le_add_semipositive omegaV (hσ j) (hTmod j).plurisubharmonic
      ((hβeq j).symm ▸ hTβ j) le_rfl).trans_eq (massCongrForm (hβeq j) _ _)
  have hposβ : ∀ j, HasPositivePotentialMass (η + s j • omegaV.form) (T j) (hTβ j) := fun j =>
    (hTmod j).positive_mass.trans_le (hmassTβ j)
  -- `W_j = P_{β_j}[T_j]`: models and `𝓘`-models, decreasing, trace operators
  let W : ℕ → V → EReal := fun j => singularityEnvelope (η + s j • omegaV.form).val (T j)
  have hgood : ∀ j, IGoodWith (η + s j • omegaV.form) (T j) (hTβ j) := by
    intro j
    obtain ⟨σ0, hσ0, hg⟩ :=
      TraceRepresentativeIGood.iGood_of_isTraceRepresentativeAlong omegaV hι (hTtrace j)
    exact (iGoodWith_iff_positive_common_potential omegaV σ0 _ hσ0 (hTβ j) hg.positiveMass
      (hposβ j)).mp hg
  have hWI : ∀ j, IsIModelPotential (η + s j • omegaV.form).val (W j) := by
    intro j
    have hI := iSingularityEnvelope_isIModelPotential (η + s j • omegaV.form).val
      (η + s j • omegaV.form).property.1 (η + s j • omegaV.form).property.2
      (hTβ j).1.hasSmoothLocalPotentials (T j) (hTβ j)
    have heqI : W j = iSingularityEnvelope (η + s j • omegaV.form).val (T j) :=
      (hgood j).envelope_eq
    rw [heqI]
    exact hI
  have hWmass : ∀ j, diagonalPotentialMass (η + s j • omegaV.form) (W j)
      (hWI j).plurisubharmonic = diagonalPotentialMass (η + s j • omegaV.form) (T j) (hTβ j) :=
    fun j => singularityEnvelopeMassPreserving omegaV _ (T j) (hTβ j) (hWI j).plurisubharmonic
  have hWmod : ∀ j, IsModelPotential (η + s j • omegaV.form) (W j) := by
    intro j
    refine ⟨(hWI j).plurisubharmonic, ?_, (hWmass j).symm ▸ hposβ j⟩
    have heqI : W j = iSingularityEnvelope (η + s j • omegaV.form).val (T j) :=
      (hgood j).envelope_eq
    rw [heqI]
    exact (singularityEnvelope_iSingularityEnvelope (η + s j • omegaV.form).val
      (η + s j • omegaV.form).property.1 (η + s j • omegaV.form).property.2
      (hTβ j).1.hasSmoothLocalPotentials (T j) (hTβ j)).symm
  have hWanti : Antitone W := fun i j hij =>
    TraceFreeLimit.singularityEnvelope_antitone omegaV.isSemipositive hsanti hTanti hij
  have hWtrace : ∀ j, IsTraceRepresentativeAlong omega omegaV hι u (W j) := fun j =>
    TraceRepresentativeGlobalPClass.isTraceRepresentativeAlong_of_sourcePEquivalent omegaV hι
      (hTtrace j)
      (SingularGlobalPEnvelopeBridge.sourcePEquivalent_singularityEnvelope omegaV _ (hTβ j))
  -- the decreasing limit `U = inf W_j` (prop:vol_limit_model with the Kähler form `ω_V`)
  have hU := isThetaPshPotential_iInf_varying_models omegaV η hsanti hslim hWmod hWanti
  have hlim := tendsto_diagonalPotentialMass_iInf_varying_models omegaV η hspos hsanti hslim
    hWmod hWanti
  have hUL : diagonalPotentialMass η (⨅ j, W j) hU ≤ L0 := by
    by_cases hpos : 0 < diagonalPotentialMass η (⨅ j, W j) hU
    · have heq : ∀ j, SourcePEquivalent (n := k) (W j) (W 0) := fun j =>
        TraceRepresentativeAllChoices.sourcePEquivalent_of_isTraceRepresentativeAlong omegaV
          omegaV hι (hWtrace j) (hWtrace 0)
      have hclass := sourcePEquivalent_iInf_of_varying_iModels omegaV η hspos hsanti hslim hWmod
        hWI hWanti hpos heq
      have hTU : IsTraceRepresentativeAlong omega omegaV hι u (⨅ j, W j) :=
        TraceRepresentativeGlobalPClass.isTraceRepresentativeAlong_of_sourcePEquivalent omegaV hι
          (hWtrace 0) hclass.symm
      have hd : HasPositiveTraceRepresentativeAlong omega omegaV hι θ u := ⟨_, hTU, hU, hpos⟩
      exact (numericalTraceMass_eq_of_positive_reader omegaV omegaV hι θ u hd hTU hU hpos).ge
    · rw [not_lt, nonpos_iff_eq_zero] at hpos
      rw [hpos]
      exact bot_le
  -- the squeeze
  have hdom : ∀ j, numericalTraceMass omega omegaV hι (θ + ε j • omega.form) u ≤
      diagonalPotentialMass (η + s j • omegaV.form) (W j) (hWmod j).plurisubharmonic := by
    intro j
    simp only [numericalTraceMass, dif_pos (hdef j)]
    exact (hmassTβ j).trans (hWmass j).ge
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact ha.trans_le (hlower t ht)
  · obtain ⟨j, hj⟩ := (hlim.eventually (gt_mem_nhds (hUL.trans_lt ha))).exists
    filter_upwards [Ioc_mem_nhdsGT (hεpos j)] with t ht
    exact ((hmono ht.2).trans (hdom j)).trans_lt hj

end Native

/-! ### Source `ex:tracedefinedposmass` on every resolution target -/

section Resolution

open SGPT.Trace.Trace2Resolution SourceTraceRepresentativeDefinition

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [CompactSpace X] {Y : ClosedIrreducibleAnalyticSubvariety n X}

omit [CompactSpace X] in
/-- Every resolution target has Kähler pullbacks of positive volume. -/
theorem pullbackKahlerVolumePos (R : ResolutionTarget Y) :
    PullbackKahlerVolumePos (M := X) R.contMDiff :=
  fun w => diagonalPotentialMass_pullback_kahler_pos R w

/-- **Source `ex:tracedefinedposmass`, the formula, for an arbitrary irreducible `Y` (read on any
resolution target `Y'`).** For `φ ∈ PSH(X, θ)` with `ν(φ, Y) = 0` and every Kähler form `ω` on
`X`: `∫_{Y'} (θ|_{Y'} + dd^c Tr^θ_Y(φ))^{dim Y}` (`0` if `Tr^θ_Y(φ)` is not defined) is the limit,
as `ε ↘ 0`, of `∫_{Y'} (θ|_{Y'} + εω|_{Y'} + dd^c Tr^{θ+εω}_Y(φ))^{dim Y}`. All ambient
dimensions. -/
theorem tendsto_sourceTraceMass_add_smul_right (R : ResolutionTarget Y)
    (omega₀ omega : KahlerBackground n X) (omegaV : KahlerBackground Y.dim R.V)
    (θ : ClosedRealOneOneForm n X) {u : X → EReal} (hu : IsThetaPshPotential θ.val u)
    (hν : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n X).sourceGenericLelong u Y.carrier = 0) :
    Tendsto (fun ε : ℝ => sourceTraceMass omega₀ omegaV R.contMDiff (θ + ε • omega.form) u)
      (𝓝[>] 0) (𝓝 (sourceTraceMass omega₀ omegaV R.contMDiff θ u)) := by
  by_cases hn : n = 0
  · exact SGPT.Trace.Trace2Mass.tendsto_sourceTraceMass_add_smul_right_of_dim_zero Y.dim_le hn
      omega₀ omega omegaV R.contMDiff θ hu
  have hgeneric : sourceGenericLelongNumber (n := n) R.ι u = 0 :=
    (sourceGenericLelongNumber_eq_sourceGenericLelong R.isResolutionOf.range_eq u).trans hν
  have h := tendsto_numericalTraceMass_add_smul_right omega omegaV R.contMDiff
    (pullbackKahlerVolumePos R) θ hu ((nativeGeneric_zero_iff_source hn R.ι u).mpr hgeneric)
  simp_rw [sourceTraceMass_eq_of_choices Y.dim_le omega₀ omega omegaV omegaV R.contMDiff,
    sourceTraceMass_eq_numericalTraceMass Y.dim_le hn omega omegaV R.contMDiff]
  exact h

/-- **Source `ex:tracedefinedposmass` for an arbitrary irreducible `Y` (read on any resolution
target `Y'`).** If the limit of the masses of `Tr^{θ+εω}_Y(φ)` as `ε ↘ 0` is positive, then
`Tr^θ_Y(φ)` is defined and its mass is that limit. -/
theorem hasPositiveSourceTraceAlong_of_tendsto_pos (R : ResolutionTarget Y)
    (omega₀ omega : KahlerBackground n X) (omegaV : KahlerBackground Y.dim R.V)
    (θ : ClosedRealOneOneForm n X) {u : X → EReal} (hu : IsThetaPshPotential θ.val u)
    (hν : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n X).sourceGenericLelong u Y.carrier = 0)
    {L : ℝ≥0∞}
    (hL : Tendsto (fun ε : ℝ => sourceTraceMass omega₀ omegaV R.contMDiff (θ + ε • omega.form) u)
      (𝓝[>] 0) (𝓝 L)) (hLpos : 0 < L) :
    HasPositiveSourceTraceAlong omega₀ omegaV R.contMDiff θ u ∧
      sourceTraceMass omega₀ omegaV R.contMDiff θ u = L := by
  have hlim := tendsto_sourceTraceMass_add_smul_right R omega₀ omega omegaV θ hu hν
  have heq : sourceTraceMass omega₀ omegaV R.contMDiff θ u = L := tendsto_nhds_unique hlim hL
  exact ⟨(hasPositiveSourceTraceAlong_iff_sourceTraceMass_pos Y.dim_le omega₀ omegaV R.contMDiff
    θ u).mpr (heq ▸ hLpos), heq⟩

end Resolution

end SGPT.Trace.RIsoB

end
