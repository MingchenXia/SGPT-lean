import SGPT.Okounkov.SourceTraceChoices
import SGPT.Foundations.Analysis.Pending.NaturalSourceTraceExistenceAllDimensions
import SGPT.Foundations.Analysis.Pending.ActualLelongPositiveScaling
import SGPT.Foundations.Analysis.Pending.TraceAdditionNaturalDomain
import SGPT.Foundations.Analysis.Pending.TracePositiveRealHomogeneity
import SGPT.Foundations.Analysis.Pending.TraceRepresentativeMaximum
import SGPT.Foundations.Analysis.Pending.GlobalQuasiPshTraceExistence
import SGPT.PSH.NativeThetaCompactMaximum

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology Manifold ENNReal ContDiff

namespace SGPT.TraceOperations

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.Pending
open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  FirstPass.QuasiEquisingularApproximation FirstPass.BlowupSequences FirstPass.IEnvelope
  SourceTraceRepresentativeDefinition
  TraceRepresentativeConstruction SingularGlobalPOrder SquaredLogLelongSourceNormalization
  NaturalSubmanifoldSourceTraceDefinition

/-- The literal source generic growth reader scales by every positive REAL,
with its zero-dimensional convention and its infinite values retained. -/
theorem sourceGenericLelongNumber_pos_smul
    {n : ℕ} {M Y : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [Nonempty Y]
    (ι : Y → M) (u : M → EReal) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    sourceGenericLelongNumber (n := n) ι (fun x => (ℓ : EReal) * u x) =
      ENNReal.ofReal ℓ * sourceGenericLelongNumber (n := n) ι u := by
  by_cases hn : n = 0
  · subst n
    simp [sourceGenericLelongNumber, squaredLogLelongNumber]
  · have htwo : 2 * sourceGenericLelongNumber (n := n) ι
        (fun x => (ℓ : EReal) * u x) =
        2 * (ENNReal.ofReal ℓ * sourceGenericLelongNumber (n := n) ι u) := by
      calc
        _ = ⨅ y : Y, lelongNumber (n := n) (fun x => (ℓ : EReal) * u x) (ι y) :=
          (nativeGeneric_eq_two_mul_source hn ι _).symm
        _ = ENNReal.ofReal ℓ * ⨅ y : Y, lelongNumber (n := n) u (ι y) := by
          simp_rw [ActualLelongPositiveScaling.lelongNumber_smul_eq hℓ,
            ← ENNReal.mul_iInf_of_ne (ENNReal.ofReal_pos.mpr hℓ).ne' ENNReal.ofReal_ne_top]
        _ = _ := by rw [nativeGeneric_eq_two_mul_source hn]; ac_rfl
    exact le_antisymm
      ((ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).mp htwo.le)
      ((ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).mp htwo.symm.le)

section SourceReaders

variable {n k : ℕ} {M Y : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel k) Y] [IsComplexManifold k Y]
  [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] [ConnectedSpace Y]

private theorem sourceTrace_target_potential
    {omega : KahlerBackground n M} {omegaY : KahlerBackground k Y}
    {ι : Y → M} {hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι}
    {u : M → EReal} {τ : Y → EReal}
    (hT : IsSourceTraceRepresentativeAlong omega omegaY hι u τ) :
    ∃ β : KahlerBackground k Y, IsThetaPshPotential β.form.val τ := by
  obtain ⟨_hg, _θ, _ε, _U, _hU, β, _hadm, hτ, _hterms, _hlim⟩ := hT
  exact ⟨β, hτ⟩

private theorem sourceTrace_finite_of_target_zero (hk : k = 0)
    {omega : KahlerBackground n M} {omegaY : KahlerBackground k Y}
    {ι : Y → M} {hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι}
    {u : M → EReal} {τ : Y → EReal}
    (hT : IsSourceTraceRepresentativeAlong omega omegaY hι u τ) :
    ∀ y, τ y ≠ ⊤ ∧ τ y ≠ ⊥ := by
  subst k
  obtain ⟨β, hτ⟩ := sourceTrace_target_potential hT
  intro y
  exact ⟨hτ.1.quasiPlurisubharmonic.ne_top y,
    RooftopDimZero.ne_bot_of_locallyNondegenerate_of_dim_zero rfl hτ.2 y⟩

private theorem sourcePEquivalent_of_finite_of_target_zero (hk : k = 0)
    (omegaY : KahlerBackground k Y) {u v : Y → EReal}
    (hu : ∀ y, u y ≠ ⊤ ∧ u y ≠ ⊥) (hv : ∀ y, v y ≠ ⊤ ∧ v y ≠ ⊥) :
    SourcePEquivalent (n := k) u v := by
  subst k
  let : DiscreteTopology Y := discreteTopology_iff_isOpen_singleton.mpr
    (RooftopDimZero.isOpen_singleton_of_dim_zero rfl)
  let : Subsingleton Y := subsingleton_of_preconnected_totallyDisconnected
  let y : Y := Classical.arbitrary Y
  have huco : ((u y).toReal : EReal) = u y := EReal.coe_toReal (hu y).1 (hu y).2
  have hvco : ((v y).toReal : EReal) = v y := EReal.coe_toReal (hv y).1 (hv y).2
  have hups : IsThetaPshPotential omegaY.form.val u :=
    RooftopDimZero.isThetaPshPotential_of_dim_zero rfl
      (LocalPotentials.closedRealOneOne_hasLocalPotentials omegaY.form)
      (fun z => (hu z).1) (fun z => (hu z).2)
  have hvps : IsThetaPshPotential omegaY.form.val v :=
    RooftopDimZero.isThetaPshPotential_of_dim_zero rfl
      (LocalPotentials.closedRealOneOne_hasLocalPotentials omegaY.form)
      (fun z => (hv z).1) (fun z => (hv z).2)
  have hmore : SameSingularityTypeOn u v Set.univ := by
    constructor
    · refine ⟨(u y).toReal - (v y).toReal, ?_⟩
      intro z _hz
      rw [Subsingleton.elim z y, ← huco, ← hvco, ← EReal.coe_add]
      exact_mod_cast (by linarith : (u y).toReal ≤
        (v y).toReal + ((u y).toReal - (v y).toReal))
    · refine ⟨(v y).toReal - (u y).toReal, ?_⟩
      intro z _hz
      rw [Subsingleton.elim z y, ← huco, ← hvco, ← EReal.coe_add]
      exact_mod_cast (by linarith : (v y).toReal ≤
        (u y).toReal + ((v y).toReal - (u y).toReal))
  exact ⟨sourcePOrder_of_moreSingularOn omegaY omegaY.form omegaY.form hups hvps hmore.1,
    sourcePOrder_of_moreSingularOn omegaY omegaY.form omegaY.form hvps hups hmore.2⟩

variable [CompactSpace M]

/-- Original genuine global quasi-PSH and source generic zero internally
produce every source trace field, including ambient dimension zero. -/
theorem exists_sourceTrace_of_globalQuasiPshPotential (hk : k ≤ n)
    (omega : KahlerBackground n M) (omegaY : KahlerBackground k Y)
    {u : M → EReal} (hu : IsGlobalQuasiPshPotential (n := n) u)
    {ι : Y → M} (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (hgeneric : sourceGenericLelongNumber (n := n) ι u = 0) :
    ∃ τ : Y → EReal, IsSourceTraceRepresentativeAlong omega omegaY hι u τ := by
  by_cases hn : n = 0
  · subst n
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
    subst k
    obtain ⟨θ, hθ⟩ :=
      (GlobalQuasiPshKahlerBackground.isGlobalQuasiPshPotential_iff_exists_closed_background
        omega u).mp hu
    exact ⟨fun y => u (ι y),
      NaturalSourceTraceExistenceAllDimensions.sourceTrace_ordinaryRestriction_zero
        omega omegaY hθ hι⟩
  · have hzero := (nativeGeneric_zero_iff_source hn ι u).mpr hgeneric
    obtain ⟨τ, hT, _hmodel⟩ :=
      GlobalQuasiPshTraceExistence.exists_of_globalQuasiPshPotential omega omegaY hu hι hzero
    exact ⟨τ, (isSourceTraceRepresentativeAlong_iff_native hn omega omegaY hι u τ).mpr hT⟩

/-- The actual original ideal-order trace comparison also retains the
source's zero-dimensional ambient branch. -/
theorem sourcePOrder_of_iOrder_of_sourceTraceRepresentatives (hk : k ≤ n)
    {omega₀ omega₁ : KahlerBackground n M} (omegaY₀ omegaY₁ : KahlerBackground k Y)
    {ι : Y → M} (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    {u v : M → EReal} {τu τv : Y → EReal}
    (hTu : IsSourceTraceRepresentativeAlong omega₀ omegaY₀ hι u τu)
    (hTv : IsSourceTraceRepresentativeAlong omega₁ omegaY₁ hι v τv)
    (hI : IOrderOnManifold (n := n) u v) : SourcePOrder (n := k) τu τv := by
  by_cases hn : n = 0
  · subst n
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
    subst k
    exact (sourcePEquivalent_of_finite_of_target_zero rfl omegaY₀
      (sourceTrace_finite_of_target_zero rfl hTu)
      (sourceTrace_finite_of_target_zero rfl hTv)).1
  · exact TraceIdealOrderMonotonicity.sourcePOrder_of_iOrder_of_isTraceRepresentativeAlong
      omegaY₀ omegaY₁ hι
      ((isSourceTraceRepresentativeAlong_iff_native hn omega₀ omegaY₀ hι u τu).mp hTu)
      ((isSourceTraceRepresentativeAlong_iff_native hn omega₁ omegaY₁ hι v τv).mp hTv) hI

/-- Source addition retains arbitrary genuine auxiliary choices, all
dimensions and every actual full reader of the original sum. -/
theorem sourcePEquivalent_add_of_sourceTraceRepresentatives (hk : k ≤ n)
    {omega₀ omega₁ omega₂ : KahlerBackground n M}
    (omegaY₀ omegaY₁ omegaY₂ : KahlerBackground k Y)
    {ι : Y → M} (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    {u v : M → EReal} {τu τv τs : Y → EReal}
    (hTu : IsSourceTraceRepresentativeAlong omega₀ omegaY₀ hι u τu)
    (hTv : IsSourceTraceRepresentativeAlong omega₁ omegaY₁ hι v τv)
    (hTs : IsSourceTraceRepresentativeAlong omega₂ omegaY₂ hι (fun x => u x + v x) τs) :
    SourcePEquivalent (n := k) τs (fun y => τu y + τv y) := by
  by_cases hn : n = 0
  · subst n
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
    subst k
    apply sourcePEquivalent_of_finite_of_target_zero rfl omegaY₂
      (sourceTrace_finite_of_target_zero rfl hTs)
    intro y
    obtain ⟨huTop, huBot⟩ := sourceTrace_finite_of_target_zero rfl hTu y
    obtain ⟨hvTop, hvBot⟩ := sourceTrace_finite_of_target_zero rfl hTv y
    have huco : ((τu y).toReal : EReal) = τu y := EReal.coe_toReal huTop huBot
    have hvco : ((τv y).toReal : EReal) = τv y := EReal.coe_toReal hvTop hvBot
    rw [← huco, ← hvco, ← EReal.coe_add]
    exact ⟨EReal.coe_ne_top _, EReal.coe_ne_bot _⟩
  · exact TraceRepresentativeAddition.sourcePEquivalent_add_of_isTraceRepresentativeAlong
      omegaY₀ omegaY₁ omegaY₂ hι
      ((isSourceTraceRepresentativeAlong_iff_native hn omega₀ omegaY₀ hι u τu).mp hTu)
      ((isSourceTraceRepresentativeAlong_iff_native hn omega₁ omegaY₁ hι v τv).mp hTv)
      ((isSourceTraceRepresentativeAlong_iff_native hn omega₂ omegaY₂ hι
        (fun x => u x + v x) τs).mp hTs)

/-- Positive REAL source trace homogeneity, with no rationality or
positive-ambient-dimension restriction. -/
theorem sourcePEquivalent_pos_smul_of_sourceTraceRepresentatives (hk : k ≤ n)
    {omega₀ omega₁ : KahlerBackground n M}
    (omegaY₀ omegaY₁ : KahlerBackground k Y)
    {ι : Y → M} (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    {u : M → EReal} {τ τℓ : Y → EReal}
    (hT : IsSourceTraceRepresentativeAlong omega₀ omegaY₀ hι u τ)
    {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hTℓ : IsSourceTraceRepresentativeAlong omega₁ omegaY₁ hι
      (fun x => (ℓ : EReal) * u x) τℓ) :
    SourcePEquivalent (n := k) τℓ (fun y => (ℓ : EReal) * τ y) := by
  by_cases hn : n = 0
  · subst n
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
    subst k
    apply sourcePEquivalent_of_finite_of_target_zero rfl omegaY₁
      (sourceTrace_finite_of_target_zero rfl hTℓ)
    intro y
    obtain ⟨hTop, hBot⟩ := sourceTrace_finite_of_target_zero rfl hT y
    have hco : ((τ y).toReal : EReal) = τ y := EReal.coe_toReal hTop hBot
    rw [← hco, ← EReal.coe_mul]
    exact ⟨EReal.coe_ne_top _, EReal.coe_ne_bot _⟩
  · exact TracePositiveRealHomogeneity.sourcePEquivalent_pos_smul_of_isTraceRepresentativeAlong
      omegaY₀ omegaY₁ hι
      ((isSourceTraceRepresentativeAlong_iff_native hn omega₀ omegaY₀ hι u τ).mp hT)
      hℓ ((isSourceTraceRepresentativeAlong_iff_native hn omega₁ omegaY₁ hι
        (fun x => (ℓ : EReal) * u x) τℓ).mp hTℓ)

/-- Maximum uses the existing actual native full maximum producer; no
generic analytic-singularity closure theorem is reproved here. -/
theorem sourcePEquivalent_max_of_sourceTraceRepresentatives (hk : k ≤ n)
    {omega₀ omega₁ omega₂ : KahlerBackground n M}
    (omegaY₀ omegaY₁ omegaY₂ : KahlerBackground k Y)
    {ι : Y → M} (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    {u v : M → EReal} {τu τv τm : Y → EReal}
    (hTu : IsSourceTraceRepresentativeAlong omega₀ omegaY₀ hι u τu)
    (hTv : IsSourceTraceRepresentativeAlong omega₁ omegaY₁ hι v τv)
    (hTm : IsSourceTraceRepresentativeAlong omega₂ omegaY₂ hι
      (fun x => max (u x) (v x)) τm) :
    SourcePEquivalent (n := k) τm (fun y => max (τu y) (τv y)) := by
  by_cases hn : n = 0
  · subst n
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
    subst k
    apply sourcePEquivalent_of_finite_of_target_zero rfl omegaY₂
      (sourceTrace_finite_of_target_zero rfl hTm)
    intro y
    rcases le_total (τu y) (τv y) with h | h
    · simpa only [max_eq_right h] using sourceTrace_finite_of_target_zero rfl hTv y
    · simpa only [max_eq_left h] using sourceTrace_finite_of_target_zero rfl hTu y
  · exact TraceRepresentativeMaximum.sourcePEquivalent_max_of_isTraceRepresentativeAlong
      omegaY₀ omegaY₁ omegaY₂ hι
      ((isSourceTraceRepresentativeAlong_iff_native hn omega₀ omegaY₀ hι u τu).mp hTu)
      ((isSourceTraceRepresentativeAlong_iff_native hn omega₁ omegaY₁ hι v τv).mp hTv)
      ((isSourceTraceRepresentativeAlong_iff_native hn omega₂ omegaY₂ hι
        (fun x => max (u x) (v x)) τm).mp hTm)

private theorem sourceGeneric_add_zero_of_sourceTraces
    {omega₀ omega₁ : KahlerBackground n M} (omegaY₀ omegaY₁ : KahlerBackground k Y)
    {ι : Y → M} (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    {u v : M → EReal} {τu τv : Y → EReal}
    (hTu : IsSourceTraceRepresentativeAlong omega₀ omegaY₀ hι u τu)
    (hTv : IsSourceTraceRepresentativeAlong omega₁ omegaY₁ hι v τv) :
    sourceGenericLelongNumber (n := n) ι (fun x => u x + v x) = 0 := by
  by_cases hn : n = 0
  · subst n
    simp [sourceGenericLelongNumber, squaredLogLelongNumber]
  · obtain ⟨_omega, hsum, _hchoices⟩ :=
      TraceAdditionNaturalDomain.exists_additive_trace_reader_with_all_choices
        omegaY₀ omegaY₁ omegaY₀ hι
        ((isSourceTraceRepresentativeAlong_iff_native hn omega₀ omegaY₀ hι u τu).mp hTu)
        ((isSourceTraceRepresentativeAlong_iff_native hn omega₁ omegaY₁ hι v τv).mp hTv)
    exact (nativeGeneric_zero_iff_source hn ι (fun x => u x + v x)).mp hsum.1

omit [CompactSpace M] in
private theorem nativeGlobal_of_sourceQPSH {u : M → EReal}
    (hu : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n M).IsQPSH u) :
    IsGlobalQuasiPshPotential (n := n) u := by
  obtain ⟨θ, hθ⟩ := hu
  exact ((SGPT.PSH.VariableComplexAtlas.isThetaPSH_iff_nativeThetaPotential θ u).mp hθ).quasiPshPotential

/-- Genuine ORIGINAL QPSH inputs and their two source generic-zero conditions
manufacture all four full trace witnesses, the sum/scalar domains and both
actual source P-equivalences. No trace, approximation or result certificate
is among the headline's inputs. -/
theorem exists_source_traces_add_and_pos_smul_from_original_inputs (hk : k ≤ n)
    (omega : KahlerBackground n M) (omegaY : KahlerBackground k Y)
    {ι : Y → M} (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    {u v : M → EReal}
    (hu : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n M).IsQPSH u)
    (hv : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n M).IsQPSH v)
    (hgu : sourceGenericLelongNumber (n := n) ι u = 0)
    (hgv : sourceGenericLelongNumber (n := n) ι v = 0) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∃ τu τv τs τℓ : Y → EReal,
      IsSourceTraceRepresentativeAlong omega omegaY hι u τu ∧
      IsSourceTraceRepresentativeAlong omega omegaY hι v τv ∧
      IsSourceTraceRepresentativeAlong omega omegaY hι (fun x => u x + v x) τs ∧
      IsSourceTraceRepresentativeAlong omega omegaY hι (fun x => (ℓ : EReal) * u x) τℓ ∧
      SourcePEquivalent (n := k) τs (fun y => τu y + τv y) ∧
      SourcePEquivalent (n := k) τℓ (fun y => (ℓ : EReal) * τu y) := by
  obtain ⟨τu, hTu⟩ := exists_sourceTrace_of_globalQuasiPshPotential hk omega omegaY
    (nativeGlobal_of_sourceQPSH hu) hι hgu
  obtain ⟨τv, hTv⟩ := exists_sourceTrace_of_globalQuasiPshPotential hk omega omegaY
    (nativeGlobal_of_sourceQPSH hv) hι hgv
  have hgsum := sourceGeneric_add_zero_of_sourceTraces omegaY omegaY hι hTu hTv
  have hgscaled : sourceGenericLelongNumber (n := n) ι (fun x => (ℓ : EReal) * u x) = 0 := by
    rw [sourceGenericLelongNumber_pos_smul ι u hℓ, hgu, mul_zero]
  have hTuKeep := hTu
  have hTvKeep := hTv
  obtain ⟨_hzeroU, _θ, _ε, _U, hU, _β, _hadmU, _hτu, _htermsU, _hlimU⟩ := hTu
  obtain ⟨_hzeroV, _σ, _δ, _V, hV, _γ, _hadmV, _hτv, _htermsV, _hlimV⟩ := hTv
  have hsum := QuasiEquisingularAddition.isQuasiEquisingularApproximation_add hU hV
  have hscaled := RestrictedApproximantComparison.isThetaPshPotential_smul hU.target hℓ
  obtain ⟨τs, hTs⟩ := exists_sourceTrace_of_globalQuasiPshPotential hk omega omegaY
    hsum.target.quasiPshPotential hι hgsum
  obtain ⟨τℓ, hTℓ⟩ := exists_sourceTrace_of_globalQuasiPshPotential hk omega omegaY
    hscaled.quasiPshPotential hι hgscaled
  exact ⟨τu, τv, τs, τℓ, hTuKeep, hTvKeep, hTs, hTℓ,
    sourcePEquivalent_add_of_sourceTraceRepresentatives hk omegaY omegaY omegaY hι
      hTuKeep hTvKeep hTs,
    sourcePEquivalent_pos_smul_of_sourceTraceRepresentatives hk omegaY omegaY hι hTuKeep hℓ hTℓ⟩

/-- The original smooth carrier itself manufactures the target atlas,
holomorphic inclusion, compact connected Kähler geometry and all four trace
witnesses. Only the original source functions and generic-zero data enter. -/
theorem exists_natural_source_traces_add_and_pos_smul
    (omega : KahlerBackground n M) {W : Set M}
    (hW : IsClosedConnectedSubmanifold n W k) {u v : M → EReal}
    (hu : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n M).IsQPSH u)
    (hv : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n M).IsQPSH v)
    (hgu : sourceGenericLelongNumber (n := n) (Subtype.val : W → M) u = 0)
    (hgv : sourceGenericLelongNumber (n := n) (Subtype.val : W → M) v = 0)
    {ℓ : ℝ} (hℓ : 0 < ℓ) :
    let hk : k ≤ n := SubmanifoldChartedSpace.le_of_isClosedConnectedSubmanifold hW
    let : ChartedSpace (ComplexModel k) W := SubmanifoldChartedSpace.chartedSpace hk hW.2.2
    let : IsComplexManifold k W := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hW.2.2
    let : ConnectedSpace W := isConnected_iff_connectedSpace.mp hW.2.1
    let : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
    let : MeasurableSpace W := borel W
    let : BorelSpace W := ⟨rfl⟩
    ∃ τu τv τs τℓ : W → EReal,
      IsNaturalSourceTraceRepresentative omega hW u τu ∧
      IsNaturalSourceTraceRepresentative omega hW v τv ∧
      IsNaturalSourceTraceRepresentative omega hW (fun x => u x + v x) τs ∧
      IsNaturalSourceTraceRepresentative omega hW (fun x => (ℓ : EReal) * u x) τℓ ∧
      SourcePEquivalent (n := k) τs (fun y => τu y + τv y) ∧
      SourcePEquivalent (n := k) τℓ (fun y => (ℓ : EReal) * τu y) := by
  let hk : k ≤ n := SubmanifoldChartedSpace.le_of_isClosedConnectedSubmanifold hW
  let : ChartedSpace (ComplexModel k) W := SubmanifoldChartedSpace.chartedSpace hk hW.2.2
  let : IsComplexManifold k W := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hk hW.2.2
  let : ConnectedSpace W := isConnected_iff_connectedSpace.mp hW.2.1
  let : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
  let : MeasurableSpace W := borel W
  let : BorelSpace W := ⟨rfl⟩
  let omegaW := SubmanifoldKahlerRestriction.kahlerBackground hk hW.2.2 omega
  let hι := SubmanifoldChartedSpace.contMDiff_val hk hW.2.2
  obtain ⟨τu, τv, τs, τℓ, hTu, hTv, hTs, hTℓ, hadd, hscale⟩ :=
    exists_source_traces_add_and_pos_smul_from_original_inputs hk omega omegaW hι hu hv hgu hgv hℓ
  exact ⟨τu, τv, τs, τℓ, hTu, hTv, hTs, hTℓ, hadd, hscale⟩

end SourceReaders

end SGPT.TraceOperations
