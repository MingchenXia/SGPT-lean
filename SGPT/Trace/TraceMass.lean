import SGPT.Trace.TraceEnvelope
import SGPT.Foundations.Analysis.Pending.NumericalTraceMass
import SGPT.Foundations.Analysis.Pending.NormalizedTraceFixedPotentialRightLimit
import SGPT.Foundations.Analysis.Pending.NonKahlerMinimalRestrictionTraceMass
import SGPT.Foundations.Analysis.Pending.MinimalPotentialNumericalTraceRightLimit
import SGPT.Foundations.Analysis.Pending.MinimalPotentialOrdinaryRestrictionRightLimit
import SGPT.Foundations.Analysis.Pending.SingularityEnvelopeMassProof

/-!
# Masses of normalized traces and restricted volumes

Source: `chapter_trace.tex`, `ex:tracedefinedposmass`, `prop:restvol_voltrace` and
`thm:rest_volume_tr_volume`. The mass `∫_Y (θ|_Y + dd^c Tr^θ_Y(φ))^{dim Y}` is
`sourceTraceMass`, with the book's convention that it is `0` when `Tr^θ_Y(φ)` is not
defined. The target is a compact connected manifold `V → X` whose pullback of the
auxiliary Kähler form is Kähler (e.g. a connected submanifold), the book's `Y` in
Sections "Relation to the classical restricted volumes".

We prove, in positive ambient dimension:

* `SGPT.Trace.tendsto_sourceTraceMass_add_smul_right` and
  `SGPT.Trace.hasPositiveSourceTraceAlong_of_tendsto_pos`: source
  `ex:tracedefinedposmass`;
* `SGPT.Trace.sourceTraceMass_minimal_eq_restriction_mass`: the second equality of
  source `prop:restvol_voltrace`, `∫(θ|_Y + dd^c Tr^θ_Y(V_θ))^m = ∫(θ|_Y + dd^c V_θ|_Y)^m`
  when `Y ⊄ nK(α)`;
* `SGPT.Trace.tendsto_restriction_minimal_mass` and
  `SGPT.Trace.tendsto_sourceTraceMass_minimal_add_smul_right`: the equality of the
  second, third and fourth terms of source `thm:rest_volume_tr_volume` when
  `Y ⊄ nn(α)`.

The identification of these quantities with the restricted volume `vol_{X|Y}(α)` of
Matsumura and Collins–Tosatti is not formalized here.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal ContDiff

namespace SGPT.Trace

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
  SGPT.Foundations.Analysis.Pending
  SourceTraceRepresentativeDefinition TraceRepresentativeConstruction
  DiagonalMass PositiveNormalizedTrace NumericalTraceMass

variable {n k : ℕ} {M V : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]

omit [CompactSpace M] in
/-- The normalized trace is a potential in the pulled-back background. -/
theorem isThetaPshPotential_sourceTraceEnvelope (omega : KahlerBackground n M)
    (omegaV : KahlerBackground k V) {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (θ : ClosedRealOneOneForm n M) (u : M → EReal)
    (hdefined : HasPositiveSourceTraceAlong omega omegaV hι θ u) :
    IsThetaPshPotential (ClosedRealOneOneForm.pullback hι θ).val
      (sourceTraceEnvelope omega omegaV hι θ u hdefined) := by
  obtain ⟨_, hτ, _⟩ := Classical.choose_spec hdefined
  let η := ClosedRealOneOneForm.pullback hι θ
  exact FirstPass.singularityEnvelope_isThetaPshPotential η.val η.property.1 η.property.2
    hτ.1.hasSmoothLocalPotentials _ hτ

/-- The mass `∫_Y (θ|_Y + dd^c Tr^θ_Y(u))^{dim Y}`, understood as `0` if
`Tr^θ_Y(u)` is not defined (the convention of source `ex:tracedefinedposmass`). -/
def sourceTraceMass (omega : KahlerBackground n M) (omegaV : KahlerBackground k V)
    {ι : V → M} (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (θ : ClosedRealOneOneForm n M) (u : M → EReal) : ℝ≥0∞ := by
  classical
  exact if hdefined : HasPositiveSourceTraceAlong omega omegaV hι θ u then
    diagonalPotentialMass (ClosedRealOneOneForm.pullback hι θ)
      (sourceTraceEnvelope omega omegaV hι θ u hdefined)
      (isThetaPshPotential_sourceTraceEnvelope omega omegaV hι θ u hdefined)
  else 0

omit [BorelSpace V] [ConnectedSpace V] in
private theorem mass_congr {η : ClosedRealOneOneForm k V} {a b : V → EReal}
    (ha : IsThetaPshPotential η.val a) (hb : IsThetaPshPotential η.val b) (hab : a = b) :
    diagonalPotentialMass η a ha = diagonalPotentialMass η b hb := by
  subst hab
  rfl

/-- When `Tr^θ_Y(u)` is defined, its mass is the mass of every positive trace operator. -/
theorem sourceTraceMass_eq_of_trace (hk : k ≤ n)
    {omega₀ omega₁ : KahlerBackground n M} (omegaV₀ omegaV₁ : KahlerBackground k V)
    {ι : V → M} (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (θ : ClosedRealOneOneForm n M) (u : M → EReal) {τ : V → EReal}
    (htrace : IsSourceTraceRepresentativeAlong omega₁ omegaV₁ hι u τ)
    (hτ : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι θ).val τ)
    (hpos : HasPositivePotentialMass (ClosedRealOneOneForm.pullback hι θ) τ hτ) :
    sourceTraceMass omega₀ omegaV₀ hι θ u =
      diagonalPotentialMass (ClosedRealOneOneForm.pullback hι θ) τ hτ := by
  classical
  have hdefined : HasPositiveSourceTraceAlong omega₀ omegaV₀ hι θ u :=
    (hasPositiveSourceTraceAlong_iff_auxiliary_choices hk omega₁ omega₀ omegaV₁ omegaV₀ hι θ u).mp
      ⟨τ, htrace, hτ, hpos⟩
  let η := ClosedRealOneOneForm.pullback hι θ
  have heq := (sourceTraceEnvelope_eq_envelopes hk omegaV₀ omegaV₁ hι θ u hdefined
    htrace hτ hpos).1
  have hP : IsThetaPshPotential η.val (singularityEnvelope η.val τ) :=
    FirstPass.singularityEnvelope_isThetaPshPotential η.val η.property.1 η.property.2
      hτ.1.hasSmoothLocalPotentials τ hτ
  simp only [sourceTraceMass, dif_pos hdefined]
  rw [mass_congr _ hP heq]
  exact singularityEnvelopeMassPreserving omegaV₀ η τ hτ hP

/-- `Tr^θ_Y(u)` is defined exactly when its mass is positive. -/
theorem hasPositiveSourceTraceAlong_iff_sourceTraceMass_pos (hk : k ≤ n)
    (omega : KahlerBackground n M) (omegaV : KahlerBackground k V) {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (θ : ClosedRealOneOneForm n M) (u : M → EReal) :
    HasPositiveSourceTraceAlong omega omegaV hι θ u ↔
      0 < sourceTraceMass omega omegaV hι θ u := by
  classical
  constructor
  · intro hdefined
    obtain ⟨τ, htrace, hτ, hpos⟩ := hdefined
    rw [sourceTraceMass_eq_of_trace hk omegaV omegaV hι θ u htrace hτ hpos]
    exact hpos
  · intro hpos
    by_contra hnot
    simp only [sourceTraceMass, dif_neg hnot, lt_self_iff_false] at hpos

/-- The mass does not depend on the auxiliary Kähler forms. -/
theorem sourceTraceMass_eq_of_choices (hk : k ≤ n)
    (omega₀ omega₁ : KahlerBackground n M) (omegaV₀ omegaV₁ : KahlerBackground k V)
    {ι : V → M} (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (θ : ClosedRealOneOneForm n M) (u : M → EReal) :
    sourceTraceMass omega₀ omegaV₀ hι θ u = sourceTraceMass omega₁ omegaV₁ hι θ u := by
  classical
  by_cases h₁ : HasPositiveSourceTraceAlong omega₁ omegaV₁ hι θ u
  · obtain ⟨τ, htrace, hτ, hpos⟩ := h₁
    rw [sourceTraceMass_eq_of_trace hk omegaV₀ omegaV₁ hι θ u htrace hτ hpos,
      sourceTraceMass_eq_of_trace hk omegaV₁ omegaV₁ hι θ u htrace hτ hpos]
  · have h₀ : ¬ HasPositiveSourceTraceAlong omega₀ omegaV₀ hι θ u := fun h =>
      h₁ ((hasPositiveSourceTraceAlong_iff_auxiliary_choices hk omega₀ omega₁ omegaV₀ omegaV₁
        hι θ u).mp h)
    simp only [sourceTraceMass, dif_neg h₀, dif_neg h₁]

/-- In positive ambient dimension the mass is the native numerical trace mass. -/
theorem sourceTraceMass_eq_numericalTraceMass (hk : k ≤ n) (hn : n ≠ 0)
    (omega : KahlerBackground n M) (omegaV : KahlerBackground k V) {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (θ : ClosedRealOneOneForm n M) (u : M → EReal) :
    sourceTraceMass omega omegaV hι θ u = numericalTraceMass omega omegaV hι θ u := by
  classical
  by_cases h : HasPositiveSourceTraceAlong omega omegaV hι θ u
  · have hnat := (hasPositiveSourceTraceAlong_iff_native hn omega omegaV hι θ u).mp h
    obtain ⟨τ, htrace, hτ, hpos⟩ := hnat
    rw [sourceTraceMass_eq_of_trace hk omegaV omegaV hι θ u
      ((isSourceTraceRepresentativeAlong_iff_native hn _ _ hι u τ).mpr htrace) hτ hpos,
      numericalTraceMass_eq_of_positive_reader omegaV omegaV hι θ u
        ((hasPositiveSourceTraceAlong_iff_native hn omega omegaV hι θ u).mp h) htrace hτ hpos]
  · have hnat : ¬ HasPositiveTraceRepresentativeAlong omega omegaV hι θ u := fun h' =>
      h ((hasPositiveSourceTraceAlong_iff_native hn omega omegaV hι θ u).mpr h')
    simp only [sourceTraceMass, dif_neg h, numericalTraceMass, dif_neg hnat]

/-- Source `ex:tracedefinedposmass`, the formula: for `u ∈ PSH(X,θ)` with `ν(u, Y) = 0`
and every Kähler form `ω` (with Kähler pullback), the mass of `Tr^θ_Y(u)` (`0` if not
defined) is the limit, as `ε ↘ 0`, of the masses of `Tr^{θ+εω}_Y(u)`. -/
theorem tendsto_sourceTraceMass_add_smul_right (hk : k ≤ n) (hn : n ≠ 0)
    (omega₀ omega : KahlerBackground n M) (omegaV : KahlerBackground k V) {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (hpull : (ClosedRealOneOneForm.pullback hι omega.form).val.IsKahler)
    (θ : ClosedRealOneOneForm n M) {u : M → EReal} (hu : IsThetaPshPotential θ.val u)
    (hgeneric : sourceGenericLelongNumber (n := n) ι u = 0) :
    Tendsto (fun ε : ℝ => sourceTraceMass omega₀ omegaV hι (θ + ε • omega.form) u)
      (𝓝[>] 0) (𝓝 (sourceTraceMass omega₀ omegaV hι θ u)) := by
  have h := NormalizedTraceFixedPotentialRightLimit.tendsto_numericalTraceMass_add_smul_right
    omega omegaV hι hpull θ hu ((nativeGeneric_zero_iff_source hn ι u).mpr hgeneric)
  simp_rw [sourceTraceMass_eq_of_choices hk omega₀ omega omegaV omegaV hι,
    sourceTraceMass_eq_numericalTraceMass hk hn omega omegaV hι]
  exact h

/-- Source `ex:tracedefinedposmass`: if the limit of the masses of `Tr^{θ+εω}_Y(u)` is
positive, then `Tr^θ_Y(u)` is defined, and its mass is that limit. -/
theorem hasPositiveSourceTraceAlong_of_tendsto_pos (hk : k ≤ n) (hn : n ≠ 0)
    (omega₀ omega : KahlerBackground n M) (omegaV : KahlerBackground k V) {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (hpull : (ClosedRealOneOneForm.pullback hι omega.form).val.IsKahler)
    (θ : ClosedRealOneOneForm n M) {u : M → EReal} (hu : IsThetaPshPotential θ.val u)
    (hgeneric : sourceGenericLelongNumber (n := n) ι u = 0) {L : ℝ≥0∞}
    (hL : Tendsto (fun ε : ℝ => sourceTraceMass omega₀ omegaV hι (θ + ε • omega.form) u)
      (𝓝[>] 0) (𝓝 L)) (hLpos : 0 < L) :
    HasPositiveSourceTraceAlong omega₀ omegaV hι θ u ∧
      sourceTraceMass omega₀ omegaV hι θ u = L := by
  have hlim := tendsto_sourceTraceMass_add_smul_right hk hn omega₀ omega omegaV hι hpull θ hu
    hgeneric
  have heq : sourceTraceMass omega₀ omegaV hι θ u = L := tendsto_nhds_unique hlim hL
  exact ⟨(hasPositiveSourceTraceAlong_iff_sourceTraceMass_pos hk omega₀ omegaV hι θ u).mpr
    (heq ▸ hLpos), heq⟩

section Minimal

variable [MeasurableSpace M] [BorelSpace M] [ConnectedSpace M]

omit [MeasurableSpace M] [BorelSpace M] [ConnectedSpace M] in
/-- Source `prop:restvol_voltrace`, the second equality: if `Y ⊄ nK(α)`, then
`Tr^θ_Y(V_θ)` is defined and `∫_Y (θ|_Y + dd^c Tr^θ_Y(V_θ))^m = ∫_Y (θ|_Y + dd^c V_θ|_Y)^m`. -/
theorem sourceTraceMass_minimal_eq_restriction_mass (hk : k ≤ n) (hn : n ≠ 0)
    (omega : KahlerBackground n M) (omegaV : KahlerBackground k V) {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (hpull : (ClosedRealOneOneForm.pullback hι omega.form).val.IsKahler)
    (θ : ClosedRealOneOneForm n M)
    (hx : ∃ y : V, ι y ∉ nonKahlerLocus (RealBottChern.ofRepresentative θ)) :
    HasPositiveSourceTraceAlong omega omegaV hι θ (thetaPshSupremum θ.val) ∧
      ∃ hw : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι θ).val
          (fun y => thetaPshSupremum θ.val (ι y)),
        sourceTraceMass omega omegaV hι θ (thetaPshSupremum θ.val) =
          diagonalPotentialMass (ClosedRealOneOneForm.pullback hι θ)
            (fun y => thetaPshSupremum θ.val (ι y)) hw := by
  classical
  obtain ⟨hd, hw, hmass⟩ :=
    NonKahlerMinimalRestrictionTraceMass.exists_positive_ordinary_restriction_mass_eq_normalizedTraceMass_of_not_mem_nonKahlerLocus
      omega omegaV hι hpull θ hx
  refine ⟨(hasPositiveSourceTraceAlong_iff_native hn omega omegaV hι θ _).mpr hd, hw, ?_⟩
  rw [sourceTraceMass_eq_numericalTraceMass hk hn, hmass]
  simp only [numericalTraceMass, dif_pos hd]

/-- Source `thm:rest_volume_tr_volume`, equality of the second and fourth terms: if
`Y ⊄ nn(α)` and `α` is big, then for every family `r_i ↘ 0` of positive reals,
`∫_Y (θ|_Y + r_iω|_Y + dd^c V_{θ+r_iω}|_Y)^m → ∫_Y (θ|_Y + dd^c Tr^θ_Y(V_θ))^m`
(the latter `0` if `Tr^θ_Y(V_θ)` is not defined). -/
theorem tendsto_restriction_minimal_mass (hk : k ≤ n) (hn : n ≠ 0)
    (omega : KahlerBackground n M) (omegaV : KahlerBackground k V) {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (hpull : (ClosedRealOneOneForm.pullback hι omega.form).val.IsKahler)
    (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (hx : ∃ y : V, ι y ∉ nonNefLocus omega (RealBottChern.ofRepresentative θ)) :
    ∃ hW : ∀ (e : ℝ), 0 < e →
      IsThetaPshPotential (ClosedRealOneOneForm.pullback hι (θ + e • omega.form)).val
        (fun y => thetaPshSupremum (θ + e • omega.form).val (ι y)),
      ∀ (I : Type*) (F : Filter I) (r : I → ℝ) (hr : ∀ i, 0 < r i),
        Tendsto r F (𝓝 0) →
          Tendsto (fun i => diagonalPotentialMass
            (ClosedRealOneOneForm.pullback hι (θ + r i • omega.form))
            (fun y => thetaPshSupremum (θ + r i • omega.form).val (ι y)) (hW (r i) (hr i))) F
            (𝓝 (sourceTraceMass omega omegaV hι θ (thetaPshSupremum θ.val))) := by
  rw [sourceTraceMass_eq_numericalTraceMass hk hn]
  exact MinimalPotentialOrdinaryRestrictionRightLimit.exists_tendsto_ordinary_minimal_restriction_mass_of_not_mem_nonNefLocus
    omega omegaV hι hpull θ hbig hx

/-- Source `thm:rest_volume_tr_volume`, equality of the third and fourth terms: if
`Y ⊄ nn(α)` and `α` is big, then
`∫_Y (θ|_Y + εω|_Y + dd^c Tr^{θ+εω}_Y(V_{θ+εω}))^m → ∫_Y (θ|_Y + dd^c Tr^θ_Y(V_θ))^m`
as `ε ↘ 0`. -/
theorem tendsto_sourceTraceMass_minimal_add_smul_right (hk : k ≤ n) (hn : n ≠ 0)
    (omega : KahlerBackground n M) (omegaV : KahlerBackground k V) {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (hpull : (ClosedRealOneOneForm.pullback hι omega.form).val.IsKahler)
    (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (hx : ∃ y : V, ι y ∉ nonNefLocus omega (RealBottChern.ofRepresentative θ)) :
    Tendsto (fun e : ℝ => sourceTraceMass omega omegaV hι (θ + e • omega.form)
        (thetaPshSupremum (θ + e • omega.form).val))
      (𝓝[>] 0) (𝓝 (sourceTraceMass omega omegaV hι θ (thetaPshSupremum θ.val))) := by
  obtain ⟨y, hy⟩ := hx
  rw [NonNefLocusLelong.nonNefLocus_eq_setOf_lelongNumber_pos omega θ hbig] at hy
  simp only [mem_ofPred_eq] at hy
  have hpoint : lelongNumber (n := n) (thetaPshSupremum θ.val) (ι y) = 0 :=
    nonpos_iff_eq_zero.mp (not_lt.mp hy)
  have hgeneric : (⨅ z : V, lelongNumber (n := n) (thetaPshSupremum θ.val) (ι z)) = 0 :=
    le_antisymm (iInf_le_of_le y hpoint.le) zero_le
  simp_rw [sourceTraceMass_eq_numericalTraceMass hk hn]
  exact MinimalPotentialNumericalTraceRightLimit.tendsto_numericalTraceMass_minimal_add_smul_right
    omega omegaV hι hpull θ hbig hgeneric

end Minimal

end SGPT.Trace
