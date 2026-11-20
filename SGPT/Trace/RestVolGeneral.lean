import SGPT.Trace.RestVolMain
import SGPT.Trace.RestVolTransfer
import SGPT.Trace.SourceTraceIntegralPerturbationMass
import SGPT.Trace.Trace2Mass

/-!
# `thm:rest_volume` in general (Step 2)

Source: `chapter_trace.tex`, Section *Restricted volumes of line bundles*, `thm:rest_volume`.

The book's setting: `X` projective, `A` a very ample line bundle with a metric `h_A` such that
`ω = dd^c h_A = c₁(A, h_A)` is a Kähler form. Here: `A` is a holomorphic line bundle on the compact
Kähler manifold `X` with a smooth metric whose Chern form `ω_A` is Kähler, together with a
holomorphic section `ϕ ∈ H⁰(X, A)` not vanishing identically on `Y` (both hold for the book's very
ample `A` and its Fubini–Study metric; `ϕ` is the section chosen in Step 2 of the book's proof).

* `sourceTraceMass_congr_geometricallyEq`: the mass of the trace only depends on `θ` up to
  geometric equality;
* `limsup_restrictedH0_le_perturbed` (Step 2, fixed `k₀ = K+1`): `limsup_k m!/k^m h⁰(Y, T|_Y ⊗
  L|_Y^k ⊗ Res_Y 𝓘(kφ)) ≤ ∫_Y (θ|_Y + k₀⁻¹ω|_Y + dd^c Tr^{θ+k₀⁻¹ω}_Y(φ))^m`, from Step 1 applied
  to `L^{k₀} ⊗ A`, `k₀φ`, `T ⊗ L^r` (`tendsto_restrictedH0_of_kahlerCurrent`), multiplication by
  `ϕ^q` (`idealH0_le_transfer`) and `sourceTraceMass_integral_perturbation`;
* **`tendsto_restrictedH0`** (`thm:rest_volume`, eq:DXmainrelative, for every `φ ∈ PSH(X, θ)` with
  `ν(φ, Y) = 0`; the left side is `0` if the trace is not defined, which covers the book's remark
  that the limit is `0` when eq:traceposmasscond2 fails);
* **`rest_volume`**: the book's statement — under eq:traceposmasscond2 the trace
  `Tr^{c₁(L|_Y)}_Y(c₁(L,h))` is defined and eq:DXmainrelative holds.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Trace.RestVol

open Set Filter MeasureTheory Bundle
open scoped Topology ENNReal ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace
open SGPT.Foundations.Analysis.Pending.SubmanifoldIdealRestriction
open SGPT.Foundations.Analysis.Pending.SourceTraceRepresentativeDefinition
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
  SGPT.Bergman.MultiplierSectionsDraft SGPT.Bergman.QuantizationDraft
open SGPT.Bergman.NativeHermitianMetric
open SGPT.PSH SGPT.PSH.VariableComplexAtlas
open HermitianHolomorphicLineBundle

/-! ### The mass of the trace and geometric equality of forms -/

section Congr

variable {n m : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [CompactSpace X]
  {V : Type} [TopologicalSpace V] [ChartedSpace (ComplexModel m) V] [IsComplexManifold m V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]

theorem hasPositiveSourceTraceAlong_of_geometricallyEq (ωb : KahlerBackground n X)
    (ωV : KahlerBackground m V) {ι : V → X}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ ι)
    {θ θ' : ClosedRealOneOneForm n X} (h : θ.val.GeometricallyEq θ'.val) {u : X → EReal}
    (hd : SGPT.Trace.HasPositiveSourceTraceAlong ωb ωV hι θ u) :
    SGPT.Trace.HasPositiveSourceTraceAlong ωb ωV hι θ' u := by
  have hp : (ClosedRealOneOneForm.pullback hι θ).val.GeometricallyEq
      (ClosedRealOneOneForm.pullback hι θ').val := by
    rw [ClosedRealOneOneForm.pullback_val, ClosedRealOneOneForm.pullback_val]
    exact h.pullback hι
  obtain ⟨τ, htr, hτ, hpos⟩ := hd
  have hτ' := (hp.thetaPshPotential_iff τ).mp hτ
  refine ⟨τ, htr, hτ', ?_⟩
  unfold HasPositivePotentialMass at *
  rwa [← ModificationMassInvariance.diagonalPotentialMass_congr_geometricallyEq hp hτ hτ']

/-- **The mass of `Tr^θ_Y(u)` only depends on `θ` up to geometric equality.** -/
theorem sourceTraceMass_congr_geometricallyEq (hk : m ≤ n) (ωb : KahlerBackground n X)
    (ωV : KahlerBackground m V) {ι : V → X}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ ι)
    {θ θ' : ClosedRealOneOneForm n X} (h : θ.val.GeometricallyEq θ'.val) (u : X → EReal) :
    SGPT.Trace.sourceTraceMass ωb ωV hι θ u = SGPT.Trace.sourceTraceMass ωb ωV hι θ' u := by
  classical
  by_cases hd : SGPT.Trace.HasPositiveSourceTraceAlong ωb ωV hι θ u
  · have hp : (ClosedRealOneOneForm.pullback hι θ).val.GeometricallyEq
        (ClosedRealOneOneForm.pullback hι θ').val := by
      rw [ClosedRealOneOneForm.pullback_val, ClosedRealOneOneForm.pullback_val]
      exact h.pullback hι
    obtain ⟨τ, htr, hτ, hpos⟩ := hd
    have hτ' := (hp.thetaPshPotential_iff τ).mp hτ
    have hmass := ModificationMassInvariance.diagonalPotentialMass_congr_geometricallyEq hp hτ hτ'
    have hpos' : HasPositivePotentialMass (ClosedRealOneOneForm.pullback hι θ') τ hτ' := by
      unfold HasPositivePotentialMass at *
      rwa [← hmass]
    rw [SGPT.Trace.sourceTraceMass_eq_of_trace hk ωV ωV hι θ u htr hτ hpos,
      SGPT.Trace.sourceTraceMass_eq_of_trace hk ωV ωV hι θ' u htr hτ' hpos', hmass]
  · have hd' : ¬ SGPT.Trace.HasPositiveSourceTraceAlong ωb ωV hι θ' u := fun h' =>
      hd (hasPositiveSourceTraceAlong_of_geometricallyEq ωb ωV hι h.symm h')
    unfold SGPT.Trace.sourceTraceMass
    rw [dif_neg hd, dif_neg hd']

/-- `ε ↦ ∫_Y (θ|_Y + εω|_Y + dd^c Tr^{θ+εω}_Y(u))^m` is right-continuous at `0`, in every ambient
dimension (`ex:tracedefinedposmass`). -/
theorem tendsto_sourceTraceMass_add_smul_right' (hk : m ≤ n) (ωb ωp : KahlerBackground n X)
    (ωV : KahlerBackground m V) {ι : V → X}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (hpull : (ClosedRealOneOneForm.pullback hι ωp.form).val.IsKahler)
    (θ : ClosedRealOneOneForm n X) {u : X → EReal} (hu : IsThetaPshPotential θ.val u)
    (hgeneric : sourceGenericLelongNumber (n := n) ι u = 0) :
    Tendsto (fun ε : ℝ => SGPT.Trace.sourceTraceMass ωb ωV hι (θ + ε • ωp.form) u)
      (𝓝[>] 0) (𝓝 (SGPT.Trace.sourceTraceMass ωb ωV hι θ u)) := by
  by_cases hn : n = 0
  · exact SGPT.Trace.Trace2Mass.tendsto_sourceTraceMass_add_smul_right_of_dim_zero hk hn ωb ωp ωV
      hι θ hu
  · exact SGPT.Trace.tendsto_sourceTraceMass_add_smul_right hk hn ωb ωp ωV hι hpull θ hu hgeneric

end Congr

/-! ### Step 2 -/

section Step2

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [CompactSpace X]

/-- `m!/(r+(K+1)q)^m · h ≤ (K+1)^{-m} · m!/q^m · h'` for `q > 0` and `h ≤ h'`. -/
theorem normalized_le_ratio {m K r q : ℕ} (hq : 0 < q) {h h' : ℕ} (hh : h ≤ h') :
    ENNReal.ofReal ((m.factorial : ℝ) / ((r + (K + 1) * q : ℕ) : ℝ) ^ m * h) ≤
      ENNReal.ofReal ((((K + 1 : ℕ) : ℝ)⁻¹) ^ m) *
        ENNReal.ofReal ((m.factorial : ℝ) / (q : ℝ) ^ m * h') := by
  rw [← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hq' : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hK : (0 : ℝ) < ((K + 1 : ℕ) : ℝ) := by positivity
  have h1 : (((K + 1 : ℕ) : ℝ) * q) ^ m ≤ ((r + (K + 1) * q : ℕ) : ℝ) ^ m := by
    apply pow_le_pow_left₀ (by positivity)
    push_cast
    nlinarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)]
  have hhR : (h : ℝ) ≤ h' := by exact_mod_cast hh
  calc (m.factorial : ℝ) / ((r + (K + 1) * q : ℕ) : ℝ) ^ m * h
      ≤ (m.factorial : ℝ) / (((K + 1 : ℕ) : ℝ) * q) ^ m * h' := by
        apply mul_le_mul (div_le_div_of_nonneg_left (by positivity) (by positivity) h1) hhR
          (by positivity) (by positivity)
    _ = (((K + 1 : ℕ) : ℝ)⁻¹) ^ m * ((m.factorial : ℝ) / (q : ℝ) ^ m * h') := by
        rw [mul_pow, inv_pow]
        field_simp

/-- **Step 2 of the proof of `thm:rest_volume`, for fixed `k₀ = K + 1`**:
`limsup_k m!/k^m h⁰(Y, T|_Y ⊗ L|_Y^k ⊗ Res_Y 𝓘(kφ)) ≤
∫_Y (θ|_Y + k₀⁻¹ω|_Y + dd^c Tr^{θ+k₀⁻¹ω}_Y(φ))^m`, `ω = c₁(A, h_A)`. -/
theorem limsup_restrictedH0_le_perturbed {L T A : HermitianHolomorphicLineBundle.{0, 0} n X}
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    (hA : IsSourceSmoothHermitianMetric A) (hAK : (sourceNativeFirstChernForm A hA).val.IsKahler)
    {W : Set X} {m : ℕ} (hW : IsClosedConnectedSubmanifold n W m)
    (sA : HolomorphicSections (n := n) A.Fiber) (hsA : ∃ y ∈ W, sA y ≠ 0)
    {φ : X → EReal} (hφ : IsThetaPshPotential (sourceNativeFirstChernForm L hL).val φ)
    (hν : sourceGenericLelongNumber (n := n) (Subtype.val : W → X) φ = 0) (K : ℕ) :
    let ωA : KahlerBackground n X := ⟨sourceNativeFirstChernForm A hA, hAK⟩
    let hk := le_of_isClosedConnectedSubmanifold hW
    letI : ChartedSpace (ComplexModel m) W := chartedSpace hk hW.2.2
    haveI : IsComplexManifold m W := isComplexManifold_chartedSpace hk hW.2.2
    haveI : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
    haveI : ConnectedSpace W := isConnected_iff_connectedSpace.mp hW.2.1
    letI : MeasurableSpace W := borel W
    haveI : BorelSpace W := ⟨rfl⟩
    limsup (fun k => normalizedIdealH0 (restrictBundle L (submanifoldInclusion hW))
        (restrictBundle T (submanifoldInclusion hW))
        (fun k => restrictIdeal (k := m) (W := W) (sourceDegreeMultiplierIdeal (n := n) k φ)) k)
        atTop ≤
      SGPT.Trace.sourceTraceMass ωA (SubmanifoldKahlerRestriction.kahlerBackground hk hW.2.2 ωA)
        (contMDiff_val hk hW.2.2)
        (sourceNativeFirstChernForm L hL + (((K + 1 : ℕ) : ℝ))⁻¹ • ωA.form) φ := by
  intro ωA hk
  let : ChartedSpace (ComplexModel m) W := chartedSpace hk hW.2.2
  have : IsComplexManifold m W := isComplexManifold_chartedSpace hk hW.2.2
  have : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
  have : ConnectedSpace W := isConnected_iff_connectedSpace.mp hW.2.1
  let : MeasurableSpace W := borel W
  have : BorelSpace W := ⟨rfl⟩
  have hval : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ (Subtype.val : W → X) :=
    contMDiff_val hk hW.2.2
  let f := submanifoldInclusion hW
  let θ := sourceNativeFirstChernForm L hL
  let ωW := SubmanifoldKahlerRestriction.kahlerBackground hk hW.2.2 ωA
  have hφq : IsGlobalQuasiPshPotential (n := n) φ := hφ.quasiPshPotential
  have hsA' : pullSection f sA ≠ 0 := by
    intro h0
    obtain ⟨y, hy, hne⟩ := hsA
    apply hne
    have := congrArg (fun s : HolomorphicSections (n := m) (restrictBundle A f).Fiber => s ⟨y, hy⟩) h0
    rw [pullSection_apply, ContMDiffSection.coe_zero, Pi.zero_apply] at this
    exact this
  -- Step 1 for `L' = L^{K+1} ⊗ A`, the potential `(K+1) φ` and the twists `L^r ⊗ T`
  have hK0 : (0 : ℝ) < ((K + 1 : ℕ) : ℝ) := by positivity
  set ψ : X → EReal := fun x => (((K + 1 : ℕ) : ℝ) : EReal) * φ x with hψdef
  have hL' := perturbedBundle_smooth hL hA K
  have hgeoL' := perturbedBundle_chern_geometricallyEq hL hA K
  have hcur : IsKahlerCurrentPotential (sourceNativeFirstChernForm (perturbedBundle L A K) hL') ψ := by
    refine ⟨ωA, ((geometricallyEq_sub_right hgeoL' ωA.form).thetaPshPotential_iff ψ).mpr ?_⟩
    have heq : ((K + 1 : ℕ) : ℝ) • θ + sourceNativeFirstChernForm A hA - ωA.form =
        ((K + 1 : ℕ) : ℝ) • θ := add_sub_cancel_right _ _
    rw [heq]
    exact RestrictedApproximantComparison.isThetaPshPotential_smul hφ hK0
  have hν' : sourceGenericLelongNumber (n := n) (Subtype.val : W → X) ψ = 0 := by
    rw [SGPT.NAPotential.BJPrep.sourceGeneric_subtype_smul_eq W φ hK0, hν, mul_zero]
  have hstep1 : ∀ r : ℕ, Tendsto (fun q => normalizedIdealH0 (restrictBundle (perturbedBundle L A K) f)
      (restrictBundle (twistedPower L T r) f)
      (fun q => restrictIdeal (k := m) (W := W) (sourceDegreeMultiplierIdeal (n := n) q ψ)) q) atTop
      (𝓝 (SGPT.Trace.sourceTraceMass ωA ωW hval
        (sourceNativeFirstChernForm (perturbedBundle L A K) hL') ψ)) := fun r =>
    tendsto_restrictedH0_of_kahlerCurrent ωA hL' (sourceNativeTwistedPower_smooth L T hL hT r) hW
      hcur hν'
  have hmassL' : SGPT.Trace.sourceTraceMass ωA ωW hval
      (sourceNativeFirstChernForm (perturbedBundle L A K) hL') ψ =
      ENNReal.ofReal (((K + 1 : ℕ) : ℝ) ^ m) * SGPT.Trace.sourceTraceMass ωA ωW hval
        (θ + (((K + 1 : ℕ) : ℝ))⁻¹ • ωA.form) φ := by
    rw [sourceTraceMass_congr_geometricallyEq hk ωA ωW hval hgeoL' ψ]
    exact SGPT.Trace.sourceTraceMass_integral_perturbation hk ωA ωW hval θ φ (K + 1)
      (Nat.succ_pos K)
  set c := SGPT.Trace.sourceTraceMass ωA ωW hval (θ + (((K + 1 : ℕ) : ℝ))⁻¹ • ωA.form) φ
  set κ : ℝ≥0∞ := ENNReal.ofReal ((((K + 1 : ℕ) : ℝ)⁻¹) ^ m) with hκ
  have hκc : κ * (ENNReal.ofReal (((K + 1 : ℕ) : ℝ) ^ m) * c) = c := by
    rw [← mul_assoc, hκ, ← ENNReal.ofReal_mul (by positivity), inv_pow,
      inv_mul_cancel₀ (by positivity), ENNReal.ofReal_one, one_mul]
  -- the bound
  refine le_of_forall_gt fun B'' hB'' => ?_
  obtain ⟨B', hcB', hB'B''⟩ := exists_between hB''
  refine lt_of_le_of_lt ?_ hB'B''
  have hev : ∀ r ∈ Finset.range (K + 1), ∀ᶠ q in atTop,
      κ * normalizedIdealH0 (restrictBundle (perturbedBundle L A K) f)
        (restrictBundle (twistedPower L T r) f)
        (fun q => restrictIdeal (k := m) (W := W) (sourceDegreeMultiplierIdeal (n := n) q ψ)) q < B' := by
    intro r _
    have := ENNReal.Tendsto.const_mul (hstep1 r) (Or.inr (ENNReal.ofReal_ne_top (r := _)))
      (a := κ)
    rw [hmassL', hκc] at this
    exact this.eventually (gt_mem_nhds hcB')
  obtain ⟨Q, hQ⟩ := eventually_atTop.mp ((Finset.range (K + 1)).eventually_all.mpr hev)
  refine limsup_le_of_le (by isBoundedDefault) ?_
  filter_upwards [eventually_ge_atTop ((K + 1) * (Q + 1))] with k hk'
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < K + 1 ∧ k = r + (K + 1) * q :=
    ⟨k / (K + 1), k % (K + 1), Nat.mod_lt _ (Nat.succ_pos K), (Nat.mod_add_div k (K + 1)).symm⟩
  have hqQ : Q ≤ q := by nlinarith
  have hq0 : 0 < q := by nlinarith
  refine le_trans ?_ (hQ q hqQ r (Finset.mem_range.mpr hr)).le
  unfold normalizedIdealH0
  exact normalized_le_ratio hq0 (idealH0_le_transfer hval hφq hsA')

/-- **`thm:rest_volume`, eq:DXmainrelative, for every `φ`**: for every `φ ∈ PSH(X, θ)` with
`ν(φ, Y) = 0` and every holomorphic line bundle `T`,
`m!/k^m h⁰(Y, T|_Y ⊗ L|_Y^k ⊗ Res_Y 𝓘(kφ)) → ∫_Y (θ|_Y + dd^c Tr^θ_Y(φ))^m`, the right side being
`0` when `Tr^θ_Y(φ)` is not defined. -/
theorem tendsto_restrictedH0 {L T A : HermitianHolomorphicLineBundle.{0, 0} n X}
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    (hA : IsSourceSmoothHermitianMetric A) (hAK : (sourceNativeFirstChernForm A hA).val.IsKahler)
    {W : Set X} {m : ℕ} (hW : IsClosedConnectedSubmanifold n W m)
    (sA : HolomorphicSections (n := n) A.Fiber) (hsA : ∃ y ∈ W, sA y ≠ 0)
    {φ : X → EReal} (hφ : IsThetaPshPotential (sourceNativeFirstChernForm L hL).val φ)
    (hν : sourceGenericLelongNumber (n := n) (Subtype.val : W → X) φ = 0) :
    let ωA : KahlerBackground n X := ⟨sourceNativeFirstChernForm A hA, hAK⟩
    let hk := le_of_isClosedConnectedSubmanifold hW
    letI : ChartedSpace (ComplexModel m) W := chartedSpace hk hW.2.2
    haveI : IsComplexManifold m W := isComplexManifold_chartedSpace hk hW.2.2
    haveI : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
    haveI : ConnectedSpace W := isConnected_iff_connectedSpace.mp hW.2.1
    letI : MeasurableSpace W := borel W
    haveI : BorelSpace W := ⟨rfl⟩
    Tendsto (fun k => normalizedIdealH0 (restrictBundle L (submanifoldInclusion hW))
        (restrictBundle T (submanifoldInclusion hW))
        (fun k => restrictIdeal (k := m) (W := W) (sourceDegreeMultiplierIdeal (n := n) k φ)) k)
      atTop (𝓝 (SGPT.Trace.sourceTraceMass ωA
        (SubmanifoldKahlerRestriction.kahlerBackground hk hW.2.2 ωA)
        (contMDiff_val hk hW.2.2) (sourceNativeFirstChernForm L hL) φ)) := by
  intro ωA hk
  let : ChartedSpace (ComplexModel m) W := chartedSpace hk hW.2.2
  have : IsComplexManifold m W := isComplexManifold_chartedSpace hk hW.2.2
  have : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
  have : ConnectedSpace W := isConnected_iff_connectedSpace.mp hW.2.1
  let : MeasurableSpace W := borel W
  have : BorelSpace W := ⟨rfl⟩
  have hval : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ (Subtype.val : W → X) :=
    contMDiff_val hk hW.2.2
  let ωW := SubmanifoldKahlerRestriction.kahlerBackground hk hW.2.2 ωA
  have hpullA : (ClosedRealOneOneForm.pullback hval ωA.form).val.IsKahler :=
    SubmanifoldKahlerRestriction.isKahler_pullback hk hW.2.2 ωA.form ωA.isKahler
  refine tendsto_of_le_liminf_of_limsup_le
    (sourceTraceMass_le_liminf_restrictedH0 ωA hL hT hW φ) ?_
  have hlim := tendsto_sourceTraceMass_add_smul_right' hk ωA ωA ωW hval hpullA
    (sourceNativeFirstChernForm L hL) hφ hν
  have hε : Tendsto (fun K : ℕ => (((K + 1 : ℕ) : ℝ))⁻¹) atTop (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun K => by
      show (0 : ℝ) < _
      positivity⟩
    have := (tendsto_inv_atTop_zero (𝕜 := ℝ)).comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
    refine this.congr fun K => ?_
    simp
  exact ge_of_tendsto' (hlim.comp hε) fun K =>
    limsup_restrictedH0_le_perturbed hL hT hA hAK hW sA hsA hφ hν K

/-- **`thm:rest_volume`** (the book's statement): if eq:traceposmasscond2 holds, i.e.
`lim_{ε→0+} ∫_Y (θ|_Y + εω|_Y + dd^c Tr^{θ+εω}_Y(φ))^m > 0` (`ω = c₁(A, h_A)`), then
`Tr^θ_Y(φ) = Tr^{c₁(L|_Y)}_Y(c₁(L,h))` is defined and, for every holomorphic line bundle `T`,
`∫_Y (θ|_Y + dd^c Tr^θ_Y(φ))^m = lim_k m!/k^m h⁰(Y, T|_Y ⊗ L|_Y^k ⊗ Res_Y 𝓘(h^k))`. -/
theorem rest_volume {L T A : HermitianHolomorphicLineBundle.{0, 0} n X}
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    (hA : IsSourceSmoothHermitianMetric A) (hAK : (sourceNativeFirstChernForm A hA).val.IsKahler)
    {W : Set X} {m : ℕ} (hW : IsClosedConnectedSubmanifold n W m)
    (sA : HolomorphicSections (n := n) A.Fiber) (hsA : ∃ y ∈ W, sA y ≠ 0)
    {φ : X → EReal} (hφ : IsThetaPshPotential (sourceNativeFirstChernForm L hL).val φ)
    (hν : sourceGenericLelongNumber (n := n) (Subtype.val : W → X) φ = 0) :
    let ωA : KahlerBackground n X := ⟨sourceNativeFirstChernForm A hA, hAK⟩
    let hk := le_of_isClosedConnectedSubmanifold hW
    letI : ChartedSpace (ComplexModel m) W := chartedSpace hk hW.2.2
    haveI : IsComplexManifold m W := isComplexManifold_chartedSpace hk hW.2.2
    haveI : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
    haveI : ConnectedSpace W := isConnected_iff_connectedSpace.mp hW.2.1
    letI : MeasurableSpace W := borel W
    haveI : BorelSpace W := ⟨rfl⟩
    (∃ M : ℝ≥0∞, 0 < M ∧ Tendsto (fun ε : ℝ => SGPT.Trace.sourceTraceMass ωA
      (SubmanifoldKahlerRestriction.kahlerBackground hk hW.2.2 ωA) (contMDiff_val hk hW.2.2)
      (sourceNativeFirstChernForm L hL + ε • ωA.form) φ) (𝓝[>] 0) (𝓝 M)) →
    SGPT.Trace.HasPositiveSourceTraceAlong ωA
        (SubmanifoldKahlerRestriction.kahlerBackground hk hW.2.2 ωA) (contMDiff_val hk hW.2.2)
        (sourceNativeFirstChernForm L hL) φ ∧
      Tendsto (fun k => normalizedIdealH0 (restrictBundle L (submanifoldInclusion hW))
        (restrictBundle T (submanifoldInclusion hW))
        (fun k => restrictIdeal (k := m) (W := W) (sourceDegreeMultiplierIdeal (n := n) k φ)) k)
      atTop (𝓝 (SGPT.Trace.sourceTraceMass ωA
        (SubmanifoldKahlerRestriction.kahlerBackground hk hW.2.2 ωA)
        (contMDiff_val hk hW.2.2) (sourceNativeFirstChernForm L hL) φ)) := by
  intro ωA hk
  let : ChartedSpace (ComplexModel m) W := chartedSpace hk hW.2.2
  have : IsComplexManifold m W := isComplexManifold_chartedSpace hk hW.2.2
  have : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
  have : ConnectedSpace W := isConnected_iff_connectedSpace.mp hW.2.1
  let : MeasurableSpace W := borel W
  have : BorelSpace W := ⟨rfl⟩
  rintro ⟨M, hM, hlimM⟩
  have hval : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ (Subtype.val : W → X) :=
    contMDiff_val hk hW.2.2
  have hpullA : (ClosedRealOneOneForm.pullback hval ωA.form).val.IsKahler :=
    SubmanifoldKahlerRestriction.isKahler_pullback hk hW.2.2 ωA.form ωA.isKahler
  refine ⟨?_, tendsto_restrictedH0 hL hT hA hAK hW sA hsA hφ hν⟩
  by_cases hn : n = 0
  · exact (SGPT.Trace.Trace2Mass.hasPositiveSourceTraceAlong_of_tendsto_pos_of_dim_zero hk hn ωA ωA
      _ hval _ hφ hlimM hM).1
  · exact (SGPT.Trace.hasPositiveSourceTraceAlong_of_tendsto_pos hk hn ωA ωA _ hval hpullA _ hφ hν
      hlimM hM).1

end Step2

end SGPT.Trace.RestVol
