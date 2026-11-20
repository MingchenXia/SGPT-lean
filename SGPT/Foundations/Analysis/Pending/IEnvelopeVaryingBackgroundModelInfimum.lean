import SGPT.Foundations.Analysis.Pending.IEnvelopeDecreasingModelInfimum
import SGPT.Foundations.Analysis.Pending.TraceFreeLimit

set_option autoImplicit false

/-! # Literal fixed I-envelope of a positive varying-background model infimum -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.IEnvelopeVaryingBackgroundModelInfimum

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus FirstPass.IEnvelope
  DiagonalMass MixedMass TraceFreeLimit PositiveCurrentRooftop
  ThetaPshConvexCombination ActualIEnvelopeAdditionConcavity
  ActualIEnvelopeUniformL1Vanishing ActualIEnvelopeOrderInfimum
  IEnvelopeIncreasingRegularizedSupremum ThetaPshDecreasingLimit
  ChartwiseGlobalL1 ThetaPshL1Order IntegrationCurrent

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

omit [BorelSpace M] [ConnectedSpace M] in
private theorem traceFreeLimit_eq_iInf
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    {ε : ℕ → ℝ} {v : ℕ → M → EReal}
    (hv : ∀ j, IsModelPotential (θ + ε j • omega.form) (v j)) :
    traceFreeLimit θ omega.form ε v = (⨅ j, v j) := by
  funext x
  simp only [traceFreeLimit, iInf_apply]
  exact iInf_congr fun j => congrFun (hv j).envelope_eq.symm x

omit [BorelSpace M] in
/-- Actual normalized compact antitone limits internally produce genuine PSH
of the unchanged pointwise infimum in the original background. -/
theorem isThetaPshPotential_iInf_varying_models
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    {ε : ℕ → ℝ} (hεanti : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0))
    {v : ℕ → M → EReal}
    (hv : ∀ j, IsModelPotential (θ + ε j • omega.form) (v j))
    (hanti : Antitone v) : IsThetaPshPotential θ.val (⨅ j, v j) := by
  have h := isThetaPshPotential_traceFreeLimit omega hεanti hεlim
    (fun j => (hv j).plurisubharmonic) (fun x i j hij => hanti hij x)
  rwa [traceFreeLimit_eq_iInf omega θ hv] at h

omit [BorelSpace M] [ConnectedSpace M] in
private theorem diagonalPotentialMass_eq_of_dim_zero
    (hn : n = 0) {θ σ : ClosedRealOneOneForm n M} {u v : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential σ.val v) :
    diagonalPotentialMass θ u hu = diagonalPotentialMass σ v hv := by
  subst hn
  have hθ : (fun _ : Fin 0 => θ) = fun _ => σ := by
    funext i
    exact Fin.elim0 i
  have huv : (fun _ : Fin 0 => u) = fun _ => v := by
    funext i
    exact Fin.elim0 i
  unfold diagonalPotentialMass diagonalPotentialMeasure
  congr 1
  let μ : (Fin 0 → ClosedRealOneOneForm 0 M) → (Fin 0 → M → EReal) → Measure M :=
    fun a f => GlobalNonPluripolar.globalMixedMeasure a f (fun i => Fin.elim0 i)
  change μ (fun _ => θ) (fun _ => u) = μ (fun _ => σ) (fun _ => v)
  exact congrArg₂ μ hθ huv

/-- Genuine varying-background model masses converge in every dimension;
the zero-dimensional branch uses the actual empty global mixed tuple. -/
theorem tendsto_diagonalPotentialMass_iInf_varying_models
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    {ε : ℕ → ℝ} (hεpos : ∀ j, 0 < ε j)
    (hεanti : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0))
    {v : ℕ → M → EReal}
    (hv : ∀ j, IsModelPotential (θ + ε j • omega.form) (v j))
    (hanti : Antitone v) :
    Tendsto (fun j => diagonalPotentialMass (θ + ε j • omega.form)
      (v j) (hv j).plurisubharmonic) atTop
      (𝓝 (diagonalPotentialMass θ (⨅ j, v j)
        (isThetaPshPotential_iInf_varying_models omega θ hεanti hεlim hv hanti))) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · have he (j : ℕ) := diagonalPotentialMass_eq_of_dim_zero hn
      (hv j).plurisubharmonic
      (isThetaPshPotential_iInf_varying_models omega θ hεanti hεlim hv hanti)
    exact tendsto_const_nhds.congr (fun j => (he j).symm)
  · have h := tendsto_diagonalPotentialMass_traceFreeLimit hn omega hεpos hεanti hεlim
      (fun j => (hv j).plurisubharmonic) (fun x i j hij => hanti hij x)
    simpa only [traceFreeLimit_eq_iInf omega θ hv] using h

/-- Internal moving-background affine barriers and a fixed normalized L1
bound identify the actual I-envelope infimum as a literal function. -/
theorem iInf_iSingularityEnvelope_eq_in_fixed_enlargement
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    {ε : ℕ → ℝ} (hεpos : ∀ j, 0 < ε j)
    (hεanti : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0))
    {v : ℕ → M → EReal}
    (hv : ∀ j, IsModelPotential (θ + ε j • omega.form) (v j))
    (hanti : Antitone v)
    (hpos : HasPositivePotentialMass θ (⨅ j, v j)
      (isThetaPshPotential_iInf_varying_models omega θ hεanti hεlim hv hanti)) :
    let γ := θ + (ε 0 + 1) • omega.form
    (⨅ j, iSingularityEnvelope γ.val (v j)) =
      iSingularityEnvelope γ.val (⨅ j, v j) := by
  classical
  let u : M → EReal := ⨅ j, v j
  have hu : IsThetaPshPotential θ.val u :=
    isThetaPshPotential_iInf_varying_models omega θ hεanti hεlim hv hanti
  let γ : ClosedRealOneOneForm n M := θ + (ε 0 + 1) • omega.form
  have hGu : IsThetaPshPotential γ.val u :=
    LocalPotentials.isThetaPshPotential_add_of_semipositive hu
      (KahlerDomination.isSemipositive_smul omega.isSemipositive (by linarith [hεpos 0]))
  have henlarge (j : ℕ) : 0 ≤ ε 0 + 1 - ε j := by
    have hle := hεanti (Nat.zero_le j)
    linarith
  have hforms (j : ℕ) : θ + ε j • omega.form +
      (ε 0 + 1 - ε j) • omega.form = γ := by
    dsimp only [γ]
    module
  have hGv (j : ℕ) : IsThetaPshPotential γ.val (v j) := by
    have h := LocalPotentials.isThetaPshPotential_add_of_semipositive
      (hv j).plurisubharmonic
      (KahlerDomination.isSemipositive_smul omega.isSemipositive (henlarge j))
    rwa [hforms j] at h
  let P : M → EReal := iSingularityEnvelope γ.val u
  let B : ℕ → M → EReal := fun j => iSingularityEnvelope γ.val (v j)
  let H : M → EReal := ⨅ j, B j
  have hP : IsThetaPshPotential γ.val P :=
    iSingularityEnvelope_isThetaPshPotential γ.val γ.property.1 γ.property.2
      hGu.1.hasSmoothLocalPotentials u hGu
  have hB (j : ℕ) : IsThetaPshPotential γ.val (B j) :=
    iSingularityEnvelope_isThetaPshPotential γ.val γ.property.1 γ.property.2
      (hGv j).1.hasSmoothLocalPotentials (v j) (hGv j)
  have huj (j : ℕ) : u ≤ v j := iInf_le v j
  have hPB (j : ℕ) : P ≤ B j :=
    iSingularityEnvelope_le_of_iOrderOnManifold γ (hGv j)
      (iOrderOnManifold_of_le (hGv j).1.quasiPlurisubharmonic (huj j))
  have hPH : P ≤ H := le_iInf hPB
  have hBanti : Antitone B := by
    intro i j hij
    exact iSingularityEnvelope_le_of_iOrderOnManifold γ (hGv i)
      (iOrderOnManifold_of_le (hGv i).1.quasiPlurisubharmonic (hanti hij))
  have hH : IsThetaPshPotential γ.val H := by
    constructor
    · have heq : H = (fun x => ⨅ j, B j x) := by
        funext x
        exact iInf_apply
      rw [heq]
      exact thetaPlurisubharmonic_iInf_of_antitone
        (fun j => (hB j).1) (fun x _ _ hij => hBanti hij x)
    · exact hP.2.mono hPH
  have hH0 : H ≤ 0 :=
    (iInf_le B 0).trans (iSingularityEnvelope_le_zero γ.val (v 0))
  have huσ (j : ℕ) : IsThetaPshPotential (θ + ε j • omega.form).val u :=
    LocalPotentials.isThetaPshPotential_add_of_semipositive hu
      (KahlerDomination.isSemipositive_smul omega.isSemipositive (hεpos j).le)
  let a : ℕ → ℝ≥0∞ := fun j => diagonalPotentialMass (θ + ε j • omega.form) u (huσ j)
  let m : ℕ → ℝ≥0∞ := fun j =>
    diagonalPotentialMass (θ + ε j • omega.form) (v j) (hv j).plurisubharmonic
  let L : ℝ≥0∞ := diagonalPotentialMass θ u hu
  have hL : 0 < L := hpos
  have hLtop : L ≠ ⊤ := (globalMixedMass_lt_top omega
    (fun _ : Fin n => hu.1)).ne
  have ha (j : ℕ) : L ≤ a j :=
    DivisorialDomination.diagonalPotentialMass_le_of_le_add_smul
      omega (hεpos j) hu (huσ j) (le_refl u)
  have hm : Tendsto m atTop (𝓝 L) :=
    tendsto_diagonalPotentialMass_iInf_varying_models omega θ hεpos hεanti hεlim hv hanti
  have hselect (r : ℕ) : ∃ j : ℕ, r ≤ j ∧
      ConvexCombEnvelopeMass.IsAdmissibleWeight n (a j) (m j) ((r : ℝ) + 2) := by
    have ht : (1 : ℝ) < (r : ℝ) + 2 := by
      have hr : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
      linarith
    have hadm := eventually_isAdmissibleWeight (n := n) hL hLtop ha hm ht
    exact ((eventually_ge_atTop r).and hadm).exists
  choose N _hN hAdm using hselect
  have hbar (r : ℕ) : ∃ η : M → EReal,
      IsThetaPshPotential (θ + ε (N r) • omega.form).val η ∧
      convexComb ((r : ℝ) + 2)⁻¹ η (v (N r)) ≤ u := by
    have hbig : IsBigClass (RealBottChern.ofRepresentative
        (θ + ε (N r) • omega.form)) :=
      PositiveCurrentAssembly.isBigClass_add_smul_of_isThetaPshPotential
        omega θ hu (hεpos (N r))
    exact exists_thetaPsh_convexCombBarrier_of_isBigClass omega
      (θ + ε (N r) • omega.form) hbig (huσ (N r))
      (hv (N r)).plurisubharmonic (huj (N r))
      (lt_of_lt_of_le hL (ha (N r))) (hAdm r)
  choose η hη hbarη using hbar
  have hηG (r : ℕ) : IsThetaPshPotential γ.val (η r) := by
    have h := LocalPotentials.isThetaPshPotential_add_of_semipositive (hη r)
      (KahlerDomination.isSemipositive_smul omega.isSemipositive (henlarge (N r)))
    rwa [hforms (N r)] at h
  let s : ℕ → Ioo (0 : ℝ) 1 := fun r => ⟨((r : ℝ) + 2)⁻¹, by
    constructor
    · positivity
    · exact inv_lt_one_of_one_lt₀ (by
        have hr : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
        linarith)⟩
  have hs : Tendsto (fun r => (s r).val) atTop (𝓝 (0 : ℝ)) := by
    have hh := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (tendsto_add_atTop_nat 1)
    simpa only [Function.comp_def, s, Nat.cast_add, Nat.cast_one, add_assoc,
      one_add_one_eq_two, one_div] using hh
  have hlow (r : ℕ) : (fun x => ((s r).val : EReal) *
      iSingularityEnvelope γ.val (η r) x +
      ((1 - (s r).val : ℝ) : EReal) * H x) ≤ P := by
    have hc := iSingularityEnvelope_convexCombination_le
      (hηG r) (hGv (N r))
      (sub_pos.mpr (s r).property.2) (sub_lt_self 1 (s r).property.1)
    have heq : (fun x => ((1 - (1 - (s r).val) : ℝ) : EReal) * η r x +
        ((1 - (s r).val : ℝ) : EReal) * v (N r) x) =
        convexComb (s r).val (η r) (v (N r)) := by
      funext x
      simp only [sub_sub_cancel, convexComb]
    rw [heq] at hc
    have horder : iSingularityEnvelope γ.val
        (convexComb (s r).val (η r) (v (N r))) ≤ P :=
      iSingularityEnvelope_le_of_iOrderOnManifold γ hGu
        (iOrderOnManifold_of_le hGu.1.quasiPlurisubharmonic (hbarη r))
    intro x
    have hHB : H x ≤ B (N r) x := iInf_le B (N r) x
    have hscale : ((1 - (s r).val : ℝ) : EReal) * H x ≤
        ((1 - (s r).val : ℝ) : EReal) * B (N r) x :=
      mul_le_mul_of_nonneg_left hHB (by exact_mod_cast (sub_pos.mpr (s r).property.2).le)
    have hh := hc x
    simp only [sub_sub_cancel] at hh
    exact (add_le_add (le_refl _) hscale).trans (hh.trans (horder x))
  have hbound (r : ℕ) : globalL1EDistance (kahlerVolume omega) P H ≤
      globalL1EDistance (kahlerVolume omega)
        (fun x => ((s r).val : EReal) * iSingularityEnvelope γ.val (η r) x)
        (fun _ => 0) := by
    apply lintegral_mono
    intro x
    exact canonical_gap_le_scaled_normalized_lower (hH0 x)
      (iSingularityEnvelope_le_zero γ.val (η r) x)
      (hPH x) (s r).property.1 (hlow r x)
  have hupper := (tendsto_global_and_manifoldL1_iSingularityEnvelope_smul
    omega γ atTop η hηG (fun r => (s r).val) (fun r => (s r).property.1) hs).1
  have hlim : Tendsto (fun _ : ℕ => globalL1EDistance (kahlerVolume omega) P H)
      atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hupper (fun _ => zero_le) hbound
  have hloc : ManifoldL1LocallyTendsto (n := n) (fun _ : ℕ => P) atTop H :=
    (manifoldL1LocallyTendsto_iff_tendsto_globalL1EDistance
      (KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume omega)
      (fun _ => hP.1.quasiPlurisubharmonic.upperSemicontinuous.measurable)
      hH.1.quasiPlurisubharmonic.upperSemicontinuous.measurable).mpr hlim
  have hHP : H ≤ P := le_of_manifoldL1LocallyTendsto
    (fun _ => hP) hH hP hloc (fun _ => le_refl P)
  exact le_antisymm hHP hPH

end
end SGPT.Foundations.Analysis.Pending.IEnvelopeVaryingBackgroundModelInfimum
