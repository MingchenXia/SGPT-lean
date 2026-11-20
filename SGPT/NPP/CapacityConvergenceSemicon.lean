import SGPT.NPP.CapacityConvergenceMonotone
import SGPT.Envelopes.SourceNonPluripolarMassOrder
import SGPT.PSH.SourceCapacityConvergence

/-!
# The semicontinuity theorem of non-pluripolar products

Source `thm:semicon` (chapter `chapter_npp.tex`, the semicontinuity theorem; the book cites
Darvas–Di Nezza–Lu, survey, Theorem 2.6; complete proof in Xia, *Foundations of
pluripotential theory*, `thm:nonpluripolar-capacity-lower-limit`).

Let `X` be a connected compact Kähler manifold of dimension `n`, `θ_1, …, θ_n` closed real
smooth `(1,1)`-forms, `φ_j, φ_j^k ∈ PSH(X, θ_j)`, and let `χ_k, χ` be nonnegative uniformly
bounded quasi-continuous functions with `χ_k → χ` in capacity. Assume that for every `j`,
either `φ_j^k` decreases to `φ_j`, or `φ_j^k` increases to `φ_j` almost everywhere. Then

* (`sourceSemicon_liminf`, `eq:semicon1`)
  `liminf_k ∫ χ_k θ_{1,φ_1^k} ∧ ⋯ ∧ θ_{n,φ_n^k} ≥ ∫ χ θ_{1,φ_1} ∧ ⋯ ∧ θ_{n,φ_n}`;
* (`sourceSemicon_tendsto_integral`) if the total masses converge, then
  `χ_k θ_{1,φ_1^k} ∧ ⋯ ∧ θ_{n,φ_n^k} → χ θ_{1,φ_1} ∧ ⋯ ∧ θ_{n,φ_n}` weakly as measures (against
  every continuous function), and (`sourceSemicon_tendsto_lintegral`) the limit in
  `eq:semicon1` exists and equality holds.

Conventions: quasi-continuity and convergence in capacity are the source `def:qc_fun` and
`def:conv_cap` (`SourceQuasiContinuousOn`, `SourceTendstoInCapacity`) on `U = X`, with respect
to the `θ`-capacity `Cap_{θ_c}` of an arbitrary reference form `θ_c` of big class (the
standing assumption of `sec:qc`); "almost everywhere" is with respect to the Lebesgue measures
of the charts (`ChartTendstoAE`). The non-pluripolar products are the source mixed
non-pluripolar measures (`sourceMixedNonPluripolarMeasure`).

The proof reduces the source data to Kähler capacity (`exists_source_capacity_control`, one
half of `thm:comp_capa`), the monotone hypotheses to convergence in capacity
(`tendsto_capacity_gap_of_antitone`, `tendsto_capacity_gap_of_monotone_ae`), and applies the
moving-weight semicontinuity `lintegral_le_liminf_moving` and `tendsto_integral_moving`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology BigOperators ENNReal

namespace SGPT.NPP.CapacityConvergence

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open ThetaCapacity CapacityWeightedConvergence GlobalNonPluripolar
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.PSH.VariableComplexAtlas

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- A source quasi-continuous real function on `X` (for the capacity of a big class) is Borel
and quasi-continuous for the Kähler capacity. -/
theorem quasiContinuousFor_kahler_of_source (ω : KahlerBackground n M)
    (θc : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θc)))
    {χ : M → ℝ} (hχ : SourceQuasiContinuousOn θc ⊤ (fun x => (χ x.1 : EReal))) :
    Measurable χ ∧ QuasiContinuousFor (thetaCapacity ω.form (fun _ => 0)) χ := by
  have hmk : Continuous (fun x : M => (⟨x, mem_univ x⟩ : (⊤ : Opens M))) :=
    continuous_id.subtype_mk _
  refine ⟨?_, ?_⟩
  · have h := measurable_ereal_toReal.comp (hχ.1.comp hmk.measurable)
    simpa only [Function.comp_def, EReal.toReal_coe] using h
  · intro η hη
    obtain ⟨r, _hr0, hrpos, hrη⟩ := ENNReal.lt_iff_exists_real_btwn.mp hη
    have hr : 0 < r := ENNReal.ofReal_pos.mp hrpos
    have hε : 0 < r / 2 := half_pos hr
    obtain ⟨Cc, hCc, hcontrol⟩ := SGPT.NPP.exists_source_capacity_control ω θc hbig hε
    obtain ⟨G, hGo, -, hGcap, hreal⟩ := hχ.2 (r / 2 / Cc) (div_pos hε hCc)
    refine ⟨G, hGo, ?_, ?_⟩
    · calc thetaCapacity ω.form (fun _ => 0) G
          ≤ ENNReal.ofReal (r / 2) + ENNReal.ofReal Cc * sourceThetaCapacity θc G :=
            hcontrol G hGo.measurableSet
        _ ≤ ENNReal.ofReal (r / 2) + ENNReal.ofReal Cc * ENNReal.ofReal (r / 2 / Cc) :=
            add_le_add le_rfl (mul_le_mul_right hGcap _)
        _ = ENNReal.ofReal r := by
            rw [← ENNReal.ofReal_mul hCc.le, mul_div_cancel₀ _ hCc.ne',
              ← ENNReal.ofReal_add hε.le hε.le, add_halves]
        _ < η := hrη
    · obtain ⟨g, hg, hfg⟩ := hreal
      refine (hg.comp hmk.continuousOn (fun x hx => hx)).congr (fun x hx => ?_)
      have h := hfg (show (⟨x, mem_univ x⟩ : (⊤ : Opens M)) ∈ {y : (⊤ : Opens M) | y.1 ∉ G}
        from hx)
      exact EReal.coe_injective h

/-- Source convergence in capacity (for a big class) of real functions on `X` gives
convergence of the absolute gaps in Kähler capacity. -/
theorem kahler_gap_tendsto_of_source (ω : KahlerBackground n M)
    (θc : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θc)))
    {χ : ℕ → M → ℝ} {χ₀ : M → ℝ} (hχm : ∀ k, Measurable (χ k)) (hχ₀m : Measurable χ₀)
    (h : SourceTendstoInCapacity θc ⊤ (fun k (x : (⊤ : Opens M)) => (χ k x.1 : EReal)) atTop
      (fun x => (χ₀ x.1 : EReal))) :
    ∀ c : ℝ, 0 < c → Tendsto (fun k => thetaCapacity ω.form (fun _ => 0)
      {x | c < |χ k x - χ₀ x|}) atTop (𝓝 0) := by
  intro c hc
  have hu := ((sourceTendstoInCapacity_iff_union θc ⊤ _ atTop _).mp h).2.2 c hc
  have hset (k : ℕ) :
      sourceCapacityUpperGap ⊤ (fun x : (⊤ : Opens M) => (χ k x.1 : EReal))
          (fun x => (χ₀ x.1 : EReal)) c ∪
        sourceCapacityLowerGap ⊤ (fun x : (⊤ : Opens M) => (χ k x.1 : EReal))
          (fun x => (χ₀ x.1 : EReal)) c = {x | c < |χ k x - χ₀ x|} := by
    ext x
    exact sourceCapacityGap_coe_iff ⊤ (fun y : (⊤ : Opens M) => χ k y.1)
      (fun y : (⊤ : Opens M) => χ₀ y.1) c ⟨x, mem_univ x⟩
  simp only [hset] at hu
  exact SGPT.NPP.source_capacity_tendsto_implies_kahler ω θc hbig _
    (fun k => measurableSet_lt measurable_const
      (continuous_abs.measurable.comp ((hχm k).sub hχ₀m))) hu

/-- The monotone hypothesis of `thm:semicon` for one slot: either the sequence decreases to
the limit, or it increases to the limit almost everywhere. -/
def SourceMonotoneLimit (φ : ℕ → M → EReal) (φ₀ : M → EReal) : Prop :=
  ((∀ x, Antitone fun k => φ k x) ∧ ∀ x, Tendsto (fun k => φ k x) atTop (𝓝 (φ₀ x))) ∨
    ((∀ x, Monotone fun k => φ k x) ∧ ChartTendstoAE (n := n) φ φ₀)

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- Source `θ`-psh potentials are native `θ`-psh potentials. -/
theorem native_of_source {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) :
    IsThetaPshPotential (atlasClosedFormToNative θ).val u :=
  (isThetaPSH_iff_nativeThetaPotential θ u).mp hu

variable [ConnectedSpace M]

/-- Monotone source sequences converge in Kähler capacity. -/
theorem tendsto_capacity_gap_of_sourceMonotoneLimit (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : ℕ → M → EReal} {φ₀ : M → EReal}
    (hφ : ∀ k, (ofFixedModel n M).IsThetaPSH θ (φ k))
    (hφ₀ : (ofFixedModel n M).IsThetaPSH θ φ₀) (hmono : SourceMonotoneLimit (n := n) φ φ₀) :
    ∀ a : ℝ, 0 < a → Tendsto (fun k => thetaCapacity ω.form (fun _ => 0)
      {x | φ k x ≠ ⊥ ∧ φ₀ x ≠ ⊥ ∧ a < |(φ k x).toReal - (φ₀ x).toReal|}) atTop (𝓝 0) := by
  rcases hmono with ⟨ha, hl⟩ | ⟨hm, hae⟩
  · exact tendsto_capacity_gap_of_antitone ω (fun k => native_of_source (hφ k))
      (native_of_source hφ₀) ha hl
  · exact tendsto_capacity_gap_of_monotone_ae ω (fun k => native_of_source (hφ k))
      (native_of_source hφ₀) hm hae

/-- **`thm:semicon`, `eq:semicon1`**: lower semicontinuity of the weighted non-pluripolar
products along monotone sequences, with moving quasi-continuous weights converging in
capacity. -/
theorem sourceSemicon_liminf (ω : KahlerBackground n M)
    (θc : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θc)))
    (θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M))
    {φ : ℕ → Fin n → M → EReal} {φ₀ : Fin n → M → EReal}
    (hφ : ∀ k j, (ofFixedModel n M).IsThetaPSH (θ j) (φ k j))
    (hφ₀ : ∀ j, (ofFixedModel n M).IsThetaPSH (θ j) (φ₀ j))
    (hmono : ∀ j, SourceMonotoneLimit (n := n) (fun k => φ k j) (φ₀ j))
    {χ : ℕ → M → ℝ} {χ₀ : M → ℝ} {C : ℝ}
    (hχC : ∀ k x, 0 ≤ χ k x ∧ χ k x ≤ C) (hχ₀C : ∀ x, 0 ≤ χ₀ x ∧ χ₀ x ≤ C)
    (hχqc : ∀ k, SourceQuasiContinuousOn θc ⊤ (fun x => (χ k x.1 : EReal)))
    (hχ₀qc : SourceQuasiContinuousOn θc ⊤ (fun x => (χ₀ x.1 : EReal)))
    (hχcap : SourceTendstoInCapacity θc ⊤ (fun k (x : (⊤ : Opens M)) => (χ k x.1 : EReal))
      atTop (fun x => (χ₀ x.1 : EReal))) :
    (∫⁻ x, ENNReal.ofReal (χ₀ x) ∂sourceMixedNonPluripolarMeasure θ φ₀ hφ₀) ≤
      liminf (fun k => ∫⁻ x, ENNReal.ofReal (χ k x)
        ∂sourceMixedNonPluripolarMeasure θ (φ k) (hφ k)) atTop := by
  have hχm : ∀ k, Measurable (χ k) := fun k =>
    (quasiContinuousFor_kahler_of_source ω θc hbig (hχqc k)).1
  obtain ⟨hχ₀m, hχ₀Q⟩ := quasiContinuousFor_kahler_of_source ω θc hbig hχ₀qc
  let C' : ℝ := max C 0
  have h := lintegral_le_liminf_moving ω (θ := fun j => atlasClosedFormToNative (θ j))
    (u := φ) (v := φ₀) (fun k j => native_of_source (hφ k j)) (fun j => native_of_source (hφ₀ j))
    (fun j => tendsto_capacity_gap_of_sourceMonotoneLimit ω (fun k => hφ k j) (hφ₀ j) (hmono j))
    (C := C') (le_max_right _ _) (fun k x => (hχC k x).1)
    (fun x => ⟨(hχ₀C x).1, by
      rw [abs_of_nonneg (hχ₀C x).1]; exact (hχ₀C x).2.trans (le_max_left _ _)⟩)
    hχm hχ₀m hχ₀Q (kahler_gap_tendsto_of_source ω θc hbig hχm hχ₀m hχcap)
    continuous_const (fun _ => zero_le_one)
  simp only [mul_one] at h
  exact h

/-- **`thm:semicon`, second part**: if the total masses converge, then
`χ_k θ_{1,φ_1^k} ∧ ⋯ ∧ θ_{n,φ_n^k} → χ θ_{1,φ_1} ∧ ⋯ ∧ θ_{n,φ_n}` weakly as measures, i.e.
against every continuous function. -/
theorem sourceSemicon_tendsto_integral (ω : KahlerBackground n M)
    (θc : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θc)))
    (θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M))
    {φ : ℕ → Fin n → M → EReal} {φ₀ : Fin n → M → EReal}
    (hφ : ∀ k j, (ofFixedModel n M).IsThetaPSH (θ j) (φ k j))
    (hφ₀ : ∀ j, (ofFixedModel n M).IsThetaPSH (θ j) (φ₀ j))
    (hmono : ∀ j, SourceMonotoneLimit (n := n) (fun k => φ k j) (φ₀ j))
    {χ : ℕ → M → ℝ} {χ₀ : M → ℝ} {C : ℝ}
    (hχC : ∀ k x, 0 ≤ χ k x ∧ χ k x ≤ C) (hχ₀C : ∀ x, 0 ≤ χ₀ x ∧ χ₀ x ≤ C)
    (hχqc : ∀ k, SourceQuasiContinuousOn θc ⊤ (fun x => (χ k x.1 : EReal)))
    (hχ₀qc : SourceQuasiContinuousOn θc ⊤ (fun x => (χ₀ x.1 : EReal)))
    (hχcap : SourceTendstoInCapacity θc ⊤ (fun k (x : (⊤ : Opens M)) => (χ k x.1 : EReal))
      atTop (fun x => (χ₀ x.1 : EReal)))
    (hmass : Tendsto (fun k => sourceMixedNonPluripolarMass θ (φ k) (hφ k)) atTop
      (𝓝 (sourceMixedNonPluripolarMass θ φ₀ hφ₀)))
    (g : C(M, ℝ)) :
    Tendsto (fun k => ∫ x, g x * χ k x ∂sourceMixedNonPluripolarMeasure θ (φ k) (hφ k)) atTop
      (𝓝 (∫ x, g x * χ₀ x ∂sourceMixedNonPluripolarMeasure θ φ₀ hφ₀)) := by
  have hχm : ∀ k, Measurable (χ k) := fun k =>
    (quasiContinuousFor_kahler_of_source ω θc hbig (hχqc k)).1
  obtain ⟨hχ₀m, hχ₀Q⟩ := quasiContinuousFor_kahler_of_source ω θc hbig hχ₀qc
  let C' : ℝ := max C 0
  exact tendsto_integral_moving ω (θ := fun j => atlasClosedFormToNative (θ j))
    (u := φ) (v := φ₀) (fun k j => native_of_source (hφ k j)) (fun j => native_of_source (hφ₀ j))
    (fun j => tendsto_capacity_gap_of_sourceMonotoneLimit ω (fun k => hφ k j) (hφ₀ j) (hmono j))
    hmass (C := C') (le_max_right _ _)
    (fun k x => ⟨(hχC k x).1, (hχC k x).2.trans (le_max_left _ _)⟩)
    (fun x => ⟨(hχ₀C x).1, (hχ₀C x).2.trans (le_max_left _ _)⟩)
    hχm hχ₀m hχ₀Q (kahler_gap_tendsto_of_source ω θc hbig hχm hχ₀m hχcap) g

/-- **`thm:semicon`, "in particular"**: under mass convergence the limit in `eq:semicon1`
exists and equality holds. -/
theorem sourceSemicon_tendsto_lintegral (ω : KahlerBackground n M)
    (θc : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θc)))
    (θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M))
    {φ : ℕ → Fin n → M → EReal} {φ₀ : Fin n → M → EReal}
    (hφ : ∀ k j, (ofFixedModel n M).IsThetaPSH (θ j) (φ k j))
    (hφ₀ : ∀ j, (ofFixedModel n M).IsThetaPSH (θ j) (φ₀ j))
    (hmono : ∀ j, SourceMonotoneLimit (n := n) (fun k => φ k j) (φ₀ j))
    {χ : ℕ → M → ℝ} {χ₀ : M → ℝ} {C : ℝ}
    (hχC : ∀ k x, 0 ≤ χ k x ∧ χ k x ≤ C) (hχ₀C : ∀ x, 0 ≤ χ₀ x ∧ χ₀ x ≤ C)
    (hχqc : ∀ k, SourceQuasiContinuousOn θc ⊤ (fun x => (χ k x.1 : EReal)))
    (hχ₀qc : SourceQuasiContinuousOn θc ⊤ (fun x => (χ₀ x.1 : EReal)))
    (hχcap : SourceTendstoInCapacity θc ⊤ (fun k (x : (⊤ : Opens M)) => (χ k x.1 : EReal))
      atTop (fun x => (χ₀ x.1 : EReal)))
    (hmass : Tendsto (fun k => sourceMixedNonPluripolarMass θ (φ k) (hφ k)) atTop
      (𝓝 (sourceMixedNonPluripolarMass θ φ₀ hφ₀))) :
    Tendsto (fun k => ∫⁻ x, ENNReal.ofReal (χ k x)
        ∂sourceMixedNonPluripolarMeasure θ (φ k) (hφ k)) atTop
      (𝓝 (∫⁻ x, ENNReal.ofReal (χ₀ x) ∂sourceMixedNonPluripolarMeasure θ φ₀ hφ₀)) := by
  have hχm : ∀ k, Measurable (χ k) := fun k =>
    (quasiContinuousFor_kahler_of_source ω θc hbig (hχqc k)).1
  have hχ₀m : Measurable χ₀ := (quasiContinuousFor_kahler_of_source ω θc hbig hχ₀qc).1
  have h := sourceSemicon_tendsto_integral ω θc hbig θ hφ hφ₀ hmono hχC hχ₀C hχqc hχ₀qc hχcap
    hmass (ContinuousMap.const M 1)
  simp only [ContinuousMap.const_apply, one_mul] at h
  have hfin (u : Fin n → M → EReal) (hu : ∀ j, (ofFixedModel n M).IsThetaPSH (θ j) (u j)) :
      IsFiniteMeasure (sourceMixedNonPluripolarMeasure θ u hu) :=
    globalMixedMeasure_isFiniteMeasure ω _
  have heq (u : Fin n → M → EReal) (hu : ∀ j, (ofFixedModel n M).IsThetaPSH (θ j) (u j))
      (w : M → ℝ) (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x ∧ w x ≤ C) :
      ENNReal.ofReal (∫ x, w x ∂sourceMixedNonPluripolarMeasure θ u hu) =
        ∫⁻ x, ENNReal.ofReal (w x) ∂sourceMixedNonPluripolarMeasure θ u hu := by
    let := hfin u hu
    refine ofReal_integral_eq_lintegral_ofReal (integrable_of_bounded (B := C) hw fun x => ?_)
      (Eventually.of_forall fun x => (hw0 x).1)
    rw [abs_of_nonneg (hw0 x).1]
    exact (hw0 x).2
  have h' := (ENNReal.continuous_ofReal.tendsto _).comp h
  simp only [Function.comp_def] at h'
  rw [heq φ₀ hφ₀ χ₀ hχ₀m hχ₀C] at h'
  exact h'.congr fun k => heq (φ k) (hφ k) (χ k) (hχm k) (hχC k)

end SGPT.NPP.CapacityConvergence
