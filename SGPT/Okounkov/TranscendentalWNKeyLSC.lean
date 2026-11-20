import SGPT.Okounkov.TranscendentalWNKeyLSCExcLocal
import SGPT.Okounkov.TranscendentalWNKeyLSCNull
import SGPT.Okounkov.TranscendentalWNKeyMain
import SGPT.Okounkov.TranscendentalWNDeformationBig

/-!
# Lower semicontinuity of the fibre masses (package WN-KEY, lane WN-LSC)

Blueprint `claude-tok-wn-key`, node `tok-wn-key:fibre-mass-lsc`; source WN21 §5 (the analytic
core of the easy inequality of Theorem 1.7).

`fibreMassLSC : FibreMassLSCStatement F`.  Let `T = Θ + dd^c φ` with `φ` gentle on the
deformation `𝒳`, nondegenerate on `X'` and on `ℰ`.  Given `δ > 0` and a neighbourhood `W` of
`0 ∈ ℙ¹`:

1. the restricted measures `ν' = ⟨(T|_{X'})ⁿ⟩` on `X` and `ν_ℰ = ⟨(T|_ℰ)ⁿ⟩` on `ℰ` are finite and
   do not charge `Z ∪ ι'⁻¹(P)`, resp. `(X' ∩ ℰ) ∪ P` (`P` the pole set of `φ`, closed since `φ` is
   gentle); inner regularity gives compact `K₁ ⊆ X \ (Z ∪ ι'⁻¹P)` and
   `K₂ ⊆ ℰ \ (X' ∪ P)` carrying all but `δ/4` of the masses;
2. `K₁` and `K₂` (in `𝒳`: `ι'(K₁)` and `K₂`) are disjoint compact sets with disjoint open
   neighbourhoods `O₀`, `O₁`;
3. away from `ℰ` (`strict_local_eventually_le`, globalized by `eventually_le_of_local`):
   eventually `ν'(K₁) ≤ ν_τ(K₁) + δ/4`, and `s_τ(K₁) ⊆ O₀` (`eventually_fibreSection_mapsTo`);
4. near `ℰ \ X'` (`exc_local_transportGood`, globalized by `transportGood_of_local`): eventually
   `ν_ℰ(K₂) ≤ ν_τ(T_τ) + δ/4` with `s_τ(T_τ) ⊆ O₁`;
5. so `K₁` and `T_τ` are disjoint and `ν'(X) + ν_ℰ(ℰ) ≤ ν_τ(X) + δ` for `τ ≠ 0` near `0`; for such
   `τ` the restriction `φ ∘ s_τ` is nondegenerate (`φ` is finite at `s_τ(x₁)` for a fixed
   `x₁ ∉ Z` with `φ(ι' x₁) ≠ -∞`, and `X` is connected).

Consequences (with `betaBig`, package WN-DEF2): the key easy inequality `keyEasy`
(`tok-wn:key-easy`) is unconditional, and WN21 Theorem C (`WNStatement`, `WNDerivativeStatement`)
holds conditionally on `KeyConvergenceStatement` and `ExceptionalRestrictedVolumeStatement` only
(`wnStatement_of_keyConvergence`, `wnDerivative_of_keyConvergence`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

universe u

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Manifold ContDiff ENNReal

namespace SGPT.Okounkov.TranscendentalWN

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.GlobalNonPluripolar
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open scoped SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open SGPT.Okounkov.TranscendentalMain
open SGPT.Okounkov.TranscendentalWN.LSC

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))

section Aux

variable {𝒳 : Type u} [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
  [IsComplexManifold (m + 1 + 1) 𝒳] {μ : 𝒳 → F.carrier × ProjectiveLine}

/-- Uniform version of `eventually_fibreSection_mapsTo` on a compact set off `Z`. -/
theorem eventually_mapsTo_of_isCompact (hμ : IsNormalConeDeformation F μ) {ι : F.carrier → 𝒳}
    (hμι : ∀ x, μ (ι x) = (x, projectiveZero)) {s : ProjectiveLine → F.carrier → 𝒳}
    (hsμ : ∀ p, p ≠ projectiveZero → ∀ x, μ (s p x) = (x, p)) {K : Set F.carrier}
    (hK : IsCompact K) (hKZ : ∀ x ∈ K, x ∉ F.flag (1 : Fin (m + 2))) {O : Set 𝒳} (hO : IsOpen O)
    (hKO : ∀ x ∈ K, ι x ∈ O) : ∀ᶠ p in 𝓝[≠] projectiveZero, MapsTo (s p) K O := by
  have h : ∀ᶠ p in 𝓝 projectiveZero, ∀ x ∈ K, p ≠ projectiveZero → s p x ∈ O := by
    refine hK.eventually_forall_of_forall_eventually fun x hx => ?_
    obtain ⟨U, hU, hxU, W, hW, h0W, hUW⟩ :=
      eventually_fibreSection_mapsTo F hμ hμι (hKZ x hx) hO (hKO x hx)
    filter_upwards [prod_mem_nhds (hW.mem_nhds h0W) (hU.mem_nhds hxU)] with z hz hz0
    exact hUW z.1 hz.1 hz0 (s z.1) (hsμ z.1 hz0) hz.2
  filter_upwards [nhdsWithin_le_nhds h, eventually_mem_nhdsWithin] with p hp hp0 x hx
  exact hp x hx hp0

end Aux

/-- **`tok-wn-key:fibre-mass-lsc`, eventual form** (WN21 §5; equivalent to the `liminf`
inequality `∫_{X'} ⟨(T|_{X'})ⁿ⟩ + ∫_ℰ ⟨(T|_ℰ)ⁿ⟩ ≤ liminf_{τ → 0} ∫_{X_τ} ⟨(T|_{X_τ})ⁿ⟩`): for every
`δ > 0`, for all `τ ≠ 0` close to `0`, the section `s_τ` of `μ` over `x ↦ (x, τ)` has a
nondegenerate restriction `φ ∘ s_τ` and
`∫_{X'} ⟨(T|_{X'})ⁿ⟩ + ∫_ℰ ⟨(T|_ℰ)ⁿ⟩ ≤ ∫_{X_τ} ⟨(T|_{X_τ})ⁿ⟩ + δ`. -/
theorem eventually_fibreMass_le (𝒳 : Type u) [TopologicalSpace 𝒳]
    [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳] [IsComplexManifold (m + 1 + 1) 𝒳]
    (μ : 𝒳 → F.carrier × ProjectiveLine) (hμ : IsNormalConeDeformation F μ)
    (Θ : ClosedRealOneOneForm (m + 1 + 1) 𝒳) (φ : 𝒳 → EReal)
    (hφ : φ ∈ TranscendentalCore.gentleCurrents Θ) (ι : F.carrier → 𝒳)
    (hι : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ ι)
    (hμι : ∀ x, μ (ι x) = (x, projectiveZero))
    (hX' : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι Θ).val (fun x => φ (ι x)))
    (hℰ : letI := exceptionalChartedSpace F hμ
      haveI := isComplexManifold_exceptional F hμ
      IsThetaPshPotential
        (ClosedRealOneOneForm.pullback (contMDiff_exceptionalInclusion F hμ) Θ).val
        (fun y : exceptionalSet F μ => φ y))
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∀ᶠ p in 𝓝[≠] projectiveZero, ∃ (s : F.carrier → 𝒳)
      (hs : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ s),
      (∀ x, μ (s x) = (x, p)) ∧
      ∃ hw : IsThetaPshPotential (ClosedRealOneOneForm.pullback hs Θ).val (fun x => φ (s x)),
        sectionMass F ι hι Θ φ hX' + exceptionalMass F hμ Θ φ hℰ ≤
          sectionMass F s hs Θ φ hw + δ := by
  classical
  let _ : MeasurableSpace F.carrier := borel F.carrier
  have _ : BorelSpace F.carrier := ⟨rfl⟩
  let _ := exceptionalChartedSpace F hμ
  have _ := isComplexManifold_exceptional F hμ
  let _ : MeasurableSpace (exceptionalSet F μ) := borel (exceptionalSet F μ)
  have _ : BorelSpace (exceptionalSet F μ) := ⟨rfl⟩
  have _ := compactSpace_exceptional F hμ
  have _ := compactSpace_normalCone F hμ
  have hφp : ThetaPlurisubharmonic Θ.val φ := hφ.1.1
  have hincl := contMDiff_exceptionalInclusion F hμ
  -- the sections over `τ ≠ 0`
  set sec : ProjectiveLine → F.carrier → 𝒳 := fun p =>
    if hp : p = projectiveZero then ι else Classical.choose (exists_fibreSection F hμ hp) with hsecdef
  have hsec : ∀ p, ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ (sec p) := by
    intro p
    by_cases hp : p = projectiveZero
    · simp only [hsecdef, hp, dite_true]
      exact hι
    · simp only [hsecdef, hp, dite_false]
      exact (Classical.choose_spec (exists_fibreSection F hμ hp)).1
  have hsecμ : ∀ p, p ≠ projectiveZero → ∀ x, μ (sec p x) = (x, p) := by
    intro p hp x
    simp only [hsecdef, hp, dite_false]
    exact (Classical.choose_spec (exists_fibreSection F hμ hp)).2.1 x
  -- the measures
  set νX := fibreMeasure hι Θ φ hφp with hνX
  set νE := fibreMeasure hincl Θ φ hφp with hνE
  set νp : ProjectiveLine → Measure F.carrier := fun p => fibreMeasure (hsec p) Θ φ hφp with hνp
  have _ : IsFiniteMeasure νX := globalMixedMeasure_isFiniteMeasure F.omega _
  obtain ⟨η'⟩ := nonempty_kahler_normalCone F hμ
  let ωE : PositiveClasses.KahlerBackground (m + 1) (exceptionalSet F μ) :=
    SubmanifoldKahlerRestriction.kahlerBackground (Nat.le_succ (m + 1))
      (fun _ hz => regularAtDim_exceptionalSet F hμ hz) η'
  have _ : IsFiniteMeasure νE := globalMixedMeasure_isFiniteMeasure ωE _
  set δ' : ℝ≥0∞ := δ / 2 / 2 with hδ'
  have hδ'0 : 0 < δ' := ENNReal.half_pos (ENNReal.half_pos hδ.ne').ne'
  -- the pole set
  set P : Set 𝒳 := {z | φ z = ⊥} with hP
  have hPc : IsClosed P := by
    have := isOpen_ne_bot_of_gentle hφ
    rw [← isOpen_compl_iff]
    convert this using 1
    ext z
    simp [hP]
  have hZc : IsClosed (F.flag (1 : Fin (m + 2))) := F.firstDivisor.1
  /- ### the compact set `K₁ ⊆ X \ (Z ∪ ι'⁻¹ P)` -/
  set U₁ : Set F.carrier := (F.flag (1 : Fin (m + 2)) ∪ ι ⁻¹' P)ᶜ with hU₁
  have hU₁o : IsOpen U₁ := (hZc.union (hPc.preimage hι.continuous)).isOpen_compl
  have hU₁ν : νX U₁ᶜ = 0 := by
    rw [hU₁, compl_compl]
    refine measure_union_null (fibreMeasure_flag_eq_zero F hι Θ φ hφp) ?_
    exact fibreMeasure_poles_eq_zero hι Θ φ hφp hX'
  obtain ⟨K₁, hK₁U, hK₁c, hK₁ν⟩ :=
    hU₁o.measurableSet.exists_isCompact_lt_add (measure_ne_top νX U₁) hδ'0.ne'
  have hνX : νX univ ≤ νX K₁ + δ' := by
    rw [← measure_add_measure_compl hU₁o.measurableSet, hU₁ν, add_zero]
    exact hK₁ν.le
  /- ### the compact set `K₂ ⊆ ℰ \ (X' ∪ P)` -/
  set U₂ : Set (exceptionalSet F μ) :=
    ((Subtype.val : exceptionalSet F μ → 𝒳) ⁻¹' strictCentralFibre F μ ∪
      {z | φ z.1 = ⊥})ᶜ with hU₂
  have hU₂o : IsOpen U₂ :=
    (((isClosed_strictCentralFibre F).preimage continuous_subtype_val).union
      (hPc.preimage continuous_subtype_val)).isOpen_compl
  have hU₂ν : νE U₂ᶜ = 0 := by
    rw [hU₂, compl_compl]
    refine measure_union_null (fibreMeasure_strict_eq_zero F hμ Θ φ hφp) ?_
    exact fibreMeasure_poles_eq_zero hincl Θ φ hφp hℰ
  obtain ⟨K₂, hK₂U, hK₂c, hK₂ν⟩ :=
    hU₂o.measurableSet.exists_isCompact_lt_add (measure_ne_top νE U₂) hδ'0.ne'
  have hνE : νE univ ≤ νE K₂ + δ' := by
    rw [← measure_add_measure_compl hU₂o.measurableSet, hU₂ν, add_zero]
    exact hK₂ν.le
  /- ### separation of `ι'(K₁)` and `K₂` -/
  have hK₁Z : ∀ x ∈ K₁, x ∉ F.flag (1 : Fin (m + 2)) := fun x hx h => hK₁U hx (Or.inl h)
  have hK₁P : ∀ x ∈ K₁, φ (ι x) ≠ ⊥ := fun x hx h => hK₁U hx (Or.inr h)
  have hdisj : Disjoint (ι '' K₁) (Subtype.val '' K₂) := by
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨x, hx, rfl⟩ ⟨z, -, hz⟩
    have hE : ι x ∈ exceptionalSet F μ := hz ▸ z.2
    have : μ (ι x) ∈ deformationCentre F := hE
    rw [hμι] at this
    exact hK₁Z x hx ((mem_deformationCentre_iff F).mp this).1
  obtain ⟨O₀, O₁, hO₀, hO₁, hKO₀, hKO₁, hO⟩ :=
    SeparatedNhds.of_isCompact_isCompact (hK₁c.image hι.continuous)
      (hK₂c.image continuous_subtype_val) hdisj
  /- ### the strict part -/
  have hstrict := eventually_le_of_local (l := 𝓝[≠] projectiveZero) (ν := νX) (νp := νp) hK₁c
    (fun x hx => strict_local_eventually_le F hμ hφ hι hμι hsec hsecμ (hK₁Z x hx) (hK₁P x hx))
    hK₁c.measurableSet subset_rfl hδ'0
  have hmaps₁ := eventually_mapsTo_of_isCompact F hμ hμι hsecμ hK₁c hK₁Z hO₀
    (fun x hx => hKO₀ ⟨x, hx, rfl⟩)
  /- ### the part near `ℰ` -/
  have hgood : TransportGood (l := 𝓝[≠] projectiveZero) νE Subtype.val sec νp K₂ :=
    transportGood_of_local continuous_subtype_val Subtype.val_injective hK₂c fun q hq =>
      exc_local_transportGood F hμ hφ hsec hsecμ q (fun h => hK₂U hq (Or.inl h))
        (fun h => hK₂U hq (Or.inr h))
  obtain ⟨T, hT⟩ := hgood O₁ hO₁ hKO₁ δ' hδ'0
  /- ### nondegeneracy of the restrictions to the fibres -/
  obtain ⟨x₁, hx₁Z, hx₁⟩ : ∃ x₁ ∈ (F.flag (1 : Fin (m + 2)))ᶜ, φ (ι x₁) ≠ ⊥ := by
    have hne : ((F.flag (1 : Fin (m + 2)))ᶜ).Nonempty := by
      have hd : Dense (F.flag (1 : Fin (m + 2)))ᶜ := by
        rw [dense_iff_closure_eq, closure_compl, interior_firstFlag F, compl_empty]
      exact hd.nonempty
    obtain ⟨x, hx⟩ := hne
    exact hX'.2 x _ hZc.isOpen_compl hx
  have hmaps₂ := eventually_mapsTo_of_isCompact F hμ hμι hsecμ (isCompact_singleton (x := x₁))
    (fun x hx => by rw [mem_singleton_iff.mp hx]; exact hx₁Z)
    (isOpen_ne_bot_of_gentle hφ) (fun x hx => by rw [mem_singleton_iff.mp hx]; exact hx₁)
  /- ### the estimate, for `τ` close to `0` -/
  filter_upwards [eventually_mem_nhdsWithin, hstrict, hmaps₁, hT, hmaps₂] with
    p hp0 hpstrict hpmaps₁ hpT hpmaps₂
  have hp0' : p ≠ projectiveZero := hp0
  have hw : IsThetaPshPotential (ClosedRealOneOneForm.pullback (hsec p) Θ).val
      (fun x => φ (sec p x)) :=
    ⟨GlobalPotentialPullback.thetaPlurisubharmonic_comp (hsec p) hφp,
      ThetaPshIdentityPrinciple.locallyNondegenerate_of_exists_ne_bot
        (GlobalPotentialPullback.thetaPlurisubharmonic_comp (hsec p) hφp)
        ⟨x₁, hpmaps₂ (mem_singleton x₁)⟩⟩
  refine ⟨sec p, hsec p, hsecμ p hp0', hw, ?_⟩
  have hdT : Disjoint K₁ (T p) := by
    refine Set.disjoint_left.mpr fun x hx1 hx2 => ?_
    exact Set.disjoint_left.mp hO (hpmaps₁ hx1) (hpT.2.1 hx2)
  have hsum : νp p K₁ + νp p (T p) ≤ νp p univ := by
    rw [← measure_union hdT hpT.1]
    exact measure_mono (subset_univ _)
  change νX univ + νE univ ≤ νp p univ + δ
  calc νX univ + νE univ ≤ (νX K₁ + δ') + (νE K₂ + δ') := add_le_add hνX hνE
    _ ≤ ((νp p K₁ + δ') + δ') + ((νp p (T p) + δ') + δ') := by
        gcongr
        exact hpT.2.2
    _ = (νp p K₁ + νp p (T p)) + ((δ' + δ') + (δ' + δ')) := by ring
    _ = (νp p K₁ + νp p (T p)) + δ := by
        rw [hδ', ENNReal.add_halves, ENNReal.add_halves]
    _ ≤ νp p univ + δ := by gcongr

/-- **`tok-wn-key:fibre-mass-lsc`** (WN21 §5): the lower semicontinuity of the fibre masses,
`∫_{X'} ⟨(T|_{X'})ⁿ⟩ + ∫_ℰ ⟨(T|_ℰ)ⁿ⟩ ≤ ∫_{X_τ} ⟨(T|_{X_τ})ⁿ⟩ + δ` for some `τ ≠ 0` in every
neighbourhood of `0`. -/
theorem fibreMassLSC : FibreMassLSCStatement F := by
  intro 𝒳 _ _ _ μ hμ Θ φ hφ ι hι hμι hX' hℰ δ hδ W hW
  have := nhdsWithin_projectiveZero_neBot
  obtain ⟨p, ⟨hpW, hp0⟩, h⟩ :=
    ((Filter.Eventually.and (nhdsWithin_le_nhds hW) eventually_mem_nhdsWithin).and
      (eventually_fibreMass_le F 𝒳 μ hμ Θ φ hφ ι hι hμι hX' hℰ hδ)).exists
  exact ⟨p, hpW, hp0, h⟩

/-- **`tok-wn:key-easy`** (WN21 Theorem 1.7, easy inequality), unconditionally:
`vol_{𝒳|X'}(β) + vol_{𝒳|ℰ}(β) ≤ vol(ξ)`. -/
theorem keyEasy : KeyEasyStatement F :=
  keyEasy_of_fibreMassLSC_of_betaBig F (fibreMassLSC F) (betaBig F)

/-- **WN21 Theorem C, integrated form with continuity** (`WNStatement`), conditional on
`KeyConvergenceStatement` (`tok-wn:convergence`) and `ExceptionalRestrictedVolumeStatement`
(`tok-wn:formula-E`) only. -/
theorem wnStatement_of_keyConvergence (hConv : KeyConvergenceStatement F)
    (hEx : ExceptionalRestrictedVolumeStatement F) : WNStatement F :=
  wnStatement_of_wnKey F (fibreMassLSC F) hConv (betaBig F) hEx

/-- **WN21 Theorem C** (`tok:ext-wn21`), conditional on `KeyConvergenceStatement` and
`ExceptionalRestrictedVolumeStatement` only. -/
theorem wnDerivative_of_keyConvergence (hConv : KeyConvergenceStatement F)
    (hEx : ExceptionalRestrictedVolumeStatement F) : WNDerivativeStatement F :=
  wnDerivative_of_wnKey F (fibreMassLSC F) hConv (betaBig F) hEx

end SGPT.Okounkov.TranscendentalWN
