import SGPT.NAPotential.Supremum
import SGPT.Foundations.Analysis.Pending.SingularPBackgroundMassPolynomial
import SGPT.Foundations.Analysis.Pending.KahlerVolumePositive

/-! # The infimum of a decreasing net of non-Archimedean metrics

Source `def:NApotential:L525`, `prop:NApotential:L548`, `prop:infGammiotherprop2` and the
infimum clause of `prop:resclacompat2` of `chapter_NApotential.tex`.

For a decreasing net `(Γ^i)_{i ∈ I}` in `PSH^NA(X, θ)` with `inf_i Γ^i_max > -∞`
(`eq:decnetcontition`), the component of `inf_i Γ^i` at a Kähler form `ω` is the test-curve
infimum `inf_i Γ^{i,θ+ω}` (`def:testcurinf`).  The book observes that this lies in
`PSH^NA(X, θ+ω)_{>0}` "by `prop:inftcistc`"; the test-curve infimum requires the uniform
positive mass condition of `def:testcurinf`, which is proved here: every slice of a component
at `ω` is the `𝓘`-envelope of a `θ + ω/2`-psh function, hence has mass at least
`2^{-n} ∫_X ω^n` in the class `θ + ω`.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set MeasureTheory
open scoped ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- Expanding `∫ (α + c ω + dd^c u)^n` in `c` and keeping the top-degree term: the mass of a
genuine `α`-psh potential in the class `α + c ω` is at least `c^n ∫ ω^n`. -/
theorem sourceNA_diagonalMass_add_smul_lower_bound (omega : KahlerBackground n M)
    {α : ClosedRealOneOneForm n M} {u : M → EReal} (hu : IsThetaPshPotential α.val u)
    {c : ℝ} (hc : 0 < c) (hu' : IsThetaPshPotential (α + c • omega.form).val u) :
    ENNReal.ofReal (c ^ n * (DiagonalMass.diagonalPotentialMass omega.form (fun _ => 0)
        (PluripolarCapacityDichotomy.isThetaPshPotential_zero omega)).toReal) ≤
      DiagonalMass.diagonalPotentialMass (α + c • omega.form) u hu' := by
  classical
  have hpu := SingularPBackgroundMassPolynomial.globalMixedMass_add_background_toReal_eq_sum
    omega (θ := fun _ : Fin n => α) (u := fun _ : Fin n => u) (fun _ => hu) hc
  have hfin : DiagonalMass.diagonalPotentialMass (α + c • omega.form) u hu' ≠ ⊤ :=
    (MixedMass.globalMixedMass_lt_top omega (fun _ : Fin n => hu'.1)).ne
  rw [← ENNReal.ofReal_toReal hfin]
  apply ENNReal.ofReal_le_ofReal
  refine le_trans ?_ (le_of_eq hpu.symm)
  have hmem : (fun _ : Fin n => (none : Option (Fin n))) ∈
      Fintype.piFinset (CanonicalBackgroundPolynomial.backgroundChoices (n := n)) := by
    simp [CanonicalBackgroundPolynomial.backgroundChoices]
  refine le_trans (le_of_eq ?_) (Finset.single_le_sum
    (fun g _ => mul_nonneg (pow_nonneg hc.le _) ENNReal.toReal_nonneg) hmem)
  simp [CanonicalBackgroundPolynomial.backgroundDegree, MixedMassBoundedDifference.optForm,
    MixedMassBoundedDifference.optPot, DiagonalMass.diagonalPotentialMass,
    DiagonalMass.diagonalPotentialMeasure, MixedMass.globalMixedMass]

omit [BorelSpace M] in
/-- The diagonal mass depends on the background only through the form. -/
theorem sourceNA_diagonalMass_congr_form {α α' : ClosedRealOneOneForm n M} (h : α = α')
    {u : M → EReal} (hu : IsThetaPshPotential α.val u) (hu' : IsThetaPshPotential α'.val u) :
    DiagonalMass.diagonalPotentialMass α u hu = DiagonalMass.diagonalPotentialMass α' u hu' := by
  subst h
  rfl

variable [ConnectedSpace M] {θ σ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- The uniform lower bound `2^{-n} ∫_X ω^n` for the masses of all slices of all components
at the Kähler index `ω`. -/
def sourceNAComponentMassBound (κ : SourceKahlerForm n M) : ℝ≥0∞ :=
  ENNReal.ofReal ((1 / 2 : ℝ) ^ n *
    (DiagonalMass.diagonalPotentialMass (sourceKahlerFormRepresentative κ).form (fun _ => 0)
      (PluripolarCapacityDichotomy.isThetaPshPotential_zero _)).toReal)

omit [ConnectedSpace M] in
theorem sourceNAComponentMassBound_pos [Nonempty M] (κ : SourceKahlerForm n M) :
    0 < sourceNAComponentMassBound κ := by
  unfold sourceNAComponentMassBound
  apply ENNReal.ofReal_pos.mpr
  apply mul_pos (pow_pos (by norm_num) n)
  exact ENNReal.toReal_pos (KahlerVolumePositive.diagonalPotentialMass_zero_pos _).ne'
    (MixedMass.globalMixedMass_lt_top (sourceKahlerFormRepresentative κ)
      (fun _ : Fin n => (PluripolarCapacityDichotomy.isThetaPshPotential_zero
        (sourceKahlerFormRepresentative κ)).1)).ne

/-- Every slice of every component at the index `ω` of a non-Archimedean metric has mass at
least `2^{-n} ∫_X ω^n` in its class `θ + ω`. -/
theorem SourceNAPotential.component_mass_lower_bound (Γ : SourceNAPotential θ)
    (κ : SourceKahlerForm n M) (r : ℝ) (hr : r < (Γ.component κ).val.max) :
    sourceNAComponentMassBound κ ≤
      sourcePotentialNonPluripolarMeasure (sourceNAComponentBackground θ κ)
        ((Γ.component κ).val.potential ⟨r, hr⟩) ((Γ.component κ).val.thetaPSH _) univ := by
  let ω := sourceKahlerFormRepresentative κ
  let ω₀ := sourceNAHalfKahlerBackground ω
  let κ₀ := sourceKahlerFormOfBackground ω₀
  have hhalf : ω₀.form = (1 / 2 : ℝ) • ω.form := by
    simp only [ω₀, sourceNAHalfKahlerBackground, KahlerBackground.smul_form]
  have hsemi : (ω.form - ω₀.form).val.IsSemipositive := by
    have h : ω.form - ω₀.form = (1 / 2 : ℝ) • ω.form := by
      rw [hhalf]
      module
    rw [h]
    exact KahlerDomination.isSemipositive_smul ω.isSemipositive (by norm_num)
  have hle : sourceKahlerFormLE κ₀ κ := by
    have h := (sourceKahlerFormLE_ofBackground_iff ω₀ ω).mpr hsemi
    simpa only [ω, sourceKahlerFormRepresentative_class] using h
  have hr₀ : r < (Γ.component κ₀).val.max := by rwa [Γ.component_max_eq κ₀ κ]
  have hrT : r < (sourceIModelTestCurveTransition ω (sourceNAComponentBackground_difference θ hle)
      (Γ.component κ₀)).val.max := by
    rwa [sourceIModelTestCurveTransition_max]
  have hpot : (Γ.component κ).val.potential ⟨r, hr⟩ =
      sourceIEnvelope (sourceNAComponentBackground θ κ)
        ((Γ.component κ₀).val.potential ⟨r, hr₀⟩) :=
    (sourceTestCurve_potential_congr (congrArg Subtype.val (Γ.compatible κ₀ κ hle)) r hrT hr).symm.trans
      (sourceIModelTestCurveTransition_potential _ _ _ r hr₀ hrT)
  have hi : sourceIModel (sourceNAComponentBackground θ κ₀)
      ((Γ.component κ₀).val.potential ⟨r, hr₀⟩) :=
    (sourceIModel_iff_native _ _).mpr
      (((sourceIModelTestCurvesPositive_iff_slices ω _).mp (Γ.component κ₀).property) ⟨r, hr₀⟩)
  have hmass := (sourceIModel_transition_envelope_and_mass ω
    (sourceNAComponentBackground_difference θ hle) hi
    ((Γ.component κ₀).val.mass_positive ω ⟨r, hr₀⟩)).2
  have hrR : r < (Γ.realizedComponent ω₀).val.max := by rwa [Γ.realizedComponent_max]
  have hreal : (Γ.realizedComponent ω₀).val.potential ⟨r, hrR⟩ =
      (Γ.component κ₀).val.potential ⟨r, hr₀⟩ :=
    Γ.realizedComponent_potential ω₀ r hr₀ hrR
  have huR : IsThetaPshPotential
      (atlasClosedFormToNative (sourceTestCurveEnlargedBackground ω₀ θ)).val
      ((Γ.component κ₀).val.potential ⟨r, hr₀⟩) :=
    hreal ▸ (Γ.realizedComponent ω₀).val.native_thetaPSH ⟨r, hrR⟩
  have hform : atlasClosedFormToNative (sourceNAComponentBackground θ κ) =
      atlasClosedFormToNative (sourceTestCurveEnlargedBackground ω₀ θ) + (1 / 2 : ℝ) • ω.form := by
    rw [sourceNAComponentBackground_native, sourceTestCurveEnlargedBackground_native, hhalf]
    module
  have hκ : IsThetaPshPotential (atlasClosedFormToNative (sourceNAComponentBackground θ κ)).val
      ((Γ.component κ₀).val.potential ⟨r, hr₀⟩) :=
    (isThetaPSH_iff_nativeThetaPotential _ _).mp
      (sourceThetaPSH_of_semipositive_difference (sourceNAComponentBackground_difference θ hle) hi.1)
  have hκ' : IsThetaPshPotential
      (atlasClosedFormToNative (sourceTestCurveEnlargedBackground ω₀ θ) + (1 / 2 : ℝ) • ω.form).val
      ((Γ.component κ₀).val.potential ⟨r, hr₀⟩) := hform ▸ hκ
  have hlow := sourceNA_diagonalMass_add_smul_lower_bound ω huR (by norm_num : (0 : ℝ) < 1 / 2) hκ'
  calc sourceNAComponentMassBound κ
      ≤ DiagonalMass.diagonalPotentialMass
          (atlasClosedFormToNative (sourceTestCurveEnlargedBackground ω₀ θ) + (1 / 2 : ℝ) • ω.form)
          ((Γ.component κ₀).val.potential ⟨r, hr₀⟩) hκ' := hlow
    _ = DiagonalMass.diagonalPotentialMass (atlasClosedFormToNative (sourceNAComponentBackground θ κ))
          ((Γ.component κ₀).val.potential ⟨r, hr₀⟩) hκ :=
        sourceNA_diagonalMass_congr_form hform.symm _ _
    _ = sourcePotentialNonPluripolarMeasure (sourceNAComponentBackground θ κ)
          ((Γ.component κ₀).val.potential ⟨r, hr₀⟩)
          (sourceThetaPSH_of_semipositive_difference (sourceNAComponentBackground_difference θ hle)
            hi.1) univ := rfl
    _ = sourcePotentialNonPluripolarMeasure (sourceNAComponentBackground θ κ)
          (sourceIEnvelope (sourceNAComponentBackground θ κ)
            ((Γ.component κ₀).val.potential ⟨r, hr₀⟩))
          (isThetaPSH_sourceIEnvelope (sourceThetaPSH_of_semipositive_difference
            (sourceNAComponentBackground_difference θ hle) hi.1)) univ := hmass.symm
    _ = sourcePotentialNonPluripolarMeasure (sourceNAComponentBackground θ κ)
          ((Γ.component κ).val.potential ⟨r, hr⟩) ((Γ.component κ).val.thetaPSH _) univ :=
        sourcePotentialMass_congr hpot.symm _ _

/-- A non-Archimedean metric can only exist on a non-empty manifold. -/
theorem SourceNAPotential.nonempty_space (Γ : SourceNAPotential θ) (κ : SourceKahlerForm n M) :
    Nonempty M := by
  by_contra hn
  have hempty : (univ : Set M) = ∅ := by
    ext x
    exact False.elim (hn ⟨x⟩)
  have hpos := (Γ.component κ).val.positiveLimitMass
  rw [hempty, measure_empty] at hpos
  exact lt_irrefl 0 hpos

section DecreasingInf

variable {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]

omit [Preorder I] [IsDirectedOrder I] [Nonempty I] in
/-- The bound `eq:decnetcontition` read at any component. -/
theorem sourceNAFamily_component_bddBelow (omega : KahlerBackground n M)
    (Γ : I → SourceNAPotential θ)
    (hb : BddBelow (range fun i => sourceNAPotentialCutoff omega (Γ i)))
    (κ : SourceKahlerForm n M) :
    BddBelow (range fun i => ((Γ i).component κ).val.max) := by
  have h : (fun i => ((Γ i).component κ).val.max) = fun i => sourceNAPotentialCutoff omega (Γ i) :=
    funext fun i => (sourceNAPotentialCutoff_eq_component omega (Γ i) κ).symm
  rw [h]
  exact hb

omit [IsDirectedOrder I] [Nonempty I] in
/-- A decreasing net in the order of `def:NApotential:L274` has decreasing components. -/
theorem sourceNAFamily_component_antitone (Γ : I → SourceNAPotential θ)
    (ha : ∀ i j, i ≤ j → SourceNAPOrder (Γ j) (Γ i)) (κ : SourceKahlerForm n M) :
    ∀ i j, i ≤ j → SourceTestCurvePOrder ((Γ j).component κ).val ((Γ i).component κ).val :=
  fun i j hij => (sourceNAPOrder_iff_component (Γ j) (Γ i) κ).mp (ha i j hij)

omit [Preorder I] [IsDirectedOrder I] in
/-- The uniform positive mass condition of `def:testcurinf` holds for the components of every
non-empty family of non-Archimedean metrics. -/
theorem sourceNAFamily_component_massCondition (omega : KahlerBackground n M)
    (Γ : I → SourceNAPotential θ)
    (hb : BddBelow (range fun i => sourceNAPotentialCutoff omega (Γ i)))
    (κ : SourceKahlerForm n M) :
    SourceTestCurveInfMassCondition (fun i => ((Γ i).component κ).val)
      (sourceNAFamily_component_bddBelow omega Γ hb κ) := by
  have := (Γ (Classical.arbitrary I)).nonempty_space κ
  refine ⟨⟨sourceTestCurveInfCutoff (fun i => ((Γ i).component κ).val) - 1,
    Set.mem_Iio.mpr (sub_one_lt _)⟩, ?_⟩
  exact (sourceNAComponentMassBound_pos κ).trans_le
    (le_iInf fun i => SourceNAPotential.component_mass_lower_bound (Γ i) κ _ _)

/-- Source `def:NApotential:L525`: the infimum `inf_{i ∈ I} Γ^i` of a decreasing net satisfying
`eq:decnetcontition`.  Its component at every geometric Kähler index is the test-curve
infimum of the components (`eq:decnettestcurdef`). -/
def SourceNAPotential.decreasingInf (omega : KahlerBackground n M) (Γ : I → SourceNAPotential θ)
    (ha : ∀ i j, i ≤ j → SourceNAPOrder (Γ j) (Γ i))
    (hb : BddBelow (range fun i => sourceNAPotentialCutoff omega (Γ i))) : SourceNAPotential θ where
  component κ := SourcePositiveIModelTestCurve.decreasingInf (sourceKahlerFormRepresentative κ)
    (fun i => (Γ i).component κ) (sourceNAFamily_component_antitone Γ ha κ)
    (sourceNAFamily_component_bddBelow omega Γ hb κ)
    (sourceNAFamily_component_massCondition omega Γ hb κ)
  compatible κ ζ h := by
    rw [SourcePositiveIModelTestCurve.decreasingInf_ambient_independent
      (sourceKahlerFormRepresentative κ) (sourceKahlerFormRepresentative ζ)]
    exact sourceIModelTestCurveTransition_decreasingInf _ _ _ _ _ _ _
      (fun i => (Γ i).compatible κ ζ h) _ _ _

/-- The defining component formula `eq:decnettestcurdef`. -/
theorem SourceNAPotential.decreasingInf_component (omega : KahlerBackground n M)
    (Γ : I → SourceNAPotential θ) (ha : ∀ i j, i ≤ j → SourceNAPOrder (Γ j) (Γ i))
    (hb : BddBelow (range fun i => sourceNAPotentialCutoff omega (Γ i)))
    (κ : SourceKahlerForm n M) :
    (SourceNAPotential.decreasingInf omega Γ ha hb).component κ =
      SourcePositiveIModelTestCurve.decreasingInf (sourceKahlerFormRepresentative κ)
        (fun i => (Γ i).component κ) (sourceNAFamily_component_antitone Γ ha κ)
        (sourceNAFamily_component_bddBelow omega Γ hb κ)
        (sourceNAFamily_component_massCondition omega Γ hb κ) := rfl

/-- `inf_i Γ^i` is the unique element with the components `eq:decnettestcurdef`. -/
theorem SourceNAPotential.decreasingInf_unique (omega : KahlerBackground n M)
    (Γ : I → SourceNAPotential θ) (ha : ∀ i j, i ≤ j → SourceNAPOrder (Γ j) (Γ i))
    (hb : BddBelow (range fun i => sourceNAPotentialCutoff omega (Γ i)))
    (E : SourceNAPotential θ)
    (h : ∀ κ : SourceKahlerForm n M, E.component κ =
      SourcePositiveIModelTestCurve.decreasingInf (sourceKahlerFormRepresentative κ)
        (fun i => (Γ i).component κ) (sourceNAFamily_component_antitone Γ ha κ)
        (sourceNAFamily_component_bddBelow omega Γ hb κ)
        (sourceNAFamily_component_massCondition omega Γ hb κ)) :
    E = SourceNAPotential.decreasingInf omega Γ ha hb :=
  SourceNAPotential.ext h

/-- The cutoff of `inf_i Γ^i` is `inf_i Γ^i_max`. -/
theorem sourceNAPotentialCutoff_decreasingInf (omega : KahlerBackground n M)
    (Γ : I → SourceNAPotential θ) (ha : ∀ i j, i ≤ j → SourceNAPOrder (Γ j) (Γ i))
    (hb : BddBelow (range fun i => sourceNAPotentialCutoff omega (Γ i))) :
    sourceNAPotentialCutoff omega (SourceNAPotential.decreasingInf omega Γ ha hb) =
      sInf (range fun i => sourceNAPotentialCutoff omega (Γ i)) := rfl

/-- The infimum lies below every member of the net. -/
theorem SourceNAPotential.decreasingInf_le (omega : KahlerBackground n M)
    (Γ : I → SourceNAPotential θ) (ha : ∀ i j, i ≤ j → SourceNAPOrder (Γ j) (Γ i))
    (hb : BddBelow (range fun i => sourceNAPotentialCutoff omega (Γ i))) (i : I) :
    SourceNAPOrder (SourceNAPotential.decreasingInf omega Γ ha hb) (Γ i) :=
  let κ := sourceKahlerFormOfBackground omega
  ⟨κ, SourceTestCurve.decreasingInf_le (sourceKahlerFormRepresentative κ)
    (fun i => ((Γ i).component κ).val) (sourceNAFamily_component_antitone Γ ha κ)
    (sourceNAFamily_component_bddBelow omega Γ hb κ)
    (sourceNAFamily_component_massCondition omega Γ hb κ) i⟩

/-- Same-background greatest-lower-bound property of the test-curve decreasing infimum. -/
theorem SourceTestCurve.le_decreasingInf (omega : KahlerBackground n M)
    (Γ : I → SourceTestCurve θ) (ha : ∀ i j, i ≤ j → SourceTestCurvePOrder (Γ j) (Γ i))
    (hb : BddBelow (range fun i => (Γ i).max)) (hm : SourceTestCurveInfMassCondition Γ hb)
    (Ξ : SourceTestCurve θ) (h : ∀ i, SourceTestCurvePOrder Ξ (Γ i)) :
    SourceTestCurvePOrder Ξ (SourceTestCurve.decreasingInf omega Γ ha hb hm) := by
  have hc : Ξ.max ≤ sourceTestCurveInfCutoff Γ :=
    le_csInf (range_nonempty _) (by rintro _ ⟨i, rfl⟩; exact (h i).cutoff_le)
  apply (sourceTestCurvePOrder_iff omega _ _).mpr
  refine ⟨hc, fun r hr x => ?_⟩
  apply le_iInf
  intro i
  obtain ⟨hci, hsi⟩ := (sourceTestCurvePOrder_iff omega Ξ (Γ i)).mp (h i)
  exact hsi r hr x

/-- Identification of equal backgrounds keeps the intrinsic type of a curve. -/
theorem SourceTestCurve.castBackground_POrder_equivalent (omega : KahlerBackground n M)
    {α β : AtlasClosedRealOneOneForm (ofFixedModel n M)} (G : SourceTestCurve α) (h : α = β) :
    SourceTestCurvePOrder G (G.castBackground h) ∧ SourceTestCurvePOrder (G.castBackground h) G := by
  cases h
  exact ⟨SourceTestCurvePOrder.refl omega G, SourceTestCurvePOrder.refl omega G⟩

/-- Greatest-lower-bound property of the test-curve decreasing infimum, against a curve in
another background. -/
theorem SourceTestCurve.le_decreasingInf_cross_background (omega : KahlerBackground n M)
    (Γ : I → SourceTestCurve θ) (ha : ∀ i j, i ≤ j → SourceTestCurvePOrder (Γ j) (Γ i))
    (hb : BddBelow (range fun i => (Γ i).max)) (hm : SourceTestCurveInfMassCondition Γ hb)
    (Ξ : SourceTestCurve σ) (h : ∀ i, SourceTestCurvePOrder Ξ (Γ i)) :
    SourceTestCurvePOrder Ξ (SourceTestCurve.decreasingInf omega Γ ha hb hm) := by
  obtain ⟨η, ζ, hη, hζ, hforms⟩ :=
    sourceTestCurve_exists_common_semipositive_background omega θ σ
  let Ξ' := (Ξ.semipositiveProjection omega ζ hζ).castBackground hforms.symm
  have hX := Ξ.semipositiveProjection_equivalent omega ζ hζ
  have hXc := (Ξ.semipositiveProjection omega ζ hζ).castBackground_POrder_equivalent omega
    hforms.symm
  have hInputs (i : I) : SourceTestCurvePOrder Ξ' ((Γ i).semipositiveProjection omega η hη) :=
    (hXc.2.trans omega hX.2).trans omega
      ((h i).trans omega ((Γ i).semipositiveProjection_equivalent omega η hη).1)
  have hlow := SourceTestCurve.le_decreasingInf omega
    (fun i => (Γ i).semipositiveProjection omega η hη)
    (sourceTestCurveSemipositiveProjectedFamily_antitone omega Γ ha η hη) hb
    (sourceTestCurveSemipositiveProjectedFamily_inf_massCondition omega Γ ha hb hm η hη) Ξ' hInputs
  rw [← source_test_curve_decreasingInf_semipositive_projection_compatible omega Γ ha hb hm η hη]
    at hlow
  exact ((hX.1.trans omega hXc.1).trans omega hlow).trans omega
    ((SourceTestCurve.decreasingInf omega Γ ha hb hm).semipositiveProjection_equivalent
      omega η hη).2

/-- The infimum is the greatest lower bound, even against a metric in another background. -/
theorem SourceNAPotential.le_decreasingInf (omega : KahlerBackground n M)
    (Γ : I → SourceNAPotential θ) (ha : ∀ i j, i ≤ j → SourceNAPOrder (Γ j) (Γ i))
    (hb : BddBelow (range fun i => sourceNAPotentialCutoff omega (Γ i)))
    (Ξ : SourceNAPotential σ) (h : ∀ i, SourceNAPOrder Ξ (Γ i)) :
    SourceNAPOrder Ξ (SourceNAPotential.decreasingInf omega Γ ha hb) := by
  let κ := sourceKahlerFormOfBackground omega
  exact ⟨κ, SourceTestCurve.le_decreasingInf_cross_background (sourceKahlerFormRepresentative κ)
    (fun i => ((Γ i).component κ).val) (sourceNAFamily_component_antitone Γ ha κ)
    (sourceNAFamily_component_bddBelow omega Γ hb κ)
    (sourceNAFamily_component_massCondition omega Γ hb κ) (Ξ.component κ).val
    (fun i => (sourceNAPOrder_iff_component Ξ (Γ i) κ).mp (h i))⟩

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- The literal background `θ + ω` dominates the component background at the class of `ω`
(they have the same coefficients on every chart target). -/
theorem sourceNA_realized_difference_semipositive
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (ω : KahlerBackground n M) :
    (atlasClosedFormToNative (sourceTestCurveEnlargedBackground ω θ) -
      atlasClosedFormToNative (sourceNAComponentBackground θ
        (sourceKahlerFormOfBackground ω))).val.IsSemipositive := by
  intro e z hz v
  have h := sourceNAComponentBackground_geometricallyEq (θ := θ) ω e hz
  simp only [sub_eq_add_neg, ClosedRealOneOneForm.coeff_add,
    ClosedRealOneOneForm.coeff_neg, h, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.neg_apply]
  exact le_of_eq (add_neg_cancel _).symm

omit [IsDirectedOrder I] [Nonempty I] in
/-- The realized components of a decreasing net decrease. -/
theorem sourceNAFamily_realized_antitone (Γ : I → SourceNAPotential θ)
    (ha : ∀ i j, i ≤ j → SourceNAPOrder (Γ j) (Γ i)) (omega' : KahlerBackground n M) :
    ∀ i j, i ≤ j → SourceTestCurvePOrder ((Γ j).realizedComponent omega').val
      ((Γ i).realizedComponent omega').val :=
  fun i j hij => (sourceNAPOrder_iff_realizedComponents (Γ j) (Γ i) omega' omega').mp (ha i j hij)

omit [Preorder I] [IsDirectedOrder I] [Nonempty I] in
/-- The bound `eq:decnetcontition` read at any literal background. -/
theorem sourceNAFamily_realized_bddBelow (omega : KahlerBackground n M)
    (Γ : I → SourceNAPotential θ)
    (hb : BddBelow (range fun i => sourceNAPotentialCutoff omega (Γ i)))
    (omega' : KahlerBackground n M) :
    BddBelow (range fun i => ((Γ i).realizedComponent omega').val.max) := by
  have h : (fun i => ((Γ i).realizedComponent omega').val.max) =
      fun i => sourceNAPotentialCutoff omega (Γ i) :=
    funext fun i => (Γ i).realizedComponent_max_eq_cutoff omega omega'
  rw [h]
  exact hb

omit [Preorder I] [IsDirectedOrder I] in
/-- The uniform mass condition for realized components. -/
theorem sourceNAFamily_realized_massCondition (omega : KahlerBackground n M)
    (Γ : I → SourceNAPotential θ)
    (hb : BddBelow (range fun i => sourceNAPotentialCutoff omega (Γ i)))
    (omega' : KahlerBackground n M) :
    SourceTestCurveInfMassCondition (fun i => ((Γ i).realizedComponent omega').val)
      (sourceNAFamily_realized_bddBelow omega Γ hb omega') :=
  sourceIModelTestCurveTransition_family_massCondition omega'
    (sourceNA_realized_difference_semipositive θ omega')
    (fun i => (Γ i).component (sourceKahlerFormOfBackground omega'))
    (sourceNAFamily_component_bddBelow omega Γ hb _)
    (sourceNAFamily_component_massCondition omega Γ hb _)
    (fun i => (Γ i).realizedComponent omega') (fun _ => rfl) _

/-- The formula `eq:decnettestcurdef` in every literal background `θ + ω`. -/
theorem SourceNAPotential.decreasingInf_realizedComponent (omega : KahlerBackground n M)
    (Γ : I → SourceNAPotential θ) (ha : ∀ i j, i ≤ j → SourceNAPOrder (Γ j) (Γ i))
    (hb : BddBelow (range fun i => sourceNAPotentialCutoff omega (Γ i)))
    (omega' : KahlerBackground n M) :
    (SourceNAPotential.decreasingInf omega Γ ha hb).realizedComponent omega' =
      SourcePositiveIModelTestCurve.decreasingInf omega' (fun i => (Γ i).realizedComponent omega')
        (sourceNAFamily_realized_antitone Γ ha omega')
        (sourceNAFamily_realized_bddBelow omega Γ hb omega')
        (sourceNAFamily_realized_massCondition omega Γ hb omega') := by
  dsimp only [SourceNAPotential.realizedComponent, sourceIModelTestCurvePresentationEquiv,
    Equiv.coe_fn_mk]
  rw [SourceNAPotential.decreasingInf_component,
    SourcePositiveIModelTestCurve.decreasingInf_ambient_independent
      (sourceKahlerFormRepresentative (sourceKahlerFormOfBackground omega')) omega']
  exact sourceIModelTestCurveTransition_decreasingInf _ _ _ _ _ _ _ (fun i => rfl) _ _ _

/-- The definition extends the infimum of decreasing nets of positive `𝓘`-model test curves
(`def:testcurinf`) under the embedding of `prop:NAposNAemb`. -/
theorem sourcePositiveTestCurveToNA_decreasingInf (omega : KahlerBackground n M)
    (G : I → SourcePositiveIModelTestCurve θ)
    (ha : ∀ i j, i ≤ j → SourceTestCurvePOrder (G j).val (G i).val)
    (hb : BddBelow (range fun i => (G i).val.max))
    (hm : SourceTestCurveInfMassCondition (fun i => (G i).val) hb) :
    sourcePositiveTestCurveToNA (SourcePositiveIModelTestCurve.decreasingInf omega G ha hb hm) =
      SourceNAPotential.decreasingInf omega (fun i => sourcePositiveTestCurveToNA (G i))
        (fun i j hij => (sourcePositiveTestCurveToNA_POrder_iff omega (G j) (G i)).mpr (ha i j hij))
        (by simpa only [sourcePositiveTestCurveToNA_cutoff] using hb) := by
  apply SourceNAPotential.ext
  intro κ
  change sourceIModelTestCurveTransition (sourceKahlerFormRepresentative κ)
      (sourceNAComponentBackground_positive θ κ)
      (SourcePositiveIModelTestCurve.decreasingInf omega G ha hb hm) = _
  rw [SourcePositiveIModelTestCurve.decreasingInf_ambient_independent omega
    (sourceKahlerFormRepresentative κ)]
  exact sourceIModelTestCurveTransition_decreasingInf _ _ _ _ _ _ _ (fun i => rfl) _ _ _

omit [IsDirectedOrder I] [Nonempty I] in
/-- A decreasing net stays decreasing after a background change. -/
theorem sourceNAFamily_backgroundChange_antitone (omega : KahlerBackground n M)
    (Γ : I → SourceNAPotential θ) (ha : ∀ i j, i ≤ j → SourceNAPOrder (Γ j) (Γ i))
    (η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive) :
    ∀ i j, i ≤ j → SourceNAPOrder ((Γ j).backgroundChange η hη) ((Γ i).backgroundChange η hη) :=
  fun i j hij => (sourceNAPOrder_backgroundChange_iff omega (Γ j) (Γ i) η hη).mp (ha i j hij)

omit [Preorder I] [IsDirectedOrder I] [Nonempty I] in
/-- The bound `eq:decnetcontition` survives a background change. -/
theorem sourceNAFamily_backgroundChange_bddBelow (omega : KahlerBackground n M)
    (Γ : I → SourceNAPotential θ)
    (hb : BddBelow (range fun i => sourceNAPotentialCutoff omega (Γ i)))
    (η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive) :
    BddBelow (range fun i => sourceNAPotentialCutoff omega ((Γ i).backgroundChange η hη)) := by
  simpa only [sourceNAPotentialCutoff_backgroundChange] using hb

/-- Source `prop:NApotential:L548`: for every closed semipositive `(1,1)`-form `η`,
`P_{θ+η}[inf_i Γ^i]_𝓘 = inf_i P_{θ+η}[Γ^i]_𝓘`. -/
theorem SourceNAPotential.decreasingInf_backgroundChange (omega : KahlerBackground n M)
    (Γ : I → SourceNAPotential θ) (ha : ∀ i j, i ≤ j → SourceNAPOrder (Γ j) (Γ i))
    (hb : BddBelow (range fun i => sourceNAPotentialCutoff omega (Γ i)))
    (η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive) :
    (SourceNAPotential.decreasingInf omega Γ ha hb).backgroundChange η hη =
      SourceNAPotential.decreasingInf omega (fun i => (Γ i).backgroundChange η hη)
        (sourceNAFamily_backgroundChange_antitone omega Γ ha η hη)
        (sourceNAFamily_backgroundChange_bddBelow omega Γ hb η hη) := by
  apply SourceNAPotential.ext
  intro κ
  rw [SourceNAPotential.backgroundChange_component, SourceNAPotential.decreasingInf_component]
  unfold SourceNAPotential.reindexedComponent
  rw [SourceNAPotential.decreasingInf_realizedComponent,
    SourcePositiveIModelTestCurve.decreasingInf_ambient_independent
      (sourceNAAugmentedKahlerBackground η hη (sourceKahlerFormRepresentative κ))
      (sourceKahlerFormRepresentative κ)]
  apply Subtype.ext
  rw [SourcePositiveIModelTestCurve.castBackground_val,
    SourcePositiveIModelTestCurve.decreasingInf_val, SourcePositiveIModelTestCurve.decreasingInf_val]
  apply SourceTestCurve.castBackground_decreasingInf
  intro i
  rw [← SourcePositiveIModelTestCurve.castBackground_val]
  rfl

omit [IsDirectedOrder I] [Nonempty I] in
/-- Translation preserves a decreasing net. -/
theorem sourceNAFamily_translate_antitone (Γ : I → SourceNAPotential θ)
    (ha : ∀ i j, i ≤ j → SourceNAPOrder (Γ j) (Γ i)) (C : ℝ) :
    ∀ i j, i ≤ j → SourceNAPOrder ((Γ j).translate C) ((Γ i).translate C) := by
  intro i j hij
  obtain ⟨κ, hκ⟩ := ha i j hij
  exact ⟨κ, hκ.translate C⟩

omit [Preorder I] [IsDirectedOrder I] [Nonempty I] in
/-- The bound `eq:decnetcontition` survives translation. -/
theorem sourceNAFamily_translate_bddBelow (omega : KahlerBackground n M)
    (Γ : I → SourceNAPotential θ)
    (hb : BddBelow (range fun i => sourceNAPotentialCutoff omega (Γ i))) (C : ℝ) :
    BddBelow (range fun i => sourceNAPotentialCutoff omega ((Γ i).translate C)) := by
  obtain ⟨B, hB⟩ := hb
  refine ⟨B + C, ?_⟩
  rintro _ ⟨i, rfl⟩
  have hi := hB (mem_range_self i)
  simp only [sourceNAPotentialCutoff_translate]
  linarith

/-- The test-curve infimum commutes with translation. -/
theorem SourceTestCurve.decreasingInf_translate (omega : KahlerBackground n M)
    (Γ : I → SourceTestCurve θ) (ha : ∀ i j, i ≤ j → SourceTestCurvePOrder (Γ j) (Γ i))
    (hb : BddBelow (range fun i => (Γ i).max)) (hm : SourceTestCurveInfMassCondition Γ hb)
    (C : ℝ) (ha' : ∀ i j, i ≤ j → SourceTestCurvePOrder ((Γ j).translate C) ((Γ i).translate C))
    (hb' : BddBelow (range fun i => ((Γ i).translate C).max))
    (hm' : SourceTestCurveInfMassCondition (fun i => (Γ i).translate C) hb') :
    SourceTestCurve.decreasingInf omega (fun i => (Γ i).translate C) ha' hb' hm' =
      (SourceTestCurve.decreasingInf omega Γ ha hb hm).translate C := by
  have hmax : sourceTestCurveInfCutoff (fun i => (Γ i).translate C) =
      sourceTestCurveInfCutoff Γ + C := by
    unfold sourceTestCurveInfCutoff
    simp only [SourceTestCurve.translate_max]
    exact ((OrderIso.addRight C).map_ciInf hb).symm
  apply SourceTestCurve.ext_of_max_potential
  · rw [SourceTestCurve.translate_max]
    exact hmax
  · intro r hr hs
    rfl

/-- Source `prop:infGammiotherprop2`, first clause: `inf_i (Γ^i + C) = inf_i Γ^i + C`. -/
theorem SourceNAPotential.decreasingInf_translate (omega : KahlerBackground n M)
    (Γ : I → SourceNAPotential θ) (ha : ∀ i j, i ≤ j → SourceNAPOrder (Γ j) (Γ i))
    (hb : BddBelow (range fun i => sourceNAPotentialCutoff omega (Γ i))) (C : ℝ) :
    SourceNAPotential.decreasingInf omega (fun i => (Γ i).translate C)
        (sourceNAFamily_translate_antitone Γ ha C) (sourceNAFamily_translate_bddBelow omega Γ hb C) =
      (SourceNAPotential.decreasingInf omega Γ ha hb).translate C := by
  apply SourceNAPotential.ext
  intro κ
  apply Subtype.ext
  exact SourceTestCurve.decreasingInf_translate (sourceKahlerFormRepresentative κ)
    (fun i => ((Γ i).component κ).val) (sourceNAFamily_component_antitone Γ ha κ)
    (sourceNAFamily_component_bddBelow omega Γ hb κ)
    (sourceNAFamily_component_massCondition omega Γ hb κ) C
    (sourceNAFamily_component_antitone _ (sourceNAFamily_translate_antitone Γ ha C) κ)
    (sourceNAFamily_component_bddBelow omega _ (sourceNAFamily_translate_bddBelow omega Γ hb C) κ)
    (sourceNAFamily_component_massCondition omega _
      (sourceNAFamily_translate_bddBelow omega Γ hb C) κ)

/-- Source `prop:infGammiotherprop2`, second clause: if `Γ^i ≤ Γ'^i` for all `i`, with `Γ'^i`
a decreasing net in another background `θ'`, then `inf_i Γ^i ≤ inf_i Γ'^i`. -/
theorem SourceNAPotential.decreasingInf_mono (omega : KahlerBackground n M)
    (Γ : I → SourceNAPotential θ) (Δ : I → SourceNAPotential σ)
    (haΓ : ∀ i j, i ≤ j → SourceNAPOrder (Γ j) (Γ i))
    (haΔ : ∀ i j, i ≤ j → SourceNAPOrder (Δ j) (Δ i))
    (hbΓ : BddBelow (range fun i => sourceNAPotentialCutoff omega (Γ i)))
    (hbΔ : BddBelow (range fun i => sourceNAPotentialCutoff omega (Δ i)))
    (h : ∀ i, SourceNAPOrder (Γ i) (Δ i)) :
    SourceNAPOrder (SourceNAPotential.decreasingInf omega Γ haΓ hbΓ)
      (SourceNAPotential.decreasingInf omega Δ haΔ hbΔ) :=
  SourceNAPotential.le_decreasingInf omega Δ haΔ hbΔ _ fun i =>
    (SourceNAPotential.decreasingInf_le omega Γ haΓ hbΓ i).trans (h i)

/-- The test-curve infimum commutes with positive rescaling. -/
theorem SourceTestCurve.decreasingInf_positiveScale (omega : KahlerBackground n M)
    (Γ : I → SourceTestCurve θ) (ha : ∀ i j, i ≤ j → SourceTestCurvePOrder (Γ j) (Γ i))
    (hb : BddBelow (range fun i => (Γ i).max)) (hm : SourceTestCurveInfMassCondition Γ hb)
    {c : ℝ} (hc : 0 < c)
    (ha' : ∀ i j, i ≤ j →
      SourceTestCurvePOrder ((Γ j).positiveScale hc) ((Γ i).positiveScale hc))
    (hb' : BddBelow (range fun i => ((Γ i).positiveScale hc).max))
    (hm' : SourceTestCurveInfMassCondition (fun i => (Γ i).positiveScale hc) hb') :
    (SourceTestCurve.decreasingInf omega Γ ha hb hm).positiveScale hc =
      SourceTestCurve.decreasingInf omega (fun i => (Γ i).positiveScale hc) ha' hb' hm' := by
  apply SourceTestCurve.ext_of_max_potential
  · rw [SourceTestCurve.positiveScale_max]
    change c * sInf (range fun i => (Γ i).max) = sInf (range fun i => c * (Γ i).max)
    exact Real.mul_iInf_of_nonneg hc.le _
  · intro r hr hs
    rw [SourceTestCurve.positiveScale_potential]
    funext x
    exact (sourcePositiveERealOrderIso c hc).map_iInf _

/-- Positive rescaling, followed by an identification of backgrounds, commutes with the
decreasing infimum of positive `𝓘`-model test curves. -/
theorem SourcePositiveIModelTestCurve.decreasingInf_positiveScale_cast
    {α β : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    (omega omega' : KahlerBackground n M) (F : I → SourcePositiveIModelTestCurve α)
    (ha : ∀ i j, i ≤ j → SourceTestCurvePOrder (F j).val (F i).val)
    (hb : BddBelow (range fun i => (F i).val.max))
    (hm : SourceTestCurveInfMassCondition (fun i => (F i).val) hb) {c : ℝ} (hc : 0 < c)
    (e : sourceNAScaledBackground α c = β) (G : I → SourcePositiveIModelTestCurve β)
    (hG : ∀ i, ((F i).positiveScale omega' hc).castBackground e = G i)
    (ha' : ∀ i j, i ≤ j → SourceTestCurvePOrder (G j).val (G i).val)
    (hb' : BddBelow (range fun i => (G i).val.max))
    (hm' : SourceTestCurveInfMassCondition (fun i => (G i).val) hb') :
    ((SourcePositiveIModelTestCurve.decreasingInf omega F ha hb hm).positiveScale omega' hc).castBackground e =
      SourcePositiveIModelTestCurve.decreasingInf omega G ha' hb' hm' := by
  cases e
  have hG' : G = fun i => (F i).positiveScale omega' hc := funext fun i => (hG i).symm
  subst hG'
  apply Subtype.ext
  exact SourceTestCurve.decreasingInf_positiveScale omega (fun i => (F i).val) ha hb hm hc ha' hb' hm'

omit [Preorder I] [IsDirectedOrder I] [Nonempty I] in
/-- The bound `eq:decnetcontition` survives positive rescaling. -/
theorem sourceNAFamily_positiveScale_bddBelow (omega : KahlerBackground n M)
    (Γ : I → SourceNAPotential θ)
    (hb : BddBelow (range fun i => sourceNAPotentialCutoff omega (Γ i))) {c : ℝ} (hc : 0 < c) :
    BddBelow (range fun i => sourceNAPotentialCutoff omega ((Γ i).positiveScale hc)) := by
  obtain ⟨B, hB⟩ := hb
  refine ⟨c * B, ?_⟩
  rintro _ ⟨i, rfl⟩
  simp only [sourceNAPotentialCutoff_positiveScale]
  exact mul_le_mul_of_nonneg_left (hB (mem_range_self i)) hc.le

/-- Source `prop:resclacompat2`, infimum clause: `λ (inf_i Γ^i) = inf_i (λ Γ^i)`. -/
theorem SourceNAPotential.decreasingInf_positiveScale (omega : KahlerBackground n M)
    (Γ : I → SourceNAPotential θ) (ha : ∀ i j, i ≤ j → SourceNAPOrder (Γ j) (Γ i))
    (hb : BddBelow (range fun i => sourceNAPotentialCutoff omega (Γ i))) {c : ℝ} (hc : 0 < c) :
    (SourceNAPotential.decreasingInf omega Γ ha hb).positiveScale hc =
      SourceNAPotential.decreasingInf omega (fun i => (Γ i).positiveScale hc)
        (fun i j hij => (ha i j hij).positiveScale hc)
        (sourceNAFamily_positiveScale_bddBelow omega Γ hb hc) := by
  apply SourceNAPotential.ext
  intro κ
  change ((((SourceNAPotential.decreasingInf omega Γ ha hb).realizedComponent
      (sourceNADividedKahlerBackground hc (sourceKahlerFormRepresentative κ))).positiveScale
      (sourceKahlerFormRepresentative κ) hc).castBackground
      (sourceNAPositiveScaleComponentBackground_eq θ hc κ)) = _
  rw [SourceNAPotential.decreasingInf_realizedComponent, SourceNAPotential.decreasingInf_component,
    SourcePositiveIModelTestCurve.decreasingInf_ambient_independent
      (sourceKahlerFormRepresentative κ)
      (sourceNADividedKahlerBackground hc (sourceKahlerFormRepresentative κ))]
  exact SourcePositiveIModelTestCurve.decreasingInf_positiveScale_cast _ _ _ _ _ _ hc _ _
    (fun i => rfl) _ _ _

end DecreasingInf

end SGPT.PSH.VariableComplexAtlas
