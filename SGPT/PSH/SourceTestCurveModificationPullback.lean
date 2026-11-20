import SGPT.PSH.SourceIModelTestCurves
import SGPT.PSH.NativeThetaModificationDescent
import SGPT.PSH.SourcePIComparison
import SGPT.Okounkov.IEnvelopeModification
import SGPT.Foundations.Analysis.Pending.AnalyticModificationMixedMass

/-!
# Test curves under proper bimeromorphic morphisms

Source `prop:ETCbimero` and `prop:ETCIbimero` (chapter `chapter_testcurve`).

Let `π : Y → X` be a proper bimeromorphic holomorphic map between complex
manifolds of the same dimension (`IsAnalyticModification`), with `X` connected
and compact. We prove:

* the ordinary envelope `P_θ[·]` commutes with pull-back
  (`sourceSingularityEnvelope_modification_pullback`, the ingredient
  `prop:Penvbimero` quoted in the source proof);
* the usc-regularized supremum of a family commutes with pull-back;
* the non-pluripolar total mass is invariant, and model potentials pull back to
  model potentials;
* the pointwise pull-back `Γ ↦ (τ ↦ Γ_τ ∘ π)` is a bijection
  `TC(X,θ) ≃ TC(Y,π^*θ)`, which restricts to a bijection
  `TC(X,θ;φ) ≃ TC(Y,π^*θ;π^*φ)` (`prop:ETCbimero`) and further to a bijection of
  `𝓘`-model test curves `ℰ^NA(X,θ;φ) ≃ ℰ^NA(Y,π^*θ;π^*φ)` (`prop:ETCIbimero`).

The Kähler hypothesis on `Y` made in the source is not needed. Compactness of
`Y` is a consequence of the hypotheses (`compactSpace_of_isAnalyticModification`);
it enters the statements as an instance argument only because the test-curve
objects on `Y` are defined under this instance (any two instances agree).
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open AnalyticModificationLocalDiscrepancy AnalyticModificationStrongPullback

universe u

variable {n : ℕ} {X Y : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

omit [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y] in
private theorem upperSemicontinuous_comp_of_continuous {f : X → EReal}
    (hf : UpperSemicontinuous f) {g : Y → X} (hg : Continuous g) :
    UpperSemicontinuous (f ∘ g) :=
  fun y a ha => (hg.tendsto y).eventually (hf (g y) a ha)

omit [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y] in
private theorem singularityLE_comp {u v : X → EReal} (h : SingularityLE u v) (g : Y → X) :
    SingularityLE (u ∘ g) (v ∘ g) := by
  obtain ⟨C, hC⟩ := (singularityLE_iff_exists_real u v).mp h
  exact (singularityLE_iff_exists_real _ _).mpr ⟨C, fun y => hC (g y)⟩

omit [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y] in
private theorem singularityLE_of_comp {u v : X → EReal} {g : Y → X}
    (hg : Function.Surjective g) (h : SingularityLE (u ∘ g) (v ∘ g)) : SingularityLE u v := by
  obtain ⟨C, hC⟩ := (singularityLE_iff_exists_real _ _).mp h
  refine (singularityLE_iff_exists_real _ _).mpr ⟨C, fun x => ?_⟩
  obtain ⟨y, rfl⟩ := hg x
  exact hC y

private theorem upperSemicontinuous_of_isThetaPSH
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)} {w : X → EReal}
    (hw : (ofFixedModel n X).IsThetaPSH θ w) : UpperSemicontinuous w :=
  ((isThetaPSH_iff_nativeThetaPotential θ w).mp hw).1.quasiPlurisubharmonic.upperSemicontinuous

section Descent

variable {π : Y → X} (hπ : IsAnalyticModification (n := n) π)

/-- The (unique) descent of a pulled-back `θ`-PSH function, `prop:PSHpullbij`. -/
def sourceModificationDescent [CompactSpace Y]
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n X)) {w : Y → EReal}
    (hw : (ofFixedModel n Y).IsThetaPSH (θ.nativeHolomorphicPullback hπ.1) w) : X → EReal :=
  (existsUnique_nativeThetaPSH_descent hπ θ hw).exists.choose

theorem sourceModificationDescent_spec [CompactSpace Y]
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n X)) {w : Y → EReal}
    (hw : (ofFixedModel n Y).IsThetaPSH (θ.nativeHolomorphicPullback hπ.1) w) :
    (ofFixedModel n X).IsThetaPSH θ (sourceModificationDescent hπ θ hw) ∧
      sourceModificationDescent hπ θ hw ∘ π = w :=
  (existsUnique_nativeThetaPSH_descent hπ θ hw).exists.choose_spec

theorem sourceModificationDescent_apply [CompactSpace Y]
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n X)) {w : Y → EReal}
    (hw : (ofFixedModel n Y).IsThetaPSH (θ.nativeHolomorphicPullback hπ.1) w) (y : Y) :
    sourceModificationDescent hπ θ hw (π y) = w y :=
  congrFun (sourceModificationDescent_spec hπ θ hw).2 y

/-- The descent of a pull-back is the original function. -/
theorem sourceModificationDescent_comp [CompactSpace Y]
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n X)) {u : X → EReal}
    (hu : (ofFixedModel n Y).IsThetaPSH (θ.nativeHolomorphicPullback hπ.1) (u ∘ π)) :
    sourceModificationDescent hπ θ hu = u := by
  funext x
  obtain ⟨y, rfl⟩ := surjective_of_isAnalyticModification hπ x
  exact sourceModificationDescent_apply hπ θ hu y

/-- The usc-regularized supremum of an arbitrary family commutes with the
pull-back, as soon as the pulled-back regularized supremum is `π^*θ`-PSH. -/
theorem uscSup_comp_modification [CompactSpace Y]
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n X)) {ι : Type*} (u : ι → X → EReal)
    (hup : (ofFixedModel n Y).IsThetaPSH (θ.nativeHolomorphicPullback hπ.1)
      (SGPT.PSH.uscSup fun i => u i ∘ π)) :
    SGPT.PSH.uscSup (fun i => u i ∘ π) = SGPT.PSH.uscSup u ∘ π := by
  have hs := surjective_of_isAnalyticModification hπ
  apply le_antisymm
  · show uscRegularization (fun y => ⨆ i, (u i ∘ π) y) ≤ _
    apply uscRegularization_le
      (upperSemicontinuous_comp_of_continuous (upperSemicontinuous_uscRegularization _)
        hπ.1.continuous)
    intro y
    exact iSup_le fun i => (le_iSup (fun i => u i (π y)) i).trans
      (le_uscRegularization (fun x => ⨆ i, u i x) (π y))
  · obtain ⟨hw, hwe⟩ := sourceModificationDescent_spec hπ θ hup
    set w := sourceModificationDescent hπ θ hup
    have hle : SGPT.PSH.uscSup u ≤ w := by
      show uscRegularization (fun x => ⨆ i, u i x) ≤ w
      apply uscRegularization_le (upperSemicontinuous_of_isThetaPSH hw)
      intro x
      obtain ⟨y, rfl⟩ := hs x
      apply iSup_le
      intro i
      have h1 : u i (π y) ≤ SGPT.PSH.uscSup (fun i => u i ∘ π) y :=
        (le_iSup (fun i => (u i ∘ π) y) i).trans
          (le_uscRegularization (fun z => ⨆ i, (u i ∘ π) z) y)
      rw [← hwe] at h1
      exact h1
    rw [← hwe]
    intro y
    exact hle (π y)

/-- Source `prop:Penvbimero` (the ingredient used in `prop:ETCbimero`): the
ordinary envelope commutes with the pull-back along a proper bimeromorphic
morphism, for every `θ`-PSH input. -/
theorem sourceSingularityEnvelope_modification_pullback [CompactSpace X] [Nonempty X]
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n X)) {u : X → EReal}
    (hu : (ofFixedModel n X).IsThetaPSH θ u) :
    sourceSingularityEnvelope (θ.nativeHolomorphicPullback hπ.1) (u ∘ π) =
      sourceSingularityEnvelope θ u ∘ π := by
  let : CompactSpace Y := compactSpace_of_isAnalyticModification hπ
  have hs := surjective_of_isAnalyticModification hπ
  let : Nonempty Y := ⟨(hs (Classical.arbitrary X)).choose⟩
  set θY := θ.nativeHolomorphicPullback hπ.1 with hθY
  have hup : (ofFixedModel n Y).IsThetaPSH θY (u ∘ π) := hu.comp_native_analyticModification hπ
  have hEY : (ofFixedModel n Y).IsThetaPSH θY (sourceSingularityEnvelope θY (u ∘ π)) :=
    isThetaPSH_sourceSingularityEnvelope hup
  apply le_antisymm
  · show uscRegularization (fun y => ⨆ v : sourceSingularityCompetitors θY (u ∘ π), v.1 y) ≤ _
    apply uscRegularization_le (upperSemicontinuous_comp_of_continuous
      (upperSemicontinuous_sourceSingularityEnvelope θ u) hπ.1.continuous)
    intro y
    apply iSup_le
    rintro ⟨v', hv', hv'0, hv'u⟩
    obtain ⟨hv, hve⟩ := sourceModificationDescent_spec hπ θ hv'
    set v := sourceModificationDescent hπ θ hv'
    have hv0 : v ≤ 0 := by
      intro x
      obtain ⟨z, rfl⟩ := hs x
      have h := hv'0 z
      rw [← hve] at h
      exact h
    have hvu : SingularityLE v u := by
      apply singularityLE_of_comp hs
      rw [hve]
      exact hv'u
    show v' y ≤ sourceSingularityEnvelope θ u (π y)
    rw [← hve]
    exact le_sourceSingularityEnvelope hv hv0 hvu (π y)
  · obtain ⟨hw, hwe⟩ := sourceModificationDescent_spec hπ θ hEY
    set w := sourceModificationDescent hπ θ hEY
    have hle : sourceSingularityEnvelope θ u ≤ w := by
      show uscRegularization (fun x => ⨆ v : sourceSingularityCompetitors θ u, v.1 x) ≤ w
      apply uscRegularization_le (upperSemicontinuous_of_isThetaPSH hw)
      intro x
      apply iSup_le
      rintro ⟨v, hv, hv0, hvu⟩
      obtain ⟨y, rfl⟩ := hs x
      have hcomp : v ∘ π ≤ sourceSingularityEnvelope θY (u ∘ π) :=
        le_sourceSingularityEnvelope (hv.comp_native_analyticModification hπ)
          (fun z => hv0 (π z)) (singularityLE_comp hvu π)
      have h := hcomp y
      rw [← hwe] at h
      exact h
    rw [← hwe]
    intro y
    exact hle (π y)

private theorem sourcePotentialNonPluripolarMeasure_congr_fun
    [MeasurableSpace Y] [CompactSpace Y] (θ : AtlasClosedRealOneOneForm (ofFixedModel n Y))
    {u v : Y → EReal} (h : u = v) (hu : (ofFixedModel n Y).IsThetaPSH θ u)
    (hv : (ofFixedModel n Y).IsThetaPSH θ v) :
    sourcePotentialNonPluripolarMeasure θ u hu = sourcePotentialNonPluripolarMeasure θ v hv := by
  subst h
  rfl

private theorem diagonalPotentialMass_congr_form [MeasurableSpace Y] [CompactSpace Y]
    {θ₁ θ₂ : ClosedRealOneOneForm n Y} (h : θ₁ = θ₂) {u : Y → EReal}
    (h₁ : IsThetaPshPotential θ₁.val u) (h₂ : IsThetaPshPotential θ₂.val u) :
    DiagonalMass.diagonalPotentialMass θ₁ u h₁ = DiagonalMass.diagonalPotentialMass θ₂ u h₂ := by
  subst h
  rfl

/-- The total non-pluripolar mass is invariant under pull-back along a proper
bimeromorphic morphism. -/
theorem sourcePotentialNonPluripolarMeasure_univ_modification_pullback
    [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
    [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n X)) {u : X → EReal}
    (hu : (ofFixedModel n X).IsThetaPSH θ u)
    (hup : (ofFixedModel n Y).IsThetaPSH (θ.nativeHolomorphicPullback hπ.1) (u ∘ π)) :
    sourcePotentialNonPluripolarMeasure (θ.nativeHolomorphicPullback hπ.1) (u ∘ π) hup univ =
      sourcePotentialNonPluripolarMeasure θ u hu univ := by
  unfold sourcePotentialNonPluripolarMeasure
  rw [DiagonalMass.diagonalPotentialMeasure_univ, DiagonalMass.diagonalPotentialMeasure_univ]
  have h := AnalyticModificationMixedMass.diagonalPotentialMass_pullback_of_isAnalyticModification
    hπ (atlasClosedFormToNative θ) ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu)
  exact (diagonalPotentialMass_congr_form (sourceNativeAtlasForm_roundTrip _) _ _).trans h

/-- A model potential pulls back to a model potential (positive mass and
ordinary-envelope fixed point). -/
theorem SourceModelPotential.modification_pullback
    [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [Nonempty X]
    [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)} {φ : X → EReal}
    (hφ : SourceModelPotential θ φ) :
    SourceModelPotential (θ.nativeHolomorphicPullback hπ.1) (φ ∘ π) := by
  obtain ⟨hpsh, heq, hmass⟩ := hφ
  refine ⟨hpsh.comp_native_analyticModification hπ, ?_, ?_⟩
  · rw [sourceSingularityEnvelope_modification_pullback hπ θ hpsh, ← heq]
  · rw [sourcePotentialNonPluripolarMeasure_univ_modification_pullback hπ θ hpsh]
    exact hmass

/-- Source `prop:Penvbimero`, last clause: `φ` is a model potential iff `π^*φ` is. -/
theorem sourceModelPotential_modification_pullback_iff
    [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [Nonempty X]
    [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)} {φ : X → EReal}
    (hpsh : (ofFixedModel n X).IsThetaPSH θ φ) :
    SourceModelPotential (θ.nativeHolomorphicPullback hπ.1) (φ ∘ π) ↔
      SourceModelPotential θ φ := by
  refine ⟨fun h => ?_, fun h => h.modification_pullback hπ⟩
  obtain ⟨hpsh', heq, hmass⟩ := h
  refine ⟨hpsh, ?_, ?_⟩
  · rw [sourceSingularityEnvelope_modification_pullback hπ θ hpsh] at heq
    exact (surjective_of_isAnalyticModification hπ).injective_comp_right heq
  · rw [sourcePotentialNonPluripolarMeasure_univ_modification_pullback hπ θ hpsh hpsh'] at hmass
    exact hmass

end Descent

section TestCurves

variable {π : Y → X} (hπ : IsAnalyticModification (n := n) π)

/-- Equality of cutoffs and of all sub-cutoff potentials determines the
preliminary test-curve data. -/
theorem SourceTestCurvePredata.ext_of_max_potential
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n Y)} (Γ Δ : SourceTestCurvePredata θ)
    (hmax : Γ.max = Δ.max)
    (hpotential : ∀ (τ : ℝ) (hτ : τ < Γ.max) (hτ' : τ < Δ.max),
      Γ.potential ⟨τ, hτ⟩ = Δ.potential ⟨τ, hτ'⟩) : Γ = Δ := by
  rcases Γ with ⟨a, p, hp, ha, hc, hf⟩
  rcases Δ with ⟨b, q, hq, hb, hd, hg⟩
  dsimp at hmax hpotential
  subst b
  have hpq : p = q := by
    funext τ
    exact hpotential τ.1 τ.2 τ.2
  subst q
  rfl

/-- The pointwise pull-back of the preliminary data of a test curve. -/
def SourceTestCurvePredata.modificationPullback [CompactSpace X] [Nonempty X]
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)} (Γ : SourceTestCurvePredata θ) :
    SourceTestCurvePredata (θ.nativeHolomorphicPullback hπ.1) where
  max := Γ.max
  potential τ := Γ.potential τ ∘ π
  thetaPSH τ := (Γ.thetaPSH τ).comp_native_analyticModification hπ
  antitone y := Γ.antitone (π y)
  concave y := Γ.concave (π y)
  fixedPoint τ := by
    rw [sourceSingularityEnvelope_modification_pullback hπ θ (Γ.thetaPSH τ), Γ.fixedPoint τ]

theorem SourceTestCurvePredata.modificationPullback_max [CompactSpace X] [Nonempty X]
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)} (Γ : SourceTestCurvePredata θ) :
    (Γ.modificationPullback hπ).max = Γ.max := rfl

/-- The pulled-back potentials are the literal pointwise pull-backs. -/
theorem SourceTestCurvePredata.modificationPullback_potential [CompactSpace X] [Nonempty X]
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)} (Γ : SourceTestCurvePredata θ)
    (τ : Iio Γ.max) : (Γ.modificationPullback hπ).potential τ = Γ.potential τ ∘ π := rfl

/-- The value at `-∞` (the usc-regularized supremum) is the pull-back of the
original value at `-∞`. -/
theorem SourceTestCurvePredata.modificationPullback_limit [CompactSpace X] [Nonempty X]
    [CompactSpace Y]
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)} (Γ : SourceTestCurvePredata θ) :
    sourceTestCurveLimit (Γ.modificationPullback hπ) = sourceTestCurveLimit Γ ∘ π :=
  uscSup_comp_modification hπ θ Γ.potential (Γ.modificationPullback hπ).limit_thetaPSH

/-- The pointwise descent of the preliminary data of a test curve on `Y`. -/
def SourceTestCurvePredata.modificationDescent [CompactSpace X] [Nonempty X] [CompactSpace Y]
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)}
    (Γ : SourceTestCurvePredata (θ.nativeHolomorphicPullback hπ.1)) :
    SourceTestCurvePredata θ where
  max := Γ.max
  potential τ := sourceModificationDescent hπ θ (Γ.thetaPSH τ)
  thetaPSH τ := (sourceModificationDescent_spec hπ θ (Γ.thetaPSH τ)).1
  antitone x := by
    obtain ⟨y, rfl⟩ := surjective_of_isAnalyticModification hπ x
    intro a b hab
    show sourceModificationDescent hπ θ (Γ.thetaPSH b) (π y) ≤
      sourceModificationDescent hπ θ (Γ.thetaPSH a) (π y)
    rw [sourceModificationDescent_apply, sourceModificationDescent_apply]
    exact Γ.antitone y hab
  concave x := by
    obtain ⟨y, rfl⟩ := surjective_of_isAnalyticModification hπ x
    have h : sourceTestCurveNegativeTrace Γ.max
        (fun τ => sourceModificationDescent hπ θ (Γ.thetaPSH τ)) (π y) =
        sourceTestCurveNegativeTrace Γ.max Γ.potential y := by
      funext τ
      unfold sourceTestCurveNegativeTrace
      split_ifs with hτ
      · exact congrArg Neg.neg (sourceModificationDescent_apply hπ θ (Γ.thetaPSH ⟨τ, hτ⟩) y)
      · rfl
    rw [h]
    exact Γ.concave y
  fixedPoint τ := by
    funext x
    obtain ⟨y, rfl⟩ := surjective_of_isAnalyticModification hπ x
    have hspec := sourceModificationDescent_spec hπ θ (Γ.thetaPSH τ)
    have h := congrFun (sourceSingularityEnvelope_modification_pullback hπ θ hspec.1) y
    rw [hspec.2, Γ.fixedPoint τ] at h
    rw [sourceModificationDescent_apply]
    exact h.symm

theorem SourceTestCurvePredata.modificationPullback_modificationDescent
    [CompactSpace X] [Nonempty X] [CompactSpace Y]
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)}
    (Γ : SourceTestCurvePredata (θ.nativeHolomorphicPullback hπ.1)) :
    (Γ.modificationDescent hπ).modificationPullback hπ = Γ := by
  apply SourceTestCurvePredata.ext_of_max_potential
    ((Γ.modificationDescent hπ).modificationPullback hπ) Γ rfl
  intro τ hτ _
  exact (sourceModificationDescent_spec hπ θ (Γ.thetaPSH ⟨τ, hτ⟩)).2

theorem SourceTestCurvePredata.modificationDescent_modificationPullback
    [CompactSpace X] [Nonempty X] [CompactSpace Y]
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)} (Γ : SourceTestCurvePredata θ) :
    (Γ.modificationPullback hπ).modificationDescent hπ = Γ := by
  apply SourceTestCurvePredata.ext_of_max_potential
    ((Γ.modificationPullback hπ).modificationDescent hπ) Γ rfl
  intro τ hτ _
  exact sourceModificationDescent_comp hπ θ ((Γ.modificationPullback hπ).thetaPSH ⟨τ, hτ⟩)

variable [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]
  [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]

omit [BorelSpace Y] in
/-- Equality of cutoffs and of all sub-cutoff potentials determines a test curve. -/
private theorem sourceTestCurve_ext_of_predata
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n Y)} {Γ Δ : SourceTestCurve θ}
    (h : Γ.toSourceTestCurvePredata = Δ.toSourceTestCurvePredata) : Γ = Δ := by
  rcases Γ with ⟨Γ₀, hm⟩
  rcases Δ with ⟨Δ₀, hn⟩
  dsimp only at h
  subst h
  rfl

/-- Source `prop:ETCbimero`, forward map: the pointwise pull-back of a test curve
is a test curve for the pulled-back form. -/
def SourceTestCurve.modificationPullback
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)} (Γ : SourceTestCurve θ) :
    SourceTestCurve (θ.nativeHolomorphicPullback hπ.1) where
  toSourceTestCurvePredata := Γ.toSourceTestCurvePredata.modificationPullback hπ
  positiveLimitMass := by
    have hL := Γ.toSourceTestCurvePredata.modificationPullback_limit hπ
    have hLp := Γ.toSourceTestCurvePredata.limit_thetaPSH
    rw [sourcePotentialNonPluripolarMeasure_congr_fun _ hL _
        (hLp.comp_native_analyticModification hπ),
      sourcePotentialNonPluripolarMeasure_univ_modification_pullback hπ θ hLp]
    exact Γ.positiveLimitMass

/-- The inverse map: pointwise descent of a test curve on `Y`. -/
def SourceTestCurve.modificationDescent
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)}
    (Γ : SourceTestCurve (θ.nativeHolomorphicPullback hπ.1)) : SourceTestCurve θ where
  toSourceTestCurvePredata := Γ.toSourceTestCurvePredata.modificationDescent hπ
  positiveLimitMass := by
    have hL := (Γ.toSourceTestCurvePredata.modificationDescent hπ).modificationPullback_limit hπ
    rw [Γ.toSourceTestCurvePredata.modificationPullback_modificationDescent hπ] at hL
    have hLp := (Γ.toSourceTestCurvePredata.modificationDescent hπ).limit_thetaPSH
    have hmass := Γ.positiveLimitMass
    rw [sourcePotentialNonPluripolarMeasure_congr_fun _ hL _
        (hLp.comp_native_analyticModification hπ),
      sourcePotentialNonPluripolarMeasure_univ_modification_pullback hπ θ hLp] at hmass
    exact hmass

/-- Source `prop:ETCbimero` on the whole collection of test curves: the
pointwise pull-back is a bijection `TC(X,θ) ≃ TC(Y,π^*θ)` whose inverse is the
pointwise descent. -/
def sourceTestCurveModificationEquiv (θ : AtlasClosedRealOneOneForm (ofFixedModel n X)) :
    SourceTestCurve θ ≃ SourceTestCurve (θ.nativeHolomorphicPullback hπ.1) where
  toFun Γ := Γ.modificationPullback hπ
  invFun Γ := Γ.modificationDescent hπ
  left_inv Γ := sourceTestCurve_ext_of_predata
    (Γ.toSourceTestCurvePredata.modificationDescent_modificationPullback hπ)
  right_inv Γ := sourceTestCurve_ext_of_predata
    (Γ.toSourceTestCurvePredata.modificationPullback_modificationDescent hπ)

theorem sourceTestCurveModificationEquiv_apply
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n X)) (Γ : SourceTestCurve θ) :
    sourceTestCurveModificationEquiv hπ θ Γ = Γ.modificationPullback hπ := rfl

/-- Basedness is preserved and reflected: `Γ_{-∞} = φ` iff `(π^*Γ)_{-∞} = π^*φ`. -/
theorem SourceTestCurve.modificationPullback_mem_based_iff
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)} {φ : X → EReal}
    (hφ : SourceModelPotential θ φ) (Γ : SourceTestCurve θ) :
    Γ.modificationPullback hπ ∈
        SourceTestCurvesBased (θ.nativeHolomorphicPullback hπ.1) (φ ∘ π)
          (hφ.modification_pullback hπ) ↔
      Γ ∈ SourceTestCurvesBased θ φ hφ := by
  change sourceTestCurveLimit (Γ.toSourceTestCurvePredata.modificationPullback hπ) = φ ∘ π ↔
    sourceTestCurveLimit Γ.toSourceTestCurvePredata = φ
  rw [Γ.toSourceTestCurvePredata.modificationPullback_limit hπ]
  exact (surjective_of_isAnalyticModification hπ).injective_comp_right.eq_iff

/-- Source `prop:ETCbimero`: the pointwise pull-back `Γ ↦ (τ ↦ Γ_τ ∘ π)` maps
`TC(X,θ;φ)` bijectively onto `TC(Y,π^*θ;π^*φ)`. -/
theorem source_test_curve_modification_pullback_bijOn
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)} {φ : X → EReal}
    (hφ : SourceModelPotential θ φ) :
    Set.BijOn (fun Γ : SourceTestCurve θ => Γ.modificationPullback hπ)
      (SourceTestCurvesBased θ φ hφ)
      (SourceTestCurvesBased (θ.nativeHolomorphicPullback hπ.1) (φ ∘ π)
        (hφ.modification_pullback hπ)) := by
  refine ⟨fun Γ hΓ => (Γ.modificationPullback_mem_based_iff hπ hφ).mpr hΓ,
    fun Γ _ Δ _ h => (sourceTestCurveModificationEquiv hπ θ).injective h, ?_⟩
  intro Γ hΓ
  have hΔ : ((sourceTestCurveModificationEquiv hπ θ).symm Γ).modificationPullback hπ = Γ :=
    (sourceTestCurveModificationEquiv hπ θ).apply_symm_apply Γ
  refine ⟨(sourceTestCurveModificationEquiv hπ θ).symm Γ, ?_, hΔ⟩
  apply (SourceTestCurve.modificationPullback_mem_based_iff hπ hφ _).mp
  rw [hΔ]
  exact hΓ

/-- Source `prop:ETCbimero`, as an equivalence of the based collections. -/
def sourceTestCurvesBasedModificationEquiv
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n X)) {φ : X → EReal}
    (hφ : SourceModelPotential θ φ) :
    SourceTestCurvesBased θ φ hφ ≃
      SourceTestCurvesBased (θ.nativeHolomorphicPullback hπ.1) (φ ∘ π)
        (hφ.modification_pullback hπ) :=
  (sourceTestCurveModificationEquiv hπ θ).subtypeEquiv
    (fun Γ => (Γ.modificationPullback_mem_based_iff hπ hφ).symm)

theorem sourceTestCurvesBasedModificationEquiv_apply
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n X)) {φ : X → EReal}
    (hφ : SourceModelPotential θ φ) (Γ : SourceTestCurvesBased θ φ hφ) :
    (sourceTestCurvesBasedModificationEquiv hπ θ hφ Γ).1 = Γ.1.modificationPullback hπ := rfl

omit [MeasurableSpace X] [BorelSpace X] [ConnectedSpace X]
  [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] in
/-- `𝓘`-model potentials are preserved and reflected by the pull-back. -/
theorem isIModelPotential_modification_pullback_iff [Nonempty X]
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n X)) {u : X → EReal}
    (hu : (ofFixedModel n X).IsThetaPSH θ u) :
    IEnvelope.IsIModelPotential (atlasClosedFormToNative (θ.nativeHolomorphicPullback hπ.1)).val
        (u ∘ π) ↔
      IEnvelope.IsIModelPotential (atlasClosedFormToNative θ).val u := by
  have hn := (isThetaPSH_iff_nativeThetaPotential θ u).mp hu
  have hnp := (isThetaPSH_iff_nativeThetaPotential _ _).mp
    (hu.comp_native_analyticModification hπ)
  have hb : atlasClosedFormToNative (θ.nativeHolomorphicPullback hπ.1) =
      ClosedRealOneOneForm.pullback hπ.1 (atlasClosedFormToNative θ) :=
    sourceNativeAtlasForm_roundTrip _
  rw [hb] at hnp ⊢
  have hI := SGPT.Okounkov.iSingularityEnvelope_modification_pullback hπ
    (atlasClosedFormToNative θ) hn
  unfold IEnvelope.IsIModelPotential
  rw [hI]
  constructor
  · rintro ⟨-, h⟩
    exact ⟨hn, (surjective_of_isAnalyticModification hπ).injective_comp_right h⟩
  · rintro ⟨-, h⟩
    exact ⟨hnp, congrArg (· ∘ π) h⟩

/-- A test curve is `𝓘`-model iff its pull-back is. -/
theorem SourceTestCurve.modificationPullback_isIModel_iff
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)} (Γ : SourceTestCurve θ) :
    SourceTestCurveIsIModel (Γ.modificationPullback hπ) ↔ SourceTestCurveIsIModel Γ := by
  unfold SourceTestCurveIsIModel
  exact forall_congr' fun τ =>
    isIModelPotential_modification_pullback_iff hπ θ (Γ.thetaPSH τ)

/-- Source `prop:ETCIbimero`: the pointwise pull-back maps the `𝓘`-model test
curves `ℰ^NA(X,θ;φ)` bijectively onto `ℰ^NA(Y,π^*θ;π^*φ)`. -/
theorem source_i_model_test_curve_modification_pullback_bijOn
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)} {φ : X → EReal}
    (hφ : SourceModelPotential θ φ) :
    Set.BijOn (fun Γ : SourceTestCurve θ => Γ.modificationPullback hπ)
      (SourceIModelTestCurves θ φ hφ)
      (SourceIModelTestCurves (θ.nativeHolomorphicPullback hπ.1) (φ ∘ π)
        (hφ.modification_pullback hπ)) := by
  have hB := source_test_curve_modification_pullback_bijOn hπ hφ
  refine ⟨fun Γ hΓ => ⟨hB.mapsTo hΓ.1, (Γ.modificationPullback_isIModel_iff hπ).mpr hΓ.2⟩,
    fun Γ hΓ Δ hΔ h => hB.injOn hΓ.1 hΔ.1 h, ?_⟩
  intro Γ hΓ
  obtain ⟨Δ, hΔ, rfl⟩ := hB.surjOn hΓ.1
  exact ⟨Δ, ⟨hΔ, (Δ.modificationPullback_isIModel_iff hπ).mp hΓ.2⟩, rfl⟩

/-- Source `prop:ETCIbimero`, as an equivalence of the based `𝓘`-model collections. -/
def sourceIModelTestCurvesModificationEquiv
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n X)) {φ : X → EReal}
    (hφ : SourceModelPotential θ φ) :
    SourceIModelTestCurves θ φ hφ ≃
      SourceIModelTestCurves (θ.nativeHolomorphicPullback hπ.1) (φ ∘ π)
        (hφ.modification_pullback hπ) :=
  (sourceTestCurveModificationEquiv hπ θ).subtypeEquiv fun Γ =>
    and_congr (Γ.modificationPullback_mem_based_iff hπ hφ).symm
      (Γ.modificationPullback_isIModel_iff hπ).symm

end TestCurves

end SGPT.PSH.VariableComplexAtlas
