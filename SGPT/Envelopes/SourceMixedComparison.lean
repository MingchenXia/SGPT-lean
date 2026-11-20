import SGPT.Envelopes.SourceMixedEnergyIntegrability
import SGPT.Foundations.Analysis.Pending.SingularGlobalPMixedMassEquality

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending DiagonalMass GlobalNonPluripolar GlobalDiagonalScaling
open RelativePreceqClasses SingularGlobalPOrder

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- Exactly n-j unchanged primary forms followed by every original auxiliary form. -/
def sourceComparisonFormTuple (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (j : Fin (n + 1)) (η : Fin j.val → AtlasClosedRealOneOneForm (ofFixedModel n M))
    (i : Fin n) : AtlasClosedRealOneOneForm (ofFixedModel n M) :=
  if hi : i.val < n - j.val then θ else η ⟨i.val - (n - j.val), by omega⟩

/-- Exactly n-j copies of the entire primary function and every unchanged auxiliary function. -/
def sourceComparisonPotentialTuple (j : Fin (n + 1)) (q : Fin j.val → M → EReal)
    (u : M → EReal) (i : Fin n) : M → EReal :=
  if hi : i.val < n - j.val then u else q ⟨i.val - (n - j.val), by omega⟩

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- The actual ordered original tuple has genuine theta tests in every unchanged background. -/
theorem sourceComparisonTuple_thetaPSH
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {j : Fin (n + 1)}
    {η : Fin j.val → AtlasClosedRealOneOneForm (ofFixedModel n M)}
    {q : Fin j.val → M → EReal} (hq : ∀ a, (ofFixedModel n M).IsThetaPSH (η a) (q a))
    {u : M → EReal} (hu : (ofFixedModel n M).IsThetaPSH θ u) :
    ∀ i, (ofFixedModel n M).IsThetaPSH (sourceComparisonFormTuple θ j η i)
      (sourceComparisonPotentialTuple j q u i) := by
  intro i
  unfold sourceComparisonFormTuple sourceComparisonPotentialTuple
  split_ifs with hi
  · exact hu
  · exact hq _

/-- The literal whole original product with all j arbitrary auxiliary currents. -/
def sourceMixedComparisonMeasure
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (j : Fin (n + 1))
    (η : Fin j.val → AtlasClosedRealOneOneForm (ofFixedModel n M))
    (q : Fin j.val → M → EReal) (hq : ∀ a, (ofFixedModel n M).IsThetaPSH (η a) (q a))
    (u : M → EReal) (hu : (ofFixedModel n M).IsThetaPSH θ u) : Measure M :=
  sourceMixedNonPluripolarMeasure (sourceComparisonFormTuple θ j η)
    (sourceComparisonPotentialTuple j q u) (sourceComparisonTuple_thetaPSH hq hu)

omit [BorelSpace M] in
/-- With no primary slot, the entire original measure is independent of the primary function. -/
theorem sourceMixedComparisonMeasure_no_primary
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {j : Fin (n + 1)}
    {η : Fin j.val → AtlasClosedRealOneOneForm (ofFixedModel n M)}
    {q : Fin j.val → M → EReal} (hq : ∀ a, (ofFixedModel n M).IsThetaPSH (η a) (q a))
    {u v : M → EReal} (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hv : (ofFixedModel n M).IsThetaPSH θ v) (hj : n - j.val = 0) :
    sourceMixedComparisonMeasure θ j η q hq u hu =
      sourceMixedComparisonMeasure θ j η q hq v hv := by
  exact globalMixedMeasure_congr rfl (by
    funext i
    simp [sourceComparisonPotentialTuple, hj])
    (fun i => ((isThetaPSH_iff_nativeThetaPotential (sourceComparisonFormTuple θ j η i) _).mp
      (sourceComparisonTuple_thetaPSH hq hu i)).1)
    (fun i => ((isThetaPSH_iff_nativeThetaPotential (sourceComparisonFormTuple θ j η i) _).mp
      (sourceComparisonTuple_thetaPSH hq hv i)).1)

/-- Actual per-slot finite translation preserves the whole original mixed measure. -/
theorem sourceMixedComparisonMeasure_add_const
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {j : Fin (n + 1)}
    {η : Fin j.val → AtlasClosedRealOneOneForm (ofFixedModel n M)}
    {q : Fin j.val → M → EReal} (hq : ∀ a, (ofFixedModel n M).IsThetaPSH (η a) (q a))
    {u : M → EReal} (hu : (ofFixedModel n M).IsThetaPSH θ u) (c : ℝ)
    (huc : (ofFixedModel n M).IsThetaPSH θ (fun x => u x + (c : EReal))) :
    sourceMixedComparisonMeasure θ j η q hq (fun x => u x + (c : EReal)) huc =
      sourceMixedComparisonMeasure θ j η q hq u hu := by
  have hraw (i : Fin n) := ((isThetaPSH_iff_nativeThetaPotential
    (sourceComparisonFormTuple θ j η i) _).mp (sourceComparisonTuple_thetaPSH hq hu i)).1
  have ht := GlobalMeasureInvariance.globalMixedMeasure_sub_const hraw
    (fun i => if i.val < n - j.val then -c else 0)
  have heq : (fun i x => sourceComparisonPotentialTuple j q u i x -
      ((if i.val < n - j.val then -c else 0 : ℝ) : EReal)) =
      sourceComparisonPotentialTuple j q (fun x => u x + (c : EReal)) := by
    funext i x
    unfold sourceComparisonPotentialTuple
    split_ifs <;> simp [EReal.coe_neg, sub_eq_add_neg]
  have hshift (i : Fin n) := ((isThetaPSH_iff_nativeThetaPotential
    (sourceComparisonFormTuple θ j η i) _).mp (sourceComparisonTuple_thetaPSH hq huc i)).1
  erw [globalMixedMeasure_congr rfl heq _ hshift] at ht
  exact ht

/-- Every genuine original potential has a null pole set for the whole auxiliary-current product. -/
theorem sourceMixedComparisonMeasure_pole_null
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {j : Fin (n + 1)}
    {η : Fin j.val → AtlasClosedRealOneOneForm (ofFixedModel n M)}
    {q : Fin j.val → M → EReal} (hq : ∀ a, (ofFixedModel n M).IsThetaPSH (η a) (q a))
    {u : M → EReal} (hu : (ofFixedModel n M).IsThetaPSH θ u)
    {σ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {v : M → EReal}
    (hv : (ofFixedModel n M).IsThetaPSH σ v) :
    sourceMixedComparisonMeasure θ j η q hq u hu {x | v x = ⊥} = 0 :=
  sourceMixedNonPluripolarMeasure_pole_null (sourceComparisonTuple_thetaPSH hq hu) hv

/-- Actual compact Kähler finiteness for every original auxiliary-current mixed domain. -/
theorem sourceMixedComparisonMeasure_apply_lt_top
    (ω : KahlerBackground n M) {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    {j : Fin (n + 1)} {η : Fin j.val → AtlasClosedRealOneOneForm (ofFixedModel n M)}
    {q : Fin j.val → M → EReal} (hq : ∀ a, (ofFixedModel n M).IsThetaPSH (η a) (q a))
    {u : M → EReal} (hu : (ofFixedModel n M).IsThetaPSH θ u) (S : Set M) :
    sourceMixedComparisonMeasure θ j η q hq u hu S < ⊤ :=
  globalMixedMeasure_apply_lt_top ω (fun i => ((isThetaPSH_iff_nativeThetaPotential
    (sourceComparisonFormTuple θ j η i) _).mp (sourceComparisonTuple_thetaPSH hq hu i)).1) S

/-- Actual simultaneous maximum locality retains every arbitrary auxiliary current. -/
theorem sourceMixedComparisonMeasure_max_restrict
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {j : Fin (n + 1)}
    {η : Fin j.val → AtlasClosedRealOneOneForm (ofFixedModel n M)}
    {q : Fin j.val → M → EReal} (hq : ∀ a, (ofFixedModel n M).IsThetaPSH (η a) (q a))
    {u v : M → EReal} (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hv : (ofFixedModel n M).IsThetaPSH θ v) :
    (sourceMixedComparisonMeasure θ j η q hq (fun x => max (u x) (v x)) (hu.max hv)).restrict
        {x | v x < u x} =
      (sourceMixedComparisonMeasure θ j η q hq u hu).restrict {x | v x < u x} := by
  classical
  by_cases hj : n - j.val = 0
  · rw [sourceMixedComparisonMeasure_no_primary hq (hu.max hv) hu hj]
  let a := sourceComparisonPotentialTuple j q u
  let b := sourceComparisonPotentialTuple j (fun _ _ => ⊥) v
  have ha (i : Fin n) := ((isThetaPSH_iff_nativeThetaPotential
    (sourceComparisonFormTuple θ j η i) _).mp (sourceComparisonTuple_thetaPSH hq hu i)).1
  have hb (i : Fin n) : ThetaPlurisubharmonic
      (atlasClosedFormToNative (sourceComparisonFormTuple θ j η i)).val (b i) := by
    by_cases hi : i.val < n - j.val
    · simpa only [b, sourceComparisonPotentialTuple, sourceComparisonFormTuple, dif_pos hi] using
        ((isThetaPSH_iff_nativeThetaPotential θ v).mp hv).1
    · simpa only [b, sourceComparisonPotentialTuple, dif_neg hi] using
        GlobalSlotComparison.thetaPlurisubharmonic_bot _ (ha i).hasSmoothLocalPotentials
  have hm (i : Fin n) := ((isThetaPSH_iff_nativeThetaPotential
    (sourceComparisonFormTuple θ j η i) _).mp (sourceComparisonTuple_thetaPSH hq (hu.max hv) i)).1
  have ep : (fun i x => max (a i x) (b i x)) =
      sourceComparisonPotentialTuple j q (fun x => max (u x) (v x)) := by
    funext i x
    simp only [a, b, sourceComparisonPotentialTuple]
    split_ifs <;> simp
  have hl := GlobalMaxLocality.globalMixedMeasure_restrict_max_eq ha hb
    (fun i => BoundedGlobalProduct.ThetaPlurisubharmonic.max (ha i) (hb i))
  erw [globalMixedMeasure_congr rfl ep _ hm] at hl
  let S : Set M := {x | v x < u x}
  let T : Set M := {x | ∀ i, b i x < a i x}
  change (sourceMixedComparisonMeasure θ j η q hq (fun x => max (u x) (v x)) (hu.max hv)).restrict T =
    (sourceMixedComparisonMeasure θ j η q hq u hu).restrict T at hl
  have hTS : T ⊆ S := by
    intro x hx
    have hn : 0 < n - j.val := Nat.pos_of_ne_zero hj
    have hi : (0 : ℕ) < n := by omega
    have h := hx ⟨0, hi⟩
    simpa [S, a, b, sourceComparisonPotentialTuple, hn] using h
  have hdiff : S \ T ⊆ ⋃ i, {x | a i x = ⊥} := by
    rintro x ⟨hx, hxt⟩
    change ¬ ∀ i, b i x < a i x at hxt
    obtain ⟨i, hi⟩ := not_forall.mp hxt
    by_cases hip : i.val < n - j.val
    · exact (hi (by simpa only [S, mem_ofPred_eq, a, b,
        sourceComparisonPotentialTuple, dif_pos hip] using hx)).elim
    · refine mem_iUnion.mpr ⟨i, ?_⟩
      have hnlt : ¬ (⊥ : EReal) < a i x := by
        simpa only [b, sourceComparisonPotentialTuple, dif_neg hip] using hi
      exact le_antisymm (not_lt.mp hnlt) bot_le
  have hae (w : M → EReal) (hw : (ofFixedModel n M).IsThetaPSH θ w) :
      S =ᵐ[sourceMixedComparisonMeasure θ j η q hq w hw] T := by
    apply ae_eq_set.mpr
    refine ⟨measure_mono_null hdiff (measure_iUnion_null fun i => ?_), ?_⟩
    · exact sourceMixedComparisonMeasure_pole_null hq hw (sourceComparisonTuple_thetaPSH hq hu i)
    · rw [sdiff_eq_empty.mpr hTS, measure_empty]
  rw [Measure.restrict_congr_set (hae _ (hu.max hv)), Measure.restrict_congr_set (hae _ hu)]
  exact hl

variable [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ u v : M → EReal}
  {hφ : SourceModelPotential θ φ}

omit [ConnectedSpace M] in
/-- Actual finite translation preserves the full original preceq full-mass class. -/
theorem sourceRelativeFullMass_add_const (hu : SourceRelativeFullMass θ φ u hφ) (c : ℝ) :
    SourceRelativeFullMass θ φ (fun x => u x + (c : EReal)) hφ := by
  apply (sourceRelativeFullMass_iff_native θ φ _ hφ).mpr
  exact ((sourceRelativeFullMass_iff_native θ φ u hφ).mp hu).add_const c

omit [ConnectedSpace M] in
/-- Full mass of the genuine actual maximum is produced in the unchanged source class. -/
theorem sourceRelativeFullMass_max (ω : KahlerBackground n M)
    (hu : SourceRelativeFullMass θ φ u hφ) (hv : SourceRelativeFullMass θ φ v hφ) :
    SourceRelativeFullMass θ φ (fun x => max (u x) (v x)) hφ := by
  exact sourceRelativeFullMass_upward ω hu
    ⟨hu.choose.max hv.choose,
      DominationPrincipleReduction.moreSingularOn_max hu.choose_spec.1 hv.choose_spec.1⟩
    (MoreSingularOn.of_le fun _ _ => le_max_left _ _)

/-- Original full-mass endpoints produce the genuine background-independent source P-equivalence. -/
theorem sourceRelativeFullMass_sourcePEquivalent (ω : KahlerBackground n M)
    (hu : SourceRelativeFullMass θ φ u hφ) (hv : SourceRelativeFullMass θ φ v hφ) :
    SourcePEquivalent (n := n) u v := by
  have hnu := (sourceRelativeFullMass_iff_native θ φ u hφ).mp hu
  have hnv := (sourceRelativeFullMass_iff_native θ φ v hφ).mp hv
  have hup : HasPositivePotentialMass (atlasClosedFormToNative θ) u hnu.plurisubharmonic := by
    unfold HasPositivePotentialMass
    rw [hnu.mass_eq hnu.plurisubharmonic]
    exact hφ.toNative.positive_mass
  have hvp : HasPositivePotentialMass (atlasClosedFormToNative θ) v hnv.plurisubharmonic := by
    unfold HasPositivePotentialMass
    rw [hnv.mass_eq hnv.plurisubharmonic]
    exact hφ.toNative.positive_mass
  apply (sourcePEquivalent_iff_pEquivalentWith ω _ hnu.plurisubharmonic
    hnv.plurisubharmonic hup hvp).mpr
  apply POrder.pEquivalentWith_iff_envelope_eq.mpr
  have heu := (sourceRelativeFullMass_iff_envelope_eq ω hu.choose).mp hu
  have hev := (sourceRelativeFullMass_iff_envelope_eq ω hv.choose).mp hv
  rw [sourceSingularityEnvelope_eq_native] at heu hev
  exact heu.trans hev.symm

/-- The full original auxiliary mixed masses agree, with no mass identity or auxiliary positivity input. -/
theorem sourceMixedComparisonMeasure_total_mass (ω : KahlerBackground n M)
    {j : Fin (n + 1)} {η : Fin j.val → AtlasClosedRealOneOneForm (ofFixedModel n M)}
    {q : Fin j.val → M → EReal} (hq : ∀ a, (ofFixedModel n M).IsThetaPSH (η a) (q a))
    (hu : SourceRelativeFullMass θ φ u hφ) (hv : SourceRelativeFullMass θ φ v hφ) :
    sourceMixedComparisonMeasure θ j η q hq u hu.choose univ =
      sourceMixedComparisonMeasure θ j η q hq v hv.choose univ := by
  have hstrong (a : M → EReal) (ha : (ofFixedModel n M).IsThetaPSH θ a) (i : Fin n) :=
    (isThetaPSH_iff_nativeThetaPotential (sourceComparisonFormTuple θ j η i) _).mp
      (sourceComparisonTuple_thetaPSH hq ha i)
  have hpeq (i : Fin n) : SourcePEquivalent (n := n)
      (sourceComparisonPotentialTuple j q u i) (sourceComparisonPotentialTuple j q v i) := by
    unfold sourceComparisonPotentialTuple
    split_ifs with hi
    · exact sourceRelativeFullMass_sourcePEquivalent ω hu hv
    · let a : Fin j.val := ⟨i.val - (n - j.val), by omega⟩
      have hr := sourcePOrder_refl_of_isThetaPshPotential ω
        ((isThetaPSH_iff_nativeThetaPotential (η a) (q a)).mp (hq a))
      exact ⟨hr, hr⟩
  exact SingularGlobalPMixedMassEquality.globalMixedMass_eq_of_sourcePEquivalent ω
    (hstrong u hu.choose) (hstrong v hv.choose) hpeq

/-- Genuine mixed maximum locality and produced total mass give the whole coarse comparison. -/
theorem sourceMixedComparisonMeasure_coarse (ω : KahlerBackground n M)
    {j : Fin (n + 1)} {η : Fin j.val → AtlasClosedRealOneOneForm (ofFixedModel n M)}
    {q : Fin j.val → M → EReal} (hq : ∀ a, (ofFixedModel n M).IsThetaPSH (η a) (q a))
    (hu : SourceRelativeFullMass θ φ u hφ) (hv : SourceRelativeFullMass θ φ v hφ) :
    sourceMixedComparisonMeasure θ j η q hq v hv.choose {x | u x < v x} ≤
      sourceMixedComparisonMeasure θ j η q hq u hu.choose {x | u x ≤ v x} := by
  let μu := sourceMixedComparisonMeasure θ j η q hq u hu.choose
  let μv := sourceMixedComparisonMeasure θ j η q hq v hv.choose
  let μm := sourceMixedComparisonMeasure θ j η q hq (fun x => max (u x) (v x))
    (hu.choose.max hv.choose)
  let S : Set M := {x | u x < v x}
  let T : Set M := {x | v x < u x}
  let R : Set M := {x | u x ≤ v x}
  have hum : Measurable u := ((isThetaPSH_iff_nativeThetaPotential θ u).mp
    hu.choose).1.quasiPlurisubharmonic.upperSemicontinuous.measurable
  have hvm : Measurable v := ((isThetaPSH_iff_nativeThetaPotential θ v).mp
    hv.choose).1.quasiPlurisubharmonic.upperSemicontinuous.measurable
  have hTm : MeasurableSet T := measurableSet_lt hvm hum
  have e1 : μm S = μv S := by
    have h := congrArg (fun ν : Measure M => ν univ)
      (sourceMixedComparisonMeasure_max_restrict hq hv.choose hu.choose)
    simpa only [μm, μv, S, max_comm, Measure.restrict_apply MeasurableSet.univ,
      univ_inter] using h
  have e2 : μm T = μu T := by
    have h := congrArg (fun ν : Measure M => ν univ)
      (sourceMixedComparisonMeasure_max_restrict hq hu.choose hv.choose)
    simpa only [μm, μu, T, Measure.restrict_apply MeasurableSet.univ, univ_inter] using h
  have hmass : μm univ = μu univ :=
    sourceMixedComparisonMeasure_total_mass ω hq (sourceRelativeFullMass_max ω hu hv) hu
  have hdisj : Disjoint S T :=
    disjoint_left.mpr fun x (h1 : u x < v x) (h2 : v x < u x) => lt_asymm h1 h2
  have hR : R = Tᶜ := by ext x; simp [R, T, not_lt]
  have hle : μv S + μu T ≤ μu R + μu T := by
    calc μv S + μu T = μm (S ∪ T) := by rw [measure_union hdisj hTm, e1, e2]
      _ ≤ μm univ := measure_mono (subset_univ _)
      _ = μu univ := hmass
      _ = μu R + μu T := by rw [hR, add_comm, measure_add_measure_compl hTm]
  exact (ENNReal.add_le_add_iff_right
    (sourceMixedComparisonMeasure_apply_lt_top ω hq hu.choose T).ne).mp hle

/-- Whole strict mixed comparison on the actual original integration domain. -/
theorem sourceMixedComparisonMeasure_strict (ω : KahlerBackground n M)
    {j : Fin (n + 1)} {η : Fin j.val → AtlasClosedRealOneOneForm (ofFixedModel n M)}
    {q : Fin j.val → M → EReal} (hq : ∀ a, (ofFixedModel n M).IsThetaPSH (η a) (q a))
    (hu : SourceRelativeFullMass θ φ u hφ) (hv : SourceRelativeFullMass θ φ v hφ) :
    sourceMixedComparisonMeasure θ j η q hq v hv.choose {x | u x < v x} ≤
      sourceMixedComparisonMeasure θ j η q hq u hu.choose {x | u x < v x} := by
  let μu := sourceMixedComparisonMeasure θ j η q hq u hu.choose
  let μv := sourceMixedComparisonMeasure θ j η q hq v hv.choose
  let S : Set M := {x | u x < v x}
  let A : ℕ → Set M := fun l => {x | u x < MaxMassDecomposition.shiftPot v l x}
  have hmono : Monotone A := by
    intro l m hlm x hx
    exact lt_of_lt_of_le hx (MaxMassDecomposition.shiftPot_mono v hlm x)
  have hvt : ∀ x, v x ≠ ⊤ := ((isThetaPSH_iff_nativeThetaPotential θ v).mp
    hv.choose).1.quasiPlurisubharmonic.ne_top
  have hsup (x : M) : (⨆ l, MaxMassDecomposition.shiftPot v l x) = v x := by
    simpa only [MaxMassDecomposition.shifted, max_eq_left bot_le] using
      MaxMassDecomposition.iSup_shifted v (fun _ => ⊥) hvt x
  have hunion : (⋃ l, A l) = S := by
    ext x
    simp only [mem_iUnion, A, mem_ofPred_eq, S]
    constructor
    · rintro ⟨l, hl⟩
      exact lt_of_lt_of_le hl (MaxMassDecomposition.shiftPot_le v l x)
    · intro hx
      rw [← hsup x, lt_iSup_iff] at hx
      exact hx
  have hbound (l : ℕ) : μv (A l) ≤ μu S := by
    have hvl := sourceRelativeFullMass_add_const hv (-MaxMassDecomposition.shift l)
    have hc := sourceMixedComparisonMeasure_coarse ω hq hu hvl
    rw [sourceMixedComparisonMeasure_add_const hq hv.choose _ hvl.choose] at hc
    have hsub : {x | u x ≤ MaxMassDecomposition.shiftPot v l x} ⊆
        S ∪ {x | v x = ⊥} := by
      intro x hx
      by_cases hvb : v x = ⊥
      · exact Or.inr hvb
      · apply Or.inl
        have hshift : MaxMassDecomposition.shiftPot v l x < v x := by
          unfold MaxMassDecomposition.shiftPot
          rw [← EReal.coe_toReal (hvt x) hvb, ← EReal.coe_add]
          apply EReal.coe_lt_coe_iff.mpr
          linarith [MaxMassDecomposition.shift_pos l]
        exact lt_of_le_of_lt hx hshift
    calc μv (A l) ≤ μu {x | u x ≤ MaxMassDecomposition.shiftPot v l x} := hc
      _ ≤ μu (S ∪ {x | v x = ⊥}) := measure_mono hsub
      _ ≤ μu S + μu {x | v x = ⊥} := measure_union_le _ _
      _ = μu S := by rw [sourceMixedComparisonMeasure_pole_null hq hu.choose hv.choose, add_zero]
  change μv S ≤ μu S
  calc μv S = μv (⋃ l, A l) := congrArg μv hunion.symm
    _ = ⨆ l, μv (A l) := hmono.measure_iUnion
    _ ≤ μu S := iSup_le hbound

/-- Whole nonstrict mixed comparison follows from actual equal finite mass and reverse strict comparison. -/
theorem sourceMixedComparisonMeasure_nonstrict (ω : KahlerBackground n M)
    {j : Fin (n + 1)} {η : Fin j.val → AtlasClosedRealOneOneForm (ofFixedModel n M)}
    {q : Fin j.val → M → EReal} (hq : ∀ a, (ofFixedModel n M).IsThetaPSH (η a) (q a))
    (hu : SourceRelativeFullMass θ φ u hφ) (hv : SourceRelativeFullMass θ φ v hφ) :
    sourceMixedComparisonMeasure θ j η q hq v hv.choose {x | u x ≤ v x} ≤
      sourceMixedComparisonMeasure θ j η q hq u hu.choose {x | u x ≤ v x} := by
  let μu := sourceMixedComparisonMeasure θ j η q hq u hu.choose
  let μv := sourceMixedComparisonMeasure θ j η q hq v hv.choose
  let T : Set M := {x | v x < u x}
  have hTm : MeasurableSet T := measurableSet_lt
    (((isThetaPSH_iff_nativeThetaPotential θ v).mp
      hv.choose).1.quasiPlurisubharmonic.upperSemicontinuous.measurable)
    (((isThetaPSH_iff_nativeThetaPotential θ u).mp
      hu.choose).1.quasiPlurisubharmonic.upperSemicontinuous.measurable)
  have hcompl : {x | u x ≤ v x} = Tᶜ := by ext x; simp [T, not_lt]
  rw [hcompl, measure_compl hTm (sourceMixedComparisonMeasure_apply_lt_top ω hq hv.choose T).ne,
    measure_compl hTm (sourceMixedComparisonMeasure_apply_lt_top ω hq hu.choose T).ne,
    sourceMixedComparisonMeasure_total_mass ω hq hv hu]
  exact tsub_le_tsub_left (sourceMixedComparisonMeasure_strict ω hq hv hu) _

/-- The complete original comparison principle, with every auxiliary current and both integration sets. -/
theorem sourceMixedComparisonPrinciple (ω : KahlerBackground n M)
    {j : Fin (n + 1)} {η : Fin j.val → AtlasClosedRealOneOneForm (ofFixedModel n M)}
    {q : Fin j.val → M → EReal} (hq : ∀ a, (ofFixedModel n M).IsThetaPSH (η a) (q a))
    (hu : SourceRelativeFullMass θ φ u hφ) (hv : SourceRelativeFullMass θ φ v hφ) :
    (sourceMixedComparisonMeasure θ j η q hq v hv.choose {x | u x < v x} ≤
      sourceMixedComparisonMeasure θ j η q hq u hu.choose {x | u x < v x}) ∧
    (sourceMixedComparisonMeasure θ j η q hq v hv.choose {x | u x ≤ v x} ≤
      sourceMixedComparisonMeasure θ j η q hq u hu.choose {x | u x ≤ v x}) :=
  ⟨sourceMixedComparisonMeasure_strict ω hq hu hv,
    sourceMixedComparisonMeasure_nonstrict ω hq hu hv⟩

end SGPT.PSH.VariableComplexAtlas
