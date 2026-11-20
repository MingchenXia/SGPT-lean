import SGPT.PSH.SourceTestCurveJoinLaws
import SGPT.PSH.SourceTestCurveIncreasingSup
import SGPT.Envelopes.SourcePositiveMassCurrents
import Mathlib.Data.Finset.Lattice.Fold

/-! # The original arbitrary-family test-curve supremum

The actual nonempty finite-join net is manufactured from the proved join LUB.
The existing increasing-test-curve producer supplies every genuine field.
Bigness, positive model bounds, exact limits and original binary/increasing
consistency are proved from the original inputs, without output certificates.
-/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set Filter Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending

/-- The literal original nonempty finite subsets, ordered by inclusion. -/
abbrev SourceTestCurveFiniteIndex (I : Type*) := {s : Finset I // s.Nonempty}

/-- Nonempty original input index produces a genuine singleton finite index. -/
instance sourceTestCurveFiniteIndexNonempty {I : Type*} [Nonempty I] :
    Nonempty (SourceTestCurveFiniteIndex I) := by
  classical
  exact ⟨⟨{Classical.arbitrary I}, Finset.singleton_nonempty _⟩⟩

/-- Actual union supplies the original common upper index, without cofinality data. -/
instance sourceTestCurveFiniteIndexDirected {I : Type*} :
    IsDirectedOrder (SourceTestCurveFiniteIndex I) := by
  classical
  refine ⟨fun F G => ?_⟩
  exact ⟨⟨F.1 ∪ G.1, F.2.mono Finset.subset_union_left⟩,
    Finset.subset_union_left, Finset.subset_union_right⟩

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- The proved actual join LUB supplies every semilattice law internally. -/
@[instance_reducible]
def sourceTestCurveSemilatticeSup (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) : SemilatticeSup (SourceTestCurve θ) :=
  { sourceTestCurvePartialOrder omega θ with
    sup := SourceTestCurve.join omega
    le_sup_left := fun Γ Δ => Γ.order_join_left omega Δ
    le_sup_right := fun Γ Δ => Γ.order_join_right omega Δ
    sup_le := fun Γ Δ Ξ hΓ hΔ => Γ.join_le omega Δ Ξ hΓ hΔ }

/-- Actual finite original join, using the repository's standard nonempty finite fold. -/
def SourceTestCurve.finiteJoin {I : Type*} (omega : KahlerBackground n M)
    (Γ : I → SourceTestCurve θ) (s : Finset I) (hs : s.Nonempty) : SourceTestCurve θ := by
  let : SemilatticeSup (SourceTestCurve θ) := sourceTestCurveSemilatticeSup omega θ
  exact s.sup' hs Γ

/-- The finite fold has precisely the genuine original intrinsic LUB relation. -/
theorem SourceTestCurve.finiteJoin_le_iff {I : Type*} (omega : KahlerBackground n M)
    (Γ : I → SourceTestCurve θ) (s : Finset I) (hs : s.Nonempty) (Ξ : SourceTestCurve θ) :
    SourceTestCurvePOrder (SourceTestCurve.finiteJoin omega Γ s hs) Ξ ↔
      ∀ i ∈ s, SourceTestCurvePOrder (Γ i) Ξ := by
  let : SemilatticeSup (SourceTestCurve θ) := sourceTestCurveSemilatticeSup omega θ
  change s.sup' hs Γ ≤ Ξ ↔ ∀ i ∈ s, Γ i ≤ Ξ
  exact Finset.sup'_le_iff hs Γ

/-- Every original member genuinely lies below the actual finite join. -/
theorem SourceTestCurve.le_finiteJoin {I : Type*} (omega : KahlerBackground n M)
    (Γ : I → SourceTestCurve θ) (s : Finset I) (hs : s.Nonempty) {i : I} (hi : i ∈ s) :
    SourceTestCurvePOrder (Γ i) (SourceTestCurve.finiteJoin omega Γ s hs) := by
  let : SemilatticeSup (SourceTestCurve θ) := sourceTestCurveSemilatticeSup omega θ
  exact Finset.le_sup' Γ hi

/-- A singleton finite fold retains the entire original curve. -/
theorem SourceTestCurve.finiteJoin_singleton {I : Type*} (omega : KahlerBackground n M)
    (Γ : I → SourceTestCurve θ) (i : I) :
    SourceTestCurve.finiteJoin omega Γ {i} (Finset.singleton_nonempty i) = Γ i := by
  let : SemilatticeSup (SourceTestCurve θ) := sourceTestCurveSemilatticeSup omega θ
  exact Finset.sup'_singleton Γ

/-- The exact finite cutoff maximum is obtained by the existing supremum homomorphism. -/
theorem SourceTestCurve.finiteJoin_max {I : Type*} (omega : KahlerBackground n M)
    (Γ : I → SourceTestCurve θ) (s : Finset I) (hs : s.Nonempty) :
    (SourceTestCurve.finiteJoin omega Γ s hs).max = s.sup' hs (fun i => (Γ i).max) := by
  let : SemilatticeSup (SourceTestCurve θ) := sourceTestCurveSemilatticeSup omega θ
  exact Finset.apply_sup'_eq_sup'_comp hs (fun G : SourceTestCurve θ => G.max)
    (fun _ _ => rfl)

/-- Inclusion gives intrinsic monotonicity of the actual original finite-join family. -/
theorem SourceTestCurve.finiteJoin_mono {I : Type*} (omega : KahlerBackground n M)
    (Γ : I → SourceTestCurve θ) (F G : Finset I) (hF : F.Nonempty) (hG : G.Nonempty)
    (hFG : F ⊆ G) :
    SourceTestCurvePOrder (SourceTestCurve.finiteJoin omega Γ F hF)
      (SourceTestCurve.finiteJoin omega Γ G hG) := by
  apply (SourceTestCurve.finiteJoin_le_iff omega Γ F hF _).mpr
  intro i hi
  exact SourceTestCurve.le_finiteJoin omega Γ G hG (hFG hi)

/-- The literal original net of all nonempty finite joins. -/
def sourceTestCurveFiniteJoinFamily {I : Type*} (omega : KahlerBackground n M)
    (Γ : I → SourceTestCurve θ) (F : SourceTestCurveFiniteIndex I) : SourceTestCurve θ :=
  SourceTestCurve.finiteJoin omega Γ F.1 F.2

/-- Its actual increasingness is produced from finite inclusion. -/
theorem sourceTestCurveFiniteJoinFamily_monotone {I : Type*} (omega : KahlerBackground n M)
    (Γ : I → SourceTestCurve θ) :
    ∀ F G : SourceTestCurveFiniteIndex I, F ≤ G →
      SourceTestCurvePOrder (sourceTestCurveFiniteJoinFamily omega Γ F)
        (sourceTestCurveFiniteJoinFamily omega Γ G) := by
  intro F G hFG
  exact SourceTestCurve.finiteJoin_mono omega Γ F.1 G.1 F.2 G.2 hFG

/-- The original real cutoff bound bounds every actual finite join cutoff. -/
theorem sourceTestCurveFiniteJoinFamily_bddAbove {I : Type*} (omega : KahlerBackground n M)
    (Γ : I → SourceTestCurve θ) (hb : BddAbove (range fun i => (Γ i).max)) :
    BddAbove (range fun F => (sourceTestCurveFiniteJoinFamily omega Γ F).max) := by
  obtain ⟨C, hC⟩ := hb
  refine ⟨C, ?_⟩
  rintro _ ⟨F, rfl⟩
  change (SourceTestCurve.finiteJoin omega Γ F.1 F.2).max ≤ C
  rw [SourceTestCurve.finiteJoin_max]
  apply Finset.sup'_le
  intro i _
  exact hC (mem_range_self i)

/-- The actual original arbitrary-family supremum, with all fields internally produced. -/
def SourceTestCurve.generalSup {I : Type*} [Nonempty I] (omega : KahlerBackground n M)
    (Γ : I → SourceTestCurve θ) (hb : BddAbove (range fun i => (Γ i).max)) : SourceTestCurve θ :=
  SourceTestCurve.increasingSup omega (sourceTestCurveFiniteJoinFamily omega Γ)
    (sourceTestCurveFiniteJoinFamily_monotone omega Γ)
    (sourceTestCurveFiniteJoinFamily_bddAbove omega Γ hb)

/-- The exact original supremum of individual real cutoffs, with both genuine bounds. -/
theorem SourceTestCurve.generalSup_max {I : Type*} [Nonempty I] (omega : KahlerBackground n M)
    (Γ : I → SourceTestCurve θ) (hb : BddAbove (range fun i => (Γ i).max)) :
    (SourceTestCurve.generalSup omega Γ hb).max = sourceTestCurveSupCutoff Γ := by
  have hF := sourceTestCurveFiniteJoinFamily_bddAbove omega Γ hb
  change sourceTestCurveSupCutoff (sourceTestCurveFiniteJoinFamily omega Γ) =
    sourceTestCurveSupCutoff Γ
  unfold sourceTestCurveSupCutoff
  apply le_antisymm
  · apply csSup_le (range_nonempty _)
    rintro _ ⟨F, rfl⟩
    change (SourceTestCurve.finiteJoin omega Γ F.1 F.2).max ≤ _
    rw [SourceTestCurve.finiteJoin_max]
    apply Finset.sup'_le
    intro i _
    exact le_csSup hb (mem_range_self i)
  · apply csSup_le (range_nonempty _)
    rintro _ ⟨i, rfl⟩
    have h := sourceTestCurveSupCutoff_ge (sourceTestCurveFiniteJoinFamily omega Γ) hF
      (⟨{i}, Finset.singleton_nonempty i⟩ : SourceTestCurveFiniteIndex I)
    change (SourceTestCurve.finiteJoin omega Γ {i} (Finset.singleton_nonempty i)).max ≤ _ at h
    rwa [SourceTestCurve.finiteJoin_singleton] at h

/-- Every actual original input lies below the actual general supremum. -/
theorem SourceTestCurve.le_generalSup {I : Type*} [Nonempty I] (omega : KahlerBackground n M)
    (Γ : I → SourceTestCurve θ) (hb : BddAbove (range fun i => (Γ i).max)) (i : I) :
    SourceTestCurvePOrder (Γ i) (SourceTestCurve.generalSup omega Γ hb) := by
  have hc : (Γ i).max ≤ (SourceTestCurve.generalSup omega Γ hb).max := by
    rw [SourceTestCurve.generalSup_max]
    exact sourceTestCurveSupCutoff_ge Γ hb i
  apply (sourceTestCurvePOrder_iff omega _ _).mpr
  refine ⟨hc, fun r hr => ?_⟩
  change (Γ i).potential ⟨r, hr⟩ ≤
    sourceTestCurveSupPotential (sourceTestCurveFiniteJoinFamily omega Γ) r
  have h := sourceTestCurveSupPotential_ge (sourceTestCurveFiniteJoinFamily omega Γ)
    (⟨{i}, Finset.singleton_nonempty i⟩ : SourceTestCurveFiniteIndex I) r
  change sourceTestCurveAt
    (SourceTestCurve.finiteJoin omega Γ {i} (Finset.singleton_nonempty i)).toSourceTestCurvePredata r ≤ _ at h
  rw [SourceTestCurve.finiteJoin_singleton] at h
  rwa [sourceTestCurveAt_of_lt _ hr] at h

/-- Positive original-union membership uses the same actually produced curve and base. -/
theorem SourceTestCurve.generalSup_mem_positive {I : Type*} [Nonempty I]
    (omega : KahlerBackground n M) (Γ : I → SourceTestCurve θ)
    (hb : BddAbove (range fun i => (Γ i).max)) :
    SourceTestCurve.generalSup omega Γ hb ∈ SourceTestCurvesPositive θ :=
  (SourceTestCurve.generalSup omega Γ hb).mem_positive omega

/-- Finite I-modelness is manufactured by actual binary-join closure. -/
theorem SourceTestCurve.finiteJoin_isIModel {I : Type*} (omega : KahlerBackground n M)
    (Γ : I → SourceTestCurve θ) (s : Finset I) (hs : s.Nonempty)
    (hI : ∀ i ∈ s, SourceTestCurveIsIModel (Γ i)) :
    SourceTestCurveIsIModel (SourceTestCurve.finiteJoin omega Γ s hs) := by
  let : SemilatticeSup (SourceTestCurve θ) := sourceTestCurveSemilatticeSup omega θ
  change SourceTestCurveIsIModel (s.sup' hs Γ)
  apply Finset.sup'_induction
  · intro A hA B hB
    exact A.join_isIModel omega B hA hB
  · exact hI

/-- Actual positive input limit mass supplies bigness before the old I-model producer. -/
theorem SourceTestCurve.generalSup_isIModel {I : Type*} [Nonempty I]
    (omega : KahlerBackground n M) (Γ : I → SourceTestCurve θ)
    (hb : BddAbove (range fun i => (Γ i).max))
    (hI : ∀ i, SourceTestCurveIsIModel (Γ i)) :
    SourceTestCurveIsIModel (SourceTestCurve.generalSup omega Γ hb) := by
  classical
  have hbig := sourcePositiveMass_isBig omega (Γ (Classical.arbitrary I)).limit_thetaPSH
    (Γ (Classical.arbitrary I)).positiveLimitMass
  exact SourceTestCurve.increasingSup_isIModel omega (sourceTestCurveFiniteJoinFamily omega Γ)
    (sourceTestCurveFiniteJoinFamily_monotone omega Γ)
    (sourceTestCurveFiniteJoinFamily_bddAbove omega Γ hb) hbig
    (fun F => SourceTestCurve.finiteJoin_isIModel omega Γ F.1 F.2 (fun i _ => hI i))

/-- The original positive I-model union, on the same actually produced output. -/
theorem SourceTestCurve.generalSup_mem_iModelPositive {I : Type*} [Nonempty I]
    (omega : KahlerBackground n M) (Γ : I → SourceTestCurve θ)
    (hb : BddAbove (range fun i => (Γ i).max))
    (hI : ∀ i, Γ i ∈ SourceIModelTestCurvesPositive θ) :
    SourceTestCurve.generalSup omega Γ hb ∈ SourceIModelTestCurvesPositive θ := by
  apply (sourceIModelTestCurvesPositive_iff_slices omega _).mpr
  exact SourceTestCurve.generalSup_isIModel omega Γ hb
    (fun i => (sourceIModelTestCurvesPositive_iff_slices omega _).mp (hI i))

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- The actual original normalized slice bound survives its spatial USC supremum. -/
theorem SourceTestCurvePredata.limit_le_zero (Γ : SourceTestCurvePredata θ) :
    sourceTestCurveLimit Γ ≤ 0 := by
  apply uscRegularization_le upperSemicontinuous_const
  intro x
  exact iSup_le (fun r => Γ.le_zero r x)

/-- The actual original spatial USC supremum of the individual limit functions. -/
def sourceTestCurveGeneralLimitSup {I : Type*} (Γ : I → SourceTestCurve θ) : M → EReal :=
  uscSup (fun i => sourceTestCurveLimit (Γ i).toSourceTestCurvePredata)

omit [BorelSpace M] [ConnectedSpace M] in
/-- Every actual individual limit bound gives the genuine common finite zero bound. -/
theorem sourceTestCurveGeneralLimitSup_le_zero {I : Type*} (Γ : I → SourceTestCurve θ) :
    sourceTestCurveGeneralLimitSup Γ ≤ 0 := by
  apply uscRegularization_le upperSemicontinuous_const
  intro x
  exact iSup_le (fun i => (Γ i).toSourceTestCurvePredata.limit_le_zero x)

omit [BorelSpace M] [ConnectedSpace M] in
/-- Genuine arbitrary-family PSH uses an actual input and the manufactured bound. -/
theorem sourceTestCurveGeneralLimitSup_thetaPSH {I : Type*} [Nonempty I]
    (Γ : I → SourceTestCurve θ) :
    (ofFixedModel n M).IsThetaPSH θ (sourceTestCurveGeneralLimitSup Γ) := by
  apply (isThetaPSH_iff_nativeThetaPotential θ _).mpr
  exact SubgeodesicSupremumInterior.isThetaPshPotential_uscRegularization_iSup
    (fun i => (isThetaPSH_iff_nativeThetaPotential θ _).mp (Γ i).limit_thetaPSH)
    (C := 0) (fun i x => (Γ i).toSourceTestCurvePredata.limit_le_zero x)

omit [ConnectedSpace M] in
/-- An actual selected positive input limit transfers positive mass to the true USC supremum. -/
theorem sourceTestCurveGeneralLimitSup_mass_positive {I : Type*} [Nonempty I]
    (omega : KahlerBackground n M) (Γ : I → SourceTestCurve θ) :
    0 < sourcePotentialNonPluripolarMeasure θ (sourceTestCurveGeneralLimitSup Γ)
      (sourceTestCurveGeneralLimitSup_thetaPSH Γ) univ := by
  classical
  let i := Classical.arbitrary I
  have hle : sourceTestCurveLimit (Γ i).toSourceTestCurvePredata ≤ sourceTestCurveGeneralLimitSup Γ := by
    intro x
    exact (le_iSup (fun j => sourceTestCurveLimit (Γ j).toSourceTestCurvePredata x) i).trans
      (le_uscRegularization (fun y => ⨆ j, sourceTestCurveLimit (Γ j).toSourceTestCurvePredata y) x)
  exact (Γ i).positiveLimitMass.trans_le (sourcePotentialNonPluripolarMass_mono omega
    (Γ i).limit_thetaPSH (sourceTestCurveGeneralLimitSup_thetaPSH Γ)
    (MoreSingularOn.of_le fun x _ => hle x))

/-- Every genuine model/positive-mass field of the original target envelope is produced. -/
theorem sourceTestCurveGeneralLimitSup_envelope_model {I : Type*} [Nonempty I]
    (omega : KahlerBackground n M) (Γ : I → SourceTestCurve θ) :
    SourceModelPotential θ (sourceSingularityEnvelope θ (sourceTestCurveGeneralLimitSup Γ)) :=
  sourceOrdinaryEnvelope_model omega (sourceTestCurveGeneralLimitSup_thetaPSH Γ)
    (sourceTestCurveGeneralLimitSup_mass_positive omega Γ)

/-- Actual finite join limits are bounded by the manufactured original target model. -/
theorem SourceTestCurve.finiteJoin_limit_le_generalEnvelope {I : Type*} [Nonempty I]
    (omega : KahlerBackground n M) (Γ : I → SourceTestCurve θ)
    (F : Finset I) (hF : F.Nonempty) :
    sourceTestCurveLimit (SourceTestCurve.finiteJoin omega Γ F hF).toSourceTestCurvePredata ≤
      sourceSingularityEnvelope θ (sourceTestCurveGeneralLimitSup Γ) := by
  let H := sourceTestCurveGeneralLimitSup Γ
  let B := sourceSingularityEnvelope θ H
  have hB : SourceModelPotential θ B := sourceTestCurveGeneralLimitSup_envelope_model omega Γ
  have hHB : H ≤ B := le_sourceSingularityEnvelope
    (sourceTestCurveGeneralLimitSup_thetaPSH Γ) (sourceTestCurveGeneralLimitSup_le_zero Γ)
    (MoreSingularOn.of_le fun _ _ => le_rfl)
  have heach (i : I) : sourceTestCurveLimit (Γ i).toSourceTestCurvePredata ≤ B := by
    intro x
    exact ((le_iSup (fun j => sourceTestCurveLimit (Γ j).toSourceTestCurvePredata x) i).trans
      (le_uscRegularization (fun y => ⨆ j, sourceTestCurveLimit (Γ j).toSourceTestCurvePredata y) x)).trans
      (hHB x)
  let : SemilatticeSup (SourceTestCurve θ) := sourceTestCurveSemilatticeSup omega θ
  change sourceTestCurveLimit (F.sup' hF Γ).toSourceTestCurvePredata ≤ B
  apply Finset.sup'_induction hF Γ
    (p := fun G : SourceTestCurve θ => sourceTestCurveLimit G.toSourceTestCurvePredata ≤ B)
  · intro A hA D hD
    change sourceTestCurveLimit (A.join omega D).toSourceTestCurvePredata ≤ B
    rw [SourceTestCurve.join_limit]
    exact (sourceOrdinaryEnvelope_mono
      (MoreSingularOn.of_le fun x _ => max_le (hA x) (hD x))).trans_eq hB.choose_spec.1.symm
  · intro i _
    exact heach i

/-- The exact original arbitrary-family negative-infinity limit formula. -/
theorem SourceTestCurve.generalSup_limit {I : Type*} [Nonempty I]
    (omega : KahlerBackground n M) (Γ : I → SourceTestCurve θ)
    (hb : BddAbove (range fun i => (Γ i).max)) :
    sourceTestCurveLimit (SourceTestCurve.generalSup omega Γ hb).toSourceTestCurvePredata =
      sourceSingularityEnvelope θ (sourceTestCurveGeneralLimitSup Γ) := by
  let S := SourceTestCurve.generalSup omega Γ hb
  let V := sourceTestCurveLimit S.toSourceTestCurvePredata
  let H := sourceTestCurveGeneralLimitSup Γ
  let B := sourceSingularityEnvelope θ H
  have hB : SourceModelPotential θ B := sourceTestCurveGeneralLimitSup_envelope_model omega Γ
  have hnet : V = uscRegularization (⨆ F : SourceTestCurveFiniteIndex I,
      sourceTestCurveLimit (sourceTestCurveFiniteJoinFamily omega Γ F).toSourceTestCurvePredata) :=
    SourceTestCurve.increasingSup_limit omega (sourceTestCurveFiniteJoinFamily omega Γ)
      (sourceTestCurveFiniteJoinFamily_monotone omega Γ)
      (sourceTestCurveFiniteJoinFamily_bddAbove omega Γ hb)
  have hupper : V ≤ B := by
    rw [hnet]
    apply uscRegularization_le
      ((isThetaPSH_iff_nativeThetaPotential θ _).mp hB.thetaPSH).1.quasiPlurisubharmonic.upperSemicontinuous
    exact iSup_le (fun F => SourceTestCurve.finiteJoin_limit_le_generalEnvelope omega Γ F.1 F.2)
  have hHV : H ≤ V := by
    apply uscRegularization_le
      ((isThetaPSH_iff_nativeThetaPotential θ _).mp S.limit_thetaPSH).1.quasiPlurisubharmonic.upperSemicontinuous
    intro x
    apply iSup_le
    intro i
    exact (SourceTestCurve.le_generalSup omega Γ hb i).limit_le omega x
  exact le_antisymm hupper ((sourceOrdinaryEnvelope_mono
    (MoreSingularOn.of_le fun x _ => hHV x)).trans_eq (S.limit_model omega).choose_spec.1.symm)

/-- Literal original defining equality with the actual nonempty finite-join net. -/
theorem SourceTestCurve.generalSup_eq_increasingSup {I : Type*} [Nonempty I]
    (omega : KahlerBackground n M) (Γ : I → SourceTestCurve θ)
    (hb : BddAbove (range fun i => (Γ i).max)) :
    SourceTestCurve.generalSup omega Γ hb =
      SourceTestCurve.increasingSup omega (sourceTestCurveFiniteJoinFamily omega Γ)
        (sourceTestCurveFiniteJoinFamily_monotone omega Γ)
        (sourceTestCurveFiniteJoinFamily_bddAbove omega Γ hb) := rfl

/-- WHOLE original prop:suptcistc on the actual original positive input/output unions. -/
theorem source_test_curve_general_sup_properties_whole {I : Type*} [Nonempty I]
    (omega : KahlerBackground n M) (Γ : I → SourceTestCurve θ)
    (hb : BddAbove (range fun i => (Γ i).max)) :
    SourceTestCurve.generalSup omega Γ hb ∈ SourceTestCurvesPositive θ ∧
    ((∀ i, Γ i ∈ SourceIModelTestCurvesPositive θ) →
      SourceTestCurve.generalSup omega Γ hb ∈ SourceIModelTestCurvesPositive θ) ∧
    sourceTestCurveLimit (SourceTestCurve.generalSup omega Γ hb).toSourceTestCurvePredata =
      sourceSingularityEnvelope θ (uscSup (fun i => sourceTestCurveLimit (Γ i).toSourceTestCurvePredata)) := by
  exact ⟨SourceTestCurve.generalSup_mem_positive omega Γ hb,
    SourceTestCurve.generalSup_mem_iModelPositive omega Γ hb,
    SourceTestCurve.generalSup_limit omega Γ hb⟩

/-- The existing increasing construction genuinely dominates every original input. -/
theorem SourceTestCurve.le_increasingSup {I : Type*} [Preorder I]
    [IsDirectedOrder I] [Nonempty I] (omega : KahlerBackground n M)
    (Γ : I → SourceTestCurve θ)
    (hm : ∀ i j, i ≤ j → SourceTestCurvePOrder (Γ i) (Γ j))
    (hb : BddAbove (range fun i => (Γ i).max)) (i : I) :
    SourceTestCurvePOrder (Γ i) (SourceTestCurve.increasingSup omega Γ hm hb) := by
  have hc : (Γ i).max ≤ (SourceTestCurve.increasingSup omega Γ hm hb).max :=
    sourceTestCurveSupCutoff_ge Γ hb i
  apply (sourceTestCurvePOrder_iff omega _ _).mpr
  refine ⟨hc, fun r hr => ?_⟩
  change (Γ i).potential ⟨r, hr⟩ ≤ sourceTestCurveSupPotential Γ r
  simpa only [sourceTestCurveAt_of_lt (Γ i).toSourceTestCurvePredata hr] using
    sourceTestCurveSupPotential_ge Γ i r

/-- An actual common upper curve bounds the old increasing construction by genuine USC. -/
theorem SourceTestCurve.increasingSup_le {I : Type*} [Preorder I]
    [IsDirectedOrder I] [Nonempty I] (omega : KahlerBackground n M)
    (Γ : I → SourceTestCurve θ)
    (hm : ∀ i j, i ≤ j → SourceTestCurvePOrder (Γ i) (Γ j))
    (hb : BddAbove (range fun i => (Γ i).max)) (Ξ : SourceTestCurve θ)
    (hΞ : ∀ i, SourceTestCurvePOrder (Γ i) Ξ) :
    SourceTestCurvePOrder (SourceTestCurve.increasingSup omega Γ hm hb) Ξ := by
  have hc : sourceTestCurveSupCutoff Γ ≤ Ξ.max := by
    apply csSup_le (range_nonempty _)
    rintro _ ⟨i, rfl⟩
    exact (hΞ i).cutoff_le
  apply (sourceTestCurvePOrder_iff omega _ _).mpr
  refine ⟨hc, fun r hr => ?_⟩
  change sourceTestCurveSupPotential Γ r ≤ Ξ.potential ⟨r, hr.trans_le hc⟩
  apply uscRegularization_le
    (Ξ.native_thetaPSH ⟨r, hr.trans_le hc⟩).1.quasiPlurisubharmonic.upperSemicontinuous
  apply iSup_le
  intro i
  have h := (sourceTestCurvePOrder_iff_extension omega (Γ i) Ξ).mp (hΞ i) r
  simpa only [sourceTestCurveAt_of_lt Ξ.toSourceTestCurvePredata (hr.trans_le hc)] using h

/-- The actual arbitrary-family construction is a genuine original intrinsic LUB. -/
theorem SourceTestCurve.generalSup_le {I : Type*} [Nonempty I]
    (omega : KahlerBackground n M) (Γ : I → SourceTestCurve θ)
    (hb : BddAbove (range fun i => (Γ i).max)) (Ξ : SourceTestCurve θ)
    (hΞ : ∀ i, SourceTestCurvePOrder (Γ i) Ξ) :
    SourceTestCurvePOrder (SourceTestCurve.generalSup omega Γ hb) Ξ := by
  apply SourceTestCurve.increasingSup_le omega (sourceTestCurveFiniteJoinFamily omega Γ)
    (sourceTestCurveFiniteJoinFamily_monotone omega Γ)
    (sourceTestCurveFiniteJoinFamily_bddAbove omega Γ hb) Ξ
  intro F
  exact (SourceTestCurve.finiteJoin_le_iff omega Γ F.1 F.2 Ξ).mpr (fun i _ => hΞ i)

/-- The original arbitrary construction really extends the actual original binary join. -/
theorem SourceTestCurve.generalSup_bool (omega : KahlerBackground n M)
    (Γ : Bool → SourceTestCurve θ) (hb : BddAbove (range fun i => (Γ i).max)) :
    SourceTestCurve.generalSup omega Γ hb = (Γ false).join omega (Γ true) := by
  apply SourceTestCurvePOrder.antisymm omega
  · apply SourceTestCurve.generalSup_le omega Γ hb
    intro i
    cases i
    · exact (Γ false).order_join_left omega (Γ true)
    · exact (Γ false).order_join_right omega (Γ true)
  · exact (Γ false).join_le omega (Γ true) _
      (SourceTestCurve.le_generalSup omega Γ hb false)
      (SourceTestCurve.le_generalSup omega Γ hb true)

/-- The original arbitrary construction also extends the actual original increasing one. -/
theorem SourceTestCurve.generalSup_eq_increasing_of_monotone {I : Type*} [Preorder I]
    [IsDirectedOrder I] [Nonempty I] (omega : KahlerBackground n M)
    (Γ : I → SourceTestCurve θ)
    (hm : ∀ i j, i ≤ j → SourceTestCurvePOrder (Γ i) (Γ j))
    (hb : BddAbove (range fun i => (Γ i).max)) :
    SourceTestCurve.generalSup omega Γ hb = SourceTestCurve.increasingSup omega Γ hm hb := by
  apply SourceTestCurvePOrder.antisymm omega
  · exact SourceTestCurve.generalSup_le omega Γ hb _
      (fun i => SourceTestCurve.le_increasingSup omega Γ hm hb i)
  · exact SourceTestCurve.increasingSup_le omega Γ hm hb _
      (fun i => SourceTestCurve.le_generalSup omega Γ hb i)

end SGPT.PSH.VariableComplexAtlas
