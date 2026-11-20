import SGPT.BDivisor.BD7NumericalTransitions
import SGPT.BDivisor.BD3SnapperNef
import SGPT.Foundations.Schemes.NativeFanoAlgebraicFiniteness
import SGPT.Foundations.Analysis.Pending.AnalyticModificationMixedMass

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.BDivisor.BD7

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes MeasureTheory Set
open SGPT.Okounkov SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open GlobalNonPluripolar ModificationMassInvariance DominationIntersectionNumbers NefMixedMass
open AnalyticModificationLocalDiscrepancy
open SGPT.Hodge.BDivChain.SourceMixedOrderDraft
open scoped Manifold ContDiff ENNReal

section ModificationIntegral

variable {n : ℕ} {X Y : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]

/-- Signed mixed top-form integrals are preserved under an actual proper
analytic modification. Expand in semipositive slots and apply total mixed-mass
change of variables to every term. -/
theorem slotIntegral_pullback_actualModification_bd7 {g : Y → X}
    (hg : IsAnalyticModification (n := n) g)
    (w : KahlerBackground n X) (w' : KahlerBackground n Y)
    (theta : Fin n → ClosedRealOneOneForm n X) :
    slotIntegral w' (fun i => ClosedRealOneOneForm.pullback hg.1 (theta i)) =
      slotIntegral w theta := by
  classical
  obtain ⟨A, _, hsemi⟩ := KahlerDomination.exists_pos_forall_isSemipositive_add_smul w theta
  set P : Fin n → ClosedRealOneOneForm n X := fun i => theta i + A • w.form with hP
  have hthetaP : theta = fun i => P i + (-A) • w.form := by
    funext i
    simp only [hP, add_assoc, ← add_smul, add_neg_cancel, zero_smul, add_zero]
  have hthetaP' : (fun i => ClosedRealOneOneForm.pullback hg.1 (theta i)) = fun i =>
      ClosedRealOneOneForm.pullback hg.1 (P i) +
        (-A) • ClosedRealOneOneForm.pullback hg.1 w.form := by
    funext i
    rw [← pullback_add_smul, hP]
    congr 1
    simp only [add_assoc, ← add_smul, add_neg_cancel, zero_smul, add_zero]
  have hpiece : ∀ s : Finset (Fin n),
      slotIntegral w' (s.piecewise (fun i => ClosedRealOneOneForm.pullback hg.1 (P i))
        fun _ => ClosedRealOneOneForm.pullback hg.1 w.form) =
      slotIntegral w (s.piecewise P fun _ => w.form) := by
    intro s
    have hsX : ∀ i, ((s.piecewise P fun _ => w.form) i).val.IsSemipositive := by
      intro i
      by_cases hi : i ∈ s
      · rw [Finset.piecewise_eq_of_mem _ _ _ hi]; exact hsemi i
      · rw [Finset.piecewise_eq_of_notMem _ _ _ hi]; exact w.isSemipositive
    have h0X : ∀ i, ThetaPlurisubharmonic ((s.piecewise P fun _ => w.form) i).val
        (fun _ => (0 : EReal)) := fun i =>
      ((LocalPotentials.isThetaPshPotential_zero_iff _).mpr (hsX i)).1
    have hpb : (s.piecewise (fun i => ClosedRealOneOneForm.pullback hg.1 (P i))
        fun _ => ClosedRealOneOneForm.pullback hg.1 w.form) =
        pullbackTuple hg.1 (s.piecewise P fun _ => w.form) := by
      funext i
      by_cases hi : i ∈ s
      · simp only [pullbackTuple, Finset.piecewise_eq_of_mem _ _ _ hi]
      · simp only [pullbackTuple, Finset.piecewise_eq_of_notMem _ _ _ hi]
    have h0Y : ∀ i, ThetaPlurisubharmonic (pullbackTuple hg.1
        (s.piecewise P fun _ => w.form) i).val (fun y => (fun _ => (0 : EReal)) (g y)) :=
      fun i => GlobalPotentialPullback.thetaPlurisubharmonic_comp hg.1 (h0X i)
    rw [hpb, slotIntegral, slotIntegral,
      ← MixedMassClassInvariance.globalMixedMeasure_real_univ_eq_integral w' _ h0Y,
      ← MixedMassClassInvariance.globalMixedMeasure_real_univ_eq_integral w _ h0X,
      measureReal_def, measureReal_def,
      AnalyticModificationMixedMass.globalMixedMeasure_univ_pullback_of_isAnalyticModification hg h0X]
  rw [hthetaP', hthetaP, slotIntegral_add_smul_eq_sum, slotIntegral_add_smul_eq_sum]
  exact Finset.sum_congr rfl fun s _ => by rw [hpiece]


end ModificationIntegral

local instance topo {V : Scheme.{0}} (g : V ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint g) := schemeAnalyticPointTopology g

local instance charts {V : Scheme.{0}} (g : V ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n g] :
    ChartedSpace (ComplexModel n) (SchemeComplexPoint g) := schemeAnalyticTNChartedSpace g n

local instance manifold {V : Scheme.{0}} (g : V ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n g] [IsSeparated g] [QuasiCompact g] :
    IsComplexManifold n (SchemeComplexPoint g) := schemeAnalyticTN_isComplexManifold g n

private theorem mixedDegreeNativeConnected {S : Scheme.{0}}
    (g : S ⟶ Spec (.of ℂ)) (n : ℕ) (EG : ClosedProjectiveEmbedding g)
    [IsIntegral S] [SmoothOfRelativeDimension n g] : ConnectedSpace (SchemeComplexPoint g) := by
  let := EG.locallyOfFiniteType
  let : Nonempty (SchemeComplexPoint g) := integralFiniteTypeSchemeComplexPoint_nonempty g
  exact SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral g EG n

private theorem mixedDegree_chern_linearCombination {V : Scheme.{0}}
    (g : V ⟶ Spec (.of ℂ)) (n : ℕ) [SmoothOfRelativeDimension n g]
    [IsSeparated g] [QuasiCompact g] {ι : Type*}
    (θ : ι → ClosedRealOneOneForm n (SchemeComplexPoint g)) (v : ι →₀ ℝ) :
    RealBottChern.ofRepresentative (Finsupp.linearCombination ℝ θ v) =
      Finsupp.linearCombination ℝ (fun i => RealBottChern.ofRepresentative (θ i)) v := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => rw [map_add, map_add, RealBottChern.ofRepresentative_add, hv, hw]
  | single i a => simp [Finsupp.linearCombination_single]

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))
    (E : ClosedProjectiveEmbedding f) {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]
    [IsSeparated f] [QuasiCompact f] [CompactSpace (SchemeComplexPoint f)]

include E in
/-- Ordinary mixed degree is preserved by domination, even when both tuples are
arbitrary representatives of their numerical classes and the Euler base lines
are chosen independently. Apply this to the identity for representative
independence and to a common higher model for model independence. -/
theorem originalMixedDegree_eq_of_numerical_pullback_bd7
    {A B : SmoothAlgebraicModel f (m + 1)} (h : A ≤ B)
    (LA : IntrinsicLineBundle A.V) (LB : IntrinsicLineBundle B.V)
    (a : Fin (m + 1) → CartierCombinations A.V) (b : Fin (m + 1) → CartierCombinations B.V)
    (hab : letI := A.embedding.isSeparated
      letI := A.embedding.quasiCompact
      letI := B.embedding.isSeparated
      letI := B.embedding.quasiCompact
      letI := A.embedding.analyticCompact
      letI := B.embedding.analyticCompact
      letI := mixedDegreeNativeConnected (A.p ≫ f) (m + 1) A.embedding
      letI := mixedDegreeNativeConnected (B.p ≫ f) (m + 1) B.embedding
      ∀ i,
      numericalCartierPullback (B.p ≫ f) (A.p ≫ f) B.embedding A.embedding (m := m)
          normalizationProjectiveForCurves_bd7 (A.homOfLE h) (SmoothAlgebraicModel.homOfLE_structure h)
          ((originalIntegralCurveDegreeRelations_bd7 (A.p ≫ f) A.embedding).mkQ (a i)) =
        (originalIntegralCurveDegreeRelations_bd7 (B.p ≫ f) B.embedding).mkQ (b i)) :
    originalRealMixedEuler (B.p ≫ f) B.embedding (m + 1) LB b =
      originalRealMixedEuler (A.p ≫ f) A.embedding (m + 1) LA a := by
  let g := A.p ≫ f
  let G := B.p ≫ f
  let : IsIntegral A.V := A.integral
  let : IsIntegral B.V := B.integral
  let : SmoothOfRelativeDimension (m + 1) g := A.smooth
  let : SmoothOfRelativeDimension (m + 1) G := B.smooth
  let : IsSeparated g := A.embedding.isSeparated
  let : QuasiCompact g := A.embedding.quasiCompact
  let : IsSeparated G := B.embedding.isSeparated
  let : QuasiCompact G := B.embedding.quasiCompact
  let : CompactSpace (SchemeComplexPoint g) := A.embedding.analyticCompact
  let : CompactSpace (SchemeComplexPoint G) := B.embedding.analyticCompact
  let : ConnectedSpace (SchemeComplexPoint g) := mixedDegreeNativeConnected g (m + 1) A.embedding
  let : ConnectedSpace (SchemeComplexPoint G) := mixedDegreeNativeConnected G (m + 1) B.embedding
  let : MeasurableSpace (SchemeComplexPoint g) := borel _
  let : BorelSpace (SchemeComplexPoint g) := ⟨rfl⟩
  let : MeasurableSpace (SchemeComplexPoint G) := borel _
  let : BorelSpace (SchemeComplexPoint G) := ⟨rfl⟩
  let κ := schemeProjectiveTNKahlerBackground g (m + 1) A.embedding
  let Κ := schemeProjectiveTNKahlerBackground G (m + 1) B.embedding
  let K (L : IntrinsicLineBundle A.V) := schemeLineBundleMetric g (m + 1) A.embedding L.atlas
  let K' (L : IntrinsicLineBundle B.V) := schemeLineBundleMetric G (m + 1) B.embedding L.atlas
  let θ (i : Fin (m + 1)) := Finsupp.linearCombination ℝ (fun L => (K L).curvature L.atlas) (a i)
  let η (i : Fin (m + 1)) := Finsupp.linearCombination ℝ (fun L => (K' L).curvature L.atlas) (b i)
  let hp := SmoothAlgebraicModel.homOfLE_analyticModification h E
  have hclass (i : Fin (m + 1)) :
      RealBottChern.ofRepresentative (η i) =
        RealBottChern.ofRepresentative (ClosedRealOneOneForm.pullback hp.1 (θ i)) := by
    dsimp only [η, θ]
    rw [mixedDegree_chern_linearCombination G (m + 1), ← classPullback_ofRepresentative,
      mixedDegree_chern_linearCombination g (m + 1)]
    have hi := numericalChern_numericalCartierPullback G g B.embedding A.embedding (m := m)
      normalizationProjectiveForCurves_bd7 (A.homOfLE h) (SmoothAlgebraicModel.homOfLE_structure h)
      ((originalIntegralCurveDegreeRelations_bd7 g A.embedding).mkQ (a i))
    rw [hab i, numericalChern_mkQ, numericalChern_mkQ] at hi
    exact hi
  calc
    _ = slotIntegral Κ η := originalRealMixedEuler_eq_slotIntegral_bd3 m G B.embedding LB K' Κ b
    _ = slotIntegral Κ (fun i => ClosedRealOneOneForm.pullback hp.1 (θ i)) :=
      slotIntegral_eq_of_bottChernRel Κ _ _ (fun i =>
        (RealBottChern.ofRepresentative_eq_iff _ _).mp (hclass i))
    _ = slotIntegral κ θ := slotIntegral_pullback_actualModification_bd7 hp κ Κ θ
    _ = _ := (originalRealMixedEuler_eq_slotIntegral_bd3 m g A.embedding LA K κ a).symm

end SGPT.BDivisor.BD7
