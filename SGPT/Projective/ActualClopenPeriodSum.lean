import SGPT.Foundations.Analysis.Pending.DominationIntersectionNumbers
import SGPT.Foundations.Analysis.Pending.GlobalNonPluripolarKahler

/-! Actual finite disjoint FULL open isomorphism loci preserve the sum of
original mixed periods, using actual measure covariance and multilinearity.
Blueprint: actual-clopen-period-sum.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.AlgebraicCurveDegree
open Set Filter MeasureTheory
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open GlobalNonPluripolar ModificationMassInvariance DominationIntersectionNumbers NefMixedMass
open scoped Topology ENNReal Manifold BigOperators ContDiff
variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

/-- ACTUAL whole source mass equals original measure of genuine entire open image. -/
theorem globalMixedMeasure_fullOpen_mass {Y : Type} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]
    {π : Y → X} (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π)
    {U : Set X} (hU : IsOpen U) (hiso : IsIsomorphismOver n π U) (hfull : π ⁻¹' U = univ)
    (theta : Fin n → ClosedRealOneOneForm n X) {u : Fin n → X → EReal}
    (hu : ∀ i, ThetaPlurisubharmonic (theta i).val (u i))
    (hu' : ∀ i, ThetaPlurisubharmonic (pullbackTuple hπ theta i).val (fun y => u i (π y))) :
    globalMixedMeasure (pullbackTuple hπ theta) (fun i y => u i (π y)) hu' univ =
      globalMixedMeasure theta u hu U := by
  rcases isEmpty_or_nonempty Y with hY | hY
  · let := hY
    have hEmpty : U = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨y, _, _⟩ := hiso.1.2.2 hx
      exact hY.false y
    simp only [hEmpty, Set.eq_empty_of_isEmpty (univ : Set Y), measure_empty]
  · let := hY
    have hnat := globalMixedMeasure_restrict_preimage_eq_map hπ hU hiso hu hu'
    rw [hfull, Measure.restrict_univ] at hnat
    have hm : AEMeasurable (invOver π U) ((globalMixedMeasure theta u hu).restrict U) :=
      (continuousOn_invOver hπ hU hiso).aemeasurable hU.measurableSet
    rw [hnat, Measure.map_apply_of_aemeasurable hm MeasurableSet.univ, Set.preimage_univ,
      Measure.restrict_apply_univ]
variable {ι : Type} [Fintype ι] {Y : ι → Type}
  [∀ c, TopologicalSpace (Y c)] [∀ c, ChartedSpace (ComplexModel n) (Y c)]
  [∀ c, IsComplexManifold n (Y c)] [∀ c, MeasurableSpace (Y c)] [∀ c, BorelSpace (Y c)]
  [∀ c, CompactSpace (Y c)]
  (π : ∀ c, Y c → X)
  (hπ : ∀ c, ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (π c))
  (U : ι → Set X) (hU : ∀ c, IsOpen (U c))
  (hiso : ∀ c, IsIsomorphismOver n (π c) (U c))
  (hfull : ∀ c, π c ⁻¹' U c = univ)
  (hdisjoint : Pairwise (fun c d => Disjoint (U c) (U d))) (hcover : (⋃ c, U c) = univ)

include U hU hiso hfull hdisjoint hcover

/-- Genuine finite original open-cover sum for semipositive test tuples. -/
theorem slotIntegral_sum_fullOpen_semipositive
    (w : KahlerBackground n X) (w' : ∀ c, KahlerBackground n (Y c))
    (theta : Fin n → ClosedRealOneOneForm n X) (htheta : ∀ i, (theta i).val.IsSemipositive) :
    (∑ c, slotIntegral (w' c) (pullbackTuple (hπ c) theta)) = slotIntegral w theta := by
  classical
  have h0 : ∀ i, ThetaPlurisubharmonic (theta i).val (fun _ => (0 : EReal)) :=
    fun i => ((LocalPotentials.isThetaPshPotential_zero_iff _).mpr (htheta i)).1
  have h0' (c : ι) : ∀ i, ThetaPlurisubharmonic (pullbackTuple (hπ c) theta i).val
      (fun y => (fun _ => (0 : EReal)) (π c y)) :=
    fun i => GlobalPotentialPullback.thetaPlurisubharmonic_comp (hπ c) (h0 i)
  let μ := globalMixedMeasure theta (fun _ _ => (0 : EReal)) h0
  let : IsFiniteMeasure μ := globalMixedMeasure_isFiniteMeasure w h0
  have hm (c : ι) : slotIntegral (w' c) (pullbackTuple (hπ c) theta) = μ.real (U c) := by
    rw [slotIntegral, ← MixedMassClassInvariance.globalMixedMeasure_real_univ_eq_integral
      (w' c) _ (h0' c), measureReal_def, measureReal_def,
      globalMixedMeasure_fullOpen_mass (hπ c) (hU c) (hiso c) (hfull c) theta h0 (h0' c)]
  rw [Finset.sum_congr rfl (fun c _ => hm c),
    ← measureReal_iUnion_fintype hdisjoint (fun c => (hU c).measurableSet), hcover]
  exact MixedMassClassInvariance.globalMixedMeasure_real_univ_eq_integral w theta h0

/-- Genuine SAME finite original open-cover sum for ARBITRARY original closed test tuples. -/
theorem slotIntegral_sum_fullOpen (w : KahlerBackground n X) (w' : ∀ c, KahlerBackground n (Y c))
    (theta : Fin n → ClosedRealOneOneForm n X) :
    (∑ c, slotIntegral (w' c) (pullbackTuple (hπ c) theta)) = slotIntegral w theta := by
  classical
  obtain ⟨A, _, hsemi⟩ := KahlerDomination.exists_pos_forall_isSemipositive_add_smul w theta
  let P : Fin n → ClosedRealOneOneForm n X := fun i => theta i + A • w.form
  have hthetaP : theta = fun i => P i + (-A) • w.form := by
    funext i
    simp only [P, add_assoc, ← add_smul, add_neg_cancel, zero_smul, add_zero]
  have hpull (c : ι) : pullbackTuple (hπ c) theta = fun i =>
      ClosedRealOneOneForm.pullback (hπ c) (P i) +
        (-A) • ClosedRealOneOneForm.pullback (hπ c) w.form := by
    funext i
    rw [← pullback_add_smul]
    exact congrArg (ClosedRealOneOneForm.pullback (hπ c)) (congrFun hthetaP i)
  have hpiece (s : Finset (Fin n)) :
      (∑ c, slotIntegral (w' c) (s.piecewise
        (fun i => ClosedRealOneOneForm.pullback (hπ c) (P i))
        (fun _ => ClosedRealOneOneForm.pullback (hπ c) w.form))) =
      slotIntegral w (s.piecewise P (fun _ => w.form)) := by
    have hsem : ∀ i, ((s.piecewise P (fun _ => w.form)) i).val.IsSemipositive := by
      intro i
      by_cases hi : i ∈ s
      · rw [Finset.piecewise_eq_of_mem _ _ _ hi]; exact hsemi i
      · rw [Finset.piecewise_eq_of_notMem _ _ _ hi]; exact w.isSemipositive
    have hpb (c : ι) : (s.piecewise
        (fun i => ClosedRealOneOneForm.pullback (hπ c) (P i))
        (fun _ => ClosedRealOneOneForm.pullback (hπ c) w.form)) =
        pullbackTuple (hπ c) (s.piecewise P (fun _ => w.form)) := by
      funext i
      by_cases hi : i ∈ s
      · simp only [pullbackTuple, Finset.piecewise_eq_of_mem _ _ _ hi]
      · simp only [pullbackTuple, Finset.piecewise_eq_of_notMem _ _ _ hi]
    simp_rw [hpb]
    exact slotIntegral_sum_fullOpen_semipositive π hπ U hU hiso hfull hdisjoint hcover w w' _ hsem
  have hcomponent (c : ι) := congrArg (slotIntegral (w' c)) (hpull c)
  simp_rw [hcomponent, slotIntegral_add_smul_eq_sum]
  rw [hthetaP, slotIntegral_add_smul_eq_sum, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [← Finset.mul_sum, hpiece]

end SGPT.Projective.NumEq.AlgebraicCurveDegree
