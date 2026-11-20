import SGPT.Foundations.Analysis.Pending.DominationIntersectionNumbers
import Mathlib.Geometry.Manifold.Diffeomorph

/-! Actual full complex diffeomorphisms preserve literal original mixed
periods. Blueprint: actual-diffeomorph-slot-integral.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections

open Set Filter MeasureTheory
open scoped Topology ENNReal Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open GlobalNonPluripolar ModificationMassInvariance DominationIntersectionNumbers NefMixedMass

variable {n : ℕ} {X Y : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]

omit [IsComplexManifold n X] [IsComplexManifold n Y] in
/-- The ACTUAL entire diffeomorphism has no exceptional locus or lost component. -/
theorem actualDiffeomorph_isIsomorphismOver
    (e : Diffeomorph 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) Y X ∞) :
    IsIsomorphismOver n e univ := by
  refine ⟨?_, ?_⟩
  · exact ⟨fun _ _ => mem_univ _, e.injective.injOn, fun x _ =>
      ⟨e.symm x, mem_univ _, e.apply_symm_apply x⟩⟩
  · apply Set.disjoint_left.mpr
    intro y _ hy
    apply hy
    have hh := (e.toOpenPartialHomeomorph_mdifferentiable (by simp)).mfderiv_bijective
      (x := y) (by simp)
    have he : (e.toHomeomorph.toOpenPartialHomeomorph : Y → X) = (e : Y → X) := rfl
    rw [he] at hh
    exact hh

variable [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
  [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]

/-- Actual original mixed-measure covariance on the WHOLE diffeomorphism domain. -/
theorem globalMixedMeasure_univ_actualDiffeomorph
    (e : Diffeomorph 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) Y X ∞)
    (theta : Fin n → ClosedRealOneOneForm n X) {u : Fin n → X → EReal}
    (hu : ∀ i, ThetaPlurisubharmonic (theta i).val (u i))
    (hu' : ∀ i, ThetaPlurisubharmonic (pullbackTuple e.contMDiff theta i).val (fun y => u i (e y))) :
    globalMixedMeasure (pullbackTuple e.contMDiff theta) (fun i y => u i (e y)) hu' univ =
      globalMixedMeasure theta u hu univ := by
  rcases isEmpty_or_nonempty Y with hY | hY
  · let : IsEmpty X := ⟨fun x => hY.false (e.symm x)⟩
    simp only [Set.eq_empty_of_isEmpty (univ : Set X), Set.eq_empty_of_isEmpty (univ : Set Y), measure_empty]
  · let := hY
    have hiso := actualDiffeomorph_isIsomorphismOver e
    have hnat := globalMixedMeasure_restrict_preimage_eq_map e.contMDiff isOpen_univ hiso hu hu'
    simp only [Set.preimage_univ, Measure.restrict_univ] at hnat
    have hm : AEMeasurable (invOver e univ) (globalMixedMeasure theta u hu) :=
      (continuousOn_univ.mp (continuousOn_invOver e.contMDiff isOpen_univ hiso)).aemeasurable
    rw [hnat, Measure.map_apply_of_aemeasurable hm MeasurableSet.univ, Set.preimage_univ]

/-- The WHOLE actual diffeomorphism preserves the independent original slot integral. -/
theorem slotIntegral_pullback_actualDiffeomorph
    (e : Diffeomorph 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) Y X ∞)
    (w : KahlerBackground n X) (w' : KahlerBackground n Y)
    (theta : Fin n → ClosedRealOneOneForm n X) :
    slotIntegral w' (fun i => ClosedRealOneOneForm.pullback e.contMDiff (theta i)) =
      slotIntegral w theta := by
  classical
  obtain ⟨A, _, hsemi⟩ := KahlerDomination.exists_pos_forall_isSemipositive_add_smul w theta
  set P : Fin n → ClosedRealOneOneForm n X := fun i => theta i + A • w.form with hP
  have hthetaP : theta = fun i => P i + (-A) • w.form := by
    funext i
    simp only [hP, add_assoc, ← add_smul, add_neg_cancel, zero_smul, add_zero]
  have hthetaP' : (fun i => ClosedRealOneOneForm.pullback e.contMDiff (theta i)) = fun i =>
      ClosedRealOneOneForm.pullback e.contMDiff (P i) +
        (-A) • ClosedRealOneOneForm.pullback e.contMDiff w.form := by
    funext i
    rw [← pullback_add_smul, hP]
    congr 1
    simp only [add_assoc, ← add_smul, add_neg_cancel, zero_smul, add_zero]
  have hpiece : ∀ s : Finset (Fin n),
      slotIntegral w' (s.piecewise (fun i => ClosedRealOneOneForm.pullback e.contMDiff (P i))
        fun _ => ClosedRealOneOneForm.pullback e.contMDiff w.form) =
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
    have hpb : (s.piecewise (fun i => ClosedRealOneOneForm.pullback e.contMDiff (P i))
        fun _ => ClosedRealOneOneForm.pullback e.contMDiff w.form) =
        pullbackTuple e.contMDiff (s.piecewise P fun _ => w.form) := by
      funext i
      by_cases hi : i ∈ s
      · simp only [pullbackTuple, Finset.piecewise_eq_of_mem _ _ _ hi]
      · simp only [pullbackTuple, Finset.piecewise_eq_of_notMem _ _ _ hi]
    have h0Y : ∀ i, ThetaPlurisubharmonic (pullbackTuple e.contMDiff
        (s.piecewise P fun _ => w.form) i).val (fun y => (fun _ => (0 : EReal)) (e y)) :=
      fun i => GlobalPotentialPullback.thetaPlurisubharmonic_comp e.contMDiff (h0X i)
    rw [hpb, slotIntegral, slotIntegral,
      ← MixedMassClassInvariance.globalMixedMeasure_real_univ_eq_integral w' _ h0Y,
      ← MixedMassClassInvariance.globalMixedMeasure_real_univ_eq_integral w _ h0X,
      measureReal_def, measureReal_def,
      globalMixedMeasure_univ_actualDiffeomorph e _ h0X h0Y]
  rw [hthetaP', hthetaP, slotIntegral_add_smul_eq_sum, slotIntegral_add_smul_eq_sum]
  exact Finset.sum_congr rfl fun s _ => by rw [hpiece]

end SGPT.Projective.NumEq.CompleteIntersections
