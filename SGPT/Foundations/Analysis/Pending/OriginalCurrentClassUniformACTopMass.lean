import SGPT.Foundations.Analysis.Pending.ThetaCurrentGlobalACDomination
import SGPT.Foundations.Analysis.Pending.PositiveCurrentPrescribedBottChernRepresentation
import SGPT.Foundations.Analysis.Pending.AmbientMassBackgroundMonotone
import SGPT.Foundations.Analysis.Pending.GlobalMixedMassMonotone

set_option autoImplicit false

/-! ONE finite bound BEFORE ALL original fullpositive closed type11 currents
in the specified actual BottChern class. Full BP math/proof precedes Lean.
Internal prescribed-class potential, global AC<=NP, positive background
increment and genuine singularity mass order. No supplied representation,
reader, atlas, analytic, compatible, finite or smoothing certificate. -/
noncomputable section
open Set MeasureTheory
open scoped Topology ENNReal
namespace SGPT.Foundations.Analysis.Pending.OriginalCurrentClassUniformACTopMass
open FirstPass FirstPass.PositiveClasses
  _root_.SGPT.Foundations.Analysis.LocalCurrents GlobalCurrents GlobalCurrentPotentials CanonicalCurrentFrame
  CurrentBottChernClass GlobalPositiveCurrentACRestriction GlobalPositiveCurrentACTopMeasure
  NaturalThetaPshGeometricCurrent PositiveCurrentPrescribedBottChernRepresentation
  ThetaCurrentGlobalACDomination GlobalNonPluripolar MixedMass GlobalMixedMassMonotone

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel (m+1)) M] [IsComplexManifold (m+1) M] [CompactSpace M]

private theorem global_ac_congr
    {T S : GlobalCurrent (m+1) M (degreeTwo (Nat.succ_pos m))}
    (hT : IsFullPositive T) (hS : IsFullPositive S) (h : T = S) :
    globalACtopMeasure T hT = globalACtopMeasure S hS := by
  subst S
  rfl

/-- ONE finite AC-top bound is chosen before ALL original positive closed
currents in the fixed genuine BottChern class. No potential is an input. -/
theorem exists_uniform_ac_top_mass_of_class
    (omega : KahlerBackground (m+1) M) (θ : ClosedRealOneOneForm (m+1) M) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ (T : ClosedOneOneCurrent (M := M) (canonicalBasis (m+1)) (Nat.succ_pos m))
        (hT : IsFullPositive T.val),
        bottChernClass (canonicalBasis (m+1)) (Nat.succ_pos m) T =
          RealBottChern.ofRepresentative θ → globalACtopMeasure T.val hT univ ≤ C := by
  rcases isEmpty_or_nonempty M with hM | hM
  · let := hM
    refine ⟨0,by simp,fun T hT _hclass => ?_⟩
    have hempty : (univ : Set M) = ∅ := by
      ext x
      exact isEmptyElim x
    simp only [hempty,measure_empty,le_refl]
  · let := hM
    obtain ⟨A,hA,hη⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul omega θ
    let η := θ + A • omega.form
    have hzero : IsThetaPshPotential η.val (fun _ : M => 0) :=
      (LocalPotentials.isThetaPshPotential_zero_iff η).mpr hη
    let C := globalMixedMeasure (fun _ : Fin (m+1) => η) (fun _ _ => 0)
      (fun _ => hzero.1) univ
    have hC : C < ⊤ := globalMixedMeasure_apply_lt_top omega (fun _ => hzero.1) univ
    refine ⟨C,hC,fun T hT hclass => ?_⟩
    obtain ⟨u,hu,hEq,_hreader⟩ := exists_theta_representation_of_class_eq T θ hT hclass
    let hpos : IsFullPositive (thetaPotentialCurrent θ.val u hu) :=
      fun e α hα => thetaPotentialCurrent_full_positive θ.val u hu e α hα
    rw [global_ac_congr hT hpos hEq]
    have hAC := globalACtopMeasure_le_globalMixedMeasure omega θ hu
    have hAω := KahlerDomination.isSemipositive_smul omega.isSemipositive hA.le
    have hue : IsThetaPshPotential η.val u :=
      LocalPotentials.isThetaPshPotential_add_of_semipositive hu hAω
    have hbg := AmbientMassBackgroundMonotone.globalMixedMeasure_diagonal_le_add_smul
      omega.isSemipositive hA hu hue.1
    obtain ⟨B,hB⟩ := hu.exists_global_upper_bound
    have horder : MoreSingularOn u (fun _ => 0) univ := by
      refine ⟨B,fun x _ => ?_⟩
      simpa only [zero_add] using hB x
    have hmass := globalMixedMass_mono_of_isThetaPshPotential omega
      (fun _ : Fin (m+1) => hue) (fun _ : Fin (m+1) => hzero) (fun _ => horder)
    calc
      _ ≤ globalMixedMeasure (fun _ : Fin (m+1) => θ) (fun _ => u) (fun _ => hu.1) univ :=
        Measure.le_iff'.mp hAC univ
      _ ≤ globalMixedMeasure (fun _ : Fin (m+1) => η) (fun _ => u) (fun _ => hue.1) univ :=
        Measure.le_iff'.mp hbg univ
      _ ≤ C := hmass

end SGPT.Foundations.Analysis.Pending.OriginalCurrentClassUniformACTopMass
