import SGPT.PSH.SourceNABackgroundChange
import SGPT.PSH.SourceNonArchimedeanPositivePart
import SGPT.Foundations.Analysis.Pending.GlobalMultilinearExpansion

/-! Actual semipositive positive-volume NA readers in every dimension.
The lower bound is manufactured by the genuine mixed-MA expansion, including
its all-smooth summand. No lower-bound/positive-volume conclusion certificate
for the input NA system is accepted. -/
set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas.WholeClosureNA

open Set MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open GlobalNonPluripolar GlobalDiagonalScaling GlobalMultilinearExpansion DiagonalMass

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- The genuine smooth top-wedge mass is bounded above by the mass after
adding a semipositive form to ANY genuine theta-psh current. The unique empty
selector in dimension zero is retained by the same proof. -/
theorem zero_mass_le_add_semipositive {α η : ClosedRealOneOneForm n M}
    {u : M → EReal} (hu : IsThetaPshPotential α.val u)
    (hη : η.val.IsSemipositive) :
    diagonalPotentialMass η (fun _ => 0)
      ((LocalPotentials.isThetaPshPotential_zero_iff η).mpr hη) ≤
    diagonalPotentialMass (α + η) u
      (LocalPotentials.isThetaPshPotential_add_of_semipositive hu hη) := by
  classical
  let A : Bool → ClosedRealOneOneForm n M := fun b => if b then η else α
  let F : Bool → M → EReal := fun b => if b then (fun _ => 0) else u
  have hz : IsThetaPshPotential η.val (fun _ : M => 0) :=
    (LocalPotentials.isThetaPshPotential_zero_iff η).mpr hη
  have hp (b : Bool) : IsThetaPshPotential (A b).val (F b) := by
    cases b
    · exact hu
    · exact hz
  have hsumA : (fun _ : Fin n => sumForm Finset.univ (fun _ : Bool => (1 : ℝ)) A) =
      fun _ => α + η := by
    funext i
    simp [sumForm, A, add_comm]
  have hsumF : (fun _ : Fin n => sumPot Finset.univ (fun _ : Bool => (1 : ℝ)) F) =
      fun _ => u := by
    funext i x
    simp [sumPot, F]
  have hexp := globalMixedMeasure_diagonal_sumPot
    (T := (Finset.univ : Finset Bool)) (by simp)
    (w := fun _ => (1 : ℝ)) (fun _ => zero_lt_one)
    (fun b => (hp b).1) (fun b => (hp b).quasiPshPotential)
  rw [globalMixedMeasure_congr hsumA hsumF _
    (fun _ => (LocalPotentials.isThetaPshPotential_add_of_semipositive hu hη).1)] at hexp
  simp only [Finset.prod_const_one, ENNReal.ofReal_one, one_smul] at hexp
  have hmem : (fun _ : Fin n => true) ∈
      Fintype.piFinset (fun _ : Fin n => (Finset.univ : Finset Bool)) := by simp
  have hterm : globalMixedMeasure (fun j : Fin n => A ((fun _ => true) j))
      (fun j => F ((fun _ : Fin n => true) j)) (fun j => (hp ((fun _ => true) j)).1) =
      globalMixedMeasure (fun _ : Fin n => η) (fun _ => (fun _ : M => (0 : EReal)))
        (fun _ => hz.1) :=
    globalMixedMeasure_congr (by funext j; rfl) (by funext j x; rfl) _ _
  have hle := Finset.single_le_sum
    (s := Fintype.piFinset (fun _ : Fin n => (Finset.univ : Finset Bool)))
    (f := fun g : Fin n → Bool => globalMixedMeasure (fun j => A (g j))
      (fun j => F (g j)) (fun j => (hp (g j)).1))
    (fun _ _ => Measure.zero_le _) hmem
  rw [hterm, ← hexp] at hle
  exact hle univ

variable [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

omit [BorelSpace M] [ConnectedSpace M] in
private theorem cast_limit_mass
    {α β : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    (G : SourcePositiveIModelTestCurve α) (h : α = β) :
    sourcePotentialNonPluripolarMeasure β
      (sourceTestCurveLimit (G.castBackground h).val.toSourceTestCurvePredata)
      (G.castBackground h).val.limit_thetaPSH univ =
    sourcePotentialNonPluripolarMeasure α
      (sourceTestCurveLimit G.val.toSourceTestCurvePredata) G.val.limit_thetaPSH univ := by
  cases h
  rfl

/-- At every original Kähler index the actual background-change component
has at least the smooth top-wedge mass of eta. Compatibility supplies the
smaller reader; no positivity premise on the original NA volume is used. -/
theorem sourceNAComponentMass_backgroundChange_lower
    (Γ : SourceNAPotential θ)
    (η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive) (κ : SourceKahlerForm n M) :
    diagonalPotentialMass (atlasClosedFormToNative η) (fun _ => 0)
      ((LocalPotentials.isThetaPshPotential_zero_iff _).mpr hη) ≤
      sourceNAComponentMass (Γ.backgroundChange η hη) κ := by
  let omega := sourceKahlerFormRepresentative κ
  let omegaA := sourceNAAugmentedKahlerBackground η hη omega
  let α := sourceTestCurveEnlargedBackground omega θ
  let β := sourceTestCurveEnlargedBackground omegaA θ
  let G := Γ.realizedComponent omega
  let H := Γ.realizedComponent omegaA
  let u := sourceTestCurveLimit G.val.toSourceTestCurvePredata
  have hu : (ofFixedModel n M).IsThetaPSH α u := G.val.limit_thetaPSH
  have hi : sourceIModel α u := G.val.limit_iModel omega
    ((sourceIModelTestCurvesPositive_iff_slices omega G.val).mp G.property)
  have hform : atlasClosedFormToNative β =
      atlasClosedFormToNative α + atlasClosedFormToNative η := by
    dsimp only [α, β, omegaA]
    rw [sourceTestCurveEnlargedBackground_native, sourceTestCurveEnlargedBackground_native]
    change atlasClosedFormToNative θ + (atlasClosedFormToNative η + omega.form) = _
    abel
  have hgap : (atlasClosedFormToNative β - atlasClosedFormToNative α).val.IsSemipositive := by
    rw [hform, add_sub_cancel_left]
    exact hη
  have haug : (omegaA.form - omega.form).val.IsSemipositive := by
    simpa only [omegaA, sourceNAAugmentedKahlerBackground, add_sub_cancel_right] using hη
  have hlim : sourceTestCurveLimit H.val.toSourceTestCurvePredata = sourceIEnvelope β u :=
    Γ.realizedComponent_limit_transition haug
  have hm := (sourceIModel_transition_envelope_and_mass omega hgap hi G.val.positiveLimitMass).2
  have hlow := zero_mass_le_add_semipositive
    ((isThetaPSH_iff_nativeThetaPotential α u).mp hu) hη
  have hmass : sourcePotentialNonPluripolarMeasure β
      (sourceTestCurveLimit H.val.toSourceTestCurvePredata) H.val.limit_thetaPSH univ =
      sourcePotentialNonPluripolarMeasure β u
        (sourceThetaPSH_of_semipositive_difference hgap hu) univ := by
    exact (sourcePotentialMass_congr hlim H.val.limit_thetaPSH _).trans hm
  have hc : sourceNAComponentMass (Γ.backgroundChange η hη) κ =
      sourcePotentialNonPluripolarMeasure β
        (sourceTestCurveLimit H.val.toSourceTestCurvePredata) H.val.limit_thetaPSH univ := by
    exact cast_limit_mass H (sourceNAAugmentedComponentBackground_eq θ η hη κ)
  rw [hc, hmass]
  simpa only [sourcePotentialNonPluripolarMeasure, diagonalPotentialMass, ← hform] using hlow

/-- Genuine semipositive addition increases the whole original NA volume by
at least its smooth top-wedge mass; the infimum is over ALL actual indices. -/
theorem sourceNAVolume_backgroundChange_lower
    (Γ : SourceNAPotential θ)
    (η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive) :
    diagonalPotentialMass (atlasClosedFormToNative η) (fun _ => 0)
      ((LocalPotentials.isThetaPshPotential_zero_iff _).mpr hη) ≤
      sourceNAVolume (Γ.backgroundChange η hη) :=
  le_iInf fun κ => sourceNAComponentMass_backgroundChange_lower Γ η hη κ

/-- Positive-volume semipositive eta therefore manufactures the actual positive
I-model reader using the existing proved positive-part recovery theorem.
The volume input here is exactly the geometric source hypothesis on eta,
never a hypothesis on the target system or recovered reader. -/
def semipositivePositiveVolumeReader (omega : KahlerBackground n M)
    (Γ : SourceNAPotential θ)
    (η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive)
    (hvol : 0 < diagonalPotentialMass (atlasClosedFormToNative η) (fun _ => 0)
      ((LocalPotentials.isThetaPshPotential_zero_iff _).mpr hη)) :
    SourcePositiveIModelTestCurve (θ.add η) :=
  sourceNARecoveredPositiveCurve omega (Γ.backgroundChange η hη)
    (hvol.trans_le (sourceNAVolume_backgroundChange_lower Γ η hη))

theorem semipositivePositiveVolumeReader_embedding (omega : KahlerBackground n M)
    (Γ : SourceNAPotential θ)
    (η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive)
    (hvol : 0 < diagonalPotentialMass (atlasClosedFormToNative η) (fun _ => 0)
      ((LocalPotentials.isThetaPshPotential_zero_iff _).mpr hη)) :
    sourcePositiveTestCurveToNA (semipositivePositiveVolumeReader omega Γ η hη hvol) =
      Γ.backgroundChange η hη :=
  sourceNARecoveredPositiveCurve_embedding omega (Γ.backgroundChange η hη)
    (hvol.trans_le (sourceNAVolume_backgroundChange_lower Γ η hη))

end SGPT.PSH.VariableComplexAtlas.WholeClosureNA
