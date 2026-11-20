import SGPT.Foundations.Analysis.Pending.MixedMassProductCalculus
import SGPT.Foundations.Analysis.Pending.KahlerVolumePositive
import SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Bergman.ReferenceEnvelopeConvergence

open Set MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending
open GlobalNonPluripolar GlobalDiagonalScaling GlobalMultilinearExpansion
open MixedMassProductCalculus DiagonalMass
open scoped ENNReal

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

/-- An ACTUAL Kahler current manufactures its original positive lower
volume bound. The all-Kahler selector of the actual finite mixed-product
expansion proves a WHOLE measure inequality, including n=0. No positive
mass, mixed expansion or lower-volume certificate is supplied. -/
theorem exists_kahlerVolume_le_of_kahlerCurrentPotential
    (omega : KahlerBackground n X) (theta : ClosedRealOneOneForm n X)
    {phi : X → EReal} (hcurrent : IsKahlerCurrentPotential theta phi) :
    ∃ kappa : KahlerBackground n X, ∃ hphi : IsThetaPshPotential theta.val phi,
      diagonalPotentialMeasure kappa.form (fun _ => 0)
          ((LocalPotentials.isThetaPshPotential_zero_iff kappa.form).mpr kappa.isSemipositive) ≤
        diagonalPotentialMeasure theta phi hphi := by
  classical
  obtain ⟨kappa, hstrict⟩ := hcurrent
  have hphi : IsThetaPshPotential theta.val phi := by
    simpa only [sub_add_cancel] using
      LocalPotentials.isThetaPshPotential_add_of_semipositive hstrict kappa.isSemipositive
  let A : Bool → ClosedRealOneOneForm n X := fun b => if b then kappa.form else theta - kappa.form
  let f : Bool → X → EReal := fun b x => if b then 0 else phi x
  have hf : ∀ b, IsThetaPshPotential (A b).val (f b) := by
    intro b
    cases b
    · exact hstrict
    · exact (LocalPotentials.isThetaPshPotential_zero_iff kappa.form).mpr kappa.isSemipositive
  have hforms : (fun _ : Fin n => sumForm Finset.univ (fun _ : Bool => (1 : ℝ)) A) =
      fun _ => theta := by
    funext i
    simp only [sumForm, Fintype.sum_bool, one_smul, A, Bool.false_eq_true, if_false, if_true]
    abel
  have hpots : (fun _ : Fin n => sumPot Finset.univ (fun _ : Bool => (1 : ℝ)) f) =
      fun _ => phi := by
    funext i x
    simp [sumPot, f]
  have heq := globalMixedMeasure_sumPot_expand omega
    (c := fun (_ : Fin n) (_ : Bool) => (1 : ℝ)) (fun _ _ => zero_le_one) hf
  rw [globalMixedMeasure_congr hforms hpots _ (fun _ => hphi.1)] at heq
  let selector : Fin n → Bool := fun _ => true
  have hterm := Finset.single_le_sum
    (f := fun g : Fin n → Bool => ENNReal.ofReal (∏ i : Fin n, (1 : ℝ)) •
      globalMixedMeasure (fun i => A (g i)) (fun i => f (g i)) (fun i => (hf (g i)).1))
    (fun _ _ => Measure.zero_le _) (Finset.mem_univ selector)
  simp only [Finset.prod_const_one, ENNReal.ofReal_one, one_smul] at heq hterm
  refine ⟨kappa, hphi, ?_⟩
  dsimp only [diagonalPotentialMeasure]
  rw [heq]
  simpa [selector, A, f] using hterm

variable [Nonempty X]

/-- Actual Kahler-current positivity produces BOTH native PSH and strict
positive original nonpluripolar mass, rather than assuming the latter. -/
theorem exists_positiveMass_of_kahlerCurrentPotential
    (omega : KahlerBackground n X) (theta : ClosedRealOneOneForm n X)
    {phi : X → EReal} (hcurrent : IsKahlerCurrentPotential theta phi) :
    ∃ hphi : IsThetaPshPotential theta.val phi, 0 < diagonalPotentialMass theta phi hphi := by
  obtain ⟨kappa, hphi, hle⟩ := exists_kahlerVolume_le_of_kahlerCurrentPotential omega theta hcurrent
  exact ⟨hphi, (KahlerVolumePositive.diagonalPotentialMass_zero_pos kappa).trans_le (hle univ)⟩

end SGPT.Bergman.ReferenceEnvelopeConvergence
