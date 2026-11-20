import SGPT.Bergman.SourceKahlerCurrentPositiveMass
import SGPT.PSH.Pluripolar

set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.ReferenceEnvelopeConvergence

open Set MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending DiagonalMass
open SGPT.PSH SGPT.PSH.VariableComplexAtlas

/-- The EXACT original non-pluripolar-subset hypothesis produces actual
ambient nonemptiness. No connected-space convention is substituted. -/
theorem sourceNonPluripolar_ambient_nonempty
    {X : Type*} [TopologicalSpace X] (A : VariableComplexAtlas X)
    {K : Set X} (hK : A.NonPluripolar K) : Nonempty X := by
  classical
  by_contra hn
  apply hK
  intro x
  exact (hn ⟨x⟩).elim

/-- Original Bergman700/704/832/833 consumer: the original non-pluripolar
K plus actual Kahler-current phi PROVE strict actual NPP mass. There is
NO Nonempty, ConnectedSpace, volume1 or mass-positivity hypothesis. The
raw actual lower-volume term and dimension0 normalization are retained. -/
theorem exists_source_positiveMass_of_nonPluripolar_and_kahlerCurrent
    {n : ℕ} {X : Type} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
    (omega : KahlerBackground n X) (theta : ClosedRealOneOneForm n X)
    {K : Set X} (hK : (ofFixedModel n X).NonPluripolar K)
    {phi : X → EReal} (hcurrent : IsKahlerCurrentPotential theta phi) :
    ∃ hphi : IsThetaPshPotential theta.val phi, 0 < diagonalPotentialMass theta phi hphi := by
  let : Nonempty X := sourceNonPluripolar_ambient_nonempty (ofFixedModel n X) hK
  exact exists_positiveMass_of_kahlerCurrentPotential omega theta hcurrent

end SGPT.Bergman.ReferenceEnvelopeConvergence
