import SGPT.Okounkov.FlagResidualCombinations
import SGPT.Foundations.Analysis.Pending.TraceRepresentativeAddition

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Okounkov
open Set Filter
open scoped Manifold ContDiff NNReal ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Foundations.Analysis.Pending ThetaPshCodimTwoExtension
open SourceTraceRepresentativeDefinition NaturalSubmanifoldSourceTraceDefinition

/-- Every actual original sum step gives the ideal class of the sum of
the two original target traces. All unit metrics, recorded approximations
and actual admissible trace backgrounds remain arbitrary. -/
theorem originalFlagStep_add_target_iEquivalent {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1))
    {u v : F.carrier → EReal} {τu τv τs : F.tail.carrier → EReal}
    (hTu : OriginalFlagStep F u τu) (hTv : OriginalFlagStep F v τv)
    (hTs : OriginalFlagStep F (fun x => u x + v x) τs) :
    IEquivalentOnManifold (n := m) τs (fun y => τu y + τv y) := by
  obtain ⟨θ, hu, D₀, hDI₀, E₀, hEW₀, hmetric₀, hTu⟩ := hTu
  obtain ⟨σ, hv, D₁, hDI₁, E₁, hEW₁, hmetric₁, hTv⟩ := hTv
  obtain ⟨_γ, _hγ, Ds, hDIs, Es, hEWs, hmetrics, hTs⟩ := hTs
  let : MeasurableSpace F.carrier := borel F.carrier
  let : BorelSpace F.carrier := ⟨rfl⟩
  have hIambient := iEquivalent_smooth_divisor_residual_add_of_unit_metrics
    F.omega hu hv F.firstDivisor D₀ D₁ Ds hDI₀ hDI₁ hDIs E₀ E₁ Es
      hEW₀ hEW₁ hEWs hmetric₀ hmetric₁ hmetrics
  have hr₀ := isThetaPshPotential_smooth_divisor_residual_of_unit_metric
    hu F.firstDivisor D₀ hDI₀ E₀ hEW₀ hmetric₀
  have hr₁ := isThetaPshPotential_smooth_divisor_residual_of_unit_metric
    hv F.firstDivisor D₁ hDI₁ E₁ hEW₁ hmetric₁
  let W := F.flag (1 : Fin (m + 2))
  let := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ m) F.firstDivisor.2.2
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace
    (Nat.le_succ m) F.firstDivisor.2.2
  let : CompactSpace W := F.tail.compact
  let : ConnectedSpace W := F.tail.connected
  let : MeasurableSpace W := borel W
  let : BorelSpace W := ⟨rfl⟩
  let : MeasurableSpace F.tail.carrier := borel F.tail.carrier
  let : BorelSpace F.tail.carrier := ⟨rfl⟩
  let hι := SubmanifoldChartedSpace.contMDiff_val (Nat.le_succ m) F.firstDivisor.2.2
  change IsSourceTraceRepresentativeAlong F.omega F.tail.omega hι _ τu at hTu
  change IsSourceTraceRepresentativeAlong F.omega F.tail.omega hι _ τv at hTv
  change IsSourceTraceRepresentativeAlong F.omega F.tail.omega hι _ τs at hTs
  have hzeroSource : sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → F.carrier)
      (fun x => extensionAcross W (smoothDivisorOffResidual E₀
        (sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → F.carrier) u).toNNReal u) x +
        extensionAcross W (smoothDivisorOffResidual E₁
          (sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → F.carrier) v).toNNReal v) x) = 0 := by
    rw [sourceGeneric_subtype_add_eq F.firstDivisor hr₀.quasiPshPotential hr₁.quasiPshPotential]
    exact (congrArg₂ (fun a b : ℝ≥0∞ => a + b) hTu.1 hTv.1).trans (zero_add 0)
  have hnativeu := (isSourceTraceRepresentativeAlong_iff_native
    (Nat.succ_ne_zero m) F.omega F.tail.omega hι _ _).mp hTu
  have hnativev := (isSourceTraceRepresentativeAlong_iff_native
    (Nat.succ_ne_zero m) F.omega F.tail.omega hι _ _).mp hTv
  obtain ⟨omegaSum, hnativeSum⟩ := TraceRepresentativeAddition.isTraceRepresentativeAlong_add
    F.tail.omega F.tail.omega F.tail.omega hι hnativeu hnativev
      ((nativeGeneric_zero_iff_source (Nat.succ_ne_zero m) (Subtype.val : W → F.carrier) _).mpr hzeroSource)
  have hsourceSum := (isSourceTraceRepresentativeAlong_iff_native
    (Nat.succ_ne_zero m) omegaSum F.tail.omega hι _ _).mpr hnativeSum
  exact iEquivalent_of_iEquivalent_of_sourceTraceRepresentatives
    (Nat.succ_ne_zero m) F.tail.omega F.tail.omega hι hTs hsourceSum hIambient

end SGPT.Okounkov
