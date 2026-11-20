import SGPT.Okounkov.FlagResidualScaling
import SGPT.Foundations.Analysis.Pending.TracePositiveRealHomogeneity

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Okounkov
open Set Filter
open scoped Manifold ContDiff NNReal ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Foundations.Analysis.Pending ThetaPshCodimTwoExtension
open SourceTraceRepresentativeDefinition NaturalSubmanifoldSourceTraceDefinition

/-- True positive scalar source-step homogeneity: every recorded scaled
step has the ideal class of the literal scaled original target trace.
The necessary intermediate trace is produced from actual generic zero. -/
theorem originalFlagStep_pos_smul_target_iEquivalent {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1))
    {u : F.carrier → EReal} {τ τc : F.tail.carrier → EReal}
    {c : ℝ} (hc : 0 < c)
    (hT : OriginalFlagStep F u τ)
    (hTc : OriginalFlagStep F (fun x => (c : EReal) * u x) τc) :
    IEquivalentOnManifold (n := m) τc (fun y => (c : EReal) * τ y) := by
  obtain ⟨θ, hu, D₀, hDI₀, E₀, hEW₀, hmetric₀, hT⟩ := hT
  obtain ⟨_γ, _hγ, D₁, hDI₁, E₁, hEW₁, hmetric₁, hTc⟩ := hTc
  let : MeasurableSpace F.carrier := borel F.carrier
  let : BorelSpace F.carrier := ⟨rfl⟩
  have hIambient := iEquivalent_smooth_divisor_residual_pos_smul
    F.omega hu hc F.firstDivisor D₀ D₁ hDI₀ hDI₁ E₀ E₁ hEW₀ hEW₁ hmetric₀ hmetric₁
  have hr := isThetaPshPotential_smooth_divisor_residual_of_unit_metric
    hu F.firstDivisor D₀ hDI₀ E₀ hEW₀ hmetric₀
  have hcr := RestrictedApproximantComparison.isThetaPshPotential_smul hr hc
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
  change IsSourceTraceRepresentativeAlong F.omega F.tail.omega hι _ τ at hT
  change IsSourceTraceRepresentativeAlong F.omega F.tail.omega hι _ τc at hTc
  have hzeroSource : sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → F.carrier)
      (fun x => (c : EReal) * extensionAcross W (smoothDivisorOffResidual E₀
        (sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → F.carrier) u).toNNReal u) x) = 0 := by
    have hscale := flagGenericLelong_smul_eq F.flag
      (extensionAcross W (smoothDivisorOffResidual E₀
        (sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → F.carrier) u).toNNReal u))
      (1 : Fin (m + 2)) hc
    change sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → F.carrier) _ =
      ENNReal.ofReal c * sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → F.carrier) _ at hscale
    exact hscale.trans ((congrArg (fun a : ℝ≥0∞ => ENNReal.ofReal c * a) hT.1).trans (mul_zero _))
  obtain ⟨ρ, hρ⟩ :=
    NaturalSourceTraceExistenceAllDimensions.exists_naturalSourceTrace_of_isThetaPshPotential
      F.omega F.firstDivisor hcr hzeroSource
  change IsSourceTraceRepresentativeAlong F.omega F.tail.omega hι _ ρ at hρ
  have htarget := iEquivalent_of_iEquivalent_of_sourceTraceRepresentatives
    (Nat.succ_ne_zero m) F.tail.omega F.tail.omega hι hTc hρ hIambient
  have hn := Nat.succ_ne_zero m
  have hnative := (isSourceTraceRepresentativeAlong_iff_native
    hn F.omega F.tail.omega hι _ _).mp hT
  have hnativeScaled := (isSourceTraceRepresentativeAlong_iff_native
    hn F.omega F.tail.omega hι _ _).mp hρ
  have hP := TracePositiveRealHomogeneity.sourcePEquivalent_pos_smul_of_isTraceRepresentativeAlong
    F.tail.omega F.tail.omega hι hnative hc hnativeScaled
  exact htarget.trans (GlobalPMultiplierOrder.iEquivalentOnManifold_of_sourcePEquivalent hP)

end SGPT.Okounkov
