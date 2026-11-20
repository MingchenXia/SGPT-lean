import SGPT.Okounkov.PotentialFlagValuation
import SGPT.Okounkov.ResidualIdealCancellation
import SGPT.Okounkov.ResidualCurrentChoices
import SGPT.Okounkov.SourceTraceIdealOrder

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
open NaturalThetaPshGeometricCurrent

/-- Every actual choice of unit metric and plain source trace carries
original multiplier equivalence to the genuine original tail manifold. -/
theorem originalFlagStep_iEquivalent_of_iEquivalent {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1))
    {u v : F.carrier → EReal} {τu τv : F.tail.carrier → EReal}
    (hI : IEquivalentOnManifold (n := m + 1) u v)
    (hTu : OriginalFlagStep F u τu) (hTv : OriginalFlagStep F v τv) :
    IEquivalentOnManifold (n := m) τu τv := by
  obtain ⟨θ, hu, D₀, hDI₀, E₀, hEW₀, hmetric₀, hTu⟩ := hTu
  obtain ⟨σ, hv, D₁, hDI₁, E₁, hEW₁, hmetric₁, hTv⟩ := hTv
  let : MeasurableSpace F.carrier := borel F.carrier
  let : BorelSpace F.carrier := ⟨rfl⟩
  have hcommon := iEquivalent_smooth_divisor_residuals_of_iEquivalent
    hu hv hI F.firstDivisor D₀ hDI₀ E₀ hEW₀ hmetric₀
  have hv₀ := isThetaPshPotential_smooth_divisor_residual_of_unit_metric
    hv F.firstDivisor D₀ hDI₀ E₀ hEW₀ hmetric₀
  have hv₁ := isThetaPshPotential_smooth_divisor_residual_of_unit_metric
    hv F.firstDivisor D₁ hDI₁ E₁ hEW₁ hmetric₁
  have hchoices := iEquivalent_smooth_divisor_residuals_of_thetaPotentialCurrent_eq
    F.omega hv hv rfl F.firstDivisor D₀ D₁ hDI₀ hDI₁ E₀ E₁
    hEW₀ hEW₁ hmetric₀ hmetric₁ hv₀ hv₁
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
  exact iEquivalent_of_iEquivalent_of_sourceTraceRepresentatives
    (Nat.succ_ne_zero m) F.tail.omega F.tail.omega hι hTu hTv (hcommon.trans hchoices)

/-- Full original dimension induction: every actual trace/unit-metric choice
has the same finite vector on ideal-equivalent genuine original inputs. -/
theorem originalPotentialFlagValuation_eq_of_iEquivalent :
    ∀ (n : ℕ) (F : OriginalFlagGeometry.{u} n)
      (u v : F.carrier → EReal) (ν μ : Fin n → ℝ≥0),
      OriginalPotentialFlagValuation n F u ν →
      OriginalPotentialFlagValuation n F v μ →
      IEquivalentOnManifold (n := n) u v → ν = μ := by
  intro n
  induction n with
  | zero =>
      intro F u v ν μ hν hμ hI
      funext i
      exact Fin.elim0 i
  | succ m ih =>
      intro F u v ν μ hν hμ hI
      obtain ⟨hν₀, τu, hTu, hνtail⟩ := hν
      obtain ⟨hμ₀, τv, hTv, hμtail⟩ := hμ
      have hItarget := originalFlagStep_iEquivalent_of_iEquivalent F hI hTu hTv
      have htail := ih F.tail τu τv (fun i => ν i.succ) (fun i => μ i.succ)
        hνtail hμtail hItarget
      obtain ⟨θ, hu, _D₀, _hDI₀, _E₀, _hEW₀, _hmetric₀, _hTu⟩ := hTu
      obtain ⟨σ, hv, _D₁, _hDI₁, _E₁, _hEW₁, _hmetric₁, _hTv⟩ := hTv
      have hcoef := sourceGeneric_subtype_eq_of_iEquivalent F.firstDivisor
        hu.quasiPshPotential hv.quasiPshPotential hI
      have hhead : ν 0 = μ 0 :=
        hν₀.trans ((congrArg ENNReal.toNNReal hcoef).trans hμ₀.symm)
      funext i
      exact Fin.cases hhead (fun j => congrFun htail j) i

/-- Every genuine original potential has a unique value under the actual
source recursion, independently of every metric and plain-trace choice. -/
theorem existsUnique_originalPotentialFlagValuation {n : ℕ}
    (F : OriginalFlagGeometry.{u} n) {θ : ClosedRealOneOneForm n F.carrier}
    {u : F.carrier → EReal} (hu : IsThetaPshPotential θ.val u) :
    ∃! ν : Fin n → ℝ≥0, OriginalPotentialFlagValuation n F u ν := by
  obtain ⟨ν, hν⟩ := exists_originalPotentialFlagValuation n F θ u hu
  exact ⟨ν, hν, fun μ hμ => originalPotentialFlagValuation_eq_of_iEquivalent
    n F u u μ ν hμ hν (IEquivalentOnManifold.refl u)⟩

/-- The actual finite vector produced by the original dimension recursion. -/
def potentialFlagValuation {n : ℕ} (F : OriginalFlagGeometry.{u} n)
    {θ : ClosedRealOneOneForm n F.carrier} {u : F.carrier → EReal}
    (hu : IsThetaPshPotential θ.val u) : Fin n → ℝ≥0 :=
  Classical.choose (exists_originalPotentialFlagValuation n F θ u hu)

theorem potentialFlagValuation_spec {n : ℕ} (F : OriginalFlagGeometry.{u} n)
    {θ : ClosedRealOneOneForm n F.carrier} {u : F.carrier → EReal}
    (hu : IsThetaPshPotential θ.val u) :
    OriginalPotentialFlagValuation n F u (potentialFlagValuation F hu) :=
  Classical.choose_spec (exists_originalPotentialFlagValuation n F θ u hu)

/-- The actual assignment depends only on original multiplier equivalence,
including changes of the genuine closed background. -/
theorem potentialFlagValuation_eq_of_iEquivalent {n : ℕ}
    (F : OriginalFlagGeometry.{u} n) {θ σ : ClosedRealOneOneForm n F.carrier}
    {u v : F.carrier → EReal}
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential σ.val v)
    (hI : IEquivalentOnManifold (n := n) u v) :
    potentialFlagValuation F hu = potentialFlagValuation F hv :=
  originalPotentialFlagValuation_eq_of_iEquivalent n F u v _ _
    (potentialFlagValuation_spec F hu) (potentialFlagValuation_spec F hv) hI

/-- The actual first value is the original finite generic coefficient;
the true extended reader is retained rather than projected from infinity. -/
theorem potentialFlagValuation_first {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1))
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {u : F.carrier → EReal}
    (hu : IsThetaPshPotential θ.val u) :
    (potentialFlagValuation F hu 0 : ℝ≥0∞) =
      sourceGenericLelongNumber (n := m + 1)
        (Subtype.val : F.flag (1 : Fin (m + 2)) → F.carrier) u := by
  have h := (potentialFlagValuation_spec F hu).1
  rw [h]
  exact ENNReal.coe_toNNReal (sourceGeneric_subtype_ne_top F.firstDivisor hu.quasiPshPotential)

/-- Every literal source trace choice gives exactly the same actual tail
valuation, in the genuine inherited manifold and original tail flag. -/
theorem potentialFlagValuation_tail_of_originalFlagStep {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1))
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {u : F.carrier → EReal}
    (hu : IsThetaPshPotential θ.val u)
    {τ : F.tail.carrier → EReal} (hT : OriginalFlagStep F u τ)
    {β : ClosedRealOneOneForm m F.tail.carrier} (hτ : IsThetaPshPotential β.val τ) :
    (fun i => potentialFlagValuation F hu i.succ) = potentialFlagValuation F.tail hτ := by
  obtain ⟨_hhead, τ₀, hT₀, htail⟩ := potentialFlagValuation_spec F hu
  have hI := originalFlagStep_iEquivalent_of_iEquivalent F
    (IEquivalentOnManifold.refl u) hT₀ hT
  exact originalPotentialFlagValuation_eq_of_iEquivalent m F.tail τ₀ τ _ _
    htail (potentialFlagValuation_spec F.tail hτ) hI

end SGPT.Okounkov
