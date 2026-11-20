import SGPT.Okounkov.PotentialFlagValuationIndependence
import SGPT.Okounkov.OriginalCurrentResidualTrace
import SGPT.Okounkov.ThetaPotentialCurrentSingularity
import SGPT.Okounkov.UnitDivisorCurrent

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov

open Set Filter
open scoped Manifold ContDiff NNReal ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open ThetaPshCodimTwoExtension NaturalSubmanifoldSourceTraceDefinition
open GlobalCurrents CanonicalCurrentFrame NaturalThetaPshGeometricCurrent
open GlobalPositiveCurrentACRestriction SourceTraceRepresentativeDefinition
open SquaredLogLelongSourceNormalization

/-- Every actual recorded source step is a trace of the literal WHOLE
unit residual current. Its residual positivity is produced from the
original potential and the genuine unit metric, rather than assumed. -/
theorem exists_originalFlagStep_unit_current {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1))
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {u : F.carrier → EReal}
    (hu : IsThetaPshPotential θ.val u)
    {τ : F.tail.carrier → EReal} (hstep : OriginalFlagStep F u τ) :
    let W := F.flag (1 : Fin (m + 2))
    let c := (sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → F.carrier) u).toNNReal
    ∃ D : EffectiveDivisor (m + 1) F.carrier, D.ideal = vanishingIdeal (n := m + 1) W ∧
      ∃ E : MeteredEffectiveQDivisor (m + 1) F.carrier, E.support = W ∧
        DivisorMetric.IsDivisorMetric D E ∧
      ∃ hv : IsThetaPshPotential (θ - (c : ℝ) • E.curvature).val
          (extensionAcross W (smoothDivisorOffResidual E c u)),
        thetaPotentialCurrent (θ - (c : ℝ) • E.curvature).val
          (extensionAcross W (smoothDivisorOffResidual E c u)) hv =
            thetaPotentialCurrent θ.val u hu - (c : ℝ) • smoothDivisorIntegrationCurrent F.firstDivisor ∧
        IsNaturalSourceTraceRepresentative F.omega F.firstDivisor
          (extensionAcross W (smoothDivisorOffResidual E c u)) τ := by
  obtain ⟨_θ, _hu, D, hDI, E, hEW, hmetric, htrace⟩ := hstep
  have hv := isThetaPshPotential_smooth_divisor_residual_of_unit_metric
    hu F.firstDivisor D hDI E hEW hmetric
  exact ⟨D, hDI, E, hEW, hmetric, hv,
    smooth_divisor_residual_current_eq_unit_current hu F.firstDivisor D hDI E hEW hmetric _ hv,
    htrace⟩

/-- Original current multiplier equivalence follows the source convention
rmk:qpshtocurrents: genuine global potential representations have equivalent
actual multiplier ideals. Same-current invariance removes their choices. -/
def OriginalCurrentsIEquivalent {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))
    (T S : GlobalCurrent (m + 1) F.carrier (degreeTwo (Nat.succ_pos m))) : Prop :=
  ∃ (θ σ : ClosedRealOneOneForm (m + 1) F.carrier)
    (u v : F.carrier → EReal)
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential σ.val v),
    T = thetaPotentialCurrent θ.val u hu ∧
    S = thetaPotentialCurrent σ.val v hv ∧ IEquivalentOnManifold (n := m + 1) u v

/-- The original convention is independent of ALL genuine global
representations, through actual same-current multiplier invariance. -/
theorem originalCurrentsIEquivalent_iff_of_theta_representations {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1))
    {T S : GlobalCurrent (m + 1) F.carrier (degreeTwo (Nat.succ_pos m))}
    {θ σ : ClosedRealOneOneForm (m + 1) F.carrier} {u v : F.carrier → EReal}
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential σ.val v)
    (hT : T = thetaPotentialCurrent θ.val u hu)
    (hS : S = thetaPotentialCurrent σ.val v hv) :
    OriginalCurrentsIEquivalent F T S ↔ IEquivalentOnManifold (n := m + 1) u v := by
  constructor
  · rintro ⟨θ₀, σ₀, u₀, v₀, hu₀, hv₀, hT₀, hS₀, hI₀⟩
    let : MeasurableSpace F.carrier := borel F.carrier
    let : BorelSpace F.carrier := ⟨rfl⟩
    have hleft := iEquivalent_of_thetaPotentialCurrent_eq F.omega hu hu₀ (hT.symm.trans hT₀)
    have hright := iEquivalent_of_thetaPotentialCurrent_eq F.omega hv₀ hv (hS₀.symm.trans hS)
    exact hleft.trans (hI₀.trans hright)
  · exact fun hI => ⟨θ, σ, u, v, hu, hv, hT, hS, hI⟩

/-- The actual whole-current source recursion retains every genuine global
potential representation and every original residual/plain-trace choice. -/
def OriginalCurrentFlagValuationRelation {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1))
    (T : GlobalCurrent (m + 1) F.carrier (degreeTwo (Nat.succ_pos m)))
    (ν : Fin (m + 1) → ℝ≥0) : Prop :=
  ∃ (θ : ClosedRealOneOneForm (m + 1) F.carrier) (u : F.carrier → EReal)
    (hu : IsThetaPshPotential θ.val u),
    T = thetaPotentialCurrent θ.val u hu ∧ OriginalPotentialFlagValuation (m + 1) F u ν

/-- Original current ideal equivalence gives equality of every actual
recursively produced value, including all potential and trace choices. -/
theorem originalCurrentFlagValuation_eq_of_iEquivalent {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1))
    {T S : GlobalCurrent (m + 1) F.carrier (degreeTwo (Nat.succ_pos m))}
    (hI : OriginalCurrentsIEquivalent F T S)
    {ν μ : Fin (m + 1) → ℝ≥0}
    (hν : OriginalCurrentFlagValuationRelation F T ν)
    (hμ : OriginalCurrentFlagValuationRelation F S μ) : ν = μ := by
  obtain ⟨θ, u, hu, hT, hν⟩ := hν
  obtain ⟨σ, v, hv, hS, hμ⟩ := hμ
  exact originalPotentialFlagValuation_eq_of_iEquivalent (m + 1) F u v ν μ hν hμ
    ((originalCurrentsIEquivalent_iff_of_theta_representations F hu hv hT hS).mp hI)

/-- Every original closed fully positive current internally supplies the
global potential representation and the unique actual finite valuation. -/
theorem existsUnique_originalCurrentFlagValuation {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1))
    (T : GlobalCurrent (m + 1) F.carrier (degreeTwo (Nat.succ_pos m)))
    (hclosed : T.IsClosed (canonicalBasis (m + 1)))
    (h11 : T.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hT : IsFullPositive T) :
    ∃! ν : Fin (m + 1) → ℝ≥0, OriginalCurrentFlagValuationRelation F T ν := by
  obtain ⟨θ, u, hu, hread, _hchart⟩ :=
    OriginalPositiveCurrentThetaRepresentation.exists_theta_representation_of_original_closed_full_positive
      T hclosed h11 hT
  obtain ⟨ν, hν⟩ := exists_originalPotentialFlagValuation (m + 1) F θ u hu
  have hI : OriginalCurrentsIEquivalent F T T :=
    ⟨θ, θ, u, u, hu, hu, hread, hread, IEquivalentOnManifold.refl u⟩
  exact ⟨ν, ⟨θ, u, hu, hread, hν⟩, fun μ hμ =>
    originalCurrentFlagValuation_eq_of_iEquivalent F hI hμ ⟨θ, u, hu, hread, hν⟩⟩

/-- Literal original current valuation obtained from genuine source existence. -/
def currentFlagValuation {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))
    (T : GlobalCurrent (m + 1) F.carrier (degreeTwo (Nat.succ_pos m)))
    (hclosed : T.IsClosed (canonicalBasis (m + 1)))
    (h11 : T.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hT : IsFullPositive T) : Fin (m + 1) → ℝ≥0 :=
  Classical.choose (existsUnique_originalCurrentFlagValuation F T hclosed h11 hT)

theorem currentFlagValuation_spec {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))
    (T : GlobalCurrent (m + 1) F.carrier (degreeTwo (Nat.succ_pos m)))
    (hclosed : T.IsClosed (canonicalBasis (m + 1)))
    (h11 : T.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hT : IsFullPositive T) :
    OriginalCurrentFlagValuationRelation F T (currentFlagValuation F T hclosed h11 hT) :=
  (Classical.choose_spec (existsUnique_originalCurrentFlagValuation F T hclosed h11 hT)).1

/-- Actual whole-current valuation is the original potential recursion for
EVERY genuine global potential representation of the same original current. -/
theorem currentFlagValuation_eq_potentialFlagValuation {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1))
    (T : GlobalCurrent (m + 1) F.carrier (degreeTwo (Nat.succ_pos m)))
    (hclosed : T.IsClosed (canonicalBasis (m + 1)))
    (h11 : T.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m)) (hT : IsFullPositive T)
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {u : F.carrier → EReal}
    (hu : IsThetaPshPotential θ.val u) (hread : T = thetaPotentialCurrent θ.val u hu) :
    currentFlagValuation F T hclosed h11 hT = potentialFlagValuation F hu := by
  have hI : OriginalCurrentsIEquivalent F T T :=
    ⟨θ, θ, u, u, hu, hu, hread, hread, IEquivalentOnManifold.refl u⟩
  exact originalCurrentFlagValuation_eq_of_iEquivalent F hI
    (currentFlagValuation_spec F T hclosed h11 hT)
    ⟨θ, u, hu, hread, potentialFlagValuation_spec F hu⟩

/-- Exact original prop:valcurr_Iind on actual whole currents: all trace
and representation choices give the same assignment for I-equivalent inputs. -/
theorem currentFlagValuation_eq_of_iEquivalent {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1))
    (T S : GlobalCurrent (m + 1) F.carrier (degreeTwo (Nat.succ_pos m)))
    (hTc : T.IsClosed (canonicalBasis (m + 1)))
    (hT11 : T.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m)) (hT : IsFullPositive T)
    (hSc : S.IsClosed (canonicalBasis (m + 1)))
    (hS11 : S.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m)) (hS : IsFullPositive S)
    (hI : OriginalCurrentsIEquivalent F T S) :
    currentFlagValuation F T hTc hT11 hT = currentFlagValuation F S hSc hS11 hS :=
  originalCurrentFlagValuation_eq_of_iEquivalent F hI
    (currentFlagValuation_spec F T hTc hT11 hT)
    (currentFlagValuation_spec F S hSc hS11 hS)

/-- The literal first coefficient is the actual whole-divisor infimum of
the canonical ORIGINAL current reader, with no infinity projection. -/
theorem currentFlagValuation_first_of_source_reader {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1))
    (T : GlobalCurrent (m + 1) F.carrier (degreeTwo (Nat.succ_pos m)))
    (hclosed : T.IsClosed (canonicalBasis (m + 1)))
    (h11 : T.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m)) (hT : IsFullPositive T)
    {μ : F.carrier → ℝ≥0∞} (hμ : IsOriginalCurrentSourceReader T μ) :
    (currentFlagValuation F T hclosed h11 hT 0 : ℝ≥0∞) =
      ⨅ y : F.flag (1 : Fin (m + 2)), μ y := by
  obtain ⟨θ, u, hu, hread, hν⟩ := currentFlagValuation_spec F T hclosed h11 hT
  have hhead := hν.1
  rw [hhead, ENNReal.coe_toNNReal
    (sourceGeneric_subtype_ne_top F.firstDivisor hu.quasiPshPotential)]
  have hμθ := original_current_source_reader_eq_theta_potential hu (hread ▸ hμ)
  unfold sourceGenericLelongNumber
  exact iInf_congr fun y => (congrFun hμθ y).symm

/-- Original current data internally produce their canonical point reader
and the literal finite first-divisor coefficient of the assignment. -/
theorem exists_source_reader_currentFlagValuation_first {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1))
    (T : GlobalCurrent (m + 1) F.carrier (degreeTwo (Nat.succ_pos m)))
    (hclosed : T.IsClosed (canonicalBasis (m + 1)))
    (h11 : T.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m)) (hT : IsFullPositive T) :
    ∃ μ : F.carrier → ℝ≥0∞, IsOriginalCurrentSourceReader T μ ∧
      (currentFlagValuation F T hclosed h11 hT 0 : ℝ≥0∞) =
        ⨅ y : F.flag (1 : Fin (m + 2)), μ y := by
  obtain ⟨μ, hμ, _hinv⟩ :=
    exists_original_full_positive_current_theta_invariant_source_reader T hclosed h11 hT
  exact ⟨μ, hμ, currentFlagValuation_first_of_source_reader F T hclosed h11 hT hμ⟩

/-- For a genuine positive-dimensional tail, the assignment obeys the
literal source current recursion for EVERY actual plain trace choice.
Its positive current is formed in its genuinely produced admissible β;
the original restricted θ is not asserted positive. -/
theorem currentFlagValuation_tail_of_originalFlagStep {q : ℕ}
    (F : OriginalFlagGeometry.{u} (q + 2))
    (T : GlobalCurrent (q + 2) F.carrier (degreeTwo (Nat.succ_pos (q + 1))))
    (hclosed : T.IsClosed (canonicalBasis (q + 2)))
    (h11 : T.IsTypeOneOne (canonicalBasis (q + 2)) (Nat.succ_pos (q + 1))) (hT : IsFullPositive T)
    {θ : ClosedRealOneOneForm (q + 2) F.carrier} {u : F.carrier → EReal}
    (hu : IsThetaPshPotential θ.val u) (hread : T = thetaPotentialCurrent θ.val u hu)
    {τ : F.tail.carrier → EReal} (htrace : OriginalFlagStep F u τ)
    {β : ClosedRealOneOneForm (q + 1) F.tail.carrier} (hτ : IsThetaPshPotential β.val τ) :
    let htarget := NaturalThetaPshClosedCurrent.thetaPotentialCurrent_closed_type_positive β.val τ hτ
    (fun i => currentFlagValuation F T hclosed h11 hT i.succ) =
      currentFlagValuation F.tail (thetaPotentialCurrent β.val τ hτ)
        htarget.1 htarget.2.1 htarget.2.2 := by
  dsimp only
  let htarget := NaturalThetaPshClosedCurrent.thetaPotentialCurrent_closed_type_positive β.val τ hτ
  calc
    (fun i => currentFlagValuation F T hclosed h11 hT i.succ) =
        (fun i => potentialFlagValuation F hu i.succ) :=
      congrArg (fun v : Fin (q + 2) → ℝ≥0 => fun i : Fin (q + 1) => v i.succ)
        (currentFlagValuation_eq_potentialFlagValuation F T hclosed h11 hT hu hread)
    _ = potentialFlagValuation F.tail hτ :=
      potentialFlagValuation_tail_of_originalFlagStep F hu htrace hτ
    _ = currentFlagValuation F.tail (thetaPotentialCurrent β.val τ hτ)
        htarget.1 htarget.2.1 htarget.2.2 :=
      (currentFlagValuation_eq_potentialFlagValuation F.tail (thetaPotentialCurrent β.val τ hτ)
        htarget.1 htarget.2.1 htarget.2.2 hτ rfl).symm

/-- Original current data produce an actual target and its literal tail
recursion. The recorded step is already proved to be a plain trace of
the WHOLE residual T-c[Y₁], and the target uses its actual admissible β. -/
theorem exists_currentFlagValuation_tail {q : ℕ}
    (F : OriginalFlagGeometry.{u} (q + 2))
    (T : GlobalCurrent (q + 2) F.carrier (degreeTwo (Nat.succ_pos (q + 1))))
    (hclosed : T.IsClosed (canonicalBasis (q + 2)))
    (h11 : T.IsTypeOneOne (canonicalBasis (q + 2)) (Nat.succ_pos (q + 1))) (hT : IsFullPositive T) :
    ∃ (θ : ClosedRealOneOneForm (q + 2) F.carrier) (u : F.carrier → EReal)
      (hu : IsThetaPshPotential θ.val u), T = thetaPotentialCurrent θ.val u hu ∧
      ∃ τ : F.tail.carrier → EReal, OriginalFlagStep F u τ ∧
        ∃ (β : ClosedRealOneOneForm (q + 1) F.tail.carrier) (hτ : IsThetaPshPotential β.val τ),
          let htarget := NaturalThetaPshClosedCurrent.thetaPotentialCurrent_closed_type_positive β.val τ hτ
          (fun i => currentFlagValuation F T hclosed h11 hT i.succ) =
            currentFlagValuation F.tail (thetaPotentialCurrent β.val τ hτ)
              htarget.1 htarget.2.1 htarget.2.2 := by
  obtain ⟨θ, u, hu, hread, _hν⟩ := currentFlagValuation_spec F T hclosed h11 hT
  obtain ⟨τ, hstep, β, hτ⟩ := exists_originalFlagStep_and_target_potential F hu
  exact ⟨θ, u, hu, hread, τ, hstep, β, hτ,
    currentFlagValuation_tail_of_originalFlagStep F T hclosed h11 hT hu hread hstep hτ⟩

/-- The zero-dimensional source case is genuinely the unique Fin 0 vector,
independently of any representation of its input current. -/
def zeroDimensionCurrentFlagValuation {C : Type u} (_T : C) : Fin 0 → ℝ≥0 := Fin.elim0

theorem zeroDimensionCurrentFlagValuation_unique {C : Type u} (T : C) (ν : Fin 0 → ℝ≥0) :
    ν = zeroDimensionCurrentFlagValuation T := by
  funext i
  exact Fin.elim0 i

/-- The original dimension-one tail is the genuine unique zero vector for
any actual chosen target representation of its plain source trace. -/
theorem currentFlagValuation_zeroDimension_tail
    (F : OriginalFlagGeometry.{u} 1)
    (T : GlobalCurrent 1 F.carrier (degreeTwo (Nat.succ_pos 0)))
    (hclosed : T.IsClosed (canonicalBasis 1))
    (h11 : T.IsTypeOneOne (canonicalBasis 1) (Nat.succ_pos 0)) (hT : IsFullPositive T)
    {C : Type u} (target : C) :
    (fun i : Fin 0 => currentFlagValuation F T hclosed h11 hT i.succ) =
      zeroDimensionCurrentFlagValuation target :=
  zeroDimensionCurrentFlagValuation_unique target _

end SGPT.Okounkov
