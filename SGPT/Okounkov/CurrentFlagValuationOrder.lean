import SGPT.Okounkov.CurrentFlagValuation
import SGPT.Okounkov.PotentialFlagValuationOrder

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Okounkov

open Set Filter
open scoped Manifold ContDiff NNReal ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Foundations.Analysis.Pending
open GlobalCurrents CanonicalCurrentFrame NaturalThetaPshGeometricCurrent
open GlobalPositiveCurrentACRestriction

/-- Original current multiplier order follows the actual source convention:
genuine global potentials of the actual whole currents have multiplier order. -/
def OriginalCurrentsIOrder {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))
    (T S : GlobalCurrent (m + 1) F.carrier (degreeTwo (Nat.succ_pos m))) : Prop :=
  ∃ (θ σ : ClosedRealOneOneForm (m + 1) F.carrier)
    (u v : F.carrier → EReal)
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential σ.val v),
    T = thetaPotentialCurrent θ.val u hu ∧
    S = thetaPotentialCurrent σ.val v hv ∧ IOrderOnManifold (n := m + 1) u v

/-- True same-current multiplier invariance makes original current order
independent of every genuine global representation and closed background. -/
theorem originalCurrentsIOrder_iff_of_theta_representations {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1))
    {T S : GlobalCurrent (m + 1) F.carrier (degreeTwo (Nat.succ_pos m))}
    {θ σ : ClosedRealOneOneForm (m + 1) F.carrier} {u v : F.carrier → EReal}
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential σ.val v)
    (hT : T = thetaPotentialCurrent θ.val u hu)
    (hS : S = thetaPotentialCurrent σ.val v hv) :
    OriginalCurrentsIOrder F T S ↔ IOrderOnManifold (n := m + 1) u v := by
  constructor
  · rintro ⟨θ₀, σ₀, u₀, v₀, hu₀, hv₀, hT₀, hS₀, hI₀⟩
    let : MeasurableSpace F.carrier := borel F.carrier
    let : BorelSpace F.carrier := ⟨rfl⟩
    have hleft := iEquivalent_of_thetaPotentialCurrent_eq F.omega hu hu₀ (hT.symm.trans hT₀)
    have hright := iEquivalent_of_thetaPotentialCurrent_eq F.omega hv₀ hv (hS₀.symm.trans hS)
    exact hleft.1.trans (hI₀.trans hright.1)
  · exact fun hI => ⟨θ, σ, u, v, hu, hv, hT, hS, hI⟩

/-- Literal first clause of original prop:nuvaluationlinear for actual
closed fully positive currents: source ideal order yields TRUE lex order. -/
theorem currentFlagValuation_lex_le_of_iOrder {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1))
    (T S : GlobalCurrent (m + 1) F.carrier (degreeTwo (Nat.succ_pos m)))
    (hTc : T.IsClosed (canonicalBasis (m + 1)))
    (hT11 : T.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m)) (hT : IsFullPositive T)
    (hSc : S.IsClosed (canonicalBasis (m + 1)))
    (hS11 : S.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m)) (hS : IsFullPositive S)
    (hI : OriginalCurrentsIOrder F T S) :
    toLex (currentFlagValuation F S hSc hS11 hS) ≤
      toLex (currentFlagValuation F T hTc hT11 hT) := by
  obtain ⟨θ, σ, u, v, hu, hv, hreadT, hreadS, hI⟩ := hI
  rw [currentFlagValuation_eq_potentialFlagValuation F S hSc hS11 hS hv hreadS,
    currentFlagValuation_eq_potentialFlagValuation F T hTc hT11 hT hu hreadT]
  exact potentialFlagValuation_lex_le_of_iOrder F hu hv hI

end SGPT.Okounkov
