import SGPT.Okounkov.TranscendentalCoreDefs
import SGPT.Okounkov.PotentialFlagValuationAdd
import SGPT.Okounkov.PotentialFlagValuationZero
import SGPT.Okounkov.PotentialFlagValuationScaling
import SGPT.Okounkov.TranscendentalCoreAlgebra
import SGPT.Foundations.Analysis.Pending.IEnvelopeOrder
import SGPT.Foundations.Analysis.Pending.RelativePreceqClasses

/-!
# Valuations of currents with bounded potentials

Source: blueprint node `tok:valuation-divisor` (used in DRWNXZ Example 5.3 and Lemma 5.5): if `R`
is a closed positive `(1,1)`-current with locally bounded potentials, then `ν(R) = 0`; if `D` is
an effective `ℚ`-divisor, then `ν([D] + R) = ν([D])`.

A bounded potential `ψ` is multiplier-ideal equivalent to `0` (all multiplier ideals are trivial),
and the valuation only depends on the multiplier-ideal class, so `ν(ψ) = ν(0) = 0`; by
additivity of the valuation, `ν(T + R) = ν(T) + ν(R) = ν(T)` for every closed positive current
`T` (in particular for `T = [D]`).

## Main results

* `flagValuation_eq_zero_of_bounded`, `flagValuation_eq_zero_of_locallyBounded`: `ν(R) = 0`.
* `flagValuation_add_of_bounded`, `flagValuation_add_of_locallyBounded`: `ν(T + R) = ν(T)`.
* `flagValuation_add_smul`: `ν(aT + bS) = a ν(T) + b ν(S)` for `a, b ≥ 0` (additivity and
  positive homogeneity of the valuation, `okflag:actual-original-potential-valuation-addition`).
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalCore

open Set Filter
open scoped Topology NNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.IEnvelope

variable {n : ℕ} {F : OriginalFlagGeometry.{u} n}

/-- On a compact manifold a locally bounded below function is bounded below. -/
theorem exists_lower_bound_of_locallyBounded {ψ : F.carrier → EReal}
    (hloc : ∀ x, ∃ U ∈ 𝓝 x, ∃ C : ℝ, ∀ y ∈ U, (C : EReal) ≤ ψ y) :
    ∃ C : ℝ, ∀ x, (C : EReal) ≤ ψ x := by
  choose U hU C hC using hloc
  obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover U (fun x _ => hU x)
  refine ⟨-∑ x ∈ t, |C x|, fun y => ?_⟩
  obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.mp (ht (mem_univ y))
  refine le_trans (EReal.coe_le_coe_iff.mpr ?_) (hC x y hyx)
  have h1 : |C x| ≤ ∑ x ∈ t, |C x| :=
    Finset.single_le_sum (f := fun x => |C x|) (fun _ _ => abs_nonneg _) hxt
  linarith [neg_abs_le (C x)]

/-- **`ν(R) = 0` for a bounded potential** (blueprint `tok:valuation-divisor`): a `θ`-psh
potential bounded below has valuation zero. -/
theorem flagValuation_eq_zero_of_bounded {θ : ClosedRealOneOneForm n F.carrier}
    {ψ : F.carrier → EReal} (hψ : IsThetaPshPotential θ.val ψ) {C : ℝ}
    (hC : ∀ x, (C : EReal) ≤ ψ x) : flagValuation F ψ = 0 := by
  obtain ⟨hzero, hν⟩ := exists_potentialFlagValuation_zero F
  obtain ⟨m, hm⟩ := Pending.RelativePreceqClasses.exists_le_coe_of_isThetaPshPotential hψ
  have hI : IEquivalentOnManifold (n := n) ψ (fun _ : F.carrier => (0 : EReal)) := by
    constructor
    · exact Pending.iOrderOnManifold_of_le_add hzero.quasiPshPotential.1 (C := m)
        fun x => by simpa using hm x
    · refine Pending.iOrderOnManifold_of_le_add hψ.quasiPshPotential.1 (C := -C) fun x => ?_
      calc (0 : EReal) = (C : EReal) + ((-C : ℝ) : EReal) := by
            rw [← EReal.coe_add, add_neg_cancel, EReal.coe_zero]
        _ ≤ ψ x + ((-C : ℝ) : EReal) := add_le_add (hC x) le_rfl
  rw [flagValuation_eq_of_iEquivalent hψ hzero hI, flagValuation_eq hzero, hν]
  rfl

/-- **`ν(R) = 0` for a current with locally bounded potentials** (blueprint
`tok:valuation-divisor`). -/
theorem flagValuation_eq_zero_of_locallyBounded {θ : ClosedRealOneOneForm n F.carrier}
    {ψ : F.carrier → EReal} (hψ : IsThetaPshPotential θ.val ψ)
    (hloc : ∀ x, ∃ U ∈ 𝓝 x, ∃ C : ℝ, ∀ y ∈ U, (C : EReal) ≤ ψ y) :
    flagValuation F ψ = 0 := by
  obtain ⟨C, hC⟩ := exists_lower_bound_of_locallyBounded hloc
  exact flagValuation_eq_zero_of_bounded hψ hC

/-- **`ν(T + R) = ν(T)` for `R` with bounded potentials** (blueprint `tok:valuation-divisor`,
`ν([D] + R) = ν([D])` for every closed positive current `T`, in particular `T = [D]`). -/
theorem flagValuation_add_of_bounded {θ σ : ClosedRealOneOneForm n F.carrier}
    {φ ψ : F.carrier → EReal} (hφ : IsThetaPshPotential θ.val φ)
    (hψ : IsThetaPshPotential σ.val ψ) {C : ℝ} (hC : ∀ x, (C : EReal) ≤ ψ x) :
    flagValuation F (fun x => φ x + ψ x) = flagValuation F φ := by
  have h0 := flagValuation_eq_zero_of_bounded hψ hC
  rw [flagValuation_eq (isThetaPshPotential_add_from_positive_sum hφ hψ),
    potentialFlagValuation_add F hφ hψ, flagValuation_eq hφ]
  rw [flagValuation_eq hψ] at h0
  funext i
  have hi := congrFun h0 i
  simp only [Pi.zero_apply] at hi
  simp only [Pi.add_apply, NNReal.coe_add, hi, add_zero]

/-- `ν(T + R) = ν(T)` for `R` with locally bounded potentials. -/
theorem flagValuation_add_of_locallyBounded {θ σ : ClosedRealOneOneForm n F.carrier}
    {φ ψ : F.carrier → EReal} (hφ : IsThetaPshPotential θ.val φ)
    (hψ : IsThetaPshPotential σ.val ψ)
    (hloc : ∀ x, ∃ U ∈ 𝓝 x, ∃ C : ℝ, ∀ y ∈ U, (C : EReal) ≤ ψ y) :
    flagValuation F (fun x => φ x + ψ x) = flagValuation F φ := by
  obtain ⟨C, hC⟩ := exists_lower_bound_of_locallyBounded hloc
  exact flagValuation_add_of_bounded hφ hψ hC

/-- **Linearity of the valuation** on nonnegative combinations: `ν(aT + bS) = a ν(T) + b ν(S)`
for `a, b ≥ 0`. -/
theorem flagValuation_add_smul {θ σ : ClosedRealOneOneForm n F.carrier}
    {φ ψ : F.carrier → EReal} (hφ : IsThetaPshPotential θ.val φ)
    (hψ : IsThetaPshPotential σ.val ψ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    flagValuation F (fun x => (a : EReal) * φ x + (b : EReal) * ψ x) =
      a • flagValuation F φ + b • flagValuation F ψ := by
  obtain ⟨hφa, hνa⟩ := exists_potentialFlagValuation_nonneg_smul F hφ ⟨a, ha⟩
  obtain ⟨hψb, hνb⟩ := exists_potentialFlagValuation_nonneg_smul F hψ ⟨b, hb⟩
  have hsum : IsThetaPshPotential (a • θ + b • σ).val
      (fun x => (a : EReal) * φ x + (b : EReal) * ψ x) :=
    isThetaPshPotential_add_from_positive_sum hφa hψb
  have hadd : potentialFlagValuation F hsum =
      potentialFlagValuation F hφa + potentialFlagValuation F hψb :=
    potentialFlagValuation_add F hφa hψb
  rw [flagValuation_eq hsum, hadd, hνa, hνb, flagValuation_eq hφ, flagValuation_eq hψ]
  funext i
  rfl

/-- `ν(aT) = a ν(T)` for `a ≥ 0`. -/
theorem flagValuation_smul {θ : ClosedRealOneOneForm n F.carrier} {φ : F.carrier → EReal}
    (hφ : IsThetaPshPotential θ.val φ) {a : ℝ} (ha : 0 ≤ a) :
    flagValuation F (fun x => (a : EReal) * φ x) = a • flagValuation F φ := by
  obtain ⟨hφa, hνa⟩ := exists_potentialFlagValuation_nonneg_smul F hφ ⟨a, ha⟩
  have hφa' : IsThetaPshPotential (a • θ).val (fun x => (a : EReal) * φ x) := hφa
  have hν : potentialFlagValuation F hφa' = potentialFlagValuation F hφa := rfl
  rw [flagValuation_eq hφa', hν, hνa, flagValuation_eq hφ]
  funext i
  rfl

end SGPT.Okounkov.TranscendentalCore
