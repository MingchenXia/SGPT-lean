import SGPT.Bergman.SiuNSFinitePotential
import SGPT.Projective.NumEqHodgeIndex

/-! The actual original real divisor span gives the finite divisor
expansion of the original Hodge quadratic intersection by global Stokes. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.Projective.NumEq
open Set
open scoped BigOperators
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.NefMixedMass
open SGPT.Hodge.BDivChain.SourceMixedOrderDraft SGPT.BDivisor.NSKodaira

variable {m : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 2)) X] [IsComplexManifold (m + 2) X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Actual slot linearity expands every finite real weighted sum in the
second original Hodge slot; no integral formula is supplied as an input. -/
theorem slotIntegral_secondSlot_sum
    (κ : KahlerBackground (m + 2) X) (alpha : ClosedRealOneOneForm (m + 2) X)
    {N : ℕ} (a : Fin N → ℝ) (E : Fin N → ClosedRealOneOneForm (m + 2) X) :
    slotIntegral κ (Function.update (oneSlot κ alpha) 1 (∑ i, a i • E i)) =
      ∑ i, a i * slotIntegral κ (Function.update (oneSlot κ alpha) 1 (E i)) := by
  classical
  let F : ClosedRealOneOneForm (m + 2) X →ₗ[ℝ] ℝ :=
    { toFun := fun beta => slotIntegral κ (Function.update (oneSlot κ alpha) 1 beta)
      map_add' := slotIntegral_update_add κ (oneSlot κ alpha) 1
      map_smul' := fun c beta => slotIntegral_update_smul κ (oneSlot κ alpha) 1 c beta }
  change F (∑ i, a i • E i) = ∑ i, a i * F (E i)
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]

/-- Membership in the ORIGINAL Néron--Severi span manufactures actual
Cartier divisors, actual metrics, and the exact finite quadratic formula.
Its only class hypothesis is membership in the existing original span. -/
theorem exists_finite_divisor_twoSlot_formula
    (κ : KahlerBackground (m + 2) X) (alpha : ClosedRealOneOneForm (m + 2) X)
    (hNS : RealBottChern.ofRepresentative alpha ∈ SGPT.BDivisor.DFAlg.neronSeveri (m + 2) X) :
    ∃ (N : ℕ) (D : Fin N → EffectiveDivisor (m + 2) X)
      (E : Fin N → MeteredEffectiveQDivisor (m + 2) X) (a : Fin N → ℝ),
      (∀ i, DivisorMetric.IsDivisorMetric (D i) (E i)) ∧
      slotIntegral κ (twoSlot κ alpha) =
        ∑ i, a i * slotIntegral κ (Function.update (oneSlot κ alpha) 1 (E i).curvature) := by
  classical
  obtain ⟨N, D, E, a, hE, f, hf, hcoef⟩ := exists_finite_divisor_potential alpha hNS
  have hrel : ClosedRealOneOneForm.BottChernRel (∑ i, a i • (E i).curvature) alpha :=
    ⟨f, hf, hcoef⟩
  have hslots : ∀ i, ClosedRealOneOneForm.BottChernRel (twoSlot κ alpha i)
      (Function.update (oneSlot κ alpha) 1 (∑ j, a j • (E j).curvature) i) := by
    intro i
    by_cases hi : i = 1
    · subst hi
      simpa only [twoSlot, oneSlot, Function.update_self] using hrel.symm
    · simpa only [twoSlot, oneSlot, Function.update_of_ne hi] using
        ClosedRealOneOneForm.BottChernRel.refl (oneSlot κ alpha i)
  refine ⟨N, D, E, a, hE, ?_⟩
  exact (slotIntegral_eq_of_bottChernRel κ _ _ hslots).trans
    (slotIntegral_secondSlot_sum κ alpha a (fun i => (E i).curvature))

end SGPT.Projective.NumEq
