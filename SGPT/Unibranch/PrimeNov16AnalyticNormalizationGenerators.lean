import SGPT.Unibranch.PrimeNov16AnalyticNormalizationDenominator
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationTransitions
import SGPT.Foundations.Analysis.Pending.AnalyticGermDecomposition

/-! Original irreducible analytic germ produces canonical finite normal-algebra
module generators, one actual denominator, numerators and monic equations.
No normalization/finite-map/coherence certificate is input.
Blueprint: prime-nov16-analytic-normalization-generators.tex. -/
set_option autoImplicit false
noncomputable section
open Polynomial
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.AnalyticGermDecomposition
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationGenerators

/-- Every ORIGINAL irreducible analytic germ internally produces all of the
canonical normal-algebra graph tuple data. Local branch scope, not a space. -/
theorem exists_original_germ_normal_generators {n : ℕ} {Z : Set (ComplexModel n)}
    (hZ : IsIrreducibleGerm Z) :
    let A := HolGerm (ComplexModel n) ⧸ vanishingIdeal Z
    let B := integralClosure A (FractionRing A)
    ∃ (N : ℕ) (s : Fin N → B) (h : A) (g : Fin N → A) (p : Fin N → A[X]),
      h ≠ 0 ∧ Submodule.span A (Set.range s) = ⊤ ∧
      ∀ i, algebraMap A (FractionRing A) (g i) =
          algebraMap A (FractionRing A) h * (s i : FractionRing A) ∧
        (p i).Monic ∧ aeval (s i : FractionRing A) (p i) = 0 := by
  let : (vanishingIdeal Z).IsPrime := (isIrreducibleGerm_iff_isPrime hZ.1).mp hZ
  let A := HolGerm (ComplexModel n) ⧸ vanishingIdeal Z
  let B := integralClosure A (FractionRing A)
  have : Module.Finite A B :=
    PrimeNov16AnalyticIntegralClosure.finite_analytic_germ_integralClosure (vanishingIdeal Z)
  obtain ⟨N,s,hs⟩ := Module.Finite.exists_fin (R := A) (M := B)
  obtain ⟨h,hh,hden⟩ :=
    PrimeNov16AnalyticNormalizationDenominator.exists_universal_denominator_of_finite_closure A
  choose g hg using fun i => hden (s i)
  choose p hpm hpeq using fun i => (s i).property
  exact ⟨N,s,h,g,p,hh,hs,fun i => ⟨hg i,hpm i,hpeq i⟩⟩

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationGenerators
