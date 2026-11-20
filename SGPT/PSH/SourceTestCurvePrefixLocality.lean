import SGPT.PSH.SourceTestCurvePrefixEnergy
import SGPT.Foundations.Analysis.Pending.GlobalDiagonalScaling

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas

open Set MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- Actual diagonal strict-maximum locality in every natural dimension. -/
theorem sourceDiagonalMeasure_restrict_max_eq {u v : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hv : (ofFixedModel n M).IsThetaPSH θ v)
    (hm : (ofFixedModel n M).IsThetaPSH θ (fun x ↦ max (u x) (v x))) :
    (sourcePotentialNonPluripolarMeasure θ (fun x ↦ max (u x) (v x)) hm).restrict
      {x | v x < u x} =
      (sourcePotentialNonPluripolarMeasure θ u hu).restrict {x | v x < u x} := by
  have hun := (isThetaPSH_iff_nativeThetaPotential θ u).mp hu
  have hvn := (isThetaPSH_iff_nativeThetaPotential θ v).mp hv
  have hmn := (isThetaPSH_iff_nativeThetaPotential θ _).mp hm
  change (DiagonalMass.diagonalPotentialMeasure (atlasClosedFormToNative θ)
    (fun x ↦ max (u x) (v x)) hmn).restrict _ =
    (DiagonalMass.diagonalPotentialMeasure (atlasClosedFormToNative θ) u hun).restrict _
  by_cases hn : n = 0
  · have heq : (fun _ : Fin n ↦ fun x ↦ max (u x) (v x)) =
        (fun _ : Fin n ↦ u) := by
      funext i
      exact (Nat.not_lt_zero i.1 (hn ▸ i.2)).elim
    exact congrArg (fun μ : Measure M ↦ μ.restrict {x | v x < u x})
      (GlobalDiagonalScaling.globalMixedMeasure_congr rfl heq
        (fun _ ↦ hmn.1) (fun _ ↦ hun.1))
  · have hpos : 0 < n := Nat.pos_of_ne_zero hn
    have hset : {x : M | ∀ _ : Fin n, v x < u x} = {x | v x < u x} := by
      ext x
      exact ⟨fun h ↦ h ⟨0, hpos⟩, fun h _ ↦ h⟩
    have hloc := GlobalMaxLocality.globalMixedMeasure_restrict_max_eq
      (θ := fun _ : Fin n ↦ atlasClosedFormToNative θ)
      (fun _ ↦ hun.1) (fun _ ↦ hvn.1) (fun _ ↦ hmn.1)
    simpa only [DiagonalMass.diagonalPotentialMeasure, hset] using hloc

/-- The same actual strict locality restricts further to any included set. -/
theorem sourceDiagonalMeasure_restrict_max_eq_on {u v : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hv : (ofFixedModel n M).IsThetaPSH θ v)
    (hm : (ofFixedModel n M).IsThetaPSH θ (fun x ↦ max (u x) (v x)))
    {A : Set M} (hA : A ⊆ {x | v x < u x}) :
    (sourcePotentialNonPluripolarMeasure θ (fun x ↦ max (u x) (v x)) hm).restrict A =
      (sourcePotentialNonPluripolarMeasure θ u hu).restrict A := by
  have h := congrArg (fun μ : Measure M ↦ μ.restrict A)
    (sourceDiagonalMeasure_restrict_max_eq hu hv hm)
  simpa only [Measure.restrict_restrict_of_subset hA] using h

end SGPT.PSH.VariableComplexAtlas
