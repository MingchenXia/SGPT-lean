import SGPT.Okounkov.SourceTestCurveAllDimensions
import SGPT.Okounkov.ValuativeFirstCoordinate

/-! The actual n=1 source trace-slice branch for whole lma:slicepob.
The target is the genuine checked zero-dimensional source body, including
its original approximation/perturbation intersections, not a substitute singleton. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.Okounkov.Valuative
open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov.PartialBody SGPT.Okounkov.TranscendentalCore

variable (F : OriginalFlagGeometry 1)

/-- The exact original first-coordinate-zero slice in dimension one equals
the actual source body on the original zero-dimensional tail. Every actual
psh trace representative in its original restricted class is covered. -/
theorem slice_zero_generalBody_eq_of_dim_one
    {θ : ClosedRealOneOneForm 1 F.carrier} {φ : F.carrier → EReal}
    (hφ : IsThetaPshPotential θ.val φ) (hzero : flagValuation F φ 0 = 0)
    {ψ : F.tail.carrier → EReal}
    (hψ : IsThetaPshPotential (TranscendentalMain.firstFlagRestriction F θ).val ψ) :
    TranscendentalMain.firstCoordinateSlice (generalPartialBody F θ φ) 0 =
      SourceTestCurveAllDimensions.generalBody F.tail
        (TranscendentalMain.firstFlagRestriction F θ) ⟨ψ, hψ⟩ := by
  change TranscendentalMain.firstCoordinateSlice (generalPartialBody F θ φ) 0 =
    ZeroSource.generalBody F.tail (TranscendentalMain.firstFlagRestriction F θ) ψ hψ
  rw [ZeroSource.generalBody_eq_partial, ZeroSource.partialOkounkovBody_eq_univ F.tail hψ]
  apply eq_univ_of_forall
  intro y
  obtain ⟨p, hp, hp0⟩ := exists_mem_generalPartialBody_zero_eq (F := F) hφ
  have hp0' : p 0 = 0 := hp0.trans hzero
  have heq : p = Fin.cons 0 y := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.elim0 j) i
    simpa only [Fin.cons_zero] using hp0'
  change Fin.cons 0 y ∈ generalPartialBody F θ φ
  simpa only [heq] using hp
end SGPT.Okounkov.Valuative
