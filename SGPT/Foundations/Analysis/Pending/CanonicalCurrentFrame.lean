import SGPT.Foundations.Analysis.Pending.TopDegreeDensity
import SGPT.Foundations.Analysis.Pending.KahlerLaplacianChart
import SGPT.Foundations.Analysis.Pending.GlobalCurrents
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

set_option autoImplicit false

/-! # The canonical complex-oriented frame and its actual Haar volume -/

noncomputable section

open MeasureTheory

namespace SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame

open FirstPass FirstPass.MongeAmpere TopDegreeDensity KahlerLaplacianChart

/-- The interleaved complex-positive frame, with the geometric current index type. -/
def canonicalBasis (n : ℕ) :
    Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n) :=
  (topBasis n).reindex (finCongr (complexModel_real_finrank n).symm)

private theorem coordinateRealBasis_eq_realBasis (n : ℕ) :
    coordinateRealBasis n =
      (realBasis (n := n)).toBasis.reindex finProdFinEquiv := by
  ext i
  obtain ⟨⟨j, k⟩, rfl⟩ := finProdFinEquiv.surjective i
  simp only [coe_coordinateRealBasis, Module.Basis.reindex_apply,
    Equiv.symm_apply_apply, OrthonormalBasis.coe_toBasis, realBasis_apply,
    coordinateRealFrame]
  fin_cases k <;> simp [ComplexHessianDeterminant.unitPair]

/-- The actual Haar normalization of the complex-positive frame is Euclidean volume. -/
theorem addHaar_canonicalBasis (n : ℕ) :
    (canonicalBasis n).addHaar = (volume : Measure (ComplexModel n)) := by
  rw [canonicalBasis, Module.Basis.addHaar_reindex, topBasis,
    Module.Basis.addHaar_reindex, coordinateRealBasis_eq_realBasis,
    Module.Basis.addHaar_reindex]
  exact (realBasis (n := n)).addHaar_eq_volume

end SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame
