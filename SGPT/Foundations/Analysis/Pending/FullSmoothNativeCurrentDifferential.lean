import SGPT.Foundations.Analysis.Pending.OpenSmoothFormDistributionReflection
import SGPT.Foundations.Analysis.Pending.XiaoLeviTestDDCDensity
import SGPT.Foundations.Analysis.Pending.GlobalCurrents

set_option autoImplicit false

/-! Full native smooth currents and their original distribution differential.
All mathematical statements and ENTIRE proofs were captured before this source.
No restricted product-test predicate is substituted for native closedness. -/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Distributions
namespace SGPT.Foundations.Analysis.Pending.FullSmoothNativeCurrentDifferential
open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses
  _root_.SGPT.Foundations.Analysis.LocalCurrents GlobalCurrents
  ProductTestForms XiaoLeviTestDDCDensity OpenSmoothFormDistributionReflection

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace (ComplexModel n)] [BorelSpace (ComplexModel n)]
  (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))

/-- Every actual native coefficient, in any admissible real degree, is the
full regular form of the same original smooth density. -/
theorem coefficients_smoothGlobalCurrent {k : CurrentDegree n}
    (a : SmoothRealForm n M k.val) (e : ComplexChart n M) :
    (smoothGlobalCurrent b a).coefficients b e = smoothFormDistribution b a e :=
  CurrentPairing.fromLocalCurrent_toLocalCurrent b k _

/-- Full distribution differentiation keeps the original chart density,
including in top and zero degree and on empty chart targets. -/
theorem exteriorDerivative_coefficients_smoothGlobalCurrent {k : CurrentDegree n}
    (a : SmoothRealForm n M k.val) (e : ComplexChart n M) :
    _root_.SGPT.Foundations.Analysis.LocalCurrents.exteriorDerivative
      ((smoothGlobalCurrent b a).coefficients b e) =
      smoothFormDistribution b a.exteriorDerivative e := by
  rw [coefficients_smoothGlobalCurrent]
  exact exteriorDerivative_regularForm_eq b.addHaar (a.coeff e) (a.smooth e)

/-- The actual full native smooth current is closed exactly when its genuine
smooth density is closed in all original charts. -/
theorem isClosed_smoothGlobalCurrent_iff {k : CurrentDegree n}
    (a : SmoothRealForm n M k.val) :
    (smoothGlobalCurrent b a).IsClosed b ↔ a.IsClosed := by
  constructor
  · intro h e z hz
    have hc := h e
    rw [coefficients_smoothGlobalCurrent] at hc
    exact (isClosed_regularForm_iff b.addHaar (a.coeff e) (a.smooth e)).mp hc z hz
  · intro h e
    rw [coefficients_smoothGlobalCurrent]
    exact (isClosed_regularForm_iff b.addHaar (a.coeff e) (a.smooth e)).mpr
      (fun z hz => h e z hz)

/-- Natural closed real (1,1) data internally give genuine closed native
currents for the very powers, without a supplied current-closedness premise. -/
theorem isClosed_smoothGlobalCurrent_formPow (C : ClosedRealOneOneForm n M)
    (q : ℕ) (hq : 2 * q < 2 * n + 1) :
    (smoothGlobalCurrent b (k := ⟨2 * q, by rw [complexModel_real_finrank]; exact hq⟩) (formPow C.val q)).IsClosed b :=
  (isClosed_smoothGlobalCurrent_iff b
    (k := ⟨2 * q, by rw [complexModel_real_finrank]; exact hq⟩) (formPow C.val q)).mpr
    (formPow_closedReal_isClosed C q)

end SGPT.Foundations.Analysis.Pending.FullSmoothNativeCurrentDifferential
