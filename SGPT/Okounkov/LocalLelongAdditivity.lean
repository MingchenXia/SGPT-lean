import SGPT.Okounkov.LocalLelong
import SGPT.Foundations.Analysis.Pending.ActualLelongAdditivity

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov

open TopologicalSpace
open scoped Manifold
open SGPT.Foundations.Analysis
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending

/-- Reusing main's full arithmetic on the genuine original open subtype
gives exact local additivity without imposing global extensions of the functions. -/
theorem lelongNumber_add_eq_on_opens {n : ℕ} {Ω : Opens (ComplexModel n)}
    {u v : ComplexModel n → EReal}
    (hu : QuasiPlurisubharmonicOn u Ω) (hv : QuasiPlurisubharmonicOn v Ω) (x : Ω) :
    lelongNumber (n := n) (fun y => u y + v y) x =
      lelongNumber (n := n) u x + lelongNumber (n := n) v x := by
  have heq := ActualLelongAdditivity.lelongNumber_add_eq
    (manifoldQuasiPlurisubharmonic_opens_restrict hu)
    (manifoldQuasiPlurisubharmonic_opens_restrict hv) x
  calc
    _ = lelongNumber (n := n) (fun y : Ω => u y + v y) x :=
      (lelongNumber_opens_restrict (fun y => u y + v y) x).symm
    _ = lelongNumber (n := n) (fun y : Ω => u y) x +
        lelongNumber (n := n) (fun y : Ω => v y) x := heq
    _ = _ := by rw [lelongNumber_opens_restrict u x, lelongNumber_opens_restrict v x]

end SGPT.Okounkov
