import SGPT.Projective.OkounkovOriginalUniformSerrePointUnits
import SGPT.Projective.OkounkovOriginalPerturbAbsorption

/-! Genuine ordinary original unit absorption factors, ONE actual threshold before all positive ample multiples/high degrees/residues/points.
Blueprint: okounkov-original-perturb-absorption-units.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalPerturbAbsorptionUnits
open Set CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) {L T A : X.Modules}
    (a : LineBundleAtlas L) (aT : LineBundleAtlas T) (aA : LineBundleAtlas A)
    (P : SGPT.LineBundle.AmplePolarization f A)

include a aT aA in
/-- ONE actual original threshold BEFORE all positive ample multiples/high degrees/residues/points, no ordinary section premise. -/
theorem exists_perturb_absorption_unit_factors (q : ℕ) :
    ∃ B : ℕ, 0<B ∧ ∀ p₀ : ℕ, 0<p₀ → ∀ g : ℕ, B≤g → ∀ r : Fin q, ∀ c : X,
      ∃ t : Γ(bundleTensor (bundleDual (bundleTensor T (bundleTensorPower L r.val)))
          (bundleTensorPower A ((P.power*p₀)*g)),⊤),
        ∀ b : LineBundleAtlas (bundleTensor (bundleDual (bundleTensor T (bundleTensorPower L r.val)))
          (bundleTensorPower A ((P.power*p₀)*g))),
          c∉(sectionZeroIdealSheaf b t).support := by
  classical
  let R (r : Fin q) := bundleDual (bundleTensor T (bundleTensorPower L r.val))
  let bR (r : Fin q) : LineBundleAtlas (R r) := ValGen2.dualAtlas (pairwiseTensorAtlas aT (a.tensorPower r.val))
  choose B hB using fun r : Fin q =>
    OriginalUniformSerrePointUnits.exists_original_ampleTwist_point_units_polarizationPower f aA P (bR r)
  let B₀ := Finset.univ.sup B+1
  refine ⟨B₀,Nat.succ_pos _,?_⟩
  intro p₀ hp₀ g hg r c
  have hrB : B r≤Finset.univ.sup B := Finset.le_sup (Finset.mem_univ r)
  have hgD : g≤p₀*g := Nat.le_mul_of_pos_left g hp₀
  have hD : B r≤p₀*g := hrB.trans ((Nat.le_succ _).trans (hg.trans hgD))
  rw [Nat.mul_assoc]
  exact hB r (p₀*g) hD c
end SGPT.Okounkov.OriginalPerturbAbsorptionUnits
