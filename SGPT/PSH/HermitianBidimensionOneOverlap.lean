import SGPT.PSH.HermitianMixedGlobalCurrent
import SGPT.PSH.HermitianProductOverlap

/-! # The original bidimension-one mixed current has genuine chart descent -/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianGlobalProducts

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open LocalProductCurrents LocalBedfordTaylorProducts LocalBedfordTaylorCollar
  LocalBedfordTaylorLocality LocalCurrentPullback
open Hermitian HermitianProducts

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
  {omega : Background (m + 1) M}

private theorem cast_backgroundExpansion_unit {n : ℕ} {U : TopologicalSpace.Opens (ComplexModel n)}
    (p r s : ℕ) (hrs : r = s) (hr : r + p = n) (hs : s + p = n)
    (v : Fin p → ComplexModel n → ℝ)
    {σ : ComplexModel n → StronglyPositiveForms.RealForm n 2}
    (hσ : ContDiffOn ℝ (↑(⊤ : ℕ∞)) σ U) :
    castLPC hrs (backgroundExpansion p r v hσ (oneCurrentOf (U := U) hr)) =
      backgroundExpansion p s v hσ (oneCurrentOf (U := U) hs) := by
  cases hrs
  rfl

private theorem pullback_congr_current {n r : ℕ} {A B : TopologicalSpace.Opens (ComplexModel n)}
    {τ ι : ComplexModel n → ComplexModel n} (h : BedfordTaylor.IsBiholomorphicPair A B τ ι)
    {S T : LocalProductCurrent n B r} (hS : IsPositive S) (hT : IsPositive T)
    (heq : S = T) : pullback h hS = pullback h hT := by
  subst T
  rfl

namespace BackgroundPatch

/-- Exact degree transport retains the original current, not just its trace. -/
theorem bidimensionOneCurrent_eq_currentOfDegree (P : BackgroundPatch omega)
    (u : Fin m → M → EReal) :
    P.bidimensionOneCurrent u = P.currentOfDegree m 1 (by omega) u :=
  cast_backgroundExpansion_unit m (m + 1 - m) 1 (by omega)
    (Nat.sub_add_cancel (by omega)) (by omega) _ P.residual_smooth

/-- Holomorphic covariance of the SAME actual bidimension-one product used
in the native supported-current construction. -/
theorem bidimensionOneCurrent_overlap (P Q : BackgroundPatch omega)
    (u : Fin m → M → EReal) (hu : ∀ i, IsHermitianPSH omega (u i))
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal)) :
    pullback (P.geometry.isBiholomorphicPair Q.geometry)
      (isPositive_restrict (Q.bidimensionOneCurrent_isPositive u hu hb)
        (Q.geometry.overlapDomain_le P.geometry)) =
      restrict (P.geometry.overlapDomain_le Q.geometry) (P.bidimensionOneCurrent u) := by
  calc
    _ = pullback (P.geometry.isBiholomorphicPair Q.geometry)
        (isPositive_restrict (Q.currentOfDegree_isPositive m 1 (by omega) u hu hb)
          (Q.geometry.overlapDomain_le P.geometry)) :=
      pullback_congr_current _ _ _ (congrArg
        (restrict (Q.geometry.overlapDomain_le P.geometry))
        (Q.bidimensionOneCurrent_eq_currentOfDegree u))
    _ = restrict (P.geometry.overlapDomain_le Q.geometry)
        (P.currentOfDegree m 1 (by omega) u) :=
      P.currentOfDegree_overlap Q m 1 (by omega) u hu hb
    _ = _ := congrArg (restrict (P.geometry.overlapDomain_le Q.geometry))
      (P.bidimensionOneCurrent_eq_currentOfDegree u).symm

end BackgroundPatch
end SGPT.PSH.HermitianGlobalProducts
