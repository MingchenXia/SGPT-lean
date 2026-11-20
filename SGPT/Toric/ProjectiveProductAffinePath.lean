import SGPT.Toric.ProjectiveProductGrowth
import SGPT.Convex.RankOneLegendreEnergy
import SGPT.Foundations.Analysis.Pending.RelativeEnergyDiamond
import SGPT.Foundations.Analysis.Pending.GlobalMultilinearExpansion

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set MeasureTheory SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.BoundedGlobalProduct
open scoped Topology RealInnerProductSpace

/-- The literal original extended-valued affine potential, before real readback. -/
def projectiveProductAffinePotential {n : ℕ} (φ u : projectiveProductSpace n → EReal)
    (t : ℝ) : projectiveProductSpace n → EReal :=
  fun p => ((1 - t : ℝ) : EReal) * φ p + (t : EReal) * u p

private theorem affine_eq_native_path {n : ℕ} {φ u : projectiveProductSpace n → EReal}
    (hφb : IsBoundedPotential φ) (hub : IsBoundedPotential u) (t : ℝ) :
    projectiveProductAffinePotential φ u t = RelativeEnergyDiamond.path φ u t := by
  funext p
  rw [projectiveProductAffinePotential, ← EReal.coe_toReal (hφb.ne_top p) (hφb.ne_bot p),
    ← EReal.coe_toReal (hub.ne_top p) (hub.ne_bot p)]
  simp only [← EReal.coe_mul, ← EReal.coe_add, RelativeEnergyDiamond.path]

/-- Genuine bounded endpoints manufacture native strong PSH on the entire closed interval. -/
theorem isThetaPshPotential_projectiveProductAffinePotential {n : ℕ}
    {φ u : projectiveProductSpace n → EReal}
    (hφ : IsThetaPshPotential (projectiveProductFSBackground n).form.val φ)
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u)
    (hφb : IsBoundedPotential φ) (hub : IsBoundedPotential u)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    IsThetaPshPotential (projectiveProductFSBackground n).form.val
      (projectiveProductAffinePotential φ u t) := by
  rw [affine_eq_native_path hφb hub]
  exact RelativeEnergyDiamond.isThetaPshPotential_path hφ hu hφb hub ht

/-- The original two finite EReal bounds give genuine finite bounds on the native path. -/
theorem isBoundedPotential_projectiveProductAffinePotential {n : ℕ}
    {φ u : projectiveProductSpace n → EReal}
    (hφb : IsBoundedPotential φ) (hub : IsBoundedPotential u)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    IsBoundedPotential (projectiveProductAffinePotential φ u t) := by
  rw [affine_eq_native_path hφb hub]
  exact RelativeEnergyDiamond.isBoundedPotential_path hφb hub ht

/-- Literal original homogeneous circle invariance survives affine combination. -/
theorem projectiveProductCircleInvariant_affinePotential {n : ℕ}
    {φ u : projectiveProductSpace n → EReal}
    (hiφ : ProjectiveProductCircleInvariant φ) (hiu : ProjectiveProductCircleInvariant u)
    (t : ℝ) : ProjectiveProductCircleInvariant (projectiveProductAffinePotential φ u t) := by
  intro a ha p
  simp only [projectiveProductAffinePotential, hiφ a ha p, hiu a ha p]

private theorem bounded_profile_eq {n : ℕ} {u : projectiveProductSpace n → EReal}
    (hub : IsBoundedPotential u) (x : EuclideanSpace ℝ (Fin n)) :
    projectiveProductToricEuclideanProfile u x =
      (projectiveProductToricDescent u x).toReal + projectiveProductReferenceProfile n x := by
  let p := (projectiveProductNativeChart n (fun _ => false)).val.symm (expCoordinates x)
  change (u p + (projectiveProductReferenceProfile n x : EReal)).toReal =
    (u p).toReal + projectiveProductReferenceProfile n x
  rw [← EReal.coe_toReal (hub.ne_top p) (hub.ne_bot p), ← EReal.coe_add,
    EReal.toReal_coe, EReal.toReal_coe]

/-- Actual original corrected descent gives exactly the real affine profile;
finite source bounds justify every real conversion. -/
theorem projectiveProductToricEuclideanProfile_affinePotential {n : ℕ}
    {φ u : projectiveProductSpace n → EReal}
    (hφb : IsBoundedPotential φ) (hub : IsBoundedPotential u)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    projectiveProductToricEuclideanProfile (projectiveProductAffinePotential φ u t) =
      fun x => (1 - t) * projectiveProductToricEuclideanProfile φ x +
        t * projectiveProductToricEuclideanProfile u x := by
  funext x
  rw [bounded_profile_eq (isBoundedPotential_projectiveProductAffinePotential hφb hub ht),
    bounded_profile_eq hφb, bounded_profile_eq hub]
  rw [projectiveProductToricDescent, affine_eq_native_path hφb hub,
    RelativeEnergyDiamond.toReal_path]
  dsimp only [projectiveProductToricDescent]
  ring

end SGPT.Toric
