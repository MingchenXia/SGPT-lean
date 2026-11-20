import SGPT.Projective.ActualCurveDegreeLinearity
import SGPT.Projective.NativeCIPeriodAlgebra
import SGPT.Foundations.Analysis.Pending.XiaoNefDifferenceCriterion

/-! On a compact connected complex curve the actual integral detects the
Bott--Chern class. Hence changing the source by a holomorphic curve map
scales every signed period by the same nonnegative factor. -/
set_option autoImplicit false

noncomputable section

namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

open MeasureTheory
open SGPT.Projective.NumEq
open SGPT.Hodge.BDivChain.SourceMixedOrderDraft
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses NefMixedMass
open scoped Manifold ContDiff

variable {S T : Type}
  [TopologicalSpace S] [ChartedSpace (ComplexModel 1) S] [IsComplexManifold 1 S]
  [CompactSpace S] [ConnectedSpace S]
  [TopologicalSpace T] [ChartedSpace (ComplexModel 1) T] [IsComplexManifold 1 T]
  [CompactSpace T] [ConnectedSpace T]

/-- The actual signed period, using the canonical Borel measure structure on the curve. -/
def compactCurvePeriod_bd7 (κ : KahlerBackground 1 T) (θ : ClosedRealOneOneForm 1 T) : ℝ :=
  letI : MeasurableSpace T := borel T
  letI : BorelSpace T := ⟨rfl⟩
  slotIntegral κ (fun _ => θ)

/-- The scalar is independent of the form. It is the ratio of the pulled-back
target Kähler period to the original target Kähler period. -/
theorem degreeAlong_eq_KahlerPeriodRatio_mul_of_compactCurves_bd7
    (κS : KahlerBackground 1 S) (κT : KahlerBackground 1 T)
    {g : S → T} (hg : ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel 1) ∞ g) :
    let a := degreeAlong κS hg κT.form / compactCurvePeriod_bd7 κT κT.form
    0 ≤ a ∧ ∀ θ : ClosedRealOneOneForm 1 T,
      degreeAlong κS hg θ = a * compactCurvePeriod_bd7 κT θ := by
  let : MeasurableSpace S := borel S
  let : BorelSpace S := ⟨rfl⟩
  let : MeasurableSpace T := borel T
  let : BorelSpace T := ⟨rfl⟩
  change 0 ≤ degreeAlong κS hg κT.form / slotIntegral κT (fun _ => κT.form) ∧
    ∀ θ : ClosedRealOneOneForm 1 T, degreeAlong κS hg θ =
      (degreeAlong κS hg κT.form / slotIntegral κT (fun _ => κT.form)) *
        slotIntegral κT (fun _ => θ)
  have hnonneg : 0 ≤ degreeAlong κS hg κT.form :=
    slotIntegral_nonneg κS fun _ =>
      ClosedRealOneOneForm.pullback_isSemipositive hg κT.isSemipositive
  have hfamily : Fin.cons κT.form (fun _ : Fin 0 => κT.form) =
      (fun _ : Fin 1 => κT.form) := by
    funext i
    rw [Fin.fin_one_eq_zero i] <;> rfl
  have hpos : 0 < slotIntegral κT (fun _ => κT.form) := by
    rw [← hfamily]
    exact XiaoNefDifferenceCriterion.slotIntegral_cons_kahler_pos (m := 0) κT κT
  refine ⟨div_nonneg hnonneg hpos.le, ?_⟩
  intro θ
  let c := slotIntegral κT (fun _ => θ) / slotIntegral κT (fun _ => κT.form)
  have hslot : slotIntegral κT (fun _ => c • κT.form) =
      slotIntegral κT (fun _ => θ) := by
    have h := slotIntegral_update_smul κT (fun _ => κT.form) 0 c κT.form
    rw [← fun_eq_update_dim_one, ← fun_eq_update_dim_one] at h
    rw [h, smul_eq_mul]
    exact div_mul_cancel₀ _ hpos.ne'
  have hid (η : ClosedRealOneOneForm 1 T) :
      slotIntegral κT (fun _ => ClosedRealOneOneForm.pullback
        (contMDiff_id (I := 𝓘(ℂ, ComplexModel 1)) (n := ∞)) η) =
      slotIntegral κT (fun _ => η) :=
    slotIntegral_eq_of_bottChernRel κT _ _ fun _ =>
      (RealBottChern.ofRepresentative_eq_iff _ _).mp
        (ClosedRealOneOneForm.ofRepresentative_pullback_id η)
  have hclass := ofRepresentative_eq_of_slotIntegral_pullback_id_eq κT
    ((hid θ).trans (hslot.symm.trans (hid (c • κT.form)).symm))
  calc
    _ = degreeAlong κS hg (c • κT.form) :=
      numericallyEquivalent_of_ofRepresentative_eq hclass S κS g hg
    _ = c • degreeAlong κS hg κT.form := degreeAlong_smul_actual κS hg c κT.form
    _ = _ := by
      simp only [smul_eq_mul, c, div_eq_mul_inv]
      ring

/-- A convenient existential form for rewriting an entire finite family of curve periods. -/
theorem exists_nonnegative_pullbackPeriodFactor_of_compactCurves_bd7
    (κS : KahlerBackground 1 S) (κT : KahlerBackground 1 T)
    {g : S → T} (hg : ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel 1) ∞ g) :
    ∃ a : ℝ, 0 ≤ a ∧ ∀ θ : ClosedRealOneOneForm 1 T,
      degreeAlong κS hg θ = a * compactCurvePeriod_bd7 κT θ :=
  ⟨degreeAlong κS hg κT.form / compactCurvePeriod_bd7 κT κT.form,
    degreeAlong_eq_KahlerPeriodRatio_mul_of_compactCurves_bd7 κS κT hg⟩

/-- When the map to the target manifold factors through a compact connected curve,
all its ambient periods are nonnegative multiples of the periods on that curve. -/
theorem exists_nonnegative_composedCurvePeriodFactor_bd7
    {A B M : Type} {n : ℕ}
    [TopologicalSpace A] [ChartedSpace (ComplexModel 1) A] [IsComplexManifold 1 A]
    [CompactSpace A] [ConnectedSpace A]
    [TopologicalSpace B] [ChartedSpace (ComplexModel 1) B] [IsComplexManifold 1 B]
    [CompactSpace B] [ConnectedSpace B]
    [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (κA : KahlerBackground 1 A) (κB : KahlerBackground 1 B)
    {q : A → B} {j : B → M}
    (hq : ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel 1) ∞ q)
    (hj : ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel n) ∞ j) :
    ∃ a : ℝ, 0 ≤ a ∧ ∀ θ : ClosedRealOneOneForm n M,
      degreeAlong κA (hj.comp hq) θ = a * degreeAlong κB hj θ := by
  obtain ⟨a, ha, he⟩ := exists_nonnegative_pullbackPeriodFactor_of_compactCurves_bd7 κA κB hq
  refine ⟨a, ha, fun θ => ?_⟩
  calc
    _ = degreeAlong κA hq (ClosedRealOneOneForm.pullback hj θ) :=
      degreeAlong_comp_actual κA hj hq θ
    _ = a * compactCurvePeriod_bd7 κB (ClosedRealOneOneForm.pullback hj θ) :=
      he (ClosedRealOneOneForm.pullback hj θ)
    _ = _ := rfl

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
