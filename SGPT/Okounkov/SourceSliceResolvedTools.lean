import SGPT.Okounkov.SourceSliceResolvedTranslation
import SGPT.Okounkov.ValuativeSliceBounded
import SGPT.Okounkov.TranscendentalVolIdDivisorRestrict
import SGPT.Trace.SmoothTarget

/-! Exact actual residual-data and zero-slice algebra for lma:slicepob.
No slice equality, bigness or mass-convergence certificate is caller data. -/
set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Okounkov.SourceSlice
open Set Matrix
open scoped Pointwise
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.TranscendentalLifting
open SGPT.Okounkov.TranscendentalPartial SGPT.Okounkov.PartialBody

/-- The literal identity-pullback residual is the same original geometric form. -/
theorem identityResidual_geometricallyEq {n : ℕ} (F : OriginalFlagGeometry.{u} n)
    (θ : ClosedRealOneOneForm n F.carrier) (D : MeteredEffectiveQDivisor n F.carrier) :
    (ClosedRealOneOneForm.pullback (identityFlagLifting F).1.1 θ - D.curvature).val.GeometricallyEq
      (θ - D.curvature).val := by
  have hgeo : (ClosedRealOneOneForm.pullback (identityFlagLifting F).1.1 θ).val.GeometricallyEq θ.val :=
    SmoothRealForm.pullback_id_geometricallyEq θ.val
  intro e z hz
  simp only [sub_eq_add_neg, ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_neg]
  rw [hgeo e hz]

/-- Actual decomposition and bounded psh residual manufacture resolution data. -/
theorem identityResolutionData_of_decomposition {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {φ b : F.carrier → EReal}
    (D : MeteredEffectiveQDivisor (m + 1) F.carrier)
    (hb : IsThetaPshPotential (θ - D.curvature).val b)
    (hbounded : ∃ C : ℝ, ∀ y, ((-C : ℝ) : EReal) ≤ b y ∧ b y ≤ (C : EReal))
    (heq : ∀ y, φ y = D.weight y + b y) :
    IsResolutionData θ φ (identityFlagLifting F) D b :=
  ⟨((identityResidual_geometricallyEq F θ D).thetaPshPotential_iff b).mpr hb, hbounded, heq⟩

/-- The real source Kähler bound produces residual bigness, rather than
requiring that conclusion from the caller. -/
theorem isBig_residual_of_actual_decomposition {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {φ b : F.carrier → EReal}
    (hφK : IsKahlerCurrentPotential θ φ) (D : MeteredEffectiveQDivisor (m + 1) F.carrier)
    (hb : IsThetaPshPotential (θ - D.curvature).val b)
    (hbounded : ∃ C : ℝ, ∀ y, ((-C : ℝ) : EReal) ≤ b y ∧ b y ≤ (C : EReal))
    (heq : ∀ y, φ y = D.weight y + b y) :
    SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative (θ - D.curvature)) := by
  have hbig := isBig_residualClass
    (identityResolutionData_of_decomposition F D hb hbounded heq) hφK
  have hclass := RealBottChern.ofRepresentative_eq_of_geometricallyEq
    (identityResidual_geometricallyEq F θ D)
  rwa [hclass] at hbig

/-- A literal original zero-coordinate slice commutes with translation by
an original vector with zero first coordinate; the actual tail is retained. -/
theorem firstCoordinateSlice_vadd_zero {m : ℕ} (d : Fin (m + 1) → ℝ)
    (hd : d 0 = 0) (B : Set (Fin (m + 1) → ℝ)) :
    TranscendentalMain.firstCoordinateSlice (d +ᵥ B) 0 =
      (fun j : Fin m => d j.succ) +ᵥ TranscendentalMain.firstCoordinateSlice B 0 := by
  ext y
  constructor
  · intro hy
    change Fin.cons 0 y ∈ d +ᵥ B at hy
    obtain ⟨z, hz, heq⟩ := hy
    change d + z = Fin.cons 0 y at heq
    have hz0 : z 0 = 0 := by
      have h := congrFun heq 0
      simpa only [Pi.add_apply, hd, zero_add, Fin.cons_zero] using h
    have hzcons : z = Fin.cons 0 (fun j : Fin m => z j.succ) := by
      funext i
      refine Fin.cases ?_ (fun _ => rfl) i
      simpa only [Fin.cons_zero] using hz0
    refine ⟨(fun j : Fin m => z j.succ), ?_, ?_⟩
    · change Fin.cons 0 (fun j : Fin m => z j.succ) ∈ B
      rw [← hzcons]
      exact hz
    · change (fun j : Fin m => d j.succ) + (fun j : Fin m => z j.succ) = y
      funext j
      simpa only [Pi.add_apply, Fin.cons_succ] using congrFun heq j.succ
  · rintro ⟨z, hz, heq⟩
    change Fin.cons 0 y ∈ d +ᵥ B
    refine ⟨Fin.cons 0 z, hz, ?_⟩
    change d + Fin.cons 0 z = Fin.cons 0 y
    change (fun j : Fin m => d j.succ) + z = y at heq
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Pi.add_apply, hd, Fin.cons_zero, add_zero]
    · simpa only [Pi.add_apply, Fin.cons_succ] using congrFun heq j
end SGPT.Okounkov.SourceSlice
