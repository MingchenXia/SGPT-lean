import SGPT.Foundations.Envelope.AlgGeom.SeshadriAmplenessCriterionNefAmple
import SGPT.Foundations.Envelope.AlgGeom.NativeNumericalRationalAmpleLines
import SGPT.Foundations.Envelope.AlgGeom.NativeNumericalPositiveAmpleSums
import SGPT.Foundations.Envelope.AlgGeom.NativeNumericalAmpleClasses

/-! Actual numerical ampleness without the unrelated PSH-ray comparison import.
Blueprint: source-numerical-ampleness.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SGPT.NAPotential.BJ.SourceNumericalAmpleness
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Scheme.Modules
open SGPT.Foundations.Envelope SGPT.Foundations.Envelope.CanonicalGeometry
open SGPT.Foundations.Envelope.NativeRealNumericalClasses
open scoped Classical NNReal ENNReal
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory
variable {k : Type u} [Field k] {X : Scheme.{u}}
  (p : X ⟶ Spec (.of k)) [IsProjective p]

local instance sourceAmpleProper : IsProper p :=
  (ProjectiveFactorizationRingIso.of_isProjective p).isProper

/-- Actual numerical ample-cone membership produces actual original line-sheaf ampleness. -/
theorem isAmple_of_lineClass_mem_ampleCone [IsIntegral X]
    (T : X.Modules) (hT : IsInvertible T) (h : lineClass p T hT ∈ ampleCone p) :
    SchemeLineAmpleness.IsAmple p T := by
  obtain ⟨n, hn, A, hA, c, hc, he⟩ := exists_positive_ample_line_sum p _ h
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  choose q hq₁ hq₂ using fun i => exists_rat_btwn (half_lt_self (hc i))
  have hqpos (i : Fin n) : 0 < q i := by exact_mod_cast (half_pos (hc i)).trans (hq₁ i)
  obtain ⟨d, hd, B, hB, hBe⟩ := exists_rational_ample_line_representative p hn A hA q hqpos
  have hTd := TensorPowerBaseIdealGrading.tensorPower_isInvertible hT d
  have hNinv : IsInvertible (bundleTensorPower T d ⊗ dualObj B) :=
    hTd.monoidalTensor hB.isInvertible.dual
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hB' : lineClass p B hB.isInvertible =
      (d : ℝ) • lineFamilyMap p A (fun i => (hA i).isInvertible) (fun i => (q i : ℝ)) := by
    rw [hBe, smul_smul, mul_inv_cancel₀ hd', one_smul]
  have hNclass : lineClass p (bundleTensorPower T d ⊗ dualObj B) hNinv =
      ∑ i, ((d : ℝ) * (c i - q i)) • lineClass p (A i) (hA i).isInvertible := by
    rw [lineClass_tensor p _ _ hTd hB.isInvertible.dual, lineClass_dual p B hB.isInvertible,
      lineClass_tensorPower p T hT d, hB', he, lineFamilyMap_apply, lineFamilyMap_apply,
      Finset.smul_sum, Finset.smul_sum, ← sub_eq_add_neg, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, smul_smul, ← sub_smul, mul_sub]
  have hnef : lineClass p (bundleTensorPower T d ⊗ dualObj B) hNinv ∈ nefCone p := by
    rw [hNclass]
    exact positive_ample_sum_mem_nefCone p A hA _
      (fun i => mul_pos (by exact_mod_cast hd) (sub_pos.mpr (hq₂ i)))
  have hNB := SeshadriAmplenessCriterionNefAmple.isAmple_tensor_nef p _ B hNinv hnef hB
  have hpow : SchemeLineAmpleness.IsAmple p (bundleTensorPower T d) :=
    AmpleTensorLines.ample_of_iso hNB
      (α_ _ _ _ ≪≫ whiskerLeftIso _ ((β_ (dualObj B) B) ≪≫ hB.isInvertible.monoidalEvaluationIso) ≪≫
        ρ_ _)
  exact AmpleLinePositivePowers.isAmple_of_tensorPower p T hT d hd hpow

end SGPT.NAPotential.BJ.SourceNumericalAmpleness
