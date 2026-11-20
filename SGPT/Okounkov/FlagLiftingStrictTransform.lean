import SGPT.Okounkov.FlagLifting
import SGPT.Okounkov.FlagLelong
import SGPT.Foundations.Analysis.Pending.AnalyticModificationDivisorStrictTransform

set_option autoImplicit false

noncomputable section
universe u

namespace SGPT.Okounkov

open Set Filter
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open SourceGenericSubmanifoldMinimum SquaredLogLelongSourceNormalization
open AnalyticModificationLocalDiscrepancy SourceTraceRepresentativeDefinition

/-- Actual intrinsic exceptional-image codimension and the identity principle
identify the original lifted first carrier with its literal strict transform. -/
theorem IsFlagLifting.first_carrier_eq_strictTransform {m : ℕ}
    {F W : OriginalFlagGeometry.{u} (m + 1)} {π : W.carrier → F.carrier}
    (hπ : IsFlagLifting F W π) :
    W.flag (1 : Fin (m + 2)) =
      strictTransform (m + 1) π (F.flag (1 : Fin (m + 2))) := by
  obtain ⟨VY, hY, hdY⟩ := exists_subvariety_carrier_eq_of_submanifold F.firstDivisor
  obtain ⟨VW, hW, _hdW⟩ := exists_subvariety_carrier_eq_of_submanifold W.firstDivisor
  have hdY' : VY.dim + 1 = m + 1 := by rw [hdY]
  obtain ⟨Vt, hstrict, _hdt, _himage, _hreader⟩ :=
    AnalyticModificationDivisorStrictTransform.exists_strictTransform_reader hπ.1 VY hdY'
  have hstrict' : Vt.carrier =
      strictTransform (m + 1) π (F.flag (1 : Fin (m + 2))) := by
    rwa [hY] at hstrict
  obtain ⟨hi, _hlevel⟩ := hπ.2 (1 : Fin (m + 2))
  have himage := hπ.component_image_eq (1 : Fin (m + 2))
  have hav := AnalyticModificationExceptionalImageCodimension.not_subset_image_exceptionalLocus_of_codim_one
    hπ.1 VY hdY'
  obtain ⟨y, hy, hyE⟩ := not_subset.mp hav
  have hy' : y ∈ F.flag (1 : Fin (m + 2)) := hY ▸ hy
  obtain ⟨w, hw, hwy⟩ := (Set.ext_iff.mp himage y).mpr hy'
  have hwE : w ∉ exceptionalLocus (m + 1) π := by
    intro h
    exact hyE ⟨w, h, hwy⟩
  have hsub : strictTransform (m + 1) π (F.flag (1 : Fin (m + 2))) ⊆
      W.flag (1 : Fin (m + 2)) := by
    change closure (π ⁻¹' F.flag (1 : Fin (m + 2)) \ exceptionalLocus (m + 1) π) ⊆ _
    refine closure_minimal ?_ W.firstDivisor.1
    rintro z ⟨hz, hzE⟩
    obtain ⟨v, hv, hvz⟩ := (Set.ext_iff.mp himage (π z)).mpr hz
    exact (AnalyticModificationExceptionalFibres.eq_of_apply_eq_of_not_mem_exceptionalLocus
      hπ.1 hzE hvz) ▸ hv
  have hrev : VW.carrier ⊆ Vt.carrier :=
    StrictTransformLocus.subset_of_inter_isOpen_subset VW Vt.analytic
      (StrictTransformComposition.isOpen_compl_exceptionalLocus hπ.1.1)
      ⟨w, hW.symm ▸ hw, hwE⟩ (by
        rintro z ⟨hz, hzE⟩
        rw [hstrict']
        exact subset_closure ⟨hi (hW ▸ hz), hzE⟩)
  exact Subset.antisymm (by simpa only [hW, hstrict'] using hrev) hsub

/-- Whole native strict-transform covariance gives the exact original source
first generic reader without a finite-reader or avoidance premise. -/
theorem IsFlagLifting.sourceGeneric_first_comp_eq {m : ℕ}
    {F W : OriginalFlagGeometry.{u} (m + 1)} {π : W.carrier → F.carrier}
    (hπ : IsFlagLifting F W π) {u : F.carrier → EReal}
    (hu : IsGlobalQuasiPshPotential (n := m + 1) u) :
    sourceGenericLelongNumber (n := m + 1)
        (Subtype.val : W.flag (1 : Fin (m + 2)) → W.carrier) (u ∘ π) =
      sourceGenericLelongNumber (n := m + 1)
        (Subtype.val : F.flag (1 : Fin (m + 2)) → F.carrier) u := by
  obtain ⟨VY, hY, hdY⟩ := exists_subvariety_carrier_eq_of_submanifold F.firstDivisor
  have hdY' : VY.dim + 1 = m + 1 := by rw [hdY]
  obtain ⟨Vt, hstrict, _hdt, _himage, hreader⟩ :=
    AnalyticModificationDivisorStrictTransform.exists_strictTransform_reader hπ.1 VY hdY'
  have hVt : Vt.carrier = W.flag (1 : Fin (m + 2)) := by
    rw [hstrict, hY, hπ.first_carrier_eq_strictTransform]
  have hn : m + 1 ≠ 0 := Nat.succ_ne_zero m
  rw [sourceGeneric_subtype_eq_iInf, sourceGeneric_subtype_eq_iInf]
  apply (ENNReal.mul_right_inj (a := 2) (by norm_num) (by norm_num)).mp
  rw [← iInf_lelongNumber_eq_two_mul_squaredLog hn,
    ← iInf_lelongNumber_eq_two_mul_squaredLog hn]
  simpa only [hVt, hY, Function.comp_def] using hreader u hu.1

end SGPT.Okounkov
