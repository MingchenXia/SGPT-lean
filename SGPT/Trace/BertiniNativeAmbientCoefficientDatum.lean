import SGPT.Trace.BertiniNativeCoefficientEnergy

/-! Literal actual physical ambient data of the original multiplier coefficient frame. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniFamilyCanonical
open Bundle Set Filter TensorProduct
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.CompactHolomorphicSectionsDraft SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Trace.Bertini SGPT.Trace.BertiniPencilFamily

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d+1)) X] [IsComplexManifold (d+1) X] [CompactSpace X]
  (p : ContMDiffMap 𝓘(ℂ,ComplexModel (d+1)) 𝓘(ℂ,ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N+1)) (a v : ComplexModel N) (U : TopologicalSpace.Opens (ComplexModel 1))
  (hsm : ∀ t : U, IsSmoothHypersurfaceMember (d+1) p (affinePoint i (a-t.val 0 • v)))
  (L : HermitianHolomorphicLineBundle.{0,0} (d+1) X)
  {φ : X → EReal} (hφ : IsGlobalQuasiPshPotential (n := d+1) φ)

theorem familyAmbientPhysicalSection_nativeMultiplierSwap :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ T : nativeMultiplierSections
      (tensor (tensor (nativeCanonicalBundle (n := d+1) (X := X)) L) (nativeBertiniHyperplaneBundle p)) φ,
      familyAmbientPhysicalSection p i a v U hsm L
        (nativeMultiplierSwapLastSectionMap (nativeCanonicalBundle (n := d+1) (X := X)) L
          (nativeBertiniHyperplaneBundle p) hφ T).val =
      nativeMultiplierFamilyPhysicalSectionMap p i a v U hsm L hφ T := by
  intros
  rfl

theorem nativeMultiplierAmbientCoefficientDatum_trace :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (r : ℕ) (S : Fin r → nativeMultiplierSections
      (tensor (tensor (nativeCanonicalBundle (n := d+1) (X := X)) L) (nativeBertiniHyperplaneBundle p)) φ)
      (c : Fin r → ℂ) (q : familyIncidence p i a v U),
      (nativeMultiplierSwapLastSectionMap (nativeCanonicalBundle (n := d+1) (X := X)) L
        (nativeBertiniHyperplaneBundle p) hφ (∑ j, c j • S j)).val q.val.2 =
      ∑ j, c j • nativeMultiplierFamilyPhysicalSectionMap p i a v U hsm L hφ (S j) q := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  classical
  intro r S c q
  change nativeMultiplierFamilyPhysicalSectionMap p i a v U hsm L hφ (∑ j, c j • S j) q = _
  have hlin : nativeMultiplierFamilyPhysicalSectionMap p i a v U hsm L hφ (∑ j, c j • S j) =
      ∑ j, c j • nativeMultiplierFamilyPhysicalSectionMap p i a v U hsm L hφ (S j) := by
    simp only [map_sum,map_smul]
  rw [hlin]
  change ((ContMDiffSection.coeAddHom 𝓘(ℂ,ComplexModel (d+1)) ℂ ∞
    (familyNativePhysicalModel p i a v U hsm L).Fiber)
      (∑ j, c j • nativeMultiplierFamilyPhysicalSectionMap p i a v U hsm L hφ (S j))) q = _
  rw [map_sum]
  simp only [Finset.sum_apply,ContMDiffSection.coeAddHom_apply]
  apply Finset.sum_congr rfl
  intro j _
  rfl

theorem nativeMultiplierAmbientCoefficientDatum_hodgeEnergy (t : U) :
    ∀ (r : ℕ) (S : Fin r → nativeMultiplierSections
      (tensor (tensor (nativeCanonicalBundle (n := d+1) (X := X)) L) (nativeBertiniHyperplaneBundle p)) φ)
      (c : Fin r → ℂ),
      nativeBertiniAdjunctionHodgeEnergy p i (a-t.val 0 • v) (hsm t) L φ
        (nativeMultiplierSwapLastSectionMap (nativeCanonicalBundle (n := d+1) (X := X)) L
          (nativeBertiniHyperplaneBundle p) hφ (∑ j, c j • S j)).val =
      nativeBertiniPhysicalQuotientHodgeEnergy p i (a-t.val 0 • v) (hsm t) L hφ
        (∑ j, c j • (nativeMultiplierSectionMap (tensor (nativeCanonicalBundle (n := d+1) (X := X)) L)
          (nativeBertiniHyperplaneBundle p) hφ (nativeBertiniAffineSection p i (a-t.val 0 • v))).range.mkQ (S j)) := by
  classical
  intro r S c
  change nativeBertiniAdjunctionHodgeEnergy p i (a-t.val 0 • v) (hsm t) L φ
    (NativeTensorSwap.swapLastSection (nativeCanonicalBundle (n := d+1) (X := X)) L
      (nativeBertiniHyperplaneBundle p) (∑ j, c j • S j).val) = _
  have h := nativeBertiniPhysicalQuotientHodgeEnergy_mk p i (a-t.val 0 • v) (hsm t) L hφ (∑ j, c j • S j)
  simpa only [map_sum,map_smul] using h.symm

end SGPT.Trace.BertiniFamilyCanonical
