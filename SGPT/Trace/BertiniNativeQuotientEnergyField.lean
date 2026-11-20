import SGPT.Trace.BertiniNativeFullBaseQuotientHodgeLowerSemicontinuity
import SGPT.Trace.BertiniNativeQuotientEnergyAlgebra

/-! Manufactured ACTUAL quotient energy field on the FULL ambient affine base. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.Bertini
open Bundle Set Filter Metric TensorProduct MeasureTheory
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.CompactHolomorphicSectionsDraft SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (V : TopologicalSpace.Opens (ComplexModel N))
  (hsV : ∀ ζ : V, IsSmoothHypersurfaceMember (d + 1) p (affinePoint i ζ.val))
  (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) X)
  {φ : X → EReal} (hφ : IsGlobalQuasiPshPotential (n := d + 1) φ) {r : ℕ}
  (S : Fin r → nativeMultiplierSections
    (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L) (nativeBertiniHyperplaneBundle p)) φ)

def nativeBertiniQuotientFrameEnergy (ζ : ComplexModel N) (v : Fin r → ℂ) : ℝ≥0∞ := by
  classical
  exact if hζ : ζ ∈ V then
    nativeBertiniPhysicalQuotientHodgeEnergy p i ζ (hsV ⟨ζ,hζ⟩) L hφ
      (∑ j, v j • (nativeMultiplierSectionMap (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L)
        (nativeBertiniHyperplaneBundle p) hφ (nativeBertiniAffineSection p i ζ)).range.mkQ (S j)) else 0

theorem nativeBertiniQuotientFrameEnergy_apply (ζ : V) (v : Fin r → ℂ) :
    nativeBertiniQuotientFrameEnergy p i V hsV L hφ S ζ.val v =
      nativeBertiniPhysicalQuotientHodgeEnergy p i ζ.val (hsV ζ) L hφ
        (∑ j, v j • (nativeMultiplierSectionMap (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L)
          (nativeBertiniHyperplaneBundle p) hφ (nativeBertiniAffineSection p i ζ.val)).range.mkQ (S j)) := by
  unfold nativeBertiniQuotientFrameEnergy
  rw [dif_pos ζ.property]

theorem nativeBertiniQuotientFrameEnergy_smul (ζ : ComplexModel N) (a : ℂ) (v : Fin r → ℂ) :
    nativeBertiniQuotientFrameEnergy p i V hsV L hφ S ζ (a • v) =
      ENNReal.ofReal (‖a‖ ^ 2) * nativeBertiniQuotientFrameEnergy p i V hsV L hφ S ζ v := by
  classical
  by_cases hζ : ζ ∈ V
  · unfold nativeBertiniQuotientFrameEnergy
    rw [dif_pos hζ,dif_pos hζ]
    let Q := (nativeMultiplierSectionMap (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L)
      (nativeBertiniHyperplaneBundle p) hφ (nativeBertiniAffineSection p i ζ)).range
    have hsum : (∑ j, (a • v) j • Q.mkQ (S j)) = a • ∑ j, v j • Q.mkQ (S j) := by
      simp only [Pi.smul_apply,Finset.smul_sum,smul_smul,smul_eq_mul]
    rw [hsum]
    exact nativeBertiniPhysicalQuotientHodgeEnergy_smul p i ζ (hsV ⟨ζ,hζ⟩) L hφ a _
  · simp only [nativeBertiniQuotientFrameEnergy,dif_neg hζ,mul_zero]

theorem nativeBertiniQuotientFrameEnergy_add_le (ζ : ComplexModel N) (v w : Fin r → ℂ) :
    nativeBertiniQuotientFrameEnergy p i V hsV L hφ S ζ (v + w) ≤
      2 * nativeBertiniQuotientFrameEnergy p i V hsV L hφ S ζ v +
      2 * nativeBertiniQuotientFrameEnergy p i V hsV L hφ S ζ w := by
  classical
  by_cases hζ : ζ ∈ V
  · unfold nativeBertiniQuotientFrameEnergy
    rw [dif_pos hζ,dif_pos hζ,dif_pos hζ]
    let Q := (nativeMultiplierSectionMap (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L)
      (nativeBertiniHyperplaneBundle p) hφ (nativeBertiniAffineSection p i ζ)).range
    have hsum : (∑ j, (v + w) j • Q.mkQ (S j)) =
        (∑ j, v j • Q.mkQ (S j)) + ∑ j, w j • Q.mkQ (S j) := by
      simp only [Pi.add_apply,add_smul,Finset.sum_add_distrib]
    rw [hsum,← mul_add]
    exact nativeBertiniPhysicalQuotientHodgeEnergy_add_le p i ζ (hsV ⟨ζ,hζ⟩) L hφ _ _
  · simp only [nativeBertiniQuotientFrameEnergy,dif_neg hζ,mul_zero,zero_add,le_refl]

omit i V hsV S in
theorem exists_native_fullBase_quotient_energy_field [ConnectedSpace X]
    (ℓ₀ : HyperplaneSpace N) (hsm₀ : IsSmoothHypersurfaceMember (d + 1) p ℓ₀)
    (hproper : ∃ x : X, x ∉ member p ℓ₀) :
    ∃ (m : ℕ) (T : Fin m → nativeMultiplierSections
      (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L) (nativeBertiniHyperplaneBundle p)) φ)
      (U : TopologicalSpace.Opens (ComplexModel N)) (_hU : affineChart (chartIndex ℓ₀) ℓ₀ ∈ U)
      (hsU : ∀ ζ : U, IsSmoothHypersurfaceMember (d + 1) p (affinePoint (chartIndex ℓ₀) ζ.val)),
      (∀ ζ : U, ∃ b : Module.Basis (Fin m) ℂ (NativeBertiniMultiplierQuotient p (chartIndex ℓ₀) ζ.val L hφ),
        ∀ j, b j = (nativeMultiplierSectionMap (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L)
          (nativeBertiniHyperplaneBundle p) hφ (nativeBertiniAffineSection p (chartIndex ℓ₀) ζ.val)).range.mkQ (T j)) ∧
      LowerSemicontinuous (fun q : ComplexModel N × (Fin m → ℂ) =>
        nativeBertiniQuotientFrameEnergy p (chartIndex ℓ₀) U hsU L hφ T q.1 q.2) := by
  classical
  obtain ⟨m,T,U,hU,hsU,hb,hl⟩ :=
    exists_native_fullBase_quotient_frame_hodge_lowerSemicontinuity p L hφ ℓ₀ hsm₀ hproper
  refine ⟨m,T,U,hU,hsU,hb,?_⟩
  let F : ((Fin m → ℂ) × U) → ℝ≥0∞ := fun q =>
    nativeBertiniQuotientFrameEnergy p (chartIndex ℓ₀) U hsU L hφ T q.2.val q.1
  have hF : LowerSemicontinuous F := by
    have heq : F = fun q : (Fin m → ℂ) × U =>
        nativeBertiniPhysicalQuotientHodgeEnergy p (chartIndex ℓ₀) q.2.val (hsU q.2) L hφ
          (∑ j, q.1 j • (nativeMultiplierSectionMap (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L)
            (nativeBertiniHyperplaneBundle p) hφ (nativeBertiniAffineSection p (chartIndex ℓ₀) q.2.val)).range.mkQ (T j)) := by
      funext q
      exact nativeBertiniQuotientFrameEnergy_apply p (chartIndex ℓ₀) U hsU L hφ T q.2 q.1
    rw [heq]
    exact hl
  let I : ((Fin m → ℂ) × U) → ((Fin m → ℂ) × ComplexModel N) := fun q => (q.1,q.2.val)
  have hI : IsOpenMap I := IsOpenMap.id.prodMap U.isOpen.isOpenMap_subtype_val
  let G : ((Fin m → ℂ) × ComplexModel N) → ℝ≥0∞ := fun q =>
    nativeBertiniQuotientFrameEnergy p (chartIndex ℓ₀) U hsU L hφ T q.2 q.1
  have hG : LowerSemicontinuous G := by
    apply lowerSemicontinuous_iff_isOpen_preimage.mpr
    intro b
    have hset : G ⁻¹' Ioi b = I '' (F ⁻¹' Ioi b) := by
      ext q
      constructor
      · intro hq
        have hmem : q.2 ∈ U := by
          by_contra hn
          have hz : G q = 0 := by simp only [G,nativeBertiniQuotientFrameEnergy,dif_neg hn]
          have hb : b < G q := hq
          rw [hz] at hb
          exact (not_lt_of_ge (show (0 : ℝ≥0∞) ≤ b from zero_le)) hb
        exact ⟨(q.1,⟨q.2,hmem⟩),hq,rfl⟩
      · rintro ⟨z,hz,rfl⟩
        exact hz
    rw [hset]
    exact hI _ (hF.isOpen_preimage b)
  exact hG.comp (continuous_snd.prodMk continuous_fst)

end SGPT.Trace.Bertini
