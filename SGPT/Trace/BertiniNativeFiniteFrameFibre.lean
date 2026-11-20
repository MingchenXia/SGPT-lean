import SGPT.Trace.BertiniNativeQuotientEnergyField
import Mathlib.MeasureTheory.Measure.OpenPos

/-! Conditional actual finite-frame fibre consumer; original AE finiteness producer remains separate. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.Bertini
open Bundle Set Filter TensorProduct MeasureTheory
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

private theorem actualNativeFrame_finite_all_coefficients (ζ : ComplexModel N)
    (hfin : ∀ j, nativeBertiniQuotientFrameEnergy p i V hsV L hφ S ζ (Pi.single j (1 : ℂ)) ≠ ⊤) :
    ∀ v : Fin r → ℂ, nativeBertiniQuotientFrameEnergy p i V hsV L hφ S ζ v ≠ ⊤ := by
  classical
  let Q := nativeBertiniQuotientFrameEnergy p i V hsV L hφ S ζ
  have hzero : Q 0 = 0 := by
    have h := nativeBertiniQuotientFrameEnergy_smul p i V hsV L hφ S ζ (0 : ℂ) 0
    simpa only [zero_smul,norm_zero,zero_pow (by decide : 2 ≠ 0),ENNReal.ofReal_zero,zero_mul] using h
  intro v
  have hsum (A : Finset (Fin r)) : Q (∑ j ∈ A, v j • Pi.single j (1 : ℂ)) ≠ ⊤ := by
    induction A using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty,hzero] using (ENNReal.zero_ne_top)
    | @insert j A hj ih =>
      rw [Finset.sum_insert hj]
      have hterm : Q (v j • Pi.single j (1 : ℂ)) ≠ ⊤ := by
        change nativeBertiniQuotientFrameEnergy p i V hsV L hφ S ζ (v j • Pi.single j 1) ≠ ⊤
        rw [nativeBertiniQuotientFrameEnergy_smul]
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfin j)
      have hle := nativeBertiniQuotientFrameEnergy_add_le p i V hsV L hφ S ζ
        (v j • Pi.single j 1) (∑ k ∈ A, v k • Pi.single k 1)
      exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr
        ⟨ENNReal.mul_ne_top (by norm_num) hterm,ENNReal.mul_ne_top (by norm_num) ih⟩) hle
  have hv : (∑ j : Fin r, v j • Pi.single j (1 : ℂ)) = v := by
    ext k
    simp [Finset.sum_apply,Pi.smul_apply,Pi.single_apply]
  have h := hsum Finset.univ
  simpa only [Finset.sum_coe_sort,hv] using h

theorem exists_native_quotient_finite_fibre_in_open_of_ae_frame
    (hBasis : ∀ ζ : V, ∃ b : Module.Basis (Fin r) ℂ (NativeBertiniMultiplierQuotient p i ζ.val L hφ),
      ∀ j, b j = (nativeMultiplierSectionMap (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L)
        (nativeBertiniHyperplaneBundle p) hφ (nativeBertiniAffineSection p i ζ.val)).range.mkQ (S j))
    (hAE : ∀ j : Fin r, ∀ᵐ ζ ∂volume.restrict (V : Set (ComplexModel N)),
      nativeBertiniQuotientFrameEnergy p i V hsV L hφ S ζ (Pi.single j (1 : ℂ)) ≠ ⊤)
    (U : TopologicalSpace.Opens (ComplexModel N)) (hUV : U ≤ V) (hU : (U : Set (ComplexModel N)).Nonempty) :
    ∃ ζ : V, ζ.val ∈ U ∧ ∀ q : NativeBertiniMultiplierQuotient p i ζ.val L hφ,
      nativeBertiniPhysicalQuotientHodgeEnergy p i ζ.val (hsV ζ) L hφ q ≠ ⊤ := by
  classical
  have hAll : ∀ᵐ ζ ∂volume.restrict (V : Set (ComplexModel N)), ∀ j : Fin r,
      nativeBertiniQuotientFrameEnergy p i V hsV L hφ S ζ (Pi.single j 1) ≠ ⊤ := ae_all_iff.mpr hAE
  have hOnU := ae_restrict_of_ae_restrict_of_subset hUV hAll
  obtain ⟨ζ,hζU,hζfin⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae (U.isOpen.measure_ne_zero volume hU) hOnU
  let zV : V := ⟨ζ,hUV hζU⟩
  obtain ⟨b,hb⟩ := hBasis zV
  refine ⟨zV,hζU,?_⟩
  intro q
  have hf := actualNativeFrame_finite_all_coefficients p i V hsV L hφ S ζ hζfin (b.equivFun q)
  have hrep : (∑ j, (b.equivFun q) j • (nativeMultiplierSectionMap
      (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L) (nativeBertiniHyperplaneBundle p)
      hφ (nativeBertiniAffineSection p i ζ)).range.mkQ (S j)) = q := by
    calc
      _ = ∑ j, (b.equivFun q) j • b j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hb j]
      _ = b.equivFun.symm (b.equivFun q) := (b.equivFun_symm_apply _).symm
      _ = q := b.equivFun.symm_apply_apply q
  have hread := nativeBertiniQuotientFrameEnergy_apply p i V hsV L hφ S zV (b.equivFun q)
  rw [hrep] at hread
  exact hread ▸ hf

end SGPT.Trace.Bertini
