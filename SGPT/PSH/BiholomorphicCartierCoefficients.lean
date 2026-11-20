import SGPT.PSH.BiholomorphicPrimeIdealOrder
import SGPT.PSH.CanonicalCartierCoefficients

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open scoped Topology Manifold ContDiff

universe u
variable {n : ℕ} {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [ChartedSpace (ComplexModel n) N] [IsComplexManifold n N]

/-- ENTIRE regular locus, preserving each actual dimension through the accepted
regular-witness producer in BOTH genuine holomorphic directions. -/
theorem regularPoints_preimage_biholomorphic (e : M ≃ₜ N)
    (he : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e)
    (hei : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e.symm)
    (A : Set N) :
    RegularLocusComponent.regularPoints (n := n) (e ⁻¹' A) =
      e ⁻¹' RegularLocusComponent.regularPoints (n := n) A := by
  ext y
  change (∃ k, RegularAtDim (n := n) (e ⁻¹' A) y k) ↔
    ∃ k, RegularAtDim (n := n) A (e y) k
  constructor
  · rintro ⟨k, hk⟩
    have h := regularAtDim_preimage_biholomorphic e.symm hei he
      (y := e y) (B := e ⁻¹' A) (k := k) (by simpa only [e.symm_apply_apply] using hk)
    have hdouble : e.symm ⁻¹' (e ⁻¹' A) = A := by
      ext z
      simp only [mem_preimage, e.apply_symm_apply]
    exact ⟨k, by simpa only [hdouble] using h⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, regularAtDim_preimage_biholomorphic e he hei hk⟩

/-- SAME actual regular component, by EXISTING homeomorphism component image
and the entire regular-locus equality; no new connectedness geometry. -/
theorem regularComponent_preimage_biholomorphic (e : M ≃ₜ N)
    (he : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e)
    (hei : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e.symm)
    (A : Set N) {c : N} (hc : c ∈ RegularLocusComponent.regularPoints (n := n) A) :
    RegularLocusComponent.component (n := n) (e ⁻¹' A) (e.symm c) =
      e ⁻¹' RegularLocusComponent.component (n := n) A c := by
  change connectedComponentIn (RegularLocusComponent.regularPoints (n := n) (e ⁻¹' A))
      (e.symm c) = e ⁻¹' connectedComponentIn (RegularLocusComponent.regularPoints (n := n) A) c
  have h := e.symm.image_connectedComponentIn hc
  simp only [e.image_symm] at h
  rw [← regularPoints_preimage_biholomorphic e he hei A] at h
  exact h.symm

private theorem globalComponents_preimage_biholomorphic (e : M ≃ₜ N)
    (he : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e)
    (hei : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e.symm)
    {A B : Set N} (hB : B ∈ GlobalComponents.globalComponents (n := n) A) :
    e ⁻¹' B ∈ GlobalComponents.globalComponents (n := n) (e ⁻¹' A) := by
  obtain ⟨c, hc, hB⟩ := hB
  refine ⟨e.symm c, ?_, ?_⟩
  · rw [regularPoints_preimage_biholomorphic e he hei A]
    change e (e.symm c) ∈ RegularLocusComponent.regularPoints (n := n) A
    simpa only [e.apply_symm_apply] using hc
  · rw [hB, e.preimage_closure, ← regularComponent_preimage_biholomorphic e he hei A hc]

/-- The ENTIRE actual global-component membership dictionary, including absent
components, follows literal regular-component closures in BOTH directions. -/
theorem globalComponents_preimage_iff_biholomorphic (e : M ≃ₜ N)
    (he : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e)
    (hei : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e.symm)
    (A B : Set N) :
    e ⁻¹' B ∈ GlobalComponents.globalComponents (n := n) (e ⁻¹' A) ↔
      B ∈ GlobalComponents.globalComponents (n := n) A := by
  constructor
  · intro h
    have hback := globalComponents_preimage_biholomorphic e.symm hei he h
    have hdouble (S : Set N) : e.symm ⁻¹' (e ⁻¹' S) = S := by
      ext z
      simp only [mem_preimage, e.apply_symm_apply]
    simpa only [hdouble] using hback
  · exact globalComponents_preimage_biholomorphic e he hei

section Coefficients
variable {m : ℕ} {X Y : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]

/-- Honest conditional ENTIRE-ideal comparison, including absent coefficient0.
Support is DERIVED FROM the full ideal equality and actual Cartier coherence;
subsequent original-input consumers must supply the full ideal equality internally. -/
theorem cartierGeometricPrimeCoefficient_biholomorphic_of_ideal_eq (e : X ≃ₜ Y)
    (he : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ e)
    (hei : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ e.symm)
    (D : EffectiveDivisor (m + 1) Y) (E : EffectiveDivisor (m + 1) X)
    (hideal : E.ideal = GermIdeal.pullback (m := m + 1) e D.ideal)
    (P : GeometricPrimeCarrier (m + 1) Y) :
    cartierGeometricPrimeCoefficient E (biholomorphic_geometricPrimeCarrier_preimage e he hei P) =
      cartierGeometricPrimeCoefficient D P := by
  classical
  let Q := biholomorphic_geometricPrimeCarrier_preimage e he hei P
  have hsupport : E.support = e ⁻¹' D.support := by
    change E.ideal.zeroLocus = e ⁻¹' D.ideal.zeroLocus
    rw [hideal, BlowupExceptionalDivisor.zeroLocus_pullback he
      (DivisorMetric.isCoherent_of_isInvertible D.isInvertible)]
  have hmem : Q.val ∈ GlobalComponents.globalComponents (n := m + 1) E.support ↔
      P.val ∈ GlobalComponents.globalComponents (n := m + 1) D.support := by
    rw [hsupport]
    exact globalComponents_preimage_iff_biholomorphic e he hei D.support P.val
  by_cases hP : P.val ∈ GlobalComponents.globalComponents (n := m + 1) D.support
  · have hQ := hmem.mpr hP
    let B : GlobalComponents.globalComponents (n := m + 1) D.support := ⟨P.val, hP⟩
    let C : GlobalComponents.globalComponents (n := m + 1) E.support := ⟨Q.val, hQ⟩
    obtain ⟨c, ⟨k, hc⟩, hB⟩ := B.property
    have hreg : RegularAtDim (n := m + 1) E.support (e.symm c) k := by
      rw [hsupport]
      apply regularAtDim_preimage_biholomorphic e he hei
      simpa only [e.apply_symm_apply] using hc
    have hC : C.val = closure (RegularLocusComponent.component (n := m + 1) E.support (e.symm c)) := by
      change e ⁻¹' P.val = _
      change P.val = closure (RegularLocusComponent.component (n := m + 1) D.support c) at hB
      rw [hB, e.preimage_closure,
        ← regularComponent_preimage_biholomorphic e he hei D.support ⟨k, hc⟩, ← hsupport]
    change cartierGeometricPrimeCoefficient E Q = cartierGeometricPrimeCoefficient D P
    unfold cartierGeometricPrimeCoefficient
    rw [dif_pos hQ, dif_pos hP]
    change regularComponentOrder E E.support C = regularComponentOrder D D.support B
    rw [regularComponentOrder_eq E E.support C hreg hC,
      regularComponentOrder_eq D D.support B hc hB, hideal, hsupport]
    simpa only [e.apply_symm_apply] using
      cartierOrder_pullback_biholomorphic e he hei D D.support (e.symm c)
  · have hQ : Q.val ∉ GlobalComponents.globalComponents (n := m + 1) E.support :=
      fun h => hP (hmem.mp h)
    change cartierGeometricPrimeCoefficient E Q = cartierGeometricPrimeCoefficient D P
    unfold cartierGeometricPrimeCoefficient
    rw [dif_neg hQ, dif_neg hP]

end Coefficients
end SGPT.PSH
