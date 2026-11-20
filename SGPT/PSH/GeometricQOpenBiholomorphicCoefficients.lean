import SGPT.PSH.NativeLogAnyDimension
import SGPT.PSH.BiholomorphicCartierCoefficients
import SGPT.PSH.FiniteGroupedCartierCoefficients
import Mathlib.Geometry.Manifold.Immersion

/-! Actual finite Cartier readback for rational open restrictions, and genuine
reduced-ideal transport in an original open biholomorphic square. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.SourceLogSingularitiesDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open scoped Topology Manifold ContDiff
universe u

variable {m : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m+1)) M] [IsComplexManifold (m+1) M]

/-- Every coefficient of the ORIGINAL rational open restriction is the finite
sum of actual restricted Cartier orders at the SAME internally chosen point.
This is the full coefficient, including coefficient0 and split primes. -/
theorem openRestriction_coefficient_finite_at_point
    (D : EffectiveGeometricQDivisor (m+1) M) (U : Opens M)
    (Q : GeometricPrimeCarrier (m+1) U) (q : U) (hq : q ∈ Q.val) :
    (geometricQDivisorOpenRestriction D U).coefficient Q =
      ∑ P ∈ (D.locallyFinite_positive.point_finite q.val).toFinset,
        D.coefficient P.val *
          (cartierGeometricPrimeCoefficient
            (cartierOpenRestriction (geometricPrimeCarrierEffectiveDivisor P.val) U) Q : ℚ) := by
  classical
  let I := {P // 0<D.coefficient P}
  let E : I → EffectiveDivisor (m+1) U :=
    fun P => cartierOpenRestriction (geometricPrimeCarrierEffectiveDivisor P.val) U
  let s := (D.locallyFinite_positive.point_finite q.val).toFinset
  have hs (P : I) : P ∈ s ↔ q.val ∈ P.val.val := Set.Finite.mem_toFinset _
  have hLF : LocallyFinite
      (fun t : (P : I) × GlobalComponents.globalComponents (n := m+1) (E P).support =>
        (cartierComponentGeometricPrime (E t.1) t.2).val) := by
    simpa only [GeometricPrimeRestrictionIndex,I,E,geometricPrimeRestrictionCarrier,
      cartierPrimeComponent_carrier,cartierComponentGeometricPrime] using
        locallyFinite_geometricPrimeRestrictionCarriers D U
  have hselect (t : (P : I) × GlobalComponents.globalComponents (n := m+1) (E P).support)
      (ht : cartierComponentGeometricPrime (E t.1) t.2=Q) : t.1 ∈ s := by
    have hval : t.2.val=Q.val := congrArg (fun P : GeometricPrimeCarrier (m+1) U => P.val) ht
    have hqB : q∈t.2.val := hval ▸ hq
    have hqE := GlobalComponents.subset_of_mem_globalComponents
      (cartierSupport_isComplexAnalytic (E t.1)) t.2.property hqB
    rw [show (E t.1).support=(Subtype.val : U → M) ⁻¹' t.1.val.val from
      (cartierOpenRestriction_support _ _).trans
        (congrArg (fun S : Set M => (Subtype.val : U → M) ⁻¹' S)
          (geometricPrimeCarrierEffectiveDivisor_support t.1.val))] at hqE
    exact (hs t.1).mpr hqE
  rw [geometricQDivisorOpenRestriction,geometricQDivisorOfLocallyFiniteFamily_coefficient]
  simpa only [GeometricPrimeRestrictionIndex,I,E,geometricPrimeRestrictionCarrier,
    geometricPrimeRestrictionContribution,cartierPrimeComponent_carrier,
    cartierComponentGeometricPrime] using
      finite_grouped_cartier_component_coefficient E (fun P => D.coefficient P.val) hLF s Q hselect

section OpenBiholomorphic
variable {n : ℕ} {N : Type u}
  [TopologicalSpace N] [ChartedSpace (ComplexModel n) N] [IsComplexManifold n N]
  {L : Type u} [TopologicalSpace L]
  [ChartedSpace (ComplexModel n) L] [IsComplexManifold n L]

/-- The SAME actual inverse-image open, with its ordinary inherited native
manifold structures. -/
def preimageOpen (e : L ≃ₜ N) (V : Opens N) : Opens L :=
  ⟨e ⁻¹' (V : Set N),V.isOpen.preimage e.continuous⟩

/-- The literal restriction of the genuine biholomorphism, not a supplied
open-map/inverse certificate. -/
def openHomeomorph (e : L ≃ₜ N) (V : Opens N) : preimageOpen e V ≃ₜ V :=
  e.subtype (fun _ => Iff.rfl)

omit [IsComplexManifold n L] in
lemma openHomeomorph_contMDiff (e : L ≃ₜ N) (V : Opens N)
    (he : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ e) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (openHomeomorph e V) := by
  apply (ContMDiff.iff_comp_isImmersionOfComplement
    (Manifold.IsImmersionOfComplement.of_opens.{0,0,0,u,0} V)).mpr
  exact ⟨(openHomeomorph e V).continuous,he.comp contMDiff_subtype_val⟩

omit [IsComplexManifold n N] in
lemma openHomeomorph_symm_contMDiff (e : L ≃ₜ N) (V : Opens N)
    (hei : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ e.symm) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (openHomeomorph e V).symm := by
  apply (ContMDiff.iff_comp_isImmersionOfComplement
    (Manifold.IsImmersionOfComplement.of_opens.{0,0,0,u,0} (preimageOpen e V))).mpr
  exact ⟨(openHomeomorph e V).symm.continuous,hei.comp contMDiff_subtype_val⟩

end OpenBiholomorphic

section ReducedSquare
variable {N : Type u} [TopologicalSpace N]
  [ChartedSpace (ComplexModel (m+1)) N] [IsComplexManifold (m+1) N]

/-- The actual open/biholomorphic square preserves the ENTIRE reduced Cartier
ideal at every stalk. Its full ideal equality is proved, not supplied. -/
theorem openPrime_reduced_ideal_square (e : M ≃ₜ N) (V : Opens N)
    (he : ContMDiff 𝓘(ℂ,ComplexModel (m+1)) 𝓘(ℂ,ComplexModel (m+1)) ∞ e)
    (hei : ContMDiff 𝓘(ℂ,ComplexModel (m+1)) 𝓘(ℂ,ComplexModel (m+1)) ∞ e.symm)
    (P : GeometricPrimeCarrier (m+1) N) :
    (cartierOpenRestriction
      (geometricPrimeCarrierEffectiveDivisor
        (biholomorphic_geometricPrimeCarrier_preimage e he hei P))
      (preimageOpen e V)).ideal =
      GermIdeal.pullback (m := m+1) (openHomeomorph e V)
        (cartierOpenRestriction (geometricPrimeCarrierEffectiveDivisor P) V).ideal := by
  let f := openHomeomorph e V
  have hf := openHomeomorph_contMDiff e V he
  have hfi := openHomeomorph_symm_contMDiff e V hei
  have hsets :
      (Subtype.val : preimageOpen e V → M) ⁻¹'
        (biholomorphic_geometricPrimeCarrier_preimage e he hei P).val =
      f ⁻¹' ((Subtype.val : V → N) ⁻¹' P.val) := by
    rw [biholomorphic_geometricPrimeCarrier_preimage_carrier]
    rfl
  have hcoh : (vanishingIdeal (n := m+1)
      (f ⁻¹' ((Subtype.val : V → N) ⁻¹' P.val))).IsCoherent := by
    rw [←hsets,←geometricPrimeOpenRestriction_ideal]
    exact DivisorMetric.isCoherent_of_isInvertible
      (cartierOpenRestriction (geometricPrimeCarrierEffectiveDivisor
        (biholomorphic_geometricPrimeCarrier_preimage e he hei P))
        (preimageOpen e V)).isInvertible
  have h := MarkedIdealBiholomorphism.pullback_vanishingIdeal_preimage
    hf hfi f.apply_symm_apply f.symm_apply_apply (g := id) contMDiff_id
      ((Subtype.val : V → N) ⁻¹' P.val)
  rw [Function.comp_id,BlowupControlledTransform.pullback_id hcoh] at h
  rw [geometricPrimeOpenRestriction_ideal,geometricPrimeOpenRestriction_ideal,hsets]
  exact h

/-- EVERY actual local prime retains its real Cartier order in the SAME
open/biholomorphic square, including order0 and singular reduced stalks. -/
theorem openPrime_cartier_coefficient_square (e : M ≃ₜ N) (V : Opens N)
    (he : ContMDiff 𝓘(ℂ,ComplexModel (m+1)) 𝓘(ℂ,ComplexModel (m+1)) ∞ e)
    (hei : ContMDiff 𝓘(ℂ,ComplexModel (m+1)) 𝓘(ℂ,ComplexModel (m+1)) ∞ e.symm)
    (P : GeometricPrimeCarrier (m+1) N) (Q : GeometricPrimeCarrier (m+1) V) :
    cartierGeometricPrimeCoefficient
      (cartierOpenRestriction (geometricPrimeCarrierEffectiveDivisor
        (biholomorphic_geometricPrimeCarrier_preimage e he hei P)) (preimageOpen e V))
      (biholomorphic_geometricPrimeCarrier_preimage (openHomeomorph e V)
        (openHomeomorph_contMDiff e V he) (openHomeomorph_symm_contMDiff e V hei) Q) =
      cartierGeometricPrimeCoefficient
        (cartierOpenRestriction (geometricPrimeCarrierEffectiveDivisor P) V) Q :=
  cartierGeometricPrimeCoefficient_biholomorphic_of_ideal_eq
    (openHomeomorph e V) (openHomeomorph_contMDiff e V he)
    (openHomeomorph_symm_contMDiff e V hei)
    (cartierOpenRestriction (geometricPrimeCarrierEffectiveDivisor P) V) _
    (openPrime_reduced_ideal_square e V he hei P) Q

end ReducedSquare
end SGPT.PSH.SourceLogSingularitiesDraft
