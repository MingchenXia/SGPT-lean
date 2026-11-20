import SGPT.Unibranch.HironakaG10PointCentreStrictIdealSaturation
import SGPT.Foundations.Analysis.Pending.HironakaSmoothCentreRealDomainActualSheafStalk

/-! Transport the ENTIRE nonreduced ideal saturation from a chart to a native
structure-sheaf stalk. The ring equivalence and the pullback-ideal identity are
explicit inputs: this file does not construct a blowup chart or identify its
strict ideal with any independently defined geometric strict transform. -/
set_option autoImplicit false
open Set
open scoped Topology Manifold ContDiff
namespace SGPT.Unibranch.HironakaG10NativeStalkSaturationTransport
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
  HolGerm HironakaSmoothCentreRealDomainActualSheafStalk
noncomputable section

/-- Given the actual pullback ideal and a ring equivalence, the whole
pivot-saturation (including all nilpotents) and quotient regularity descend to
the original ring. No properness or radicality assumption is needed. -/
theorem ringEquiv_saturation_to_native_quotient
    {R S : Type*} [CommRing R] [CommRing S]
    (E : R ≃+* S) (I : Ideal R) (T N : Ideal S) (t : R)
    (hT : Ideal.map E.toRingHom I = T)
    (hN : ∀ y : S, y ∈ N ↔ ∃ q : ℕ, (E t)^q * y ∈ T) :
    let J := N.comap E.toRingHom
    Ideal.map E.toRingHom J = N ∧
    (∀ x : R, x ∈ J ↔ ∃ q : ℕ, t^q * x ∈ I) ∧
    (∀ x : R, t*x ∈ J ↔ x ∈ J) ∧
    IsRegular (Ideal.Quotient.mk J t) := by
  let J := N.comap E.toRingHom
  have hmap : Ideal.map E.toRingHom J = N :=
    Ideal.map_comap_of_surjective E.toRingHom E.surjective N
  have hmem (x : R) : E x ∈ T ↔ x ∈ I := by
    rw [← hT, Ideal.mem_map_iff_of_surjective E.toRingHom E.surjective]
    constructor
    · rintro ⟨y,hy,he⟩
      have h : y = x := E.injective he
      simpa only [h] using hy
    · intro hx
      exact ⟨x,hx,rfl⟩
  have hwhole : ∀ x : R, x ∈ J ↔ ∃ q : ℕ, t^q*x ∈ I := by
    intro x
    change E x ∈ N ↔ _
    rw [hN]
    constructor
    · rintro ⟨q,hq⟩
      refine ⟨q, (hmem (t^q*x)).mp ?_⟩
      simpa only [map_mul, map_pow] using hq
    · rintro ⟨q,hq⟩
      refine ⟨q, ?_⟩
      have he := (hmem (t^q*x)).mpr hq
      simpa only [map_mul, map_pow] using he
  have hpivot : ∀ x : R, t*x ∈ J ↔ x ∈ J := by
    intro x
    constructor
    · intro hx
      obtain ⟨q,hq⟩ := (hwhole (t*x)).mp hx
      apply (hwhole x).mpr
      refine ⟨q+1, ?_⟩
      simpa only [pow_succ, mul_assoc] using hq
    · exact fun hx => J.mul_mem_left t hx
  have hregular : IsRegular (Ideal.Quotient.mk J t) := by
    rw [isRegular_iff_eq_zero_of_mul]
    have h : ∀ x : R ⧸ J, Ideal.Quotient.mk J t*x=0 → x=0 := by
      intro x hx
      obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hx
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact (hpivot x).mp hx
    exact ⟨h, fun x hx => h x (by rw [mul_comm]; exact hx)⟩
  exact ⟨hmap,hwhole,hpivot,hregular⟩

/-- Literal structure-sheaf-stalk instance. E must identify the actual
native pullback stalk ideal with T and take the stated native pivot to the
chart pivot; those identities are not inferred from the topological support. -/
theorem actual_structure_stalk_saturation_quotient_regular
    {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] (x : M)
    (E : actualComplexStructureStalk (n := n) x ≃+* HolGerm (ComplexModel n))
    (I : Ideal (actualComplexStructureStalk (n := n) x))
    (T N : Ideal (HolGerm (ComplexModel n))) (t : actualComplexStructureStalk (n := n) x)
    (hT : Ideal.map E.toRingHom I = T)
    (hN : ∀ y : HolGerm (ComplexModel n), y ∈ N ↔ ∃ q : ℕ, (E t)^q*y ∈ T) :
    let J := N.comap E.toRingHom
    Ideal.map E.toRingHom J = N ∧
    (∀ z, z ∈ J ↔ ∃ q : ℕ, t^q*z ∈ I) ∧
    (∀ z, t*z ∈ J ↔ z ∈ J) ∧
    IsRegular (Ideal.Quotient.mk J t) :=
  ringEquiv_saturation_to_native_quotient E I T N t hT hN
end
end SGPT.Unibranch.HironakaG10NativeStalkSaturationTransport
