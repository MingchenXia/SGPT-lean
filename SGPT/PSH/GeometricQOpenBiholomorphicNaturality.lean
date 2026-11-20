import SGPT.PSH.GeometricQOpenBiholomorphicCoefficients

/-! Actual rational coefficients commute with the genuine open restriction
of a biholomorphism. This is a proved full-divisor identity. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.SourceLogSingularitiesDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff
universe u
variable {n : ℕ} {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [ChartedSpace (ComplexModel n) N] [IsComplexManifold n N]

private def positivePrimeEquiv (D : EffectiveGeometricQDivisor n N) (e : M ≃ₜ N)
    (he : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ e)
    (hei : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ e.symm) :
    {P // 0<D.coefficient P} ≃
      {Q // 0<(geometricQDivisorBiholomorphicPreimage D e he hei).coefficient Q} := by
  let K := biholomorphic_geometricPrimeCarrier_equiv e he hei
  refine {
    toFun := fun P => ⟨K P.val,?_⟩
    invFun := fun Q => ⟨K.symm Q.val,Q.property⟩
    left_inv := fun P => Subtype.ext (K.symm_apply_apply P.val)
    right_inv := fun Q => Subtype.ext (K.apply_symm_apply Q.val) }
  change 0<D.coefficient (K.symm (K P.val))
  rw [K.symm_apply_apply]
  exact P.property

private theorem positivePrime_finite_at_point (D : EffectiveGeometricQDivisor n N)
    (e : M ≃ₜ N)
    (he : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ e)
    (hei : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ e.symm) (q : M) :
    ((geometricQDivisorBiholomorphicPreimage D e he hei).locallyFinite_positive.point_finite q).toFinset =
      (D.locallyFinite_positive.point_finite (e q)).toFinset.map
        (positivePrimeEquiv D e he hei).toEmbedding := by
  classical
  let K := biholomorphic_geometricPrimeCarrier_equiv e he hei
  let J := positivePrimeEquiv D e he hei
  ext Q
  have hcarrier : e ⁻¹' (K.symm Q.val).val=Q.val.val :=
    congrArg (fun P : GeometricPrimeCarrier n M => P.val) (K.apply_symm_apply Q.val)
  have hsource (P : {P // 0<D.coefficient P}) :
      P∈(D.locallyFinite_positive.point_finite (e q)).toFinset ↔ e q∈P.val.val :=
    Set.Finite.mem_toFinset _
  have htarget (R : {Q // 0<(geometricQDivisorBiholomorphicPreimage D e he hei).coefficient Q}) :
      R∈((geometricQDivisorBiholomorphicPreimage D e he hei).locallyFinite_positive.point_finite q).toFinset ↔
        q∈R.val.val := Set.Finite.mem_toFinset _
  constructor
  · intro hQ
    have hq : q∈Q.val.val := (htarget Q).mp hQ
    apply Finset.mem_map.mpr
    refine ⟨J.symm Q,?_,J.apply_symm_apply Q⟩
    apply (hsource (J.symm Q)).mpr
    change e q∈(K.symm Q.val).val
    rwa [←hcarrier] at hq
  · intro hQ
    obtain ⟨P,hP,hPQ⟩ := Finset.mem_map.mp hQ
    have hp : e q∈P.val.val := (hsource P).mp hP
    apply (htarget Q).mpr
    have h : J P=Q := hPQ
    rw [←h]
    change q∈(K P.val).val
    exact hp

private theorem qdiv_ext {D E : EffectiveGeometricQDivisor n M}
    (h : ∀ P,D.coefficient P=E.coefficient P) : D=E := by
  cases D
  cases E
  have hc := funext h
  cases hc
  rfl

/-- The ENTIRE existing rational open restriction commutes with the genuine
biholomorphic square. All split/zero coefficients are proved from actual
finite local Cartier orders; no compatibility certificate is an input. -/
theorem openRestriction_biholomorphic_naturality
    (D : EffectiveGeometricQDivisor n N) (e : M ≃ₜ N) (V : Opens N)
    (he : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ e)
    (hei : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ e.symm) :
    geometricQDivisorOpenRestrictionAnyDimension
      (geometricQDivisorBiholomorphicPreimage D e he hei) (preimageOpen e V) =
    geometricQDivisorBiholomorphicPreimage
      (geometricQDivisorOpenRestrictionAnyDimension D V) (openHomeomorph e V)
      (openHomeomorph_contMDiff e V he) (openHomeomorph_symm_contMDiff e V hei) := by
  apply qdiv_ext
  intro Q
  cases n with
  | zero => exact isEmptyElim Q
  | succ m =>
    classical
    let K := biholomorphic_geometricPrimeCarrier_equiv e he hei
    let J := positivePrimeEquiv D e he hei
    let f := openHomeomorph e V
    let hf := openHomeomorph_contMDiff e V he
    let hfi := openHomeomorph_symm_contMDiff e V hei
    let Kf := biholomorphic_geometricPrimeCarrier_equiv f hf hfi
    let P := Kf.symm Q
    obtain ⟨q,hq⟩ := Q.nonempty
    have hqP : f q∈P.val := by
      have hcarrier : f ⁻¹' P.val=Q.val :=
        congrArg (fun A : GeometricPrimeCarrier (m+1) (preimageOpen e V) => A.val)
          (Kf.apply_symm_apply Q)
      rwa [←hcarrier] at hq
    change (geometricQDivisorOpenRestriction
      (geometricQDivisorBiholomorphicPreimage D e he hei) (preimageOpen e V)).coefficient Q =
        (geometricQDivisorOpenRestriction D V).coefficient P
    rw [openRestriction_coefficient_finite_at_point _ _ Q q hq,
      openRestriction_coefficient_finite_at_point D V P (f q) hqP,
      positivePrime_finite_at_point D e he hei q.val,Finset.sum_map]
    apply Finset.sum_congr rfl
    intro R _hR
    change (geometricQDivisorBiholomorphicPreimage D e he hei).coefficient (K R.val) *
      (cartierGeometricPrimeCoefficient
        (cartierOpenRestriction (geometricPrimeCarrierEffectiveDivisor (K R.val))
          (preimageOpen e V)) Q : ℚ) = _
    have horder := openPrime_cartier_coefficient_square e V he hei R.val P
    change cartierGeometricPrimeCoefficient
      (cartierOpenRestriction (geometricPrimeCarrierEffectiveDivisor (K R.val))
        (preimageOpen e V)) (Kf P) = _ at horder
    rw [show Kf P=Q from Kf.apply_symm_apply Q] at horder
    have hweight : (geometricQDivisorBiholomorphicPreimage D e he hei).coefficient (K R.val)=
        D.coefficient R.val := by
      change D.coefficient (K.symm (K R.val))=D.coefficient R.val
      rw [K.symm_apply_apply]
    rw [hweight,horder]

end SGPT.PSH.SourceLogSingularitiesDraft
