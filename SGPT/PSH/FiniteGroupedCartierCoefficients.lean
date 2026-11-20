import SGPT.PSH.GeometricQDivisorOpenRestriction

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open scoped Topology Manifold ContDiff

variable {m : ℕ} {M ι : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- A reusable finite reader for the ENTIRE actual same-carrier component
fiber, with every original index and absent-component zero retained. -/
theorem finite_grouped_cartier_component_coefficient
    (E : ι → EffectiveDivisor (m + 1) M) (w : ι → ℚ)
    (hLF : LocallyFinite (fun t : (i : ι) × GlobalComponents.globalComponents (n := m + 1) (E i).support =>
      (cartierComponentGeometricPrime (E t.1) t.2).val))
    (s : Finset ι) (A : GeometricPrimeCarrier (m + 1) M)
    (hs : ∀ t : (i : ι) × GlobalComponents.globalComponents (n := m + 1) (E i).support,
      cartierComponentGeometricPrime (E t.1) t.2 = A → t.1 ∈ s) :
    (∑ t ∈ (geometricPrimeCarrier_fiber_finite
      (fun t : (i : ι) × GlobalComponents.globalComponents (n := m + 1) (E i).support =>
        cartierComponentGeometricPrime (E t.1) t.2) hLF A).toFinset,
      w t.1 * (regularComponentOrder (E t.1) (E t.1).support t.2 : ℚ)) =
      ∑ i ∈ s, w i * (cartierGeometricPrimeCoefficient (E i) A : ℚ) := by
  classical
  let I := (i : ι) × GlobalComponents.globalComponents (n := m + 1) (E i).support
  let K : I → GeometricPrimeCarrier (m + 1) M := fun t => cartierComponentGeometricPrime (E t.1) t.2
  let T := (geometricPrimeCarrier_fiber_finite K hLF A).toFinset
  have hT (t : I) : t ∈ T ↔ K t = A := Set.Finite.mem_toFinset _
  have hval (t : I) (ht : t ∈ T) : t.2.val = A.val :=
    congrArg (fun P : GeometricPrimeCarrier (m + 1) M => P.val) ((hT t).mp ht)
  have hinj : Set.InjOn (fun t : I => t.1) T := by
    intro t ht v hv heq
    have htv := (hval t ht).trans (hval v hv).symm
    cases t with
    | mk i B =>
      cases v with
      | mk j C =>
        dsimp only at heq
        subst j
        congr 1
        exact Subtype.ext htv
  let J := T.image (fun t : I => t.1)
  have hJS : J ⊆ s := by
    intro i hi
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hi
    exact hs t ((hT t).mp ht)
  have hterm (t : I) (ht : t ∈ T) : regularComponentOrder (E t.1) (E t.1).support t.2 =
      cartierGeometricPrimeCoefficient (E t.1) A := by
    rw [← (hT t).mp ht]
    exact (cartierGeometricPrimeCoefficient_component (E t.1) t.2).symm
  have hzero (i : ι) (hiJ : i ∉ J) : cartierGeometricPrimeCoefficient (E i) A = 0 := by
    apply Nat.eq_zero_of_not_pos
    rw [cartierGeometricPrimeCoefficient_pos_iff]
    intro hmem
    let t : I := ⟨i, ⟨A.val, hmem⟩⟩
    have ht : t ∈ T := (hT t).mpr (GeometricPrimeCarrier.ext rfl)
    exact hiJ (Finset.mem_image.mpr ⟨t, ht, rfl⟩)
  change (∑ t ∈ T, w t.1 * (regularComponentOrder (E t.1) (E t.1).support t.2 : ℚ)) = _
  calc
    _ = ∑ t ∈ T, w t.1 * (cartierGeometricPrimeCoefficient (E t.1) A : ℚ) :=
      Finset.sum_congr rfl (fun t ht => by rw [hterm t ht])
    _ = ∑ i ∈ J, w i * (cartierGeometricPrimeCoefficient (E i) A : ℚ) :=
      (Finset.sum_image (f := fun i => w i * (cartierGeometricPrimeCoefficient (E i) A : ℚ)) hinj).symm
    _ = _ := Finset.sum_subset hJS (fun i _ hiJ => by rw [hzero i hiJ]; simp only [Nat.cast_zero, mul_zero])

/-- Original nearby geometry manufactures the finite-reader selection for
EVERY actual prime meeting the original open, including every split branch. -/
theorem geometricQDivisorOpenRestriction_local_coefficient
    (D : EffectiveGeometricQDivisor (m + 1) M) (U V : Opens M)
    (s : Finset {P // 0 < D.coefficient P})
    (hs : ∀ P, P ∈ s ↔ (P.val.val ∩ (V : Set M)).Nonempty)
    (A : GeometricPrimeCarrier (m + 1) U)
    (hA : (A.val ∩ (Subtype.val : U → M) ⁻¹' (V : Set M)).Nonempty) :
    (geometricQDivisorOpenRestriction D U).coefficient A =
      ∑ P ∈ s, D.coefficient P.val *
        (cartierGeometricPrimeCoefficient (cartierOpenRestriction
          (geometricPrimeCarrierEffectiveDivisor P.val) U) A : ℚ) := by
  let E := fun P : {P // 0 < D.coefficient P} =>
    cartierOpenRestriction (geometricPrimeCarrierEffectiveDivisor P.val) U
  have hselect (t : GeometricPrimeRestrictionIndex D U)
      (ht : cartierComponentGeometricPrime (E t.1) t.2 = A) : t.1 ∈ s := by
    obtain ⟨y, hyA, hyV⟩ := hA
    have hval : t.2.val = A.val := congrArg
      (fun P : GeometricPrimeCarrier (m + 1) U => P.val) ht
    have hyB : y ∈ t.2.val := by rw [hval]; exact hyA
    have hyP := GlobalComponents.subset_of_mem_globalComponents
      (cartierSupport_isComplexAnalytic (E t.1)) t.2.property hyB
    change y ∈ (cartierOpenRestriction (geometricPrimeCarrierEffectiveDivisor t.1.val) U).support at hyP
    rw [cartierOpenRestriction_support, geometricPrimeCarrierEffectiveDivisor_support] at hyP
    exact (hs t.1).mpr ⟨(y : M), hyP, hyV⟩
  unfold geometricQDivisorOpenRestriction
  rw [geometricQDivisorOfLocallyFiniteFamily_coefficient]
  exact finite_grouped_cartier_component_coefficient E (fun P => D.coefficient P.val)
    (locallyFinite_geometricPrimeRestrictionCarriers D U) s A hselect

end SGPT.PSH
