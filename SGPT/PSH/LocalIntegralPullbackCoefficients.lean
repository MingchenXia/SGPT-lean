import SGPT.PSH.GeometricQDivisorPullback
import SGPT.PSH.CanonicalCartierAdditivity

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending HironakaEffectiveDivisorSum
open scoped Topology Manifold ContDiff Classical

universe u
variable {m : ℕ} {X Y : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
  {π : Y → X}

/-- The ENTIRE grouped raw fiber projects injectively into the EXACT original
nearby family. All absent actual transformed components contribute literal zero. -/
theorem geometricQDivisorModificationPullback_local_coefficient
    (D : EffectiveGeometricQDivisor (m + 1) X)
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
    (U : Opens X) (s : Finset {P // 0 < D.coefficient P})
    (hs : ∀ P, P ∈ s ↔ (P.val.val ∩ (U : Set X)).Nonempty)
    (A : GeometricPrimeCarrier (m + 1) Y)
    (hA : (A.val ∩ π ⁻¹' (U : Set X)).Nonempty) :
    (geometricQDivisorModificationPullback D hπ).coefficient A =
      ∑ P ∈ s, D.coefficient P.val *
        (cartierGeometricPrimeCoefficient (geometricPrimeCarrierTotalTransform P.val hπ) A : ℚ) := by
  classical
  let T := (geometricPrimeCarrier_fiber_finite (geometricPrimeTransformCarrier D hπ)
    (locallyFinite_geometricPrimeTransformCarriers D hπ) A).toFinset
  have hT (t : GeometricPrimeTransformIndex D hπ) :
      t ∈ T ↔ geometricPrimeTransformCarrier D hπ t = A := Set.Finite.mem_toFinset _
  have hval (t : GeometricPrimeTransformIndex D hπ) (ht : t ∈ T) : t.2.val = A.val := by
    have h := congrArg (fun P : GeometricPrimeCarrier (m + 1) Y => P.val) ((hT t).mp ht)
    change (cartierPrimeComponent (geometricPrimeCarrierTotalTransform t.1.val hπ) t.2).carrier = A.val at h
    rwa [cartierPrimeComponent_carrier] at h
  have hinj : Set.InjOn (fun t : GeometricPrimeTransformIndex D hπ => t.1) T := by
    intro t ht v hv heq
    have htv := (hval t ht).trans (hval v hv).symm
    cases t with
    | mk P B =>
      cases v with
      | mk Q C =>
        dsimp only at heq
        subst Q
        congr 1
        exact Subtype.ext htv
  let J := T.image (fun t : GeometricPrimeTransformIndex D hπ => t.1)
  have hJS : J ⊆ s := by
    intro P hP
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hP
    obtain ⟨y, hyA, hyU⟩ := hA
    have hyB : y ∈ t.2.val := by rw [hval t ht]; exact hyA
    have hyΔ := GlobalComponents.subset_of_mem_globalComponents
      (cartierSupport_isComplexAnalytic (geometricPrimeCarrierTotalTransform t.1.val hπ)) t.2.property hyB
    rw [geometricPrimeCarrierTotalTransform_support] at hyΔ
    exact (hs t.1).mpr ⟨π y, hyΔ, hyU⟩
  have hterm (t : GeometricPrimeTransformIndex D hπ) (ht : t ∈ T) :
      regularComponentOrder (geometricPrimeCarrierTotalTransform t.1.val hπ)
          (geometricPrimeCarrierTotalTransform t.1.val hπ).support t.2 =
        cartierGeometricPrimeCoefficient (geometricPrimeCarrierTotalTransform t.1.val hπ) A := by
    have hcomp : cartierComponentGeometricPrime (geometricPrimeCarrierTotalTransform t.1.val hπ) t.2 = A :=
      GeometricPrimeCarrier.ext (hval t ht)
    rw [← hcomp, cartierGeometricPrimeCoefficient_component]
  have hzero (P : {P // 0 < D.coefficient P}) (hPJ : P ∉ J) :
      cartierGeometricPrimeCoefficient (geometricPrimeCarrierTotalTransform P.val hπ) A = 0 := by
    apply Nat.eq_zero_of_not_pos
    rw [cartierGeometricPrimeCoefficient_pos_iff]
    intro hmem
    let B : GlobalComponents.globalComponents (n := m + 1)
        (geometricPrimeCarrierTotalTransform P.val hπ).support := ⟨A.val, hmem⟩
    let t : GeometricPrimeTransformIndex D hπ := ⟨P, B⟩
    have ht : t ∈ T := (hT t).mpr (GeometricPrimeCarrier.ext (by
      change (cartierPrimeComponent (geometricPrimeCarrierTotalTransform P.val hπ) B).carrier = A.val
      rw [cartierPrimeComponent_carrier]))
    exact hPJ (Finset.mem_image.mpr ⟨t, ht, rfl⟩)
  rw [geometricQDivisorModificationPullback_coefficient]
  change (∑ t ∈ T, D.coefficient t.1.val *
      (regularComponentOrder (geometricPrimeCarrierTotalTransform t.1.val hπ)
        (geometricPrimeCarrierTotalTransform t.1.val hπ).support t.2 : ℚ)) = _
  calc
    _ = ∑ t ∈ T, D.coefficient t.1.val *
        (cartierGeometricPrimeCoefficient (geometricPrimeCarrierTotalTransform t.1.val hπ) A : ℚ) :=
      Finset.sum_congr rfl (fun t ht => by rw [hterm t ht])
    _ = ∑ P ∈ J, D.coefficient P.val *
        (cartierGeometricPrimeCoefficient (geometricPrimeCarrierTotalTransform P.val hπ) A : ℚ) :=
      (Finset.sum_image (f := fun P : {P // 0 < D.coefficient P} => D.coefficient P.val *
        (cartierGeometricPrimeCoefficient (geometricPrimeCarrierTotalTransform P.val hπ) A : ℚ)) hinj).symm
    _ = _ := Finset.sum_subset hJS (fun P _ hPJ => by rw [hzero P hPJ]; simp only [Nat.cast_zero, mul_zero])

/-- ORIGINAL D,x and actual modification ALONE produce the SAME exact nearby
original indices/local denominator and a genuine finite transformed Cartier sum
whose EVERY meeting canonical coefficient matches the global grouped pullback. -/
theorem exists_geometric_q_local_integral_pullback_coefficients
    (D : EffectiveGeometricQDivisor (m + 1) X) (x : X)
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π) :
    ∃ U : Opens X, x ∈ U ∧
      ∃ (s : Finset {P // 0 < D.coefficient P}) (d : ℕ)
        (a : {P // 0 < D.coefficient P} → ℕ),
        (∀ P, P ∈ s ↔ (P.val.val ∩ (U : Set X)).Nonempty) ∧ 0 < d ∧
        (∀ P ∈ s, 0 < a P ∧ D.coefficient P.val = (a P : ℚ) / (d : ℚ)) ∧
        let H := ∑ P ∈ s, a P • geometricPrimeCarrierTotalTransform P.val hπ
        ∀ A : GeometricPrimeCarrier (m + 1) Y,
          (A.val ∩ π ⁻¹' (U : Set X)).Nonempty →
          (geometricQDivisorModificationPullback D hπ).coefficient A =
            (cartierGeometricPrimeCoefficient H A : ℚ) / (d : ℚ) := by
  obtain ⟨U, hxU, s, d, a, _g, hs, hd, ha, _hgens, _hrest⟩ :=
    exists_geometric_q_local_integral_cartier_presentation D x
  refine ⟨U, hxU, s, d, a, hs, hd, ha, ?_⟩
  dsimp only
  intro A hA
  rw [geometricQDivisorModificationPullback_local_coefficient D hπ U s hs A hA,
    cartierGeometricPrimeCoefficient_finset_sum, Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro P hP
  rw [(ha P hP).2, Nat.cast_mul]
  ring

end SGPT.PSH
