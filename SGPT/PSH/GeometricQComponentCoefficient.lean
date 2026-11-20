import SGPT.PSH.AtlasLogRangePrime

/-! Actual whole-component rational restriction retains every original
prime coefficient, proved from full Cartier ideals and finite-at-point orders. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas.SourceLogReverseDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.PSH.SourceLogSingularitiesDraft
open SGPT.PSH.VariableComplexAtlas.SourceLogTransportDraft
open scoped Topology Manifold ContDiff Classical
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

private theorem prime_subset_component_of_mem (P : GeometricPrimeCarrier n M)
    (q z : M) (hzP : z∈P.val) (hzC : z∈connectedComponent q) :
    P.val⊆connectedComponent q := by
  have hc : IsPreconnected P.val := by
    rw [←P.subvariety_carrier]
    exact CodimOneSupport.isPreconnected_of_isComplexAnalyticallyIrreducible P.subvariety.irreducible_carrier
  intro y hy
  have h := hc.subset_connectedComponent hzP hy
  rwa [←connectedComponent_eq hzC] at h

section Cartier
variable {m : ℕ} {N : Type u} [TopologicalSpace N]
  [ChartedSpace (ComplexModel (m+1)) N] [IsComplexManifold (m+1) N]

/-- Full reduced ideals make the actual whole-carrier clopen restriction
of an original prime have EXACT Kronecker order at any actual restricted
prime, retaining zero orders and every singular reduced scalar stalk. -/
theorem cartierPrimeOpen_coefficient_of_whole_carriers
    (P R : GeometricPrimeCarrier (m+1) N) (U : Opens N) (hU : IsClopen (U : Set N))
    (hP : P.val⊆(U : Set N)) (hR : R.val⊆(U : Set N))
    (PC : GeometricPrimeCarrier (m+1) U)
    (hPC : PC.val=(Subtype.val : U → N) ⁻¹' P.val) :
    cartierGeometricPrimeCoefficient
      (cartierOpenRestriction (geometricPrimeCarrierEffectiveDivisor R) U) PC=
      if P=R then 1 else 0 := by
  obtain ⟨RC,hRC⟩ := exists_prime_on_clopen_of_subset R U hU hR
  have hCartier : cartierOpenRestriction (geometricPrimeCarrierEffectiveDivisor R) U=
      geometricPrimeCarrierEffectiveDivisor RC := by
    apply HironakaEffectiveDivisorSum.effectiveDivisor_eq_of_ideal_eq
    rw [geometricPrimeOpenRestriction_ideal,geometricPrimeCarrierEffectiveDivisor_ideal,hRC]
  rw [hCartier,cartierGeometricPrimeCoefficient_reduced]
  have hEq : PC=RC ↔ P=R := by
    constructor
    · intro h
      apply GeometricPrimeCarrier.ext
      have hpre : (Subtype.val : U → N) ⁻¹' P.val=(Subtype.val : U → N) ⁻¹' R.val :=
        (hPC.symm.trans (congrArg Subtype.val h)).trans hRC
      ext z
      constructor
      · intro hz
        have hm : (⟨z,hP hz⟩ : U)∈(Subtype.val : U → N) ⁻¹' R.val := by
          rw [←hpre]
          exact hz
        exact hm
      · intro hz
        have hm : (⟨z,hR hz⟩ : U)∈(Subtype.val : U → N) ⁻¹' P.val := by
          rw [hpre]
          exact hz
        exact hm
    · intro h
      subst R
      exact GeometricPrimeCarrier.ext (hPC.trans hRC.symm)
  simp only [hEq]

end Cartier

/-- Every coefficient of a rational divisor is retained on the actual
whole connected component containing that prime. Local finiteness chooses
only actual primes through an actual point, and full reduced ideals prove
their orders; no desired coefficient identity is an input. -/
theorem geometricQOpen_component_coefficient (D : EffectiveGeometricQDivisor n M)
    (q : M) (P : GeometricPrimeCarrier n M)
    (PC : GeometricPrimeCarrier n (nativeConnectedOpen (n := n) q))
    (hPC : PC.val=(Subtype.val : nativeConnectedOpen (n := n) q → M) ⁻¹' P.val) :
    (geometricQDivisorOpenRestrictionAnyDimension D (nativeConnectedOpen (n := n) q)).coefficient PC=
      D.coefficient P := by
  cases n with
  | zero => exact isEmptyElim P
  | succ m =>
    let C := nativeConnectedOpen (n := m+1) q
    obtain ⟨z,hz⟩ := PC.nonempty
    have hzP : z.val∈P.val := by rwa [hPC] at hz
    have hP : P.val⊆(C : Set M) := prime_subset_component_of_mem P q z.val hzP z.property
    have hC : IsClopen (C : Set M) := ⟨isClosed_connectedComponent,C.isOpen⟩
    let s := (D.locallyFinite_positive.point_finite z.val).toFinset
    have hs (R : {R // 0<D.coefficient R}) : R∈s ↔ z.val∈R.val.val := Set.Finite.mem_toFinset _
    have horder (R : {R // 0<D.coefficient R}) (hR : R∈s) :
        cartierGeometricPrimeCoefficient
          (cartierOpenRestriction (geometricPrimeCarrierEffectiveDivisor R.val) C) PC=
          if P=R.val then 1 else 0 :=
      cartierPrimeOpen_coefficient_of_whole_carriers P R.val C hC hP
        (prime_subset_component_of_mem R.val q z.val ((hs R).mp hR) z.property) PC hPC
    change (geometricQDivisorOpenRestriction D C).coefficient PC=D.coefficient P
    rw [openRestriction_coefficient_finite_at_point D C PC z hz]
    change (∑ R∈s,D.coefficient R.val *
      (cartierGeometricPrimeCoefficient
        (cartierOpenRestriction (geometricPrimeCarrierEffectiveDivisor R.val) C) PC : ℚ))=D.coefficient P
    have hsum : (∑ R∈s,D.coefficient R.val *
      (cartierGeometricPrimeCoefficient
        (cartierOpenRestriction (geometricPrimeCarrierEffectiveDivisor R.val) C) PC : ℚ))=
        ∑ R∈s,if R.val=P then D.coefficient P else 0 := by
      apply Finset.sum_congr rfl
      intro R hR
      rw [horder R hR]
      by_cases h : R.val=P
      · simp [h]
      · simp [h,Ne.symm h]
    rw [hsum]
    by_cases hpos : 0<D.coefficient P
    · let PP : {P // 0<D.coefficient P} := ⟨P,hpos⟩
      have hPP : PP∈s := (hs PP).mpr hzP
      rw [Finset.sum_eq_single PP]
      · simp [PP]
      · intro R _ hne
        have hRP : R.val≠P := fun h => hne (Subtype.ext h)
        simp [hRP]
      · intro hnot
        exact False.elim (hnot hPP)
    · have hzero : D.coefficient P=0 := le_antisymm (le_of_not_gt hpos) (D.coefficient_nonneg P)
      simp [hzero]

end SGPT.PSH.VariableComplexAtlas.SourceLogReverseDraft
