import SGPT.PSH.LogResolution
import SGPT.Foundations.Analysis.Pending.CodimOneSupport
import SGPT.Foundations.Analysis.Pending.StrictTransformLocus
import SGPT.Foundations.Analysis.Pending.AnalyticSubsetPreimage
import SGPT.Foundations.Analysis.Pending.CodimOneAdmissibleAlong

/-!
# Simple normal crossing divisors: support form and component form

Source: `chapter_pshfunctions.tex`, `def:logres` ("simple normal crossing effective
`ℚ`-divisor").  The project's definition `EffectiveGeometricQDivisor.IsSNC` is the support form
(Bierstone--Milman): the support is the union of a locally finite family of closed sets which,
at every point, are distinct coordinate hyperplanes of one holomorphic coordinate system.  The
other usual form is stated on the prime components:

* `IsSNCComponentwise D`: at every point `x`, the prime components of `D` (positive coefficient)
  passing through `x` are, near `x`, DISTINCT coordinate hyperplanes of one holomorphic
  coordinate system centred at `x`; in particular every prime component is smooth and the
  components cross transversally.
* `isSNC_iff_isSNCComponentwise`: the two forms are equivalent.  The non-trivial direction uses
  that an irreducible hypersurface contained in a locally finite union of smooth hypersurfaces
  lies in one of them (Baire and the identity theorem, TN's
  `exists_subset_of_inter_isOpen_subset_iUnion`), and then coincides with it near each of its
  points (TN's filling lemma `eventually_mem_iff_of_regularAtDim_of_locDimGE`, with the pure
  dimensionality `locDimGE_carrier` of irreducible subvarieties); two prime components which agree
  near a point are equal (`subset_of_inter_isOpen_subset`).
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.EffectiveGeometricQDivisor

open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.NormalCrossings
open scoped Topology Manifold ContDiff

universe u

/-- Source `def:logres`, component form of "simple normal crossing": at every point `x` the prime
components of `D` (those with positive coefficient) through `x` are, near `x`, distinct coordinate
hyperplanes of one holomorphic coordinate system centred at `x` (each prime component is smooth
and the components cross normally). -/
def IsSNCComponentwise {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (D : EffectiveGeometricQDivisor n M) : Prop :=
  ∀ x : M, ∃ S : {P : GeometricPrimeCarrier n M // 0 < D.coefficient P} → Finset (Fin n),
    IsCoordinateFamilyAt n (fun P => P.val.val) S x ∧
      (∀ P, x ∈ P.val.val → (S P).card = 1) ∧ InjOn S {P | x ∈ P.val.val}

/-- The component form implies the support form (the family of prime components itself). -/
theorem isSNC_of_isSNCComponentwise {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {D : EffectiveGeometricQDivisor n M} (h : D.IsSNCComponentwise) : D.IsSNC := by
  refine ⟨{P : GeometricPrimeCarrier n M // 0 < D.coefficient P}, fun P => P.val.val,
    D.locallyFinite_positive, fun P => P.val.isClosed, ?_, h⟩
  ext x
  rw [D.mem_support, mem_iUnion]
  constructor
  · rintro ⟨P, hP, hx⟩
    exact ⟨⟨P, hP⟩, hx⟩
  · rintro ⟨P, hx⟩
    exact ⟨P.val, P.property, hx⟩

section Positive

variable {m : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M]
  [IsComplexManifold (m + 1) M]

omit [IsComplexManifold (m + 1) M] in
/-- A member through `x` of a family with adapted coordinates in which it is a single coordinate
hyperplane is regular of dimension `m` at `x` (the argument of TN's `regularAtDim_member`, for an
arbitrary index type). -/
private theorem regularAtDim_of_coordinateFamily {ι : Type*} {H : ι → Set M}
    {S : ι → Finset (Fin (m + 1))} {x : M} (hS : IsCoordinateFamilyAt (m + 1) H S x) (i : ι)
    (hx : x ∈ H i) (hcard : (S i).card = 1) : RegularAtDim (n := m + 1) (H i) x m := by
  classical
  obtain ⟨Φ, hsrc, h0, hflat⟩ := hS
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hcard
  let e : Equiv.Perm (Fin (m + 1)) := Equiv.swap j (Fin.last m)
  let L : ComplexModel (m + 1) ≃L[ℂ] ComplexModel (m + 1) :=
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toContinuousLinearEquiv
  have hlast (z : ComplexModel (m + 1)) : (L z) (Fin.last m) = z j := by
    change z (e.symm (Fin.last m)) = z j
    simp [e]
  have hplane (z : ComplexModel (m + 1)) :
      z ∈ coordSubspace ({j} : Finset (Fin (m + 1))) ↔
        L z ∈ complexCoordinatePlane (m + 1) m := by
    constructor
    · intro hz k hk
      have hk' : k = Fin.last m := Fin.ext (by simp only [Fin.val_last]; omega)
      rw [hk', hlast]
      exact hz j (Finset.mem_singleton_self j)
    · intro hz k hk
      rw [Finset.mem_singleton.mp hk]
      rw [← hlast]
      exact hz (Fin.last m) le_rfl
  let Θ : LocalHolomorphicEquivAt (n := m + 1) ((complexChartAt (n := m + 1) x).val x) := {
    source := Φ.source
    target := L.symm ⁻¹' Φ.target
    isOpen_source := Φ.isOpen_source
    isOpen_target := Φ.isOpen_target.preimage L.symm.continuous
    center_mem_source := Φ.center_mem_source
    toFun := fun z => L (Φ.toFun z)
    invFun := fun z => Φ.invFun (L.symm z)
    toFun_holomorphic := L.differentiable.comp_differentiableOn Φ.toFun_holomorphic
    invFun_holomorphic := Φ.invFun_holomorphic.comp L.symm.differentiable.differentiableOn
      (fun _ hz => hz)
    mapsTo_toFun := by
      intro z hz
      change L.symm (L (Φ.toFun z)) ∈ Φ.target
      rw [L.symm_apply_apply]
      exact Φ.mapsTo_toFun hz
    mapsTo_invFun := fun _ hz => Φ.mapsTo_invFun hz
    left_inv := by
      intro z hz
      rw [L.symm_apply_apply]
      exact Φ.left_inv z hz
    right_inv := by
      intro z hz
      rw [Φ.right_inv _ hz, L.apply_symm_apply] }
  refine ⟨Nat.le_succ m, hx, Θ, hsrc, ?_, ?_⟩
  · change L (Φ.toFun ((complexChartAt (n := m + 1) x).val x)) = 0
    rw [h0, L.map_zero]
  · intro y hy hyΦ
    have hfi := hflat i hx hy hyΦ
    rw [hj] at hfi
    exact hfi.trans (hplane (Φ.toFun ((complexChartAt (n := m + 1) x).val y)))

/-- The support form implies the component form (positive dimension). -/
private theorem isSNCComponentwise_of_isSNC_succ (D : EffectiveGeometricQDivisor (m + 1) M)
    (hD : D.IsSNC) : D.IsSNCComponentwise := by
  classical
  obtain ⟨ι, H, hLF, hcl, hsupp, hloc⟩ := hD
  -- the members are smooth hypersurfaces, hence analytic
  have hreg : ∀ i, ∀ x ∈ H i, RegularAtDim (n := m + 1) (H i) x m := by
    intro i x hx
    obtain ⟨S, hS, hcard, -⟩ := hloc x
    exact regularAtDim_of_coordinateFamily hS i hx (hcard i hx)
  have han : ∀ i, IsComplexAnalyticSubset (n := m + 1) (H i) := fun i =>
    AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold
      ⟨hcl i, fun x hx => ⟨m, hreg i x hx⟩⟩
  have hPan : ∀ P : GeometricPrimeCarrier (m + 1) M,
      IsComplexAnalyticSubset (n := m + 1) P.val := fun P =>
    P.subvariety_carrier ▸ P.subvariety.analytic
  have hsuppP : ∀ P : {P : GeometricPrimeCarrier (m + 1) M // 0 < D.coefficient P},
      P.val.val ⊆ ⋃ i, H i := by
    intro P y hy
    rw [← hsupp]
    exact (D.mem_support y).mpr ⟨P.val, P.property, hy⟩
  -- every prime component lies in one member
  have hmem : ∀ P : {P : GeometricPrimeCarrier (m + 1) M // 0 < D.coefficient P},
      ∃ i, P.val.val ⊆ H i := by
    intro P
    have hV : P.val.subvariety.carrier = P.val.val := P.val.subvariety_carrier
    obtain ⟨x₀, hx₀⟩ := P.val.nonempty
    obtain ⟨t, ht, hfin⟩ := hLF x₀
    obtain ⟨U, hUt, hUo, hx₀U⟩ := mem_nhds_iff.mp ht
    obtain ⟨i₀, hi₀⟩ := mem_iUnion.mp (hsuppP P hx₀)
    have hne : {i | (H i ∩ t).Nonempty}.Nonempty := ⟨i₀, x₀, hi₀, mem_of_mem_nhds ht⟩
    obtain ⟨f, hf⟩ := hfin.countable.exists_eq_range hne
    have hsub : P.val.subvariety.carrier ∩ U ⊆ ⋃ k, H (f k) := by
      rintro y ⟨hyV, hyU⟩
      rw [hV] at hyV
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hsuppP P hyV)
      have hiF : i ∈ {i | (H i ∩ t).Nonempty} := ⟨y, hi, hUt hyU⟩
      rw [hf] at hiF
      obtain ⟨k, rfl⟩ := hiF
      exact mem_iUnion.mpr ⟨k, hi⟩
    obtain ⟨k, hk⟩ := StrictTransformLocus.exists_subset_of_inter_isOpen_subset_iUnion
      P.val.subvariety (fun k => han (f k)) hUo ⟨x₀, hV ▸ hx₀, hx₀U⟩ hsub
    exact ⟨f k, hV ▸ hk⟩
  choose iP hiP using hmem
  -- near each of its points, a prime component is its member
  have hloceq : ∀ (P : {P : GeometricPrimeCarrier (m + 1) M // 0 < D.coefficient P}) (x : M),
      x ∈ P.val.val → ∀ᶠ y in 𝓝 x, y ∈ P.val.val ↔ y ∈ H (iP P) := by
    intro P x hx
    have hV : P.val.subvariety.carrier = P.val.val := P.val.subvariety_carrier
    have hdim : P.val.subvariety.dim = m := by
      have := P.val.subvariety_codimension
      omega
    have hld := CodimOneSupport.locDimGE_carrier P.val.subvariety (hV ▸ hx)
    rw [hdim, hV] at hld
    exact CodimOneSupport.eventually_mem_iff_of_regularAtDim_of_locDimGE (hPan P.val)
      (hreg _ x (hiP P hx)) (Eventually.of_forall fun y hy => hiP P hy) hld
  -- two prime components in the same member through a point are equal
  have hinjP : ∀ (P Q : {P : GeometricPrimeCarrier (m + 1) M // 0 < D.coefficient P}) (x : M),
      x ∈ P.val.val → x ∈ Q.val.val → iP P = iP Q → P = Q := by
    intro P Q x hxP hxQ hPQ
    have h1 := hloceq P x hxP
    have h2 := hloceq Q x hxQ
    rw [hPQ] at h1
    obtain ⟨W, hWsub, hWo, hxW⟩ := mem_nhds_iff.mp (h1.and h2)
    have hsub : ∀ (A B : {P : GeometricPrimeCarrier (m + 1) M // 0 < D.coefficient P}),
        x ∈ A.val.val → A.val.val ∩ W ⊆ B.val.val → A.val.val ⊆ B.val.val := by
      intro A B hxA hAB
      have hVA : A.val.subvariety.carrier = A.val.val := A.val.subvariety_carrier
      have h := StrictTransformLocus.subset_of_inter_isOpen_subset A.val.subvariety
        (hPan B.val) hWo ⟨x, hVA ▸ hxA, hxW⟩ (hVA ▸ hAB)
      rwa [hVA] at h
    have hPQsub : P.val.val ⊆ Q.val.val := hsub P Q hxP fun y hy =>
      (hWsub hy.2).2.mpr ((hWsub hy.2).1.mp hy.1)
    have hQPsub : Q.val.val ⊆ P.val.val := hsub Q P hxQ fun y hy =>
      (hWsub hy.2).1.mpr ((hWsub hy.2).2.mp hy.1)
    exact Subtype.ext (GeometricPrimeCarrier.ext (subset_antisymm hPQsub hQPsub))
  intro x
  obtain ⟨S, hS, hcard, hinj⟩ := hloc x
  refine ⟨fun P => S (iP P), ?_, fun P hxP => hcard _ (hiP P hxP), ?_⟩
  · -- the members of the components, then the components themselves
    have hA : IsCoordinateFamilyAt (m + 1) (fun P => H (iP P)) (fun P => S (iP P)) x := by
      obtain ⟨Φ, h1, h2, h3⟩ := hS
      exact ⟨Φ, h1, h2, fun P hxP y hy hyΦ => h3 (iP P) hxP hy hyΦ⟩
    let C : {P : GeometricPrimeCarrier (m + 1) M // 0 < D.coefficient P} → Set M := fun P =>
      if x ∈ P.val.val then P.val.val else H (iP P)
    obtain ⟨t, ht, hfin⟩ := D.locallyFinite_positive x
    have hfinx : {P : {P : GeometricPrimeCarrier (m + 1) M // 0 < D.coefficient P} |
        x ∈ P.val.val}.Finite :=
      hfin.subset fun P hP => ⟨x, hP, mem_of_mem_nhds ht⟩
    have hev : ∀ᶠ y in 𝓝 x, ∀ P, y ∈ C P ↔ y ∈ H (iP P) := by
      have hall := (eventually_all_finite hfinx).mpr fun P hP => hloceq P x hP
      filter_upwards [hall] with y hy P
      by_cases hxP : x ∈ P.val.val
      · simp only [C, if_pos hxP]
        exact hy P hxP
      · simp only [C, if_neg hxP]
    obtain ⟨Φ, h1, h2, h3⟩ := CodimOneAdmissibleAlong.isCoordinateFamilyAt_congr hev hA
    refine ⟨Φ, h1, h2, fun P hxP y hy hyΦ => ?_⟩
    have h := h3 P (by simp only [C, if_pos hxP]; exact hxP) hy hyΦ
    simpa only [C, if_pos hxP] using h
  · intro P hP Q hQ hSPQ
    exact hinjP P Q x hP hQ (hinj (hiP P hP) (hiP Q hQ) hSPQ)

end Positive

/-- Source `def:logres`: the support form of "simple normal crossing" (`IsSNC`) is equivalent to
the component form (`IsSNCComponentwise`: smooth prime components crossing normally). -/
theorem isSNC_iff_isSNCComponentwise {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (D : EffectiveGeometricQDivisor n M) : D.IsSNC ↔ D.IsSNCComponentwise := by
  refine ⟨fun h => ?_, isSNC_of_isSNCComponentwise⟩
  cases n with
  | zero =>
    intro x
    have : IsEmpty {P : GeometricPrimeCarrier 0 M // 0 < D.coefficient P} :=
      ⟨fun P => isEmptyElim P.val⟩
    exact ⟨fun P => isEmptyElim P, isCoordinateFamilyAt_of_isEmpty _ _ x,
      fun P => isEmptyElim P, fun P => isEmptyElim P⟩
  | succ m => exact isSNCComponentwise_of_isSNC_succ D h

end SGPT.PSH.EffectiveGeometricQDivisor
