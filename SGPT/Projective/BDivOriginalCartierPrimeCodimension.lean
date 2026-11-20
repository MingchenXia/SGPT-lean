import SGPT.Projective.BDivOriginalCanonicalPrimeClass
import SGPT.Okounkov.OF5PrimeDivisorPresentation
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.AlgebraicGeometry.FunctionField

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory TopologicalSpace Set
open SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open scoped Topology Manifold

namespace SGPT.Projective.BDivNov16

noncomputable section

/-- The actual generic point of an integral effective Cartier subscheme has
codimension one in the original integral scheme. -/
theorem originalCartierPrime_generic_coheight
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (I : X.IdealSheafData) [IsIntegral I.subscheme] (hI : I.IsInvertible) :
    Order.coheight (I.subschemeι (genericPoint I.subscheme)) = 1 := by
  let q := genericPoint I.subscheme
  let z : X := I.subschemeι q
  let R := X.presheaf.stalk z
  have hk : RingHom.ker (I.subschemeι.stalkMap q).hom = I.stalkIdeal z :=
    I.ker_stalkMap_subschemeι q
  let e := (Ideal.quotEquivOfEq hk.symm).trans
    ((I.subschemeι.stalkMap q).hom.quotientKerEquivOfSurjective
      (I.subschemeι.stalkMap_surjective q))
  have hfield : IsField (I.subscheme.presheaf.stalk q) := Field.toIsField I.subscheme.functionField
  have hm : I.stalkIdeal z = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (Ideal.Quotient.maximal_of_isField _ (e.toMulEquiv.isField hfield))
  obtain ⟨U, hzU, a, ha, hU⟩ := hI z
  let g : R := X.presheaf.germ U.1 z hzU a
  have hg : g ∈ nonZeroDivisors R := by
    let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨z, hzU⟩
    have hloc := U.2.isLocalization_stalk ⟨z, hzU⟩
    exact (@IsLocalization.map_nonZeroDivisors_le Γ(X,U) _
      (U.2.primeIdealOf ⟨z, hzU⟩).asIdeal.primeCompl R _ _ hloc) ⟨a, ha, rfl⟩
  have hgen : IsLocalRing.maximalIdeal R = Ideal.span {g} := by
    rw [← hm, I.stalkIdeal_eq_affine z U hzU, hU, Ideal.map_span, Set.image_singleton]
  let : (IsLocalRing.maximalIdeal R).IsPrincipal := ⟨g, hgen⟩
  have hmin : IsLocalRing.maximalIdeal R ∈ (IsLocalRing.maximalIdeal R).minimalPrimes := by
    rw [Ideal.minimalPrimes_eq_subsingleton_self]
    exact Set.mem_singleton _
  have ht := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes_of_isLocalRing _ hmin
  have hdim : ringKrullDim R ≤ 1 := by
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
    exact_mod_cast ht
  have hle : Order.coheight z ≤ 1 := by
    change ringKrullDim (X.presheaf.stalk z) ≤ 1 at hdim
    rw [ringKrullDim_stalk_eq_coheight] at hdim
    exact_mod_cast hdim
  have hne : Order.coheight z ≠ 0 := by
    intro hz
    let : Ring.KrullDimLE 0 R := Ring.krullDimLE_iff.mpr (by
      change ringKrullDim (X.presheaf.stalk z) ≤ 0
      rw [ringKrullDim_stalk_eq_coheight, hz]
      rfl)
    have hb : IsLocalRing.maximalIdeal R = ⊥ :=
      IsLocalRing.isField_iff_maximalIdeal_eq.mp Ring.KrullDimLE.isField_of_isDomain
    rw [hgen] at hb
    exact (mem_nonZeroDivisors_iff_ne_zero.mp hg) (Ideal.span_singleton_eq_bot.mp hb)
  exact le_antisymm hle (Order.one_le_iff_ne_zero.mpr hne)

/-- The point realizing the generic support is the image of the same
Cartier subscheme's generic point. -/
theorem originalCartierPrime_closure
    {X : Scheme.{0}} (I : X.IdealSheafData) [IsIntegral I.subscheme] :
    closure {I.subschemeι (genericPoint I.subscheme)} = (I.support : Set X) := by
  have h := (genericPoint_spec I.subscheme).image I.subschemeι.continuous
  rw [Set.image_univ, I.range_subschemeι, I.support.isClosed.closure_eq] at h
  exact h.def

section Native

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (m : ℕ)
  [SmoothOfRelativeDimension (m+1) f] [IsSeparated f] [QuasiCompact f]
  (E : ClosedProjectiveEmbedding f)

local instance : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance : ChartedSpace (ComplexModel (m+1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m+1)
local instance : IsComplexManifold (m+1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m+1)

omit [IsSeparated f] [QuasiCompact f] in
/-- Every original Zariski-closed set is determined by its literal complex trace. -/
private theorem closed_subset_of_native_trace_subset [LocallyOfFiniteType f]
    {A B : Set X} (hA : IsClosed A) (hB : IsClosed B)
    (h : schemeNativeAlgebraicTrace f A ⊆ schemeNativeAlgebraicTrace f B) : A ⊆ B := by
  let : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  rw [← hA.closure_eq, ← JacobsonSpace.closure_inter_closedPoints_eq_closure hA.isLocallyClosed]
  apply closure_minimal _ hB
  intro x hx
  let p : SchemeComplexPoint f := ⟨pointOfClosedPoint f x hx.2, pointOfClosedPoint_comp f x hx.2⟩
  have hp : schemeComplexPointImage f p = x := pointOfClosedPoint_apply f x hx.2 _
  rw [← hp]
  exact h (show schemeComplexPointImage f p ∈ A from hp.symm ▸ hx.1)

include E in
/-- The trace of an original irreducible closed set is analytically irreducible.
An analytic decomposition algebraizes by direct homogeneous equations. -/
theorem native_trace_analyticIrreducible_of_isIrreducible
    {A : Set X} (hA : IsClosed A) (hirr : IsIrreducible A) :
    IsComplexAnalyticallyIrreducible (n := m+1) (schemeNativeAlgebraicTrace f A) := by
  let : LocallyOfFiniteType f := E.locallyOfFiniteType
  let : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  refine ⟨schemeNativeAlgebraicTrace_isComplexAnalyticSubset f (m+1) A hA, ?_, ?_⟩
  · obtain ⟨x, hxA, hx⟩ := nonempty_inter_closedPoints hirr.nonempty hA.isLocallyClosed
    let p : SchemeComplexPoint f := ⟨pointOfClosedPoint f x hx, pointOfClosedPoint_comp f x hx⟩
    refine ⟨p, ?_⟩
    change schemeComplexPointImage f p ∈ A
    have hp : schemeComplexPointImage f p = x := pointOfClosedPoint_apply f x hx _
    rw [hp]
    exact hxA
  · intro B C hB hC hBA hCA heq
    obtain ⟨I, _, _, hI, _, _, _⟩ := exists_original_reduced_analytic_ideal_direct f m E B hB
    obtain ⟨J, _, _, hJ, _, _, _⟩ := exists_original_reduced_analytic_ideal_direct f m E C hC
    have hTraceI : schemeNativeAlgebraicTrace f (I.support : Set X) = B := by
      rw [← hI, closedImmersionComplexPointMap_range, I.range_subschemeι] <;> rfl
    have hTraceJ : schemeNativeAlgebraicTrace f (J.support : Set X) = C := by
      rw [← hJ, closedImmersionComplexPointMap_range, J.range_subschemeι] <;> rfl
    have hcover : A ⊆ (I.support : Set X) ∪ (J.support : Set X) := by
      apply closed_subset_of_native_trace_subset f hA (I.support.isClosed.union J.support.isClosed)
      change schemeNativeAlgebraicTrace f A ⊆
        schemeNativeAlgebraicTrace f (I.support : Set X) ∪
          schemeNativeAlgebraicTrace f (J.support : Set X)
      rw [hTraceI, hTraceJ]
      exact heq.le
    rcases isPreirreducible_iff_isClosed_union_isClosed.mp hirr.isPreirreducible
      _ _ I.support.isClosed J.support.isClosed hcover with hi | hj
    · apply Or.inl
      apply subset_antisymm _ hBA
      rw [← hTraceI]
      exact Set.preimage_mono hi
    · apply Or.inr
      apply subset_antisymm _ hCA
      rw [← hTraceJ]
      exact Set.preimage_mono hj

include E in
/-- An actual original codimension-one point gives a native prime on the
literal trace of its entire Zariski closure. -/
theorem exists_nativePrime_of_original_codimOne [IsIntegral X]
    {z : X} (hz : Order.coheight z = 1) :
    ∃ P : SGPT.PSH.GeometricPrimeCarrier (m+1) (SchemeComplexPoint f),
      P.val = schemeNativeAlgebraicTrace f (closure {z}) := by
  let : IsProper f := E.isProper
  let : LocallyOfFiniteType f := E.locallyOfFiniteType
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let A := schemeNativeAlgebraicTrace f (closure {z})
  have hi : IsComplexAnalyticallyIrreducible (n := m+1) A :=
    native_trace_analyticIrreducible_of_isIrreducible f m E isClosed_closure
      (isIrreducible_singleton.closure)
  obtain ⟨y, Ψ, _, _⟩ := SGPT.Okounkov.OF5.exists_point_normalOrder_eq_ord (m := m) E hz
  have hy : RegularAtDim (n := m+1) A y m :=
    IdealPowerNormalOrder.regularAtDim_of_divisorFlattening Ψ
  let V : ClosedIrreducibleAnalyticSubvariety (m+1) (SchemeComplexPoint f) :=
    ⟨A, hi.analytic.isClosed, hi, m, Nat.le_succ m, ⟨y, hy⟩⟩
  exact ⟨⟨A, V, rfl, rfl⟩, rfl⟩


/-- The actual original Cartier prime used in the Chern identity has the
whole closure of one original codimension-one scheme point as its support. -/
theorem exists_originalCartierCodimOnePrime_cycleClass [IsIntegral X]
    (P : SGPT.PSH.GeometricPrimeCarrier (m+1) (SchemeComplexPoint f)) :
    letI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    ∃ (z : X) (I : X.IdealSheafData) (hI : I.IsInvertible),
      Order.coheight z = 1 ∧ closure {z} = (I.support : Set X) ∧
      P.val = schemeNativeAlgebraicTrace f (closure {z}) ∧
      I.radical = I ∧ IsIntegral I.subscheme ∧
      originalCartierCanonicalSection I ≠ 0 ∧
      sectionZeroIdealSheaf (originalCartierIdealAtlas I hI).dual
        (originalCartierCanonicalSection I) = I ∧
      SGPT.BDivisor.DFAlg.cycleClass (SGPT.Siu.primeEffectiveDivisor P) =
        RealBottChern.ofRepresentative
          ((schemeLineBundleMetric f (m+1) E (originalCartierIdealAtlas I hI).dual).curvature
            (originalCartierIdealAtlas I hI).dual) := by
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : LocallyOfFiniteType f := E.locallyOfFiniteType
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨I, hI, hrad, hint, himage, hsection, hzero, hclass⟩ :=
    exists_originalCartierPrime_cycleClass f m E P
  let : IsIntegral I.subscheme := hint
  let z := I.subschemeι (genericPoint I.subscheme)
  have hcl : closure {z} = (I.support : Set X) := originalCartierPrime_closure I
  have htrace : P.val = schemeNativeAlgebraicTrace f (closure {z}) := by
    rw [← himage, closedImmersionComplexPointMap_range, I.range_subschemeι, hcl]
    rfl
  exact ⟨z, I, hI, originalCartierPrime_generic_coheight I hI, hcl, htrace,
    hrad, hint, hsection, hzero, hclass⟩

/-- Literal complex traces distinguish the original codimension-one points. -/
theorem original_codimOne_eq_of_native_trace_eq [LocallyOfFiniteType f]
    {z w : X}
    (h : schemeNativeAlgebraicTrace f (closure {z}) =
      schemeNativeAlgebraicTrace f (closure {w})) : z = w := by
  have hc := Set.Subset.antisymm
    (closed_subset_of_native_trace_subset f isClosed_closure isClosed_closure h.le)
    (closed_subset_of_native_trace_subset f isClosed_closure isClosed_closure h.ge)
  exact (show IsGenericPoint z (closure {w}) from hc ▸ (show IsGenericPoint z (closure {z}) from rfl)).eq
    (show IsGenericPoint w (closure {w}) from rfl)

end Native

end

end SGPT.Projective.BDivNov16
