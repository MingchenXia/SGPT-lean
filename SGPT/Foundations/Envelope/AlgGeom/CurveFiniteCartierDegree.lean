import SGPT.Foundations.Envelope.AlgGeom.CurveFiniteCartierFibres
import SGPT.Foundations.Envelope.AlgGeom.CurveFiniteMapDegrees
import SGPT.Foundations.Envelope.AlgGeom.CurveProperDominantFinite

/-! # TRUE whole original nonflat finite Cartier/Euler degree scaling, including singular targets -/
open AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section
universe u
namespace SGPT.Foundations.Envelope.CurveFiniteCartierDegree
open CurveCartierLocalOrders CurveLineDegrees
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem finsum_eq_mem_of_support_subset {T : Type*} (w : T → ℤ) (S : Set T)
    (h : Function.support w ⊆ S) : (∑ᶠ x : T, w x) = ∑ᶠ x ∈ S, w x := by
  have he : Set.univ ∩ Function.support w = S ∩ Function.support w := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_univ, true_and]
    exact ⟨fun hx => ⟨h hx, hx⟩, And.right⟩
  rw [← finsum_mem_univ w, finsum_mem_inter_support_eq w Set.univ S he]

private theorem weight_zero {T : Scheme.{u}} [IsIntegral T] [IsLocallyNoetherian T]
    {k : Type u} [Field k] (q : T ⟶ Spec (.of k)) (I : T.IdealSheafData)
    (hI : I.IsInvertible) (x : T) (hx : x ∉ I.support) : weightedLocalOrder q I hI x = 0 := by
  unfold weightedLocalOrder
  rw [localOrder_eq_zero_of_not_mem_support I hI x hx, zero_mul]

/-- The TRUE native Cartier weighted-order sums over the WHOLE original
curves scale by SAME native function-field degree, including singular targets.
No finite support/fibre, normality, flatness or degree certificate is supplied. -/
theorem finsum_comap {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    {k : Type u} [Field k] (g : Y ⟶ X) [IsFinite g] [IsDominant g]
    (q : X ⟶ Spec (.of k)) (hq : IsProjectiveFactorization q)
    (hdimX : topologicalKrullDim X ≤ 1) (hdimY : topologicalKrullDim Y ≤ 1)
    (I : X.IdealSheafData) (hI : I.IsInvertible) :
    letI : IsProper q := hq.isProper
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian q
    letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
    letI := (DominantFunctionFieldMaps.functionFieldMap g).hom.toAlgebra
    (∑ᶠ y : Y, weightedLocalOrder (g ≫ q) (I.comap g) (hI.comap_of_dominant_integral g) y) =
      (Module.finrank X.functionField Y.functionField : ℤ) * ∑ᶠ x : X, weightedLocalOrder q I hI x := by
  let : IsProper q := hq.isProper
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian q
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace q
  let : AlgebraicGeometry.IsNoetherian X :=
    { toIsLocallyNoetherian := inferInstance, toCompactSpace := inferInstance }
  let := (DominantFunctionFieldMaps.functionFieldMap g).hom.toAlgebra
  let J := I.comap g
  let hJ : J.IsInvertible := hI.comap_of_dominant_integral g
  let S : Set X := I.support
  let wx := weightedLocalOrder q I hI
  let wy := weightedLocalOrder (g ≫ q) J hJ
  let n : ℤ := Module.finrank X.functionField Y.functionField
  have hS : S.Finite := CurveProperDominantFinite.finite_closed_subset hdimX I.support
    (CurveCartierIdealDegrees.support_ne_top I hI)
  have hsx : Function.support wx ⊆ S := by
    intro x hx
    by_contra hn
    exact hx (weight_zero q I hI x hn)
  have hsy : Function.support wy ⊆ g ⁻¹' S := by
    intro y hy
    by_contra hn
    have hj : y ∉ J.support := by
      rw [show J.support = I.support.preimage g.continuous from I.support_comap g]
      change g y ∉ I.support
      exact hn
    exact hy (weight_zero (g ≫ q) J hJ y hj)
  have hpre : g ⁻¹' S = ⋃ x ∈ S, {y : Y | g y = x} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · intro hy
      exact ⟨g y, hy, rfl⟩
    · rintro ⟨x, hx, he⟩
      exact he ▸ hx
  have hdis : S.PairwiseDisjoint (fun x => {y : Y | g y = x}) := by
    intro x _hx x' _hx' hxx
    change Disjoint {y : Y | g y = x} {y : Y | g y = x'}
    rw [Set.disjoint_left]
    intro y hy hy'
    exact hxx (hy.symm.trans hy')
  have hfin : ∀ x ∈ S, ({y : Y | g y = x} : Set Y).Finite := by
    intro x _hx
    apply (g.finite_preimage_singleton x).subset
    intro y hy
    exact Set.mem_singleton_iff.mpr hy
  have hfibre (x : X) (hx : x ∈ S) : (∑ᶠ y ∈ {y : Y | g y = x}, wy y) = n * wx x := by
    have hng : x ≠ genericPoint X := by
      intro he
      exact CurveFiniteClosedSubschemes.genericPoint_not_mem I.support
        (CurveCartierIdealDegrees.support_ne_top I hI) (he ▸ hx)
    rw [← finsum_set_coe_eq_finsum_mem]
    exact CurveFiniteCartierFibres.finsum_fibre_comap g q hq hdimX hdimY I hI x hng
  calc
    _ = ∑ᶠ y ∈ g ⁻¹' S, wy y := finsum_eq_mem_of_support_subset wy _ hsy
    _ = ∑ᶠ x ∈ S, ∑ᶠ y ∈ {y : Y | g y = x}, wy y := by
      rw [hpre]
      exact finsum_mem_biUnion hdis hS hfin
    _ = ∑ᶠ x ∈ S, n * wx x := by
      apply finsum_congr
      intro x
      apply finsum_congr
      intro hx
      exact hfibre x hx
    _ = n * ∑ᶠ x ∈ S, wx x := by
      rw [finsum_mem_eq_finite_toFinset_sum _ hS, finsum_mem_eq_finite_toFinset_sum _ hS,
        Finset.mul_sum]
    _ = _ := congrArg (fun z => n * z) (finsum_eq_mem_of_support_subset wx S hsx).symm

/-- The SAME actual original geometric Cartier comap line has its TRUE full
Euler degree scaled by the SAME native function-field degree under ANY finite
dominant original curve map; no normality or flatness of the target. -/
theorem degree_comap {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    {k : Type u} [Field k] (g : Y ⟶ X) [IsFinite g] [IsDominant g]
    (q : X ⟶ Spec (.of k)) (hq : IsProjectiveFactorization q)
    (hdimX : topologicalKrullDim X ≤ 1) (hdimY : topologicalKrullDim Y ≤ 1)
    (I : X.IdealSheafData) (hI : I.IsInvertible) :
    letI : IsProper q := hq.isProper
    letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace q
    letI : IsProper (g ≫ q) := (CurveFiniteMapDegrees.finite_comp_projectiveFactorization q hq g).isProper
    letI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (g ≫ q)
    letI := (DominantFunctionFieldMaps.functionFieldMap g).hom.toAlgebra
    degree (g ≫ q) (I.comap g).toModules =
      (Module.finrank X.functionField Y.functionField : ℤ) * degree q I.toModules := by
  let : IsProper q := hq.isProper
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace q
  let hqY := CurveFiniteMapDegrees.finite_comp_projectiveFactorization q hq g
  let : IsProper (g ≫ q) := hqY.isProper
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (g ≫ q)
  let := (DominantFunctionFieldMaps.functionFieldMap g).hom.toAlgebra
  change SchemeCoherentEulerCharacteristic.normalizedEulerCharacteristic _ _ =
    _ * SchemeCoherentEulerCharacteristic.normalizedEulerCharacteristic _ _
  rw [normalizedEulerCharacteristic_eq_neg_finsum (g ≫ q) hqY hdimY (I.comap g)
    (hI.comap_of_dominant_integral g), normalizedEulerCharacteristic_eq_neg_finsum q hq hdimX I hI,
    finsum_comap g q hq hdimX hdimY I hI, mul_neg]

end SGPT.Foundations.Envelope.CurveFiniteCartierDegree
