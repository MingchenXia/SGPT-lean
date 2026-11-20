import SGPT.Unibranch.HironakaG10RmClosedSubspace

/-!
# Images through global components; proper analytic subsets of irreducible spaces (Remmert, 5.2.f)

Run 0081 lane G10R2. Consumer-side consequences of item 5.2 for the native Remmert assembly (item 5.7 of
`G10MW/remmert-reduced-spaces.md`, port of `ProperMappingInduction.properImageStatement_succ` and
`ProperImageIrreducible`). Blueprint: `hironaka-g10rm-global-components.tex`.

* `isComplexAnalyticSubset_range_of_forall_nativeGlobalComponents`: for a proper map `F` from a reduced complex
  space to a complex manifold, if `F '' B` is analytic for every native global component `B`, then `range F`
  is analytic (near a point only finitely many components meet the compact preimage of a compact
  neighbourhood); `..._of_forall_sourceObject`: the same with the images written as ranges of `F ∘ ι_B` on
  the reduced closed subspaces.
* `isComplexAnalyticSubset_range_of_nativeDimLE_zero`: the base case `(R_0)` (a zero-dimensional space is
  discrete).
* `subset_closure_compl_of_irreducible`, `interior_eq_empty_of_irreducible`: a proper analytic subset of an
  irreducible space is nowhere dense; `nativeDimLE_of_irreducible_of_ne_univ`,
  `nativeDimLE_pred_of_irreducible_of_ne_univ`: it has dimension one less; `nativeDimLE_univ_of_nativePureDim`.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace Topology CategoryTheory AlgebraicGeometry
open scoped Topology

namespace SGPT.Unibranch.HironakaG10RmComponentImage

open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
  SourceReducedComplexSpace OriginalAnalyticClosedSubspace
  HironakaG10RmGlobalComponents HironakaG10EpNativeDim

noncomputable section

variable {Y : SourceReducedComplexSpace}

/-! ### The image of a proper map through the global components -/

/-- **General step of the induction**: if a proper map from `Y` to a complex manifold has analytic images
of all native global components, its range is analytic. -/
theorem isComplexAnalyticSubset_range_of_forall_nativeGlobalComponents {k : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel k) M] [IsComplexManifold k M]
    {F : Y.obj.left → M} (hF : IsProperMap F)
    (hcomp : ∀ B ∈ nativeGlobalComponents Y, IsComplexAnalyticSubset (n := k) (F '' B)) :
    IsComplexAnalyticSubset (n := k) (range F) := by
  classical
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (ComplexModel k) M
  refine AnalyticSubsetOpens.isComplexAnalyticSubset_of_forall_opens fun y => ?_
  obtain ⟨K, hKc, hKy⟩ := exists_compact_mem_nhds y
  have hfin := (locallyFinite_nativeGlobalComponents Y).finite_nonempty_inter_compact
    (hF.isCompact_preimage hKc)
  refine ⟨⟨interior K, isOpen_interior⟩, mem_interior_iff_mem_nhds.mpr hKy, ?_⟩
  have heq : ((↑) ⁻¹' range F : Set (⟨interior K, isOpen_interior⟩ : Opens M)) =
      (↑) ⁻¹' (⋃ B ∈ hfin.toFinset, F '' (B : Set Y.obj.left)) := by
    ext z
    constructor
    · rintro ⟨x, hx⟩
      obtain ⟨B, hB, hxB⟩ := exists_mem_nativeGlobalComponents x
      have hxK : F x ∈ K := by
        rw [hx]
        exact interior_subset z.2
      exact mem_iUnion₂.mpr ⟨⟨B, hB⟩, hfin.mem_toFinset.mpr ⟨x, hxB, hxK⟩, x, hxB, hx⟩
    · intro hz
      obtain ⟨B, -, x, -, hx⟩ := mem_iUnion₂.mp hz
      exact ⟨x, hx⟩
  rw [heq]
  exact AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val
    (ConstantRankImage.isComplexAnalyticSubset_biUnion _
      fun (B : nativeGlobalComponents Y) _ => hcomp B.1 B.2) _

/-- The general step with the component images written as ranges on the reduced closed subspaces. -/
theorem isComplexAnalyticSubset_range_of_forall_sourceObject {k : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel k) M] [IsComplexManifold k M]
    {F : Y.obj.left → M} (hF : IsProperMap F)
    (hcomp : ∀ (B : Set Y.obj.left) (hBc : B ∈ nativeGlobalComponents Y),
      IsComplexAnalyticSubset (n := k) (range (F ∘ (inclusion Y B
        (isAnalyticSubset_of_mem_nativeGlobalComponents hBc)).hom.left.base))) :
    IsComplexAnalyticSubset (n := k) (range F) := by
  refine isComplexAnalyticSubset_range_of_forall_nativeGlobalComponents hF fun B hBc => ?_
  have h := hcomp B hBc
  rwa [range_comp, inclusion_range] at h

/-- **`(R_0)` natively**: a proper map from a reduced complex space of dimension `0` to a complex manifold
has analytic range (the space is discrete, so the preimage of a compact set is finite). -/
theorem isComplexAnalyticSubset_range_of_nativeDimLE_zero {k : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel k) M] [IsComplexManifold k M]
    {F : Y.obj.left → M} (hF : IsProperMap F) (hdim : NativeDimLE Y univ 0) :
    IsComplexAnalyticSubset (n := k) (range F) := by
  classical
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (ComplexModel k) M
  have hdisc : ∀ s : Set Y.obj.left, IsDiscrete s := by
    intro s
    refine isDiscrete_iff_forall_mem_exists_isOpen.mpr fun y hy => ?_
    obtain ⟨U, hU, hyU, hUsub⟩ :=
      exists_isolated_of_nativeDimLE_zero isAnalyticSubset_univ hdim (mem_univ y)
    refine ⟨U, hU, Subset.antisymm (fun z hz => hUsub ⟨hz.1, mem_univ z⟩) ?_⟩
    rintro z rfl
    exact ⟨hyU, hy⟩
  refine AnalyticSubsetOpens.isComplexAnalyticSubset_of_forall_opens fun y => ?_
  obtain ⟨K, hKc, hKy⟩ := exists_compact_mem_nhds y
  have hfin : (F ⁻¹' K).Finite := (hF.isCompact_preimage hKc).finite (hdisc _)
  refine ⟨⟨interior K, isOpen_interior⟩, mem_interior_iff_mem_nhds.mpr hKy, ?_⟩
  have heq : ((↑) ⁻¹' range F : Set (⟨interior K, isOpen_interior⟩ : Opens M)) =
      (↑) ⁻¹' (F '' (F ⁻¹' K)) := by
    ext z
    constructor
    · rintro ⟨x, hx⟩
      have hxK : F x ∈ K := by
        rw [hx]
        exact interior_subset z.2
      exact ⟨x, hxK, hx⟩
    · rintro ⟨x, -, hx⟩
      exact ⟨x, hx⟩
  rw [heq]
  exact AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val
    (ProperMappingInduction.isComplexAnalyticSubset_of_finite (hfin.image F)) _

/-! ### Proper analytic subsets of an irreducible space -/

/-- A proper analytic subset of an irreducible space is nowhere dense. -/
theorem subset_closure_compl_of_irreducible (h : Y.IsIrreducibleAnalyticSubset univ)
    {S : Set Y.obj.left} (hS : Y.IsAnalyticSubset S) (hne : S ≠ univ) :
    univ ⊆ closure (univ \ S) := by
  have hC := HironakaG10NativeAnalyticClosureDifference.isAnalyticSubset_closure_diff
    isAnalyticSubset_univ hS
  have hunion : (univ : Set Y.obj.left) = S ∪ closure (univ \ S) := by
    refine Subset.antisymm (fun z _ => ?_) (subset_univ _)
    by_cases hz : z ∈ S
    · exact Or.inl hz
    · exact Or.inr (subset_closure ⟨mem_univ z, hz⟩)
  rcases h.2.2 S _ hS hC (subset_univ _) (subset_univ _) hunion with h1 | h1
  · exact absurd h1.symm hne
  · exact h1.subset

/-- A proper analytic subset of an irreducible space has empty interior. -/
theorem interior_eq_empty_of_irreducible (h : Y.IsIrreducibleAnalyticSubset univ)
    {S : Set Y.obj.left} (hS : Y.IsAnalyticSubset S) (hne : S ≠ univ) : interior S = ∅ := by
  refine interior_eq_empty_iff_dense_compl.mpr (dense_iff_closure_eq.mpr ?_)
  refine eq_univ_of_univ_subset ((subset_closure_compl_of_irreducible h hS hne).trans ?_)
  exact closure_mono fun z hz => hz.2

/-- A proper analytic subset of an irreducible space of dimension `≤ m + 1` has dimension `≤ m`. -/
theorem nativeDimLE_of_irreducible_of_ne_univ (h : Y.IsIrreducibleAnalyticSubset univ)
    {S : Set Y.obj.left} (hS : Y.IsAnalyticSubset S) (hne : S ≠ univ) {m : ℕ}
    (hdim : NativeDimLE Y univ (m + 1)) : NativeDimLE Y S m :=
  nativeDimLE_of_subset_of_dense isAnalyticSubset_univ (subset_univ S)
    (subset_closure_compl_of_irreducible h hS hne) hdim

/-- A space of pure dimension `d` has dimension `≤ d`. -/
theorem nativeDimLE_univ_of_nativePureDim {d : ℕ}
    (hY : HironakaG10MwRemmertRegular.NativePureDim Y d) : NativeDimLE Y univ d := by
  intro e y j hy
  rw [trace_univ] at hy
  exact (hY _ j ((regularAtDim_carrier_iff e ⟨y, hy.2.1⟩ j).mp hy)).le

/-- A proper analytic subset of an irreducible space of pure dimension `d` has dimension `≤ d - 1`. -/
theorem nativeDimLE_pred_of_irreducible_of_ne_univ (h : Y.IsIrreducibleAnalyticSubset univ) {d : ℕ}
    (hY : HironakaG10MwRemmertRegular.NativePureDim Y d) {S : Set Y.obj.left}
    (hS : Y.IsAnalyticSubset S) (hne : S ≠ univ) : NativeDimLE Y S (d - 1) :=
  nativeDimLE_of_irreducible_of_ne_univ h hS hne
    ((nativeDimLE_univ_of_nativePureDim hY).mono (by omega))

end

end SGPT.Unibranch.HironakaG10RmComponentImage
