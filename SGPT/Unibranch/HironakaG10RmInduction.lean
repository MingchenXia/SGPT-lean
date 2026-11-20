import SGPT.Unibranch.HironakaG10RmComponentImage

/-!
# The native Remmert induction, reduced to the irreducible case (Remmert, 5.2.g)

Run 0081 lane G10R2. Skeleton of item 5.7 of `G10MW/remmert-reduced-spaces.md` (port of
`ProperMappingInduction.properImageStatement_zero`, `properImageStatement_succ` and
`properImageStatement_of_remmertStein`, Demailly II.8.8). Blueprint: `hironaka-g10rm-global-components.tex`.

* `NativeProperImageDim m` — the statement `(R_m)`: `NativeProperImageCore` for sources of dimension `≤ m`;
  `NativeIrreducibleProperImageDim m` — the same for irreducible sources.
* `nativeProperImageDim_zero` — `(R_0)` (a zero-dimensional space is discrete).
* `nativeProperImageDim_succ` — the irreducible case in dimension `≤ m + 1` gives `(R_{m+1})`: apply it to the
  reduced closed subspace on each native global component, which is irreducible, second countable and of
  dimension `≤ m + 1`, and use local finiteness of the components.
* `nativeProperImageCore_of_irreducible` — if `(R_m)` implies the irreducible case in dimension `≤ m + 1` for
  every `m`, then `NativeProperImageCore` holds.

This is a reduction theorem: the irreducible case is an explicit hypothesis of the last theorem, to be
discharged by item 5.7 (rank, fibre and image dimension, constant-rank image, Remmert–Stein).
-/

set_option autoImplicit false

open Set TopologicalSpace Topology CategoryTheory AlgebraicGeometry
open scoped Topology

namespace SGPT.Unibranch.HironakaG10RmInduction

open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
  SourceReducedComplexSpace OriginalAnalyticClosedSubspace HironakaG10MwRemmertRegular
  HironakaG10EpNativeDim HironakaG10RmGlobalComponents HironakaG10RmClosedSubspace
  HironakaG10RmComponentImage

noncomputable section

/-- The statement `(R_m)`: a proper native morphism from a second-countable reduced complex space of
dimension `≤ m` into a closed analytic subset of a complex manifold has analytic range. -/
def NativeProperImageDim (m : ℕ) : Prop :=
  ∀ (Y : SourceReducedComplexSpace) [SecondCountableTopology Y.obj.left],
    NativeDimLE Y univ m →
    ∀ (k : ℕ) (M : Type) [TopologicalSpace M] [ChartedSpace (ComplexModel k) M]
      [IsComplexManifold k M] (C : Set M) (hC : IsComplexAnalyticSubset (n := k) C)
      (φ : Y ⟶ ofClosedAnalytic C hC), IsProperMap (pointMap φ) →
      IsComplexAnalyticSubset (n := k) (range (pointMap φ))

/-- The statement `(R_m)` for irreducible sources. -/
def NativeIrreducibleProperImageDim (m : ℕ) : Prop :=
  ∀ (Y : SourceReducedComplexSpace) [SecondCountableTopology Y.obj.left],
    Y.IsIrreducibleAnalyticSubset univ → NativeDimLE Y univ m →
    ∀ (k : ℕ) (M : Type) [TopologicalSpace M] [ChartedSpace (ComplexModel k) M]
      [IsComplexManifold k M] (C : Set M) (hC : IsComplexAnalyticSubset (n := k) C)
      (φ : Y ⟶ ofClosedAnalytic C hC), IsProperMap (pointMap φ) →
      IsComplexAnalyticSubset (n := k) (range (pointMap φ))

/-- `NativeProperImageCore` is `(R_m)` for all `m`. -/
theorem nativeProperImageCore_iff : NativeProperImageCore ↔ ∀ m, NativeProperImageDim m :=
  ⟨fun h m Y _ hdim => h Y m hdim, fun h Y _ m hdim => h m Y hdim⟩

/-- **`(R_0)`.** -/
theorem nativeProperImageDim_zero : NativeProperImageDim 0 := by
  intro Y _ hdim k M _ _ _ C hC φ hprop
  exact isComplexAnalyticSubset_range_of_nativeDimLE_zero hprop hdim

/-- The point map of a composite with the closed embedding of a reduced closed subspace. -/
theorem pointMap_inclusion_comp {k : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel k) M] [IsComplexManifold k M] {C : Set M}
    {hC : IsComplexAnalyticSubset (n := k) C} {Y : SourceReducedComplexSpace} {B : Set Y.obj.left}
    (hB : Y.IsAnalyticSubset B) (φ : Y ⟶ ofClosedAnalytic C hC) :
    pointMap (inclusion Y B hB ≫ φ) = pointMap φ ∘ (inclusion Y B hB).hom.left.base :=
  rfl

/-- **The irreducible case gives `(R_{m+1})`.** -/
theorem nativeProperImageDim_succ {m : ℕ} (hI : NativeIrreducibleProperImageDim (m + 1)) :
    NativeProperImageDim (m + 1) := by
  intro Y _ hdim k M _ _ _ C hC φ hprop
  refine isComplexAnalyticSubset_range_of_forall_sourceObject hprop fun B hBc => ?_
  have hBa := isAnalyticSubset_of_mem_nativeGlobalComponents hBc
  have : SecondCountableTopology (sourceObject Y B hBa).obj.left :=
    secondCountableTopology_sourceObject Y B hBa
  have hirr := isIrreducibleAnalyticSubset_univ_sourceObject_of_mem_nativeGlobalComponents Y B hBa hBc
  have hdimB : NativeDimLE (sourceObject Y B hBa) univ (m + 1) :=
    nativeDimLE_univ_sourceObject Y B hBa (hdim.anti isAnalyticSubset_univ (subset_univ B))
  have hpropB : IsProperMap (pointMap (inclusion Y B hBa ≫ φ)) := by
    rw [pointMap_inclusion_comp]
    exact hprop.comp (inclusion_isClosedEmbedding Y B hBa).isProperMap
  have h := hI (sourceObject Y B hBa) hirr hdimB k M C hC (inclusion Y B hBa ≫ φ) hpropB
  rwa [pointMap_inclusion_comp] at h

/-- **The native Remmert induction**: if, for every `m`, `(R_m)` gives the irreducible case in dimension
`≤ m + 1`, then `NativeProperImageCore` holds. -/
theorem nativeProperImageCore_of_irreducible
    (hirr : ∀ m, NativeProperImageDim m → NativeIrreducibleProperImageDim (m + 1)) :
    NativeProperImageCore := by
  refine nativeProperImageCore_iff.mpr fun m => ?_
  induction m with
  | zero => exact nativeProperImageDim_zero
  | succ m ih => exact nativeProperImageDim_succ (hirr m ih)

end

end SGPT.Unibranch.HironakaG10RmInduction
