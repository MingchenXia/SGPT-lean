import SGPT.Okounkov.FlagLifting
import SGPT.Foundations.Analysis.Pending.AnalyticSubsetPreimage

set_option autoImplicit false
noncomputable section

universe u

namespace SGPT.Okounkov

open Set
open scoped Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending
open AnalyticModificationLocalDiscrepancy

/-- The actual nested carrier and the original smaller carrier have the
same subtype topology, via literal projection and original containment. -/
def nestedCarrierHomeomorph {X : Type u} [TopologicalSpace X]
    {N S : Set X} (hSN : S ⊆ N) :
    (Subtype.val ⁻¹' S : Set N) ≃ₜ S where
  toFun z := ⟨z.val.val, z.property⟩
  invFun z := ⟨⟨z.val, hSN z.property⟩, z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

section Nested

variable {n k l : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {N S : Set X} (hkn : k ≤ n) (hlk : l ≤ k)
  (hN : IsClosedConnectedSubmanifold n N k)
  (hS : IsClosedConnectedSubmanifold n S l) (hSN : S ⊆ N)

/-- The genuine nested and original inherited atlases are holomorphically
compatible, by actual inclusion followed by actual corestriction. -/
theorem contMDiff_nestedCarrierHomeomorph :
    let := SubmanifoldChartedSpace.chartedSpace hkn hN.2.2
    let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hkn hN.2.2
    let hNS := regularAtDim_subtype_of_nested hkn hlk hN.2.2 hS.2.2 hSN
    let := SubmanifoldChartedSpace.chartedSpace hlk hNS
    let := SubmanifoldChartedSpace.chartedSpace (hlk.trans hkn) hS.2.2
    ContMDiff 𝓘(ℂ, ComplexModel l) 𝓘(ℂ, ComplexModel l) ∞
      (nestedCarrierHomeomorph hSN) := by
  let := SubmanifoldChartedSpace.chartedSpace hkn hN.2.2
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hkn hN.2.2
  let hNS := regularAtDim_subtype_of_nested hkn hlk hN.2.2 hS.2.2 hSN
  let := SubmanifoldChartedSpace.chartedSpace hlk hNS
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hlk hNS
  let := SubmanifoldChartedSpace.chartedSpace (hlk.trans hkn) hS.2.2
  have hincl : ContMDiff 𝓘(ℂ, ComplexModel l) 𝓘(ℂ, ComplexModel n) ∞
      (fun z : (Subtype.val ⁻¹' S : Set N) => (z.val.val : X)) :=
    (SubmanifoldChartedSpace.contMDiff_val hkn hN.2.2).comp
      (SubmanifoldChartedSpace.contMDiff_val hlk hNS)
  exact SubmanifoldCodRestrict.contMDiff_codRestrict
    (hlk.trans hkn) hS.2.2 hincl (fun z => z.property)

/-- The inverse inserts the actual original containment and is holomorphic
by two true corestrictions, rather than a transferred complex structure. -/
theorem contMDiff_nestedCarrierHomeomorph_symm :
    let := SubmanifoldChartedSpace.chartedSpace hkn hN.2.2
    let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hkn hN.2.2
    let hNS := regularAtDim_subtype_of_nested hkn hlk hN.2.2 hS.2.2 hSN
    let := SubmanifoldChartedSpace.chartedSpace hlk hNS
    let := SubmanifoldChartedSpace.chartedSpace (hlk.trans hkn) hS.2.2
    ContMDiff 𝓘(ℂ, ComplexModel l) 𝓘(ℂ, ComplexModel l) ∞
      (nestedCarrierHomeomorph hSN).symm := by
  let := SubmanifoldChartedSpace.chartedSpace hkn hN.2.2
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hkn hN.2.2
  let hNS := regularAtDim_subtype_of_nested hkn hlk hN.2.2 hS.2.2 hSN
  let := SubmanifoldChartedSpace.chartedSpace hlk hNS
  let := SubmanifoldChartedSpace.chartedSpace (hlk.trans hkn) hS.2.2
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (hlk.trans hkn) hS.2.2
  have htoN : ContMDiff 𝓘(ℂ, ComplexModel l) 𝓘(ℂ, ComplexModel k) ∞
      (fun z : S => (⟨z.val, hSN z.property⟩ : N)) :=
    SubmanifoldCodRestrict.contMDiff_codRestrict hkn hN.2.2
      (SubmanifoldChartedSpace.contMDiff_val (hlk.trans hkn) hS.2.2)
      (fun z => hSN z.property)
  exact SubmanifoldCodRestrict.contMDiff_codRestrict hlk hNS htoN
    (fun z => z.property)

end Nested

private theorem interior_preimage_homeomorph_eq_empty
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) {A : Set Y} (hA : interior A = ∅) :
    interior (e ⁻¹' A) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hsub : e '' interior (e ⁻¹' A) ⊆ A := by
    rintro _ ⟨y, hy, rfl⟩
    exact (interior_subset hy : y ∈ e ⁻¹' A)
  have himem : e x ∈ interior A :=
    interior_maximal hsub (e.isOpenMap _ isOpen_interior) ⟨x, hx, rfl⟩
  simp only [hA, notMem_empty] at himem

/-- Genuine biholomorphic source and target changes transport actual
inverse/analytic/thin data. Compactness supplies true properness. -/
theorem isAnalyticModification_biholomorphic_transport
    {n : ℕ} {X Y X' Y' : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    [TopologicalSpace X'] [ChartedSpace (ComplexModel n) X'] [IsComplexManifold n X']
    [TopologicalSpace Y'] [ChartedSpace (ComplexModel n) Y'] [IsComplexManifold n Y']
    [CompactSpace Y'] (eX : X' ≃ₜ X) (eY : Y' ≃ₜ Y)
    (heX : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ eX)
    (heXi : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ eX.symm)
    (heY : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ eY)
    (heYi : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ eY.symm)
    {π : Y → X} (hπ : IsAnalyticModification (n := n) π) :
    IsAnalyticModification (n := n) (eX.symm ∘ π ∘ eY) := by
  obtain ⟨A, B, s, hAc, hAa, hAi, hBc, hBa, hBi, hpre, hs, hright, hleft⟩ := hπ.2.2
  have hhol : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (eX.symm ∘ π ∘ eY) := heXi.comp (hπ.1.comp heY)
  refine ⟨hhol, hhol.continuous.isProperMap, eY ⁻¹' A, eX ⁻¹' B,
    eY.symm ∘ s ∘ eX, hAc.preimage eY.continuous,
    AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage heY hAa,
    interior_preimage_homeomorph_eq_empty eY hAi,
    hBc.preimage eX.continuous,
    AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage heX hBa,
    interior_preimage_homeomorph_eq_empty eX hBi, ?_, ?_, ?_, ?_⟩
  · ext y
    simp only [mem_preimage, Function.comp_apply, Homeomorph.apply_symm_apply]
    exact Set.ext_iff.mp hpre (eY y)
  · have hs' : ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
        (s ∘ eX) (eX ⁻¹' B)ᶜ :=
      hs.comp heX.contMDiffOn (fun _ hx => hx)
    exact (heYi.contMDiffOn : ContMDiffOn 𝓘(ℂ, ComplexModel n)
      𝓘(ℂ, ComplexModel n) ∞ eY.symm univ).comp hs' (fun _ _ => mem_univ _)
  · intro x hx
    change eX.symm (π (eY (eY.symm (s (eX x))))) = x
    rw [eY.apply_symm_apply, hright (eX x) hx, eX.symm_apply_apply]
  · intro y hy
    change eY.symm (s (eX (eX.symm (π (eY y))))) = y
    rw [eX.apply_symm_apply, hleft (eY y) hy, eY.symm_apply_apply]


/-- Equality of the actual model dimensions transports the same inherited
atlas construction; all regularity proofs are propositionally irrelevant. -/
theorem isAnalyticModification_inherited_dimension_congr
    {n d e : ℕ} {X Y : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    {S : Set X} {T : Set Y} (hde : d = e) (hd : d ≤ n) (he : e ≤ n)
    (hSd : ∀ x ∈ S, RegularAtDim (n := n) S x d)
    (hTd : ∀ y ∈ T, RegularAtDim (n := n) T y d)
    (hSe : ∀ x ∈ S, RegularAtDim (n := n) S x e)
    (hTe : ∀ y ∈ T, RegularAtDim (n := n) T y e) (f : T → S) :
    (letI := SubmanifoldChartedSpace.chartedSpace hd hSd
     letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hd hSd
     letI := SubmanifoldChartedSpace.chartedSpace hd hTd
     letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hd hTd
     IsAnalyticModification (n := d) f) ↔
    (letI := SubmanifoldChartedSpace.chartedSpace he hSe
     letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace he hSe
     letI := SubmanifoldChartedSpace.chartedSpace he hTe
     letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace he hTe
     IsAnalyticModification (n := e) f) := by
  subst e
  rfl

namespace OriginalFlagGeometry

/-- The actual shifted original component, in the exact tail model dimension. -/
@[instance_reducible]
def shiftedComponentCharts {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))
    (i : Fin (m + 1)) : ChartedSpace (ComplexModel (m - (i : ℕ))) (F.flag i.succ) :=
  SubmanifoldChartedSpace.chartedSpace
    ((Nat.sub_le m i).trans (Nat.le_succ m))
    (show ∀ x ∈ F.flag i.succ,
      RegularAtDim
        (n := m + 1) (F.flag i.succ) x (m - (i : ℕ)) from
      by simpa using (F.smooth.2.2 i.succ).2.2)

/-- The shifted direct component has its genuine inherited complex structure. -/
theorem shiftedComponentComplex {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))
    (i : Fin (m + 1)) :
    letI := F.shiftedComponentCharts i
    IsComplexManifold (m - (i : ℕ)) (F.flag i.succ) :=
  SubmanifoldChartedSpace.isComplexManifold_chartedSpace _ _

/-- Literal nested-to-original projection on each actual tail component. -/
def tailComponentHomeomorph {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))
    (i : Fin (m + 1)) : F.tail.flag i ≃ₜ F.flag i.succ :=
  nestedCarrierHomeomorph (by
    apply F.smooth.2.1
    change 1 ≤ (i : ℕ) + 1
    omega)

/-- The actual tail-component atlas and the original component atlas are
biholomorphically identified, with original carriers and topology retained. -/
theorem contMDiff_tailComponentHomeomorph {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1)) (i : Fin (m + 1)) :
    letI := F.tail.componentCharts i
    letI := F.shiftedComponentCharts i
    ContMDiff 𝓘(ℂ, ComplexModel (m - (i : ℕ)))
      𝓘(ℂ, ComplexModel (m - (i : ℕ))) ∞ (F.tailComponentHomeomorph i) := by
  have hC : IsClosedConnectedSubmanifold (m + 1) (F.flag i.succ) (m - (i : ℕ)) :=
    by simpa using F.smooth.2.2 i.succ
  have hCN : F.flag i.succ ⊆ F.flag (1 : Fin (m + 2)) := by
    apply F.smooth.2.1
    change 1 ≤ (i : ℕ) + 1
    omega
  exact contMDiff_nestedCarrierHomeomorph (Nat.le_succ m) (Nat.sub_le m i)
      F.firstDivisor hC hCN

/-- The inverse genuinely inserts containment in the original first carrier. -/
theorem contMDiff_tailComponentHomeomorph_symm {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1)) (i : Fin (m + 1)) :
    letI := F.tail.componentCharts i
    letI := F.shiftedComponentCharts i
    ContMDiff 𝓘(ℂ, ComplexModel (m - (i : ℕ)))
      𝓘(ℂ, ComplexModel (m - (i : ℕ))) ∞ (F.tailComponentHomeomorph i).symm := by
  have hC : IsClosedConnectedSubmanifold (m + 1) (F.flag i.succ) (m - (i : ℕ)) :=
    by simpa using F.smooth.2.2 i.succ
  have hCN : F.flag i.succ ⊆ F.flag (1 : Fin (m + 2)) := by
    apply F.smooth.2.1
    change 1 ≤ (i : ℕ) + 1
    omega
  exact contMDiff_nestedCarrierHomeomorph_symm (Nat.le_succ m) (Nat.sub_le m i)
      F.firstDivisor hC hCN

end OriginalFlagGeometry

/-- The literal restricted map is a genuine lifting of the actual tails,
including the true inherited component atlases and zero-dimensional level. -/
theorem IsFlagLifting.tail {m : ℕ} {F W : OriginalFlagGeometry.{u} (m + 1)}
    {π : W.carrier → F.carrier} (hπ : IsFlagLifting F W π)
    (h1 : MapsTo π (W.flag (1 : Fin (m + 2))) (F.flag (1 : Fin (m + 2)))) :
    IsFlagLifting F.tail W.tail (flagComponentMap F W π (1 : Fin (m + 2)) h1) := by
  let : ChartedSpace (ComplexModel m) (F.flag (1 : Fin (m + 2))) := F.tail.charts
  let : IsComplexManifold m (F.flag (1 : Fin (m + 2))) := F.tail.complex
  let : ChartedSpace (ComplexModel m) (W.flag (1 : Fin (m + 2))) := W.tail.charts
  let : IsComplexManifold m (W.flag (1 : Fin (m + 2))) := W.tail.complex
  obtain ⟨h1', hmod1⟩ := hπ.2 (1 : Fin (m + 2))
  have hbase : IsAnalyticModification (n := m)
      (flagComponentMap F W π (1 : Fin (m + 2)) h1) := by
    simp only [Fin.val_one] at hmod1
    exact hmod1
  refine ⟨hbase, ?_⟩
  intro i
  obtain ⟨hi, hmodi⟩ := hπ.2 i.succ
  have hitail : MapsTo (flagComponentMap F W π (1 : Fin (m + 2)) h1)
      (W.tail.flag i) (F.tail.flag i) := fun _ hx => hi hx
  refine ⟨hitail, ?_⟩
  let := F.tail.componentCharts i
  let := F.tail.componentComplex i
  let := W.tail.componentCharts i
  let := W.tail.componentComplex i
  let := F.shiftedComponentCharts i
  let := F.shiftedComponentComplex i
  let := W.shiftedComponentCharts i
  let := W.shiftedComponentComplex i
  let : CompactSpace (W.tail.flag i) :=
    isCompact_iff_compactSpace.mp (W.tail.smooth.level_isCompact i)
  have horiginal : IsAnalyticModification (n := m - (i : ℕ))
      (flagComponentMap F W π i.succ hi) := by
    have hFe : ∀ x ∈ F.flag i.succ,
        RegularAtDim (n := m + 1) (F.flag i.succ) x (m - (i : ℕ)) :=
      by simpa using (F.smooth.2.2 i.succ).2.2
    have hWe : ∀ x ∈ W.flag i.succ,
        RegularAtDim (n := m + 1) (W.flag i.succ) x (m - (i : ℕ)) :=
      by simpa using (W.smooth.2.2 i.succ).2.2
    exact (isAnalyticModification_inherited_dimension_congr
      (show m + 1 - (i.succ : ℕ) = m - (i : ℕ) by simp)
      (Nat.sub_le (m + 1) (i.succ : ℕ)) ((Nat.sub_le m i).trans (Nat.le_succ m))
      (F.smooth.2.2 i.succ).2.2 (W.smooth.2.2 i.succ).2.2 hFe hWe
      (flagComponentMap F W π i.succ hi)).mp hmodi
  have htransport := isAnalyticModification_biholomorphic_transport
    (F.tailComponentHomeomorph i) (W.tailComponentHomeomorph i)
    (F.contMDiff_tailComponentHomeomorph i)
    (F.contMDiff_tailComponentHomeomorph_symm i)
    (W.contMDiff_tailComponentHomeomorph i)
    (W.contMDiff_tailComponentHomeomorph_symm i) horiginal
  exact htransport

end SGPT.Okounkov
