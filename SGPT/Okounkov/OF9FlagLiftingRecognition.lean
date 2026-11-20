import SGPT.Okounkov.FlagLiftingTail
import SGPT.Okounkov.FlagLiftingStrictTransform
import SGPT.Okounkov.IntrinsicModificationRestriction
import SGPT.Okounkov.NativeFlagBaseGeometry

/-!
# Recognizing liftings of smooth flags

Source: chapter *The theory of Okounkov bodies*, `def:lifting` (*"`W•` is a lifting of `Y•` to `Z`
if
`π(Wᵢ) ⊆ Yᵢ` and the induced maps `Wᵢ → Yᵢ` are bimeromorphic … the component `W_{i+1}` is
necessarily the strict transform of `Y_{i+1}` with respect to `Wᵢ → Yᵢ`"*), used for `rmk:valcurr`.

* `first_eq_strictTransform_of_image_eq`: if an analytic modification `q : Z → X` maps the first
  member `W₁` of a smooth flag of `Z` **onto** the first member `Y₁` of a smooth flag of `X`, then
  `W₁` is the strict transform of `Y₁` (a codimension-one prime is never contained in the image of
  the exceptional locus).
* `isFlagLifting_of_tail`: a lifting is assembled from its first level and a lifting of the tails.
* **`isFlagLifting_of_image_eq`**: an analytic modification `q` with `q(Wᵢ) = Yᵢ` for every `i` is a
  lifting of `Y•` (`def:lifting`): the bimeromorphy of the restrictions is automatic.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.OF9

open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Okounkov
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending
open SourceGenericSubmanifoldMinimum
open AnalyticModificationLocalDiscrepancy

/-- **The first member is the strict transform.** If `q(W₁) = Y₁` for an analytic modification
`q : Z → X` and first flag members `W₁ ⊆ Z`, `Y₁ ⊆ X`, then `W₁ = q^{-1}[Y₁]` (strict transform). -/
theorem first_eq_strictTransform_of_image_eq {m : ℕ} {F W : OriginalFlagGeometry.{u} (m + 1)}
    {q : W.carrier → F.carrier} (hq : IsAnalyticModification (n := m + 1) q)
    (himage : q '' W.flag (1 : Fin (m + 2)) = F.flag (1 : Fin (m + 2))) :
    W.flag (1 : Fin (m + 2)) = strictTransform (m + 1) q (F.flag (1 : Fin (m + 2))) := by
  obtain ⟨VY, hY, hdY⟩ := exists_subvariety_carrier_eq_of_submanifold F.firstDivisor
  obtain ⟨VW, hW, _hdW⟩ := exists_subvariety_carrier_eq_of_submanifold W.firstDivisor
  have hdY' : VY.dim + 1 = m + 1 := by rw [hdY]
  obtain ⟨Vt, hstrict, _hdt, _himage, _hreader⟩ :=
    AnalyticModificationDivisorStrictTransform.exists_strictTransform_reader hq VY hdY'
  have hstrict' : Vt.carrier =
      strictTransform (m + 1) q (F.flag (1 : Fin (m + 2))) := by
    rwa [hY] at hstrict
  have hi : MapsTo q (W.flag (1 : Fin (m + 2))) (F.flag (1 : Fin (m + 2))) := by
    intro z hz
    rw [← himage]
    exact ⟨z, hz, rfl⟩
  have hav :=
    AnalyticModificationExceptionalImageCodimension.not_subset_image_exceptionalLocus_of_codim_one
      hq VY hdY'
  obtain ⟨y, hy, hyE⟩ := not_subset.mp hav
  have hy' : y ∈ F.flag (1 : Fin (m + 2)) := hY ▸ hy
  obtain ⟨w, hw, hwy⟩ := (Set.ext_iff.mp himage y).mpr hy'
  have hwE : w ∉ exceptionalLocus (m + 1) q := by
    intro h
    exact hyE ⟨w, h, hwy⟩
  have hsub : strictTransform (m + 1) q (F.flag (1 : Fin (m + 2))) ⊆
      W.flag (1 : Fin (m + 2)) := by
    change closure (q ⁻¹' F.flag (1 : Fin (m + 2)) \ exceptionalLocus (m + 1) q) ⊆ _
    refine closure_minimal ?_ W.firstDivisor.1
    rintro z ⟨hz, hzE⟩
    obtain ⟨v, hv, hvz⟩ := (Set.ext_iff.mp himage (q z)).mpr hz
    exact (AnalyticModificationExceptionalFibres.eq_of_apply_eq_of_not_mem_exceptionalLocus
      hq hzE hvz) ▸ hv
  have hrev : VW.carrier ⊆ Vt.carrier :=
    StrictTransformLocus.subset_of_inter_isOpen_subset VW Vt.analytic
      (StrictTransformComposition.isOpen_compl_exceptionalLocus hq.1)
      ⟨w, hW.symm ▸ hw, hwE⟩ (by
        rintro z ⟨hz, hzE⟩
        rw [hstrict']
        exact subset_closure ⟨hi (hW ▸ hz), hzE⟩)
  exact Subset.antisymm (by simpa only [hW, hstrict'] using hrev) hsub

/-- **Assembling a lifting from its first level and its tail.** -/
theorem isFlagLifting_of_tail {m : ℕ} {F W : OriginalFlagGeometry.{u} (m + 1)}
    {q : W.carrier → F.carrier} (hq : IsAnalyticModification (n := m + 1) q)
    (h1 : MapsTo q (W.flag (1 : Fin (m + 2))) (F.flag (1 : Fin (m + 2))))
    (htail : IsFlagLifting F.tail W.tail (flagComponentMap F W q (1 : Fin (m + 2)) h1)) :
    IsFlagLifting F W q := by
  refine ⟨hq, ?_⟩
  intro i
  cases i using Fin.cases with
  | zero =>
    obtain ⟨hi, hmod⟩ := isAnalyticModification_wholeSetRestriction hq
      F.smooth.1 W.smooth.1 (F.smooth.2.2 0).2.2 (W.smooth.2.2 0).2.2
    exact ⟨hi, hmod⟩
  | succ i =>
    obtain ⟨hiT, hmodT⟩ := htail.2 i
    have hW1 : W.flag i.succ ⊆ W.flag (1 : Fin (m + 2)) := by
      apply W.smooth.2.1
      change 1 ≤ (i : ℕ) + 1
      omega
    have hi : MapsTo q (W.flag i.succ) (F.flag i.succ) := by
      intro z hz
      have h := hiT (show (⟨z, hW1 hz⟩ : W.flag (1 : Fin (m + 2))) ∈ W.tail.flag i from hz)
      exact h
    refine ⟨hi, ?_⟩
    let := F.tail.componentCharts i
    let := F.tail.componentComplex i
    let := W.tail.componentCharts i
    let := W.tail.componentComplex i
    let := F.shiftedComponentCharts i
    let := F.shiftedComponentComplex i
    let := W.shiftedComponentCharts i
    let := W.shiftedComponentComplex i
    have hCi : IsClosedConnectedSubmanifold (m + 1) (W.flag i.succ) (m - (i : ℕ)) := by
      simpa only [Fin.val_succ, Nat.add_sub_add_right] using W.smooth.2.2 i.succ
    let : CompactSpace (W.flag i.succ) := isCompact_iff_compactSpace.mp hCi.1.isCompact
    have htransport := isAnalyticModification_biholomorphic_transport
      (F.tailComponentHomeomorph i).symm (W.tailComponentHomeomorph i).symm
      (F.contMDiff_tailComponentHomeomorph_symm i)
      (F.contMDiff_tailComponentHomeomorph i)
      (W.contMDiff_tailComponentHomeomorph_symm i)
      (W.contMDiff_tailComponentHomeomorph i) hmodT
    have hMap : flagComponentMap F W q i.succ hi =
        (F.tailComponentHomeomorph i).symm.symm ∘
          flagComponentMap F.tail W.tail (flagComponentMap F W q (1 : Fin (m + 2)) h1) i hiT ∘
            (W.tailComponentHomeomorph i).symm := by
      funext z
      rfl
    have hmodShift : IsAnalyticModification (n := m - (i : ℕ))
        (flagComponentMap F W q i.succ hi) := hMap.symm ▸ htransport
    have hFe : ∀ x ∈ F.flag i.succ,
        RegularAtDim (n := m + 1) (F.flag i.succ) x (m - (i : ℕ)) := by
      simpa only [Fin.val_succ, Nat.add_sub_add_right] using (F.smooth.2.2 i.succ).2.2
    have hWe : ∀ x ∈ W.flag i.succ,
        RegularAtDim (n := m + 1) (W.flag i.succ) x (m - (i : ℕ)) := by
      simpa only [Fin.val_succ, Nat.add_sub_add_right] using (W.smooth.2.2 i.succ).2.2
    exact (isAnalyticModification_inherited_dimension_congr
      (show m + 1 - (i.succ : ℕ) = m - (i : ℕ) by simp)
      (Nat.sub_le (m + 1) (i.succ : ℕ)) ((Nat.sub_le m i).trans (Nat.le_succ m))
      (F.smooth.2.2 i.succ).2.2 (W.smooth.2.2 i.succ).2.2 hFe hWe
      (flagComponentMap F W q i.succ hi)).mpr hmodShift

/-- **Liftings are recognized by images.** An analytic modification `q : Z → X` between the
carriers of two smooth flags with `q(Wᵢ) = Yᵢ` for every `i` is a lifting of `Y•` to `W•`
(`def:lifting`): the restrictions `Wᵢ → Yᵢ` are bimeromorphic, each `W_{i+1}` being the strict
transform of `Y_{i+1}` under `Wᵢ → Yᵢ`. -/
theorem isFlagLifting_of_image_eq : ∀ (n : ℕ) (F W : OriginalFlagGeometry.{u} n)
    (q : W.carrier → F.carrier), IsAnalyticModification (n := n) q →
      (∀ i, q '' W.flag i = F.flag i) → IsFlagLifting F W q := by
  intro n
  induction n with
  | zero =>
    intro F W q hq _
    refine ⟨hq, ?_⟩
    intro i
    have hi0 : i = (0 : Fin 1) := by apply Fin.ext; omega
    subst i
    obtain ⟨hi, hmod⟩ := isAnalyticModification_wholeSetRestriction hq
      F.smooth.1 W.smooth.1 (F.smooth.2.2 0).2.2 (W.smooth.2.2 0).2.2
    exact ⟨hi, hmod⟩
  | succ m ih =>
    intro F W q hq himage
    have h1 : MapsTo q (W.flag (1 : Fin (m + 2))) (F.flag (1 : Fin (m + 2))) := by
      intro z hz
      rw [← himage 1]
      exact ⟨z, hz, rfl⟩
    have hstrict := first_eq_strictTransform_of_image_eq hq (himage 1)
    obtain ⟨hi1, hmod1⟩ :=
      exists_intrinsicModification_strictDivisor hq F.firstDivisor W.firstDivisor hstrict
    let : ChartedSpace (ComplexModel m) (F.flag (1 : Fin (m + 2))) := F.tail.charts
    let : IsComplexManifold m (F.flag (1 : Fin (m + 2))) := F.tail.complex
    let : ChartedSpace (ComplexModel m) (W.flag (1 : Fin (m + 2))) := W.tail.charts
    let : IsComplexManifold m (W.flag (1 : Fin (m + 2))) := W.tail.complex
    have hq1 : IsAnalyticModification (n := m)
        (flagComponentMap F W q (1 : Fin (m + 2)) h1) := hmod1
    refine isFlagLifting_of_tail hq h1 (ih F.tail W.tail _ hq1 ?_)
    intro i
    have hW1 : W.flag i.succ ⊆ W.flag (1 : Fin (m + 2)) := by
      apply W.smooth.2.1
      change 1 ≤ (i : ℕ) + 1
      omega
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      change q z.1 ∈ F.flag i.succ
      rw [← himage i.succ]
      exact ⟨z.1, hz, rfl⟩
    · intro hy
      change y.1 ∈ F.flag i.succ at hy
      rw [← himage i.succ] at hy
      obtain ⟨z, hz, hzy⟩ := hy
      exact ⟨⟨z, hW1 hz⟩, hz, Subtype.ext hzy⟩

end SGPT.Okounkov.OF9
