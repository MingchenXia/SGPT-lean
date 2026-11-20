import SGPT.Okounkov.NextIntrinsicFlagChild
import SGPT.Okounkov.FiniteBlowupCommonModification
import SGPT.Okounkov.FlagLiftingTail
import SGPT.Foundations.Analysis.Pending.BlowupConnected
import SGPT.Foundations.Analysis.Pending.LocusProperties
import SGPT.Foundations.Analysis.Pending.AnalyticIrreducibleComponents
import Mathlib.Data.Fin.Tuple.Basic

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov

open Set
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending
open AnalyticModificationLocalDiscrepancy

/-- The actual child is below the last actual ancestor, so adjoining it
preserves the antitonicity of the entire original prefix. -/
private theorem finiteFlag_snoc_antitone {r : ℕ} {X : Type u}
    {T : Fin (r + 1) → Set X} (hT : Antitone T) {C : Set X}
    (hC : C ⊆ T (Fin.last r)) : Antitone (Fin.snoc T C) := by
  intro i j hij
  cases i using Fin.lastCases with
  | last =>
      have hj : j = Fin.last (r + 1) := le_antisymm (Fin.le_last j) hij
      subst j
      exact Subset.rfl
  | cast i =>
      cases j using Fin.lastCases with
      | last =>
          simpa only [Fin.snoc_castSucc, Fin.snoc_last] using
            hC.trans (hT (Fin.le_last i))
      | cast j =>
          simpa only [Fin.snoc_castSucc] using hT (by simpa using hij)

/-- Equal actual carriers and dimensions transport SAME inherited atlases.
After eliminating carrier equalities, the accepted dimension theorem is
exactly the required statement; all membership and regularity proofs
are propositionally irrelevant. -/
private theorem finiteFlag_component_congr
    {n d e : ℕ} {X Y : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    {S S' : Set X} {T T' : Set Y} (hde : d = e) (hS : S = S') (hT : T = T')
    (hd : d ≤ n) (he : e ≤ n)
    (hSd : ∀ x ∈ S, RegularAtDim (n := n) S x d)
    (hTd : ∀ y ∈ T, RegularAtDim (n := n) T y d)
    (hSe : ∀ x ∈ S', RegularAtDim (n := n) S' x e)
    (hTe : ∀ y ∈ T', RegularAtDim (n := n) T' y e)
    (f : Y → X) (hi : ∀ y ∈ T, f y ∈ S) (hi' : ∀ y ∈ T', f y ∈ S') :
    (letI := SubmanifoldChartedSpace.chartedSpace hd hSd
     letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hd hSd
     letI := SubmanifoldChartedSpace.chartedSpace hd hTd
     letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hd hTd
     IsAnalyticModification (n := d) (fun y : T => (⟨f y, hi y y.2⟩ : S))) ↔
    (letI := SubmanifoldChartedSpace.chartedSpace he hSe
     letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace he hSe
     letI := SubmanifoldChartedSpace.chartedSpace he hTe
     letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace he hTe
     IsAnalyticModification (n := e) (fun y : T' => (⟨f y, hi' y y.2⟩ : S'))) := by
  subst S'
  subst T'
  exact isAnalyticModification_inherited_dimension_congr hde hd he hSd hTd hSe hTe
    (fun y : T => (⟨f y, hi y y.2⟩ : S))

/-- Both zero carriers have their SAME inherited atlases. Their actual
inclusions and inverse corestrictions thinly transport the original map. -/
private theorem finiteFlag_zero_component_modification {n : ℕ}
    (F : OriginalFlagGeometry.{u} n) {Z : Type u} [TopologicalSpace Z]
    [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z] [CompactSpace Z]
    {π : Z → F.carrier} (hπ : IsAnalyticModification (n := n) π)
    (hU : ∀ z ∈ (univ : Set Z), RegularAtDim (n := n) univ z n)
    (hi : ∀ z ∈ (univ : Set Z), π z ∈ F.flag 0) :
    letI := SubmanifoldChartedSpace.chartedSpace (Nat.le_refl n) hU
    letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_refl n) hU
    let hF0 : ∀ x ∈ F.flag 0, RegularAtDim (n := n) (F.flag 0) x n := by
      simpa only [Fin.val_zero, Nat.sub_zero] using (F.smooth.2.2 0).2.2
    let := SubmanifoldChartedSpace.chartedSpace (Nat.le_refl n) hF0
    let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_refl n) hF0
    IsAnalyticModification (n := n)
      (fun z : (univ : Set Z) => (⟨π z, hi z z.2⟩ : F.flag 0)) := by
  let := SubmanifoldChartedSpace.chartedSpace (Nat.le_refl n) hU
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_refl n) hU
  let hF0 : ∀ x ∈ F.flag 0, RegularAtDim (n := n) (F.flag 0) x n := by
    simpa only [Fin.val_zero, Nat.sub_zero] using (F.smooth.2.2 0).2.2
  let := SubmanifoldChartedSpace.chartedSpace (Nat.le_refl n) hF0
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_refl n) hF0
  let eZ : (univ : Set Z) ≃ₜ Z := Homeomorph.Set.univ Z
  let eF : F.flag 0 ≃ₜ F.carrier :=
    (Homeomorph.setCongr F.smooth.1).trans (Homeomorph.Set.univ F.carrier)
  have heZ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ eZ := by
    change ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (Subtype.val : ↥(univ : Set Z) → Z)
    exact SubmanifoldChartedSpace.contMDiff_val (Nat.le_refl n) hU
  have heZi : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ eZ.symm := by
    exact SubmanifoldCodRestrict.contMDiff_codRestrict (Nat.le_refl n) hU
      contMDiff_id (fun z => mem_univ z)
  have heF : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ eF := by
    change ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (Subtype.val : F.flag 0 → F.carrier)
    exact SubmanifoldChartedSpace.contMDiff_val (Nat.le_refl n) hF0
  have heFi : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ eF.symm := by
    have hm : ∀ x : F.carrier, x ∈ F.flag 0 := by
      intro x
      rw [F.smooth.1]
      exact mem_univ x
    exact SubmanifoldCodRestrict.contMDiff_codRestrict (Nat.le_refl n) hF0
      contMDiff_id hm
  let : CompactSpace (univ : Set Z) := isCompact_iff_compactSpace.mp isCompact_univ
  have hmod := isAnalyticModification_biholomorphic_transport
    eF eZ heF heFi heZ heZi hπ
  have heq : eF.symm ∘ π ∘ eZ =
      (fun z : (univ : Set Z) => (⟨π z, hi z z.2⟩ : F.flag 0)) := by
    funext z
    apply Subtype.ext
    rfl
  rwa [heq] at hmod

/-- A genuine partial lifted family is produced for every finite length.
All component modifications use the SAME original target flag and the
actual inherited source atlases. No partial-family certificate is an input. -/
theorem exists_partialFlag_lifting_of_isBlowupSequence {n : ℕ}
    (F : OriginalFlagGeometry.{u} n) {Z : Type u} [TopologicalSpace Z]
    [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]
    {π : Z → F.carrier} (hπ : IsBlowupSequence n F.carrier Z π)
    (r : ℕ) (hr : r ≤ n) :
    ∃ (W : Type u) (_ : TopologicalSpace W)
      (_ : ChartedSpace (ComplexModel n) W) (_ : IsComplexManifold n W)
      (_ : CompactSpace W) (_ : ConnectedSpace W) (_ : KahlerBackground n W)
      (a : W → Z) (S : Fin (r + 1) → Set W),
      IsBlowupSequence n Z W a ∧
      IsAnalyticModification (n := n) (π ∘ a) ∧ S 0 = univ ∧ Antitone S ∧
      ∃ hS : ∀ j : Fin (r + 1), IsClosedConnectedSubmanifold n (S j) (n - (j : ℕ)),
        ∃ hi : ∀ j : Fin (r + 1), ∀ x ∈ S j,
          (π ∘ a) x ∈ F.flag ⟨(j : ℕ), by omega⟩,
          (∀ j : Fin (r + 1),
            letI := SubmanifoldChartedSpace.chartedSpace (Nat.sub_le n j) (hS j).2.2
            letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace
              (Nat.sub_le n j) (hS j).2.2
            letI := F.componentCharts ⟨(j : ℕ), by omega⟩
            letI := F.componentComplex ⟨(j : ℕ), by omega⟩
            IsAnalyticModification (n := n - (j : ℕ))
              (fun x : S j =>
                (⟨(π ∘ a) x, hi j x x.2⟩ : F.flag ⟨(j : ℕ), by omega⟩))) ∧
          ∀ j : Fin (r + 1), (π ∘ a) '' S j = F.flag ⟨(j : ℕ), by omega⟩ := by
  classical
  revert hr
  induction r with
  | zero =>
      intro hr
      obtain ⟨compactZ, omegaZ⟩ :=
        LocusProperties.compactSpace_and_kahler_of_isBlowupSequence ⟨F.omega⟩ π hπ
      let := compactZ
      let := BlowupConnected.connectedSpace_of_isBlowupSequence π hπ
      let S : Fin 1 → Set Z := fun _ => univ
      have hS : ∀ j : Fin 1, IsClosedConnectedSubmanifold n (S j) (n - (j : ℕ)) := by
        intro j
        have hj : j = 0 := Fin.ext (by omega)
        subst j
        exact ⟨isClosed_univ, isConnected_univ,
          fun x _ => AnalyticIrreducibleComponents.regularAtDim_univ x⟩
      have hi : ∀ j : Fin 1, ∀ z ∈ S j,
          (π ∘ id) z ∈ F.flag ⟨(j : ℕ), by omega⟩ := by
        intro j z _
        have hj : j = 0 := Fin.ext (by omega)
        subst j
        rw [show (⟨((0 : Fin 1) : ℕ), by omega⟩ : Fin (n + 1)) = 0 from rfl,
          F.smooth.1]
        exact mem_univ _
      have hπmod := isAnalyticModification_of_isBlowupSequence hπ
      refine ⟨Z, inferInstance, inferInstance, inferInstance, inferInstance,
        inferInstance, Classical.choice omegaZ, id, S, IsBlowupSequence.refl,
        ?_, rfl, fun _ _ _ => Subset.rfl, hS, hi, ?_, ?_⟩
      · simpa only [Function.comp_id] using hπmod
      · intro j
        have hj : j = 0 := Fin.ext (by omega)
        subst j
        simp only [Fin.val_zero, Nat.sub_zero]
        exact finiteFlag_zero_component_modification F hπmod (hS 0).2.2
          (fun z hz => hi 0 z hz)
      · intro j
        have hj : j = 0 := Fin.ext (by omega)
        subst j
        rw [show (⟨((0 : Fin 1) : ℕ), by omega⟩ : Fin (n + 1)) = 0 from rfl,
          F.smooth.1]
        simpa only [S, Function.comp_id, image_univ] using
          AnalyticModificationStrongPullback.surjective_of_isAnalyticModification hπmod
            |>.range_eq
  | succ r ih =>
      intro hr
      obtain ⟨W, topW, chartsW, complexW, compactW, connectedW, omegaW,
        a, S, ha, hκ, hS0, hSa, hS, hi, hmods, _himages⟩ := ih (by omega)
      let := topW
      let := chartsW
      let := complexW
      let := compactW
      let := connectedW
      obtain ⟨k, hdim⟩ : ∃ k : ℕ, n = k + 1 + r := ⟨n - (r + 1), by omega⟩
      subst n
      obtain ⟨Y, topY, chartsY, complexY, compactY, connectedY, omegaY,
        b, T, hb, hκb, _hstrict, hTa, hT0, hT, hBi, _hfinitelevels,
        hprefix, himages, C, hC, hFnext, hCT, hCimage, hc, hchild⟩ :=
        exists_nextIntrinsicFlagChild F omegaW hκ S hSa hS0 hS hi hmods
      let := topY
      let := chartsY
      let := complexY
      let := compactY
      let := connectedY
      let U : Fin (r + 1 + 1) → Set Y := Fin.snoc T C
      have hU : ∀ j : Fin (r + 1 + 1),
          IsClosedConnectedSubmanifold (k + 1 + r) (U j) (k + 1 + r - (j : ℕ)) := by
        intro j
        cases j using Fin.lastCases with
        | last =>
            simpa only [U, Fin.snoc_last, Fin.val_last,
              show k + 1 + r - (r + 1) = k by omega] using hC
        | cast j =>
            simpa only [U, Fin.snoc_castSucc, Fin.val_castSucc] using hT j
      have hUi : ∀ j : Fin (r + 1 + 1), ∀ y ∈ U j,
          (π ∘ (a ∘ b)) y ∈ F.flag ⟨(j : ℕ), by omega⟩ := by
        intro j
        cases j using Fin.lastCases with
        | last =>
            simpa only [U, Fin.snoc_last, Fin.val_last, Function.comp_apply] using hc
        | cast j =>
            intro y hy
            have hyT : y ∈ T j := by simpa only [U, Fin.snoc_castSucc] using hy
            exact hi j (b y) (hBi j y hyT)
      refine ⟨Y, topY, chartsY, complexY, compactY, connectedY, omegaY,
        a ∘ b, U, isBlowupSequence_comp ha hb, ?_, ?_,
        finiteFlag_snoc_antitone hTa hCT, hU, hUi, ?_, ?_⟩
      · simpa only [Function.comp_assoc] using hκb
      · simpa only [U, Fin.snoc_apply_zero] using hT0
      · intro j
        cases j using Fin.lastCases with
        | last =>
            exact (finiteFlag_component_congr
              (show k = k + 1 + r - ((Fin.last (r + 1) : Fin (r + 1 + 1)) : ℕ) by
                simp only [Fin.val_last]; omega)
              (show F.flag ⟨r + 1, by omega⟩ =
                  F.flag ⟨((Fin.last (r + 1) : Fin (r + 1 + 1)) : ℕ), by omega⟩ from rfl)
              (show C = U (Fin.last (r + 1)) by simp only [U, Fin.snoc_last])
              (show k ≤ k + 1 + r by omega)
              (Nat.sub_le (k + 1 + r) ((Fin.last (r + 1) : Fin (r + 1 + 1)) : ℕ))
              hFnext.2.2 hC.2.2
              (F.smooth.2.2 ⟨((Fin.last (r + 1) : Fin (r + 1 + 1)) : ℕ), by omega⟩).2.2
              (hU (Fin.last (r + 1))).2.2
              (π ∘ (a ∘ b)) hc (hUi (Fin.last (r + 1)))).mp hchild
        | cast j =>
            exact (finiteFlag_component_congr
              (show k + 1 + r - (j : ℕ) = k + 1 + r - (j.castSucc : ℕ) from rfl)
              (show F.flag ⟨(j : ℕ), by omega⟩ =
                F.flag ⟨(j.castSucc : ℕ), by omega⟩ from rfl)
              (show T j = U j.castSucc by simp only [U, Fin.snoc_castSucc])
              (Nat.sub_le (k + 1 + r) j) (Nat.sub_le (k + 1 + r) j.castSucc)
              (F.smooth.2.2 ⟨(j : ℕ), by omega⟩).2.2 (hT j).2.2
              (F.smooth.2.2 ⟨(j.castSucc : ℕ), by omega⟩).2.2 (hU j.castSucc).2.2
              (π ∘ (a ∘ b)) (fun y hy => hi j (b y) (hBi j y hy))
              (hUi j.castSucc)).mp (hprefix j)
      · intro j
        cases j using Fin.lastCases with
        | last =>
            simpa only [U, Fin.snoc_last, Fin.val_last, Function.comp_assoc] using hCimage
        | cast j =>
            simpa only [U, Fin.snoc_castSucc, Fin.val_castSucc, Function.comp_assoc]
              using himages j

/-- The terminal partial family has every original smooth-flag field.
The original finite map and all original literal component modifications
are produced; an arbitrary reduced-space Chow domination is not an input. -/
theorem exists_flagLifting_domination_of_isBlowupSequence {n : ℕ}
    (F : OriginalFlagGeometry.{u} n) {Z : Type u} [TopologicalSpace Z]
    [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]
    {π : Z → F.carrier} (hπ : IsBlowupSequence n F.carrier Z π) :
    ∃ (W : OriginalFlagGeometry.{u} n) (a : W.carrier → Z),
      IsBlowupSequence n Z W.carrier a ∧
      IsBlowupSequence n F.carrier W.carrier (π ∘ a) ∧
      IsFlagLifting F W (π ∘ a) := by
  obtain ⟨Y, topY, chartsY, complexY, compactY, connectedY, omegaY,
    a, S, ha, hκ, hS0, hSa, hS, hi, hmods, _himages⟩ :=
    exists_partialFlag_lifting_of_isBlowupSequence F hπ n le_rfl
  let := topY
  let := chartsY
  let := complexY
  let := compactY
  let := connectedY
  let W := OriginalFlagGeometry.ofOriginal omegaY S ⟨hS0, hSa, hS⟩
  refine ⟨W, a, ha, isBlowupSequence_comp hπ ha, hκ, ?_⟩
  intro i
  have hei : (⟨(i : ℕ), by omega⟩ : Fin (n + 1)) = i := Fin.ext rfl
  refine ⟨fun _ hx => ?_, ?_⟩
  · change (π ∘ a) _ ∈ F.flag i
    simpa only [hei] using hi i _ hx
  · exact (finiteFlag_component_congr (show n - (i : ℕ) = n - (i : ℕ) from rfl)
      (show F.flag ⟨(i : ℕ), by omega⟩ = F.flag i by rw [hei])
      (show S i = W.flag i from rfl) (Nat.sub_le n i) (Nat.sub_le n i)
      (F.smooth.2.2 ⟨(i : ℕ), by omega⟩).2.2 (hS i).2.2
      (F.smooth.2.2 i).2.2 (W.smooth.2.2 i).2.2
      (π ∘ a) (hi i) (fun x hx => by simpa only [hei] using hi i x hx)).mp (hmods i)

end SGPT.Okounkov
