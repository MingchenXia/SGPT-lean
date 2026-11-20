import SGPT.Okounkov.AmbientIntrinsicBlowupAncestors
import SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
import SGPT.Foundations.Analysis.Pending.AnalyticSubsetPreimage

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov

open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.RegularLocusDense
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending
open AnalyticModificationLocalDiscrepancy

/-- Actual intrinsic thinness produces empty relative interior of the same
centre on every containing ancestor. -/
theorem interior_ancestorCentre_eq_empty
    {X : Type u} [TopologicalSpace X] {N A : Set X}
    (hNA : N ⊆ A) (C : Set N) (hCi : interior C = ∅) :
    interior ((Subtype.val : A → X) ⁻¹' (Subtype.val '' C)) = ∅ := by
  apply interior_eq_empty_iff_dense_compl.mpr
  apply Subtype.dense_iff.mpr
  have himage : (Subtype.val : A → X) ''
      ((Subtype.val : A → X) ⁻¹' (Subtype.val '' C))ᶜ = A \ Subtype.val '' C := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p.2, hp⟩
    · intro hx
      exact ⟨⟨x, hx.1⟩, hx.2, rfl⟩
  rw [himage]
  exact ancestor_subset_closure_sdiff_of_subtype_thin hNA C hCi

/-- The actual defining strict closure produces empty interior of the whole
relative inverse-image centre on the manufactured ancestor carrier. -/
theorem interior_strictAncestorCentre_eq_empty
    {n : ℕ} {X Y : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    {N A : Set X} (hNA : N ⊆ A) (hAc : IsClosed A)
    (C : Set N) (hCi : interior C = ∅) {a : Y → X}
    (ha : IsBlowupAlong n (Subtype.val '' C) a) :
    interior ((fun y : strictTransform n a A => a y.1) ⁻¹' (Subtype.val '' C)) = ∅ := by
  apply interior_eq_empty_iff_dense_compl.mpr
  apply Subtype.dense_iff.mpr
  have heq := BlowupStrictIdeal.geoStrictTransform_eq_strictTransform ha
    (ancestor_subset_closure_sdiff_of_subtype_thin hNA C hCi)
  have himage : (Subtype.val : strictTransform n a A → Y) ''
      ((fun y : strictTransform n a A => a y.1) ⁻¹' (Subtype.val '' C))ᶜ =
        a ⁻¹' (A \ Subtype.val '' C) := by
    ext y
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨HironakaAdmissibleCalculus.strictTransform_subset_preimage
        ha.contMDiff.continuous hAc p.2, hp⟩
    · intro hy
      have hyS : y ∈ strictTransform n a A := by
        rw [← heq]
        exact subset_closure hy
      exact ⟨⟨y, hyS⟩, hy.2, rfl⟩
  rw [himage, ← heq]
  exact Subset.rfl

/-- Restrict the genuine ambient off-centre section to the same literal
strict ancestor and manufacture both inverse equations in its inherited atlas. -/
theorem exists_strictAncestor_section_compl
    {n d : ℕ} {X Y : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    {N A : Set X} (hd : d ≤ n) (hNA : N ⊆ A) (hAc : IsClosed A)
    (hA : ∀ x ∈ A, RegularAtDim (n := n) A x d)
    (C : Set N) (hCi : interior C = ∅) {a : Y → X}
    (ha : IsBlowupAlong n (Subtype.val '' C) a) :
    let S := strictTransform n a A
    ∃ hS : ∀ y ∈ S, RegularAtDim (n := n) S y d,
      ∃ hi : ∀ y ∈ S, a y ∈ A,
        letI := SubmanifoldChartedSpace.chartedSpace hd hA
        letI := SubmanifoldChartedSpace.chartedSpace hd hS
        let B : Set A := Subtype.val ⁻¹' (Subtype.val '' C)
        let hBc : IsClosed B := ha.1.1.preimage continuous_subtype_val
        let U : TopologicalSpace.Opens A := ⟨Bᶜ, hBc.isOpen_compl⟩
        let r : S → A := fun y => ⟨a y.1, hi y.1 y.2⟩
        ∃ s : U → S,
          ContMDiff 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel d) ∞ s ∧
          r ∘ s = Subtype.val ∧
          (∀ y : S, ∀ hy : a y.1 ∉ Subtype.val '' C, s ⟨r y, hy⟩ = y) ∧
          s '' univ = {y : S | a y.1 ∉ Subtype.val '' C} := by
  classical
  let D : Set X := Subtype.val '' C
  let S := strictTransform n a A
  obtain ⟨_, hS, hi, _⟩ := regularAtDim_strictTransform_ancestor hNA hAc hA C hCi ha
  have hi' : ∀ y ∈ S, a y ∈ A := fun _ hy => hi hy
  refine ⟨hS, hi', ?_⟩
  let := SubmanifoldChartedSpace.chartedSpace hd hA
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hd hA
  let := SubmanifoldChartedSpace.chartedSpace hd hS
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hd hS
  let B : Set A := Subtype.val ⁻¹' D
  let hBc : IsClosed B := ha.1.1.preimage continuous_subtype_val
  let U : TopologicalSpace.Opens A := ⟨Bᶜ, hBc.isOpen_compl⟩
  let O : TopologicalSpace.Opens X := ⟨Dᶜ, ha.1.1.isOpen_compl⟩
  let r : S → A := fun y => ⟨a y.1, hi' y.1 y.2⟩
  obtain ⟨s0, hs0, has0, hs0a⟩ := BlowupIsomorphismOff.exists_section_compl ha
  let j : U → O := fun x => ⟨x.1.1, x.2⟩
  have hj0 : ContMDiff 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel n) ∞
      (fun x : U => x.1.1) :=
    (SubmanifoldChartedSpace.contMDiff_val hd hA).comp contMDiff_subtype_val
  have hj : ContMDiff 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel n) ∞ j :=
    BlowupRestrictOpen.contMDiff_opens_mk hj0 (fun x => x.2)
  have hproj : ∀ x : U, a (s0 (j x)) = x.1.1 :=
    fun x => congrFun has0 (j x)
  have hland : ∀ x : U, s0 (j x) ∈ S := by
    intro x
    have heq := BlowupStrictIdeal.geoStrictTransform_eq_strictTransform ha
      (ancestor_subset_closure_sdiff_of_subtype_thin hNA C hCi)
    rw [show S = strictTransform n a A from rfl, ← heq]
    apply subset_closure
    change a (s0 (j x)) ∈ A \ D
    rw [hproj]
    exact ⟨x.1.2, x.2⟩
  let s : U → S := fun x => ⟨s0 (j x), hland x⟩
  have hs : ContMDiff 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel d) ∞ s :=
    SubmanifoldCodRestrict.contMDiff_codRestrict hd hS (hs0.comp hj) hland
  have hrs : r ∘ s = Subtype.val := by
    funext x
    exact Subtype.ext (hproj x)
  have hsr : ∀ y : S, ∀ hy : a y.1 ∉ D, s ⟨r y, hy⟩ = y := by
    intro y hy
    exact Subtype.ext (hs0a y.1 hy)
  refine ⟨s, hs, hrs, hsr, ?_⟩
  ext y
  constructor
  · rintro ⟨x, _, rfl⟩
    show a (s0 (j x)) ∉ D
    rw [hproj]
    exact x.2
  · intro hy
    exact ⟨⟨r y, hy⟩, mem_univ _, hsr y hy⟩

/-- The same actual inherited-atlas restriction is a genuine analytic
modification, including closed analytic thin sets and whole off-set inverse
data. No compactness or connectedness is imposed. -/
theorem isAnalyticModification_strictAncestorRestriction
    {n d : ℕ} {X Y : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    {N A : Set X} (hd : d ≤ n) (hNA : N ⊆ A) (hAc : IsClosed A)
    (hA : ∀ x ∈ A, RegularAtDim (n := n) A x d)
    (C : Set N) (hCi : interior C = ∅) {a : Y → X}
    (ha : IsBlowupAlong n (Subtype.val '' C) a) :
    let S := strictTransform n a A
    ∃ hS : ∀ y ∈ S, RegularAtDim (n := n) S y d,
      ∃ hi : ∀ y ∈ S, a y ∈ A,
        letI := SubmanifoldChartedSpace.chartedSpace hd hA
        letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hd hA
        letI := SubmanifoldChartedSpace.chartedSpace hd hS
        letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hd hS
        IsAnalyticModification (n := d) (fun y : S => (⟨a y.1, hi y.1 y.2⟩ : A)) := by
  classical
  let D : Set X := Subtype.val '' C
  let S := strictTransform n a A
  obtain ⟨hS, hi, sigma, hsigma, hrsigma, hsigmaR, _himage⟩ :=
    exists_strictAncestor_section_compl hd hNA hAc hA C hCi ha
  refine ⟨hS, hi, ?_⟩
  let := SubmanifoldChartedSpace.chartedSpace hd hA
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hd hA
  let := SubmanifoldChartedSpace.chartedSpace hd hS
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hd hS
  let r : S → A := fun y => ⟨a y.1, hi y.1 y.2⟩
  let B : Set A := Subtype.val ⁻¹' D
  let E : Set S := r ⁻¹' B
  have hr : ContMDiff 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel d) ∞ r :=
    SubmanifoldCodRestrict.contMDiff_restrictPreimage hd hA hd hS ha.contMDiff hi
  have hrp : IsProperMap r := by
    apply isProperMap_of_comp_of_t2 hr.continuous continuous_subtype_val
    exact (HironakaLocalPrincipalization.isProperMap_of_isBlowupAlong ha).comp
      (show IsClosed S from isClosed_closure).isProperMap_subtypeVal
  have hBc : IsClosed B := ha.1.1.preimage continuous_subtype_val
  have hEc : IsClosed E := hBc.preimage hr.continuous
  have hBi : interior B = ∅ := interior_ancestorCentre_eq_empty hNA C hCi
  have hEi : interior E = ∅ := interior_strictAncestorCentre_eq_empty hNA hAc C hCi ha
  have hBa : IsComplexAnalyticSubset (n := d) B :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage
      (SubmanifoldChartedSpace.contMDiff_val hd hA)
      (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold ha.1)
  have hEa : IsComplexAnalyticSubset (n := d) E :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hr hBa
  let U : TopologicalSpace.Opens A := ⟨Bᶜ, hBc.isOpen_compl⟩
  have hsurj : Function.Surjective r := by
    have hrange : IsClosed (range r) := hrp.isClosedMap.isClosed_range
    have hsub : Bᶜ ⊆ range r := by
      intro x hx
      exact ⟨sigma (⟨x, hx⟩ : U), congrFun hrsigma (⟨x, hx⟩ : U)⟩
    have hclosure : closure Bᶜ ⊆ range r := closure_minimal hsub hrange
    rw [(interior_eq_empty_iff_dense_compl.mp hBi).closure_eq] at hclosure
    exact fun x => hclosure (mem_univ x)
  let s : A → S := fun x => Classical.choose (hsurj x)
  have hrs : ∀ x, r (s x) = x := fun x => Classical.choose_spec (hsurj x)
  have hsame : (fun x : U => s x.1) = sigma := by
    funext x
    have hnon : a (s x.1).1 ∉ D := by
      have heq : a (s x.1).1 = x.1.1 := congrArg Subtype.val (hrs x.1)
      rw [heq]
      exact x.2
    have hleft := hsigmaR (s x.1) hnon
    have hx : (⟨r (s x.1), hnon⟩ : U) = x := Subtype.ext (hrs x.1)
    rw [hx] at hleft
    exact hleft.symm
  have hs : ContMDiffOn 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel d) ∞ s Bᶜ := by
    have hrest : ContMDiff 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel d) ∞
        (fun x : U => s x.1) := hsame.symm ▸ hsigma
    intro x hx
    exact (contMDiffAt_subtype_iff.mp (hrest (⟨x, hx⟩ : U))).contMDiffWithinAt
  refine ⟨hr, hrp, E, B, s, hEc, hEa, hEi, hBc, hBa, hBi, rfl, hs,
    fun x _ => hrs x, ?_⟩
  intro y hy
  have hnon : a y.1 ∉ D := hy
  have heq := congrFun hsame (⟨r y, hnon⟩ : U)
  exact heq.trans (hsigmaR y hnon)

end SGPT.Okounkov
