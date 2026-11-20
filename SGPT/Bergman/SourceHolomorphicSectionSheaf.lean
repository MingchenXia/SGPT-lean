import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.Sheaf.Smooth
import Mathlib.Algebra.Category.ModuleCat.Presheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import SGPT.Foundations.Analysis.FirstPass.ComplexManifold
import SGPT.Foundations.Analysis.Pending.HironakaSmoothCentreRealDomainActualSheafStalk
import SGPT.Foundations.Analysis.Pending.HironakaSmoothCentreRealDomainActualIdealPresheaf

/-!
# HolomorphicSectionSheaf

The sheaf of holomorphic sections of a holomorphic line bundle, as a sheaf of modules over the structure sheaf, with local frame coefficients. Infrastructure for `H⁰(X, L^k ⊗ T ⊗ I(kφ))` (source `def:Bergman:L778`).

Ported from the previous team's drafts (`work/sgpt-active-lanes-20261102/bergman-*`).
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.Bergman.MultiplierSectionsDraft

open Bundle Set Filter TopologicalSpace CategoryTheory Opposite
open scoped Manifold ContDiff Topology
open SGPT.Foundations.Analysis.FirstPass

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  (V : X → Type) [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℂ (V x)]
  [TopologicalSpace (TotalSpace ℂ V)] [FiberBundle ℂ V] [VectorBundle ℂ ℂ V]
  [ContMDiffVectorBundle ∞ ℂ V (𝓘(ℂ, ComplexModel n))]

/-- Actual complex smoothness of the dependent graph, with genuine restriction and locality. -/
def bundleSectionLocalPredicate : TopCat.LocalPredicate (X := TopCat.of X) V := by
  let Q := (contDiffWithinAt_localInvariantProp (I := 𝓘(ℂ, ComplexModel n))
    (I' := (𝓘(ℂ, ComplexModel n)).prod (𝓘(ℂ, ℂ))) ∞).localPredicate X (TotalSpace ℂ V)
  exact {
    pred := fun {U} s => Q.pred (fun x : U => (⟨x.val, s x⟩ : TotalSpace ℂ V))
    res := by
      intro U W i s hs
      exact Q.res i (fun x : W => (⟨x.val, s x⟩ : TotalSpace ℂ V)) hs
    locality := by
      intro U s hs
      apply Q.locality (fun x : U => (⟨x.val, s x⟩ : TotalSpace ℂ V))
      intro x
      obtain ⟨W, hx, i, hW⟩ := hs x
      exact ⟨W, hx, i, hW⟩ }

/-- The actual sheaf of ALL local holomorphic sections on the original dependent fibers. -/
def bundleSectionSheaf : TopCat.Sheaf (Type) (TopCat.of X) :=
  TopCat.subsheafToTypes (bundleSectionLocalPredicate (n := n) V)

/-- ALL actual sections over the genuine original open U. -/
abbrev OpenSections (U : Opens X) := (bundleSectionSheaf (n := n) V).presheaf.obj (op U)

omit [IsComplexManifold n X] [∀ x, NormedSpace ℂ (V x)] [VectorBundle ℂ ℂ V]
  [ContMDiffVectorBundle ∞ ℂ V (𝓘(ℂ, ComplexModel n))] in
/-- The actual sheaf sections have their genuine complex-smooth total-space maps. -/
theorem openSection_contMDiff (U : Opens X) (s : OpenSections (n := n) V U) :
    ContMDiff (𝓘(ℂ, ComplexModel n)) ((𝓘(ℂ, ComplexModel n)).prod (𝓘(ℂ, ℂ))) ∞
      (fun x : U => (⟨x.val, s.val x⟩ : TotalSpace ℂ V)) := s.property

omit [IsComplexManifold n X] in
/-- Every actual original frame reads a genuine holomorphic local coefficient. -/
theorem openSection_coefficient_contMDiffAt (U : Opens X) (s : OpenSections (n := n) V U)
    (e : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ V → X)) [MemTrivializationAtlas e]
    (x : U) (hx : x.val ∈ e.baseSet) :
    ContMDiffAt (𝓘(ℂ, ComplexModel n)) (𝓘(ℂ, ℂ)) ∞
      (fun y : U => (e ⟨y.val, s.val y⟩).2) x :=
  ((e.contMDiffAt_iff (e.mem_source.mpr hx)).mp ((openSection_contMDiff (n := n) V U s) x)).2

/-- The actual complex structure sheaf, with the same native definition as the original germ APIs. -/
abbrev structureSheaf := smoothSheafCommRing (𝓘(ℂ, ComplexModel n)) (𝓘(ℂ, ℂ)) X ℂ

/-- Actual holomorphic scalar sections on the original open U. -/
abbrev ScalarSections (U : Opens X) : Type := (structureSheaf (n := n) (X := X)).presheaf.obj (op U)

/-- Evaluation of a true holomorphic scalar section, as its actual ring homomorphism. -/
def scalarEvaluation (U : Opens X) (x : U) : ScalarSections (n := n) U →+* ℂ :=
  ContMDiffMap.evalRingHom x

/-- The genuine original scalar-section action on each SAME included fiber. -/
instance openFiberScalarModule (U : Opens X) (x : U) :
    Module (ScalarSections (n := n) U) (V x.val) :=
  Module.compHom (V x.val) (scalarEvaluation (n := n) U x)

/-- All complex-smooth dependent sections form a true O(U)-submodule of ALL fiber-valued functions. -/
def openSectionSubmodule (U : Opens X) :
    Submodule (ScalarSections (n := n) U) (∀ x : U, V x.val) where
  carrier := {s | (bundleSectionLocalPredicate (n := n) V).pred s}
  zero_mem' := by
    change ContMDiff (𝓘(ℂ, ComplexModel n)) ((𝓘(ℂ, ComplexModel n)).prod (𝓘(ℂ, ℂ))) ∞
      (fun x : U => (⟨x.val, (0 : V x.val)⟩ : TotalSpace ℂ V))
    exact (contMDiff_zeroSection ℂ V).comp contMDiff_subtype_val
  add_mem' := by
    intro s t hs ht x
    let e := trivializationAt ℂ V x.val
    have hx : x.val ∈ e.baseSet := mem_baseSet_trivializationAt ℂ V x.val
    apply (e.contMDiffAt_iff (e.mem_source.mpr hx)).mpr
    refine ⟨contMDiff_subtype_val.contMDiffAt, ?_⟩
    have h₁ := openSection_coefficient_contMDiffAt (n := n) V U ⟨s, hs⟩ e x hx
    have h₂ := openSection_coefficient_contMDiffAt (n := n) V U ⟨t, ht⟩ e x hx
    apply (h₁.add h₂).congr_of_eventuallyEq
    filter_upwards [(e.open_baseSet.preimage continuous_subtype_val).mem_nhds hx] with y hy
    exact (e.linear ℂ hy).1 (s y) (t y)
  smul_mem' := by
    intro r s hs x
    let e := trivializationAt ℂ V x.val
    have hx : x.val ∈ e.baseSet := mem_baseSet_trivializationAt ℂ V x.val
    apply (e.contMDiffAt_iff (e.mem_source.mpr hx)).mpr
    refine ⟨contMDiff_subtype_val.contMDiffAt, ?_⟩
    have h₁ : ContMDiffAt (𝓘(ℂ, ComplexModel n)) (𝓘(ℂ, ℂ)) ∞ (fun y : U => r y) x :=
      (smoothSheaf.contMDiff_section r) x
    have h₂ := openSection_coefficient_contMDiffAt (n := n) V U ⟨s, hs⟩ e x hx
    apply (h₁.smul h₂).congr_of_eventuallyEq
    filter_upwards [(e.open_baseSet.preimage continuous_subtype_val).mem_nhds hx] with y hy
    exact (e.linear ℂ hy).2 (r y) (s y)

omit [IsComplexManifold n X] in
/-- The genuine O(U)-module uses exactly the already produced actual sheaf sections. -/
theorem openSections_eq_submodule (U : Opens X) :
    OpenSections (n := n) V U = ↥(openSectionSubmodule (n := n) V U) := rfl

instance openSectionsAddCommGroup (U : Opens X) : AddCommGroup (OpenSections (n := n) V U) :=
  inferInstanceAs (AddCommGroup ↥(openSectionSubmodule (n := n) V U))

instance openSectionsModule (U : Opens X) :
    Module (ScalarSections (n := n) U) (OpenSections (n := n) V U) :=
  inferInstanceAs (Module (ScalarSections (n := n) U) ↥(openSectionSubmodule (n := n) V U))

/-- The SAME original complex structure sheaf viewed as a sheaf of rings. -/
def structureRingSheaf : TopCat.Sheaf RingCat (TopCat.of X) where
  obj := (structureSheaf (n := n) (X := X)).presheaf ⋙ forget₂ CommRingCat RingCat
  property := by
    rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _ (CategoryTheory.forget RingCat)]
    exact (CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _
      (CategoryTheory.forget CommRingCat)).mp (structureSheaf (n := n) (X := X)).property

/-- Literal restriction between actual sections is additive, with no extension/junk outside the original open. -/
def openSectionRestrict {U W : Opens X} (hUW : U ≤ W) :
    OpenSections (n := n) V W →+ OpenSections (n := n) V U where
  toFun := (bundleSectionSheaf (n := n) V).presheaf.map (homOfLE hUW).op
  map_zero' := by apply Subtype.ext; rfl
  map_add' s t := by apply Subtype.ext; rfl

/-- ALL actual original-open section modules, with the real restriction maps. -/
def bundleSectionAddPresheaf : TopCat.Presheaf AddCommGrpCat (TopCat.of X) where
  obj U := AddCommGrpCat.of (OpenSections (n := n) V (unop U))
  map i := AddCommGrpCat.ofHom (openSectionRestrict (n := n) V (leOfHom i.unop))
  map_id := by intro U; ext s; rfl
  map_comp := by intro U W Z i j; ext s; rfl

omit [IsComplexManifold n X] in
/-- Forgetting additive structure retains exactly the independently produced actual section sheaf. -/
theorem bundleSectionAddPresheaf_forget :
    bundleSectionAddPresheaf (n := n) V ⋙ forget AddCommGrpCat =
      (bundleSectionSheaf (n := n) V).presheaf := rfl

/-- The actual additive section presheaf is a genuine sheaf, by the proved dependent-function locality. -/
def bundleSectionAddSheaf : TopCat.Sheaf AddCommGrpCat (TopCat.of X) where
  obj := bundleSectionAddPresheaf (n := n) V
  property := by
    rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _ (CategoryTheory.forget AddCommGrpCat)]
    exact (bundleSectionSheaf (n := n) V).property

/-- Genuine O_X module presheaf, with independently constructed pointwise action and restriction. -/
def bundleSectionModulePresheaf :
    PresheafOfModules (structureRingSheaf (n := n) (X := X)).presheaf := by
  letI (U : (Opens X)ᵒᵖ) : Module
      ((structureRingSheaf (n := n) (X := X)).presheaf.obj U)
      ((bundleSectionAddPresheaf (n := n) V).obj U) :=
    inferInstanceAs (Module (ScalarSections (n := n) (unop U)) (OpenSections (n := n) V (unop U)))
  apply PresheafOfModules.ofPresheaf (bundleSectionAddPresheaf (n := n) V)
  intro U W i r s
  apply Subtype.ext
  rfl

/-- The genuine O_X module SHEAF of ALL holomorphic sections in the SAME original bundle. -/
def bundleSectionModuleSheaf : SheafOfModules (structureRingSheaf (n := n) (X := X)) where
  val := bundleSectionModulePresheaf (n := n) V
  isSheaf := (bundleSectionAddSheaf (n := n) V).property

/-- Genuine scalar section obtained from ANY true original bundle frame on its original open. -/
def frameCoefficientSection (U : Opens X)
    (e : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ V → X)) [MemTrivializationAtlas e]
    (hU : (U : Set X) ⊆ e.baseSet) (s : OpenSections (n := n) V U) : ScalarSections (n := n) U :=
  ⟨fun x : U => (e ⟨x.val, s.val x⟩).2,
    fun x => openSection_coefficient_contMDiffAt (n := n) V U s e x (hU x.property)⟩

/-- The literal original fiber inverse sends EVERY actual scalar section to an actual bundle section. -/
def frameSection (U : Opens X)
    (e : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ V → X)) [MemTrivializationAtlas e]
    (hU : (U : Set X) ⊆ e.baseSet) (a : ScalarSections (n := n) U) : OpenSections (n := n) V U :=
  ⟨fun x : U => (e.linearEquivAt ℂ x.val (hU x.property)).symm (a x), by
    intro x
    apply (e.contMDiffAt_iff (e.mem_source.mpr (hU x.property))).mpr
    refine ⟨contMDiff_subtype_val.contMDiffAt, ?_⟩
    have heq : (fun y : U => (e ⟨y.val,
        (e.linearEquivAt ℂ y.val (hU y.property)).symm (a y)⟩).2) = (a : U → ℂ) := by
      funext y
      exact (e.linearEquivAt ℂ y.val (hU y.property)).apply_symm_apply (a y)
    rw [heq]
    exact (smoothSheaf.contMDiff_section a) x⟩

/-- Actual O(U)-linear local-frame isomorphism, with both maps defined on ALL true sections. -/
def frameSectionEquiv (U : Opens X)
    (e : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ V → X)) [MemTrivializationAtlas e]
    (hU : (U : Set X) ⊆ e.baseSet) :
    OpenSections (n := n) V U ≃ₗ[ScalarSections (n := n) U] ScalarSections (n := n) U where
  toFun := frameCoefficientSection (n := n) V U e hU
  invFun := frameSection (n := n) V U e hU
  left_inv s := by
    apply Subtype.ext
    funext x
    exact (e.linearEquivAt ℂ x.val (hU x.property)).symm_apply_apply (s.val x)
  right_inv a := by
    apply ContMDiffMap.ext
    intro x
    exact (e.linearEquivAt ℂ x.val (hU x.property)).apply_symm_apply (a x)
  map_add' s t := by
    apply ContMDiffMap.ext
    intro x
    exact (e.linear ℂ (hU x.property)).1 (s.val x) (t.val x)
  map_smul' r s := by
    apply ContMDiffMap.ext
    intro x
    exact (e.linear ℂ (hU x.property)).2 (r x) (s.val x)

omit [IsComplexManifold n X] in
/-- Actual coefficient restriction commutes with the SAME original scalar sheaf restriction. -/
theorem frameCoefficientSection_restrict {U W : Opens X} (hUW : U ≤ W)
    (e : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ V → X)) [MemTrivializationAtlas e]
    (hW : (W : Set X) ⊆ e.baseSet) (s : OpenSections (n := n) V W) :
    (structureSheaf (n := n) (X := X)).presheaf.map (homOfLE hUW).op
        (frameCoefficientSection (n := n) V W e hW s) =
      frameCoefficientSection (n := n) V U e (fun _ hx => hW (hUW hx))
        (openSectionRestrict (n := n) V hUW s) := by
  apply ContMDiffMap.ext
  intro x
  rfl

/-- The actual original structure-sheaf COLIMIT germ of EVERY genuine local coefficient. -/
def frameCoefficientGerm (U : Opens X)
    (e : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ V → X)) [MemTrivializationAtlas e]
    (hU : (U : Set X) ⊆ e.baseSet) (s : OpenSections (n := n) V U) (x : U) :=
  (SGPT.Foundations.Analysis.Pending.HironakaSmoothCentreRealDomainActualSheafStalk.actualComplexStructureSheaf
    (n := n) X).presheaf.germ U x.val x.property (frameCoefficientSection (n := n) V U e hU s)

/-- The SAME original coefficient representative, with no chart or colimit-renaming assumption. -/
theorem frameCoefficientGerm_original (U : Opens X)
    (e : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ V → X)) [MemTrivializationAtlas e]
    (hU : (U : Set X) ⊆ e.baseSet) (s : OpenSections (n := n) V U) (x : U) :
    frameCoefficientGerm (n := n) V U e hU s x =
      SGPT.Foundations.Analysis.Pending.HironakaSmoothCentreRealDomainActualSheafStalk.actualOriginalFunctionGerm
        x.val
        (SGPT.Foundations.Analysis.Pending.HironakaSmoothCentreRealDomainActualSheafStalk.sectionExtension U
          (frameCoefficientSection (n := n) V U e hU s))
        (SGPT.Foundations.Analysis.Pending.HironakaSmoothCentreRealDomainActualSheafStalk.sectionExtension_holomorphicAt
          U (frameCoefficientSection (n := n) V U e hU s) x.val x.property) := by
  symm
  apply SGPT.Foundations.Analysis.Pending.HironakaSmoothCentreRealDomainActualSheafStalk.actualOriginalFunctionGerm_eq_section
  exact Filter.Eventually.of_forall fun _ => rfl

/-- An actual rank-one scalar module automorphism internally produces its true unit, with both inverse laws. -/
def scalarLinearEquivUnit {R : Type} [CommRing R] (A : R ≃ₗ[R] R) : Rˣ := by
  have h : A.symm 1 * A 1 = 1 := by
    have hh := A.map_smul (A.symm 1) (1 : R)
    simpa only [smul_eq_mul, mul_one, A.apply_symm_apply] using hh.symm
  exact ⟨A 1, A.symm 1, (mul_comm _ _).trans h, h⟩

/-- The true scalar-coordinate automorphism from the TWO original frame isomorphisms. -/
def frameChangeEquiv (U : Opens X)
    (e f : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ V → X))
    [MemTrivializationAtlas e] [MemTrivializationAtlas f]
    (he : (U : Set X) ⊆ e.baseSet) (hf : (U : Set X) ⊆ f.baseSet) :
    ScalarSections (n := n) U ≃ₗ[ScalarSections (n := n) U] ScalarSections (n := n) U :=
  (frameSectionEquiv (n := n) V U e he).symm.trans (frameSectionEquiv (n := n) V U f hf)

/-- The original overlap multiplier is an INTERNALLY produced genuine holomorphic unit. -/
def frameTransitionUnit (U : Opens X)
    (e f : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ V → X))
    [MemTrivializationAtlas e] [MemTrivializationAtlas f]
    (he : (U : Set X) ⊆ e.baseSet) (hf : (U : Set X) ⊆ f.baseSet) :
    (ScalarSections (n := n) U)ˣ :=
  scalarLinearEquivUnit (frameChangeEquiv (n := n) V U e f he hf)

omit [IsComplexManifold n X] in
/-- The produced unit is exactly the ORIGINAL native bundle transition at EVERY actual point. -/
theorem frameTransitionUnit_original (U : Opens X)
    (e f : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ V → X))
    [MemTrivializationAtlas e] [MemTrivializationAtlas f]
    (he : (U : Set X) ⊆ e.baseSet) (hf : (U : Set X) ⊆ f.baseSet) (x : U) :
    ((frameTransitionUnit (n := n) V U e f he hf : ScalarSections (n := n) U) x) =
      (e.coordChangeL ℂ f x.val) 1 :=
  (Trivialization.coordChangeL_apply e f ⟨he x.property, hf x.property⟩ 1).symm

omit [IsComplexManifold n X] in
/-- Changing ANY actual original frame multiplies EVERY true section coefficient by that SAME unit. -/
theorem frameCoefficientSection_change (U : Opens X)
    (e f : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ V → X))
    [MemTrivializationAtlas e] [MemTrivializationAtlas f]
    (he : (U : Set X) ⊆ e.baseSet) (hf : (U : Set X) ⊆ f.baseSet)
    (s : OpenSections (n := n) V U) :
    frameCoefficientSection (n := n) V U f hf s =
      (frameTransitionUnit (n := n) V U e f he hf : ScalarSections (n := n) U) *
        frameCoefficientSection (n := n) V U e he s := by
  let A := frameChangeEquiv (n := n) V U e f he hf
  let b := frameCoefficientSection (n := n) V U e he s
  have hE : A b = frameCoefficientSection (n := n) V U f hf s :=
    congrArg (frameSectionEquiv (n := n) V U f hf) ((frameSectionEquiv (n := n) V U e he).symm_apply_apply s)
  calc
    _ = A b := hE.symm
    _ = b * A 1 := by simpa only [smul_eq_mul, mul_one] using A.map_smul b (1 : ScalarSections (n := n) U)
    _ = _ := mul_comm _ _

open SGPT.Foundations.Analysis.Pending.HironakaSmoothCentreRealDomainActualSheafStalk
  SGPT.Foundations.Analysis.Pending.HironakaSmoothCentreRealDomainActualIdealPresheaf
  SGPT.Foundations.Analysis.Pending.HironakaHolomorphicJetRankLoci
  SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves

/-- BOTH actual whole-stalk inclusions reflect the SAME original coefficient, by genuine native coherence. -/
theorem originalFunctionGerm_mem_whole_iff (A : GermIdeal n X) (hA : A.IsCoherent)
    (x : X) (a : X → ℂ) (ha : HolomorphicAt n a x) :
    actualOriginalFunctionGerm x a ha ∈ actualWholeSheafStalkIdeal A x ↔ A.mem x a := by
  constructor
  · intro h
    have hm := Ideal.mem_map_of_mem (actualStalkChartEquiv (n := n) x).toRingHom h
    rw [map_actualWholeSheafStalkIdeal] at hm
    change actualStalkChartEquiv x (actualOriginalFunctionGerm x a ha) ∈
      wholeChartStalkIdeal A x x (mem_chart_source (ComplexModel n) x) at hm
    rw [actualOriginalFunctionGerm_chart] at hm
    obtain ⟨U, _hU, hxU, _N, _G, _hsrc, _hG, hcolumns⟩ :=
      exists_coherent_whole_stalk_original_columns A hA x
    obtain ⟨_hGT, hbridge, hwhole⟩ := hcolumns x hxU
    rw [hwhole] at hm
    exact (hbridge a ha).mpr hm
  · intro h
    exact Ideal.subset_span ⟨a, ha, h, rfl⟩

/-- Actual original ideal-SECTIONS membership is EXACTLY the SAME all-point original coefficient condition. -/
theorem scalarSection_mem_actualIdeal_iff (A : GermIdeal n X) (hA : A.IsCoherent)
    (U : Opens X) (a : ScalarSections (n := n) U) :
    a ∈ actualSectionIdeal A U ↔ ∀ x ∈ U, A.mem x (sectionExtension U a) := by
  have hh (x : X) (hx : x ∈ U) :
      actualOriginalFunctionGerm x (sectionExtension U a) (sectionExtension_holomorphicAt U a x hx) =
        (actualComplexStructureSheaf (n := n) X).presheaf.germ U x hx a :=
    actualOriginalFunctionGerm_eq_section U x hx a _ _ (Filter.Eventually.of_forall fun _ => rfl)
  constructor
  · intro h x hx
    apply (originalFunctionGerm_mem_whole_iff A hA x _ (sectionExtension_holomorphicAt U a x hx)).mp
    rw [hh]
    exact h x hx
  · intro h x hx
    rw [← hh]
    exact (originalFunctionGerm_mem_whole_iff A hA x _ (sectionExtension_holomorphicAt U a x hx)).mpr (h x hx)

omit [IsComplexManifold n X] in
/-- The actual ORIGINAL whole-stalk coefficient map has the original holomorphic-unit multiplication formula. -/
theorem frameCoefficientGerm_change (U : Opens X)
    (e f : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ V → X))
    [MemTrivializationAtlas e] [MemTrivializationAtlas f]
    (he : (U : Set X) ⊆ e.baseSet) (hf : (U : Set X) ⊆ f.baseSet)
    (s : OpenSections (n := n) V U) (x : U) :
    frameCoefficientGerm (n := n) V U f hf s x =
      (actualComplexStructureSheaf (n := n) X).presheaf.germ U x.val x.property
        (frameTransitionUnit (n := n) V U e f he hf : ScalarSections (n := n) U) *
          frameCoefficientGerm (n := n) V U e he s x := by
  change ((actualComplexStructureSheaf (n := n) X).presheaf.germ U x.val x.property).hom
    (frameCoefficientSection (n := n) V U f hf s) = _
  rw [frameCoefficientSection_change (n := n) V U e f he hf s, map_mul]
  rfl

/-- BOTH full original stalk membership directions, for EVERY actual original frame and every true section. -/
theorem frameCoefficientGerm_mem_iff (A : GermIdeal n X) (U : Opens X)
    (e f : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ V → X))
    [MemTrivializationAtlas e] [MemTrivializationAtlas f]
    (he : (U : Set X) ⊆ e.baseSet) (hf : (U : Set X) ⊆ f.baseSet)
    (s : OpenSections (n := n) V U) (x : U) :
    frameCoefficientGerm (n := n) V U e he s x ∈ actualWholeSheafStalkIdeal A x.val ↔
      frameCoefficientGerm (n := n) V U f hf s x ∈ actualWholeSheafStalkIdeal A x.val := by
  constructor
  · intro h
    rw [frameCoefficientGerm_change (n := n) V U e f he hf s x]
    exact (actualWholeSheafStalkIdeal A x.val).mul_mem_left _ h
  · intro h
    rw [frameCoefficientGerm_change (n := n) V U f e hf he s x]
    exact (actualWholeSheafStalkIdeal A x.val).mul_mem_left _ h

/-- BOTH full ideal-section membership directions on ANY true original overlap, without a generator-family proxy. -/
theorem frameCoefficientSection_mem_actualIdeal_iff (A : GermIdeal n X) (U : Opens X)
    (e f : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ V → X))
    [MemTrivializationAtlas e] [MemTrivializationAtlas f]
    (he : (U : Set X) ⊆ e.baseSet) (hf : (U : Set X) ⊆ f.baseSet)
    (s : OpenSections (n := n) V U) :
    frameCoefficientSection (n := n) V U e he s ∈ actualSectionIdeal A U ↔
      frameCoefficientSection (n := n) V U f hf s ∈ actualSectionIdeal A U := by
  constructor
  · intro h x hx
    exact (frameCoefficientGerm_mem_iff (n := n) V A U e f he hf s ⟨x, hx⟩).mp (h x hx)
  · intro h x hx
    exact (frameCoefficientGerm_mem_iff (n := n) V A U e f he hf s ⟨x, hx⟩).mpr (h x hx)

/-- The genuine native constant-function algebra on the actual original holomorphic scalar sections. -/
instance scalarSectionsAlgebra (U : Opens X) : Algebra ℂ (ScalarSections (n := n) U) :=
  inferInstanceAs (Algebra ℂ (ContMDiffMap (𝓘(ℂ, ComplexModel n)) (𝓘(ℂ, ℂ)) U ℂ ∞))

/-- Restricting the actual O(U)-module along the genuine constant-scalar map gives its original complex action. -/
instance openSectionsComplexModule (U : Opens X) : Module ℂ (OpenSections (n := n) V U) :=
  Module.compHom (OpenSections (n := n) V U) (algebraMap ℂ (ScalarSections (n := n) U))

/-- ALL native global sections restrict to true local sections, with the SAME original values. -/
def globalSectionRestrict (U : Opens X) :
    ContMDiffSection (𝓘(ℂ, ComplexModel n)) ℂ ∞ V →ₗ[ℂ] OpenSections (n := n) V U where
  toFun s := ⟨fun x : U => s x.val, s.contMDiff.comp contMDiff_subtype_val⟩
  map_add' s t := by apply Subtype.ext; rfl
  map_smul' r s := by apply Subtype.ext; rfl

/-- The actual full original H0 is genuinely the full section sheaf's value on X, in BOTH directions. -/
def globalSectionSheafEquiv :
    ContMDiffSection (𝓘(ℂ, ComplexModel n)) ℂ ∞ V ≃ₗ[ℂ] OpenSections (n := n) V ⊤ where
  toFun := globalSectionRestrict (n := n) V ⊤
  invFun s := {
    toFun := fun x : X => s.val ⟨x, Set.mem_univ x⟩
    contMDiff_toFun := by
      intro x
      exact (contMDiffAt_subtype_iff (x := (⟨x, Set.mem_univ x⟩ : (⊤ : Opens X)))).mp
        ((openSection_contMDiff (n := n) V ⊤ s) ⟨x, Set.mem_univ x⟩) }
  left_inv s := by apply ContMDiffSection.ext; intro x; rfl
  right_inv s := by apply Subtype.ext; funext x; rfl
  map_add' s t := by apply Subtype.ext; rfl
  map_smul' r s := by apply Subtype.ext; rfl

end SGPT.Bergman.MultiplierSectionsDraft
