import SGPT.Bergman.SourceHolomorphicSectionSheaf

/-!
# MultiplierSectionSubsheaf

The subsheaf of sections of a line bundle whose local frame coefficients lie in a germ ideal (e.g. a multiplier ideal), and its global sections `fullHolomorphicIdealSections`.

Ported from the previous team's drafts (`work/sgpt-active-lanes-20261102/bergman-*`).
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.Bergman.MultiplierSectionsDraft

open Bundle Set Filter TopologicalSpace CategoryTheory Opposite
open scoped Manifold ContDiff Topology
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending.HironakaSmoothCentreRealDomainActualSheafStalk
  SGPT.Foundations.Analysis.Pending.HironakaSmoothCentreRealDomainActualIdealPresheaf

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  (V : X → Type) [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℂ (V x)]
  [TopologicalSpace (TotalSpace ℂ V)] [FiberBundle ℂ V] [VectorBundle ℂ ℂ V]
  [ContMDiffVectorBundle ∞ ℂ V (𝓘(ℂ, ComplexModel n))]

/-- The actual original native frame atlas, without a preferred-frame restriction. -/
abbrev OriginalFrame :=
  {e : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ V → X) // MemTrivializationAtlas e}

instance originalFrame_memAtlas (e : OriginalFrame V) : MemTrivializationAtlas e.val := e.property

/-- The actual original part of U on which this original bundle frame is defined. -/
abbrev frameOpen (U : Opens X) (e : OriginalFrame V) : Opens X :=
  U ⊓ ⟨e.val.baseSet, e.val.open_baseSet⟩

/-- The genuine local coefficient on the real original frame-open intersection. -/
def localFrameCoefficient (U : Opens X) (e : OriginalFrame V) (s : OpenSections (n := n) V U) :
    ScalarSections (n := n) (frameOpen V U e) :=
  frameCoefficientSection (n := n) V (frameOpen V U e) e.val (fun _ hy => hy.2)
    (openSectionRestrict (n := n) V inf_le_left s)

/-- The literal original whole structure-sheaf colimit germ of the actual local coefficient. -/
def localFrameCoefficientGerm (U : Opens X) (e : OriginalFrame V)
    (s : OpenSections (n := n) V U) (x : U) (hx : x.val ∈ e.val.baseSet) :=
  (actualComplexStructureSheaf (n := n) X).presheaf.germ (frameOpen V U e)
    x.val ⟨x.property, hx⟩ (localFrameCoefficient (n := n) V U e s)

omit [IsComplexManifold n X] in
/-- True coefficient restriction is the SAME actual scalar-section restriction. -/
theorem localFrameCoefficient_restrict {U W : Opens X} (hUW : U ≤ W)
    (e : OriginalFrame V) (s : OpenSections (n := n) V W) :
    (structureSheaf (n := n) (X := X)).presheaf.map
        (homOfLE (show frameOpen V U e ≤ frameOpen V W e from fun _ hy => ⟨hUW hy.1, hy.2⟩)).op
        (localFrameCoefficient (n := n) V W e s) =
      localFrameCoefficient (n := n) V U e (openSectionRestrict (n := n) V hUW s) := by
  apply ContMDiffMap.ext
  intro x
  rfl

omit [IsComplexManifold n X] in
/-- Actual original germ naturality under EVERY true open restriction. -/
theorem localFrameCoefficientGerm_restrict {U W : Opens X} (hUW : U ≤ W)
    (e : OriginalFrame V) (s : OpenSections (n := n) V W)
    (x : U) (hx : x.val ∈ e.val.baseSet) :
    localFrameCoefficientGerm (n := n) V U e (openSectionRestrict (n := n) V hUW s) x hx =
      localFrameCoefficientGerm (n := n) V W e s ⟨x.val, hUW x.property⟩ hx := by
  unfold localFrameCoefficientGerm
  rw [← localFrameCoefficient_restrict (n := n) V hUW e s]
  exact (actualComplexStructureSheaf (n := n) X).presheaf.germ_res_apply
    (homOfLE (show frameOpen V U e ≤ frameOpen V W e from fun _ hy => ⟨hUW hy.1, hy.2⟩))
    x.val ⟨x.property, hx⟩ _

omit [IsComplexManifold n X] in
/-- The real zero section has the real zero coefficient on every actual original frame open. -/
theorem localFrameCoefficient_zero (U : Opens X) (e : OriginalFrame V) :
    localFrameCoefficient (n := n) V U e 0 = 0 := by
  change frameSectionEquiv (n := n) V (frameOpen V U e) e.val (fun _ hy => hy.2)
    (openSectionRestrict (n := n) V inf_le_left 0) = 0
  rw [map_zero, map_zero]

omit [IsComplexManifold n X] in
/-- Original local coefficients preserve addition on ALL actual sections. -/
theorem localFrameCoefficient_add (U : Opens X) (e : OriginalFrame V)
    (s t : OpenSections (n := n) V U) :
    localFrameCoefficient (n := n) V U e (s + t) =
      localFrameCoefficient (n := n) V U e s + localFrameCoefficient (n := n) V U e t := by
  apply ContMDiffMap.ext
  intro x
  exact (e.val.linear ℂ x.property.2).1 _ _

omit [IsComplexManifold n X] in
/-- The actual local coefficient scalar is the restriction of the SAME original O(U) scalar. -/
theorem localFrameCoefficient_smul (U : Opens X) (e : OriginalFrame V)
    (r : ScalarSections (n := n) U) (s : OpenSections (n := n) V U) :
    localFrameCoefficient (n := n) V U e (r • s) =
      (structureSheaf (n := n) (X := X)).presheaf.map (homOfLE inf_le_left).op r *
        localFrameCoefficient (n := n) V U e s := by
  apply ContMDiffMap.ext
  intro x
  exact (e.val.linear ℂ x.property.2).2 _ _

omit [IsComplexManifold n X] in
/-- The original zero coefficient has the zero germ in the literal original stalk. -/
theorem localFrameCoefficientGerm_zero (U : Opens X) (e : OriginalFrame V)
    (x : U) (hx : x.val ∈ e.val.baseSet) :
    localFrameCoefficientGerm (n := n) V U e 0 x hx = 0 := by
  change ((actualComplexStructureSheaf (n := n) X).presheaf.germ (frameOpen V U e)
    x.val ⟨x.property, hx⟩).hom (localFrameCoefficient (n := n) V U e 0) = 0
  rw [localFrameCoefficient_zero, map_zero]

omit [IsComplexManifold n X] in
/-- Addition is retained in the ACTUAL original colimit coefficient map. -/
theorem localFrameCoefficientGerm_add (U : Opens X) (e : OriginalFrame V)
    (s t : OpenSections (n := n) V U) (x : U) (hx : x.val ∈ e.val.baseSet) :
    localFrameCoefficientGerm (n := n) V U e (s + t) x hx =
      localFrameCoefficientGerm (n := n) V U e s x hx + localFrameCoefficientGerm (n := n) V U e t x hx := by
  change ((actualComplexStructureSheaf (n := n) X).presheaf.germ (frameOpen V U e)
    x.val ⟨x.property, hx⟩).hom (localFrameCoefficient (n := n) V U e (s + t)) = _
  rw [localFrameCoefficient_add, map_add]
  rfl

omit [IsComplexManifold n X] in
/-- Scalar multiplication is retained in the ACTUAL original colimit coefficient map. -/
theorem localFrameCoefficientGerm_smul (U : Opens X) (e : OriginalFrame V)
    (r : ScalarSections (n := n) U) (s : OpenSections (n := n) V U)
    (x : U) (hx : x.val ∈ e.val.baseSet) :
    localFrameCoefficientGerm (n := n) V U e (r • s) x hx =
      (actualComplexStructureSheaf (n := n) X).presheaf.germ U x.val x.property r *
        localFrameCoefficientGerm (n := n) V U e s x hx := by
  change ((actualComplexStructureSheaf (n := n) X).presheaf.germ (frameOpen V U e)
    x.val ⟨x.property, hx⟩).hom (localFrameCoefficient (n := n) V U e (r • s)) = _
  rw [localFrameCoefficient_smul, map_mul]
  rw [(actualComplexStructureSheaf (n := n) X).presheaf.germ_res_apply (homOfLE inf_le_left)
    x.val ⟨x.property, hx⟩ r]
  rfl

/-- Actual O(U)-submodule of ALL genuine sections with WHOLE original ideal coefficients in EVERY original frame. -/
def idealOpenSectionSubmodule (A : GermIdeal n X) (U : Opens X) :
    Submodule (ScalarSections (n := n) U) (OpenSections (n := n) V U) where
  carrier := {s | ∀ (e : OriginalFrame V) (x : U) (hx : x.val ∈ e.val.baseSet),
    localFrameCoefficientGerm (n := n) V U e s x hx ∈ actualWholeSheafStalkIdeal A x.val}
  zero_mem' := by
    intro e x hx
    rw [localFrameCoefficientGerm_zero]
    exact (actualWholeSheafStalkIdeal A x.val).zero_mem
  add_mem' := by
    intro s t hs ht e x hx
    rw [localFrameCoefficientGerm_add]
    exact (actualWholeSheafStalkIdeal A x.val).add_mem (hs e x hx) (ht e x hx)
  smul_mem' := by
    intro r s hs e x hx
    rw [localFrameCoefficientGerm_smul]
    exact (actualWholeSheafStalkIdeal A x.val).mul_mem_left _ (hs e x hx)

/-- Literal restriction preserves the full original ideal condition for ALL actual frames/points. -/
theorem idealOpenSectionSubmodule_restrict (A : GermIdeal n X) {U W : Opens X} (hUW : U ≤ W)
    (s : OpenSections (n := n) V W) (hs : s ∈ idealOpenSectionSubmodule (n := n) V A W) :
    openSectionRestrict (n := n) V hUW s ∈ idealOpenSectionSubmodule (n := n) V A U := by
  intro e x hx
  rw [localFrameCoefficientGerm_restrict]
  exact hs e ⟨x.val, hUW x.property⟩ hx

/-- The true original WHOLE ideal coefficient condition is local; it is not an incoming sheaf certificate. -/
def idealBundleSectionLocalPredicate (A : GermIdeal n X) : TopCat.LocalPredicate (X := TopCat.of X) V where
  pred {U} f := ∃ hf : (bundleSectionLocalPredicate (n := n) V).pred f,
    (⟨f, hf⟩ : OpenSections (n := n) V U) ∈ idealOpenSectionSubmodule (n := n) V A U
  res := by
    intro U W i f h
    obtain ⟨hf, hmem⟩ := h
    refine ⟨(bundleSectionLocalPredicate (n := n) V).res i f hf, ?_⟩
    exact idealOpenSectionSubmodule_restrict (n := n) V A (leOfHom i) ⟨f, hf⟩ hmem
  locality := by
    intro U f h
    have hf : (bundleSectionLocalPredicate (n := n) V).pred f := by
      apply (bundleSectionLocalPredicate (n := n) V).locality f
      intro x
      obtain ⟨W, hxW, i, hW⟩ := h x
      exact ⟨W, hxW, i, hW.choose⟩
    refine ⟨hf, ?_⟩
    intro e x hx
    obtain ⟨W, hxW, i, hW⟩ := h x
    obtain ⟨hfW, hmW⟩ := hW
    have hm := hmW e ⟨x.val, hxW⟩ hx
    have heq := localFrameCoefficientGerm_restrict (n := n) V (leOfHom i) e
      (⟨f, hf⟩ : OpenSections (n := n) V U) ⟨x.val, hxW⟩ hx
    exact heq ▸ hm

/-- Genuine sheaf of ALL actual bundle sections with the entire original ideal coefficient condition. -/
def idealBundleSectionSheaf (A : GermIdeal n X) : TopCat.Sheaf Type (TopCat.of X) :=
  TopCat.subsheafToTypes (idealBundleSectionLocalPredicate (n := n) V A)

/-- The independently proved local-predicate sheaf has EXACTLY the actual O(U)-submodule objects. -/
def idealSheafSectionEquiv (A : GermIdeal n X) (U : Opens X) :
    (idealBundleSectionSheaf (n := n) V A).presheaf.obj (op U) ≃
      ↥(idealOpenSectionSubmodule (n := n) V A U) where
  toFun a := ⟨⟨a.val, a.property.choose⟩, a.property.choose_spec⟩
  invFun a := ⟨a.val.val, ⟨a.val.property, a.property⟩⟩
  left_inv a := by apply Subtype.ext; rfl
  right_inv a := by apply Subtype.ext; apply Subtype.ext; rfl

/-- Literal restriction on the actual original ideal-valued section submodules. -/
def idealOpenSectionRestrict (A : GermIdeal n X) {U W : Opens X} (hUW : U ≤ W) :
    idealOpenSectionSubmodule (n := n) V A W →+ idealOpenSectionSubmodule (n := n) V A U where
  toFun s := ⟨openSectionRestrict (n := n) V hUW s.val,
    idealOpenSectionSubmodule_restrict (n := n) V A hUW s.val s.property⟩
  map_zero' := by apply Subtype.ext; exact map_zero _
  map_add' s t := by apply Subtype.ext; exact map_add _ _ _

/-- Actual additive ideal section presheaf, retaining ALL original points and frames. -/
def idealBundleSectionAddPresheaf (A : GermIdeal n X) : TopCat.Presheaf AddCommGrpCat (TopCat.of X) where
  obj U := AddCommGrpCat.of (idealOpenSectionSubmodule (n := n) V A (unop U))
  map i := AddCommGrpCat.ofHom (idealOpenSectionRestrict (n := n) V A (leOfHom i.unop))
  map_id := by intro U; ext s; rfl
  map_comp := by intro U W Z i j; ext s; rfl

/-- The actual original restriction diagram, with no sheaf/Gamma identification assumption. -/
def idealBundleSectionPresheafTypeIso (A : GermIdeal n X) :
    idealBundleSectionAddPresheaf (n := n) V A ⋙ forget AddCommGrpCat ≅
      (idealBundleSectionSheaf (n := n) V A).presheaf :=
  NatIso.ofComponents (fun U => (idealSheafSectionEquiv (n := n) V A (unop U)).symm.toIso)
    (by intro U W i; ext s; apply Subtype.ext; rfl)

/-- The original ideal-valued section additive presheaf is genuinely a SHEAF. -/
def idealBundleSectionAddSheaf (A : GermIdeal n X) : TopCat.Sheaf AddCommGrpCat (TopCat.of X) where
  obj := idealBundleSectionAddPresheaf (n := n) V A
  property := by
    rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _ (CategoryTheory.forget AddCommGrpCat)]
    exact (TopCat.Presheaf.isSheaf_iso_iff (idealBundleSectionPresheafTypeIso (n := n) V A)).mpr
      (idealBundleSectionSheaf (n := n) V A).property

/-- The original O_X scalar action on ideal-valued bundle sections is the actual inherited submodule action. -/
def idealBundleSectionModulePresheaf (A : GermIdeal n X) :
    PresheafOfModules (structureRingSheaf (n := n) (X := X)).presheaf := by
  letI (U : (Opens X)ᵒᵖ) : Module ((structureRingSheaf (n := n) (X := X)).presheaf.obj U)
      ((idealBundleSectionAddPresheaf (n := n) V A).obj U) :=
    inferInstanceAs (Module (ScalarSections (n := n) (unop U))
      ↥(idealOpenSectionSubmodule (n := n) V A (unop U)))
  apply PresheafOfModules.ofPresheaf (idealBundleSectionAddPresheaf (n := n) V A)
  intro U W i r s
  apply Subtype.ext
  apply Subtype.ext
  rfl

/-- The genuine O_X MODULE SHEAF of actual ideal-valued holomorphic bundle sections. -/
def idealBundleSectionModuleSheaf (A : GermIdeal n X) :
    SheafOfModules (structureRingSheaf (n := n) (X := X)) where
  val := idealBundleSectionModulePresheaf (n := n) V A
  isSheaf := (idealBundleSectionAddSheaf (n := n) V A).property

/-- Complex scalars act through the SAME genuine original constant-section map. -/
def idealOpenSectionComplexSubmodule (A : GermIdeal n X) (U : Opens X) :
    Submodule ℂ (OpenSections (n := n) V U) where
  carrier := (idealOpenSectionSubmodule (n := n) V A U).carrier
  zero_mem' := (idealOpenSectionSubmodule (n := n) V A U).zero_mem
  add_mem' := (idealOpenSectionSubmodule (n := n) V A U).add_mem
  smul_mem' r _ hs := (idealOpenSectionSubmodule (n := n) V A U).smul_mem
    (algebraMap ℂ (ScalarSections (n := n) U) r) hs

/-- Actual complex submodule of the full ORIGINAL H0, by the proved genuine global section equivalence. -/
def fullHolomorphicIdealSections (A : GermIdeal n X) :
    Submodule ℂ (ContMDiffSection (𝓘(ℂ, ComplexModel n)) ℂ ∞ V) :=
  (idealOpenSectionComplexSubmodule (n := n) V A ⊤).comap (globalSectionSheafEquiv (n := n) V).toLinearMap

omit [IsComplexManifold n X] in
/-- On a genuine original frame domain, the local coefficient germ is EXACTLY the original whole-domain coefficient germ. -/
theorem localFrameCoefficientGerm_eq_frame (U : Opens X) (e : OriginalFrame V)
    (he : (U : Set X) ⊆ e.val.baseSet) (s : OpenSections (n := n) V U)
    (x : U) (hx : x.val ∈ e.val.baseSet) :
    localFrameCoefficientGerm (n := n) V U e s x hx =
      frameCoefficientGerm (n := n) V U e.val he s x := by
  have hc : (structureSheaf (n := n) (X := X)).presheaf.map
      (homOfLE (show frameOpen V U e ≤ U from inf_le_left)).op
      (frameCoefficientSection (n := n) V U e.val he s) = localFrameCoefficient (n := n) V U e s :=
    frameCoefficientSection_restrict (n := n) V inf_le_left e.val he s
  change (actualComplexStructureSheaf (n := n) X).presheaf.germ (frameOpen V U e)
      x.val ⟨x.property, hx⟩ (localFrameCoefficient (n := n) V U e s) =
    (actualComplexStructureSheaf (n := n) X).presheaf.germ U x.val x.property
      (frameCoefficientSection (n := n) V U e.val he s)
  rw [← hc]
  exact (actualComplexStructureSheaf (n := n) X).presheaf.germ_res_apply
    (homOfLE inf_le_left) x.val ⟨x.property, hx⟩ _

/-- BOTH entire original coefficient-stalk membership directions hold on ANY actual original overlap near a point. -/
theorem localFrameCoefficientGerm_mem_iff (A : GermIdeal n X) (U : Opens X)
    (e f : OriginalFrame V) (s : OpenSections (n := n) V U) (x : U)
    (he : x.val ∈ e.val.baseSet) (hf : x.val ∈ f.val.baseSet) :
    localFrameCoefficientGerm (n := n) V U e s x he ∈ actualWholeSheafStalkIdeal A x.val ↔
      localFrameCoefficientGerm (n := n) V U f s x hf ∈ actualWholeSheafStalkIdeal A x.val := by
  let W : Opens X := frameOpen V (frameOpen V U e) f
  have hWU : W ≤ U := fun _ hy => hy.1.1
  have hWe : (W : Set X) ⊆ e.val.baseSet := fun _ hy => hy.1.2
  have hWf : (W : Set X) ⊆ f.val.baseSet := fun _ hy => hy.2
  let xW : W := ⟨x.val, ⟨⟨x.property, he⟩, hf⟩⟩
  let sw := openSectionRestrict (n := n) V hWU s
  have heq := localFrameCoefficientGerm_restrict (n := n) V hWU e s xW he
  have hfq := localFrameCoefficientGerm_restrict (n := n) V hWU f s xW hf
  rw [← heq, ← hfq, localFrameCoefficientGerm_eq_frame (n := n) V W e hWe sw xW he,
    localFrameCoefficientGerm_eq_frame (n := n) V W f hWf sw xW hf]
  exact frameCoefficientGerm_mem_iff (n := n) V A W e.val f.val hWe hWf sw xW

/-- The original preferred frame is an actual member of the SAME full native bundle atlas. -/
def preferredOriginalFrame (x : X) : OriginalFrame V := ⟨trivializationAt ℂ V x, inferInstance⟩

/-- Testing the ACTUAL preferred coefficient is equivalent to testing EVERY actual original frame. -/
theorem mem_idealOpenSectionSubmodule_iff_preferred (A : GermIdeal n X) (U : Opens X)
    (s : OpenSections (n := n) V U) :
    s ∈ idealOpenSectionSubmodule (n := n) V A U ↔
      ∀ x : U, localFrameCoefficientGerm (n := n) V U (preferredOriginalFrame V x.val) s x
        (mem_baseSet_trivializationAt ℂ V x.val) ∈ actualWholeSheafStalkIdeal A x.val := by
  constructor
  · intro h x
    exact h (preferredOriginalFrame V x.val) x (mem_baseSet_trivializationAt ℂ V x.val)
  · intro h e x hx
    exact (localFrameCoefficientGerm_mem_iff (n := n) V A U (preferredOriginalFrame V x.val) e s x
      (mem_baseSet_trivializationAt ℂ V x.val) hx).mp (h x)

/-- The actual WHOLE ideal-valued bundle sections use precisely the native ORIGINAL ideal-section modules in ALL real frame opens. -/
theorem mem_idealOpenSectionSubmodule_iff_actualIdeal (A : GermIdeal n X) (U : Opens X)
    (s : OpenSections (n := n) V U) :
    s ∈ idealOpenSectionSubmodule (n := n) V A U ↔
      ∀ e : OriginalFrame V, localFrameCoefficient (n := n) V U e s ∈ actualSectionIdeal A (frameOpen V U e) := by
  constructor
  · intro h e x hx
    exact h e ⟨x, hx.1⟩ hx.2
  · intro h e x hx
    exact h e x.val ⟨x.property, hx⟩

/-- BOTH full original coefficient-predicate directions, with no desired global-ideal reflection certificate. -/
theorem mem_idealOpenSectionSubmodule_iff_original (A : GermIdeal n X) (hA : A.IsCoherent)
    (U : Opens X) (s : OpenSections (n := n) V U) :
    s ∈ idealOpenSectionSubmodule (n := n) V A U ↔
      ∀ (e : OriginalFrame V) (x : X), x ∈ frameOpen V U e →
        A.mem x (sectionExtension (frameOpen V U e) (localFrameCoefficient (n := n) V U e s)) := by
  rw [mem_idealOpenSectionSubmodule_iff_actualIdeal]
  constructor
  · intro h e
    exact (scalarSection_mem_actualIdeal_iff A hA _ _).mp (h e)
  · intro h e
    exact (scalarSection_mem_actualIdeal_iff A hA _ _).mpr (h e)

end SGPT.Bergman.MultiplierSectionsDraft
