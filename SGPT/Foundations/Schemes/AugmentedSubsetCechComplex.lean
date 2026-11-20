import SGPT.Foundations.Schemes.FiniteGradedPolynomialVanishing

/-! # The actual augmented finite-subset complex

This extends the accepted augmented complex, whose degree-p term is the
actual cardinal-p cochain module. Maps and short exactness include the
empty-subset component. The true cardinal-zero differential maps to the
actual nonaugmented cocycles; native augmented homology zero in degrees
zero and one proves this map bijective.
-/

universe u

open CategoryTheory CategoryTheory.Limits DirectSum

namespace SGPT.Foundations.Schemes

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

section ActualAugmentedFunctor

variable {K I : Type u} [CommRing K] [LinearOrder I]

/-- Actual natural maps act on every augmented cardinal term, including the empty one. -/
def augmentedSubsetCechComplexMap {F G : Finset I ⥤ ModuleCat.{u} K} (α : F ⟶ G) :
    augmentedSubsetCechComplex F ⟶ augmentedSubsetCechComplex G :=
  CochainComplex.ofHom
    (fun p => ModuleCat.ofHom (subsetCechCardMap α p)) (by
      intro p
      simp only [augmentedSubsetCechComplex, CochainComplex.of_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      apply Subtype.ext
      exact (subsetCechCubeMap_comm α c.val).symm)

/-- The actual augmented complex constructor is a genuine native functor on full diagrams. -/
def actualAugmentedSubsetCechFunctor :
    (Finset I ⥤ ModuleCat.{u} K) ⥤ CochainComplex (ModuleCat.{u} K) ℕ where
  obj F := augmentedSubsetCechComplex F
  map α := augmentedSubsetCechComplexMap α
  map_id F := by
    apply HomologicalComplex.Hom.ext
    funext p
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    funext S
    rfl
  map_comp α β := by
    apply HomologicalComplex.Hom.ext
    funext p
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    funext S
    rfl

/-- The genuine augmented functor preserves actual additions of natural diagram maps. -/
instance actualAugmentedSubsetCechFunctorAdditive :
    (actualAugmentedSubsetCechFunctor (K := K) (I := I)).Additive where
  map_add := by
    intro X Y α β
    apply HomologicalComplex.Hom.ext
    funext p
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    funext S
    rfl

variable (F : Finset I ⥤ ModuleCat.{u} K)

/-- The actual consecutive cardinal terms form a native short complex. -/
def augmentedSubsetCechCardShortComplex (n : ℕ) : ShortComplex (ModuleCat.{u} K) :=
  ShortComplex.moduleCatMk (subsetCechCardDifferential F n)
    (subsetCechCardDifferential F (n + 1)) (by
      apply LinearMap.ext
      intro c
      exact subsetCechCardDifferential_squared F n c)

/-- At a successor degree the actual augmented native short complex has literal cardinal terms. -/
theorem augmentedSubsetCechComplex_sc'_eq (n : ℕ) :
    (augmentedSubsetCechComplex F).sc' n (n + 1) (n + 2) =
      augmentedSubsetCechCardShortComplex F n := by
  simp [augmentedSubsetCechComplex, HomologicalComplex.sc',
    HomologicalComplex.shortComplexFunctor', augmentedSubsetCechCardShortComplex,
    ShortComplex.moduleCatMk, CochainComplex.of.d, Nat.add_assoc]

/-- The actual initial native short complex has zero incoming map and true augmentation outgoing map. -/
def augmentedSubsetCechZeroShortComplex : ShortComplex (ModuleCat.{u} K) :=
  ShortComplex.moduleCatMk
    (0 : subsetCechCardPiece F 0 →ₗ[K] subsetCechCardPiece F 0)
    (subsetCechCardDifferential F 0) (by simp)

/-- Native zero-degree homology keeps the actual cardinal-zero augmentation term. -/
theorem augmentedSubsetCechComplex_sc'_zero_eq :
    (augmentedSubsetCechComplex F).sc' 0 0 1 = augmentedSubsetCechZeroShortComplex F := by
  simp [augmentedSubsetCechComplex, HomologicalComplex.sc',
    HomologicalComplex.shortComplexFunctor', augmentedSubsetCechZeroShortComplex,
    ShortComplex.moduleCatMk, CochainComplex.of.d]

/-- The actual cardinal-zero term is linearly equivalent to the genuine empty diagram component. -/
def subsetCechCardZeroEquiv : subsetCechCardPiece F 0 ≃ₗ[K] F.obj ∅ where
  toFun c := c.val ∅
  invFun x := ⟨fun S => if h : S = ∅ then h.symm ▸ x else 0, by
    intro S hS
    have hne : S ≠ ∅ := by intro h; subst S; exact hS rfl
    simp only [dif_neg hne]⟩
  left_inv c := by
    apply Subtype.ext
    funext S
    by_cases hS : S = ∅
    · subst S
      simp
    · have hc : c.val S = 0 := c.property S (fun h => hS (Finset.card_eq_zero.mp h))
      simp only [dif_neg hS, hc]
  right_inv x := by simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The genuine augmentation maps into exactly the actual outgoing cardinal-one kernel. -/
def subsetCechAugmentationToCycles :
    subsetCechCardPiece F 0 →ₗ[K] LinearMap.ker (subsetCechCardDifferential F 1) :=
  (subsetCechCardDifferential F 0).codRestrict _ (subsetCechCardDifferential_squared F 0)

/-- Actual native augmented H0 and H1 zero give a bijective genuine augmentation to cocycles. -/
theorem subsetCechAugmentationToCycles_bijective_of_isZero
    (h0 : IsZero ((augmentedSubsetCechComplex F).homology 0))
    (h1 : IsZero ((augmentedSubsetCechComplex F).homology 1)) :
    Function.Bijective (subsetCechAugmentationToCycles F) := by
  have he0 := (HomologicalComplex.exactAt_iff' _ 0 0 1
    CochainComplex.prev_nat_zero (CochainComplex.next ℕ 0)).mp
      ((HomologicalComplex.exactAt_iff_isZero_homology _ 0).mpr h0)
  rw [augmentedSubsetCechComplex_sc'_zero_eq] at he0
  have hx0 := (ShortComplex.moduleCat_exact_iff _).mp he0
  have he1 := (HomologicalComplex.exactAt_iff' _ 0 1 2
    (CochainComplex.prev_nat_succ 0) (CochainComplex.next ℕ 1)).mp
      ((HomologicalComplex.exactAt_iff_isZero_homology _ 1).mpr h1)
  rw [augmentedSubsetCechComplex_sc'_eq] at he1
  have hx1 := (ShortComplex.moduleCat_exact_iff _).mp he1
  constructor
  · intro a b hab
    have hd : subsetCechCardDifferential F 0 a = subsetCechCardDifferential F 0 b :=
      congrArg Subtype.val hab
    have hz : subsetCechCardDifferential F 0 (a - b) = 0 := by rw [map_sub, hd, sub_self]
    obtain ⟨w, hw⟩ := hx0 (a - b) hz
    change (0 : subsetCechCardPiece F 0) = a - b at hw
    exact sub_eq_zero.mp hw.symm
  · intro c
    obtain ⟨b, hb⟩ := hx1 c.val c.property
    exact ⟨b, Subtype.ext hb⟩

end ActualAugmentedFunctor

section ActualAugmentedShortExact

variable {K I : Type u} [CommRing K] [LinearOrder I]
  {F G H : Finset I ⥤ ModuleCat.{u} K}

/-- Actual pointwise exact diagrams form a true short complex of full augmented complexes. -/
def actualAugmentedSubsetCechShortComplex (α : F ⟶ G) (β : G ⟶ H)
    (he : ∀ S, Function.Exact (α.app S) (β.app S)) :
    ShortComplex (CochainComplex (ModuleCat.{u} K) ℕ) :=
  ShortComplex.mk (augmentedSubsetCechComplexMap α) (augmentedSubsetCechComplexMap β) (by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    funext S
    change β.app S (α.app S (a.val S)) = 0
    exact (he S).apply_apply_eq_zero (a.val S))

/-- Genuine degreewise exactness, including the empty component, gives native augmented short exactness. -/
theorem actualAugmentedSubsetCechShortComplex_shortExact (α : F ⟶ G) (β : G ⟶ H)
    (he : ∀ S, Function.Exact (α.app S) (β.app S))
    (hi : ∀ S, Function.Injective (α.app S))
    (hs : ∀ S, Function.Surjective (β.app S)) :
    (actualAugmentedSubsetCechShortComplex α β he).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
    exact subsetCechCardMap_exact α β he n
  · apply (ModuleCat.mono_iff_injective _).mpr
    exact subsetCechCardMap_injective α hi n
  · apply (ModuleCat.epi_iff_surjective _).mpr
    exact subsetCechCardMap_surjective β hs n

end ActualAugmentedShortExact

section ActualAugmentedSupport

variable {K I : Type u} [CommRing K] [LinearOrder I] [Fintype I]
  (F : Finset I ⥤ ModuleCat.{u} K)

/-- The full actual augmented complex is exact strictly above the true coordinate cardinality. -/
theorem augmentedSubsetCechComplex_exactAt_of_card_lt (p : ℕ) (hp : Fintype.card I < p) :
    (augmentedSubsetCechComplex F).ExactAt p := by
  have : Subsingleton ((augmentedSubsetCechComplex F).X p) :=
    subsetCechCardPiece_subsingleton F p hp
  exact HomologicalComplex.ExactAt.of_isZero (ModuleCat.isZero_of_subsingleton _)

/-- The full actual native augmented cohomology vanishes strictly above the coordinate bound. -/
theorem augmentedSubsetCechComplex_homology_isZero_of_card_lt (p : ℕ)
    (hp : Fintype.card I < p) :
    IsZero ((augmentedSubsetCechComplex F).homology p) :=
  (augmentedSubsetCechComplex_exactAt_of_card_lt F p hp).isZero_homology

end ActualAugmentedSupport

section ActualHomogeneousAugmentation

variable {K R M N I : Type u} [CommRing K] [CommRing R] [Algebra K R]
  [AddCommGroup M] [AddCommGroup N] [LinearOrder I]
  [Module K M] [Module R M] [IsScalarTower K R M]
  [Module K N] [Module R N] [IsScalarTower K R N]
  (𝒜 : ℤ → Submodule K R) [GradedRing 𝒜]
  (ℳ : ℤ → Submodule K M) (𝒩 : ℤ → Submodule K N)
  [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝒩]
  [SetLike.GradedSMul 𝒜 ℳ] [SetLike.GradedSMul 𝒜 𝒩]
  (x : I → R) (hx : ∀ i, x i ∈ 𝒜 1)

omit [AddCommGroup N] [Module K N] [Module R N] [IsScalarTower K R N]
  [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝒩] [SetLike.GradedSMul 𝒜 𝒩] in
/-- The full native augmented homogeneous coordinate complex retains the true empty degree piece. -/
def homogeneousCoordinateAugmentedCechComplex (m : ℤ) :
    CochainComplex (ModuleCat.{u} K) ℕ :=
  augmentedSubsetCechComplex (homogeneousCoordinateSubsetDiagram 𝒜 ℳ x hx m)

/-- The true homogeneous kernel sequence forms a literal full augmented short complex. -/
def actualHomogeneousKernelAugmentedCechShortComplex (f : M →ₗ[R] N)
    (hf : ∀ d v, v ∈ ℳ d → f v ∈ 𝒩 d) (m : ℤ) :
    ShortComplex (CochainComplex (ModuleCat.{u} K) ℕ) := by
  let ℒ := homogeneousSubmodulePiece ℳ (LinearMap.ker f)
  let _ := actualHomogeneousKernelDecomposition ℳ 𝒩 f hf
  let hi := actualHomogeneousKernelInclusion_homogeneous ℳ f
  exact actualAugmentedSubsetCechShortComplex
    (homogeneousCoordinateSubsetDiagramMap 𝒜 ℒ x hx ℳ (LinearMap.ker f).subtype hi m)
    (homogeneousCoordinateSubsetDiagramMap 𝒜 ℳ x hx 𝒩 f hf m)
    (fun S => homogeneousCoordinateSubsetDiagramMap_exact 𝒜 ℒ x hx ℳ 𝒩
      (LinearMap.ker f).subtype f hi hf (LinearMap.exact_subtype_ker_map f) m S)

/-- Actual homogeneous surjectivity produces native augmented short exactness in every degree. -/
theorem actualHomogeneousKernelAugmentedCechShortComplex_shortExact (f : M →ₗ[R] N)
    (hf : ∀ d v, v ∈ ℳ d → f v ∈ 𝒩 d) (hs : Function.Surjective f) (m : ℤ) :
    (actualHomogeneousKernelAugmentedCechShortComplex 𝒜 ℳ 𝒩 x hx f hf m).ShortExact := by
  let ℒ := homogeneousSubmodulePiece ℳ (LinearMap.ker f)
  let _ := actualHomogeneousKernelDecomposition ℳ 𝒩 f hf
  let hi := actualHomogeneousKernelInclusion_homogeneous ℳ f
  apply actualAugmentedSubsetCechShortComplex_shortExact _ _
    (fun S => homogeneousCoordinateSubsetDiagramMap_exact 𝒜 ℒ x hx ℳ 𝒩
      (LinearMap.ker f).subtype f hi hf (LinearMap.exact_subtype_ker_map f) m S)
  · exact fun S => homogeneousCoordinateSubsetDiagramMap_injective 𝒜 ℒ ℳ x hx
      (LinearMap.ker f).subtype hi (LinearMap.ker f).subtype_injective m S
  · exact fun S => homogeneousCoordinateSubsetDiagramMap_surjective 𝒜 ℳ x hx 𝒩 f hf hs m S

end ActualHomogeneousAugmentation

end

end SGPT.Foundations.Schemes
