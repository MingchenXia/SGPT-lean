import SGPT.Foundations.Schemes.AugmentedSubsetCechComplex

/-! # Uniform actual augmented vanishing and true homogeneous saturation

The full polynomial/Laurent and shifted-free diagram isomorphisms include
the empty component. Their actual augmented complexes are transported by
the true augmented functor. Bounded real homogeneous-kernel covers give
uniform augmented vanishing, including H0 and H1. The true degree piece
maps bijectively to the empty localization at one without a torsion-free
assumption, and hence eventually to the actual nonaugmented cocycles.
-/

universe u

open CategoryTheory CategoryTheory.Limits DirectSum

namespace SGPT.Foundations.Schemes

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

section ActualFreeAugmentedVanishing

variable {K I : Type u} [Field K] [LinearOrder I] [Fintype I] [Nonempty I]

/-- The true Laurent augmentation and all true cardinal sequences are exact in nonnegative degree. -/
theorem polynomialLaurentAugmentedCech_exactAt_of_nonneg
    (m : ℤ) (hm : 0 ≤ m) (p : ℕ) :
    (augmentedSubsetCechComplex
      (polynomialLaurentCechDiagram (K := K) (I := I) m)).ExactAt p := by
  cases p with
  | zero =>
    apply (HomologicalComplex.exactAt_iff' _ 0 0 1
      CochainComplex.prev_nat_zero (CochainComplex.next ℕ 0)).mpr
    rw [augmentedSubsetCechComplex_sc'_zero_eq]
    apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro c hc
    have hz : c = 0 := by
      apply polynomialLaurentCechCardDifferential_zero_injective_of_nonneg m hm
      rw [map_zero]
      exact hc
    exact ⟨0, hz.symm⟩
  | succ n =>
    apply (HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2)
      (CochainComplex.prev_nat_succ n) (CochainComplex.next ℕ (n + 1))).mpr
    rw [augmentedSubsetCechComplex_sc'_eq]
    exact polynomialLaurentCechCardShortComplex_exact_of_nonneg (K := K) (I := I) m hm n

/-- Every actual Laurent augmented native homology object is zero in nonnegative degree. -/
theorem polynomialLaurentAugmentedCech_homology_isZero_of_nonneg
    (m : ℤ) (hm : 0 ≤ m) (p : ℕ) :
    IsZero ((augmentedSubsetCechComplex
      (polynomialLaurentCechDiagram (K := K) (I := I) m)).homology p) :=
  (polynomialLaurentAugmentedCech_exactAt_of_nonneg (K := K) (I := I) m hm p).isZero_homology

/-- The full true polynomial/Laurent diagram isomorphism transports the actual empty component too. -/
def polynomialCoordinateAugmentedCechLaurentIso (m : ℤ) :
    augmentedSubsetCechComplex
      (polynomialCoordinateHomogeneousDiagram (K := K) (I := I) m) ≅
      augmentedSubsetCechComplex (polynomialLaurentCechDiagram (K := K) (I := I) m) :=
  (actualAugmentedSubsetCechFunctor (K := K) (I := I)).mapIso
    (polynomialCoordinateHomogeneousDiagramLaurentIso m)

/-- Genuine homogeneous polynomial augmented homology is zero in every degree, including zero and one. -/
theorem polynomialCoordinateAugmentedCech_homology_isZero_of_nonneg
    (m : ℤ) (hm : 0 ≤ m) (p : ℕ) :
    IsZero ((augmentedSubsetCechComplex
      (polynomialCoordinateHomogeneousDiagram (K := K) (I := I) m)).homology p) :=
  (polynomialLaurentAugmentedCech_homology_isZero_of_nonneg (K := K) (I := I) m hm p).of_iso
    (HomologicalComplex.homologyMapIso (polynomialCoordinateAugmentedCechLaurentIso m) p)

omit [Fintype I] [Nonempty I] in
/-- The true finite product augmented homology is the literal product of all factor homologies. -/
def actualAugmentedFiniteProductCechHomologyPiIso {A : Type u} [Fintype A]
    (F : A → Finset I ⥤ ModuleCat.{u} K) (p : ℕ) :
    (augmentedSubsetCechComplex (actualModuleSubsetDiagramPi F)).homology p ≅
      ModuleCat.of K (∀ a, (augmentedSubsetCechComplex (F a)).homology p) := by
  let G := actualAugmentedSubsetCechFunctor (K := K) (I := I)
  let b := G.mapBicone (actualModuleSubsetDiagramPiBicone F)
  let hb := actualAdditiveFiniteBiconeMapIsBilimit G
    (actualModuleSubsetDiagramPiBicone F) (actualModuleSubsetDiagramPiIsBilimit F)
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} K) (ComplexShape.up ℕ) p
  let hbh := actualAdditiveFiniteBiconeMapIsBilimit H b hb
  exact IsLimit.conePointUniqueUpToIso hbh.isLimit
    (ModuleCat.HasLimit.productLimitCone
      (fun a => (augmentedSubsetCechComplex (F a)).homology p)).isLimit

variable {A : Type u} [Fintype A] [DecidableEq A] (δ : A → ℤ)

/-- The genuine shifted-free full diagram comparison produces an actual augmented product isomorphism. -/
def finiteShiftedPolynomialAugmentedCechProductIso (m : ℤ) :
    homogeneousCoordinateAugmentedCechComplex (polynomialIntegralGrading (K := K) (I := I))
      (finiteShiftedFreePiece (polynomialIntegralGrading (K := K) (I := I)) δ)
      (fun i => (MvPolynomial.X i : MvPolynomial I K)) polynomialCoordinate_X_degree m ≅
      augmentedSubsetCechComplex (actualModuleSubsetDiagramPi
        (fun a => polynomialCoordinateHomogeneousDiagram (K := K) (I := I) (m - δ a))) :=
  (actualAugmentedSubsetCechFunctor (K := K) (I := I)).mapIso
    (finiteShiftedCoordinateSubsetDiagramIso (polynomialIntegralGrading (K := K) (I := I))
      δ (fun i => (MvPolynomial.X i : MvPolynomial I K)) polynomialCoordinate_X_degree m)

/-- Actual finite shifted free augmented cohomology is zero above all actual generator shifts. -/
theorem finiteShiftedPolynomialAugmentedCech_homology_isZero_of_shift_le
    (m : ℤ) (hm : ∀ a, δ a ≤ m) (p : ℕ) :
    IsZero
      ((homogeneousCoordinateAugmentedCechComplex (polynomialIntegralGrading (K := K) (I := I))
        (finiteShiftedFreePiece (polynomialIntegralGrading (K := K) (I := I)) δ)
        (fun i => (MvPolynomial.X i : MvPolynomial I K)) polynomialCoordinate_X_degree m).homology p) := by
  let F := fun a => polynomialCoordinateHomogeneousDiagram (K := K) (I := I) (m - δ a)
  let _ : ∀ a, Subsingleton ((augmentedSubsetCechComplex (F a)).homology p) :=
    fun a => ModuleCat.subsingleton_of_isZero
      (polynomialCoordinateAugmentedCech_homology_isZero_of_nonneg
        (K := K) (I := I) (m - δ a) (sub_nonneg.mpr (hm a)) p)
  have hz : IsZero (ModuleCat.of K (∀ a, (augmentedSubsetCechComplex (F a)).homology p)) :=
    ModuleCat.isZero_of_subsingleton _
  exact (hz.of_iso (actualAugmentedFiniteProductCechHomologyPiIso F p)).of_iso
    (HomologicalComplex.homologyMapIso
      (finiteShiftedPolynomialAugmentedCechProductIso (K := K) (I := I) δ m) p)

/-- A single true free-module bound works for every augmented cohomological degree and later twist. -/
theorem finiteShiftedPolynomialAugmentedCech_homology_eventually_isZero :
    ∃ b : ℤ, ∀ m : ℤ, b ≤ m → ∀ p : ℕ,
      IsZero
        ((homogeneousCoordinateAugmentedCechComplex (polynomialIntegralGrading (K := K) (I := I))
          (finiteShiftedFreePiece (polynomialIntegralGrading (K := K) (I := I)) δ)
          (fun i => (MvPolynomial.X i : MvPolynomial I K)) polynomialCoordinate_X_degree m).homology p) := by
  classical
  let b : ℤ := Finset.univ.sup' (by simp : (Finset.univ : Finset (Option A)).Nonempty)
    (fun a => a.elim 0 δ)
  refine ⟨b, fun m hm p =>
    finiteShiftedPolynomialAugmentedCech_homology_isZero_of_shift_le δ m ?_ p⟩
  intro a
  exact le_trans (Finset.le_sup' (f := fun a : Option A => a.elim 0 δ)
    (Finset.mem_univ (some a))) hm

end ActualFreeAugmentedVanishing

section ActualFiniteAugmentedVanishing

variable {K I : Type u} [Field K] [LinearOrder I] [Fintype I] [Nonempty I]

/-- Bounded genuine kernel covers give uniform zero augmented cohomology within the actual support bound. -/
theorem finiteGradedPolynomialAugmentedCech_homology_eventually_isZero_dimensionInduction
    (t : ℕ) :
    ∀ (M : Type u) [AddCommGroup M] [Module K M] [Module (MvPolynomial I K) M]
      [IsScalarTower K (MvPolynomial I K) M]
      (ℳ : ℤ → Submodule K M) [DirectSum.Decomposition ℳ]
      [SetLike.GradedSMul (polynomialIntegralGrading (K := K) (I := I)) ℳ]
      [Module.Finite (MvPolynomial I K) M],
      ∃ b : ℤ, ∀ m : ℤ, b ≤ m → ∀ p : ℕ, Fintype.card I + 1 ≤ p + t →
        IsZero
          ((homogeneousCoordinateAugmentedCechComplex (polynomialIntegralGrading (K := K) (I := I))
            ℳ (fun i => (MvPolynomial.X i : MvPolynomial I K))
              polynomialCoordinate_X_degree m).homology p) := by
  classical
  induction t with
  | zero =>
    intro M _ _ _ _ ℳ _ _ _
    exact ⟨0, fun m _ p hp =>
      augmentedSubsetCechComplex_homology_isZero_of_card_lt _ p (by omega)⟩
  | succ t ih =>
    intro M _ _ _ _ ℳ _ _ _
    let 𝒜 := polynomialIntegralGrading (K := K) (I := I)
    obtain ⟨s, δ, hg, hs, _⟩ := finiteShiftedGradedPresentation_exists 𝒜 ℳ
    let ℱ := finiteShiftedFreePiece 𝒜 δ
    let f := finiteHomogeneousPresentationMap (R := MvPolynomial I K)
      (fun i : s => (i : M))
    let hf := finiteHomogeneousPresentationMap_homogeneous 𝒜 ℳ δ _ hg
    let _ : DirectSum.Decomposition ℱ := finiteShiftedFreeDecomposition 𝒜 δ
    let _ : SetLike.GradedSMul 𝒜 ℱ := finiteShiftedFreeGradedSMul 𝒜 δ
    let ℒ := homogeneousSubmodulePiece ℱ (LinearMap.ker f)
    let _ : DirectSum.Decomposition ℒ := actualHomogeneousKernelDecomposition ℱ ℳ f hf
    obtain ⟨bker, hker⟩ := ih (LinearMap.ker f) ℒ
    obtain ⟨bfree, hfree⟩ :=
      finiteShiftedPolynomialAugmentedCech_homology_eventually_isZero (K := K) (I := I) δ
    refine ⟨max bker bfree, ?_⟩
    intro m hm p hbound
    have hmk : bker ≤ m := le_trans (le_max_left _ _) hm
    have hmf : bfree ≤ m := le_trans (le_max_right _ _) hm
    have hzker : IsZero
        ((homogeneousCoordinateAugmentedCechComplex 𝒜 ℒ
          (fun i => (MvPolynomial.X i : MvPolynomial I K))
          polynomialCoordinate_X_degree m).homology (p + 1)) :=
      hker m hmk (p + 1) (by omega)
    have hzfree : IsZero
        ((homogeneousCoordinateAugmentedCechComplex 𝒜 ℱ
          (fun i => (MvPolynomial.X i : MvPolynomial I K))
          polynomialCoordinate_X_degree m).homology p) :=
      hfree m hmf p
    let C := actualHomogeneousKernelAugmentedCechShortComplex 𝒜 ℱ ℳ
      (fun i => (MvPolynomial.X i : MvPolynomial I K)) polynomialCoordinate_X_degree f hf m
    exact nativeCochainHomology_isZero_dimensionShift C
      (actualHomogeneousKernelAugmentedCechShortComplex_shortExact 𝒜 ℱ ℳ
        (fun i => (MvPolynomial.X i : MvPolynomial I K))
        polynomialCoordinate_X_degree f hf hs m) p hzfree hzker

variable {M : Type u} [AddCommGroup M] [Module K M] [Module (MvPolynomial I K) M]
  [IsScalarTower K (MvPolynomial I K) M]
  (ℳ : ℤ → Submodule K M) [DirectSum.Decomposition ℳ]
  [SetLike.GradedSMul (polynomialIntegralGrading (K := K) (I := I)) ℳ]
  [Module.Finite (MvPolynomial I K) M]

/-- Every true finite graded polynomial module has one uniform bound killing every augmented obstruction. -/
theorem finiteGradedPolynomialAugmentedCech_homology_eventually_isZero :
    ∃ b : ℤ, ∀ m : ℤ, b ≤ m → ∀ p : ℕ,
      IsZero
        ((homogeneousCoordinateAugmentedCechComplex (polynomialIntegralGrading (K := K) (I := I))
          ℳ (fun i => (MvPolynomial.X i : MvPolynomial I K))
          polynomialCoordinate_X_degree m).homology p) := by
  obtain ⟨b, hb⟩ :=
    finiteGradedPolynomialAugmentedCech_homology_eventually_isZero_dimensionInduction
      (K := K) (I := I) (Fintype.card I + 1) M ℳ
  exact ⟨b, fun m hm p => hb m hm p (by omega)⟩

end ActualFiniteAugmentedVanishing

section TrueHomogeneousEmptyPiece

variable {K R M I : Type u} [CommRing K] [CommRing R] [Algebra K R]
  [AddCommGroup M] [Module K M] [Module R M] [IsScalarTower K R M] [LinearOrder I]
  (𝒜 : ℤ → Submodule K R) [GradedRing 𝒜]
  (ℳ : ℤ → Submodule K M) [SetLike.GradedSMul 𝒜 ℳ]
  (x : I → R) (hx : ∀ i, x i ∈ 𝒜 1)

/-- A true homogeneous vector gives its genuine fraction v/1 in the actual empty subset component. -/
def homogeneousCoordinateEmptyPieceMap (m : ℤ) :
    ℳ m →ₗ[K] (homogeneousCoordinateSubsetDiagram 𝒜 ℳ x hx m).obj ∅ := by
  let f := ((LocalizedModule.mkLinearMap
    (Submonoid.powers (homogeneousCoordinateSubsetProduct x ∅)) M).restrictScalars K).comp
      (ℳ m).subtype
  exact f.codRestrict _ (by
    intro v
    refine ⟨0, v.val, by simpa only [Nat.cast_zero, zero_mul, add_zero] using v.property, ?_⟩
    change LocalizedModule.mk v.val
      (homogeneousPowerDenominator (homogeneousCoordinateSubsetProduct x ∅) 0) =
        LocalizedModule.mkLinearMap (Submonoid.powers (homogeneousCoordinateSubsetProduct x ∅)) M v.val
    rw [LocalizedModule.mkLinearMap_apply]
    congr 1
    apply Subtype.ext
    simp [homogeneousPowerDenominator])

/-- Every empty denominator is a power of one, so the actual degree-piece map is bijective even with torsion. -/
theorem homogeneousCoordinateEmptyPieceMap_bijective (m : ℤ) :
    Function.Bijective (homogeneousCoordinateEmptyPieceMap 𝒜 ℳ x hx m) := by
  constructor
  · intro a b hab
    have he : LocalizedModule.mk a.val
        (1 : Submonoid.powers (homogeneousCoordinateSubsetProduct x ∅)) =
        LocalizedModule.mk b.val 1 := congrArg Subtype.val hab
    obtain ⟨s, hs⟩ := LocalizedModule.mk_eq.mp he
    have hs1 : (s : R) = 1 := by
      obtain ⟨q, hq⟩ := s.property
      simpa [homogeneousCoordinateSubsetProduct] using hq.symm
    apply Subtype.ext
    simpa [Submonoid.smul_def, hs1] using hs
  · intro z
    obtain ⟨q, v, hv, hz⟩ := z.property
    refine ⟨⟨v, by simpa using hv⟩, ?_⟩
    apply Subtype.ext
    change LocalizedModule.mk v
      (1 : Submonoid.powers (homogeneousCoordinateSubsetProduct x ∅)) = z.val
    rw [← hz]
    congr 1
    apply Subtype.ext
    simp [homogeneousPowerDenominator, homogeneousCoordinateSubsetProduct]

/-- The genuine degree piece maps to the actual cardinal-zero term by its v/1 empty value. -/
def homogeneousCoordinateDegreeToCardZero (m : ℤ) :
    ℳ m →ₗ[K] subsetCechCardPiece (homogeneousCoordinateSubsetDiagram 𝒜 ℳ x hx m) 0 :=
  (subsetCechCardZeroEquiv (homogeneousCoordinateSubsetDiagram 𝒜 ℳ x hx m)).symm.toLinearMap.comp
    (homogeneousCoordinateEmptyPieceMap 𝒜 ℳ x hx m)

/-- The actual degree/cardinal-zero identification is bijective for every true integral degree. -/
theorem homogeneousCoordinateDegreeToCardZero_bijective (m : ℤ) :
    Function.Bijective (homogeneousCoordinateDegreeToCardZero 𝒜 ℳ x hx m) :=
  (subsetCechCardZeroEquiv (homogeneousCoordinateSubsetDiagram 𝒜 ℳ x hx m)).symm.bijective.comp
    (homogeneousCoordinateEmptyPieceMap_bijective 𝒜 ℳ x hx m)

/-- The actual homogeneous degree maps to genuine coordinate cocycles through its true augmentation. -/
def homogeneousCoordinateDegreeToCocycles (m : ℤ) :
    ℳ m →ₗ[K] LinearMap.ker
      (subsetCechCardDifferential (homogeneousCoordinateSubsetDiagram 𝒜 ℳ x hx m) 1) :=
  (subsetCechAugmentationToCycles (homogeneousCoordinateSubsetDiagram 𝒜 ℳ x hx m)).comp
    (homogeneousCoordinateDegreeToCardZero 𝒜 ℳ x hx m)

end TrueHomogeneousEmptyPiece

section TrueFiniteHomogeneousSaturation

variable {K I M : Type u} [Field K] [LinearOrder I] [Fintype I] [Nonempty I]
  [AddCommGroup M] [Module K M] [Module (MvPolynomial I K) M]
  [IsScalarTower K (MvPolynomial I K) M]
  (ℳ : ℤ → Submodule K M) [DirectSum.Decomposition ℳ]
  [SetLike.GradedSMul (polynomialIntegralGrading (K := K) (I := I)) ℳ]
  [Module.Finite (MvPolynomial I K) M]

/-- The true homogeneous degree maps bijectively to the actual nonaugmented cocycles at one eventual bound. -/
theorem finiteGradedPolynomialCoordinateDegreeToCocycles_eventually_bijective :
    ∃ b : ℤ, ∀ m : ℤ, b ≤ m → Function.Bijective
      (homogeneousCoordinateDegreeToCocycles (polynomialIntegralGrading (K := K) (I := I))
        ℳ (fun i => (MvPolynomial.X i : MvPolynomial I K)) polynomialCoordinate_X_degree m) := by
  obtain ⟨b, hb⟩ := finiteGradedPolynomialAugmentedCech_homology_eventually_isZero (K := K) (I := I) ℳ
  refine ⟨b, fun m hm => ?_⟩
  exact (subsetCechAugmentationToCycles_bijective_of_isZero
    (homogeneousCoordinateSubsetDiagram (polynomialIntegralGrading (K := K) (I := I))
      ℳ (fun i => (MvPolynomial.X i : MvPolynomial I K)) polynomialCoordinate_X_degree m)
    (hb m hm 0) (hb m hm 1)).comp
      (homogeneousCoordinateDegreeToCardZero_bijective
        (polynomialIntegralGrading (K := K) (I := I)) ℳ
        (fun i => (MvPolynomial.X i : MvPolynomial I K)) polynomialCoordinate_X_degree m)

end TrueFiniteHomogeneousSaturation

end

end SGPT.Foundations.Schemes
