import SGPT.Foundations.Schemes.PolynomialCechPositiveTwistVanishing
import SGPT.Foundations.Schemes.HomogeneousCechDimensionShift

/-! # Uniform native positive cohomology vanishing for true finite graded modules

One fixed finite homogeneous cover and its actual internally graded kernel
give a native cohomology dimension shift. Induction on a bounded number of
genuine kernel covers combines their fixed thresholds before varying either
the homogeneous or cohomological degree. The actual finite coordinate-cover
length supplies the terminating cohomological bound; no terminating module
resolution or vanishing certificate is assumed.

The nonaugmented degree-zero cohomology and saturation comparison are separate.
-/

universe u

open CategoryTheory CategoryTheory.Limits DirectSum

namespace SGPT.Foundations.Schemes

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

section NativeDimensionShift

variable {K : Type u} [CommRing K]

/-- Actual native exactness and zero outer cohomology make the middle cohomology zero. -/
theorem nativeCochainHomology_isZero_dimensionShift
    (S : ShortComplex (CochainComplex (ModuleCat.{u} K) ℕ)) (hS : S.ShortExact) (p : ℕ)
    (hfree : IsZero (S.X₂.homology p)) (hker : IsZero (S.X₁.homology (p + 1))) :
    IsZero (S.X₃.homology p) := by
  have he := hS.homology_exact₃ p (p + 1) (by rfl)
  have he' := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp he
  let _ : Subsingleton (S.X₂.homology p) := ModuleCat.subsingleton_of_isZero hfree
  let _ : Subsingleton (S.X₁.homology (p + 1)) := ModuleCat.subsingleton_of_isZero hker
  have hz : ∀ z : S.X₃.homology p, z = 0 := by
    intro z
    obtain ⟨w, hw⟩ := (he' z).mp (Subsingleton.elim _ _)
    rw [Subsingleton.elim w 0, map_zero] at hw
    exact hw.symm
  let _ : Subsingleton (S.X₃.homology p) := ⟨fun a b => (hz a).trans (hz b).symm⟩
  exact ModuleCat.isZero_of_subsingleton _

end NativeDimensionShift

variable {K I : Type u} [Field K] [LinearOrder I] [Fintype I] [Nonempty I]

/-- A bounded number of true kernel covers gives one threshold independent of both degrees. -/
theorem finiteGradedPolynomialCoordinateCech_homology_eventually_isZero_dimensionInduction
    (t : ℕ) :
    ∀ (M : Type u) [AddCommGroup M] [Module K M] [Module (MvPolynomial I K) M]
      [IsScalarTower K (MvPolynomial I K) M]
      (ℳ : ℤ → Submodule K M) [DirectSum.Decomposition ℳ]
      [SetLike.GradedSMul (polynomialIntegralGrading (K := K) (I := I)) ℳ]
      [Module.Finite (MvPolynomial I K) M],
      ∃ b : ℤ, ∀ m : ℤ, b ≤ m → ∀ p : ℕ, 0 < p → Fintype.card I ≤ p + t →
        IsZero
          ((homogeneousCoordinateCechComplex (polynomialIntegralGrading (K := K) (I := I))
            ℳ (fun i => (MvPolynomial.X i : MvPolynomial I K))
              polynomialCoordinate_X_degree m).homology p) := by
  classical
  induction t with
  | zero =>
    intro M _ _ _ _ ℳ _ _ _
    exact ⟨0, fun m _ p _ hp =>
      subsetCechComplex_homology_isZero_of_card_le _ p (by simpa using hp)⟩
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
      finiteShiftedPolynomialCoordinateCech_homology_eventually_isZero (K := K) (I := I) δ
    refine ⟨max bker bfree, ?_⟩
    intro m hm p hp hbound
    have hmk : bker ≤ m := le_trans (le_max_left _ _) hm
    have hmf : bfree ≤ m := le_trans (le_max_right _ _) hm
    have hzker : IsZero
        ((homogeneousCoordinateCechComplex 𝒜 ℒ
          (fun i => (MvPolynomial.X i : MvPolynomial I K))
          polynomialCoordinate_X_degree m).homology (p + 1)) :=
      hker m hmk (p + 1) (by omega) (by omega)
    obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
    have hzfree : IsZero
        ((homogeneousCoordinateCechComplex 𝒜 ℱ
          (fun i => (MvPolynomial.X i : MvPolynomial I K))
          polynomialCoordinate_X_degree m).homology (n + 1)) :=
      hfree m hmf n
    let C := actualHomogeneousKernelCechShortComplex 𝒜 ℱ ℳ
      (fun i => (MvPolynomial.X i : MvPolynomial I K)) polynomialCoordinate_X_degree f hf m
    exact nativeCochainHomology_isZero_dimensionShift C
      (actualHomogeneousKernelCechShortComplex_shortExact 𝒜 ℱ ℳ
        (fun i => (MvPolynomial.X i : MvPolynomial I K))
        polynomialCoordinate_X_degree f hf hs m) (n + 1) hzfree hzker

variable {M : Type u} [AddCommGroup M] [Module K M] [Module (MvPolynomial I K) M]
  [IsScalarTower K (MvPolynomial I K) M]
  (ℳ : ℤ → Submodule K M) [DirectSum.Decomposition ℳ]
  [SetLike.GradedSMul (polynomialIntegralGrading (K := K) (I := I)) ℳ]
  [Module.Finite (MvPolynomial I K) M]

/-- Every actual finite graded polynomial module has uniformly zero native positive cohomology. -/
theorem finiteGradedPolynomialCoordinateCech_homology_eventually_isZero :
    ∃ b : ℤ, ∀ m : ℤ, b ≤ m → ∀ n : ℕ,
      IsZero
        ((homogeneousCoordinateCechComplex (polynomialIntegralGrading (K := K) (I := I))
          ℳ (fun i => (MvPolynomial.X i : MvPolynomial I K))
          polynomialCoordinate_X_degree m).homology (n + 1)) := by
  obtain ⟨b, hb⟩ :=
    finiteGradedPolynomialCoordinateCech_homology_eventually_isZero_dimensionInduction
      (K := K) (I := I) (Fintype.card I) M ℳ
  exact ⟨b, fun m hm n => hb m hm (n + 1) (by omega) (by omega)⟩

end

end SGPT.Foundations.Schemes
