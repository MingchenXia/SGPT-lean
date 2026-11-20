import SGPT.Foundations.Schemes.PolynomialTwistedCoordinateScalars
import SGPT.Foundations.Schemes.HomogeneousSubsetLocalization
import SGPT.Foundations.Schemes.PolynomialProjectiveSubsetCharts
import Mathlib.Algebra.Module.LocalizedModule.Away

/-! # Actual homogeneous module localization on coordinate intersections

For i in a genuine nonempty subset S, the native degree-zero product-localized
module is the actual localization of the Xi chart module at the true product
of coordinate ratios. The constructions use literal native fractions and
retain localization torsion throughout.
-/

open CategoryTheory Opposite AlgebraicGeometry

namespace SGPT.Foundations.Schemes

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

variable (K : Type) [Field K] (n : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The literal product of coordinates inverted on an actual finite intersection. -/
abbrev polynomialHomogeneousSubsetProduct (S : Finset (Fin (n + 1))) :=
  homogeneousCoordinateSubsetProduct (fun j => (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) K)) S

/-- The same true coordinate product has its native nonnegative homogeneous cardinal degree. -/
theorem polynomialHomogeneousSubsetProduct_degree (S : Finset (Fin (n + 1))) :
    polynomialHomogeneousSubsetProduct K n S ∈
      MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K S.card := by
  simpa only [homogeneousCoordinateSubsetProduct, Finset.sum_const, nsmul_eq_mul, mul_one, Nat.cast_id] using
    SetLike.prod_mem_graded (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
      (fun _ : Fin (n + 1) => (1 : ℕ)) (fun j => (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) K))
      (F := S) (fun j _ => MvPolynomial.isHomogeneous_X K j)

/-- Membership of a coordinate gives the genuine complementary factor of the inverted subset product. -/
theorem polynomialHomogeneousSubsetProduct_factor (i : Fin (n + 1)) (S : Finset (Fin (n + 1)))
    (hi : i ∈ S) :
    polynomialHomogeneousSubsetProduct K n S =
      MvPolynomial.X i * polynomialHomogeneousSubsetProduct K n (S.erase i) := by
  simpa only [homogeneousCoordinateSubsetProduct, Finset.prod_singleton,
    Finset.sdiff_singleton_eq_erase] using
    homogeneousCoordinateSubsetProduct_factor
      (fun j => (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) K))
      (Finset.singleton_subset_iff.mpr hi)

/-- The true selected-coordinate map into the actual product chart ring. -/
def polynomialHomogeneousSubsetChartRingMap (i : Fin (n + 1))
    (S : Finset (Fin (n + 1))) (hi : i ∈ S) :
    polynomialProjCoordinateRing K n i →+*
      HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
        (polynomialHomogeneousSubsetProduct K n S) :=
  HomogeneousLocalization.awayMap _
    (polynomialHomogeneousSubsetProduct_degree K n (S.erase i))
    (polynomialHomogeneousSubsetProduct_factor K n i S hi)

/-- The literal true ratio product is a native fraction with the actual product numerator. -/
theorem polynomialProjSubsetRatioProduct_val (i : Fin (n + 1))
    (S : Finset (Fin (n + 1))) :
    (polynomialProjSubsetRatioProduct K n i S).val =
      Localization.mk (polynomialHomogeneousSubsetProduct K n S)
        (homogeneousPowerDenominator (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) K) S.card) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp [polynomialProjSubsetRatioProduct, polynomialHomogeneousSubsetProduct,
      homogeneousCoordinateSubsetProduct, homogeneousPowerDenominator]
  | @insert j S hj hS =>
    simp only [polynomialProjSubsetRatioProduct, Finset.prod_insert hj,
      HomogeneousLocalization.val_mul, polynomialProjCoordinateRatio,
      HomogeneousLocalization.Away.val_mk, pow_one] at *
    rw [hS, Localization.mk_mul]
    congr 1
    · simp [polynomialHomogeneousSubsetProduct, homogeneousCoordinateSubsetProduct, hj]
    · apply Subtype.ext
      simp [homogeneousPowerDenominator, Finset.card_insert_of_notMem hj, pow_succ, mul_comm]

/-- The true ratio product is its literal native homogeneous product fraction. -/
theorem polynomialProjSubsetRatioProduct_eq_mk (i : Fin (n + 1))
    (S : Finset (Fin (n + 1))) :
    polynomialProjSubsetRatioProduct K n i S =
      HomogeneousLocalization.Away.mk _ (MvPolynomial.isHomogeneous_X K i) S.card
        (polynomialHomogeneousSubsetProduct K n S)
        (by simpa using polynomialHomogeneousSubsetProduct_degree K n S) := by
  apply HomogeneousLocalization.val_injective
  rw [polynomialProjSubsetRatioProduct_val, HomogeneousLocalization.Away.val_mk]
  rfl

/-- The actual principal ratio product is exactly the native localization element for the selected product chart. -/
theorem polynomialProjSubsetRatioProduct_eq_localizationElem (i : Fin (n + 1))
    (S : Finset (Fin (n + 1))) (hi : i ∈ S) :
    polynomialProjSubsetRatioProduct K n i S =
      HomogeneousLocalization.Away.isLocalizationElem (MvPolynomial.isHomogeneous_X K i)
        (polynomialHomogeneousSubsetProduct_degree K n (S.erase i)) := by
  apply HomogeneousLocalization.val_injective
  rw [polynomialProjSubsetRatioProduct_val]
  simp only [HomogeneousLocalization.Away.isLocalizationElem,
    HomogeneousLocalization.Away.val_mk, pow_one]
  have hcard : S.card = (S.erase i).card + 1 := by
    rw [Finset.card_erase_of_mem hi]
    have := Finset.card_pos.mpr ⟨i, hi⟩
    omega
  rw [polynomialHomogeneousSubsetProduct_factor K n i S hi, hcard]
  apply Localization.mk_eq_mk_iff.mpr
  apply Localization.r_iff_exists.mpr
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, homogeneousPowerDenominator,
    Subtype.coe_mk, pow_succ]
  ring

/-- The actual product chart ring is the actual localization at the true ratio product. -/
theorem polynomialHomogeneousSubsetChartRing_isLocalization (i : Fin (n + 1))
    (S : Finset (Fin (n + 1))) (hi : i ∈ S) :
    letI := (polynomialHomogeneousSubsetChartRingMap K n i S hi).toAlgebra
    IsLocalization.Away (polynomialProjSubsetRatioProduct K n i S)
      (HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
        (polynomialHomogeneousSubsetProduct K n S)) := by
  rw [polynomialProjSubsetRatioProduct_eq_localizationElem K n i S hi]
  exact HomogeneousLocalization.Away.isLocalization_mul
    (MvPolynomial.isHomogeneous_X K i)
    (polynomialHomogeneousSubsetProduct_degree K n (S.erase i))
    (polynomialHomogeneousSubsetProduct_factor K n i S hi) (by decide)

variable {V : Type} [AddCommGroup V] [Module K V]
  [Module (MvPolynomial (Fin (n + 1)) K) V]
  [IsScalarTower K (MvPolynomial (Fin (n + 1)) K) V]
  (ℳ : ℤ → Submodule K V)
  [SetLike.GradedSMul (polynomialIntegralGrading (K := K) (I := Fin (n + 1))) ℳ]

/-- The literal native integral degree piece on the actual product-coordinate localization. -/
abbrev polynomialHomogeneousSubsetPiece (S : Finset (Fin (n + 1))) (k : ℤ) :=
  localizedHomogeneousModulePiece
    (polynomialIntegralGrading (K := K) (I := Fin (n + 1))) ℳ
    (polynomialHomogeneousSubsetProduct K n S) (S.card : ℤ)
    (homogeneousCoordinateSubsetProduct_degree _ _ polynomialCoordinate_X_degree S) k

/-- Actual product-chart ring scalars act on the actual ordinary localized module by their literal native values. -/
instance polynomialHomogeneousSubsetAmbientModule (S : Finset (Fin (n + 1))) :
    Module (HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
      (polynomialHomogeneousSubsetProduct K n S))
      (LocalizedModule (Submonoid.powers (polynomialHomogeneousSubsetProduct K n S)) V) :=
  Module.compHom _ (algebraMap
    (HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
      (polynomialHomogeneousSubsetProduct K n S))
    (Localization.Away (polynomialHomogeneousSubsetProduct K n S)))

/-- Genuine homogeneous degree-zero chart scalars preserve every literal integral localized degree. -/
theorem polynomialHomogeneousSubset_smul_mem (S : Finset (Fin (n + 1))) (k : ℤ)
    (r : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
      (polynomialHomogeneousSubsetProduct K n S))
    (z : LocalizedModule (Submonoid.powers (polynomialHomogeneousSubsetProduct K n S)) V)
    (hz : z ∈ polynomialHomogeneousSubsetPiece K n ℳ S k) :
    r • z ∈ polynomialHomogeneousSubsetPiece K n ℳ S k := by
  obtain ⟨a, p, hp, rfl⟩ := HomogeneousLocalization.Away.mk_surjective _
    (polynomialHomogeneousSubsetProduct_degree K n S) r
  obtain ⟨b, v, hv, rfl⟩ := hz
  refine ⟨a + b, p • v, ?_, ?_⟩
  · have hp' := polynomialHomogeneous_mem_integral K n (a * S.card) p (by simpa using hp)
    convert SetLike.GradedSMul.smul_mem hp' hv using 1
    congr 1
    simp only [vadd_eq_add, Nat.cast_add, Nat.cast_mul]
    ring
  · change LocalizedModule.mk (p • v)
      (homogeneousPowerDenominator (polynomialHomogeneousSubsetProduct K n S) (a + b)) =
      (HomogeneousLocalization.Away.mk (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
        (polynomialHomogeneousSubsetProduct_degree K n S) a p hp).val •
        LocalizedModule.mk v (homogeneousPowerDenominator (polynomialHomogeneousSubsetProduct K n S) b)
    rw [HomogeneousLocalization.Away.val_mk, LocalizedModule.mk_smul_mk]
    congr 1
    exact homogeneousPowerDenominator_add _ _ _

/-- The native product-chart scalar action restricts literally to the true homogeneous module piece. -/
instance polynomialHomogeneousSubsetPieceSMul (S : Finset (Fin (n + 1))) (k : ℤ) :
    SMul (HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
      (polynomialHomogeneousSubsetProduct K n S)) (polynomialHomogeneousSubsetPiece K n ℳ S k) where
  smul r z := ⟨r • z.val, polynomialHomogeneousSubset_smul_mem K n ℳ S k r z.val z.property⟩

/-- Genuine native product-chart module laws hold on the actual integral localized pieces. -/
instance polynomialHomogeneousSubsetPieceModule (S : Finset (Fin (n + 1))) (k : ℤ) :
    Module (HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
      (polynomialHomogeneousSubsetProduct K n S)) (polynomialHomogeneousSubsetPiece K n ℳ S k) :=
  Subtype.coe_injective.module _ (polynomialHomogeneousSubsetPiece K n ℳ S k).subtype.toAddMonoidHom
    (fun _ _ => rfl)

/-- Native selected-chart scalars act through the true selected-chart ring restriction. -/
abbrev polynomialHomogeneousSubsetChartModule (i : Fin (n + 1))
    (S : Finset (Fin (n + 1))) (hi : i ∈ S) (k : ℤ) :
    Module (polynomialProjCoordinateRing K n i) (polynomialHomogeneousSubsetPiece K n ℳ S k) :=
  Module.compHom _ (polynomialHomogeneousSubsetChartRingMap K n i S hi)

/-- The genuine degree-preserving module restriction from a selected chart to the true intersection. -/
def polynomialHomogeneousSubsetChartRestrictionK (i : Fin (n + 1))
    (S : Finset (Fin (n + 1))) (hi : i ∈ S) (k : ℤ) :
    localizedHomogeneousModulePiece polynomialIntegralGrading ℳ
      (MvPolynomial.X i) 1 (polynomialCoordinate_X_degree i) k →ₗ[K]
        polynomialHomogeneousSubsetPiece K n ℳ S k :=
  (((actualLocalizedModuleDivisorRestriction (M := V) (MvPolynomial.X i)
    (polynomialHomogeneousSubsetProduct K n S)
    ⟨polynomialHomogeneousSubsetProduct K n (S.erase i),
      polynomialHomogeneousSubsetProduct_factor K n i S hi⟩).restrictScalars K).comp
    (localizedHomogeneousModulePiece polynomialIntegralGrading ℳ
      (MvPolynomial.X i) 1 (polynomialCoordinate_X_degree i) k).subtype).codRestrict _ (by
    intro z
    obtain ⟨a, v, hv, he⟩ := z.property
    refine ⟨a, polynomialHomogeneousSubsetProduct K n (S.erase i) ^ a • v, ?_, ?_⟩
    · have hcard : (S.card : ℤ) = 1 + ((S.erase i).card : ℤ) := by
        rw [Finset.card_erase_of_mem hi]
        have := Finset.card_pos.mpr ⟨i, hi⟩
        omega
      convert SetLike.GradedSMul.smul_mem
        (SetLike.pow_mem_graded (A := polynomialIntegralGrading) a
          (polynomialHomogeneous_mem_integral K n (S.erase i).card _
            (polynomialHomogeneousSubsetProduct_degree K n (S.erase i)))) hv using 1
      congr 1
      simp only [nsmul_eq_mul, vadd_eq_add]
      rw [hcard]
      ring
    · change LocalizedModule.mk _ _ = actualLocalizedModuleDivisorRestriction (M := V)
        (MvPolynomial.X i) (polynomialHomogeneousSubsetProduct K n S)
          ⟨polynomialHomogeneousSubsetProduct K n (S.erase i),
            polynomialHomogeneousSubsetProduct_factor K n i S hi⟩ z.val
      rw [← he, actualLocalizedModuleDivisorRestriction_mk _ _ _
        (polynomialHomogeneousSubsetProduct_factor K n i S hi)])

/-- True selected-chart restriction is linear for the actual selected-chart homogeneous ring. -/
def polynomialHomogeneousSubsetChartRestriction (i : Fin (n + 1))
    (S : Finset (Fin (n + 1))) (hi : i ∈ S) (k : ℤ) :
    letI := polynomialHomogeneousSubsetChartModule K n ℳ i S hi k
    localizedHomogeneousModulePiece polynomialIntegralGrading ℳ
      (MvPolynomial.X i) 1 (polynomialCoordinate_X_degree i) k →ₗ[polynomialProjCoordinateRing K n i]
        polynomialHomogeneousSubsetPiece K n ℳ S k := by
  letI := polynomialHomogeneousSubsetChartModule K n ℳ i S hi k
  refine { toFun := polynomialHomogeneousSubsetChartRestrictionK K n ℳ i S hi k
           map_add' := (polynomialHomogeneousSubsetChartRestrictionK K n ℳ i S hi k).map_add
           map_smul' := ?_ }
  intro r z
  apply Subtype.ext
  obtain ⟨a, p, hp, rfl⟩ := HomogeneousLocalization.Away.mk_surjective _
    (MvPolynomial.isHomogeneous_X K i) r
  obtain ⟨b, v, hv, he⟩ := z.property
  change actualLocalizedModuleDivisorRestriction (M := V) (MvPolynomial.X i)
    (polynomialHomogeneousSubsetProduct K n S)
    ⟨polynomialHomogeneousSubsetProduct K n (S.erase i),
      polynomialHomogeneousSubsetProduct_factor K n i S hi⟩
    ((HomogeneousLocalization.Away.mk _ (MvPolynomial.isHomogeneous_X K i) a p hp).val • z.val) =
    ((polynomialHomogeneousSubsetChartRingMap K n i S hi)
      (HomogeneousLocalization.Away.mk _ (MvPolynomial.isHomogeneous_X K i) a p hp)).val •
      actualLocalizedModuleDivisorRestriction (M := V) (MvPolynomial.X i)
        (polynomialHomogeneousSubsetProduct K n S)
          ⟨polynomialHomogeneousSubsetProduct K n (S.erase i),
            polynomialHomogeneousSubsetProduct_factor K n i S hi⟩ z.val
  rw [← he, HomogeneousLocalization.Away.val_mk, LocalizedModule.mk_smul_mk]
  change actualLocalizedModuleDivisorRestriction (M := V) (MvPolynomial.X i)
    (polynomialHomogeneousSubsetProduct K n S)
    ⟨polynomialHomogeneousSubsetProduct K n (S.erase i),
      polynomialHomogeneousSubsetProduct_factor K n i S hi⟩
    (LocalizedModule.mk (p • v)
      (homogeneousPowerDenominator (MvPolynomial.X i) a * homogeneousPowerDenominator (MvPolynomial.X i) b)) = _
  rw [← homogeneousPowerDenominator_add,
    actualLocalizedModuleDivisorRestriction_mk _ _ _
      (polynomialHomogeneousSubsetProduct_factor K n i S hi),
    actualLocalizedModuleDivisorRestriction_mk _ _ _
      (polynomialHomogeneousSubsetProduct_factor K n i S hi)]
  change _ = (HomogeneousLocalization.awayMap _
    (polynomialHomogeneousSubsetProduct_degree K n (S.erase i))
    (polynomialHomogeneousSubsetProduct_factor K n i S hi)
    (HomogeneousLocalization.Away.mk _ (MvPolynomial.isHomogeneous_X K i) a p hp)).val • _
  rw [HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.Away.val_mk,
    LocalizedModule.mk_smul_mk]
  change _ = LocalizedModule.mk
    ((p * polynomialHomogeneousSubsetProduct K n (S.erase i) ^ a) •
      (polynomialHomogeneousSubsetProduct K n (S.erase i) ^ b • v))
    (homogeneousPowerDenominator (polynomialHomogeneousSubsetProduct K n S) a *
      homogeneousPowerDenominator (polynomialHomogeneousSubsetProduct K n S) b)
  rw [← homogeneousPowerDenominator_add]
  congr 1
  simp only [smul_smul, pow_add]
  congr 1
  ring


/-- True selected-chart restriction has the literal complementary-factor fraction formula. -/
theorem polynomialHomogeneousSubsetChartRestriction_fraction (i : Fin (n + 1))
    (S : Finset (Fin (n + 1))) (hi : i ∈ S) (k : ℤ)
    (a : ℕ) (v : V) (hv : v ∈ ℳ (k + (a : ℤ) * 1)) :
    (polynomialHomogeneousSubsetChartRestriction K n ℳ i S hi k
      ⟨LocalizedModule.mk v (homogeneousPowerDenominator (MvPolynomial.X i) a),
        a, v, hv, rfl⟩).val =
      LocalizedModule.mk (polynomialHomogeneousSubsetProduct K n (S.erase i) ^ a • v)
        (homogeneousPowerDenominator (polynomialHomogeneousSubsetProduct K n S) a) :=
  actualLocalizedModuleDivisorRestriction_mk _ _ _
    (polynomialHomogeneousSubsetProduct_factor K n i S hi) v a

/-- Powers of the true ratio product act on true selected-chart fractions by literal numerator multiplication. -/
theorem polynomialHomogeneousSubsetRatioPower_smul_fraction (i : Fin (n + 1))
    (S : Finset (Fin (n + 1))) (k : ℤ) (a b : ℕ)
    (v : V) (hv : v ∈ ℳ (k + (b : ℤ) * 1)) :
    (((polynomialProjSubsetRatioProduct K n i S) ^ a) •
      (⟨LocalizedModule.mk v (homogeneousPowerDenominator (MvPolynomial.X i) b),
        b, v, hv, rfl⟩ : localizedHomogeneousModulePiece polynomialIntegralGrading ℳ
          (MvPolynomial.X i) 1 (polynomialCoordinate_X_degree i) k)).val =
      LocalizedModule.mk (polynomialHomogeneousSubsetProduct K n S ^ a • v)
        (homogeneousPowerDenominator (MvPolynomial.X i) (S.card * a + b)) := by
  change ((polynomialProjSubsetRatioProduct K n i S) ^ a).val •
    LocalizedModule.mk v (homogeneousPowerDenominator (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) K) b) = _
  rw [polynomialProjSubsetRatioProduct_eq_mk, HomogeneousLocalization.val_pow,
    HomogeneousLocalization.Away.val_mk, Localization.mk_pow, LocalizedModule.mk_smul_mk]
  congr 1
  apply Subtype.ext
  simp [homogeneousPowerDenominator, pow_mul, pow_add]

/-- The true ratio product acts invertibly on the true subset localized piece. -/
theorem polynomialHomogeneousSubsetRatio_isUnit (i : Fin (n + 1))
    (S : Finset (Fin (n + 1))) (hi : i ∈ S) (k : ℤ) :
    letI := polynomialHomogeneousSubsetChartModule K n ℳ i S hi k
    IsUnit (algebraMap (polynomialProjCoordinateRing K n i)
      (Module.End (polynomialProjCoordinateRing K n i) (polynomialHomogeneousSubsetPiece K n ℳ S k))
        (polynomialProjSubsetRatioProduct K n i S)) := by
  let Rₛ := HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
    (polynomialHomogeneousSubsetProduct K n S)
  let _instAlgebra := (polynomialHomogeneousSubsetChartRingMap K n i S hi).toAlgebra
  let _instChartModule := polynomialHomogeneousSubsetChartModule K n ℳ i S hi k
  let _instTower : IsScalarTower (polynomialProjCoordinateRing K n i) Rₛ
      (polynomialHomogeneousSubsetPiece K n ℳ S k) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let _instLocalization : IsLocalization.Away (polynomialProjSubsetRatioProduct K n i S) Rₛ :=
    polynomialHomogeneousSubsetChartRing_isLocalization K n i S hi
  have hu := IsLocalization.Away.algebraMap_isUnit (R := polynomialProjCoordinateRing K n i)
    (S := Rₛ) (polynomialProjSubsetRatioProduct K n i S)
  have h := hu.map (Algebra.lsmul (polynomialProjCoordinateRing K n i)
    (polynomialProjCoordinateRing K n i) (polynomialHomogeneousSubsetPiece K n ℳ S k))
  convert h using 1
  ext z
  rfl

/-- Every true subset fraction admits actual ratio-product denominator clearing from a selected chart. -/
theorem polynomialHomogeneousSubsetChartRestriction_surj (i : Fin (n + 1))
    (S : Finset (Fin (n + 1))) (hi : i ∈ S) (k : ℤ) :
    letI := polynomialHomogeneousSubsetChartModule K n ℳ i S hi k
    ∀ z : polynomialHomogeneousSubsetPiece K n ℳ S k,
      ∃ (a : ℕ) (v : localizedHomogeneousModulePiece polynomialIntegralGrading ℳ
        (MvPolynomial.X i) 1 (polynomialCoordinate_X_degree i) k),
        polynomialProjSubsetRatioProduct K n i S ^ a • z =
          polynomialHomogeneousSubsetChartRestriction K n ℳ i S hi k v := by
  let _instChartModule := polynomialHomogeneousSubsetChartModule K n ℳ i S hi k
  intro z
  obtain ⟨a, v, hv, he⟩ := z.property
  have hv' : v ∈ ℳ (k + ((S.card * a : ℕ) : ℤ) * 1) := by
    simpa only [Nat.cast_mul, mul_one, one_mul, mul_comm] using hv
  refine ⟨a, ⟨LocalizedModule.mk v
    (homogeneousPowerDenominator (MvPolynomial.X i) (S.card * a)), S.card * a, v, hv', rfl⟩, ?_⟩
  apply Subtype.ext
  rw [polynomialHomogeneousSubsetChartRestriction_fraction K n ℳ i S hi k (S.card * a) v hv']
  change ((polynomialHomogeneousSubsetChartRingMap K n i S hi)
    (polynomialProjSubsetRatioProduct K n i S ^ a)).val • z.val = _
  rw [← he, map_pow, polynomialProjSubsetRatioProduct_eq_mk]
  change (HomogeneousLocalization.awayMap _
    (polynomialHomogeneousSubsetProduct_degree K n (S.erase i))
    (polynomialHomogeneousSubsetProduct_factor K n i S hi)
    (HomogeneousLocalization.Away.mk _ (MvPolynomial.isHomogeneous_X K i) S.card
      (polynomialHomogeneousSubsetProduct K n S) _ ) ^ a).val • _ = _
  rw [HomogeneousLocalization.val_pow, HomogeneousLocalization.awayMap_mk,
    HomogeneousLocalization.Away.val_mk, Localization.mk_pow, LocalizedModule.mk_smul_mk]
  apply LocalizedModule.mk_eq.mpr
  refine ⟨1, ?_⟩
  simp only [Submonoid.smul_def, Submonoid.coe_mul, SubmonoidClass.coe_pow,
    homogeneousPowerDenominator, smul_smul]
  congr 1
  simp only [mul_pow, pow_mul]
  ring


/-- Actual vanishing after subset restriction is killed by an actual power of the true ratio product. -/
theorem polynomialHomogeneousSubsetChartRestriction_kernel (i : Fin (n + 1))
    (S : Finset (Fin (n + 1))) (hi : i ∈ S) (k : ℤ)
    (z : localizedHomogeneousModulePiece polynomialIntegralGrading ℳ
      (MvPolynomial.X i) 1 (polynomialCoordinate_X_degree i) k)
    (hz : polynomialHomogeneousSubsetChartRestriction K n ℳ i S hi k z = 0) :
    ∃ a : ℕ, polynomialProjSubsetRatioProduct K n i S ^ a • z = 0 := by
  obtain ⟨b, v, hv, he⟩ := z.property
  have hz' := congrArg Subtype.val hz
  change actualLocalizedModuleDivisorRestriction (M := V) (MvPolynomial.X i)
    (polynomialHomogeneousSubsetProduct K n S)
    ⟨polynomialHomogeneousSubsetProduct K n (S.erase i),
      polynomialHomogeneousSubsetProduct_factor K n i S hi⟩ z.val = 0 at hz'
  rw [← he, actualLocalizedModuleDivisorRestriction_mk _ _ _
    (polynomialHomogeneousSubsetProduct_factor K n i S hi)] at hz'
  rw [← LocalizedModule.zero_mk 1] at hz'
  obtain ⟨s, hs⟩ := LocalizedModule.mk_eq.mp hz'
  obtain ⟨t, ht⟩ := s.property
  have hs' : polynomialHomogeneousSubsetProduct K n S ^ t •
      (polynomialHomogeneousSubsetProduct K n (S.erase i) ^ b • v) = 0 := by
    simpa only [Submonoid.smul_def, ht, OneMemClass.coe_one, one_smul, smul_zero] using hs
  have hkill : polynomialHomogeneousSubsetProduct K n S ^ (t + b) • v = 0 := by
    calc
      polynomialHomogeneousSubsetProduct K n S ^ (t + b) • v =
          (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) K) ^ b •
            (polynomialHomogeneousSubsetProduct K n S ^ t •
              (polynomialHomogeneousSubsetProduct K n (S.erase i) ^ b • v)) := by
        simp only [smul_smul]
        congr 1
        rw [pow_add, polynomialHomogeneousSubsetProduct_factor K n i S hi, mul_pow]
        ring
      _ = 0 := by rw [hs', smul_zero]
  have hze : z = ⟨LocalizedModule.mk v (homogeneousPowerDenominator (MvPolynomial.X i) b),
      b, v, hv, rfl⟩ := Subtype.ext he.symm
  refine ⟨t + b, ?_⟩
  apply Subtype.ext
  rw [hze, polynomialHomogeneousSubsetRatioPower_smul_fraction K n ℳ i S k (t + b) b v hv,
    hkill, LocalizedModule.zero_mk]
  rfl

/-- The true degree-piece restriction is actual module localization at the actual chart ratio product. -/
theorem polynomialHomogeneousSubsetChartRestriction_isLocalized (i : Fin (n + 1))
    (S : Finset (Fin (n + 1))) (hi : i ∈ S) (k : ℤ) :
    letI := polynomialHomogeneousSubsetChartModule K n ℳ i S hi k
    IsLocalizedModule.Away (polynomialProjSubsetRatioProduct K n i S)
      (polynomialHomogeneousSubsetChartRestriction K n ℳ i S hi k) := by
  let _instChartModule := polynomialHomogeneousSubsetChartModule K n ℳ i S hi k
  exact IsLocalizedModule.Away.mk_of_addCommGroup
    (polynomialHomogeneousSubsetRatio_isUnit K n ℳ i S hi k)
    (polynomialHomogeneousSubsetChartRestriction_surj K n ℳ i S hi k)
    (polynomialHomogeneousSubsetChartRestriction_kernel K n ℳ i S hi k)


end

end SGPT.Foundations.Schemes
