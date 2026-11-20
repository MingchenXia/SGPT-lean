import SGPT.NAPotential.ProjectiveGraphEmbedding
import SGPT.NAPotential.ProjectiveGraphProjectiveHomeomorph

/-!
# the projective scheme cut out by homogeneous polynomials

Source: `rmk:bdiv:L749` (algebraization of the book's blow-up models).

For homogeneous polynomials `P_k` of degree `m` in `ℂ[x₀, …, x_N]`, with homogeneous ideal
`J = (P_k)`, the scheme `V = Proj(ℂ[x]/J)` (`zeroScheme`) is a closed subscheme of `ℙᴺ_ℂ`
(`zeroSchemeι`, lane NAPotential's quotient closed immersion), hence a projective complex scheme
(`zeroEmbedding : ClosedProjectiveEmbedding`).

* `zeroSchemeι_app_ratio_dehom`: the regular function `P_k/x_i^m` of `ℙᴺ` on `D₊(x_i)` pulls
  back to `0` on `V`;
* `mem_prime_zeroPoint`: every complex point of `V` maps to a point of `ℙᴺ` whose homogeneous
  prime contains `J`;
* `exists_zeroPoint_eq`: conversely every complex point `[v]` of `ℙᴺ` with `P_k(v) = 0` for all
  `k` comes from a complex point of `V` (the evaluation at `v` on the chart `D₊(x_i)` factors
  through `(ℂ[x]/J)_{(x_i)}`);
* `projectivePoint_zeroPoint_mem_iff`: the complex points of `V`, read in `ℙᴺ`, are exactly the
  common zeros `{x : P_k(x) = 0 ∀ k}`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.BDivisor.BD5

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes HomogeneousLocalization Set
open SGPT.NAPotential.AlgPrimes3.GradedGraphQuotient
open SGPT.NAPotential.AlgPrimes3.ProjectiveGraphProjectivePoint
open SGPT.NAPotential.AlgPrimes3.ProjectiveGraphProjectiveReadback
open SGPT.Okounkov SGPT.GAGA.H0S SGPT.NAPotential.FSPos
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The grading of `ℂ[x₀, …, x_N]` by degree. -/
abbrev polyGrading (N : ℕ) : ℕ → Submodule ℂ (MvPolynomial (Fin (N + 1)) ℂ) :=
  MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℂ

theorem X_mem_polyGrading {N : ℕ} (i : Fin (N + 1)) :
    (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) ℂ) ∈ polyGrading N 1 :=
  (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X ℂ i)

section Scheme

variable {N : ℕ} {μ : Type} (P : μ → MvPolynomial (Fin (N + 1)) ℂ) {m : ℕ}
  (hP : ∀ k, (P k).IsHomogeneous m)

/-- The homogeneous ideal `J = (P_k)`. -/
def polyIdeal : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℂ) :=
  ⟨Ideal.span (Set.range P), Ideal.homogeneous_span _ _ (by
    rintro _ ⟨k, rfl⟩
    exact ⟨m, (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (hP k)⟩)⟩

theorem mem_polyIdeal (k : μ) : P k ∈ (polyIdeal P hP).toIdeal :=
  Ideal.subset_span ⟨k, rfl⟩

/-- **The projective scheme `V(P) = Proj(ℂ[x]/(P_k))`.** -/
abbrev zeroScheme : Scheme.{0} :=
  Proj (grading (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℂ) (polyIdeal P hP).toIdeal)

/-- The closed immersion `V(P) → ℙᴺ`. -/
def zeroSchemeι : zeroScheme P hP ⟶ polynomialProj ℂ N :=
  quotientSchemeMap (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℂ) (polyIdeal P hP)

instance zeroSchemeι_isClosedImmersion : IsClosedImmersion (zeroSchemeι P hP) :=
  instIsClosedImmersion_quotientSchemeMap _ _

/-- The structure morphism `V(P) → Spec ℂ`. -/
def zeroStructure : zeroScheme P hP ⟶ Spec (.of ℂ) :=
  zeroSchemeι P hP ≫ polynomialProjStructureMap ℂ N

/-- `V(P)` is projective: its closed projective embedding into `ℙᴺ`. -/
def zeroEmbedding : ClosedProjectiveEmbedding (zeroStructure P hP) where
  ambientDimension := N
  map := zeroSchemeι P hP
  closedImmersion := inferInstance
  over_base := rfl

/-- Complex points of `V(P)` as complex points of `ℙᴺ`. -/
def zeroPoint (q : SchemeComplexPoint (zeroStructure P hP)) :
    SchemeComplexPoint (polynomialProjStructureMap ℂ N) :=
  schemeComplexPointMap (zeroStructure P hP) (polynomialProjStructureMap ℂ N) (zeroSchemeι P hP)
    rfl q

theorem zeroPoint_image (q : SchemeComplexPoint (zeroStructure P hP)) :
    schemeComplexPointImage (polynomialProjStructureMap ℂ N) (zeroPoint P hP q) =
      zeroSchemeι P hP (schemeComplexPointImage (zeroStructure P hP) q) := rfl

theorem zeroPoint_injective : Function.Injective (zeroPoint P hP) := by
  intro q q' h
  apply schemeComplexPointImage_injective (zeroStructure P hP)
  have h' := congrArg (schemeComplexPointImage (polynomialProjStructureMap ℂ N)) h
  rw [zeroPoint_image, zeroPoint_image] at h'
  exact (zeroSchemeι P hP).isClosedEmbedding.injective h'

/-! ### The equations pull back to zero -/

theorem ratioMap_dehomogenization (i : Fin (N + 1)) (Q : MvPolynomial (Fin (N + 1)) ℂ)
    (hQ : Q ∈ polyGrading N (m • 1)) :
    polynomialProjRatioMap ℂ N i (polynomialProjDehomogenization ℂ N i Q) =
      Away.mk (polyGrading N) (X_mem_polyGrading i) m Q hQ := by
  rw [← polynomialProjCoordinateDehomogenization_mk ℂ N i m Q (by simpa using hQ)]
  exact polynomialProjRatioMap_coordinateDehomogenization ℂ N i _

/-- The regular function `P_k / x_i^m` on `D₊(x_i)` pulls back to zero on `V(P)`. -/
theorem zeroSchemeι_app_ratio_dehom (i : Fin (N + 1)) (k : μ) :
    (zeroSchemeι P hP).app (polynomialProjCoordinateOpen ℂ N i)
      (polynomialProjCoordinateSectionMap ℂ N i
        (polynomialProjRatioMap ℂ N i (polynomialProjDehomogenization ℂ N i (P k)))) = 0 := by
  have hk : P k ∈ polyGrading N (m • 1) := by simpa using hP k
  rw [ratioMap_dehomogenization i (P k) hk]
  have hsq := Proj.awayToSection_comp_appLE (gradedMk (polyGrading N) (polyIdeal P hP).toIdeal)
    (irrelevant_le_map _ (polyIdeal P hP)) (X_mem_polyGrading i)
  have h := congrArg (fun φ => φ.hom (Away.mk (polyGrading N) (X_mem_polyGrading i) m (P k) hk))
    hsq
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom, Away.map_mk] at h
  rw [Scheme.Hom.app_eq_appLE]
  change (Scheme.Hom.appLE (zeroSchemeι P hP) _ _ _)
    ((Proj.awayToSection _ (MvPolynomial.X i)).hom _) = 0
  erw [h]
  have hz : Away.mk (grading (polyGrading N) (polyIdeal P hP).toIdeal)
      ((gradedMk _ _).map_mem (X_mem_polyGrading i)) m
      (gradedMk (polyGrading N) (polyIdeal P hP).toIdeal (P k))
      ((gradedMk _ _).map_mem hk) = 0 := by
    apply HomogeneousLocalization.val_injective
    rw [Away.val_mk, HomogeneousLocalization.val_zero, gradedMk_apply,
      Ideal.Quotient.eq_zero_iff_mem.mpr (mem_polyIdeal P hP k), Localization.mk_zero]
  erw [hz]
  exact map_zero _

/-! ### Complex points -/

/-- The image of a complex point of `V(P)` lies on `V(J)`. -/
theorem mem_prime_zeroPoint (q : SchemeComplexPoint (zeroStructure P hP)) (k : μ) :
    P k ∈ (schemeComplexPointImage (polynomialProjStructureMap ℂ N)
      (zeroPoint P hP q)).asHomogeneousIdeal := by
  have hr : schemeComplexPointImage (polynomialProjStructureMap ℂ N) (zeroPoint P hP q) ∈
      Set.range (quotientSchemeMap (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℂ)
        (polyIdeal P hP)) := ⟨_, rfl⟩
  rw [range_quotientSchemeMap] at hr
  exact hr (mem_polyIdeal P hP k)

/-- Common zeros in a vector: scaling. -/
theorem eval_smul_eq_zero {v : Fin (N + 1) → ℂ} (c : ℂ) {Q : MvPolynomial (Fin (N + 1)) ℂ}
    (hQ : Q.IsHomogeneous m) (h : MvPolynomial.eval v Q = 0) :
    MvPolynomial.eval (fun j => c * v j) Q = 0 := by
  have := homogeneousPolynomial_eval₂_scaled hQ (RingHom.id ℂ) v c
  change MvPolynomial.eval₂Hom (RingHom.id ℂ) (fun j => c * v j) Q = 0
  rw [this]
  change c ^ m * MvPolynomial.eval v Q = 0
  rw [h, mul_zero]

/-- The vector-point evaluation of the chart ring at `v` reads homogeneous fractions as values
at the normalized vector `v / v_i`. -/
theorem vectorChartAlgebraPoint_mk (i : Fin (N + 1)) (v : Fin (N + 1) → ℂ) (hi : v i ≠ 0)
    (n : ℕ) (a : MvPolynomial (Fin (N + 1)) ℂ) (ha : a ∈ polyGrading N (n • 1)) :
    polynomialProjVectorChartAlgebraPoint N i v (Away.mk (polyGrading N) (X_mem_polyGrading i) n a ha) =
      MvPolynomial.eval (fun j => (v i)⁻¹ * v j) a := by
  change MvPolynomial.eval (polynomialProjVectorRatios N i v)
    (polynomialProjCoordinateDehomogenization ℂ N i (Away.mk _ _ n a ha)) = _
  rw [polynomialProjCoordinateDehomogenization_mk ℂ N i n a (by simpa using ha),
    polynomialProjVectorChartAlgebraPoint_dehomogenization N i v hi]

/-- The kernel of the chart map `ℂ[x]_{(x_i)} → (ℂ[x]/J)_{(x_i)}` vanishes at every common
zero `v` with `v_i ≠ 0`. -/
theorem ker_awayMap_le (i : Fin (N + 1)) (v : Fin (N + 1) → ℂ) (hi : v i ≠ 0)
    (hv : ∀ k, MvPolynomial.eval v (P k) = 0) :
    RingHom.ker (Away.map (gradedMk (polyGrading N) (polyIdeal P hP).toIdeal) (MvPolynomial.X i)) ≤
      RingHom.ker (polynomialProjVectorChartAlgebraPoint N i v).toRingHom := by
  intro z hz
  rw [RingHom.mem_ker] at hz ⊢
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective (polyGrading N) (X_mem_polyGrading i) z
  change polynomialProjVectorChartAlgebraPoint N i v _ = 0
  rw [vectorChartAlgebraPoint_mk i v hi]
  rw [Away.map_mk] at hz
  have hv0 := congrArg HomogeneousLocalization.val hz
  rw [Away.val_mk, HomogeneousLocalization.val_zero, Localization.mk_eq_mk',
    IsLocalization.mk'_eq_zero_iff] at hv0
  obtain ⟨⟨_, e, rfl⟩, he⟩ := hv0
  have hmem : MvPolynomial.X i ^ e * a ∈ (polyIdeal P hP).toIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simpa [gradedMk_apply, map_mul, map_pow] using he
  have hle : (polyIdeal P hP).toIdeal ≤
      RingHom.ker (MvPolynomial.eval (fun j => (v i)⁻¹ * v j)) := by
    change Ideal.span (Set.range P) ≤ _
    rw [Ideal.span_le]
    rintro _ ⟨k, rfl⟩
    exact eval_smul_eq_zero (v i)⁻¹ (hP k) (hv k)
  have h := hle hmem
  rw [RingHom.mem_ker] at h
  simpa [map_mul, map_pow, hi] using h

/-- The lifted evaluation `(ℂ[x]/J)_{(x_i)} → ℂ` at a common zero. -/
def liftedChartEval (i : Fin (N + 1)) (v : Fin (N + 1) → ℂ) (hi : v i ≠ 0)
    (hv : ∀ k, MvPolynomial.eval v (P k) = 0) :
    Away (grading (polyGrading N) (polyIdeal P hP).toIdeal)
      (gradedMk (polyGrading N) (polyIdeal P hP).toIdeal (MvPolynomial.X i)) →+* ℂ :=
  RingHom.liftOfSurjective
    (Away.map (gradedMk (polyGrading N) (polyIdeal P hP).toIdeal) (MvPolynomial.X i))
    (awayMap_surjective (polyGrading N) (polyIdeal P hP) (X_mem_polyGrading i))
    ⟨(polynomialProjVectorChartAlgebraPoint N i v).toRingHom, ker_awayMap_le P hP i v hi hv⟩

theorem liftedChartEval_comp (i : Fin (N + 1)) (v : Fin (N + 1) → ℂ) (hi : v i ≠ 0)
    (hv : ∀ k, MvPolynomial.eval v (P k) = 0) :
    (liftedChartEval P hP i v hi hv).comp
      (Away.map (gradedMk (polyGrading N) (polyIdeal P hP).toIdeal) (MvPolynomial.X i)) =
      (polynomialProjVectorChartAlgebraPoint N i v).toRingHom :=
  RingHom.liftOfRightInverse_comp _ _ _ _

/-- The scheme point of `V(P)` over a common zero. -/
def liftedChartPoint (i : Fin (N + 1)) (v : Fin (N + 1) → ℂ) (hi : v i ≠ 0)
    (hv : ∀ k, MvPolynomial.eval v (P k) = 0) : Spec (.of ℂ) ⟶ zeroScheme P hP :=
  Spec.map (CommRingCat.ofHom (liftedChartEval P hP i v hi hv)) ≫
    Proj.awayι (grading (polyGrading N) (polyIdeal P hP).toIdeal)
      (gradedMk (polyGrading N) (polyIdeal P hP).toIdeal (MvPolynomial.X i))
      ((gradedMk _ _).map_mem (X_mem_polyGrading i)) (by decide : 0 < 1)

theorem liftedChartPoint_comp (i : Fin (N + 1)) (v : Fin (N + 1) → ℂ) (hi : v i ≠ 0)
    (hv : ∀ k, MvPolynomial.eval v (P k) = 0) :
    liftedChartPoint P hP i v hi hv ≫ zeroSchemeι P hP =
      (polynomialProjVectorChartPoint N i v).val := by
  rw [polynomialProjVectorChartPoint_val, liftedChartPoint, Category.assoc]
  have hsq := Proj.awayι_comp_map (gradedMk (polyGrading N) (polyIdeal P hP).toIdeal)
    (irrelevant_le_map (polyGrading N) (polyIdeal P hP)) (by decide : 0 < 1)
    (MvPolynomial.X i) (X_mem_polyGrading i)
  erw [hsq]
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, liftedChartEval_comp]
  rfl

/-- **Every common zero comes from a complex point of `V(P)`.** -/
theorem exists_zeroPoint_eq (i : Fin (N + 1)) (v : Fin (N + 1) → ℂ) (hi : v i ≠ 0)
    (hv : ∀ k, MvPolynomial.eval v (P k) = 0) :
    ∃ q : SchemeComplexPoint (zeroStructure P hP),
      zeroPoint P hP q = polynomialProjVectorChartPoint N i v := by
  refine ⟨⟨liftedChartPoint P hP i v hi hv, ?_⟩, ?_⟩
  · change _ ≫ (zeroSchemeι P hP ≫ polynomialProjStructureMap ℂ N) = _
    rw [← Category.assoc, liftedChartPoint_comp]
    exact (polynomialProjVectorChartPoint N i v).property
  · exact Subtype.ext (liftedChartPoint_comp P hP i v hi hv)

/-- The common zero set `{x ∈ ℙᴺ : P_k(x) = 0 ∀ k}`. -/
def commonZeros : Set (ComplexProjectiveSpace N) :=
  {x | ∀ k, MvPolynomial.eval x.rep (P k) = 0}

omit hP in
theorem mk_mem_commonZeros_iff (hP : ∀ k, (P k).IsHomogeneous m) {v : Fin (N + 1) → ℂ}
    (hv : v ≠ 0) : mk v hv ∈ commonZeros P ↔ ∀ k, MvPolynomial.eval v (P k) = 0 := by
  obtain ⟨c, hc, hrep⟩ := rep_smul (mk v hv) hv rfl
  simp only [commonZeros, mem_ofPred_eq, hrep]
  refine forall_congr' fun k => ?_
  have h := eval_smul_eq_zero (v := v) c (hP k)
  constructor
  · intro h0
    have h' := eval_smul_eq_zero (v := fun j => c * v j) c⁻¹ (hP k) (by simpa [Pi.smul_def] using h0)
    simpa [← mul_assoc, inv_mul_cancel₀ hc] using h'
  · intro h0
    simpa [Pi.smul_def] using h h0

/-- **The complex points of `V(P)` are the common zeros.**  A complex point `p` of `ℙᴺ` comes
from `V(P)` iff its projective point lies in `{P_k = 0}`. -/
theorem mem_range_zeroPoint_iff (p : SchemeComplexPoint (polynomialProjStructureMap ℂ N)) :
    p ∈ Set.range (zeroPoint P hP) ↔
      projectivePoint (polynomialProjStructureMap ℂ N) (identityEmbedding N) N p ∈
        commonZeros P := by
  obtain ⟨⟨v, hv⟩, rfl⟩ := polynomialProjNonzeroVectorPoint_surjective N p
  obtain ⟨i, hi⟩ := polynomialProjVector_exists_nonzero_coordinate N v hv
  rw [polynomialProjNonzeroVectorPoint_eq_chart N ⟨v, hv⟩ i hi,
    nativeVectorPoint_projectivePoint N i v hv hi, mk_mem_commonZeros_iff P hP hv]
  constructor
  · rintro ⟨q, hq⟩ k
    have h := mem_prime_zeroPoint P hP q k
    rw [hq, polynomialProjVectorChartPoint_mem_homogeneous N i v hi m (P k) (hP k)] at h
    exact h
  · intro h
    obtain ⟨q, hq⟩ := exists_zeroPoint_eq P hP i v hi h
    exact ⟨q, hq⟩

end Scheme

end SGPT.BDivisor.BD5
