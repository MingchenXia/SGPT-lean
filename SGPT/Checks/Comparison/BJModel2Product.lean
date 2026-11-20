import SGPT.Support.Alterations.Geometry.ProjectiveSpaceBaseChange
import SGPT.Support.Alterations.Geometry.ProjIntegral
import SGPT.Support.Alterations.Geometry.SegreChart
import SGPT.Foundations.Envelope.AlgGeom.ProjectiveFactorizationProducts
import SGPT.Foundations.Envelope.AlgGeom.NativeProjectivityFromPolynomialFactorization
import SGPT.Foundations.Envelope.AlgGeom.ProjectiveFactorizationRingIso
import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-!
# The product `X ×_k ℙ¹_k` and its central fibre (lane BJ-MODEL2, step R1(a))

Source: Boucksom–Jonsson, *Global pluripotential theory over a trivially valued field* ([BJ22],
`references/bj22-trivval`), §1.2 (test configurations as models of `X × ℙ¹`), used in the
comparison `thm:BJappseq` of `chapter_NApotential.tex`. Blueprint: `claude-bj-model2.tex`.

Test configurations of `X` are (normalized) blow-ups of `X × ℙ¹` along flag ideals cosupported on
the central fibre `X × {0}`. This file provides the ambient scheme:

* `geometricallyIntegral_projectiveSpaceStructure`: `ℙⁿ_K ⟶ Spec K` is geometrically integral for
  every field `K` (every base change to a field `E` is `ℙⁿ_E`, which is integral);
* `productLine p = X ×_k ℙ¹_k` for `p : X ⟶ Spec k`, with projections `productFst`, `productSnd`
  and structure morphism `productStructure`; it is integral when `X` is integral and locally
  Noetherian (`productLine_isIntegral`), projective over `k` when `X` is
  (`productStructure_isProjective`), hence proper;
* the `k`-point `0 = [1 : 0]` of `ℙ¹` (`zeroPoint`, a closed immersion), its ideal sheaf
  `zeroIdeal` (the kernel of `zeroPoint`), and the ideal sheaf `centralIdeal p` of the central
  fibre `X × {0}` (its inverse image on `X × ℙ¹`), whose support is the central fibre
  (`support_centralIdeal`) and is not everything when `X ≠ ∅` (`support_centralIdeal_ne_top`).

The coordinate of `ℙ¹ = Proj k[x₀, x₁]` is `t = x₁/x₀` on the standard chart
`D₊(x₀) = Spec k[t]` (`ProjectiveIdeal.CoordinateRing k 0`), and `0 = {t = 0}`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

namespace SGPT.NAPotential.BJ

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open SGPT.Support.Alterations SGPT.Support.Alterations.Geometry

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### Geometric integrality of projective space -/

/-- Integrality of schemes is invariant under isomorphism. -/
instance isIntegral_isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms (C := Scheme.{u}) IsIntegral :=
  ⟨fun e h => by
    let := h
    exact IsIntegral.of_isIso e.hom⟩

/-- Projective space over a field is integral. -/
theorem projectiveSpace_isIntegral (K : Type u) [Field K] (n : ℕ) :
    IsIntegral (projectiveSpace K n) := by
  apply ProjIntegral.isIntegral_proj
  intro h
  have hx := HomogeneousIdeal.mem_irrelevant_of_mem (projectiveSpaceGrading K n)
    (by decide : 0 < (1 : ℕ)) (MvPolynomial.isHomogeneous_X K (0 : Fin (n + 1)))
  rw [h] at hx
  exact MvPolynomial.X_ne_zero (0 : Fin (n + 1)) hx

/-- **Projective space is geometrically integral** over every field `K`: its base change along
`Spec E ⟶ Spec K` for a field `E` is `ℙⁿ_E` (`projectiveSpaceBaseChangeIso`), which is
integral. -/
instance geometricallyIntegral_projectiveSpaceStructure (K : Type u) [Field K] (n : ℕ) :
    GeometricallyIntegral (projectiveSpaceStructure K n) := by
  constructor
  rw [geometrically_iff_of_isClosedUnderIsomorphisms]
  intro E _ y
  obtain ⟨φ, rfl⟩ : ∃ φ, y = Spec.map φ := ⟨Spec.preimage y, (Spec.map_preimage y).symm⟩
  let := projectiveSpace_isIntegral E n
  exact IsIntegral.of_isIso (ProjectiveSpaceBaseChange.projectiveSpaceBaseChangeIso φ.hom n).hom

/-- Projective space over a ring has a polynomial projective factorization. -/
theorem projectiveSpaceStructure_isProjectiveFactorization (R : Type u) [CommRing R] (n : ℕ) :
    IsProjectiveFactorization (projectiveSpaceStructure R n) :=
  (SGPT.Foundations.Envelope.ProjectiveBlowupSequence.isProjectiveOver_iff _).mp
    (isProjectiveOver_projectiveSpaceStructure R n)

/-! ### The product `X ×_k ℙ¹_k` -/

section product

variable {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k))

/-- The product `X ×_k ℙ¹_k` ([BJ22, §1.2]), the ambient scheme of the test configurations of
`X`. -/
abbrev productLine : Scheme.{u} := pullback p (projectiveSpaceStructure k 1)

/-- The first projection `X × ℙ¹ ⟶ X`. -/
abbrev productFst : productLine p ⟶ X := pullback.fst p (projectiveSpaceStructure k 1)

/-- The second projection `X × ℙ¹ ⟶ ℙ¹`. -/
abbrev productSnd : productLine p ⟶ projectiveSpace k 1 :=
  pullback.snd p (projectiveSpaceStructure k 1)

/-- The structure morphism `X × ℙ¹ ⟶ Spec k`. -/
abbrev productStructure : productLine p ⟶ Spec (.of k) := productFst p ≫ p

theorem productSnd_structure :
    productSnd p ≫ projectiveSpaceStructure k 1 = productStructure p :=
  pullback.condition.symm

/-- A scheme projective over a field is locally Noetherian. -/
theorem isLocallyNoetherian_of_isProjective [IsProjective p] : IsLocallyNoetherian X :=
  let : IsProper p := (SGPT.Foundations.Envelope.ProjectiveFactorizationRingIso.of_isProjective p).isProper
  LocallyOfFiniteType.isLocallyNoetherian p

/-- **`X × ℙ¹` is integral** if `X` is integral and locally Noetherian (`ℙ¹` is geometrically
integral, flat and universally open over `k`). -/
instance productLine_isIntegral [IsIntegral X] [IsLocallyNoetherian X] :
    IsIntegral (productLine p) :=
  inferInstance

/-- **`X × ℙ¹` is projective over `k`** if `X` is. -/
theorem productStructure_isProjectiveFactorization (hp : IsProjectiveFactorization p) :
    IsProjectiveFactorization (productStructure p) :=
  SGPT.Foundations.Envelope.ProjectiveFactorizationProducts.pullback p _ hp
    (projectiveSpaceStructure_isProjectiveFactorization k 1)

/-- **`X × ℙ¹` is projective over `k`** if `X` is (Hironaka's projectivity predicate). -/
instance productStructure_isProjective [IsProjective p] : IsProjective (productStructure p) :=
  SGPT.Foundations.Envelope.NativeProjectivityFromPolynomialFactorization.of_isProjectiveFactorization _
    (productStructure_isProjectiveFactorization p
      (SGPT.Foundations.Envelope.ProjectiveFactorizationRingIso.of_isProjective p))

/-- **`X × ℙ¹` is integral** if `X` is integral and projective over `k`. -/
theorem productLine_isIntegral_of_isProjective [IsIntegral X] [IsProjective p] :
    IsIntegral (productLine p) :=
  let := isLocallyNoetherian_of_isProjective p
  inferInstance

instance productStructure_isProper [IsProjective p] : IsProper (productStructure p) :=
  (productStructure_isProjectiveFactorization p
    (SGPT.Foundations.Envelope.ProjectiveFactorizationRingIso.of_isProjective p)).isProper

instance productLine_isLocallyNoetherian [IsProjective p] : IsLocallyNoetherian (productLine p) :=
  LocallyOfFiniteType.isLocallyNoetherian (productStructure p)

instance productLine_compactSpace [IsProjective p] : CompactSpace (productLine p) :=
  QuasiCompact.compactSpace_of_compactSpace (productStructure p)

instance productLine_isSeparated [IsProjective p] : (productLine p).IsSeparated :=
  ⟨by
    have h : IsSeparated (productStructure p ≫ terminal.from (Spec (.of k))) := inferInstance
    simpa only [terminal.comp_from] using h⟩

/-- The second projection is surjective if `X` is nonempty. -/
theorem productSnd_surjective [Nonempty X] : Function.Surjective (productSnd p) := by
  have : Surjective p := ⟨fun y => by
    obtain ⟨x⟩ := (inferInstance : Nonempty X)
    exact ⟨x, Subsingleton.elim _ _⟩⟩
  exact (inferInstance : Surjective (productSnd p)).surj

end product

/-! ### The point `0` of `ℙ¹` and the central fibre -/

section zero

variable (k : Type u) [Field k]

/-- The standard chart `D₊(x₀) = Spec k[t] ⟶ ℙ¹_k` (with `t = x₁/x₀`). -/
abbrev lineChart :
    Spec (.of (ProjectiveIdeal.CoordinateRing k (0 : Fin 2))) ⟶ projectiveSpace k 1 :=
  Segre.coordinateChartInclusion (R := k) (0 : Fin 2)

/-- Evaluation of the chart coordinates at `0`. -/
def evalZero : ProjectiveIdeal.CoordinateRing k (0 : Fin 2) →+* k :=
  MvPolynomial.eval (fun _ => 0)

/-- **The point `0 = [1 : 0]` of `ℙ¹_k`**, the centre of the central fibre. -/
def zeroPoint : Spec (.of k) ⟶ projectiveSpace k 1 :=
  Spec.map (CommRingCat.ofHom (evalZero k)) ≫ lineChart k

theorem zeroPoint_structure : zeroPoint k ≫ projectiveSpaceStructure k 1 = 𝟙 _ := by
  rw [zeroPoint, Category.assoc, Segre.coordinateChartInclusion_structure, ← Spec.map_comp,
    ← Spec.map_id]
  congr 1
  ext c
  simp [evalZero]

instance zeroPoint_isClosedImmersion : IsClosedImmersion (zeroPoint k) := by
  have : IsClosedImmersion (zeroPoint k ≫ projectiveSpaceStructure k 1) := by
    rw [zeroPoint_structure]
    infer_instance
  exact IsClosedImmersion.of_comp (zeroPoint k) (projectiveSpaceStructure k 1)

/-- **The ideal sheaf of `0 ∈ ℙ¹_k`** (the kernel of `zeroPoint`). -/
def zeroIdeal : (projectiveSpace k 1).IdealSheafData := (zeroPoint k).ker

theorem support_zeroIdeal :
    ((zeroIdeal k).support : Set (projectiveSpace k 1)) = Set.range (zeroPoint k) := by
  rw [zeroIdeal, Scheme.Hom.support_ker]
  exact (zeroPoint k).isClosedEmbedding.isClosed_range.closure_eq

/-- The generic point of the chart `Spec k[t]`, a point of `ℙ¹` different from `0`. -/
theorem exists_not_mem_range_zeroPoint : ∃ x : projectiveSpace k 1, x ∉ Set.range (zeroPoint k) := by
  let A := ProjectiveIdeal.CoordinateRing k (0 : Fin 2)
  let η : Spec (.of A) := ⟨⊥, Ideal.isPrime_bot⟩
  refine ⟨lineChart k η, ?_⟩
  rintro ⟨z, hz⟩
  rw [zeroPoint, Scheme.Hom.comp_apply] at hz
  have hz' := (lineChart k).isOpenEmbedding.injective hz
  have hX : (MvPolynomial.X ⟨1, by decide⟩ : A) ∈
      (Spec.map (CommRingCat.ofHom (evalZero k)) z).asIdeal := by
    rw [Spec.map_apply, PrimeSpectrum.comap_asIdeal]
    simp only [Ideal.mem_comap, CommRingCat.hom_ofHom, evalZero, MvPolynomial.eval_X]
    exact Ideal.zero_mem _
  rw [hz'] at hX
  exact MvPolynomial.X_ne_zero _ ((Submodule.mem_bot _).mp hX)

theorem support_zeroIdeal_ne_top : (zeroIdeal k).support ≠ ⊤ := by
  intro h
  obtain ⟨x, hx⟩ := exists_not_mem_range_zeroPoint k
  have : x ∈ ((zeroIdeal k).support : Set (projectiveSpace k 1)) := by rw [h]; trivial
  rw [support_zeroIdeal] at this
  exact hx this

variable {k} {X : Scheme.{u}} (p : X ⟶ Spec (.of k))

/-- **The ideal sheaf of the central fibre `X × {0}`** of `X × ℙ¹`: the inverse image of the ideal
sheaf of `0 ∈ ℙ¹`. -/
def centralIdeal : (productLine p).IdealSheafData := (zeroIdeal k).comap (productSnd p)

/-- The central fibre `X × {0}` is the support of `centralIdeal`. -/
theorem support_centralIdeal : ((centralIdeal p).support : Set (productLine p)) =
    productSnd p ⁻¹' Set.range (zeroPoint k) := by
  rw [centralIdeal, Scheme.IdealSheafData.support_comap]
  change productSnd p ⁻¹' ((zeroIdeal k).support : Set _) = _
  rw [support_zeroIdeal]

/-- The central fibre is a proper closed subset of `X × ℙ¹` if `X` is nonempty. -/
theorem support_centralIdeal_ne_top [Nonempty X] : (centralIdeal p).support ≠ ⊤ := by
  intro h
  obtain ⟨x, hx⟩ := exists_not_mem_range_zeroPoint k
  obtain ⟨z, rfl⟩ := productSnd_surjective p x
  have : z ∈ ((centralIdeal p).support : Set (productLine p)) := by rw [h]; trivial
  rw [support_centralIdeal] at this
  exact hx this

end zero

end SGPT.NAPotential.BJ
