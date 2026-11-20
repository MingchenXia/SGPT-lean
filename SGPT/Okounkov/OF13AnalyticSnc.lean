import SGPT.Okounkov.OF13FlatSnc
import SGPT.Okounkov.OF11SncFlag
import SGPT.NAPotential.FSPosImmersion
import SGPT.Okounkov.SchemeNativeStalkFlatness
import SGPT.Projective.AlgebraicSmoothStalk
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Analytic normal crossings data at the centre give the admissible flag

Source: chapter *The theory of Okounkov bodies*, Section *Flags and valuations*, `rmk:Abhyankar`:
*if a valuation has value group identified with `ℤⁿ_lex` and maximal rational rank `n`, then
[CFKLRS17, Theorem 2.9] shows that it is equivalent to, but not necessarily equal to, a valuation
induced by an admissible flag on a modification of `X`.*

Lane OF11 (`OF11.exists_admissibleFlag_lexEquivalent_of_model`) proved the conclusion on every
smooth model `V` of `ℂ(X)` on which, at the centre `x` of `ν`, elements `u₁, …, uₙ ∈ ℂ(X)` with
`ν(u_k) = e_k` are Laurent monomials `ε_k ∏ⱼ zⱼ^{a_{kj}}` in *algebraic* strict normal crossings
coordinates `zⱼ ∈ 𝒪_{V,x}` (`OF11.IsSNCCoordinates`). Resolution of singularities is available in
this project only analytically (principalization on complex manifolds), so its output is analytic:
the germs of the `u_k` at the point are analytic units times monomials in analytic coordinates.

This file proves that **analytic data suffice**, as soon as the coordinates have algebraic local
equations. Let `V` be an integral scheme, smooth of relative dimension `n` over `ℂ` (separated,
quasi-compact), `p` a complex point with image `x`, and `stalkToModel : 𝒪_{V,x} → 𝒪_{ℂⁿ,0}` the
analytic germ in the preferred chart at `p` (faithfully flat, local, injective). If
`z₁, …, zₙ ∈ 𝒪_{V,x}` are such that the germs `tⱼ = zⱼ^{an}` generate the maximal ideal of
`𝒪_{ℂⁿ,0}` and every ideal `(t_s)` is prime (they are analytic coordinates), then:

* `isSNCCoordinates_of_analytic`: `z` are strict normal crossings coordinates at `x`
  (`(z) = 𝔪_x` and `(z_s)` prime by faithful flatness; `ht (z_s) = |s|` by Krull's height theorem
  and the chain `(z_∅) ⊊ ⋯`; `𝒪_{V,x}/(z_s)` formally smooth by the Jacobian criterion with the
  analytic point derivations `a ↦ d(a^{an})(0)·v` dual to `dt`, `dualVectors_of_span_eq`);
* `exists_admissibleFlag_lexEquivalent_of_analytic`: if moreover the meromorphic germ of each
  `u_k` is an analytic unit times `∏ⱼ tⱼ^{a_{kj}}` (`a_{kj} ∈ ℤ`) and the germ of `u_k` or of
  `u_k⁻¹` is holomorphic, then `ν` is equivalent to the valuation `ν_{Y•} ∘ e` of an admissible
  flag `Y•` on `V` with point `x` (the units `ε_k` and the regularity of `u_k` are algebraic by
  faithful flatness: `OF13.exists_unit_algebraMap_eq_of_map_eq`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Okounkov.OF13

open CategoryTheory AlgebraicGeometry Filter IsLocalRing SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open HironakaHolomorphicJetMonomialSpan HolomorphicGermCoordinateDerivation
open SGPT.Okounkov SGPT.NAPotential.FSPos SGPT.Okounkov.OF5 SGPT.Okounkov.OF6 SGPT.Okounkov.ValCurr
open SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open scoped Topology Manifold

/-! ### Dual vectors of analytic coordinates -/

section Dual

variable {n : ℕ}

/-- If germs `t₁, …, tₙ` generate the maximal ideal of `𝒪_{ℂⁿ,0}`, their differentials at `0`
are a basis: there are vectors `vᵢ` with `dtⱼ(0)·vᵢ = δᵢⱼ`. -/
theorem dualVectors_of_span_eq (t : Fin n → HolGerm (ComplexModel n))
    (ht : Ideal.span (Set.range t) = maximalIdeal (HolGerm (ComplexModel n))) :
    ∃ v : Fin n → ComplexModel n, ∀ i j, germDeriv (v i) (t j) = if j = i then 1 else 0 := by
  classical
  have ht0 : ∀ j, HolGerm.eval (t j) = 0 := fun j => by
    rw [← HolGerm.mem_maximalIdeal_iff, ← ht]
    exact Ideal.subset_span ⟨j, rfl⟩
  have hc : ∀ m : Fin n, ∃ c : Fin n → HolGerm (ComplexModel n),
      ∑ j, c j * t j = coordinateGerm m := by
    intro m
    have hm : coordinateGerm m ∈ Ideal.span (Set.range t) := by
      rw [ht, HolGerm.mem_maximalIdeal_iff]
      simp [coordinateGerm, HolGerm.eval_mk]
    exact (Ideal.mem_span_range_iff_exists_fun).mp hm
  choose c hc using hc
  let J : Matrix (Fin n) (Fin n) ℂ := fun j l => HolGerm.eval (coordinatePartial l (t j))
  let C : Matrix (Fin n) (Fin n) ℂ := fun m j => HolGerm.eval (c m j)
  have hCJ : C * J = 1 := by
    ext m l
    have h := congrArg (fun g => HolGerm.eval (coordinatePartial l g)) (hc m)
    simp only [map_sum, Derivation.leibniz, smul_eq_mul, map_add, map_mul, ht0, zero_mul,
      add_zero, coordinatePartial_coordinate] at h
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [C, J]
    rw [h]
    split_ifs <;> simp
  have hJC : J * C = 1 := mul_eq_one_comm.mp hCJ
  refine ⟨fun i => WithLp.toLp 2 (fun l => C l i), fun i j => ?_⟩
  have h := congrFun (congrFun hJC j) i
  rw [Matrix.mul_apply, Matrix.one_apply] at h
  simp only [germDeriv]
  rw [← h]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

end Dual

/-! ### The analytic germ map of a smooth scheme -/

section Scheme

variable {V : Scheme.{0}} (f : V ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]

local instance of13Topology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance of13Charts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance of13Manifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

variable (p : SchemeComplexPoint f)

/-- The analytic germ map `𝒪_{V,x} → 𝒪_{ℂⁿ,0}` is faithfully flat. -/
theorem stalkToModel_faithfullyFlat' : (stalkToModel f n p).FaithfullyFlat :=
  RingHom.FaithfullyFlat.stableUnderComposition _ _
    (schemeNativeStalkGerm_faithfullyFlat f n p)
    (RingHom.FaithfullyFlat.of_bijective (NativeHolGerm.chartEquiv (n := n) p).bijective)

/-- The analytic germ map is a local homomorphism. -/
instance stalkToModel_isLocalHom : IsLocalHom (stalkToModel f n p) := by
  unfold stalkToModel
  let e := (NativeHolGerm.chartEquiv (n := n) p).toRingHom
  have : IsLocalHom e := by
    refine ⟨fun a ha => ?_⟩
    have h := ha.map (NativeHolGerm.chartEquiv (n := n) p).symm.toRingHom
    change IsUnit ((NativeHolGerm.chartEquiv (n := n) p).symm
      ((NativeHolGerm.chartEquiv (n := n) p) a)) at h
    rwa [RingEquiv.symm_apply_apply] at h
  exact RingHom.isLocalHom_comp e (schemeNativeStalkGerm f n p)

theorem stalkToModel_injective [IsIntegral V] : Function.Injective (stalkToModel f n p) :=
  (NativeHolGerm.chartEquiv (n := n) p).injective.comp (schemeNativeStalkGerm_injective f n p)

/-- The structural constants have constant analytic germs. -/
theorem stalkToModel_algebraMap (c : ℂ) :
    letI := stalkComplexAlgebra f (schemeComplexPointImage f p)
    stalkToModel f n p (algebraMap ℂ (V.presheaf.stalk (schemeComplexPointImage f p)) c) =
      HolGerm.constHom c :=
  stalkToModel_constants f n p c

/-- The residue map `a ↦ a(p)`, read through the analytic germ. -/
def pointResidue : V.presheaf.stalk (schemeComplexPointImage f p) →+* ℂ :=
  HolGerm.eval.comp (stalkToModel f n p)

theorem pointResidue_algebraMap (c : ℂ) :
    letI := stalkComplexAlgebra f (schemeComplexPointImage f p)
    pointResidue f n p (algebraMap ℂ (V.presheaf.stalk (schemeComplexPointImage f p)) c) = c := by
  change HolGerm.eval (stalkToModel f n p _) = c
  rw [stalkToModel_algebraMap, HolGerm.eval_constHom]

/-- The analytic point derivation `a ↦ d(a^{an})(0)·v` of `𝒪_{V,x}` into `ℂ` (a `𝒪_{V,x}`-module
through `pointResidue`). -/
def pointDerivation (v : ComplexModel n) :
    letI := stalkComplexAlgebra f (schemeComplexPointImage f p)
    letI := (pointResidue f n p).toAlgebra
    Derivation ℂ (V.presheaf.stalk (schemeComplexPointImage f p)) ℂ :=
  letI := stalkComplexAlgebra f (schemeComplexPointImage f p)
  letI := (pointResidue f n p).toAlgebra
  Derivation.mk'
    { toFun := fun a => germDeriv v (stalkToModel f n p a)
      map_add' := fun a b => by simp only [map_add, germDeriv_add]
      map_smul' := fun c a => by
        simp only [Algebra.smul_def, map_mul, germDeriv_mul, RingHom.id_apply]
        rw [stalkToModel_algebraMap, HolGerm.eval_constHom]
        change c * _ + _ * germDeriv v (algebraMap ℂ (HolGerm (ComplexModel n)) c) = _
        rw [germDeriv_algebraMap, mul_zero, add_zero]
        rfl }
    (fun a b => by
      change germDeriv v (stalkToModel f n p (a * b)) =
        pointResidue f n p a * germDeriv v (stalkToModel f n p b) +
          pointResidue f n p b * germDeriv v (stalkToModel f n p a)
      rw [map_mul, germDeriv_mul]
      rfl)

theorem pointDerivation_apply (v : ComplexModel n)
    (a : V.presheaf.stalk (schemeComplexPointImage f p)) :
    letI := stalkComplexAlgebra f (schemeComplexPointImage f p)
    letI := (pointResidue f n p).toAlgebra
    pointDerivation f n p v a = germDeriv v (stalkToModel f n p a) :=
  rfl

/-! ### Strict normal crossings coordinates from analytic coordinates -/

variable {f n p}

/-- If the analytic germs of `z₁, …, zₙ ∈ 𝒪_{V,x}` generate the maximal ideal of `𝒪_{ℂⁿ,0}`, then
`zⱼ ∉ (z_s)` for `j ∉ s`, and each `𝒪_{V,x}/(z_s)` is formally smooth over `ℂ`. -/
theorem formallySmooth_quotient_of_analytic
    (z : Fin n → V.presheaf.stalk (schemeComplexPointImage f p))
    (hm : Ideal.span (Set.range (stalkToModel f n p ∘ z)) = maximalIdeal (HolGerm (ComplexModel n)))
    (s : Finset (Fin n)) :
    letI := stalkComplexAlgebra f (schemeComplexPointImage f p)
    Algebra.FormallySmooth ℂ (V.presheaf.stalk (schemeComplexPointImage f p) ⧸
      Ideal.span (z '' ↑s)) := by
  classical
  let x := schemeComplexPointImage f p
  let O := V.presheaf.stalk x
  let := stalkComplexAlgebra f x
  let : Algebra O ℂ := (pointResidue f n p).toAlgebra
  have : IsScalarTower ℂ O ℂ := IsScalarTower.of_algebraMap_eq fun c =>
    (pointResidue_algebraMap f n p c).symm
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  obtain ⟨hfs, -, hfin, hfree⟩ := originalSmoothStalk_differentials f x
  obtain ⟨v, hv⟩ := dualVectors_of_span_eq _ hm
  let I : Ideal O := Ideal.span (z '' ↑s)
  have hres : ∀ j, pointResidue f n p (z j) = 0 := fun j => by
    change HolGerm.eval (stalkToModel f n p (z j)) = 0
    rw [← HolGerm.mem_maximalIdeal_iff, ← hm]
    exact Ideal.subset_span ⟨j, rfl⟩
  have hIker : I ≤ RingHom.ker (pointResidue f n p) := by
    rw [Ideal.span_le]
    rintro _ ⟨j, -, rfl⟩
    exact hres j
  let ρ' : O ⧸ I →+* ℂ := Ideal.Quotient.lift I (pointResidue f n p) hIker
  let : Algebra (O ⧸ I) ℂ := ρ'.toAlgebra
  have : IsScalarTower O (O ⧸ I) ℂ := IsScalarTower.of_algebraMap_eq fun a => rfl
  have hI1 : I ≠ ⊤ := fun h => by
    have h1 : (1 : O) ∈ RingHom.ker (pointResidue f n p) := hIker (h ▸ Submodule.mem_top)
    rw [RingHom.mem_ker, map_one] at h1
    exact one_ne_zero h1
  have : Nontrivial (O ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI1
  have : IsLocalRing (O ⧸ I) := IsLocalRing.of_surjective' (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective
  have hρ'surj : Function.Surjective ρ' := fun c => ⟨Ideal.Quotient.mk I (algebraMap ℂ O c), by
    change pointResidue f n p (algebraMap ℂ O c) = c
    exact pointResidue_algebraMap f n p c⟩
  have hBK : maximalIdeal (O ⧸ I) ≤ RingHom.ker (algebraMap (O ⧸ I) ℂ) := by
    have hmax : (RingHom.ker ρ').IsMaximal := RingHom.ker_isMaximal_of_surjective ρ' hρ'surj
    exact (IsLocalRing.eq_maximalIdeal hmax).symm.le
  let g : s → O := fun j => z j
  have hg : ∀ j, g j ∈ RingHom.ker (algebraMap O (O ⧸ I)) := fun j => by
    rw [RingHom.mem_ker, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span ⟨j, j.2, rfl⟩
  have hker : RingHom.ker (algebraMap O (O ⧸ I)) = Ideal.span (Set.range g) := by
    rw [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]
    change Ideal.span (z '' ↑s) = _
    rw [Set.image_eq_range]
    rfl
  let D : s → Derivation ℂ O ℂ := fun i => pointDerivation f n p (v i)
  have hD : ∀ i j, D i (g j) = if i = j then 1 else 0 := fun i j => by
    change germDeriv (v i) (stalkToModel f n p (z j)) = _
    have h := hv i j
    simp only [Function.comp_apply] at h
    rw [h]
    by_cases hij : i = j
    · rw [if_pos (congrArg Subtype.val hij).symm, if_pos hij]
    · rw [if_neg fun h => hij (Subtype.ext h.symm), if_neg hij]
  exact formallySmooth_of_derivations Ideal.Quotient.mk_surjective g hg hker D hD hBK

/-- For analytic coordinates `t = z^{an}`, `zⱼ ∉ (z_s)` when `j ∉ s`. -/
theorem notMem_span_image_of_analytic
    (z : Fin n → V.presheaf.stalk (schemeComplexPointImage f p))
    (hm : Ideal.span (Set.range (stalkToModel f n p ∘ z)) = maximalIdeal (HolGerm (ComplexModel n)))
    (s : Finset (Fin n)) (j : Fin n) (hj : j ∉ s) : z j ∉ Ideal.span (z '' ↑s) := by
  classical
  obtain ⟨v, hv⟩ := dualVectors_of_span_eq _ hm
  have hres : ∀ k, HolGerm.eval (stalkToModel f n p (z k)) = 0 := fun k => by
    rw [← HolGerm.mem_maximalIdeal_iff, ← hm]
    exact Ideal.subset_span ⟨k, rfl⟩
  intro hmem
  have key : ∀ a ∈ Ideal.span (z '' ↑s),
      HolGerm.eval (stalkToModel f n p a) = 0 ∧ germDeriv (v j) (stalkToModel f n p a) = 0 := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem a ha =>
        obtain ⟨k, hk, rfl⟩ := ha
        refine ⟨hres k, ?_⟩
        change germDeriv (v j) ((stalkToModel f n p ∘ z) k) = 0
        rw [hv j k, if_neg]
        rintro rfl
        exact hj hk
    | zero => simp [germDeriv_zero]
    | add a b _ _ ha hb => simp [map_add, germDeriv_add, ha.1, hb.1, ha.2, hb.2]
    | smul r a _ ha =>
        rw [smul_eq_mul, map_mul, map_mul, germDeriv_mul, ha.1, ha.2]
        simp
  have h := (key _ hmem).2
  change germDeriv (v j) ((stalkToModel f n p ∘ z) j) = 0 at h
  rw [hv j j, if_pos rfl] at h
  exact one_ne_zero h

/-- **Analytic coordinates with algebraic local equations are strict normal crossings
coordinates.** If the analytic germs `tⱼ` of `z₁, …, zₙ ∈ 𝒪_{V,x}` generate the maximal ideal of
`𝒪_{ℂⁿ,0}` and all the ideals `(t_s)` are prime, then `z` are strict normal crossings coordinates
at `x` in the sense of lane OF11. -/
theorem isSNCCoordinates_of_analytic [IsIntegral V]
    (z : Fin n → V.presheaf.stalk (schemeComplexPointImage f p))
    (hm : Ideal.span (Set.range (stalkToModel f n p ∘ z)) = maximalIdeal (HolGerm (ComplexModel n)))
    (hp : ∀ s : Finset (Fin n), (Ideal.span ((stalkToModel f n p ∘ z) '' ↑s)).IsPrime) :
    OF11.IsSNCCoordinates f (schemeComplexPointImage f p) z := by
  have hff := stalkToModel_faithfullyFlat' f n p
  have : IsNoetherianRing (V.presheaf.stalk (schemeComplexPointImage f p)) := by
    let := stalkComplexAlgebra f (schemeComplexPointImage f p)
    have : Smooth f := SmoothOfRelativeDimension.smooth n f
    obtain ⟨-, hft, -, -⟩ := originalSmoothStalk_differentials f (schemeComplexPointImage f p)
    exact Algebra.EssFiniteType.isNoetherianRing ℂ _
  have hprime : ∀ s : Finset (Fin n), (Ideal.span (z '' ↑s)).IsPrime := fun s =>
    isPrime_span_image_of_map _ z hff _ (hp s)
  refine ⟨span_range_eq_maximalIdeal_of_map _ z hff hm, fun s => ⟨hprime s, ?_, ?_⟩⟩
  · exact height_span_image_eq_card z hprime
      (fun s j hj => notMem_span_image_of_analytic z hm s j hj) s
  · exact formallySmooth_quotient_of_analytic z hm s

/-! ### Meromorphic germs of rational functions -/

variable (f n p) in
/-- The meromorphic germ at `p` (in the preferred chart) of a rational function of `V`. -/
def modelFractionGerm [IsIntegral V] :
    V.functionField →+* FractionRing (HolGerm (ComplexModel n)) :=
  IsFractionRing.map (A := V.presheaf.stalk (schemeComplexPointImage f p))
    (K := V.functionField) (L := FractionRing (HolGerm (ComplexModel n)))
    (stalkToModel_injective f n p)

theorem modelFractionGerm_algebraMap [IsIntegral V]
    (a : V.presheaf.stalk (schemeComplexPointImage f p)) :
    modelFractionGerm f n p (algebraMap _ V.functionField a) =
      algebraMap _ (FractionRing (HolGerm (ComplexModel n))) (stalkToModel f n p a) :=
  fractionMap_algebraMap (stalkToModel_injective f n p) a

/-! ### The main theorem -/

/-- **[CFKLRS17, Thm 2.9] from analytic log resolution data.** Let `X` be integral, `ν` a
valuation of `ℂ(X)` with values in `ℤⁿ_lex`, and `V` an integral scheme, smooth of relative
dimension `n` over `ℂ` (separated, quasi-compact), with `e : ℂ(X) ≃ ℂ(V)` (a model of `ℂ(X)`),
on which `ν` is centred at the image `x` of a complex point `p`. Suppose that there are
`z₁, …, zₙ ∈ 𝒪_{V,x}` (algebraic local equations) whose analytic germs `tⱼ` are analytic
coordinates at `p` (they generate the maximal ideal and every `(t_s)` is prime), and
`u₁, …, uₙ ∈ ℂ(X)` with `ν(u_k) = e_k` whose meromorphic germs at `p` are analytic units times
Laurent monomials `∏ⱼ tⱼ^{a_{kj}}`, with the germ of `u_k` or of `u_k⁻¹` holomorphic. Then `ν` is
equivalent to the valuation `ν_{Y•} ∘ e` of an admissible flag `Y•` on `V` with point `x`. -/
theorem exists_admissibleFlag_lexEquivalent_of_analytic {X : Scheme.{0}} [IsIntegral X]
    [IsIntegral V] (e : X.functionField ≃+* V.functionField)
    (ν : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ))))
    (hcent : AlgebraicValuation.IsValuationCenter (ν.comap e.symm.toRingHom)
      (schemeComplexPointImage f p))
    (z : Fin n → V.presheaf.stalk (schemeComplexPointImage f p))
    (hm : Ideal.span (Set.range (stalkToModel f n p ∘ z)) = maximalIdeal (HolGerm (ComplexModel n)))
    (hp : ∀ s : Finset (Fin n), (Ideal.span ((stalkToModel f n p ∘ z) '' ↑s)).IsPrime)
    (u : Fin n → X.functionField) (η : Fin n → (HolGerm (ComplexModel n))ˣ)
    (a : Fin n → Fin n → ℤ)
    (hu : ∀ k, modelFractionGerm f n p (e (u k)) =
      algebraMap _ (FractionRing (HolGerm (ComplexModel n))) (η k : HolGerm (ComplexModel n)) *
        ∏ j, (algebraMap _ (FractionRing (HolGerm (ComplexModel n)))
          (stalkToModel f n p (z j))) ^ (a k j))
    (hreg : ∀ k, (∃ h : HolGerm (ComplexModel n), modelFractionGerm f n p (e (u k)) =
        algebraMap _ (FractionRing (HolGerm (ComplexModel n))) h) ∨
      ∃ h : HolGerm (ComplexModel n), modelFractionGerm f n p (e (u k))⁻¹ =
        algebraMap _ (FractionRing (HolGerm (ComplexModel n))) h)
    (hνu : ∀ k, ν (u k) = basisValue k) :
    ∃ (Y : Fin (n + 1) → Set V) (hY : IsAdmissibleFlag f n Y),
      hY.point = schemeComplexPointImage f p ∧
      ValuationsLexEquivalent ((admissibleFlagValuation hY).comap e.toRingHom) ν := by
  classical
  let x := schemeComplexPointImage f p
  let L := FractionRing (HolGerm (ComplexModel n))
  have hinj := stalkToModel_injective f n p
  have hff := stalkToModel_faithfullyFlat' f n p
  have hz := isSNCCoordinates_of_analytic z hm hp
  have hz0 : ∀ j, z j ≠ 0 := fun j h => by
    have := notMem_span_image_of_analytic z hm ∅ j (Finset.notMem_empty j)
    apply this
    rw [h]
    exact Ideal.zero_mem _
  let P : Fin n → V.functionField := fun k =>
    ∏ j, (algebraMap _ V.functionField (z j)) ^ (a k j)
  have hP0 : ∀ k, P k ≠ 0 := fun k => Finset.prod_ne_zero_iff.mpr fun j _ =>
    zpow_ne_zero _ ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (hz0 j))
  have hPgerm : ∀ k, modelFractionGerm f n p (P k) =
      ∏ j, (algebraMap _ L (stalkToModel f n p (z j))) ^ (a k j) := fun k => by
    simp only [P, map_prod, map_zpow₀, modelFractionGerm_algebraMap]
    rfl
  have hε : ∀ k, ∃ ε : (V.presheaf.stalk x)ˣ,
      algebraMap _ V.functionField (ε : V.presheaf.stalk x) = e (u k) / P k := fun k => by
    refine exists_unit_algebraMap_eq_of_map_eq (K := V.functionField) (L := L) hinj hff _ (η k) ?_
    have hL : modelFractionGerm f n p (P k) ≠ 0 :=
      (map_ne_zero_iff _ (modelFractionGerm f n p).injective).mpr (hP0 k)
    change modelFractionGerm f n p (e (u k) / P k) = _
    rw [map_div₀, div_eq_iff hL, hu k, hPgerm k]
  choose ε hε using hε
  refine OF11.exists_admissibleFlag_lexEquivalent_of_model e ν hcent hz u ε a (fun k => ?_)
    (fun k => ?_) hνu
  · rw [hε k, div_mul_cancel₀ _ (hP0 k)]
  · rcases hreg k with ⟨h, hh⟩ | ⟨h, hh⟩
    · exact Or.inl (exists_algebraMap_eq_of_map_eq (K := V.functionField) (L := L) hinj hff _ h hh)
    · exact Or.inr (exists_algebraMap_eq_of_map_eq (K := V.functionField) (L := L) hinj hff _ h hh)

end Scheme

end SGPT.Okounkov.OF13
