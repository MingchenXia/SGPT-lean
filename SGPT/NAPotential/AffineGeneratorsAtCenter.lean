import SGPT.NAPotential.GraphDivisorOrderTransport
import SGPT.NAPotential.NativeGraphPrimeLocalization

/-! # Original affine generators on a prescribed actual centre chart

Complete blueprint: `affine-generators-at-center.tex`.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.NAPotential.AffineGeneratorsAtCenter
open AlgebraicGeometry CategoryTheory Topology IsLocalRing Opposite
open SGPT.NAPotential.Berkovich
open SGPT.NAPotential.AlgPrimes3.PrimeDivisorOver'
variable {X : Scheme.{0}} (D : PrimeDivisorOver X)

/-- The original affine coefficient chart is PRESCRIBED and retains the actual centre. -/
theorem exists_affine_generators_on (U : X.Opens) (hUa : IsAffineOpen U)
    (hpU : D.π D.point ∈ U) :
    ∃ (hU : D.π (genericPoint D.Y) ∈ U) (s : ℕ)
      (b : Fin s → X.residueField (D.π (genericPoint D.Y))),
      (∀ g ∈ Subring.closure (Set.range (sectionToField D U hU) ∪ Set.range b), g ≠ 0 →
        0 ≤ D.ord g) ∧
      ∀ g : X.residueField (D.π (genericPoint D.Y)), g ≠ 0 → 0 ≤ D.ord g →
        ∃ a ∈ Subring.closure (Set.range (sectionToField D U hU) ∪ Set.range b),
        ∃ c ∈ Subring.closure (Set.range (sectionToField D U hU) ∪ Set.range b),
          c ≠ 0 ∧ D.ord c = 0 ∧ g * c = a := by
  classical
  have hpU' : D.point ∈ D.π ⁻¹ᵁ U := hpU
  obtain ⟨_, ⟨V, hVa, rfl⟩, hpV, hVU⟩ :=
    D.Y.isBasis_affineOpens.exists_subset_of_mem_open hpU' (D.π ⁻¹ᵁ U).isOpen
  have hηp : genericPoint D.Y ⤳ D.point := (genericPoint_spec D.Y).specializes (Set.mem_univ _)
  have hηV : genericPoint D.Y ∈ V := hηp.mem_open V.isOpen hpV
  have hηU : D.π (genericPoint D.Y) ∈ U := hVU hηV
  have e : V ≤ D.π ⁻¹ᵁ U := hVU
  have : Nonempty V := ⟨⟨_, hpV⟩⟩
  have : Nonempty (D.π ⁻¹ᵁ U) := ⟨⟨_, hpU'⟩⟩
  -- `Γ(V, 𝒪_Y)` is a finitely generated `Γ(U, 𝒪_X)`-algebra
  set φ : Γ(X, U) →+* Γ(D.Y, V) := (D.π.appLE U V e).hom with hφ
  have hft : φ.FiniteType :=
    HasRingHomProperty.appLE @LocallyOfFiniteType D.π inferInstance ⟨U, hUa⟩ ⟨V, hVa⟩ e
  let := φ.toAlgebra
  obtain ⟨t, ht⟩ := hft.out
  set ψ : Γ(D.Y, V) →+* X.residueField (D.π (genericPoint D.Y)) :=
    (pullbackEquiv D).symm.toRingHom.comp (D.Y.germToFunctionField V).hom with hψ
  set b : Fin t.card → X.residueField (D.π (genericPoint D.Y)) :=
    fun i => ψ (t.equivFin.symm i).1 with hb
  set S := Set.range (sectionToField D U hηU) ∪ Set.range b with hS
  -- `ψ ∘ φ` is `sectionToField`
  have hψφ : ∀ a, ψ (φ a) = sectionToField D U hηU a := by
    intro a
    apply (pullbackEquiv D).injective
    rw [hψ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.apply_symm_apply, pullbackEquiv_apply, pullback_sectionToField]
    rw [hφ, Scheme.Hom.appLE]
    change (D.Y.presheaf.germ V (genericPoint D.Y) hηV)
      ((D.Y.presheaf.map (homOfLE e).op) (D.π.app U a)) = _
    rw [TopCat.Presheaf.germ_res_apply]
  -- the image of `ψ` lies in `A[b]`
  have hψS : ∀ x : Γ(D.Y, V), ψ x ∈ Subring.closure S := by
    intro x
    have hx : x ∈ Algebra.adjoin Γ(X, U) (t : Set Γ(D.Y, V)) := by rw [ht]; trivial
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      apply Subring.subset_closure
      right
      refine ⟨t.equivFin ⟨x, hx⟩, ?_⟩
      simp [hb]
    | algebraMap a =>
      apply Subring.subset_closure
      left
      exact ⟨a, (hψφ a).symm⟩
    | add x y _ _ hx hy =>
      rw [map_add]
      exact Subring.add_mem _ hx hy
    | mul x y _ _ hx hy =>
      rw [map_mul]
      exact Subring.mul_mem _ hx hy
  -- the pull-back of `ψ x` is the germ of `x` at `D`
  have hpbψ : ∀ x : Γ(D.Y, V), D.pullback (ψ x) =
      algebraMap (D.Y.presheaf.stalk D.point) D.Y.functionField (D.Y.presheaf.germ V _ hpV x) := by
    intro x
    rw [← pullbackEquiv_apply, hψ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply,
      Scheme.algebraMap_germ_eq_germToFunctionField]
  -- `A[b]` lies in the valuation ring
  set T : Subring (X.residueField (D.π (genericPoint D.Y))) :=
    (algebraMap (D.Y.presheaf.stalk D.point) D.Y.functionField).range.comap D.pullback with hT
  have hST : Subring.closure S ≤ T := by
    rw [Subring.closure_le]
    rintro g (⟨a, rfl⟩ | ⟨i, rfl⟩)
    · rw [SetLike.mem_coe, hT, Subring.mem_comap, pullback_sectionToField]
      exact ⟨_, Scheme.algebraMap_germ_eq_germToFunctionField (X := D.Y) hpU' _⟩
    · rw [SetLike.mem_coe, hT, Subring.mem_comap, hpbψ]
      exact ⟨_, rfl⟩
  refine ⟨hηU, t.card, b, fun g hg hg0 => (ord_nonneg_iff_mem_range D hg0).mpr (hST hg),
    fun g hg0 hg => ?_⟩
  -- the converse: `R_D` is the localization of `Γ(V, 𝒪_Y)` at the prime of `D`
  obtain ⟨r, hr⟩ := (ord_nonneg_iff_mem_range D hg0).mp hg
  let := TopCat.Presheaf.algebra_section_stalk D.Y.presheaf ⟨D.point, hpV⟩
  have hloc : IsLocalization.AtPrime (D.Y.presheaf.stalk D.point)
      (hVa.primeIdealOf ⟨D.point, hpV⟩).asIdeal := hVa.isLocalization_stalk ⟨D.point, hpV⟩
  obtain ⟨⟨a', c'⟩, hac⟩ := IsLocalization.surj (hVa.primeIdealOf ⟨D.point, hpV⟩).asIdeal.primeCompl r
  have hgerm : ∀ x : Γ(D.Y, V), algebraMap Γ(D.Y, V) (D.Y.presheaf.stalk D.point) x =
      D.Y.presheaf.germ V _ hpV x := fun x => rfl
  simp only [hgerm] at hac
  have hcu : IsUnit (D.Y.presheaf.germ V _ hpV (c' : Γ(D.Y, V))) := by
    by_contra h
    exact c'.2 ((IsLocalization.AtPrime.to_map_mem_maximal_iff (D.Y.presheaf.stalk D.point)
      (hVa.primeIdealOf ⟨D.point, hpV⟩).asIdeal (c' : Γ(D.Y, V))).mp h)
  refine ⟨ψ a', hψS a', ψ c', hψS c', ?_, ?_, ?_⟩
  · intro h0
    have h1 := hpbψ c'
    rw [h0, map_zero] at h1
    exact hcu.ne_zero ((IsFractionRing.injective _ D.Y.functionField) (h1.symm.trans (map_zero _).symm))
  · exact ord_eq_zero_of_isUnit D hcu (hpbψ c')
  · apply D.pullback_injective
    rw [map_mul, hpbψ, hpbψ, ← hr, ← map_mul, hac]

/-- Actual prime localization and its original coefficient map on the PRESCRIBED affine chart. -/
theorem exists_primeLocalization_on (U : X.Opens) (hUa : IsAffineOpen U)
    (hpU : D.π D.point ∈ U) :
    ∃ (hU : D.π (genericPoint D.Y) ∈ U) (s : ℕ)
      (b : Fin s → X.residueField (D.π (genericPoint D.Y))),
      letI := (sectionToField D U hU).toAlgebra
      ∃ i : Algebra.adjoin Γ(X, U) (Set.range b) →+* D.Y.presheaf.stalk D.point,
        (∀ v : Algebra.adjoin Γ(X, U) (Set.range b),
          algebraMap (D.Y.presheaf.stalk D.point) D.Y.functionField (i v) = D.pullback v) ∧
        letI := i.toAlgebra
        IsLocalization.AtPrime (D.Y.presheaf.stalk D.point) ((maximalIdeal _).comap i) ∧
          IsDiscreteValuationRing (Localization.AtPrime ((maximalIdeal _).comap i)) := by
  obtain ⟨hU, s, b, hB, hfrac⟩ := exists_affine_generators_on D U hUa hpU
  refine ⟨hU, s, b, ?_⟩
  let := (sectionToField D U hU).toAlgebra
  have hd := SGPT.NAPotential.AlgPrimes3.ProjectiveGraphRelations.adjoin_toSubring_eq
    (A := Γ(X, U)) b
  change (Algebra.adjoin Γ(X, U) (Set.range b)).toSubring =
    Subring.closure (Set.range (sectionToField D U hU) ∪ Set.range b) at hd
  have hloc := GraphDivisorOrderTransport.exists_primeLocalization_of_orderFractions D _ hB hfrac
  rw [← hd] at hloc
  obtain ⟨i, hi, hloc⟩ := hloc
  refine ⟨i, hi, ?_⟩
  let : Algebra (Algebra.adjoin Γ(X, U) (Set.range b)) (D.Y.presheaf.stalk D.point) := i.toAlgebra
  let p := (maximalIdeal (D.Y.presheaf.stalk D.point)).comap i
  let : IsLocalization.AtPrime (D.Y.presheaf.stalk D.point) p := hloc
  exact ⟨inferInstance, NativeGraphPrimeLocalization.atPrime_dvr_of_localization
    (R := D.Y.presheaf.stalk D.point) p⟩

/-- The SAME prescribed centre chart produces the literal native `X.functionField`
graph localization, retaining its exact original coefficient square and actual DVR prime. -/
theorem exists_nativePrimeLocalization_on [IsIntegral X]
    (U : X.Opens) (hUa : IsAffineOpen U) (hpU : D.π D.point ∈ U) :
    ∃ (_hU : D.π (genericPoint D.Y) ∈ U) (s : ℕ)
      (b : Fin s → X.residueField (D.π (genericPoint D.Y))),
      letI : Nonempty U := ⟨⟨D.π D.point, hpU⟩⟩
      let bX := fun k => OpenDivisorOrderTransport.originalFunctionFieldEquiv D (b k)
      ∃ iX : Algebra.adjoin Γ(X, U) (Set.range bX) →+* D.Y.presheaf.stalk D.point,
        (∀ v : Algebra.adjoin Γ(X, U) (Set.range bX),
          algebraMap (D.Y.presheaf.stalk D.point) D.Y.functionField (iX v) =
            D.pullback ((OpenDivisorOrderTransport.originalFunctionFieldEquiv D).symm v)) ∧
        letI := iX.toAlgebra
        IsLocalization.AtPrime (D.Y.presheaf.stalk D.point) ((maximalIdeal _).comap iX) ∧
          IsDiscreteValuationRing (Localization.AtPrime ((maximalIdeal _).comap iX)) := by
  obtain ⟨hU, s, b, i, hi, hloc, -⟩ := exists_primeLocalization_on D U hUa hpU
  refine ⟨hU, s, b, ?_⟩
  let : Nonempty U := ⟨⟨D.π D.point, hpU⟩⟩
  let := (sectionToField D U hU).toAlgebra
  let e := OpenDivisorOrderTransport.originalGraphAlgebraEquiv D U hU b
  let iX := i.comp e.symm.toRingHom
  refine ⟨iX, ?_, ?_⟩
  · intro v
    change algebraMap _ D.Y.functionField (i (e.symm v)) = _
    rw [hi (e.symm v)]
    apply congrArg D.pullback
    apply (OpenDivisorOrderTransport.originalFunctionFieldEquiv D).injective
    rw [(OpenDivisorOrderTransport.originalFunctionFieldEquiv D).apply_symm_apply]
    have h := OpenDivisorOrderTransport.originalGraphAlgebraEquiv_coe D U hU b (e.symm v)
    change (e (e.symm v) : X.functionField) =
      OpenDivisorOrderTransport.originalFunctionFieldEquiv D (e.symm v) at h
    rw [e.apply_symm_apply] at h
    exact h.symm
  · let : Algebra _ (D.Y.presheaf.stalk D.point) := iX.toAlgebra
    let p := (maximalIdeal (D.Y.presheaf.stalk D.point)).comap iX
    let : IsLocalization.AtPrime (D.Y.presheaf.stalk D.point) p :=
      NativeGraphPrimeLocalization.primeLocalization_baseEquiv i e.toRingEquiv hloc
    exact ⟨inferInstance, NativeGraphPrimeLocalization.atPrime_dvr_of_localization
      (R := D.Y.presheaf.stalk D.point) p⟩

end SGPT.NAPotential.AffineGeneratorsAtCenter
