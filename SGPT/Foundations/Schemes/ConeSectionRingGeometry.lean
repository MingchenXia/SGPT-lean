import SGPT.Foundations.Schemes.SectionRingValuation
import SGPT.Foundations.Schemes.ValuationLocalization
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic

/-! # The genuine section-ring cone and its vertex

The cone is the spectrum of the constructed direct sum of actual global
sections. Its irrelevant ideal is the kernel of the literal degree-zero
projection. Proper integral geometry over an algebraically closed field
provides the actual constants equivalence used to derive the closed vertex.
-/

open CategoryTheory Opposite AlgebraicGeometry
open scoped DirectSum

namespace SGPT.Foundations.Schemes

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

variable {X : Scheme.{u}}

/-- The literal degree-zero projection is a ring map, by the actual homogeneous
multiplication and positivity of the natural-number grading. -/
def IntrinsicLineBundle.sectionRingAugmentation (L : IntrinsicLineBundle X) :
    L.sectionRing →+* Γ(X, ⊤) where
  toFun := L.degreeComponent 0
  map_zero' := (L.degreeComponent 0).map_zero
  map_add' := (L.degreeComponent 0).map_add
  map_one' := by
    rw [← L.ofSection_one]
    exact DirectSum.of_eq_same 0 (bundlePowerGlobalOne L.sheaf)
  map_mul' x y := by
    classical
    let : CommRing (bundlePowerGlobalSections L.sheaf 0) :=
      inferInstanceAs (CommRing Γ(X, ⊤))
    induction x using DirectSum.induction_on with
    | zero => simp
    | of m s =>
        induction y using DirectSum.induction_on with
        | zero => simp
        | of n t =>
            change L.degreeComponent 0 (L.ofSection m s * L.ofSection n t) = _
            rw [L.ofSection_mul]
            by_cases hm : m = 0
            · subst m
              by_cases hn : n = 0
              · subst n
                change ((DirectSum.of (bundlePowerGlobalSections L.sheaf) 0)
                  (atlasPowerGlobalMul L.atlas 0 0 s t)) 0 =
                    (((DirectSum.of (bundlePowerGlobalSections L.sheaf) 0) s) 0 : Γ(X, ⊤)) *
                      (((DirectSum.of (bundlePowerGlobalSections L.sheaf) 0) t) 0 : Γ(X, ⊤))
                erw [DirectSum.of_eq_same, DirectSum.of_eq_same, DirectSum.of_eq_same]
                exact atlasPowerGlobalMul_degree_zero L.atlas s t
              · change ((DirectSum.of (bundlePowerGlobalSections L.sheaf) (0 + n))
                  (atlasPowerGlobalMul L.atlas 0 n s t)) 0 =
                    (((DirectSum.of (bundlePowerGlobalSections L.sheaf) 0) s) 0 : Γ(X, ⊤)) *
                      (((DirectSum.of (bundlePowerGlobalSections L.sheaf) n) t) 0 : Γ(X, ⊤))
                erw [DirectSum.of_eq_of_ne (0 + n) 0 _ (by omega),
                  DirectSum.of_eq_of_ne n 0 _ (by omega), mul_zero]
            · change ((DirectSum.of (bundlePowerGlobalSections L.sheaf) (m + n))
                (atlasPowerGlobalMul L.atlas m n s t)) 0 =
                  (((DirectSum.of (bundlePowerGlobalSections L.sheaf) m) s) 0 : Γ(X, ⊤)) *
                    (((DirectSum.of (bundlePowerGlobalSections L.sheaf) n) t) 0 : Γ(X, ⊤))
              erw [DirectSum.of_eq_of_ne (m + n) 0 _ (by omega),
                DirectSum.of_eq_of_ne m 0 _ (by omega), zero_mul]
        | add y z hy hz => simp only [mul_add, map_add, hy, hz]
    | add x z hx hz => simp only [add_mul, map_add, hx, hz]

/-- Its value is exactly the literal direct-sum degree-zero component. -/
theorem IntrinsicLineBundle.sectionRingAugmentation_apply (L : IntrinsicLineBundle X)
    (x : L.sectionRing) : L.sectionRingAugmentation x = L.degreeComponent 0 x := rfl

/-- Actual degree-zero global functions are retained unchanged. -/
theorem IntrinsicLineBundle.sectionRingAugmentation_constants (L : IntrinsicLineBundle X)
    (r : Γ(X, ⊤)) : L.sectionRingAugmentation (L.sectionRingConstants r) = r := by
  change ((DirectSum.of (bundlePowerGlobalSections L.sheaf) 0) r) 0 = r
  exact DirectSum.of_eq_same (β := bundlePowerGlobalSections L.sheaf) 0 r

/-- Every actual global function is the augmentation of its degree-zero inclusion. -/
theorem IntrinsicLineBundle.sectionRingAugmentation_surjective (L : IntrinsicLineBundle X) :
    Function.Surjective L.sectionRingAugmentation :=
  fun r ↦ ⟨L.sectionRingConstants r, L.sectionRingAugmentation_constants r⟩

/-- The cone uses the actual ring operations constructed from sheaf multiplication. -/
def IntrinsicLineBundle.sectionRingCone (L : IntrinsicLineBundle X) : Scheme.{u} :=
  Spec (.of L.sectionRing)

/-- The actual positive-degree ideal, with no colength or vertex certificate. -/
def IntrinsicLineBundle.irrelevantIdeal (L : IntrinsicLineBundle X) : Ideal L.sectionRing :=
  RingHom.ker L.sectionRingAugmentation

/-- Membership is precisely vanishing of the actual degree-zero component. -/
theorem IntrinsicLineBundle.mem_irrelevantIdeal (L : IntrinsicLineBundle X)
    (x : L.sectionRing) : x ∈ L.irrelevantIdeal ↔ L.degreeComponent 0 x = 0 := Iff.rfl

/-- Every genuine positive-degree homogeneous section lies in the irrelevant ideal. -/
theorem IntrinsicLineBundle.ofSection_mem_irrelevantIdeal (L : IntrinsicLineBundle X)
    {n : ℕ} (hn : 0 < n) (s : bundlePowerGlobalSections L.sheaf n) :
    L.ofSection n s ∈ L.irrelevantIdeal := by
  rw [L.mem_irrelevantIdeal]
  exact DirectSum.of_eq_of_ne n 0 s (by omega)

/-- The actual ideal is homogeneous: all literal degree components of an element
of it also belong to it. -/
theorem IntrinsicLineBundle.irrelevantIdeal_homogeneous (L : IntrinsicLineBundle X)
    {x : L.sectionRing} (hx : x ∈ L.irrelevantIdeal) (n : ℕ) :
    L.ofSection n (L.degreeComponent n x) ∈ L.irrelevantIdeal := by
  by_cases hn : n = 0
  · subst n
    rw [L.mem_irrelevantIdeal] at hx ⊢
    change ((DirectSum.of (bundlePowerGlobalSections L.sheaf) 0)
      (L.degreeComponent 0 x)) 0 = 0
    erw [DirectSum.of_eq_same]
    exact hx
  · exact L.ofSection_mem_irrelevantIdeal (by omega) _

/-- Conversely membership of every homogeneous component implies membership
of the finite sum itself. -/
theorem IntrinsicLineBundle.mem_irrelevantIdeal_iff_components (L : IntrinsicLineBundle X)
    (x : L.sectionRing) : x ∈ L.irrelevantIdeal ↔
      ∀ n, L.ofSection n (L.degreeComponent n x) ∈ L.irrelevantIdeal := by
  constructor
  · exact fun hx n ↦ L.irrelevantIdeal_homogeneous hx n
  · intro h
    have hz := h 0
    rw [L.mem_irrelevantIdeal] at hz ⊢
    change ((DirectSum.of (bundlePowerGlobalSections L.sheaf) 0)
      (L.degreeComponent 0 x)) 0 = 0 at hz
    erw [DirectSum.of_eq_same] at hz
    exact hz

/-- The irrelevant ideal is generated by all actual strictly positive-degree sections. -/
theorem IntrinsicLineBundle.irrelevantIdeal_eq_span (L : IntrinsicLineBundle X) :
    L.irrelevantIdeal = Ideal.span {x : L.sectionRing | ∃ n : ℕ, 0 < n ∧
      ∃ s : bundlePowerGlobalSections L.sheaf n, L.ofSection n s = x} := by
  classical
  apply le_antisymm
  · intro x hx
    rw [← DirectSum.sum_support_of x]
    apply Submodule.sum_mem
    intro n hn
    by_cases hzero : n = 0
    · subst n
      rw [L.mem_irrelevantIdeal] at hx
      change L.ofSection 0 (L.degreeComponent 0 x) ∈ _
      rw [hx, map_zero]
      exact Submodule.zero_mem _
    · exact Ideal.subset_span ⟨n, by omega, L.degreeComponent n x, rfl⟩
  · apply Ideal.span_le.2
    rintro x ⟨n, hn, s, rfl⟩
    exact L.ofSection_mem_irrelevantIdeal hn s

/-- The actual augmentation quotient is the actual global structure ring. -/
def IntrinsicLineBundle.irrelevantQuotientRingEquiv (L : IntrinsicLineBundle X) :
    L.sectionRing ⧸ L.irrelevantIdeal ≃+* Γ(X, ⊤) :=
  L.sectionRingAugmentation.quotientKerEquivOfSurjective L.sectionRingAugmentation_surjective

/-- The quotient identification retains the literal degree-zero coefficient. -/
theorem IntrinsicLineBundle.irrelevantQuotientRingEquiv_mk (L : IntrinsicLineBundle X)
    (x : L.sectionRing) :
    L.irrelevantQuotientRingEquiv (Ideal.Quotient.mk L.irrelevantIdeal x) =
      L.degreeComponent 0 x :=
  RingHom.quotientKerEquivOfSurjective_apply_mk L.sectionRingAugmentation_surjective x

/-- The augmentation is linear for the actual structural base-field actions. -/
def IntrinsicLineBundle.sectionRingAugmentationAlgHom {K : Type u} [Field K]
    (L : IntrinsicLineBundle X) (f : X ⟶ Spec (.of K)) :
    letI := L.sectionRingAlgebra f
    letI := schemeGlobalSectionsAlgebra f
    L.sectionRing →ₐ[K] Γ(X, ⊤) := by
  letI := L.sectionRingAlgebra f
  letI := schemeGlobalSectionsAlgebra f
  exact { L.sectionRingAugmentation with
    commutes' := fun c ↦ L.sectionRingAugmentation_constants (schemeConstantMap f c) }

section Integral

variable [IsIntegral X]

/-- The actual cone is integral, by the faithful generic polynomial representation. -/
theorem IntrinsicLineBundle.sectionRingCone_isIntegral (L : IntrinsicLineBundle X) :
    IsIntegral L.sectionRingCone := inferInstanceAs (IsIntegral (Spec (.of L.sectionRing)))

/-- The positive-degree ideal is prime because the degree-zero structure ring is a domain. -/
instance intrinsicLineBundleIrrelevantIdealIsPrime (L : IntrinsicLineBundle X) :
    L.irrelevantIdeal.IsPrime := RingHom.ker_isPrime L.sectionRingAugmentation

/-- The actual vertex is the actual irrelevant prime in the spectrum. -/
def IntrinsicLineBundle.coneVertex (L : IntrinsicLineBundle X) : L.sectionRingCone :=
  ⟨L.irrelevantIdeal, inferInstance⟩

/-- Its prime ideal is the positive-degree ideal constructed above. -/
theorem IntrinsicLineBundle.coneVertex_asIdeal (L : IntrinsicLineBundle X) :
    L.coneVertex.asIdeal = L.irrelevantIdeal := rfl

/-- The native structure-sheaf stalk action of the actual section ring. -/
instance intrinsicLineBundleConeVertexStalkAlgebra (L : IntrinsicLineBundle X) :
    Algebra L.sectionRing (L.sectionRingCone.presheaf.stalk L.coneVertex) :=
  inferInstanceAs (Algebra L.sectionRing
    ((structurePresheafInCommRingCat L.sectionRing).stalk L.coneVertex))

/-- The genuine cone stalk is the localization at the genuine vertex prime. -/
def IntrinsicLineBundle.coneVertexStalkIso (L : IntrinsicLineBundle X) :
    Localization.AtPrime L.irrelevantIdeal ≃ₐ[L.sectionRing]
      L.sectionRingCone.presheaf.stalk L.coneVertex :=
  StructureSheaf.stalkIso L.sectionRing L.coneVertex

/-- The localization-to-stalk identification retains the actual ring-to-stalk map. -/
theorem IntrinsicLineBundle.coneVertexStalkIso_algebraMap (L : IntrinsicLineBundle X)
    (x : L.sectionRing) :
    L.coneVertexStalkIso (algebraMap L.sectionRing
      (Localization.AtPrime L.irrelevantIdeal) x) =
      algebraMap L.sectionRing (L.sectionRingCone.presheaf.stalk L.coneVertex) x :=
  L.coneVertexStalkIso.commutes x

section Constants

variable {K : Type u} [Field K] [IsAlgClosed K]

/-- The actual vertex quotient map uses the geometrically derived constants equivalence. -/
def IntrinsicLineBundle.coneResidueMap (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) [UniversallyClosed f] : L.sectionRing →+* K :=
  (schemeConstantsRingEquiv f).symm.toRingHom.comp L.sectionRingAugmentation

theorem IntrinsicLineBundle.coneResidueMap_apply (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) [UniversallyClosed f] (x : L.sectionRing) :
    L.coneResidueMap f x = (schemeConstantsRingEquiv f).symm (L.degreeComponent 0 x) := rfl

/-- The actual structural scalars survive unchanged in the vertex quotient. -/
theorem IntrinsicLineBundle.coneResidueMap_base (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) [UniversallyClosed f] (c : K) :
    L.coneResidueMap f (L.sectionRingBaseMap f c) = c := by
  change (schemeConstantsRingEquiv f).symm
    (L.sectionRingAugmentation (L.sectionRingConstants (schemeConstantMap f c))) = c
  rw [L.sectionRingAugmentation_constants]
  exact (schemeConstantsRingEquiv f).symm_apply_apply c

theorem IntrinsicLineBundle.coneResidueMap_surjective (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) [UniversallyClosed f] :
    Function.Surjective (L.coneResidueMap f) :=
  fun c ↦ ⟨L.sectionRingBaseMap f c, L.coneResidueMap_base f c⟩

/-- The kernel is the actual positive-degree ideal, not an assumed center. -/
theorem IntrinsicLineBundle.coneResidueMap_ker (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) [UniversallyClosed f] :
    RingHom.ker (L.coneResidueMap f) = L.irrelevantIdeal := by
  ext x
  change (schemeConstantsRingEquiv f).symm (L.sectionRingAugmentation x) = 0 ↔
    L.sectionRingAugmentation x = 0
  exact (schemeConstantsRingEquiv f).symm.map_eq_zero_iff

/-- Proper integral geometry over the algebraically closed field makes the vertex maximal. -/
theorem IntrinsicLineBundle.irrelevantIdeal_isMaximal (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) [UniversallyClosed f] : L.irrelevantIdeal.IsMaximal := by
  rw [← L.coneResidueMap_ker f]
  exact RingHom.ker_isMaximal_of_surjective (L.coneResidueMap f)
    (L.coneResidueMap_surjective f)

/-- The vertex is a genuinely closed point of the actual cone. -/
theorem IntrinsicLineBundle.coneVertex_isClosed (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) [UniversallyClosed f] :
    IsClosed ({L.coneVertex} : Set L.sectionRingCone) :=
  L.coneVertex.isClosed_singleton_iff_isMaximal.mpr (L.irrelevantIdeal_isMaximal f)

/-- The actual vertex quotient, as a ring, is the base field. -/
def IntrinsicLineBundle.vertexQuotientRingEquiv (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) [UniversallyClosed f] :
    L.sectionRing ⧸ L.irrelevantIdeal ≃+* K :=
  L.irrelevantQuotientRingEquiv.trans (schemeConstantsRingEquiv f).symm

theorem IntrinsicLineBundle.vertexQuotientRingEquiv_mk (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) [UniversallyClosed f] (x : L.sectionRing) :
    L.vertexQuotientRingEquiv f (Ideal.Quotient.mk L.irrelevantIdeal x) =
      L.coneResidueMap f x := by
  exact congrArg (schemeConstantsRingEquiv f).symm (L.irrelevantQuotientRingEquiv_mk x)

/-- The residue map is a map over the actual structural base field. -/
def IntrinsicLineBundle.coneResidueAlgHom (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) [UniversallyClosed f] :
    letI := L.sectionRingAlgebra f
    L.sectionRing →ₐ[K] K := by
  letI := L.sectionRingAlgebra f
  exact { L.coneResidueMap f with commutes' := L.coneResidueMap_base f }

/-- The quotient identification respects the actual base-field algebra. -/
def IntrinsicLineBundle.vertexQuotientAlgEquiv (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) [UniversallyClosed f] :
    letI := L.sectionRingAlgebra f
    (L.sectionRing ⧸ L.irrelevantIdeal) ≃ₐ[K] K := by
  letI := L.sectionRingAlgebra f
  exact { L.vertexQuotientRingEquiv f with
    commutes' := fun c ↦ (L.vertexQuotientRingEquiv_mk f _).trans
      (L.coneResidueMap_base f c) }

/-- The actual vertex localization has the actual base field as residue field. -/
def IntrinsicLineBundle.vertexLocalResidueAlgEquiv (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) [UniversallyClosed f] :
    letI := L.sectionRingAlgebra f
    L.irrelevantIdeal.ResidueField ≃ₐ[K] K := by
  letI := L.sectionRingAlgebra f
  letI := L.irrelevantIdeal_isMaximal f
  exact (AlgEquiv.ofBijective
    (IsScalarTower.toAlgHom K (L.sectionRing ⧸ L.irrelevantIdeal) L.irrelevantIdeal.ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField L.irrelevantIdeal)).symm.trans
      (L.vertexQuotientAlgEquiv f)

/-- The native local residue quotient retains exactly the actual degree-zero scalar. -/
theorem IntrinsicLineBundle.vertexLocalResidueAlgEquiv_algebraMap
    (L : IntrinsicLineBundle X) (f : X ⟶ Spec (.of K)) [UniversallyClosed f]
    (x : L.sectionRing) :
    letI := L.sectionRingAlgebra f
    L.vertexLocalResidueAlgEquiv f (algebraMap L.sectionRing L.irrelevantIdeal.ResidueField x) =
      L.coneResidueMap f x := by
  let := L.sectionRingAlgebra f
  let := L.irrelevantIdeal_isMaximal f
  let e := AlgEquiv.ofBijective
    (IsScalarTower.toAlgHom K (L.sectionRing ⧸ L.irrelevantIdeal) L.irrelevantIdeal.ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField L.irrelevantIdeal)
  change L.vertexQuotientAlgEquiv f
    (e.symm (algebraMap L.sectionRing L.irrelevantIdeal.ResidueField x)) = _
  rw [← Ideal.algebraMap_quotient_residueField_mk (I := L.irrelevantIdeal) x]
  change L.vertexQuotientAlgEquiv f
    (e.symm (e (Ideal.Quotient.mk L.irrelevantIdeal x))) = _
  rw [e.symm_apply_apply]
  exact L.vertexQuotientRingEquiv_mk f x

/-- The residue-field algebra map needed by local length is genuinely bijective. -/
theorem IntrinsicLineBundle.vertexLocalResidue_bijective (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) [UniversallyClosed f] :
    letI := L.sectionRingAlgebra f
    Function.Bijective (algebraMap K L.irrelevantIdeal.ResidueField) := by
  let := L.sectionRingAlgebra f
  have h : algebraMap K L.irrelevantIdeal.ResidueField =
      (L.vertexLocalResidueAlgEquiv f).symm.toRingHom := by
    ext c
    exact ((L.vertexLocalResidueAlgEquiv f).symm.commutes c).symm
  rw [h]
  exact (L.vertexLocalResidueAlgEquiv f).symm.bijective

/-- The scheme-theoretic residue field of the actual cone vertex is the base field. -/
def IntrinsicLineBundle.coneVertexResidueRingEquiv (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) [UniversallyClosed f] :
    L.sectionRingCone.residueField L.coneVertex ≃+* K :=
  (Scheme.Spec.residueFieldIso (.of L.sectionRing) L.coneVertex).commRingCatIsoToRingEquiv.trans
    (by letI := L.sectionRingAlgebra f
        exact (L.vertexLocalResidueAlgEquiv f).toRingEquiv)

/-- The literal structural cone map is induced by the actual degree-zero constants. -/
def IntrinsicLineBundle.coneStructuralMap (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) : L.sectionRingCone ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (L.sectionRingBaseMap f))

/-- The literal rational vertex is induced by the proved quotient map. -/
def IntrinsicLineBundle.coneVertexMorphism (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) [UniversallyClosed f] : Spec (.of K) ⟶ L.sectionRingCone :=
  Spec.map (CommRingCat.ofHom (L.coneResidueMap f))

/-- The actual rational vertex is a closed immersion, from the actual surjection. -/
theorem IntrinsicLineBundle.coneVertexMorphism_isClosedImmersion (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) [UniversallyClosed f] :
    IsClosedImmersion (L.coneVertexMorphism f) :=
  IsClosedImmersion.spec_of_surjective _ (L.coneResidueMap_surjective f)

/-- Every point of `Spec K` maps to the constructed irrelevant prime. -/
theorem IntrinsicLineBundle.coneVertexMorphism_apply (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) [UniversallyClosed f] (x : Spec (.of K)) :
    (L.coneVertexMorphism f) x = L.coneVertex := by
  apply PrimeSpectrum.ext
  change Ideal.comap (L.coneResidueMap f) x.asIdeal = L.irrelevantIdeal
  rw [x.asIdeal.eq_bot_of_prime]
  exact L.coneResidueMap_ker f

/-- The vertex morphism is a section of the genuine cone structure map. -/
theorem IntrinsicLineBundle.coneVertexMorphism_structural (L : IntrinsicLineBundle X)
    (f : X ⟶ Spec (.of K)) [UniversallyClosed f] :
    L.coneVertexMorphism f ≫ L.coneStructuralMap f = 𝟙 (Spec (.of K)) := by
  have h : (L.coneResidueMap f).comp (L.sectionRingBaseMap f) = RingHom.id K := by
    ext c
    exact L.coneResidueMap_base f c
  change Spec.map (CommRingCat.ofHom (L.coneResidueMap f)) ≫
    Spec.map (CommRingCat.ofHom (L.sectionRingBaseMap f)) = _
  rw [← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom ((L.coneResidueMap f).comp
    (L.sectionRingBaseMap f))) = _
  rw [h]
  exact Spec.map_id _

end Constants

end Integral

end

end SGPT.Foundations.Schemes
