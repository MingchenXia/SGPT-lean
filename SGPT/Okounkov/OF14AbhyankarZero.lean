import SGPT.Okounkov.OF2AbhyankarCurve
import SGPT.Okounkov.OF11SncFlag
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import SGPT.Unibranch.UnibAnSpace
import SGPT.Unibranch.SmoothCentreModification

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.OF14

open Algebra CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set TopologicalSpace
open SGPT.Okounkov.OF5 SGPT.Okounkov.ValCurr
open SGPT.Unibranch SGPT.Unibranch.SmoothCentreModification

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))
  [IsSeparated f] [QuasiCompact f] [LocallyOfFiniteType f]

/-- Rank zero in the algebraic statement. The only member of the flag is the
original singleton scheme, and its analytic modification is the identity. -/
theorem exists_identity_admissibleFlag_lexEquivalent_dim_zero
    (_E : ClosedProjectiveEmbedding f)
    (hdim : letI := schemeFunctionFieldAlgebra f; Algebra.trdeg ℂ X.functionField = 0)
    (ν : AddValuation X.functionField (WithTop (Lex (Fin 0 → ℤ)))) :
    IsModification (𝟙 (UnibAn.analytification f)) ∧
      ∃ (_ : IsIso f) (hsm : SmoothOfRelativeDimension 0 f)
        (Y : Fin (0 + 1) → Set X) (hY : IsAdmissibleFlag f 0 Y),
        letI := hsm
        Y 0 = {hY.point} ∧ admissibleFlagValuation hY = ν := by
  classical
  let x : X := genericPoint X
  let K := X.presheaf.stalk x
  let : Algebra ℂ K := stalkComplexAlgebra f x
  have htrdeg : Algebra.trdeg ℂ K = 0 := hdim
  let : Algebra.IsAlgebraic ℂ K := trdeg_eq_zero_iff.mp htrdeg
  let : Algebra.IsIntegral ℂ K := inferInstance
  let e : ℂ ≃ₐ[ℂ] K := AlgEquiv.ofBijective (Algebra.ofId ℂ K)
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let q : (↥K ⧸ (⊥ : Ideal ↥K)) ≃ₐ[ℂ] ↥K :=
    { RingEquiv.quotientBot K with commutes' := fun c => rfl }
  have hSmooth : Algebra.FormallySmooth ℂ (↥K ⧸ (⊥ : Ideal ↥K)) :=
    Algebra.FormallySmooth.of_equiv (e.trans q.symm)
  have hmax : IsLocalRing.maximalIdeal K = ⊥ :=
    IsLocalRing.isField_iff_maximalIdeal_eq.mp (Semifield.toIsField K)
  let p : Fin (0 + 1) → Ideal K := fun _ => ⊥
  have hprime (i : Fin (0 + 1)) : (p i).IsPrime :=
    inferInstanceAs ((⊥ : Ideal K).IsPrime)
  have hheight (i : Fin (0 + 1)) : (p i).height = (i : ℕ) := by
    have hi : i = 0 := by
      apply Fin.ext
      change i.val = 0
      exact Nat.lt_one_iff.mp i.isLt
    subst i
    exact Ideal.height_eq_zero_iff_eq_bot.mpr rfl
  obtain ⟨Y, hY, -, -⟩ :=
    OF11.exists_admissibleFlag_of_primeChain (f := f) x p hprime (fun _ _ _ => le_rfl)
      hheight rfl hmax.symm (fun i => by
        change Algebra.FormallySmooth ℂ (↥K ⧸ (⊥ : Ideal ↥K))
        exact hSmooth)
  let a : CommRingCat.of ℂ ⟶ X.functionField := CommRingCat.ofHom (algebraMap ℂ K)
  let s : X.functionField ⟶ CommRingCat.of ℂ := CommRingCat.ofHom e.symm.toRingHom
  let t := X.fromSpecStalk x
  have ht : t.appTop ≫ (Scheme.ΓSpecIso (X.presheaf.stalk x)).hom =
      X.presheaf.germ ⊤ x trivial := by
    dsimp only [t]
    rw [Scheme.fromSpecStalk_appTop]
    simp only [homOfLE_refl, op_id]
    rw [(Spec (X.presheaf.stalk x)).presheaf.map_id (.op ⊤)]
    simp only [Category.comp_id, Category.assoc, Iso.inv_hom_id]
  have ha : AlgebraicValuation.complexToFunctionField f = a := by
    let u := t ≫ f
    have hn := Scheme.ΓSpecIso_inv_naturality (Spec.preimage u)
    rw [Spec.map_preimage] at hn
    have hr : (Scheme.ΓSpecIso (.of ℂ)).inv ≫ u.appTop ≫
        (Scheme.ΓSpecIso (X.presheaf.stalk x)).hom = Spec.preimage u := by
      rw [← Category.assoc, ← hn]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    change Spec.preimage u = a
    rw [← hr]
    change (Scheme.ΓSpecIso (.of ℂ)).inv ≫ (t ≫ f).appTop ≫
      (Scheme.ΓSpecIso (X.presheaf.stalk x)).hom = a
    rw [Scheme.Hom.comp_appTop, Category.assoc, ht]
    rfl
  have has : a ≫ s = 𝟙 _ := by
    apply CommRingCat.hom_ext
    ext c
    exact e.symm_apply_apply c
  let sectionPoint := Spec.map s ≫ t
  have hsection : sectionPoint ≫ f = 𝟙 _ := by
    change (Spec.map s ≫ X.fromSpecStalk (genericPoint X)) ≫ f = _
    rw [Category.assoc, ← AlgebraicValuation.spec_map_complexToFunctionField f,
      ha, ← Spec.map_comp, has, Spec.map_id]
  let : IsProper (sectionPoint ≫ f) := hsection.symm ▸ inferInstanceAs (IsProper (𝟙 _))
  let : IsProper sectionPoint := IsProper.of_comp sectionPoint f
  have hxPoint : sectionPoint default = x := by
    change (Spec.map s ≫ t) default = x
    rw [Scheme.Hom.comp_apply]
    have hprimeSpec : Subsingleton (PrimeSpectrum X.functionField) :=
      PrimeSpectrum.subsingleton_iff_isField_of_isReduced.mpr (Field.toIsField X.functionField)
    have hd : Spec.map s default = IsLocalRing.closedPoint K :=
      @Subsingleton.elim (PrimeSpectrum X.functionField) hprimeSpec _ _
    rw [hd]
    exact Scheme.fromSpecStalk_closedPoint
  have hrange : range sectionPoint = {x} := by
    let z : SchemeComplexPoint f := ⟨sectionPoint, hsection⟩
    exact (schemeComplexPoint_range f z).trans (congrArg Set.singleton hxPoint)
  have hClosed : IsClosed ({x} : Set X) := hrange ▸ sectionPoint.isClosedMap.isClosed_range
  have hXsingleton : (univ : Set X) = {x} :=
    (genericPoint_spec X).def.symm.trans hClosed.closure_eq
  have hpoint (a : X) : a = x := by
    have ha : a ∈ (univ : Set X) := mem_univ _
    rw [hXsingleton] at ha
    exact Set.mem_singleton_iff.mp ha
  have h0 : Y 0 = {hY.point} := by
    rw [hY.zero_eq, hXsingleton, hpoint hY.point]
  have hcomp : (f ≫ sectionPoint) ≫ f = f := by rw [Category.assoc, hsection, Category.comp_id]
  have : LocallyOfFiniteType ((f ≫ sectionPoint) ≫ f) := by rw [hcomp]; infer_instance
  have hleft : f ≫ sectionPoint = 𝟙 X :=
    ext_of_apply_eq f univ isOpen_univ.isLocallyClosed dense_univ
      (fun a _ _ => (hpoint ((f ≫ sectionPoint) a)).trans (hpoint ((𝟙 X) a)).symm)
      (hcomp.trans (Category.id_comp f).symm)
  let : IsIso f := ⟨⟨sectionPoint, hleft, hsection⟩⟩
  have hsm : SmoothOfRelativeDimension 0 f := inferInstance
  exact ⟨IsModification.id _, inferInstance, hsm, Y, hY, h0, OF2.addValuation_fin_zero_eq _ _⟩

end SGPT.Okounkov.OF14
