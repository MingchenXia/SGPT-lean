import SGPT.BDivisor.BD7BirationalProjection
import SGPT.BDivisor.BD7GAGA
import SGPT.Okounkov.OF12SmoothProjectiveBirationalModel

/-! Cofinality of the book's blow-up models over integral projective birational models. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.BDivisor.BD7

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set TopologicalSpace
open SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Manifold ContDiff

local instance cofinalTopology {S : Scheme.{0}} (g : S ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint g) :=
  schemeAnalyticPointTopology g

local instance cofinalCharts {S : Scheme.{0}} (g : S ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d g] :
    ChartedSpace (ComplexModel d) (SchemeComplexPoint g) :=
  schemeAnalyticTNChartedSpace g d

local instance cofinalManifold {S : Scheme.{0}} (g : S ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d g] [IsSeparated g] [QuasiCompact g] :
    IsComplexManifold d (SchemeComplexPoint g) :=
  schemeAnalyticTN_isComplexManifold g d

private theorem genericPoint_eq_of_isIso_stalkMap {A B : Scheme.{0}}
    [IsIntegral A] [IsIntegral B] (q : A ⟶ B)
    [LocallyOfFiniteType q] [IsSeparated q] [IsIso (q.stalkMap (genericPoint A))] :
    q (genericPoint A) = genericPoint B := by
  obtain ⟨U, hU, hIso⟩ := exists_isIso_morphismRestrict_of_isIso_stalkMap q
  let : IsIso (q ∣_ U) := hIso
  let : IsDominant U.ι := Opens.isDominant_ι (U.isOpen.dense hU)
  have : IsDominant ((q ⁻¹ᵁ U).ι ≫ q) := by
    rw [← morphismRestrict_ι]
    infer_instance
  let : IsDominant q := IsDominant.of_comp (q ⁻¹ᵁ U).ι q
  apply ((genericPoint_spec B).eq _).symm
  simpa only [Set.image_univ, q.denseRange.closure_range] using
    (genericPoint_spec A).image q.continuous

/-- The composite of actual generic-stalk isomorphisms is again a generic-stalk isomorphism
when the first morphism sends the generic point to the generic point. -/
theorem isIso_genericStalkMap_comp {A B C : Scheme.{0}} [IsIntegral A] [IsIntegral B]
    (a : A ⟶ B) (b : B ⟶ C) (ha : a (genericPoint A) = genericPoint B)
    [IsIso (a.stalkMap (genericPoint A))] [IsIso (b.stalkMap (genericPoint B))] :
    IsIso ((a ≫ b).stalkMap (genericPoint A)) := by
  have h : IsIso (b.stalkMap (a (genericPoint A))) := by
    rw [ha]
    infer_instance
  let := h
  rw [Scheme.Hom.stalkMap_comp]
  infer_instance

/-- Every integral projective birational model is dominated by an algebraized blow-up model
of the book with an actual proper birational projection. -/
theorem exists_proper_birational_blowupModel_dominates_integral
    {X X' : Scheme.{0}} [IsIntegral X] [IsIntegral X']
    (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f) {d : ℕ}
    [SmoothOfRelativeDimension d f] (ρ : X' ⟶ X)
    (E' : ClosedProjectiveEmbedding (ρ ≫ f)) [IsIso (ρ.stalkMap (genericPoint X'))] :
    letI := E.isSeparated
    letI := E.quasiCompact
    letI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    ∃ (π : (ModelSystem.blowup d (SchemeComplexPoint f)).Model)
      (V : Scheme.{0}) (hV : IsIntegral V) (p : V ⟶ X)
      (hsm : SmoothOfRelativeDimension d (p ≫ f)) (EV : ClosedProjectiveEmbedding (p ≫ f)),
      letI := hV
      letI := hsm
      letI := EV.isSeparated
      letI := EV.quasiCompact
      IsProper p ∧ IsIso (p.stalkMap (genericPoint V)) ∧
        ∃ φ : SchemeComplexPoint (p ≫ f) ≃ₘ⟮𝓘(ℂ, ComplexModel d), 𝓘(ℂ, ComplexModel d)⟯
            π.1.carrier,
          schemeComplexPointMap (p ≫ f) f p rfl = π.1.map ∘ φ ∧
          ∃ k : V ⟶ X', k ≫ ρ = p := by
  let := E.isSeparated
  let := E.quasiCompact
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : LocallyOfFiniteType f := E.locallyOfFiniteType
  let : LocallyOfFiniteType (ρ ≫ f) := E'.locallyOfFiniteType
  let : LocallyOfFiniteType ρ := locallyOfFiniteType_of_comp ρ f
  let : IsProper (ρ ≫ f) := E'.isProper
  let : IsSeparated ρ := IsSeparated.of_comp (f := ρ) (g := f)
  let := schemeFunctionFieldAlgebra f
  let := schemeFunctionFieldAlgebra (ρ ≫ f)
  obtain ⟨R, hR, σ, hσ, n, hnSmooth, ER, hdim, hσbir, _, _⟩ :=
    OF12.exists_smooth_projective_birational_model E'
  let := hR
  let := hσ
  let := hσbir
  let : LocallyOfFiniteType (σ ≫ (ρ ≫ f)) := ER.locallyOfFiniteType
  let : LocallyOfFiniteType σ := locallyOfFiniteType_of_comp σ (ρ ≫ f)
  have ησ := genericPoint_eq_of_isIso_stalkMap σ
  have ηρ := genericPoint_eq_of_isIso_stalkMap ρ
  let c := X.presheaf.stalkCongr (.of_eq ηρ.symm)
  let e := (asIso (c.hom ≫ ρ.stalkMap (genericPoint X'))).commRingCatIsoToRingEquiv
  have he : OF12.IsStalkCompatible ρ e.toRingHom :=
    SGPT.NAPotential.AlgPrimes3.ProjectiveGraphStalkNaturality.genericPullback_stalk ρ ηρ
  have hdim' : Algebra.trdeg ℂ X'.functionField = d :=
    (OF12.IsStalkCompatible.toFunctionFieldAlgEquiv f ρ e he).trdeg_eq.symm.trans
      (nativeSmoothFunctionField_trdeg f d)
  have hnd : n = d := by exact_mod_cast hdim.symm.trans hdim'
  subst n
  let F := σ ≫ ρ
  have hF : F ≫ f = σ ≫ ρ ≫ f := Category.assoc σ ρ f
  let ER' : ClosedProjectiveEmbedding (F ≫ f) := hF.symm ▸ ER
  let : SmoothOfRelativeDimension d (F ≫ f) := hF.symm ▸ hnSmooth
  let : IsIso (F.stalkMap (genericPoint R)) := isIso_genericStalkMap_comp σ ρ ησ
  let : LocallyOfFiniteType (F ≫ f) := ER'.locallyOfFiniteType
  let : LocallyOfFiniteType F := locallyOfFiniteType_of_comp F f
  let : IsSeparated (F ≫ f) := ER'.isSeparated
  let : IsSeparated F := IsSeparated.of_comp (f := F) (g := f)
  let := ER'.quasiCompact
  obtain ⟨U, hU, hIso⟩ := exists_isIso_morphismRestrict_of_isIso_stalkMap F
  let := hIso
  obtain ⟨π, γ, hγ, hγproj, _⟩ := exists_blowupModel_dominates f E F ER' (d := d) U hU
  obtain ⟨V, hV, p, hsm, EV, hp, hpbir, φ, hproj⟩ :=
    exists_proper_birational_projection_of_isBlowupSequence f d E π.2
  let := hV
  let := hsm
  let := EV.isSeparated
  let := EV.quasiCompact
  let := EV.locallyOfFiniteType
  obtain ⟨j, hj, hmap⟩ := gagaMorphismsSmooth V R (p ≫ f) (F ≫ f) d d EV ER'
    (γ ∘ φ) (hγ.comp φ.contMDiff)
  have htriangle : j ≫ F = p := by
    apply hom_ext_of_schemeComplexPointMap_eq (p ≫ f) f
      (show (j ≫ F) ≫ f = p ≫ f by rw [Category.assoc, hj]) rfl
    intro z
    rw [schemeComplexPointMap_comp (p ≫ f) (F ≫ f) f j hj F rfl, hmap z]
    exact (congrFun hγproj (φ z)).trans (congrFun hproj z).symm
  exact ⟨π, V, hV, p, hsm, EV, hp, hpbir, φ, hproj, j ≫ σ,
    by simpa only [F, Category.assoc] using htriangle⟩

end SGPT.BDivisor.BD7
