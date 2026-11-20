import SGPT.Okounkov.OF2AbhyankarFlagExample
import SGPT.BDivisor.BD7Morphisms
import SGPT.BDivisor.BD7Birational
import SGPT.Okounkov.SchemeNativeBirationalModification
import SGPT.Unibranch.HironakaG10Complete

/-!
# cofinality of the book's blow-up models among smooth projective birational models

Source: `rmk:bdiv:L749`.  Dang–Favre [DF20] index b-divisor classes by the normal projective
birational models `ρ : X' → X` of `X`; the book indexes them by its blow-up models (`def:modif`,
finite compositions of blow-ups with smooth centres, `SGPT.BDivisor.ModelSystem.blowup`).  The
two projective limits agree once every model of Dang–Favre is dominated by a blow-up model,
compatibly with the algebraic structures.

Here `X` is an integral smooth projective complex scheme (the algebraic setting of the book: `X(ℂ)`
is a compact Kähler manifold) and `ρ : X' → X` is a **birational morphism from a smooth projective
integral complex scheme**: an isomorphism over a nonempty open subset `U ⊆ X`.

* `isAnalyticModification_of_birational`: the analytification `ρ(ℂ) : X'(ℂ) → X(ℂ)` is a proper
  bimeromorphic holomorphic map (lane Okounkov's `schemeNative_isAnalyticModification_of_isIso_restrict`);
* `exists_blowupModel_dominates`: **analytic domination** — by Hironaka's Chow lemma (goal G10,
  `SGPT.Unibranch.HironakaG10Complete.hironakaChowLemmaManifold`), some model `π : Y → X(ℂ)` of the
  book's blow-up system dominates `ρ(ℂ)`: `π = ρ(ℂ) ∘ γ` for a holomorphic `γ : Y → X'(ℂ)`;
* `exists_algebraic_blowupModel_dominates`: **algebraic domination** — given GAGA for morphisms
  (`GAGAMorphismsSmooth`), the dominating model has an algebraization `e : V(ℂ) ≃ Y` by an integral
  smooth projective complex scheme `V` (lanes BD5/OF14) and a morphism `h : V → X'` over `ℂ` with
  `h(ℂ) = γ ∘ e`; the composite `h ≫ ρ : V → X` is the algebraic projection of the model
  (`(h ≫ ρ)(ℂ) = π ∘ e`);
* `exists_algebraic_blowupModel_dominates_of_birational`: the same for a birational morphism in
  the sense of Stacks 01RO (an isomorphism of the local rings at the generic point, i.e. of function
  fields), which is an isomorphism over a nonempty open by `BD7Birational`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.BDivisor.BD7

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open SGPT.Okounkov SGPT.GAGA.H0S SGPT.Projective

local instance bd7CofTopology {X : Scheme.{0}} (h : X ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint h) := schemeAnalyticPointTopology h
local instance bd7CofCharts {X : Scheme.{0}} (h : X ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d h] : ChartedSpace (ComplexModel d) (SchemeComplexPoint h) :=
  schemeAnalyticTNChartedSpace h d
local instance bd7CofManifold {X : Scheme.{0}} (h : X ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d h] [IsSeparated h] [QuasiCompact h] :
    IsComplexManifold d (SchemeComplexPoint h) := schemeAnalyticTN_isComplexManifold h d

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f) {d : ℕ}
  [SmoothOfRelativeDimension d f] [IsIntegral X]
  {X' : Scheme.{0}} (ρ : X' ⟶ X) (E' : ClosedProjectiveEmbedding (ρ ≫ f))
  [SmoothOfRelativeDimension d (ρ ≫ f)] [IsIntegral X']

/-- **The analytification of a birational morphism of smooth projective varieties is a
modification.**  If `ρ : X' → X` is an isomorphism over a nonempty open `U ⊆ X` (`X`, `X'` integral
smooth projective over `ℂ` of the same dimension `d`), then `ρ(ℂ) : X'(ℂ) → X(ℂ)` is proper,
holomorphic and bimeromorphic (`IsAnalyticModification`). -/
theorem isAnalyticModification_of_birational (U : X.Opens) [IsIso (ρ ∣_ U)]
    (hU : (U : Set X).Nonempty) :
    let := E.isSeparated
    let := E.quasiCompact
    let := E'.isSeparated
    let := E'.quasiCompact
    IsAnalyticModification (n := d) (schemeComplexPointMap (ρ ≫ f) f ρ rfl) := by
  let := E.isSeparated
  let := E.quasiCompact
  let := E'.isSeparated
  let := E'.quasiCompact
  have : CompactSpace (SchemeComplexPoint (ρ ≫ f)) := E'.analyticCompact
  have : T2Space (SchemeComplexPoint f) := E.analyticT2
  have hproper : IsProperMap (schemeComplexPointMap (ρ ≫ f) f ρ rfl) :=
    (schemeComplexPointMap_continuous f ρ).isProperMap
  exact schemeNative_isAnalyticModification_of_isIso_restrict f ρ d U hU hproper

/-- **Analytic cofinality of the book's blow-up models** (Hironaka's Chow lemma).  Every birational
morphism `ρ : X' → X` (an isomorphism over a nonempty open `U ⊆ X`) from an integral smooth
projective complex scheme is dominated by a model `π : Y → X(ℂ)` of the book's blow-up system:
`ρ(ℂ) ∘ γ = π` for a holomorphic `γ : Y → X'(ℂ)`; equivalently the modification `ρ(ℂ)` of `X(ℂ)` is
dominated by `π`. -/
theorem exists_blowupModel_dominates (U : X.Opens) [IsIso (ρ ∣_ U)]
    (hU : (U : Set X).Nonempty) :
    let := E.isSeparated
    let := E.quasiCompact
    let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    let := E'.isSeparated
    let := E'.quasiCompact
    ∃ (π : (ModelSystem.blowup d (SchemeComplexPoint f)).Model)
      (γ : π.1.carrier → SchemeComplexPoint (ρ ≫ f)),
      ContMDiff 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel d) ∞ γ ∧
        schemeComplexPointMap (ρ ≫ f) f ρ rfl ∘ γ = π.1.map ∧
        (⟨SchemeComplexPoint (ρ ≫ f), schemeComplexPointMap (ρ ≫ f) f ρ rfl,
          isAnalyticModification_of_birational f E ρ E' (d := d) U hU⟩ : Modification d _) ≤ π.1 := by
  let := E.isSeparated
  let := E.quasiCompact
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let := E'.isSeparated
  let := E'.quasiCompact
  dsimp only
  have hmod := isAnalyticModification_of_birational f E ρ E' (d := d) U hU
  obtain ⟨W, tW, cW, mW, σ, γ, hσ, hγ, hc⟩ :=
    SGPT.Unibranch.HironakaG10Complete.hironakaChowLemmaManifold d (SchemeComplexPoint f)
      (SchemeComplexPoint (ρ ≫ f)) (schemeComplexPointMap (ρ ≫ f) f ρ rfl) hmod
  let π : (ModelSystem.blowup d (SchemeComplexPoint f)).Model :=
    ⟨Modification.ofIsBlowupSequence hσ, hσ⟩
  exact ⟨π, γ, hγ, hc, Modification.le_iff_dominates.mpr ⟨γ, hγ, hc⟩⟩

/-- **Algebraic cofinality of the book's blow-up models.**  Given GAGA for morphisms, every
birational morphism `ρ : X' → X` (an isomorphism over a nonempty open `U ⊆ X`) from an integral
smooth projective complex scheme `X'` is dominated by a model `π : Y → X(ℂ)` of the book's blow-up
system compatibly with the algebraic structures: `ρ(ℂ) ∘ γ = π` for a holomorphic
`γ : Y → X'(ℂ)`, `Y` has an algebraization `e : V(ℂ) ≃ Y` by an integral smooth projective complex
scheme `V`, and there is a morphism `h : V → X'` over `ℂ` with `h(ℂ) = γ ∘ e`; the algebraic
projection of the model is `h ≫ ρ : V → X`, `(h ≫ ρ)(ℂ) = π ∘ e`. -/
theorem exists_algebraic_blowupModel_dominates (H : GAGAMorphismsSmooth) (U : X.Opens)
    [IsIso (ρ ∣_ U)] (hU : (U : Set X).Nonempty) :
    let := E.isSeparated
    let := E.quasiCompact
    let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    let := E'.isSeparated
    let := E'.quasiCompact
    ∃ (π : (ModelSystem.blowup d (SchemeComplexPoint f)).Model)
      (γ : π.1.carrier → SchemeComplexPoint (ρ ≫ f)),
      ContMDiff 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel d) ∞ γ ∧
        schemeComplexPointMap (ρ ≫ f) f ρ rfl ∘ γ = π.1.map ∧
      ∃ (V : Scheme.{0}) (g : V ⟶ Spec (.of ℂ)) (hsm : SmoothOfRelativeDimension d g)
        (EV : ClosedProjectiveEmbedding g),
        letI := hsm
        letI := EV.isSeparated
        letI := EV.quasiCompact
        IsIntegral V ∧
        ∃ (e : SchemeComplexPoint g ≃ₘ⟮𝓘(ℂ, ComplexModel d), 𝓘(ℂ, ComplexModel d)⟯ π.1.carrier)
          (h : V ⟶ X') (hh : h ≫ ρ ≫ f = g),
          (∀ q, schemeComplexPointMap g (ρ ≫ f) h hh q = γ (e q)) ∧
          ∀ q, schemeComplexPointMap g f (h ≫ ρ) (by rw [Category.assoc, hh]) q =
            π.1.map (e q) := by
  let := E.isSeparated
  let := E.quasiCompact
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let := E'.isSeparated
  let := E'.quasiCompact
  dsimp only
  obtain ⟨π, γ, hγ, hc, -⟩ := exists_blowupModel_dominates f E ρ E' (d := d) U hU
  obtain ⟨V, g, hsm, EV, ⟨e⟩⟩ := BD5.exists_algebraization_of_blowup_model_bd5 f E π
  let := hsm
  let := EV.isSeparated
  let := EV.quasiCompact
  have : Nonempty (SchemeComplexPoint f) := SGPT.Okounkov.OF2.nonempty_schemeComplexPoint f E
  have : ConnectedSpace (SchemeComplexPoint f) :=
    SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E d
  have : ConnectedSpace π.1.carrier := Modification.IsBlowupModel.connectedSpace π.2
  have : ConnectedSpace (SchemeComplexPoint g) :=
    e.symm.toHomeomorph.surjective.connectedSpace e.symm.continuous
  have hint : IsIntegral V :=
    SGPT.Okounkov.OF14.isIntegral_of_connectedSpace_schemeComplexPoint g d EV
  obtain ⟨h, hh, hpt⟩ := H V X' g (ρ ≫ f) d d EV E' (γ ∘ e) (hγ.comp e.contMDiff)
  refine ⟨π, γ, hγ, hc, V, g, hsm, EV, hint, e, h, hh, hpt, fun q => ?_⟩
  have h1 : schemeComplexPointMap g f (h ≫ ρ) (by rw [Category.assoc, hh]) q =
      schemeComplexPointMap (ρ ≫ f) f ρ rfl (schemeComplexPointMap g (ρ ≫ f) h hh q) :=
    Subtype.ext (Category.assoc _ _ _).symm
  rw [h1, hpt q]
  exact congrFun hc (e q)

/-- **Algebraic cofinality of the book's blow-up models, birational form.**  Given GAGA for
morphisms, every **birational** morphism `ρ : X' → X` (Stacks 01RO: `ρ` induces an isomorphism of
the local rings at the generic point of `X'`, i.e. `ℂ(X) ≅ ℂ(X')`) from an integral smooth projective
complex scheme `X'` of the same dimension is dominated by a model `π : Y → X(ℂ)` of the book's blow-up
system compatibly with the algebraic structures (as in `exists_algebraic_blowupModel_dominates`). -/
theorem exists_algebraic_blowupModel_dominates_of_birational (H : GAGAMorphismsSmooth)
    [IsIso (ρ.stalkMap (genericPoint X'))] :
    let := E.isSeparated
    let := E.quasiCompact
    let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    let := E'.isSeparated
    let := E'.quasiCompact
    ∃ (π : (ModelSystem.blowup d (SchemeComplexPoint f)).Model)
      (γ : π.1.carrier → SchemeComplexPoint (ρ ≫ f)),
      ContMDiff 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel d) ∞ γ ∧
        schemeComplexPointMap (ρ ≫ f) f ρ rfl ∘ γ = π.1.map ∧
      ∃ (V : Scheme.{0}) (g : V ⟶ Spec (.of ℂ)) (hsm : SmoothOfRelativeDimension d g)
        (EV : ClosedProjectiveEmbedding g),
        letI := hsm
        letI := EV.isSeparated
        letI := EV.quasiCompact
        IsIntegral V ∧
        ∃ (e : SchemeComplexPoint g ≃ₘ⟮𝓘(ℂ, ComplexModel d), 𝓘(ℂ, ComplexModel d)⟯ π.1.carrier)
          (h : V ⟶ X') (hh : h ≫ ρ ≫ f = g),
          (∀ q, schemeComplexPointMap g (ρ ≫ f) h hh q = γ (e q)) ∧
          ∀ q, schemeComplexPointMap g f (h ≫ ρ) (by rw [Category.assoc, hh]) q =
            π.1.map (e q) := by
  have : LocallyOfFiniteType (ρ ≫ f) := E'.locallyOfFiniteType
  have : LocallyOfFiniteType ρ := locallyOfFiniteType_of_comp ρ f
  have : IsSeparated (ρ ≫ f) := E'.isSeparated
  have : IsSeparated ρ := IsSeparated.of_comp (f := ρ) (g := f)
  obtain ⟨U, hU, hiso⟩ := exists_isIso_morphismRestrict_of_isIso_stalkMap ρ
  exact exists_algebraic_blowupModel_dominates f E ρ E' (d := d) H U hU

end SGPT.BDivisor.BD7
