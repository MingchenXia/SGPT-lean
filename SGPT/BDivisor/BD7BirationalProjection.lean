import SGPT.BDivisor.GMMorphism
import SGPT.Okounkov.OF14Algebraization
import SGPT.Okounkov.SchemeGenericPointComplexSurjectivity
import SGPT.Okounkov.SchemeNativeGenericStalkIso

/-! The algebraic projection on a book blow-up model is proper and birational. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.BDivisor.BD7

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open scoped Manifold ContDiff

local instance pointTopology {S : Scheme.{0}} (f : S ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f

local instance pointCharts {S : Scheme.{0}} (f : S ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f] :
    ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n

local instance pointManifold {S : Scheme.{0}} (f : S ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]

/-- Every finite book blow-up tower over a smooth integral projective base has a smooth integral
projective algebraization with the actual projection proper and birational. -/
theorem exists_proper_birational_projection_of_isBlowupSequence
    (E : ClosedProjectiveEmbedding f)
    {Y : Type} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    {π : Y → SchemeComplexPoint f} (hseq : IsBlowupSequence n (SchemeComplexPoint f) Y π) :
    ∃ (V : Scheme.{0}) (hV : IsIntegral V) (p : V ⟶ X)
      (hsm : SmoothOfRelativeDimension n (p ≫ f)) (EV : ClosedProjectiveEmbedding (p ≫ f)),
      letI := hV
      letI := hsm
      letI := EV.isSeparated
      letI := EV.quasiCompact
      IsProper p ∧ IsIso (p.stalkMap (genericPoint V)) ∧
        ∃ φ : SchemeComplexPoint (p ≫ f) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y,
          schemeComplexPointMap (p ≫ f) f p rfl = π ∘ φ := by
  let hπ := HironakaChowLemma.isAnalyticModification_of_isBlowupSequence hseq
  obtain ⟨V, hV, g, hsm, EV, φ, e, he⟩ := OF14.hasRationalAlgebraization_of_isBlowupSequence f E hseq
  let := hV
  let := hsm
  let := EV.isSeparated
  let := EV.quasiCompact
  obtain ⟨p, ⟨hp, hprojection⟩, -⟩ :=
    GM.exists_unique_morphism_of_holomorphic_smooth g EV n f E n (π ∘ φ)
      ((hπ.1.comp φ.contMDiff).mdifferentiable (by simp))
  subst g
  let : LocallyOfFiniteType f := E.locallyOfFiniteType
  let : IsProper (p ≫ f) := EV.isProper
  have hproper : IsProper p := IsProper.of_comp p f
  have hprojection' : schemeComplexPointMap (p ≫ f) f p rfl = π ∘ φ := funext hprojection
  have hsurj : Function.Surjective (schemeComplexPointMap (p ≫ f) f p rfl) := by
    rw [hprojection']
    exact (HironakaLocalPrincipalization.IsBlowupSequence.surjective hseq).comp φ.surjective
  have hη := genericPoint_eq_of_surjective_complexPoints f p hsurj
  obtain ⟨v⟩ := OF2.nonempty_schemeComplexPoint (p ≫ f) EV
  have hbir := isIso_genericStalkMap_of_rationalAlgebraization f p n hη hπ φ hprojection' v e
    (fun q => he q v)
  exact ⟨V, hV, p, hsm, EV, hproper, hbir, φ, hprojection'⟩

end SGPT.BDivisor.BD7
